module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SENeDRed
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Core
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KF138OmegaCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (d : G) (K : Subgroup G),
    K ∈ thetaComponentsAt 3 d → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    E ≤ Subgroup.normalizer (K : Set G) →
    Late.sectionCentralizer E K ((aschbacherSolvableCore 3 K).map K.subtype) =
      (Subgroup.zpowers d : Set G) →
    Sec8.IsZ3PGLThreePi (lBarA d K E) → (∃ x₀ ∈ E, Sec4.InducesTypeOn K x₀ 3) →
    ∀ g ∈ Subgroup.normalizer (K : Set G), g ^ 3 = 1 →
      (∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ Sec4.thetaQuotCentralizer K) →
        ∃ e ∈ E, e⁻¹ * g ∈ Sec4.thetaQuotCentralizer K

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commute_of_mem_zpowers {d g z : G} (hdg : Commute d g) (hz : z ∈ Subgroup.zpowers d) :
    Commute z g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact hdg.zpow_left k

theorem step138ENeDTwo_of (hKF : KF138OmegaCent) (hcore : Step13PZeroCore) :
    Step138ENeDTwo := by
  intro G _ _ A c L E F x y t hfr hΩ K hK hdK hEKc hFK htK hPGLK hAut hx₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d := ⁅x, y⁆ with hd
  have h := hfr.hH.1
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  have hD : Sec13Data G E d K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := hΩ
      mem_lA := hK }
  have hE3 : CFSG.Assembly.IsElemAbelian 3 E := hfr.hH.2.2.2.1
  have hdF : d ∈ F := (Subgroup.mem_inf.mp hfr.hdZ).2
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hdC : d ∈ Sec4.thetaQuotCentralizer K := by
    have : d ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) := by
      rw [← hCEset]
      exact Subgroup.mem_zpowers d
    exact (Subgroup.mem_inf.mp this).2
  have hya : ∀ a ∈ E, y * a * y⁻¹ * a⁻¹ ∈ Subgroup.zpowers d := by
    intro a ha
    by_cases haF : a ∈ F
    · rw [hfr.hFab y hfr.hyF a haF, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · obtain ⟨k, -, hk⟩ := conj_y_eq_of_not_mem hfr.frame hfr.hxE hfr.hyF hfr.hE27 hfr.hF27
        hfr.h9 hfr.hFN hfr.hEab ha haF
      have hda : Commute (d ^ k) a :=
        (show Commute d a from hfr.hEab d hfr.hdE a ha).pow_left k
      rw [hk, show a * d ^ k * a⁻¹ = d ^ k by rw [← hda.eq]; group]
      exact pow_mem (Subgroup.mem_zpowers d) k
  have hy3 : y ^ 3 = 1 := hfr.frame.y3
  obtain ⟨e, heE, hey⟩ := hKF G E d K hK.1 hE3 hfr.hE27 hK.2.1 hK.2.2.1 hPGLK hx₀ y
    (hFK hfr.hyF) hy3 (fun a ha => Subgroup.zpowers_le.mpr hdC (hya a ha))
  set w := e⁻¹ * y with hw
  have hdy : Commute d y := hfr.hFab d hdF y hfr.hyF
  have hde : Commute d e⁻¹ := (show Commute d e from hfr.hEab d hfr.hdE e heE).inv_right
  have hk : ⁅y, e⁻¹⁆ ∈ Subgroup.zpowers d := by
    rw [commutatorElement_def]
    exact hya e⁻¹ (inv_mem heE)
  have hw3 : w ^ 3 = 1 := by
    rw [hw, mul_pow_three_of_commute (commute_of_mem_zpowers hdy hk)
      (commute_of_mem_zpowers hde hk), hy3, inv_pow, hfr.hE3 e heE, inv_one, one_mul, mul_one]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hfr.hd3, one_zpow]
  have hwd : w ∉ Subgroup.zpowers d := by
    intro hwd
    have hyE : y ∈ E := by
      rw [show y = e * w by rw [hw]; group]
      exact mul_mem heE (Subgroup.zpowers_le.mpr hfr.hdE hwd)
    apply hfr.hd1
    rw [commutatorElement_def, hfr.hEab x hfr.hxE y hyE]
    group
  have hdw : ∀ a ∈ Subgroup.zpowers d, a * w = w * a := fun a ha =>
    (commute_of_mem_zpowers (hde.mul_right hdy) ha).eq
  obtain ⟨hWel, hW9⟩ := Sec5.isElemAbelian_sup_zpowers (isElemAbelian_zpowers hfr.hd3) hwd hw3 hdw
  rw [card_zpowers_of_pow_three hfr.hd3 hfr.hd1] at hW9
  have hWC : Subgroup.zpowers d ⊔ Subgroup.zpowers w ≤ Sec4.thetaQuotCentralizer K :=
    sup_le (Subgroup.zpowers_le.mpr hdC) (Subgroup.zpowers_le.mpr hey)
  exact hcore G E d K hD (facts_of_isZ3PGLThreePi hD hPGLK).1 _
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)) hWC hWel hW9

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
