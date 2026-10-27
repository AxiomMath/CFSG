module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSPhi
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (thL
  exists_fixed_coset not_dvd_card_of_no_order_three eq_one_of_pow_three_of_not_dvd
  le_normalizer_of_conj_mem subgroupOf_commutator_of_le)
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] noncomputable def bar (L U : Subgroup Γ) :
    Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :=
  (U.subgroupOf (Subgroup.normalizer (L : Set Γ))).map (phi L)

section Bar

variable {L : Subgroup Γ}

theorem mem_bar {U : Subgroup Γ} {x : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)} :
    x ∈ bar L U ↔ ∃ (g : Γ) (hg : g ∈ Subgroup.normalizer (L : Set Γ)), g ∈ U ∧
      phi L ⟨g, hg⟩ = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, y.2, hy, rfl⟩
  · rintro ⟨g, hg, hgU, rfl⟩
    exact ⟨⟨g, hg⟩, hgU, rfl⟩

theorem phi_mem_bar {U : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (L : Set Γ))
    (hgU : g ∈ U) : phi L ⟨g, hg⟩ ∈ bar L U :=
  mem_bar.mpr ⟨g, hg, hgU, rfl⟩

theorem bar_mono {U V : Subgroup Γ} (h : U ≤ V) : bar L U ≤ bar L V := by
  intro x hx
  obtain ⟨g, hg, hgU, rfl⟩ := mem_bar.mp hx
  exact phi_mem_bar hg (h hgU)

theorem bar_bot : bar L (⊥ : Subgroup Γ) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨g, hg, hg1, rfl⟩ := mem_bar.mp hx
  have : g = 1 := hg1
  subst this
  have : (⟨1, hg⟩ : ↥(Subgroup.normalizer (L : Set Γ))) = 1 := rfl
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem bar_commutator {U V : Subgroup Γ} (hU : U ≤ Subgroup.normalizer (L : Set Γ))
    (hV : V ≤ Subgroup.normalizer (L : Set Γ)) : bar L ⁅U, V⁆ = ⁅bar L U, bar L V⁆ := by
  rw [bar, bar, bar, subgroupOf_commutator_of_le hU hV, Subgroup.map_commutator]

theorem bar_le_normalizer_bar {K' O : Subgroup Γ} (hKO : K' ≤ Subgroup.normalizer (O : Set Γ)) :
    bar L K' ≤
      Subgroup.normalizer (↑(bar L O) : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
  have key : ∀ g ∈ K', ∀ (hg : g ∈ Subgroup.normalizer (L : Set Γ)), ∀ y ∈ bar L O,
      phi L ⟨g, hg⟩ * y * (phi L ⟨g, hg⟩)⁻¹ ∈ bar L O := by
    intro g hgK hg y hy
    obtain ⟨o, ho, hoO, rfl⟩ := mem_bar.mp hy
    have hconj : g * o * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hgK) o).mp hoO
    have hconjN : g * o * g⁻¹ ∈ Subgroup.normalizer (L : Set Γ) :=
      mul_mem (mul_mem hg ho) (inv_mem hg)
    have : phi L ⟨g, hg⟩ * phi L ⟨o, ho⟩ * (phi L ⟨g, hg⟩)⁻¹ = phi L ⟨g * o * g⁻¹, hconjN⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact phi_mem_bar hconjN hconj
  intro x hx
  obtain ⟨g, hg, hgK, rfl⟩ := mem_bar.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hgK hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hgK) (inv_mem hg) _ hy
  have e : phi L ⟨g⁻¹, inv_mem hg⟩ = (phi L ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, inv_inv] at this
  simpa [mul_assoc] using this

theorem card_bar_dvd {U : Subgroup Γ} (hU : U ≤ Subgroup.normalizer (L : Set Γ)) :
    Nat.card (bar L U) ∣ Nat.card U := by
  have h1 : Nat.card (bar L U) ∣ Nat.card (U.subgroupOf (Subgroup.normalizer (L : Set Γ))) :=
    Subgroup.card_map_dvd _ _
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv] at h1

theorem bar_pPrimeCoreOf_le {K' : Subgroup Γ} (hK : K' ≤ Subgroup.normalizer (L : Set Γ)) :
    bar L (pPrimeCoreOf 3 K') ≤ pPrimeCoreOf 3 (bar L K') := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : pPrimeCoreOf 3 K' ≤ K' := pPrimeCoreOf_le 3 K'
  refine le_pPrimeCoreOf (bar_mono hO)
    (bar_le_normalizer_bar (le_normalizer_pPrimeCoreOf 3 K')) ?_
  exact Nat.Coprime.coprime_dvd_right (card_bar_dvd (hO.trans hK)) (coprime_card_pPrimeCoreOf 3 K')

end Bar

@[expose] noncomputable def kerLR (L R : Subgroup Γ) : Subgroup Γ :=
  (phi L).ker.map (Subgroup.normalizer (L : Set Γ)).subtype ⊓ (L ⊔ R)

theorem mem_kerLR {L R : Subgroup Γ} {g : Γ} :
    g ∈ kerLR L R ↔
      (∃ hg : g ∈ Subgroup.normalizer (L : Set Γ), phi L ⟨g, hg⟩ = 1) ∧ g ∈ L ⊔ R := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hLR⟩
    exact ⟨⟨y.2, hy⟩, hLR⟩
  · rintro ⟨⟨hg, h⟩, hLR⟩
    exact ⟨⟨⟨g, hg⟩, h, rfl⟩, hLR⟩

theorem le_normalizer_kerLR {L R A : Subgroup Γ} (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) :
    A ≤ Subgroup.normalizer (kerLR L R : Set Γ) := by
  refine le_normalizer_of_conj_mem fun a ha g hg => ?_
  obtain ⟨⟨hgN, h1⟩, hgLR⟩ := mem_kerLR.mp hg
  have haN := hAL ha
  have hconjN : a * g * a⁻¹ ∈ Subgroup.normalizer (L : Set Γ) :=
    mul_mem (mul_mem haN hgN) (inv_mem haN)
  have hLRn : A ≤ Subgroup.normalizer ((L ⊔ R : Subgroup Γ) : Set Γ) :=
    Sec14.le_normalizer_sup hAL hAR
  refine mem_kerLR.mpr ⟨⟨hconjN, ?_⟩, (Subgroup.mem_normalizer_iff.mp (hLRn ha) g).mp hgLR⟩
  have e : (⟨a * g * a⁻¹, hconjN⟩ : ↥(Subgroup.normalizer (L : Set Γ))) =
      ⟨a, haN⟩ * ⟨g, hgN⟩ * ⟨a, haN⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]

namespace LRData

variable {L R : Subgroup Γ} (d : LRData L R)
include d

theorem not_dvd_card_of_le_kerLR {S : Subgroup Γ} (hS : S ≤ kerLR L R) : ¬ 3 ∣ Nat.card S :=
  not_dvd_card_of_no_order_three fun g hg h3 => by
    obtain ⟨⟨hgN, h1⟩, hgLR⟩ := mem_kerLR.mp (hS hg)
    exact d.eq_one_of_phi_one hgLR hgN h1 h3

theorem exists_centralizer_lift {W H : Subgroup Γ} (hW : W ≤ L ⊔ R) (hH : IsPGroup 3 H)
    (hHL : H ≤ Subgroup.normalizer (L : Set Γ)) (hHR : H ≤ Subgroup.normalizer (R : Set Γ))
    (hHW : H ≤ Subgroup.normalizer (W : Set Γ)) {x : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hx : x ∈ bar L W)
    (hxc : x ∈ Subgroup.centralizer
      (↑(bar L H) : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)))) :
    ∃ c ∈ W ⊓ Subgroup.centralizer (H : Set Γ),
      ∃ hc : c ∈ Subgroup.normalizer (L : Set Γ), phi L ⟨c, hc⟩ = x := by
  obtain ⟨w, hwN, hwW, rfl⟩ := mem_bar.mp hx
  have hLRn : H ≤ Subgroup.normalizer ((L ⊔ R : Subgroup Γ) : Set Γ) :=
    Sec14.le_normalizer_sup hHL hHR
  obtain ⟨c, hc, hfix⟩ := exists_fixed_coset (H := H) (N := W ⊓ kerLR L R) hH
    (d.not_dvd_card_of_le_kerLR inf_le_right)
    (fun h hh => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hHW hh, le_normalizer_kerLR hHL hHR hh⟩) (g := w) (by
      intro h hh
      have hwLR : w ∈ L ⊔ R := hW hwW
      have hhN := hHL hh
      refine ⟨W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHW hh) w).mp hwW) (W.inv_mem hwW), ?_⟩
      have hconjN : h * w * h⁻¹ * w⁻¹ ∈ Subgroup.normalizer (L : Set Γ) :=
        mul_mem (mul_mem (mul_mem hhN hwN) (inv_mem hhN)) (inv_mem hwN)
      refine mem_kerLR.mpr ⟨⟨hconjN, ?_⟩, mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hLRn hh) w).mp hwLR) (inv_mem hwLR)⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc _ (phi_mem_bar hhN hh)
      have e : (⟨h * w * h⁻¹ * w⁻¹, hconjN⟩ : ↥(Subgroup.normalizer (L : Set Γ))) =
          ⟨h, hhN⟩ * ⟨w, hwN⟩ * ⟨h, hhN⟩⁻¹ * ⟨w, hwN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group)
  have hcW : c ∈ W := by
    have := W.mul_mem hc.1 hwW
    simpa using this
  have hcN : c ∈ Subgroup.normalizer (L : Set Γ) := d.sup_le_normalizer (hW hcW)
  refine ⟨c, ⟨hcW, ?_⟩, hcN, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have := hfix h hh
    calc h * c = h * c * h⁻¹ * h := by group
      _ = c * h := by rw [this]
  · obtain ⟨⟨hcwN, hrk⟩, -⟩ := mem_kerLR.mp hc.2
    have e : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (L : Set Γ))) = ⟨c * w⁻¹, hcwN⟩ * ⟨w, hwN⟩ := by
      apply Subtype.ext
      simp
    rw [e, map_mul, hrk, one_mul]

theorem bar_inf_centralizer {W H : Subgroup Γ} (hW : W ≤ L ⊔ R) (hH : IsPGroup 3 H)
    (hHL : H ≤ Subgroup.normalizer (L : Set Γ)) (hHR : H ≤ Subgroup.normalizer (R : Set Γ))
    (hHW : H ≤ Subgroup.normalizer (W : Set Γ)) :
    bar L (W ⊓ Subgroup.centralizer (H : Set Γ)) = bar L W ⊓
      Subgroup.centralizer (↑(bar L H) : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, hg, ⟨hgW, hgC⟩, rfl⟩ := mem_bar.mp hx
    refine ⟨phi_mem_bar hg hgW, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨h, hh, hhH, rfl⟩ := mem_bar.mp hy
    have hcomm : h * g = g * h := Subgroup.mem_centralizer_iff.mp hgC h hhH
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  · rintro x ⟨hxW, hxC⟩
    obtain ⟨c, hcWC, hc, hcx⟩ := d.exists_centralizer_lift hW hH hHL hHR hHW hxW hxC
    exact mem_bar.mpr ⟨c, hc, hcWC, hcx⟩

theorem not_bar_le_core {W Q : Subgroup Γ} (hW : W ≤ L ⊔ R) (hQW : Q ≤ W)
    (h : ¬ Q ≤ pPrimeCoreOf 3 W) : ¬ bar L Q ≤ pPrimeCoreOf 3 (bar L W) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hle
  apply h
  set O := pPrimeCoreOf 3 (bar L W) with hO
  have hO3 : ¬ 3 ∣ Nat.card O := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 (bar L W)) h3
  set M : Subgroup Γ := W ⊓ (O.comap (phi L)).map (Subgroup.normalizer (L : Set Γ)).subtype
    with hM
  have hmem : ∀ g : Γ, g ∈ M ↔ g ∈ W ∧
      ∃ hg : g ∈ Subgroup.normalizer (L : Set Γ), phi L ⟨g, hg⟩ ∈ O := by
    intro g
    rw [hM, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hgW, y, hy, rfl⟩
      exact ⟨hgW, y.2, hy⟩
    · rintro ⟨hgW, hg, h⟩
      exact ⟨hgW, ⟨⟨g, hg⟩, h, rfl⟩⟩
  have hMW : M ≤ W := inf_le_left
  have hM3 : ¬ 3 ∣ Nat.card M := not_dvd_card_of_no_order_three fun g hg h3 => by
    obtain ⟨hgW, hgN, hgO⟩ := (hmem g).mp hg
    have : (phi L ⟨g, hgN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (L : Set Γ))) ^ 3 = 1 := Subtype.ext h3
      rw [this, map_one]
    exact d.eq_one_of_phi_one (hW hgW) hgN (eq_one_of_pow_three_of_not_dvd hO3 hgO this) h3
  have hWM : W ≤ Subgroup.normalizer (M : Set Γ) := by
    refine le_normalizer_of_conj_mem fun w hw g hg => ?_
    obtain ⟨hgW, hgN, hgO⟩ := (hmem g).mp hg
    have hwN : w ∈ Subgroup.normalizer (L : Set Γ) := d.sup_le_normalizer (hW hw)
    have hconjN : w * g * w⁻¹ ∈ Subgroup.normalizer (L : Set Γ) :=
      mul_mem (mul_mem hwN hgN) (inv_mem hwN)
    refine (hmem _).mpr ⟨W.mul_mem (W.mul_mem hw hgW) (W.inv_mem hw), hconjN, ?_⟩
    have e : phi L ⟨w * g * w⁻¹, hconjN⟩ =
        phi L ⟨w, hwN⟩ * phi L ⟨g, hgN⟩ * (phi L ⟨w, hwN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pPrimeCoreOf 3 (bar L W) (phi_mem_bar hwN hw)) _).mp hgO
  have hMcore : M ≤ pPrimeCoreOf 3 W :=
    le_pPrimeCoreOf hMW hWM ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hM3)
  intro q hq
  have hqN : q ∈ Subgroup.normalizer (L : Set Γ) := d.sup_le_normalizer (hW (hQW hq))
  exact hMcore ((hmem q).mpr ⟨hQW hq, hqN, hle (phi_mem_bar hqN hq)⟩)

theorem exists_lift_signalizer {A W H : Subgroup Γ} (hAp : IsPGroup 3 A)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) (hW : W ≤ L ⊔ R) (hHA : H ≤ A)
    (hAW : A ≤ Subgroup.normalizer (W : Set Γ))
    {V' : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))} (hV'W : V' ≤ bar L W)
    (hV'C : V' ≤ Subgroup.centralizer
      (↑(bar L H) : Set (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))))
    (hV' : V' ∈ invariantPiSubgroups ⊤ (bar L A) (piCompl 3)) (hV'c : V' = ⁅V', bar L A⁆) :
    ∃ V : Subgroup Γ, V ≤ W ⊓ Subgroup.centralizer (H : Set Γ) ∧
      V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧ V = ⁅V, A⁆ ∧ V' ≤ bar L V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV'3 : ¬ 3 ∣ Nat.card V' := fun h => (hV'.2.1 ⟨3, Nat.prime_three⟩ h) rfl
  set Vt : Subgroup Γ := W ⊓ (V'.comap (phi L)).map (Subgroup.normalizer (L : Set Γ)).subtype
    with hVt
  have hmemVt : ∀ g : Γ, g ∈ Vt ↔ g ∈ W ∧
      ∃ hg : g ∈ Subgroup.normalizer (L : Set Γ), phi L ⟨g, hg⟩ ∈ V' := by
    intro g
    rw [hVt, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hgW, y, hy, rfl⟩
      exact ⟨hgW, y.2, hy⟩
    · rintro ⟨hgW, hg, h⟩
      exact ⟨hgW, ⟨⟨g, hg⟩, h, rfl⟩⟩
  have hVtW : Vt ≤ W := inf_le_left
  have hAVt : A ≤ Subgroup.normalizer (Vt : Set Γ) := by
    refine le_normalizer_of_conj_mem fun a ha g hg => ?_
    obtain ⟨hgW, hgN, hgV⟩ := (hmemVt g).mp hg
    have haN := hAL ha
    have hconjN : a * g * a⁻¹ ∈ Subgroup.normalizer (L : Set Γ) :=
      mul_mem (mul_mem haN hgN) (inv_mem haN)
    refine (hmemVt _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hAW ha) g).mp hgW, hconjN, ?_⟩
    have e : phi L ⟨a * g * a⁻¹, hconjN⟩ =
        phi L ⟨a, haN⟩ * phi L ⟨g, hgN⟩ * (phi L ⟨a, haN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hV'.2.2 (phi_mem_bar haN ha)) _).mp hgV
  have hVt3 : ¬ 3 ∣ Nat.card Vt := not_dvd_card_of_no_order_three fun g hg h3 => by
    obtain ⟨hgW, hgN, hgV⟩ := (hmemVt g).mp hg
    have : (phi L ⟨g, hgN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (L : Set Γ))) ^ 3 = 1 := Subtype.ext h3
      rw [this, map_one]
    exact d.eq_one_of_phi_one (hW hgW) hgN (eq_one_of_pow_three_of_not_dvd hV'3 hgV this) h3
  set C : Subgroup Γ := Vt ⊓ Subgroup.centralizer (H : Set Γ) with hC
  have hCVt : C ≤ Vt := inf_le_left
  have hV'bar : V' ≤ bar L C := by
    intro v hv
    obtain ⟨c, ⟨hcW, hcC⟩, hc, hcv⟩ := d.exists_centralizer_lift hW (hAp.to_le hHA)
      (hHA.trans hAL) (hHA.trans hAR) (hHA.trans hAW) (hV'W hv) (hV'C hv)
    exact mem_bar.mpr ⟨c, hc, ⟨(hmemVt c).mpr ⟨hcW, hc, hcv ▸ hv⟩, hcC⟩, hcv⟩
  have hAC : A ≤ Subgroup.normalizer (C : Set Γ) := by
    refine le_normalizer_of_conj_mem fun a ha g hg => ?_
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hAVt ha) g).mp hg.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have h1 : h * a = a * h := hAc h (hHA hh) a ha
    have h2 : h * g = g * h := Subgroup.mem_centralizer_iff.mp hg.2 h hh
    have h3 : a⁻¹ * h = h * a⁻¹ := by
      calc a⁻¹ * h = a⁻¹ * (h * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * h) * a⁻¹ := by rw [h1]
        _ = h * a⁻¹ := by group
    calc h * (a * g * a⁻¹) = (h * a) * g * a⁻¹ := by group
      _ = a * (h * g) * a⁻¹ := by rw [h1]; group
      _ = a * (g * h) * a⁻¹ := by rw [h2]
      _ = a * g * (h * a⁻¹) := by group
      _ = a * g * (a⁻¹ * h) := by rw [← h3]
      _ = a * g * a⁻¹ * h := by group
  have hC3 : ¬ 3 ∣ Nat.card C := fun h => hVt3 (h.trans (Subgroup.card_dvd_of_le hCVt))
  have hle : ⁅C, A⁆ ≤ C :=
    CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized C A hAC
  refine ⟨⁅C, A⁆, ?_, ⟨le_top, ?_, ?_⟩, ?_, ?_⟩
  · exact le_inf ((hle.trans hCVt).trans hVtW) (hle.trans inf_le_right)
  · intro q hq
    have hq3 : ¬ 3 ∣ Nat.card (⁅C, A⁆ : Subgroup Γ) := fun h =>
      hC3 (h.trans (Subgroup.card_dvd_of_le hle))
    show (q : ℕ) ≠ 3
    intro h
    exact hq3 (h ▸ hq)
  · exact Subgroup.normalizer_commutator_ge_right C A
  · exact (CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three A C hAp hC3 hAC).symm
  · have hCN : C ≤ Subgroup.normalizer (L : Set Γ) :=
      ((hCVt.trans hVtW).trans hW).trans d.sup_le_normalizer
    rw [bar_commutator hCN hAL]
    calc V' = ⁅V', bar L A⁆ := hV'c
      _ ≤ ⁅bar L C, bar L A⁆ := Subgroup.commutator_mono hV'bar le_rfl

end LRData

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS
