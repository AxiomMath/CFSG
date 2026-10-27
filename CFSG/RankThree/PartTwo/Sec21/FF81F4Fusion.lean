module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Ord3
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Node
public import Certificates.Certificate799603
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLSp6Facts
public import CFSG.Adapters.LieModelSimple
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore
public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSp6
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.StandardType CFSG.Assembly
open CFSG.SeitzReduction.F4Pilot CFSG.StandardType.TableBF4TwoInputs
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Model

theorem card_model_sp6 {H : Type} [Group H] (hH : StatedClassicalModel H .PSp 3 2 1) :
    Nat.card H = 1451520 := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hH).2.2.1 rfl]
  norm_num [CFSG.Open.ordBC, Finset.prod_Icc_succ_top]

theorem isQuasisimple_of_model_sp6 {H : Type} [Group H] (hH : StatedClassicalModel H .PSp 3 2 1) :
    CFSG.IsQuasisimple H := by
  haveI : IsSimpleGroup H := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hH
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.isQuasisimple_of_simple_nonabelian ?_
  intro hcomm
  have hcen : Subgroup.center H = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun g => Subgroup.mem_center_iff.2 fun h => hcomm h g
  rw [center_eq_bot_of_sp6Model hH] at hcen
  have h1 : Nat.card H = 1 := by
    rw [← Subgroup.card_top, ← hcen, Subgroup.card_bot]
  rw [card_model_sp6 hH] at h1
  omega

end Model

@[expose] def K12P (x : F42C) : Prop :=
  ∀ K : Subgroup F42C, Subgroup.zpowers x ⊔ K = Subgroup.centralizer ({x} : Set F42C) →
    StatedClassicalModel ↥K .PSp 3 2 1 → ∀ x₁ ∈ K, ∀ x₂ ∈ K, (∃ c : F42C, c * x * c⁻¹ = x₁) →
      (∃ c : F42C, c * x * c⁻¹ = x₂) → ∃ k ∈ K, k * x₁ * k⁻¹ = x₂

theorem K12P_aut (α : F42C ≃* F42C) {x : F42C} (h : K12P x) : K12P (α x) := by
  intro K hK hm x₁ hx₁ x₂ hx₂ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
  set K₀ : Subgroup F42C := K.map α.symm.toMonoidHom with hK₀
  have hz : (Subgroup.zpowers (α x)).map α.symm.toMonoidHom = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    simp
  have hcen : (Subgroup.centralizer ({α x} : Set F42C)).map α.symm.toMonoidHom =
      Subgroup.centralizer ({x} : Set F42C) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h'
      have := congrArg α.symm h'
      simpa using this
    · intro h'
      have := congrArg α h'
      simpa using this
  have hK₀x : Subgroup.zpowers x ⊔ K₀ = Subgroup.centralizer ({x} : Set F42C) := by
    rw [← hz, ← hcen, ← hK, Subgroup.map_sup]
  have hm₀ : StatedClassicalModel ↥K₀ .PSp 3 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      (Subgroup.equivMapOfInjective K α.symm.toMonoidHom α.symm.injective) hm
  obtain ⟨k, hk, hkk⟩ := h K₀ hK₀x hm₀ (α.symm x₁) ⟨x₁, hx₁, rfl⟩ (α.symm x₂) ⟨x₂, hx₂, rfl⟩
    ⟨α.symm c₁, by rw [← hc₁]; simp⟩ ⟨α.symm c₂, by rw [← hc₂]; simp⟩
  refine ⟨α k, ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hk
    simpa using hy
  · have := congrArg α hkk
    simpa using this

section Fusion


theorem card_cen_of_model {x : F42C} (hx : orderOf x = 3) {K : Subgroup F42C}
    (hKx : Subgroup.zpowers x ⊔ K = Subgroup.centralizer ({x} : Set F42C))
    (hKm : StatedClassicalModel ↥K .PSp 3 2 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set F42C)) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
  haveI : Finite F42C := finite_adjF
  have hKc : K ≤ Subgroup.centralizer ({x} : Set F42C) := le_sup_right.trans hKx.le
  have hKz : K ≤ Subgroup.centralizer (Subgroup.zpowers x : Set F42C) :=
    hKc.trans (centralizer_singleton_eq_zpowers (K := ZMod 2) x).le
  have hxK : x ∉ K := by
    intro hxK
    have hcen : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (hKc g.2)
    rw [center_eq_bot_of_sp6Model hKm, Subgroup.mem_bot] at hcen
    have h1 : x = 1 := congrArg Subtype.val hcen
    rw [h1, orderOf_one] at hx
    omega
  have h3 : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hinf : Subgroup.zpowers x ⊓ K = ⊥ := by
    have hd : Nat.card ↥(Subgroup.zpowers x ⊓ K) ∣ 3 := by
      rw [← h3]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : Subgroup.zpowers x ⊓ K = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h3])
      have : x ∈ Subgroup.zpowers x ⊓ K := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxK this.2
  have hc := card_sup_eq_mul_of_le_centralizer hKz hinf
  rw [hKx] at hc
  rw [hc, h3, card_model_sp6 hKm]
  norm_num

theorem K12P_rA : K12P rAE := by
  intro K hKx hKm x₁ hx₁ x₂ hx₂ h₁ h₂
  have hKc : K ≤ Subgroup.centralizer ({rAE} : Set F42C) := le_sup_right.trans hKx.le
  have hq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_model_sp6 hKm
  have hz1 : Subgroup.zpowers rAE ≤ Subgroup.centralizer (K : Set F42C) :=
    Subgroup.le_centralizer_iff.2
      (hKc.trans (centralizer_singleton_eq_zpowers (K := ZMod 2) rAE).le)
  have hle : Subgroup.zpowers rAE ⊔ K ≤ Subgroup.normalizer (K : Set F42C) :=
    sup_le (hz1.trans (Subgroup.centralizer_le_normalizer (K : Set F42C))) Subgroup.le_normalizer
  have hnorm : ∀ c ∈ Subgroup.centralizer ({rAE} : Set F42C), ∀ d ∈ K, c * d * c⁻¹ ∈ K := by
    intro c hc d hd
    rw [← hKx] at hc
    exact ((Subgroup.mem_normalizer_iff.1 (hle hc)) d).1 hd
  have hD : CFSG.StandardType.SmallExc.F4Two.EltHyp rAE K := ⟨hKc, hnorm, hq⟩
  have hKL : K = C3Levi (ZMod 2) :=
    CFSG.StandardType.SmallExc.F4Two.eq_C3Levi_of_eltHyp (K := ZMod 2) (by simp) hD
  subst hKL
  exact Certificates.certificate799603 x₁ hx₁ x₂ hx₂ (isConj_iff.2 h₁) (isConj_iff.2 h₂)

theorem K12C {x : F42C}
    (hx : orderOf x = 3) : K12P x := by
  intro K hKx hKm x₁ hx₁ x₂ hx₂ h₁ h₂
  have hcard := card_cen_of_model hx hKx hKm
  have hnd : ¬ 3 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set F42C)) := by
    rw [hcard]
    norm_num
  have hα : ∃ α : F42C ≃* F42C, α rAE = x := by
    rcases order_three_AB hx hnd with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine ⟨MulAut.conj c⁻¹, ?_⟩
      rw [MulAut.conj_apply, ← hc]
      group
    · haveI : CharP (ZMod 2) ReeTag.F4.prime := inferInstanceAs (CharP (ZMod 2) 2)
      obtain ⟨c', hc'⟩ := isConj_iff.1 phi_link_C
      refine ⟨(ReeTag.F4.finiteExceptionalAut (ZMod 2)).trans (MulAut.conj (c⁻¹ * c')), ?_⟩
      rw [MulEquiv.trans_apply, MulAut.conj_apply]
      calc c⁻¹ * c' * (ReeTag.F4.finiteExceptionalAut (ZMod 2)) rAE * (c⁻¹ * c')⁻¹
          = c⁻¹ * (c' * (ReeTag.F4.finiteExceptionalAut (ZMod 2)) rAE * c'⁻¹) * c := by group
        _ = c⁻¹ * rBE * c := by rw [hc']
        _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [hc]
        _ = x := by group
  obtain ⟨α, hα⟩ := hα
  have hK := K12P_aut α K12P_rA
  rw [hα] at hK
  exact hK K hKx hKm x₁ hx₁ x₂ hx₂ h₁ h₂

end Fusion

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
