module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcE7Inndiag
import CFSG.LieType.AlgebraicGroups.E7RationalFourFixedPrime
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSL
import CFSG.LieType.SeitzGeneration.OrdinaryOuterLocal
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration


theorem exists_fixed_rElement_four_e7 {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    (E : Subgroup (MulAut ↥(adjointGroup .E7 K))) (hE : CFSG.Open.IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) :
    ∃ y : ↥(adjointGroup .E7 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      ∀ e ∈ E, e y = y := by
  classical
  rcases exists_fixed_rElement_four_e7_or_nontoral hK E hE h4 with h |
    ⟨x₁, x₂, hx₁, hx₂, hc, h1, h2, h12, hι₁, hι₂, hfix, -⟩
  · exact h
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hpdef
  have : CharP K p := ringChar.charP K
  obtain ⟨e, hpp, hcardK⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hpp⟩
  have hcardK' : Nat.card K = p ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, hcardK]
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius _ p e with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, hcardK']
  set ι := baseChangeGL (τ := .E7) (algebraMap K (AlgebraicClosure K)) with hιdef
  have hιF : ∀ w : ModGL .E7 K, Units.map (entrywiseHom Fr) (ι w) = ι w := fun w => by
    have hcomp : Fr.comp (algebraMap K (AlgebraicClosure K)) =
        algebraMap K (AlgebraicClosure K) := RingHom.ext fun c => by
      change Fr (algebraMap K (AlgebraicClosure K) c) = algebraMap K (AlgebraicClosure K) c
      rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h' : Units.map (entrywiseHom Fr) (ι w) = baseChangeGL Fr (ι w) := Units.ext rfl
    rw [h', hιdef, baseChangeGL_baseChangeGL, hcomp]
  have : Finite (ModGL .E7 K) := finite_modGL
  have hsq₁ : x₁ * x₁ = 1 := by rw [← pow_two]; exact hx₁
  have hsq₂ : x₂ * x₂ = 1 := by rw [← pow_two]; exact hx₂
  obtain ⟨hmem, -, hEA, hcard⟩ :=
    CFSG.GH74.GLS.Stage1.Main.four_of_invols hsq₁ hsq₂ hc h1 h2 h12
  have hE₀ : CFSG.Open.IsElemAbelian 2 (zpowers x₁ ⊔ zpowers x₂) :=
    CFSG.Open.isElemAbelian_of_isElementaryAbelian
  have hE' : CFSG.Open.IsElemAbelian 2 ((zpowers x₁ ⊔ zpowers x₂).map ι) := hE₀.map ι
  have hE'4 : Nat.card ((zpowers x₁ ⊔ zpowers x₂).map ι) = 4 := by
    rw [Subgroup.card_map_of_injective (baseChangeGL_injective _), hcard]
  have hE'R : (zpowers x₁ ⊔ zpowers x₂).map ι ≤ adjointGroup .E7 (AlgebraicClosure K) ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨?_, hιF w⟩
    rcases hmem w hw with rfl | rfl | rfl | rfl
    · rw [map_one]
      exact one_mem _
    · exact hι₁
    · exact hι₂
    · rw [map_mul]
      exact mul_mem hι₁ hι₂
  obtain ⟨u, huG, huord, huF, hucomm⟩ :=
    CFSG.LieType.AlgebraicGroups.e7_rational_four_fixed_prime hK Fr hFr _ hE' hE'4 hE'R
  have hodd : Odd (orderOf u) := by
    rw [huord]
    exact hpp.odd_of_ne_two hK
  obtain ⟨y, hyC, rfl⟩ :=
    CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E7 Fr hFr huG huF
      fun _ => hodd
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  have hcomm : ∀ x : ModGL .E7 K, x ∈ zpowers x₁ ⊔ zpowers x₂ → Commute y x := fun x hx => by
    have h := hucomm (ι x) ⟨x, hx, rfl⟩
    exact hιinj (by rw [map_mul, map_mul]; exact h.eq)
  refine ⟨⟨y, hyC⟩, fun hy => ?_, ⟨1, ?_⟩, hfix ⟨y, hyC⟩
    (hcomm x₁ (mem_sup_left (mem_zpowers x₁))) (hcomm x₂ (mem_sup_right (mem_zpowers x₂)))⟩
  · have hy1 : y = 1 := congrArg Subtype.val hy
    rw [hy1, map_one, orderOf_one] at huord
    exact hpp.one_lt.ne huord
  · apply Subtype.ext
    apply hιinj
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, map_pow, map_one]
    rw [hpdef, ← huord]
    exact pow_orderOf_eq_one _

theorem exists_normalized_rSubgroup_four_e7 {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (E : Subgroup (MulAut ↥(adjointGroup .E7 K)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    ∃ R : Subgroup ↥(adjointGroup .E7 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      ∀ e ∈ E, R.map e.toMonoidHom = R := by
  obtain ⟨y, hy1, ⟨n, hyn⟩, hyE⟩ := exists_fixed_rElement_four_e7 hK E hE h4
  refine ⟨zpowers y, fun h => hy1 ?_, ?_, fun e he => ?_⟩
  · have hmem : y ∈ zpowers y := mem_zpowers y
    rwa [h, Subgroup.mem_bot] at hmem
  · rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyn, one_zpow]
  · rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hyE e he]

theorem seitzFour_e7 :
    SeitzFour fun X _ => ∃ p f : ℕ, p ≠ 2 ∧ CFSG.Models.LieModel X .E7 0 p f := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 _
  obtain ⟨p, f, hp2, hm⟩ := hP
  obtain ⟨K, _, _, hK2, ⟨φ⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K ≠ 2 ∧
      Nonempty (↥L ≃* ↥(adjointGroup .E7 K)) := by
    obtain ⟨hadm, hU⟩ :=
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        hm).chevalleyExceptionalModel (by decide)
    obtain ⟨K, _, _, hK, he⟩ := nonempty_mulEquiv_adjointGroup .E7 hU
    have : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        hadm.1 hadm.2.1 hK
    exact ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp2, he⟩
  set A := E.map (MulAut.conjNormal : G →* MulAut ↥L)
  have hA : CFSG.Open.IsElemAbelian 2 A := hE.map _
  have hA4 : Nat.card A = 4 := by
    rw [Subgroup.card_map_of_injective (conjNormal_injective_of_centralizer_eq_bot hC), h4]
  set A' := A.map (MulAut.congr φ).toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian 2 A' := hA.map _
  have hA'4 : Nat.card A' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hA4]
  obtain ⟨R, hR, hRr, hER⟩ := exists_normalized_rSubgroup_four_e7 hK2 A' hA' hA'4
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have : IsSimpleGroup ↥(adjointGroup .E7 K) := φ.symm.isSimpleGroup
  have hPA : PlaneGen A := (planeGen_map_congr φ A).1
    (planeGen_of_normalized_rSubgroup_adjointGroup hK2 A' hA' hA'4 R hR hRr hER)
  exact iSup_centralizer_eq_of_seitzHyperGamma hC h4
    ((planeGen_iff_seitzHyperGamma Nat.prime_two (by rw [hA4]; norm_num)).1 hPA)

end CFSG.LocalAnalysis.WeakClosure81
