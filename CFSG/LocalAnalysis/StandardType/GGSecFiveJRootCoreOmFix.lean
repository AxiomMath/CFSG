module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmDiag
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmEigen
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmFour
import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
import CFSG.ClassicalGroups.Orthogonal.Models
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LieType.SeitzGeneration.OrthNonsplitTools
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.SeitzGeneration.HyperLinear
import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
import CFSG.LieType.SeitzGeneration.OrthExLift
import CFSG.RankThree.PartOne.CTP.SeitzLinear
import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonal

theorem jcoreOm_fixed_mem {n : ℕ} {F : Type} [Field F]
    {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {a : Fin n → Fˣ}
    (hxa : ∀ v c, x v c = ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) * v c) {l : Fin n}
    (hl : a l = 1) (b : Bool) : plusVec n F l b ∈ fixedSpace x := by
  have hw : ∀ c : Fin n ⊕ Fin n, ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) = 1 →
      (Pi.single c 1 : Fin n ⊕ Fin n → F) ∈ fixedSpace x := by
    intro c hc
    have h := (jcoreOm_eigen_iff hxa 1 (Pi.single c 1)).mpr fun b hb => by
      have hbc : b ≠ c := by
        rintro rfl
        exact hb hc
      exact Pi.single_eq_of_ne hbc 1
    rw [one_smul] at h
    exact mem_fixedSpace.mpr h
  cases b
  · exact hw (.inr l) (by show (((a l)⁻¹ : Fˣ) : F) = 1; rw [hl, inv_one, Units.val_one])
  · exact hw (.inl l) (by show ((a l : Fˣ) : F) = 1; rw [hl, Units.val_one])

theorem jcoreOm_finrank_fixed {n : ℕ} {F : Type} [Field F]
    {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {a : Fin n → Fˣ}
    (hxa : ∀ v c, x v c = ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) * v c) :
    Module.finrank F (fixedSpace x) = 2 * Nat.card {k // a k = 1} := by
  classical
  rw [jcoreOm_finrank_eigen (W := fixedSpace x) hxa 1 fun v => by rw [mem_fixedSpace, one_smul],
    Nat.card_congr Equiv.subtypeSum, Nat.card_sum, two_mul]
  congr 1
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun k => Units.val_eq_one)
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun k =>
      (Units.val_eq_one (a := (a k)⁻¹)).trans inv_eq_one)

theorem jcoreOm_singular_three {n : ℕ} {F : Type} [Field F]
    {W : Submodule F (Fin n ⊕ Fin n → F)} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hW : ∀ l, l = i ∨ l = j ∨ l = k → ∀ b : Bool, plusVec n F l b ∈ W) :
    ∃ U : Submodule F W, Module.finrank F U = 3 ∧
      ∀ u ∈ U, ((quadPlus n F).comp W.subtype) u = 0 := by
  let P : ∀ l, l = i ∨ l = j ∨ l = k → HypPair ((quadPlus n F).comp W.subtype) := fun l hl =>
    { e := ⟨_, hW l hl true⟩
      f := ⟨_, hW l hl false⟩
      Q_e := (plusPair F l).Q_e
      Q_f := (plusPair F l).Q_f
      polar_ef := (plusPair F l).polar_ef }
  have hO : ∀ {l l'} (hl : l = i ∨ l = j ∨ l = k) (hl' : l' = i ∨ l' = j ∨ l' = k), l ≠ l' →
      (P l hl).Orth (P l' hl') := fun _ _ hll' =>
    ⟨(plusPair_orth hll').ee, (plusPair_orth hll').ef, (plusPair_orth hll').fe,
      (plusPair_orth hll').ff⟩
  exact exists_totallySingular_of_hypPairs (hO (Or.inl rfl) (Or.inr (Or.inl rfl)) hij)
    (hO (Or.inl rfl) (Or.inr (Or.inr rfl)) hik) (hO (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hjk)

theorem jcoreOm_eq_of_normal {G : Type*} [Group G] {S T : Subgroup G}
    (hSq : CFSG.IsQuasisimple ↥S) (hTq : CFSG.IsQuasisimple ↥T) (hTle : T ≤ S)
    (hTn : (T.subgroupOf S).Normal) : S ≤ T := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hSq hTn with h | h
  · exact Subgroup.subgroupOf_eq_top.mp h
  · exfalso
    obtain ⟨-, -, u, v, huv⟩ := hTq
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    have hv : (⟨v, hTle v.2⟩ : ↥S) ∈ Subgroup.center ↥S := h (Subgroup.mem_subgroupOf.mpr v.2)
    have hc' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hv ⟨u, hTle u.2⟩)
    have hc : u * v = v * u := Subtype.ext hc'
    exact huv (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc])

private theorem jcoreOm_eichler_mem_fixed {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {x : V ≃ₗ[F] V}
    (hx : OddOrderIsometry Q p x)
    (hT : ∃ U : Submodule F (fixedSpace x), Module.finrank F U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0)
    {u w : V} (hu : u ∈ fixedSpace x) (hw : w ∈ fixedSpace x) :
    eichler Q u w ∈ supportedFixedDerived Q x := by
  by_cases huw : QuadraticMap.polar Q u w = 0
  · obtain ⟨-, horth⟩ := hx.fixed_others
    have hcomm : eichler Q u w * x = x * eichler Q u w := by
      have h := eichler_conj hx.mem u w
      rw [mem_fixedSpace.mp hu, mem_fixedSpace.mp hw] at h
      calc eichler Q u w * x = (x * eichler Q u w * x⁻¹) * x := by rw [h]
        _ = x * eichler Q u w := by group
    have hS : eichler Q u w ∈ supportedBlock Q x (Polynomial.X - 1) := by
      refine mem_supportedBlock.mpr ⟨⟨eichler_mem_orthogonalGroup Q u w,
        Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩, fun r hr => ?_⟩
      refine eichler_apply_of_polar_eq_zero ?_ ?_
      · rw [QuadraticMap.polar_comm]; exact horth u hu r hr
      · rw [QuadraticMap.polar_comm]; exact horth w hw r hr
    refine mem_supportedFixedDerived.mpr ⟨hS, ?_⟩
    have hres : (restrictFixed Q x ⟨eichler Q u w, hS⟩ : fixedSpace x ≃ₗ[F] fixedSpace x) =
        eichler (Q.comp (fixedSpace x).subtype) ⟨u, hu⟩ ⟨w, hw⟩ := by
      refine LinearEquiv.ext fun z => Subtype.ext ?_
      rw [coe_restrictFixed, CFSG.LieType.SeitzGeneration.OrthNS.eichler_comp_subtype_apply]
    rw [hres, (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure
      hx.polarBilin_fixed_nondegenerate hT).1]
    exact eichler_mem_elementaryGroup _ _ _
  · rw [eichler_of_polar_ne_zero huw]
    exact Subgroup.one_mem _

theorem jcoreOm_fixed_large {n p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hx : OddOrderIsometry (quadPlus n F) p x) {a : Fin n → Fˣ}
    (hxa : ∀ v c, x v c = ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) * v c)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hai : a i = 1) (haj : a j = 1)
    (hak : a k = 1) {T : Subgroup ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))}
    (hTq : CFSG.IsQuasisimple ↥T) (hTle : T ≤ supportedFixedDerived (quadPlus n F) x)
    (hTn : (T.subgroupOf (supportedFixedDerived (quadPlus n F) x)).Normal) :
    JCoreOmRootPair n F T := by
  classical
  have hT := jcoreOm_singular_three (W := fixedSpace x) hij hik hjk fun l hl b => by
    rcases hl with rfl | rfl | rfl
    · exact jcoreOm_fixed_mem hxa hai b
    · exact jcoreOm_fixed_mem hxa haj b
    · exact jcoreOm_fixed_mem hxa hak b
  have hST := jcoreOm_eq_of_normal (hx.isQuasisimple_supportedFixedDerived hT) hTq hTle hTn
  refine ⟨i, j, hij, true, true, fun c => ⟨?_, ?_⟩⟩
  · exact hST (jcoreOm_eichler_mem_fixed hx hT (jcoreOm_fixed_mem hxa haj _)
      (Submodule.smul_mem _ c (jcoreOm_fixed_mem hxa hai _)))
  · exact hST (jcoreOm_eichler_mem_fixed hx hT (jcoreOm_fixed_mem hxa hai _)
      (Submodule.smul_mem _ c (jcoreOm_fixed_mem hxa haj _)))

theorem jcoreOm_fixed {n p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hx : OddOrderIsometry (quadPlus n F) p x) {a : Fin n → Fˣ}
    (hxa : ∀ v c, x v c = ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) * v c)
    (hL : FixedLayerListed (quadPlus n F) x)
    {T : Subgroup ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))}
    (hTq : CFSG.IsQuasisimple ↥T) (hTle : T ≤ supportedFixedDerived (quadPlus n F) x)
    (hTn : (T.subgroupOf (supportedFixedDerived (quadPlus n F) x)).Normal) :
    JCoreOmRootPair n F T := by
  classical
  have hdim := jcoreOm_finrank_fixed hxa
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hdim
  have h3 := hL.1
  by_cases hm : 2 < (Finset.univ.filter fun l => a l = 1).card
  · obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hk
    exact jcoreOm_fixed_large hx hxa hij hik hjk hi hj hk hTq hTle hTn
  · obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp
      (show (Finset.univ.filter fun l => a l = 1).card = 2 by omega)
    have hmem : ∀ l, a l = 1 ↔ l = i ∨ l = j := fun l => by
      simpa using Finset.ext_iff.mp hs l
    exact jcoreOm_fixed_four hF hx hxa hij ((hmem i).mpr (Or.inl rfl))
      ((hmem j).mpr (Or.inr rfl)) (fun k hk => (hmem k).mp hk) hTq hTle hTn

end CFSG.StandardType

end
