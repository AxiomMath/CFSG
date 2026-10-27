module

public import CFSG.LocalAnalysis.StandardType.GGPresentationWeyl
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LieType.Universal.SymplecticRoots.Weyl
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CoxeterSystem
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  TauCeti.GLSymplecticFin CFSG.Assembly.LowTwoRank

section CharTwo

variable {F : Type} [Field F]

theorem sp_neg_eq_self_of_two (h2 : (2 : F) = 0) (c : F) : -c = c := by
  linear_combination (-c) * h2

theorem sp_units_neg_one_eq_one_of_two (h2 : (2 : F) = 0) : (-1 : Fˣ) = 1 :=
  Units.ext (by simpa using sp_neg_eq_self_of_two h2 (1 : F))

theorem sp_ite_neg_one_of_two (h2 : (2 : F) = 0) {ι : Type*} (x k : ι) [Decidable (x = k)] :
    (if x = k then (-1 : F) else 1) = 1 := by
  split_ifs
  · exact sp_neg_eq_self_of_two h2 1
  · rfl

end CharTwo

section Involution

variable (m : ℕ) {F : Type} [Field F]

theorem spWeylRep_mul_self (h2 : (2 : F) = 0) (k : Fin m) : weylRep m F k * weylRep m F k = 1 := by
  have hu := sp_units_neg_one_eq_one_of_two h2
  rw [weylRep_eq, ← map_mul, ← pow_two]
  by_cases h : k.val + 1 < m
  · rw [weylElt_of_lt m F h, shortWeyl_sq]
    have e : (fun x => if x = k then (-1 : Fˣ) else if x = (⟨k.val + 1, h⟩ : Fin m) then (-1)⁻¹
        else 1) = 1 := by
      funext x
      simp only [hu, inv_one, ite_self, Pi.one_apply]
    rw [e, map_one, inv_one, map_one]
  · rw [weylElt_of_not_lt m F h, longWeyl_sq, hu, Pi.mulSingle_one, map_one, inv_one, map_one]

@[expose] noncomputable def spWeylLift (h2 : (2 : F) = 0) :
    (coxeterMatrix (isFiniteType_cartanC m)).Group →* StatedSp m F :=
  (coxeterMatrix (isFiniteType_cartanC m)).toCoxeterSystem.lift
    ⟨weylRep m F, isLiftable_of_braid _ (spWeylRep_mul_self m h2) (isCTGroupDatum m F).braid⟩

theorem spWeylLift_simple (h2 : (2 : F) = 0) (k : Fin m) :
    spWeylLift m h2 ((coxeterMatrix (isFiniteType_cartanC m)).toCoxeterSystem.simple k) =
      weylRep m F k :=
  (coxeterMatrix (isFiniteType_cartanC m)).toCoxeterSystem.lift_apply_simple _ k

theorem spWeylLift_spec (h2 : (2 : F) = 0) :
    GGWeylLift (Symplectic.rootDatum m F) (spWeylLift m h2) :=
  ggWeylLiftOf_spec (D := Symplectic.rootDatum m F) (Symplectic.isCTGroupDatum m F)
    (spWeylRep_mul_self m h2)

end Involution

section Conj

variable {m : ℕ} {F : Type} [Field F]

private theorem spWeylElt_conj_two (h2 : (2 : F) = 0) (k : Fin m) (r : RootSubgroupIndex m)
    (c : F) : ∃ r' : RootSubgroupIndex m,
      weylElt m F k * r.hom (Multiplicative.ofAdd c) * (weylElt m F k)⁻¹ =
        r'.hom (Multiplicative.ofAdd c) ∧ stdVec r' = stdRefl m k (stdVec r) := by
  have hs : ∀ x : Fin m, (if x = k then (-1 : F) else 1) = 1 :=
    fun x => sp_ite_neg_one_of_two h2 x k
  have hn : -c = c := sp_neg_eq_self_of_two h2 c
  by_cases h : k.val + 1 < m
  · rw [weylElt_of_lt m F h, stdRefl_of_lt m h]
    have hk := ne_succ m h
    cases r with
    | positiveLong a =>
      refine ⟨.positiveLong (Equiv.swap k ⟨k.val + 1, h⟩ a), ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
          toAdd_ofAdd]
        exact shortWeyl_conj_positiveLong hk a _
      · simp only [stdVec]
        rw [Pi.smul_comp, single_comp_swap]
    | negativeLong a =>
      refine ⟨.negativeLong (Equiv.swap k ⟨k.val + 1, h⟩ a), ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
          toAdd_ofAdd]
        exact shortWeyl_conj_negativeLong hk a _
      · simp only [stdVec]
        rw [Pi.neg_comp, Pi.smul_comp, single_comp_swap]
    | difference a b hab =>
      refine ⟨.difference _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab), ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]
        rw [shortWeyl_conj_difference hk hab, hs a, hs b, one_mul, one_mul]
      · simp only [stdVec]
        rw [Pi.sub_comp, single_comp_swap, single_comp_swap]
    | positiveSum a b hab =>
      refine ⟨.short .positiveSum _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab.ne), ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_short, ShortRootFamily.hom_positiveSum,
          positiveSumShortRootHom_apply, RootSubgroupIndex.hom_positiveSum, toAdd_ofAdd]
        rw [shortWeyl_conj_positiveSum hk hab.ne, hs a, hs b, one_mul, one_mul]
      · rw [stdVec_short_positiveSum]
        simp only [stdVec]
        rw [Pi.add_comp, single_comp_swap, single_comp_swap]
    | negativeSum a b hab =>
      refine ⟨.short .negativeSum _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab.ne), ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_short, ShortRootFamily.hom_negativeSum,
          negativeSumShortRootHom_apply, RootSubgroupIndex.hom_negativeSum, toAdd_ofAdd]
        rw [shortWeyl_conj_negativeSum hk hab.ne, hs a, hs b, one_mul, one_mul]
      · rw [stdVec_short_negativeSum]
        simp only [stdVec]
        rw [Pi.neg_comp, Pi.add_comp, single_comp_swap, single_comp_swap]
  · rw [weylElt_of_not_lt m F h, stdRefl_of_not_lt m h]
    have hmax : ∀ a : Fin m, a ≠ k → a.val < k.val := fun a ha => by
      have := Fin.val_ne_of_ne ha
      omega
    cases r with
    | positiveLong a =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.negativeLong k, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_positiveLong, RootSubgroupIndex.hom_negativeLong,
            positiveLongRootTransvectionHom_apply, negativeLongRootTransvectionHom_apply,
            toAdd_ofAdd]
          rw [positiveLongRootWeylElement_inv,
            positiveLongRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv k c, hn]
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
      · refine ⟨.positiveLong a, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
            toAdd_ofAdd]
          exact longWeyl_conj_positiveLong_of_ne ha.symm _
        · funext x
          simp only [stdVec, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
    | negativeLong a =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.positiveLong k, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_positiveLong, RootSubgroupIndex.hom_negativeLong,
            positiveLongRootTransvectionHom_apply, negativeLongRootTransvectionHom_apply,
            toAdd_ofAdd]
          rw [positiveLongRootWeylElement_inv,
            positiveLongRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv k c, hn]
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
      · refine ⟨.negativeLong a, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
            toAdd_ofAdd]
          exact longWeyl_conj_negativeLong_of_ne ha.symm _
        · funext x
          simp only [stdVec, Pi.neg_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
    | difference a b hab =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.short .negativeSum k b hab, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_short,
            ShortRootFamily.hom_negativeSum, differenceShortRootHom_apply,
            negativeSumShortRootHom_apply, toAdd_ofAdd]
          rw [longWeyl_conj_difference_left hab c, hn]
        · rw [stdVec_short_negativeSum]
          funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.short .positiveSum a k hab, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_short,
            ShortRootFamily.hom_positiveSum, differenceShortRootHom_apply,
            positiveSumShortRootHom_apply, toAdd_ofAdd]
          rw [longWeyl_conj_difference_right hab c, hn]
        · rw [stdVec_short_positiveSum]
          funext x
          simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
      · refine ⟨.difference a b hab, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]
          exact longWeyl_conj_difference_of_ne hab ha.symm hb.symm _
        · funext x
          simp only [stdVec, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
    | positiveSum a b hab =>
      have ha : a ≠ k := fun e => by
        have := hmax b (fun e' => by subst e e'; exact lt_irrefl _ hab)
        have : a.val < b.val := hab
        omega
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.difference a k hab.ne, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_positiveSum,
            differenceShortRootHom_apply, positiveSumShortRootHom_apply, toAdd_ofAdd]
          exact longWeyl_conj_positiveSum_right hab.ne _
        · funext x
          simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
      · refine ⟨.positiveSum a b hab, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_positiveSum, positiveSumShortRootHom_apply,
            toAdd_ofAdd]
          exact longWeyl_conj_positiveSum_of_ne hab.ne ha hb.symm _
        · funext x
          simp only [stdVec, Pi.add_apply, Pi.single_apply]
          split_ifs <;> simp_all
    | negativeSum a b hab =>
      have ha : a ≠ k := fun e => by
        have := hmax b (fun e' => by subst e e'; exact lt_irrefl _ hab)
        have : a.val < b.val := hab
        omega
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.difference k a hab.ne.symm, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_negativeSum,
            differenceShortRootHom_apply, negativeSumShortRootHom_apply, toAdd_ofAdd]
          exact longWeyl_conj_negativeSum_right hab.ne _
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
      · refine ⟨.negativeSum a b hab, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_negativeSum, negativeSumShortRootHom_apply,
            toAdd_ofAdd]
          exact longWeyl_conj_negativeSum_of_ne hab.ne ha hb.symm _
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.single_apply]
          split_ifs <;> simp_all

end Conj

section StandardCopy

variable {m : ℕ} {F : Type} [Field F]

theorem spWeylRep_conj_elt (h2 : (2 : F) = 0) (k : Fin m) {γ : Fin m → ℤ}
    {r : RootSubgroupIndex m} (hr : stdVec r = toStd m γ) (c : F) :
    ∃ r' : RootSubgroupIndex m, stdVec r' = toStd m (weylAction (isFiniteType_cartanC m)
        ((coxeterMatrix (isFiniteType_cartanC m)).toCoxeterSystem.simple k) γ) ∧
      weylRep m F k * elt r c * (weylRep m F k)⁻¹ = elt r' c := by
  obtain ⟨r', he, hs⟩ := spWeylElt_conj_two h2 k r c
  refine ⟨r', ?_, ?_⟩
  · rw [hs, hr, weylAction_simple, toStd_reflection]
  · rw [weylRep_eq, elt, elt, ← map_inv, ← map_mul, ← map_mul, he]

theorem spWeylLift_conj_elt (h2 : (2 : F) = 0)
    (w : (coxeterMatrix (isFiniteType_cartanC m)).Group) :
    ∀ {γ : Fin m → ℤ} {r : RootSubgroupIndex m}, stdVec r = toStd m γ → ∀ c : F,
      ∃ r' : RootSubgroupIndex m, stdVec r' = toStd m (weylAction (isFiniteType_cartanC m) w γ) ∧
        spWeylLift m h2 w * elt r c * (spWeylLift m h2 w)⁻¹ = elt r' c := by
  induction w using (coxeterMatrix (isFiniteType_cartanC m)).toCoxeterSystem.simple_induction_left
    with
  | one =>
    intro γ r hr c
    exact ⟨r, by rw [map_one, Module.End.one_apply, hr], by rw [map_one, one_mul, inv_one, mul_one]⟩
  | mul_simple_left w k ih =>
    intro γ r hr c
    obtain ⟨r₁, hr₁, he₁⟩ := ih hr c
    obtain ⟨r₂, hr₂, he₂⟩ := spWeylRep_conj_elt h2 k hr₁ c
    refine ⟨r₂, by rw [hr₂, weylAction_mul_apply], ?_⟩
    rw [map_mul, spWeylLift_simple, ← he₂, ← he₁]
    group

theorem spWeylLift_standardCopy (h2 : (2 : F) = 0) :
    GGStandardCopy (Symplectic.rootDatum m F) (spWeylLift m h2) := by
  refine ⟨spWeylLift_spec m h2, ?_⟩
  intro w α hα hfix z hz
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots (n := m) hα
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (F := F) hr).mp hz
  have key : ∀ w' : (coxeterMatrix (isFiniteType_cartanC m)).Group,
      weylAction (isFiniteType_cartanC m) w' α = α →
        spWeylLift m h2 w' * elt r c * (spWeylLift m h2 w')⁻¹ = elt r c := by
    intro w' hw'
    obtain ⟨r', hr', he⟩ := spWeylLift_conj_elt h2 w' hr c
    rw [hw', ← hr] at hr'
    obtain rfl := stdVec_injective hr'
    exact he
  exact key w hfix

end StandardCopy
