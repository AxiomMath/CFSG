
module

public import CFSG.Quasithin.H13.J4CoreBase

public import CFSG.Quasithin.H13.J4Words
public import CFSG.Certificates.ExtraspecialNormalForm
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public meta import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4CoreInputs
public import Certificates.Certificate7012
public import CFSG.Quasithin.H13.J4WordsInputs
public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open CFSG.Certificates.ExtraspecialNF

section NF

variable {G : Type*} [Group G] {n : ℕ} {z : G} {q : Fin n → G} {c : Fin n → Fin n → ZMod 2}

end NF

theorem pChecks_eq : pChecks = true :=
  Certificates.certificate7012

theorem prRep_rConjN (i : ℕ) :
    PrRep (rConjN i) (rPairs[i]?.getD prOne) := by
  unfold rConjN
  split_ifs with hi
  · rw [show rPairs[i]? = some (rConjOf (uvPairsOf basePairs) (coreBasisConjugators.getD i []))
      by simp [rPairs, hi], Option.getD_some]
    exact prRep_rConj ⟨i, hi⟩
  · rw [show rPairs[i]? = none by simp [rPairs]; omega, Option.getD_none]
    exact PrRep.one

theorem prRep_rProd (l : List ℕ) :
    PrRep (rProd l) (rProdPair l) := by
  unfold rProd rProdPair
  suffices ∀ (acc : Pr) (g : GL (Fin 112) (ZMod 2)), PrRep g acc →
      PrRep (g * (l.map rConjN).prod)
        (l.foldl (fun acc i => prMul acc (rPairs[i]?.getD prOne)) acc) by
    simpa using this prOne 1 PrRep.one
  induction l with
  | nil => intro acc g hg; simpa using hg
  | cons i l ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih _ _ (hg.mul (prRep_rConjN i))

theorem prRep_qProd (l : List ℕ) :
    PrRep (qProd l) (qProdPair l) := by
  unfold qProd qProdPair
  suffices ∀ (acc : Pr) (g : GL (Fin 112) (ZMod 2)), PrRep g acc →
      PrRep (g * (l.map fun a => rProd (qIdx.getD a [])).prod)
        (l.foldl (fun acc a => prMul acc (rProdPair (qIdx.getD a []))) acc) by
    simpa using this prOne 1 PrRep.one
  induction l with
  | nil => intro acc g hg; simpa using hg
  | cons a l ih =>
    intro acc g hg
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih _ _ (hg.mul (prRep_rProd _))

theorem pChecks_spec :
    (∀ a : Fin 12, qGen a * qGen a = 1) ∧
    (∀ a b : Fin 12, qGen a * qGen b = qGen b * qGen a * t ^ (cMat a b).val) ∧
    ∀ i : Fin 12, rConj i =
      (if (rExpr.getD i (0, [])).1 = 1 then t else 1) * qProd (rExpr.getD i (0, [])).2 := by
  have h := pChecks_eq
  simp only [pChecks, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hq : ∀ a : Fin 12, PrRep (qGen a)
      (((List.range 12).map fun a => rProdPair (qIdx.getD a [])).getD a prOne) := by
    intro a
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    exact prRep_rProd _
  refine ⟨fun a => ?_, fun a b => ?_, fun i => ?_⟩
  · refine eq_of_eqRows ?_ ?_ (h1 a a.2)
    · rw [rowsMatrix_mulRows, (hq a).1, Units.val_mul]
    · rw [rowsMatrix_idRows, Units.val_one]
  · have e := h2 a a.2 b b.2
    unfold cMat
    split_ifs at e ⊢ with hc
    · refine eq_of_eqRows ?_ ?_ e
      · rw [rowsMatrix_mulRows, (hq a).1, (hq b).1, Units.val_mul]
      · rw [rowsMatrix_mulRows, rowsMatrix_mulRows, (hq a).1, (hq b).1, prRep_t.1,
          ZMod.val_one, pow_one, Units.val_mul, Units.val_mul]
    · refine eq_of_eqRows ?_ ?_ e
      · rw [rowsMatrix_mulRows, (hq a).1, (hq b).1, Units.val_mul]
      · rw [rowsMatrix_mulRows, (hq a).1, (hq b).1, ZMod.val_zero, pow_zero, mul_one,
          Units.val_mul]
  · have e := h3 i i.2
    have hr : PrRep (rConj i) (rPairs[(i : ℕ)]?.getD prOne) := by
      have e : rConjN i = rConj i := by
        unfold rConjN
        split_ifs with hi
        · rfl
        · exact absurd i.2 hi
      rw [← e]
      exact prRep_rConjN i
    split_ifs at e ⊢ with hs
    · refine eq_of_eqRows hr.1 ?_ e
      rw [rowsMatrix_mulRows, prRep_t.1, (prRep_qProd _).1, Units.val_mul]
    · rw [one_mul]
      exact eq_of_eqRows hr.1 (prRep_qProd _).1 e

theorem rel_q : Rel t qGen cMat where
  z_sq := t_mul_t
  z_comm a := by
    have := W_le_centralizer (qGen_mem_W a)
    rw [Subgroup.mem_centralizer_iff] at this
    exact this t rfl
  q_sq := pChecks_spec.1
  comm := pChecks_spec.2.1

theorem injective_nf_q :
    Function.Injective (Function.uncurry (nf t qGen)) :=
  injective_nf rel_q t_ne_one nondegenerate_cMat

theorem P_eq_closure_q :
    P = Subgroup.closure (insert t (Set.range qGen)) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [pChecks_spec.2.2 i]
      refine Subgroup.mul_mem _ ?_ ?_
      · split_ifs
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · exact Subgroup.one_mem _
      · refine Subgroup.list_prod_mem _ fun x hx => ?_
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
        by_cases ha : a < 12
        · rw [← qGen_eq ⟨a, ha⟩]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨⟨a, ha⟩, rfl⟩)
        · rw [show qIdx.getD a [] = [] by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [qIdx]; omega)]; rfl]
          exact Subgroup.one_mem _
  · rw [Subgroup.closure_le]
    rintro _ (rfl | ⟨a, rfl⟩)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      unfold rConjN
      split_ifs with hi
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨⟨i, hi⟩, rfl⟩)
      · exact Subgroup.one_mem _

theorem card_P :
    Nat.card P = 2 ^ 13 := by
  rw [P_eq_closure_q]
  exact card_closure rel_q injective_nf_q

theorem isExtraspecialPGroup_P :
    IsExtraspecialPGroup 2 P := by
  rw [P_eq_closure_q]
  exact isExtraspecialPGroup rel_q injective_nf_q nondegenerate_cMat (by norm_num)

theorem map_center_P :
    (Subgroup.center P).map P.subtype = Subgroup.zpowers t := by
  rw [P_eq_closure_q]
  exact map_center_eq rel_q injective_nf_q nondegenerate_cMat

end CFSG.Quasithin.H13.J4
