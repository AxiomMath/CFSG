module

public import CFSG.RankThree.PartOne.KA5L.Frames
public import CFSG.LieType.Chevalley.E6GraphLeviRealization
public import CFSG.ClassicalInvolution.WeakCT.Standard

public noncomputable section

namespace CFSG.RankThree.PartOne.KA5L

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)

open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Commute

variable {L : Type} [Field L]

theorem not_isRoot_add_of_cartan_zero {p q : Fin Tag.E7.rank}
    (hpq : p ≠ q) (hc : Tag.E7.cartan p q = 0) {α β : Fin Tag.E7.rank → ℤ}
    (hα : α = Pi.single p 1 ∨ α = -Pi.single p 1)
    (hβ : β = Pi.single q 1 ∨ β = -Pi.single q 1) : ¬ IsRoot Tag.E7 (α + β) := by
  intro hroot
  obtain ⟨m, hm⟩ := (isRoot_iff_exists_e7RootVec).1 hroot
  have key : ∀ p q : Fin 7, p ≠ q → Tag.E7.cartan (e7Index p) (e7Index q) = 0 → ∀ m : Fin 126,
      e7RootVec m ≠ Pi.single (e7Index p) 1 + Pi.single (e7Index q) 1 ∧
      e7RootVec m ≠ Pi.single (e7Index p) 1 + -Pi.single (e7Index q) 1 ∧
      e7RootVec m ≠ -Pi.single (e7Index p) 1 + Pi.single (e7Index q) 1 ∧
      e7RootVec m ≠ -Pi.single (e7Index p) 1 + -Pi.single (e7Index q) 1 := by
    decide +kernel
  have := key ⟨p.val, p.2⟩ ⟨q.val, q.2⟩ (fun h => hpq (Fin.ext (by simpa using congrArg Fin.val h)))
    hc m
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
  · exact this.1 hm
  · exact this.2.1 hm
  · exact this.2.2.1 hm
  · exact this.2.2.2 hm

theorem isRoot_single_e7 (r : Fin Tag.E7.rank) : IsRoot Tag.E7 (Pi.single r 1) := IsRoot.basis r

theorem isRoot_neg_single_e7 (r : Fin Tag.E7.rank) : IsRoot Tag.E7 (-Pi.single r 1) := by
  have h := (IsRoot.basis (τ := Tag.E7) r).reflect r
  have e : ∀ r : Fin 7, reflect Tag.E7 (e7Index r) (Pi.single (e7Index r) 1) =
      -Pi.single (e7Index r) 1 := by decide +kernel
  have e' : reflect Tag.E7 r (Pi.single r 1) = -Pi.single r 1 := e ⟨r.val, r.2⟩
  rwa [e'] at h

theorem commute_pinnedX_of_cartan_zero {p q : Fin Tag.E7.rank} (hpq : p ≠ q)
    (hc : Tag.E7.cartan p q = 0) {α β : Fin Tag.E7.rank → ℤ}
    (hα : α = Pi.single p 1 ∨ α = -Pi.single p 1)
    (hβ : β = Pi.single q 1 ∨ β = -Pi.single q 1) (s t : L) :
    Commute (pinnedX Tag.E7 L α s) (pinnedX Tag.E7 L β t) := by
  have hαr : IsRoot Tag.E7 α := by
    rcases hα with rfl | rfl
    exacts [isRoot_single_e7 p, isRoot_neg_single_e7 p]
  have hβr : IsRoot Tag.E7 β := by
    rcases hβ with rfl | rfl
    exacts [isRoot_single_e7 q, isRoot_neg_single_e7 q]
  have hne : α ≠ β := by
    intro h
    have := congrFun h p
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> simp [hpq] at this
  have hne' : α ≠ -β := by
    intro h
    have := congrFun h p
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> simp [hpq] at this
  exact (simply_laced_root_commutator_unit Tag.E7 (Or.inr (Or.inr (Or.inl rfl))) hαr hβr hne
    hne').2 (not_isRoot_add_of_cartan_zero hpq hc hα hβ) L _
    (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨s, rfl⟩) _
    (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨t, rfl⟩)

theorem commute_xUnit_yUnit_of_cartan_zero {p q : Fin Tag.E7.rank} (hpq : p ≠ q)
    (hc : Tag.E7.cartan p q = 0) (s t : L) :
    Commute (xUnit Tag.E7 L p s) (xUnit Tag.E7 L q t) ∧
      Commute (xUnit Tag.E7 L p s) (yUnit Tag.E7 L q t) ∧
      Commute (yUnit Tag.E7 L p s) (xUnit Tag.E7 L q t) ∧
      Commute (yUnit Tag.E7 L p s) (yUnit Tag.E7 L q t) := by
  rw [← pinnedX_single, ← pinnedX_single, ← pinnedX_neg_single, ← pinnedX_neg_single]
  exact ⟨commute_pinnedX_of_cartan_zero hpq hc (Or.inl rfl) (Or.inl rfl) s t,
    commute_pinnedX_of_cartan_zero hpq hc (Or.inl rfl) (Or.inr rfl) s t,
    commute_pinnedX_of_cartan_zero hpq hc (Or.inr rfl) (Or.inl rfl) s t,
    commute_pinnedX_of_cartan_zero hpq hc (Or.inr rfl) (Or.inr rfl) s t⟩

theorem commute_simpleRootSL2 {p q : Fin Tag.E7.rank} (hpq : p ≠ q)
    (hc : Tag.E7.cartan p q = 0) (A B : SL2 L) :
    Commute (simpleRootSL2 Tag.E7 L p A) (simpleRootSL2 Tag.E7 L q B) := by
  have hxy := fun s t => commute_xUnit_yUnit_of_cartan_zero (L := L) hpq hc s t
  have h1 : ∀ g : ModGL Tag.E7 L, (∀ t, Commute g (xUnit Tag.E7 L q t)) →
      (∀ t, Commute g (yUnit Tag.E7 L q t)) →
      ∀ B : SL2 L, Commute g (simpleRootSL2 Tag.E7 L q B) := by
    intro g hx hy B
    have hB : B ∈ Subgroup.closure (Set.range (sl2Upper L) ∪ Set.range (sl2Lower L)) := by
      rw [sl2_closure_upper_lower]
      trivial
    induction hB using Subgroup.closure_induction with
    | mem x hx' =>
      rcases hx' with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact (simpleRootSL2_uSL q c) ▸ hx c
      · exact (simpleRootSL2_vSL q c) ▸ hy c
    | one => rw [map_one]; exact Commute.one_right _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
    | inv x _ hx => rw [map_inv]; exact hx.inv_right
  have hA : A ∈ Subgroup.closure (Set.range (sl2Upper L) ∪ Set.range (sl2Lower L)) := by
    rw [sl2_closure_upper_lower]
    trivial
  induction hA using Subgroup.closure_induction with
  | mem x hx' =>
    rcases hx' with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [show sl2Upper L c = uSL c from rfl, simpleRootSL2_uSL]
      exact h1 _ (fun t => (hxy c t).1) (fun t => (hxy c t).2.1) B
    · rw [show sl2Lower L c = vSL c from rfl, simpleRootSL2_vSL]
      exact h1 _ (fun t => (hxy c t).2.2.1) (fun t => (hxy c t).2.2.2) B
  | one => rw [map_one]; exact Commute.one_left _
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_left hy
  | inv x _ hx => rw [map_inv]; exact hx.inv_left

end Commute

section Family

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)


theorem a5chain_cartan_zero : ∀ i j : Fin 5, (i : ℕ) + 1 < j →
    a5chain i ≠ a5chain j ∧ Tag.E7.cartan (a5chain i) (a5chain j) = 0 := by
  decide +kernel

variable (L : Type) [Field L]

noncomputable def a5CTFamily : CTFamily L (ModGL Tag.E7 L) 5 where
  ι i := simpleRootSL2 Tag.E7 L (a5chain i)
  θ i := if h : i.val < 4 then (exists_a5Frame (L := L) ⟨i.val, h⟩).choose else 1
  left i hi := by
    have h : i.val < 4 := by omega
    simp only [dite_eq_left h]
    exact (exists_a5Frame (L := L) ⟨i.val, h⟩).choose_spec.1
  right i hi := by
    have h : i.val < 4 := by omega
    simp only [dite_eq_left h]
    exact (exists_a5Frame (L := L) ⟨i.val, h⟩).choose_spec.2
  comm i j hij a b :=
    (commute_simpleRootSL2 (a5chain_cartan_zero i j hij).1 (a5chain_cartan_zero i j hij).2 a b).eq

@[expose] noncomputable def a5Frame : SL(6, L) →* ModGL Tag.E7 L :=
  (exists_hom_of_ctFamily (a5CTFamily L)).choose

theorem a5Frame_comp_blockSL2 (i : Fin 5) :
    (a5Frame L).comp (blockSL2 L 5 i) = simpleRootSL2 Tag.E7 L (a5chain i) :=
  (exists_hom_of_ctFamily (a5CTFamily L)).choose_spec.1 i

variable {L}

theorem blockSL2_uSL (i : Fin 5) (t : L) : blockSL2 L 5 i (uSL t) =
    Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := i)).ne t := by
  apply Subtype.ext
  rw [blockSL2, coe_blockSL, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, uSL]

theorem blockSL2_vSL (i : Fin 5) (t : L) : blockSL2 L 5 i (vSL t) =
    Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := i)).ne' t := by
  apply Subtype.ext
  rw [blockSL2, coe_blockSL, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, vSL]

end Family

section Values

variable {L : Type} [Field L]

theorem a5Frame_castSucc (i : Fin 5) (t : L) :
    a5Frame L (Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := i)).ne t) =
      xUnit Tag.E7 L (a5chain i) t := by
  rw [← blockSL2_uSL, ← MonoidHom.comp_apply, a5Frame_comp_blockSL2, simpleRootSL2_uSL]

theorem a5Frame_succ (i : Fin 5) (t : L) :
    a5Frame L (Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := i)).ne' t) =
      yUnit Tag.E7 L (a5chain i) t := by
  rw [← blockSL2_vSL, ← MonoidHom.comp_apply, a5Frame_comp_blockSL2, simpleRootSL2_vSL]

theorem a5Frame_ne_one : ∃ B : SL(6, L), a5Frame L B ≠ 1 := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := 0)).ne 1, ?_⟩
  rw [a5Frame_castSucc]
  intro h
  have h' : xUnit Tag.E7 L (a5chain 0) 1 = xUnit Tag.E7 L (a5chain 0) 0 := by
    rw [h, xUnit_zero]
  rw [← pinnedX_single, ← pinnedX_single] at h'
  exact one_ne_zero (pinnedX_injective Tag.E7 L _ h')

theorem ker_a5Frame_le_center : (a5Frame L).ker ≤ Subgroup.center SL(6, L) :=
  CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num)) a5Frame_ne_one

theorem range_a5Frame :
    (a5Frame L).range = subsystemGroup Tag.E7 L (a5Nodes Tag.E7) := by
  rw [MonoidHom.range_eq_map, ← CFSG.LieType.Chevalley.E6GraphLevi.closure_adjacentSet,
    MonoidHom.map_closure, subsystemGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨B, ⟨t, c, rfl | rfl⟩, rfl⟩
    · exact ⟨a5chain t, a5chain_mem t, c, Or.inl (a5Frame_castSucc t c)⟩
    · exact ⟨a5chain t, a5chain_mem t, c, Or.inr (a5Frame_succ t c)⟩
  · rintro ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨t, rfl⟩ := exists_a5chain_of_mem hi
      exact ⟨_, ⟨t, c, Or.inl rfl⟩, a5Frame_castSucc t c⟩
    · obtain ⟨t, rfl⟩ := exists_a5chain_of_mem hi
      exact ⟨_, ⟨t, c, Or.inr rfl⟩, a5Frame_succ t c⟩

end Values

end CFSG.RankThree.PartOne.KA5L
