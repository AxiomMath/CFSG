module

public import CFSG.Quasithin.H13.LocDblProfDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.Quasithin.H13.LocDbl.M24Tab

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.M24Prof

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 24)]

theorem tab_one' : tab 24 (1 : Γ) = List.range 24 := by
  unfold tab
  simp [List.map_coe_finRange_eq_range]

theorem tab_injective_of_faithful [FaithfulSMul Γ (Fin 24)] {g h : Γ}
    (hgh : tab 24 g = tab 24 h) : g = h := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin 24) fun i => ?_
  apply Fin.ext
  have := congrArg (fun t => t.getD i.val 0) hgh
  rw [tab_getD, tab_getD] at this
  exact this

theorem fixCount_eq (g : Γ) :
    fixCount g = ((List.range 24).filter fun i => (tab 24 g).getD i 0 == i).length := by
  classical
  unfold fixCount
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  refine Finset.card_bij (fun p _ => p.val) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq]
    refine ⟨p.isLt, ?_⟩
    rw [tab_getD, hp]
  · intro p _ q _ h
    exact Fin.ext h
  · intro q hq
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq] at hq
    refine ⟨⟨q, hq.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    have := tab_getD g ⟨q, hq.1⟩
    simp only at this
    rw [← this]
    exact hq.2

theorem fixCount_conj (g y : Γ) : fixCount (g * y * g⁻¹) = fixCount y := by
  classical
  unfold fixCount
  refine Finset.card_bij (fun p _ => g⁻¹ • p) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have h1 : (g * y * g⁻¹) • p = p := hp
    calc y • g⁻¹ • p = g⁻¹ • ((g * y * g⁻¹) • p) := by simp [mul_smul]
      _ = g⁻¹ • p := by rw [h1]
  · intro p _ q _ h
    simpa using h
  · intro q hq
    refine ⟨g • q, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    calc (g * y * g⁻¹) • g • q = g • (y • q) := by simp [mul_smul]
      _ = g • q := by rw [hq]

theorem fixCount_mem_of_sylow [Finite Γ] (p : ℕ) [Fact p.Prime] (P0 : Subgroup Γ)
    (hP0 : Nat.card P0 = p ^ (Nat.card Γ).factorization p) (T : Set ℕ)
    (hT : ∀ x ∈ P0, fixCount x ∈ T) {x : Γ} (hx : IsPGroup p (Subgroup.zpowers x)) :
    fixCount x ∈ T := by
  let P : Sylow p Γ := Sylow.ofCard P0 hP0
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P Q
  have hxQ : x ∈ (Q : Subgroup Γ) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, rfl⟩ := hxQ
  have hsP0 : s ∈ P0 := hs
  have : (MulAut.conj g • s : Γ) = g * s * g⁻¹ := rfl
  rw [this, fixCount_conj]
  exact hT s hsP0

theorem tab_inv_of_cube [FaithfulSMul Γ (Fin 24)] {s : Γ}
    (h : compTab (tab 24 s) (compTab (tab 24 s) (tab 24 s)) = List.range 24) :
    tab 24 s⁻¹ = compTab (tab 24 s) (tab 24 s) := by
  have h3 : s * (s * s) = 1 := by
    apply tab_injective_of_faithful
    rw [tab_mul, tab_mul, tab_one']
    exact h
  have : s⁻¹ = s * s := by
    calc s⁻¹ = s⁻¹ * (s * (s * s)) := by rw [h3, mul_one]
      _ = s * s := by group
  rw [this, tab_mul]

theorem card_closure_of_tables [FaithfulSMul Γ (Fin 24)] (gens : List Γ)
    (Lw : List (List ℕ × List ℕ)) (hnd : (Lw.map Prod.fst).Nodup)
    (hone : tab 24 (1 : Γ) ∈ Lw.map Prod.fst)
    (hgen : ∀ g ∈ gens, tab 24 g ∈ Lw.map Prod.fst ∧ tab 24 g⁻¹ ∈ Lw.map Prod.fst)
    (hmul : ∀ t ∈ Lw.map Prod.fst, ∀ u ∈ Lw.map Prod.fst, compTab t u ∈ Lw.map Prod.fst)
    (hwords : ∀ q ∈ Lw,
      (q.2.map fun i => tab 24 (gens.getD i 1)).foldr compTab (List.range 24) = q.1) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = Lw.length ∧
      ∀ x ∈ Subgroup.closure {g | g ∈ gens}, tab 24 x ∈ Lw.map Prod.fst := by
  classical
  set C := Subgroup.closure {g | g ∈ gens} with hC
  have hmem : ∀ x ∈ C, tab 24 x ∈ Lw.map Prod.fst ∧ tab 24 x⁻¹ ∈ Lw.map Prod.fst := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem g hg => exact hgen g hg
    | one => exact ⟨hone, by rw [inv_one]; exact hone⟩
    | mul x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · rw [tab_mul]
        exact hmul _ hx.1 _ hy.1
      · rw [mul_inv_rev, tab_mul]
        exact hmul _ hy.2 _ hx.2
    | inv x _ hx => exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩
  have hsurj : ∀ q ∈ Lw, ∃ x ∈ C, tab 24 x = q.1 := by
    intro q hq
    refine ⟨(q.2.map fun i => gens.getD i 1).prod, ?_, ?_⟩
    · apply Subgroup.list_prod_mem
      intro y hy
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      by_cases hi : i < gens.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact Subgroup.subset_closure (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (not_lt.1 hi)]
        exact C.one_mem
    · rw [← hwords q hq]
      generalize q.2 = w
      induction w with
      | nil => simp [tab_one']
      | cons i w ih => simp only [List.map_cons, List.prod_cons, List.foldr_cons, tab_mul, ih]
  refine ⟨?_, fun x hx => (hmem x hx).1⟩
  let f : C → {t // t ∈ Lw.map Prod.fst} := fun x => ⟨tab 24 x.1, (hmem x.1 x.2).1⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (tab_injective_of_faithful (congrArg Subtype.val h)), ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ht
    obtain ⟨x, hxC, hx⟩ := hsurj q hq
    exact ⟨⟨x, hxC⟩, Subtype.ext hx⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  have h2 : Nat.card {t // t ∈ Lw.map Prod.fst} = (Lw.map Prod.fst).toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun t => by simp)
  rw [h2, List.toFinset_card_of_nodup hnd, List.length_map]

end CFSG.Quasithin.H13.LocDbl.M24Tab
