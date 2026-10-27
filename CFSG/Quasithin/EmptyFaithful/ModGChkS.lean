module

public import CFSG.Quasithin.EmptyFaithful.ModGBase

public section

namespace CFSG.Quasithin.ModG

open CFSG.Blueprint

theorem mem_of_cd_mem {L : List Mg} {x : Mg} (h : cd x ∈ L.map cd) : x ∈ L := by
  obtain ⟨y, hy, hxy⟩ := List.mem_map.1 h
  exact cd_injective hxy ▸ hy

theorem cd_mem_of_mem {L : List Mg} {x : Mg} (h : x ∈ L) : cd x ∈ L.map cd := List.mem_map_of_mem h

@[expose] def sCheck : Bool :=
  nodupB SK && memB kId SK && allL (fun c => allL (fun l => memB (comp c l) SK) LsK) SK

theorem sCheck_true : sCheck = true := by decide +kernel

theorem SEl_nodup : SEl.Nodup := by
  have h0 := sCheck_true
  simp only [sCheck, Bool.and_eq_true] at h0
  have h := nodupB_iff.1 h0.1.1
  rw [← SEl_cd] at h
  exact List.Nodup.of_map cd h

theorem one_mem_SEl : (1 : Mg) ∈ SEl := by
  have h : memB kId SK = true := by
    have := sCheck_true
    simp only [sCheck, Bool.and_eq_true] at this
    exact this.1.2
  rw [← cd_one, ← SEl_cd] at h
  exact mem_of_cd_mem (memB_iff.1 h)

theorem SEl_closed : ∀ x ∈ SEl, ∀ l ∈ Ls, x * l ∈ SEl := by
  intro x hx l hl
  have h := sCheck_true
  simp only [sCheck, Bool.and_eq_true] at h
  have h3 := allL_iff.1 h.2 (cd x) (by rw [← SEl_cd]; exact cd_mem_of_mem hx)
  have h4 := memB_iff.1 (allL_iff.1 h3 (cd l) (by rw [← Ls_cd]; exact cd_mem_of_mem hl))
  rw [← cd_mul, ← SEl_cd] at h4
  exact mem_of_cd_mem h4

theorem SEl_length : SEl.length = 128 := by
  rw [SEl, List.length_map]
  decide +kernel

theorem invAlph_inv_mem (ls : List Mg) {y : Mg} (hy : y ∈ invAlph ls) : y⁻¹ ∈ invAlph ls := by
  simp only [invAlph, List.mem_append, List.mem_map] at hy ⊢
  rcases hy with h | ⟨z, hz, rfl⟩
  · exact Or.inr ⟨y, h, rfl⟩
  · exact Or.inl (by simpa using hz)

@[expose] def Sg : Subgroup Mg := Subgroup.closure {x | x ∈ Ls}

theorem mem_Sg_iff (g : Mg) : g ∈ Sg ↔ g ∈ SEl := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact one_mem_SEl
    | mul_right x hx y hy ih => exact SEl_closed x ih y hy
    | mul_inv_cancel x hx y hy ih => exact SEl_closed x ih y⁻¹ (invAlph_inv_mem _ hy)
  · intro hg
    rw [SEl, List.mem_map] at hg
    obtain ⟨w, -, rfl⟩ := hg
    exact ev_mem (fun x hx => Subgroup.subset_closure hx) w

theorem card_Sg : Nat.card Sg = 128 := by
  have h1 : Nat.card Sg = Nat.card {g : Mg // g ∈ SEl} :=
    Nat.card_congr (Equiv.subtypeEquivRight mem_Sg_iff)
  rw [h1, Nat.card_eq_fintype_card]
  have : Fintype.card {g : Mg // g ∈ SEl} = SEl.toFinset.card := by
    rw [← Fintype.card_coe]
    simp
  rw [this, List.toFinset_card_of_nodup SEl_nodup, SEl_length]

@[expose] def pairsB (S : List ℕ) (L : List (ℕ × ℕ)) : Bool :=
  List.rec true (fun p rest ih => Bool.and (allL (fun q => Bool.not (memB (comp p.1 q.2) S)) rest) ih) L

theorem pairsB_cons (S : List ℕ) (p : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
    pairsB S (p :: rest) = (allL (fun q => !(memB (comp p.1 q.2) S)) rest && pairsB S rest) := rfl

theorem pairsB_iff {S : List ℕ} {L : List (ℕ × ℕ)} :
    pairsB S L = true ↔ L.Pairwise (fun p q => memB (comp p.1 q.2) S = false) := by
  induction L with
  | nil => exact ⟨fun _ => List.Pairwise.nil, fun _ => rfl⟩
  | cons p rest ih =>
    rw [pairsB_cons, Bool.and_eq_true, ih, List.pairwise_cons, allL_iff]
    simp only [Bool.not_eq_true']

attribute [irreducible] pairsB

@[expose] def pairsOf (w : List ℕ) : ℕ × ℕ := (evc Lks8K (invW 4 w), evc Lks8K w)

@[expose] def bCheck : Bool := pairsB SK (dWd.map pairsOf)

theorem bCheck_true : bCheck = true := by decide +kernel

theorem dEl_pairs : dEl.map (fun x => (cd x⁻¹, cd x)) = dWd.map pairsOf := by
  rw [dEl, List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp, pairsOf]
  rw [← Lks8_cd, ← ev_invW Lks8_inv w (dWd_lt w hw), c_ev cd cd_mul cd_one,
    c_ev cd cd_mul cd_one]

theorem dEl_pairwise : dEl.Pairwise (fun x y => x⁻¹ * y ∉ Sg) := by
  have h := pairsB_iff.1 bCheck_true
  rw [← dEl_pairs, List.pairwise_map] at h
  refine h.imp ?_
  intro x y hxy hmem
  rw [mem_Sg_iff] at hmem
  have h2 : cd (x⁻¹ * y) ∈ SK := by
    rw [← SEl_cd]
    exact cd_mem_of_mem hmem
  have h3 := memB_iff.2 h2
  rw [cd_mul] at h3
  rw [h3] at hxy
  exact Bool.noConfusion hxy

end CFSG.Quasithin.ModG
