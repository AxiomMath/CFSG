module

public import CFSG.Permutation.AlternatingAutomorphism.JohnsonGraph

public section

namespace CFSG

namespace AlternatingAutomorphism.johnsonGraph

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

@[expose] def star (t : {s : Finset α // #s = k}) : Finset {s : Finset α // #s = k + 1} :=
  {s | t.1 ⊆ s.1}

@[simp]
theorem mem_star {t : {s : Finset α // #s = k}} {s : {s : Finset α // #s = k + 1}} :
    s ∈ star t ↔ t.1 ⊆ s.1 := by
  simp [star]

private theorem isClique_star (t : {s : Finset α // #s = k}) :
    (johnsonGraph α (k + 1)).IsClique (star t : Set {s : Finset α // #s = k + 1}) := by
  intro a ha b hb hab
  have := card_le_card (subset_inter (mem_star.mp ha) (mem_star.mp hb))
  have := card_inter_lt hab
  simp only [adj_iff]
  omega

private theorem card_star (t : {s : Finset α // #s = k}) : #(star t) = Fintype.card α - k := by
  have : #t.1ᶜ = Fintype.card α - k := by rw [card_compl, t.2]
  rw [← this]
  refine (card_bij (fun x hx => ⟨insert x t.1, by rw [card_insert_of_notMem (mem_compl.mp hx),
    t.2]⟩) (fun x _ => mem_star.mpr (subset_insert x t.1)) (fun x hx y hy h => ?_)
    (fun s hs => ?_)).symm
  · have h : insert x t.1 = insert y t.1 := congrArg Subtype.val h
    have : x ∈ insert y t.1 := h ▸ mem_insert_self x t.1
    exact (mem_insert.mp this).resolve_right (mem_compl.mp hx)
  · obtain ⟨x, hx⟩ := card_eq_one.mp (by
      rw [card_sdiff_of_subset (mem_star.mp hs), s.2, t.2, Nat.add_sub_cancel_left])
    refine ⟨x, mem_compl.mpr fun hxt => ?_, Subtype.ext ?_⟩
    · exact (mem_sdiff.mp (hx.symm ▸ mem_singleton_self x : x ∈ s.1 \ t.1)).2 hxt
    · change insert x t.1 = s.1
      rw [insert_eq, ← hx, sdiff_union_of_subset (mem_star.mp hs)]

private theorem star_injective (hk : k + 2 ≤ Fintype.card α) :
    Function.Injective (star : {s : Finset α // #s = k} → _) := by
  intro t t' h
  refine (Subtype.ext (eq_of_subset_of_card_le (fun x hx => ?_) (by rw [t.2, t'.2]))).symm
  by_contra hxt
  obtain ⟨y, hy⟩ : ((insert x t.1)ᶜ).Nonempty := by
    rw [← card_pos, card_compl, card_insert_of_notMem hxt, t.2]
    omega
  simp only [mem_compl, mem_insert, not_or] at hy
  have : ⟨insert y t.1, by rw [card_insert_of_notMem hy.2, t.2]⟩ ∈ star t' :=
    h ▸ mem_star.mpr (subset_insert y t.1)
  rcases mem_insert.mp (mem_star.mp this hx) with rfl | hx
  · exact hy.1 rfl
  · exact hxt hx

private theorem adj_iff_exists_mem_star {t t' : {s : Finset α // #s = k}} (h : t ≠ t') :
    (johnsonGraph α k).Adj t t' ↔ ∃ s, s ∈ star t ∧ s ∈ star t' := by
  have hU := card_union_add_card_inter t.1 t'.1
  rw [t.2, t'.2] at hU
  have := card_inter_lt h
  refine ⟨fun hadj => ⟨⟨t.1 ∪ t'.1, ?_⟩, ?_, ?_⟩, fun ⟨s, hs, hs'⟩ => ?_⟩
  · simp only [adj_iff] at hadj
    omega
  · exact mem_star.mpr subset_union_left
  · exact mem_star.mpr subset_union_right
  · have := card_le_card (union_subset (mem_star.mp hs) (mem_star.mp hs'))
    simp only [adj_iff]
    omega

private theorem exists_map_star_eq (hk : 2 * (k + 1) < Fintype.card α)
    (F : johnsonGraph α (k + 1) ≃g johnsonGraph α (k + 1)) (t : {s : Finset α // #s = k}) :
    ∃ t', (star t).map F.toEquiv.toEmbedding = star t' := by
  set C := (star t).map F.toEquiv.toEmbedding
  have hC : (johnsonGraph α (k + 1)).IsClique (C : Set {s : Finset α // #s = k + 1}) := by
    intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_map.mp hb
    exact F.map_adj_iff.mpr (isClique_star t ha' hb' (ne_of_apply_ne _ hab))
  have hcard : #C = Fintype.card α - k := by rw [card_map, card_star]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < #C)
  have hab' : #(a.1 ∩ b.1) = k := by
    have := hC ha hb hab
    simp only [adj_iff] at this
    omega
  refine ⟨⟨a.1 ∩ b.1, hab'⟩, eq_of_subset_of_card_le (fun d hd => mem_star.mpr ?_) ?_⟩
  · exact subset_of_isClique hC (by omega) ha hb hab hd
  · rw [hcard, card_star]

private theorem exists_iso_map_star (hk : 2 * (k + 1) < Fintype.card α)
    (F : johnsonGraph α (k + 1) ≃g johnsonGraph α (k + 1)) :
    ∃ F' : johnsonGraph α k ≃g johnsonGraph α k,
      ∀ t, (star t).map F.toEquiv.toEmbedding = star (F' t) := by
  choose f hf using exists_map_star_eq hk F
  have hinj : Function.Injective f := fun t t' h =>
    star_injective (by omega) (map_injective _ (by rw [hf, hf, h]))
  refine ⟨⟨.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, fun {t t'} => ?_⟩, hf⟩
  change (johnsonGraph α k).Adj (f t) (f t') ↔ _
  obtain rfl | h := eq_or_ne t t'
  · exact iff_of_false (SimpleGraph.irrefl _) (SimpleGraph.irrefl _)
  rw [adj_iff_exists_mem_star h, adj_iff_exists_mem_star (hinj.ne h), ← hf, ← hf]
  simp only [mem_map_equiv]
  exact ⟨fun ⟨s, h⟩ => ⟨_, h⟩, fun ⟨s, h⟩ => ⟨F.toEquiv s, by rwa [Equiv.symm_apply_apply]⟩⟩

private theorem eq_map_of_map_star (hk : 1 ≤ k)
    {F : johnsonGraph α (k + 1) ≃g johnsonGraph α (k + 1)}
    {F' : johnsonGraph α k ≃g johnsonGraph α k}
    (hF' : ∀ t, (star t).map F.toEquiv.toEmbedding = star (F' t)) {σ : Equiv.Perm α}
    (hσ : ∀ t, (F' t).1 = t.1.map σ.toEmbedding) (s : {s : Finset α // #s = k + 1}) :
    (F s).1 = s.1.map σ.toEmbedding := by
  refine (eq_of_subset_of_card_le (fun z hz => ?_) (by rw [card_map, s.2, (F s).2])).symm
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hz
  obtain ⟨y, hy, hyx⟩ := exists_mem_ne (by rw [s.2]; omega) x
  let t : {s : Finset α // #s = k} := ⟨s.1.erase y, by rw [card_erase_of_mem hy, s.2]; rfl⟩
  have : F s ∈ star (F' t) := by
    rw [← hF']
    exact mem_map_of_mem _ (mem_star.mpr (erase_subset y s.1))
  refine mem_star.mp this ?_
  rw [hσ t]
  exact mem_map_of_mem _ (mem_erase.mpr ⟨hyx.symm, hx⟩)

omit [Fintype α] in
private theorem exists_perm_of_iso_one [Finite α] (F : johnsonGraph α 1 ≃g johnsonGraph α 1) :
    ∃ σ : Equiv.Perm α, ∀ s, (F s).1 = s.1.map σ.toEmbedding := by
  choose f hf using fun x : α => card_eq_one.mp (F ⟨{x}, card_singleton x⟩).2
  have hinj : Function.Injective f := fun x y h => by
    have := F.injective (Subtype.ext (by rw [hf, hf, h]) :
      F ⟨{x}, card_singleton x⟩ = F ⟨{y}, card_singleton y⟩)
    simpa using congrArg Subtype.val this
  refine ⟨.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, fun s => ?_⟩
  obtain ⟨x, hx⟩ := card_eq_one.mp s.2
  obtain rfl : s = ⟨{x}, card_singleton x⟩ := Subtype.ext hx
  simp only [hf, map_singleton]
  rfl

private theorem exists_perm_of_iso_of_two_mul_lt (hk : 2 * k < Fintype.card α)
    (F : johnsonGraph α k ≃g johnsonGraph α k) :
    ∃ σ : Equiv.Perm α, ∀ s, (F s).1 = s.1.map σ.toEmbedding := by
  induction k with
  | zero => exact ⟨1, fun s => by rw [card_eq_zero.mp s.2, card_eq_zero.mp (F s).2, map_empty]⟩
  | succ k ih =>
    obtain rfl | hk0 := Nat.eq_zero_or_pos k
    · exact exists_perm_of_iso_one F
    obtain ⟨F', hF'⟩ := exists_iso_map_star hk F
    obtain ⟨σ, hσ⟩ := ih (by omega) F'
    exact ⟨σ, eq_map_of_map_star hk0 hF' hσ⟩

private def complIso (hk : k ≤ Fintype.card α) :
    johnsonGraph α k ≃g johnsonGraph α (Fintype.card α - k) where
  toFun s := ⟨s.1ᶜ, by rw [card_compl, s.2]⟩
  invFun s := ⟨s.1ᶜ, by rw [card_compl, s.2]; omega⟩
  left_inv s := by simp
  right_inv s := by simp
  map_rel_iff' {s t} := by
    simp only [Equiv.coe_fn_mk, adj_iff, ← compl_union, card_compl]
    have h₁ := card_union_add_card_inter s.1 t.1
    have h₂ := card_le_univ (s.1 ∪ t.1)
    rw [s.2, t.2] at h₁
    omega

theorem exists_perm_of_iso (hk : 2 * k ≠ Fintype.card α)
    (F : johnsonGraph α k ≃g johnsonGraph α k) :
    ∃ σ : Equiv.Perm α, ∀ s, (F s).1 = s.1.map σ.toEmbedding := by
  obtain hk | hk := hk.lt_or_gt
  · exact exists_perm_of_iso_of_two_mul_lt hk F
  obtain hkn | hkn := le_or_gt k (Fintype.card α)
  · obtain ⟨σ, hσ⟩ := exists_perm_of_iso_of_two_mul_lt (by omega)
      (((complIso hkn).symm.trans F).trans (complIso hkn))
    refine ⟨σ, fun s => compl_injective ?_⟩
    have := hσ (complIso hkn s)
    simp only [RelIso.trans_apply, RelIso.symm_apply_apply] at this
    rw [show (F s).1ᶜ = (complIso hkn (F s)).1 from rfl, this]
    ext
    simp [complIso, mem_map_equiv]
  · exact ⟨1, fun s => absurd (card_le_univ s.1) (by rw [s.2]; omega)⟩

end AlternatingAutomorphism.johnsonGraph

end CFSG
