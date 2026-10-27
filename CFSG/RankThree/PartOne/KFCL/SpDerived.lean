module

public import CFSG.RankThree.PartOne.KFCL.SpBase

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFCL.BlockSL
open scoped MatrixGroups commutatorElement Classical

variable {K : Type} [Field K] [CharP K 2] {p : ℕ}

section Trivial

variable {S : Subgroup (StatedSp 3 K)}

omit [CharP K 2] in
theorem eq_one_of_trivial (hST : S ≤ spTorus p 3 K) {s : StatedSp 3 K} (hs : s ∈ S)
    (h : ∀ a, mat 3 K s a a = 1) : s = 1 := by
  apply mat_injective
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [h a, map_one, Matrix.one_apply_eq]
  · rw [spTorus_apply_ne (hST hs) hab, map_one, Matrix.one_apply_ne hab]

theorem suppGroup_triv_le_Jjoin (hST : S ≤ spTorus p 3 K) (hS0 : S ≠ ⊥) :
    suppGroup {a : Fin 3 ⊕ Fin 3 | cls S a = 1} ≤ Jjoin p S := by
  set Y : Finset (Fin 3) := Finset.univ.filter (fun k => cls S (Sum.inl k) = 1) with hY
  have hYne : Y ≠ Finset.univ := by
    intro hYu
    apply hS0
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    refine eq_one_of_trivial hST hs (fun a => ?_)
    have hall : ∀ k, cls S (Sum.inl k) = 1 := fun k => by
      have : k ∈ Y := by rw [hYu]; exact Finset.mem_univ k
      simpa [hY] using this
    rcases a with k | k
    · exact congrFun (hall k) ⟨s, hs⟩
    · have := congrFun (cls_par hST (Sum.inl k)) ⟨s, hs⟩
      simp only [par_inl] at this
      have h2 : cls S (Sum.inr k) ⟨s, hs⟩ = (cls S (Sum.inl k) ⟨s, hs⟩)⁻¹ := this
      rw [show mat 3 K s (Sum.inr k) (Sum.inr k) = cls S (Sum.inr k) ⟨s, hs⟩ from rfl, h2,
        show cls S (Sum.inl k) ⟨s, hs⟩ = 1 from congrFun (hall k) ⟨s, hs⟩, inv_one]
  have hmemY : ∀ k, k ∈ Y ↔ cls S (Sum.inl k) = 1 := fun k => by simp [hY]
  have htriv : ∀ k ∈ Y, ∀ s ∈ S, mat 3 K s (Sum.inl k) (Sum.inl k) = 1 := fun k hk s hs =>
    congrFun ((hmemY k).1 hk) ⟨s, hs⟩
  have hX : ∀ a : Fin 3 ⊕ Fin 3, cls S a = 1 ↔ ∃ k ∈ Y, a ∈ coords k := by
    intro a
    rcases a with k | k
    · constructor
      · intro h
        exact ⟨k, (hmemY k).2 h, inl_mem_coords k⟩
      · rintro ⟨k', hk', hmem⟩
        rcases mem_coords.1 hmem with h | h
        · have := Sum.inl_injective h
          subst this
          exact (hmemY _).1 hk'
        · exact absurd h Sum.inl_ne_inr
    · constructor
      · intro h
        refine ⟨k, (hmemY k).2 ?_, inr_mem_coords k⟩
        have h2 := cls_par hST (Sum.inl k)
        simp only [par_inl] at h2
        rw [h2] at h
        exact inv_eq_one.1 h
      · rintro ⟨k', hk', hmem⟩
        rcases mem_coords.1 hmem with h | h
        · exact absurd h Sum.inr_ne_inl
        · have := Sum.inr_injective h
          subst this
          have h2 := cls_par hST (Sum.inl k)
          simp only [par_inl] at h2
          rw [h2, (hmemY k).1 hk', inv_one]
  have hshape : ∀ Y : Finset (Fin 3), Y ≠ Finset.univ →
      Y = ∅ ∨ (∃ k, Y = {k}) ∨ ∃ i j, i ≠ j ∧ Y = {i, j} := by decide
  rcases hshape Y hYne with h0 | ⟨k, hk⟩ | ⟨i, j, hij, hij'⟩
  ·
    intro x hx
    have : x = 1 := by
      apply mat_injective
      ext a b
      have hX0 : ¬ (a ∈ {a : Fin 3 ⊕ Fin 3 | cls S a = 1} ∧ b ∈ {a : Fin 3 ⊕ Fin 3 | cls S a = 1}) := by
        rintro ⟨ha, -⟩
        obtain ⟨k, hk, -⟩ := (hX a).1 ha
        rw [h0] at hk
        exact Finset.notMem_empty k hk
      rw [hx a b hX0, map_one]
    rw [this]
    exact Subgroup.one_mem _
  · have hXk : {a : Fin 3 ⊕ Fin 3 | cls S a = 1} = coords k := by
      ext a
      rw [Set.mem_ofPred_eq, hX a]
      constructor
      · rintro ⟨k', hk', hmem⟩
        rw [hk, Finset.mem_singleton] at hk'
        subst hk'
        exact hmem
      · intro hmem
        exact ⟨k, by rw [hk]; exact Finset.mem_singleton_self k, hmem⟩
    rw [hXk]
    exact suppGroup_coords_le_Jjoin hST (htriv k (by rw [hk]; exact Finset.mem_singleton_self k))
  · have hXij : {a : Fin 3 ⊕ Fin 3 | cls S a = 1} = coords i ∪ coords j := by
      ext a
      rw [Set.mem_ofPred_eq, hX a, Set.mem_union]
      constructor
      · rintro ⟨k', hk', hmem⟩
        rw [hij', Finset.mem_insert, Finset.mem_singleton] at hk'
        rcases hk' with rfl | rfl
        · exact Or.inl hmem
        · exact Or.inr hmem
      · rintro (hmem | hmem)
        · exact ⟨i, by rw [hij']; simp, hmem⟩
        · exact ⟨j, by rw [hij']; simp, hmem⟩
    rw [hXij]
    exact suppGroup_coords_union_le_Jjoin hST hij
      (htriv i (by rw [hij']; simp)) (htriv j (by rw [hij']; simp))

end Trivial

section Induction

variable {S : Subgroup (StatedSp 3 K)}

@[expose] noncomputable def badClasses (S : Subgroup (StatedSp 3 K)) (c : StatedSp 3 K) : Finset (↥S → K) :=
  (Finset.univ.image (cls S)).filter (fun κ => κ ≠ 1 ∧ blkS S κ c ≠ 1)

omit [CharP K 2] in
theorem mem_badClasses {c : StatedSp 3 K} {κ : ↥S → K} :
    κ ∈ badClasses S c ↔ κ ≠ 1 ∧ blkS S κ c ≠ 1 := by
  unfold badClasses
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    by_contra hnot
    apply h2
    have hempty : IsEmpty {a // cls S a = κ} := ⟨fun a => hnot ⟨a.1, Finset.mem_univ _, a.2⟩⟩
    ext a
    exact (hempty.false a).elim

omit [CharP K 2] in
theorem mem_suppGroup_of_badClasses_empty (hST : S ≤ spTorus p 3 K) {c : StatedSp 3 K}
    (hc : c ∈ Subgroup.centralizer (S : Set (StatedSp 3 K))) (h : badClasses S c = ∅) :
    c ∈ suppGroup {a : Fin 3 ⊕ Fin 3 | cls S a = 1} := by
  rw [mem_suppGroup]
  intro a b hab
  by_cases hcls : cls S a = cls S b
  · have hne : cls S a ≠ 1 := fun h1 => hab ⟨h1, hcls.symm.trans h1⟩
    have h1 : blkS S (cls S a) c = 1 := by
      by_contra hb
      have : cls S a ∈ badClasses S c := mem_badClasses.2 ⟨hne, hb⟩
      rw [h] at this
      exact Finset.notMem_empty _ this
    have := congrFun (congrFun h1 ⟨a, rfl⟩) ⟨b, hcls.symm⟩
    simpa [blkS_apply, Matrix.one_apply, Subtype.ext_iff] using this
  · rw [bd_of_mem_centralizer hST hc hcls, Matrix.one_apply_ne]
    intro hab'
    exact hcls (by rw [hab'])

theorem mem_Jjoin_of_dets (hodd : Odd p) (hST : S ≤ spTorus p 3 K) (hS0 : S ≠ ⊥) :
    ∀ (n : ℕ) (c : StatedSp 3 K), c ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) →
      (∀ κ : ↥S → K, κ ≠ 1 → detBlk κ c = 1) → (badClasses S c).card ≤ n → c ∈ Jjoin p S := by
  intro n
  induction n with
  | zero =>
    intro c hc _ hcard
    have h0 : badClasses S c = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    exact suppGroup_triv_le_Jjoin hST hS0 (mem_suppGroup_of_badClasses_empty hST hc h0)
  | succ n ih =>
    intro c hc hdet hcard
    by_cases h0 : badClasses S c = ∅
    · exact suppGroup_triv_le_Jjoin hST hS0 (mem_suppGroup_of_badClasses_empty hST hc h0)
    · obtain ⟨κ, hκ⟩ := Finset.nonempty_iff_ne_empty.2 h0
      obtain ⟨hκ1, -⟩ := mem_badClasses.1 hκ
      have hd : (blkS S κ c).det = 1 := hdet κ hκ1
      obtain ⟨h, hJ, hC, hbh, hother⟩ := peel_step hodd hST hκ1 ⟨blkS S κ c, hd⟩
      have hC' : h⁻¹ ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) := Subgroup.inv_mem _ hC
      have hg'C : h⁻¹ * c ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) := Subgroup.mul_mem _ hC' hc
      have hκg : blkS S κ (h⁻¹ * c) = 1 := by
        rw [blkS_mul hST κ hC', blkS_inv hST κ hC]
        have hbh' : blkS S κ h = blkS S κ c := hbh
        rw [hbh']
        exact Matrix.nonsing_inv_mul _ (by rw [hd]; exact isUnit_one)
      have hκg' : blkS S κ⁻¹ (h⁻¹ * c) = 1 := blkS_inv_eq_one hST κ hg'C hκg
      have hother' : ∀ l : ↥S → K, l ≠ κ → l ≠ κ⁻¹ → blkS S l (h⁻¹ * c) = blkS S l c := by
        intro l hl hl'
        rw [blkS_mul hST l hC', blkS_inv hST l hC, hother l hl hl', inv_one, one_mul]
      have hdet' : ∀ l : ↥S → K, l ≠ 1 → detBlk l (h⁻¹ * c) = 1 := by
        intro l hl1
        by_cases hlκ : l = κ
        · subst hlκ
          unfold detBlk
          rw [hκg, Matrix.det_one]
        · by_cases hlκ' : l = κ⁻¹
          · subst hlκ'
            unfold detBlk
            rw [hκg', Matrix.det_one]
          · unfold detBlk
            rw [hother' l hlκ hlκ']
            exact hdet l hl1
      have hsub : badClasses S (h⁻¹ * c) ⊆ (badClasses S c).erase κ := by
        intro l hl
        obtain ⟨hl1, hlb⟩ := mem_badClasses.1 hl
        have hlκ : l ≠ κ := fun e => hlb (e ▸ hκg)
        have hlκ' : l ≠ κ⁻¹ := fun e => hlb (e ▸ hκg')
        refine Finset.mem_erase.2 ⟨hlκ, mem_badClasses.2 ⟨hl1, ?_⟩⟩
        rwa [← hother' l hlκ hlκ']
      have hcard' : (badClasses S (h⁻¹ * c)).card ≤ n := by
        calc (badClasses S (h⁻¹ * c)).card ≤ ((badClasses S c).erase κ).card := Finset.card_le_card hsub
          _ = (badClasses S c).card - 1 := Finset.card_erase_of_mem hκ
          _ ≤ n := by omega
      have hrest := ih (h⁻¹ * c) hg'C hdet' hcard'
      have := Subgroup.mul_mem _ hJ hrest
      rwa [mul_inv_cancel_left] at this

theorem derived_le_sp (hodd : Odd p) (hST : S ≤ spTorus p 3 K) (hS0 : S ≠ ⊥) :
    ⁅Subgroup.centralizer (S : Set (StatedSp 3 K)), Subgroup.centralizer (S : Set (StatedSp 3 K))⁆ ≤
      Jjoin p S := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxy : ⁅x, y⁆ ∈ Subgroup.centralizer (S : Set (StatedSp 3 K)) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
      (Subgroup.inv_mem _ hy)
  exact mem_Jjoin_of_dets hodd hST hS0 _ ⁅x, y⁆ hxy (fun κ _ => detBlk_commutator hST κ hx hy) le_rfl

end Induction

section Shapes

variable {ζ : Kˣ}

omit [CharP K 2] in
theorem two_mul_le_card_spTorus (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot (ζ : K) p)
    [Finite ↥(spTorus p 3 K)] : 2 * p ≤ Nat.card ↥(spTorus p 3 K) := by
  have hpz := units_pow_eq_one hζ
  let f : Fin p × Fin 2 → ↥(spTorus p 3 K) := fun x =>
    ⟨torZ ζ ![((x.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ), 0], torZ_mem ζ _ hpz⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' : torZ ζ ![((i : ℕ) : ℤ), ((j : ℕ) : ℤ), 0] = torZ ζ ![((i' : ℕ) : ℤ), ((j' : ℕ) : ℤ), 0] :=
      congrArg Subtype.val h
    have e0 := congrArg (fun g => mat 3 K g (Sum.inl 0) (Sum.inl 0)) h'
    have e1 := congrArg (fun g => mat 3 K g (Sum.inl 1) (Sum.inl 1)) h'
    simp only [mat_torZ_apply, tv, Sum.elim_inl] at e0 e1
    simp at e0 e1
    have hj2 : ∀ x : Fin 2, (x : ℕ) < p := fun x => lt_of_lt_of_le x.2 (by omega)
    have hi : (i : ℕ) = i' := hζ.pow_inj i.2 i'.2 e0
    have hj : (j : ℕ) = j' := hζ.pow_inj (hj2 j) (hj2 j') e1
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  have := Nat.card_le_card_of_injective f hf
  simpa [mul_comm] using this

omit [CharP K 2] in
theorem ne_bot_of_shape (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot (ζ : K) p) {S : Subgroup (StatedSp 3 K)}
    (hS : S.relIndex (spTorus p 3 K) = p ∨
      ∃ e : StatedSp 3 K, e ∈ spTorus p 3 K ∧ e ≠ 1 ∧ S = Subgroup.zpowers e) : S ≠ ⊥ := by
  rcases hS with h | ⟨e, -, he1, rfl⟩
  · intro hbot
    subst hbot
    rw [Subgroup.relIndex_bot_left] at h
    have hfin : Finite ↥(spTorus p 3 K) := Nat.finite_of_card_ne_zero (by rw [h]; omega)
    have := two_mul_le_card_spTorus (K := K) hp5 hζ
    omega
  · intro h
    apply he1
    have : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
    rw [h] at this
    exact Subgroup.mem_bot.1 this

theorem derived_le_sp' (hp : p.Prime) (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot (ζ : K) p)
    {S : Subgroup (StatedSp 3 K)} (hST : S ≤ spTorus p 3 K)
    (hS : S.relIndex (spTorus p 3 K) = p ∨
      ∃ e : StatedSp 3 K, e ∈ spTorus p 3 K ∧ e ≠ 1 ∧ S = Subgroup.zpowers e) :
    ⁅Subgroup.centralizer (S : Set (StatedSp 3 K)), Subgroup.centralizer (S : Set (StatedSp 3 K))⁆ ≤
      Jjoin p S :=
  derived_le_sp (hp.odd_of_ne_two (by omega)) hST (ne_bot_of_shape hp5 hζ hS)

end Shapes

end CFSG.RankThree.PartOne.KFCL.Sp
