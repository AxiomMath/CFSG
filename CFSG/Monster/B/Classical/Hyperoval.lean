module

public import Certificates.Certificate16042
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Monster.B.Classical.Plane

open CFSG.Fischer
open scoped LinearAlgebra.Projectivization

@[expose] def IsHyperoval (A : Finset (Fin 21)) : Prop :=
  A.card = 6 ∧ ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → x ≠ z → y ≠ z → ¬Collinear3 x y z

instance : DecidablePred IsHyperoval := fun A => by
  unfold IsHyperoval Collinear3; infer_instance

@[expose] def hyperovals : Finset (Finset (Fin 21)) := Finset.univ.filter IsHyperoval

theorem mem_hyperovals {A : Finset (Fin 21)} : A ∈ hyperovals ↔ IsHyperoval A := by
  simp [hyperovals]

@[expose] def O (i : Fin 3) : Finset (Finset (Fin 21)) := ((orbMasks i).map ofMask).toFinset

@[expose] def leastMask : Fin 3 → ℕ := ![1656, 2740, 3276]

theorem mask_ofMask_orbMasks :
    ∀ i : Fin 3, ∀ m ∈ orbMasks i, mask (ofMask m : Finset (Fin 21)) = m :=
  Certificates.certificate16042.1

theorem mem_O
    {i : Fin 3} {A : Finset (Fin 21)} : A ∈ O i ↔ mask A ∈ orbMasks i := by
  simp only [O, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rwa [mask_ofMask_orbMasks i m hm]
  · intro h
    exact ⟨_, h, ofMask_mask A⟩

theorem orbMasks_nodup : ∀ i : Fin 3, (orbMasks i).Nodup :=
  Certificates.certificate16042.2.1

theorem card_O (i : Fin 3) : (O i).card = 56 := by
  rw [O, List.toFinset_card_of_nodup]
  · rw [List.length_map]
    exact Certificates.certificate16042.2.2.1 i
  · refine (orbMasks_nodup i).map_on fun m hm n hn h => ?_
    rw [← mask_ofMask_orbMasks i m hm, ← mask_ofMask_orbMasks i n hn, h]

theorem orbMasks_disjoint :
    ∀ i j : Fin 3, i ≠ j → ∀ m ∈ orbMasks i, m ∉ orbMasks j :=
  Certificates.certificate16042.2.2.2.1

theorem disjoint_O
    {i j : Fin 3} (h : i ≠ j) : Disjoint (O i) (O j) := by
  rw [Finset.disjoint_left]
  intro A hi hj
  exact orbMasks_disjoint i j h _ (mem_O.1 hi) (mem_O.1 hj)

theorem O_ne {i j : Fin 3} (h : i ≠ j) : O i ≠ O j := by
  intro he
  have hne : (O i).Nonempty := by rw [← Finset.card_pos, card_O]; norm_num
  obtain ⟨A, hA⟩ := hne
  exact Finset.disjoint_left.1 (disjoint_O h) hA (he ▸ hA)

theorem isHyperoval_ofMask_iff (m : ℕ) : IsHyperoval (ofMask m : Finset (Fin 21)) ↔
    (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21, m.testBit x = true →
      m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z → colB x y z = false := by
  simp only [IsHyperoval, ofMask, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => ⟨fun h x y z hx hy hz hxy hxz hyz => ?_,
    fun h x hx y hy z hz hxy hxz hyz hc => ?_⟩
  · have := h x hx y hy z hz hxy hxz hyz
    rw [← colB_iff] at this
    simpa using this
  · have := h x y z hx hy hz hxy hxz hyz
    rw [← colB_iff] at hc
    simp [hc] at this

theorem listed_isHyperoval_of {l : List ℕ}
    (h : ∀ m ∈ l, (ofMask m : Finset (Fin 21)).card = 6 ∧ ∀ x y z : Fin 21, m.testBit x = true →
      m.testBit y = true → m.testBit z = true → x ≠ y → x ≠ z → y ≠ z → colB x y z = false) :
    ∀ m ∈ l, IsHyperoval (ofMask m : Finset (Fin 21)) :=
  fun m hm => (isHyperoval_ofMask_iff m).2 (h m hm)

theorem mem_blocks {l : List ℕ} {m : ℕ} (hm : m ∈ l) :
    m ∈ l.take 14 ∨ m ∈ (l.drop 14).take 14 ∨ m ∈ (l.drop 28).take 14 ∨ m ∈ l.drop 42 := by
  rw [← List.take_append_drop 14 l, List.mem_append] at hm
  rcases hm with h | h
  · exact Or.inl h
  rw [← List.take_append_drop 14 (l.drop 14), List.mem_append, List.drop_drop] at h
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  rw [← List.take_append_drop 14 (l.drop 28), List.mem_append, List.drop_drop] at h
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

section Blocks

set_option maxHeartbeats 8000000

theorem listed_isHyperoval_0_0 : ∀ m ∈ (orbMasks 0).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.1)
theorem listed_isHyperoval_0_1 :
    ∀ m ∈ ((orbMasks 0).drop 14).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.1)
theorem listed_isHyperoval_0_2 :
    ∀ m ∈ ((orbMasks 0).drop 28).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.1)
theorem listed_isHyperoval_0_3 : ∀ m ∈ (orbMasks 0).drop 42,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.1)
theorem listed_isHyperoval_1_0 : ∀ m ∈ (orbMasks 1).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.2.1)
theorem listed_isHyperoval_1_1 :
    ∀ m ∈ ((orbMasks 1).drop 14).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.2.2.1)
theorem listed_isHyperoval_1_2 :
    ∀ m ∈ ((orbMasks 1).drop 28).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.2.2.2.1)
theorem listed_isHyperoval_1_3 : ∀ m ∈ (orbMasks 1).drop 42,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.2.2.2.2.1)
theorem listed_isHyperoval_2_0 : ∀ m ∈ (orbMasks 2).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.2.2.2.2.2.1)
theorem listed_isHyperoval_2_1 :
    ∀ m ∈ ((orbMasks 2).drop 14).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
theorem listed_isHyperoval_2_2 :
    ∀ m ∈ ((orbMasks 2).drop 28).take 14,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
theorem listed_isHyperoval_2_3 : ∀ m ∈ (orbMasks 2).drop 42,
    IsHyperoval (ofMask m : Finset (Fin 21)) :=
  listed_isHyperoval_of (by exact Certificates.certificate16042.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

end Blocks

theorem listed_isHyperoval :
    ∀ m ∈ allMasks, IsHyperoval (ofMask m : Finset (Fin 21)) := by
  intro m hm
  simp only [allMasks, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · rcases mem_blocks hm with h | h | h | h
    exacts [listed_isHyperoval_0_0 m h, listed_isHyperoval_0_1 m h, listed_isHyperoval_0_2 m h,
      listed_isHyperoval_0_3 m h]
  · rcases mem_blocks hm with h | h | h | h
    exacts [listed_isHyperoval_1_0 m h, listed_isHyperoval_1_1 m h, listed_isHyperoval_1_2 m h,
      listed_isHyperoval_1_3 m h]
  · rcases mem_blocks hm with h | h | h | h
    exacts [listed_isHyperoval_2_0 m h, listed_isHyperoval_2_1 m h, listed_isHyperoval_2_2 m h,
      listed_isHyperoval_2_3 m h]

set_option maxHeartbeats 4000000 in
theorem search :
    ∀ x₀ x₁ : Fin 21, x₀ < x₁ → ∀ x₂ : Fin 21, x₁ < x₂ → colB x₀ x₁ x₂ = false →
    ∀ x₃ : Fin 21, x₂ < x₃ →
      (colB x₀ x₁ x₃ = false ∧ colB x₀ x₂ x₃ = false ∧ colB x₁ x₂ x₃ = false) →
    ∀ x₄ : Fin 21, x₃ < x₄ →
      (colB x₀ x₁ x₄ = false ∧ colB x₀ x₂ x₄ = false ∧ colB x₀ x₃ x₄ = false ∧
        colB x₁ x₂ x₄ = false ∧ colB x₁ x₃ x₄ = false ∧ colB x₂ x₃ x₄ = false) →
    ∀ x₅ : Fin 21, x₄ < x₅ →
      (colB x₀ x₁ x₅ = false ∧ colB x₀ x₂ x₅ = false ∧ colB x₀ x₃ x₅ = false ∧
        colB x₀ x₄ x₅ = false ∧ colB x₁ x₂ x₅ = false ∧ colB x₁ x₃ x₅ = false ∧
        colB x₁ x₄ x₅ = false ∧ colB x₂ x₃ x₅ = false ∧ colB x₂ x₄ x₅ = false ∧
        colB x₃ x₄ x₅ = false) →
    2 ^ (x₀ : ℕ) + 2 ^ (x₁ : ℕ) + 2 ^ (x₂ : ℕ) + 2 ^ (x₃ : ℕ) + 2 ^ (x₄ : ℕ) + 2 ^ (x₅ : ℕ) ∈
      allMasks :=
  Certificates.certificate16042.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem colB_false_of_isHyperoval {A : Finset (Fin 21)} (hA : IsHyperoval A) {x y z : Fin 21}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    colB x y z = false := by
  have := hA.2 x hx y hy z hz hxy hxz hyz
  rw [← colB_iff] at this
  simpa using this

theorem mask_mem_allMasks
    {A : Finset (Fin 21)} (hA : IsHyperoval A) : mask A ∈ allMasks := by
  set e := A.orderEmbOfFin hA.1
  have hmem : ∀ k, e k ∈ A := fun k => A.orderEmbOfFin_mem hA.1 k
  have hlt : ∀ k l : Fin 6, k < l → e k < e l := fun k l h => e.strictMono h
  have hne : ∀ k l : Fin 6, k < l → e k ≠ e l := fun k l h => (hlt k l h).ne
  have himg : A = Finset.univ.map e.toEmbedding := by
    rw [← Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact (A.range_orderEmbOfFin hA.1).symm
  have hmask : mask A = 2 ^ (e 0 : ℕ) + 2 ^ (e 1 : ℕ) + 2 ^ (e 2 : ℕ) + 2 ^ (e 3 : ℕ) +
      2 ^ (e 4 : ℕ) + 2 ^ (e 5 : ℕ) := by
    rw [mask, himg, Finset.sum_map, Fin.sum_univ_six]
    rfl
  rw [hmask]
  have c := fun k l m (hkl : k < l) (hlm : l < m) =>
    colB_false_of_isHyperoval hA (hmem k) (hmem l) (hmem m) (hne k l hkl) (hne k m (hkl.trans hlm))
      (hne l m hlm)
  exact search _ _ (hlt 0 1 (by decide)) _ (hlt 1 2 (by decide)) (c 0 1 2 (by decide) (by decide))
    _ (hlt 2 3 (by decide))
    ⟨c 0 1 3 (by decide) (by decide), c 0 2 3 (by decide) (by decide),
      c 1 2 3 (by decide) (by decide)⟩
    _ (hlt 3 4 (by decide))
    ⟨c 0 1 4 (by decide) (by decide), c 0 2 4 (by decide) (by decide),
      c 0 3 4 (by decide) (by decide), c 1 2 4 (by decide) (by decide),
      c 1 3 4 (by decide) (by decide), c 2 3 4 (by decide) (by decide)⟩
    _ (hlt 4 5 (by decide))
    ⟨c 0 1 5 (by decide) (by decide), c 0 2 5 (by decide) (by decide),
      c 0 3 5 (by decide) (by decide), c 0 4 5 (by decide) (by decide),
      c 1 2 5 (by decide) (by decide), c 1 3 5 (by decide) (by decide),
      c 1 4 5 (by decide) (by decide), c 2 3 5 (by decide) (by decide),
      c 2 4 5 (by decide) (by decide), c 3 4 5 (by decide) (by decide)⟩

theorem hyperovals_eq : hyperovals = O 0 ∪ O 1 ∪ O 2 := by
  ext A
  rw [mem_hyperovals, Finset.mem_union, Finset.mem_union, mem_O, mem_O, mem_O]
  constructor
  · intro hA
    have := mask_mem_allMasks hA
    simpa [allMasks, or_assoc] using this
  · intro h
    have hm : mask A ∈ allMasks := by simpa [allMasks, or_assoc] using h
    have := listed_isHyperoval _ hm
    rwa [ofMask_mask] at this

theorem card_hyperovals : hyperovals.card = 168 := by
  rw [hyperovals_eq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_O, card_O,
    card_O]
  · exact disjoint_O (by decide)
  · rw [Finset.disjoint_union_left]
    exact ⟨disjoint_O (by decide), disjoint_O (by decide)⟩

end CFSG.Monster.B.Classical.Plane
