module

public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

variable {G : Type} [Group G]

private theorem conjByElt_mul_aux (s t : G) (K : Subgroup G) :
    conjByElt (s * t) K = conjByElt s (conjByElt t K) := by
  ext x
  rw [mem_conjByElt, mem_conjByElt, mem_conjByElt]
  rw [mul_inv_rev]
  group

private theorem conjByElt_pow_aux {y : G} {L : Subgroup G} (h : conjByElt y L = L) (k : ℕ) :
    conjByElt (y ^ k) L = L := by
  induction k with
  | zero =>
    ext x
    rw [mem_conjByElt]
    simp
  | succ k ih => rw [pow_succ, conjByElt_mul_aux, h, ih]

private theorem mem_normalizer_of_conjByElt_eq_aux {y : G} {L : Subgroup G}
    (h : conjByElt y L = L) : y ∈ Subgroup.normalizer (L : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem conjByElt_eq_self_of_pair {y : G} {m : ℕ} (hm : Odd m) (hym : y ^ m = 1)
    {L L' : Subgroup G} (h1 : conjByElt y L ∈ ({L, L'} : Set (Subgroup G)))
    (h2 : conjByElt y L' ∈ ({L, L'} : Set (Subgroup G))) : conjByElt y L = L := by
  rcases h1 with h1 | h1
  · exact h1
  rcases h2 with h2 | h2
  ·
    have hy2 : conjByElt (y ^ 2) L = L := by
      rw [pow_two, conjByElt_mul_aux, h1, h2]
    obtain ⟨j, rfl⟩ := hm
    have hy : y = (y ^ 2) ^ (j + 1) := by
      rw [← pow_mul]
      have : y ^ (2 * (j + 1)) = y ^ (2 * j + 1) * y := by rw [← pow_succ]; ring_nf
      rw [this, hym, one_mul]
    have h3 := conjByElt_pow_aux hy2 (j + 1)
    rw [← hy] at h3
    exact h3
  ·
    have : L = L' := by
      have e : conjByElt y L = conjByElt y L' := h1.trans h2.symm
      ext x
      have hx := Subgroup.ext_iff.mp e (y * x * y⁻¹)
      rw [mem_conjByElt, mem_conjByElt] at hx
      have : y⁻¹ * (y * x * y⁻¹) * y = x := by group
      rw [this] at hx
      exact hx
    rw [h1, this]

theorem le_normalizer_of_orbits {X S L Y : Subgroup G}
    (hXS : conjSubgroupsBy X L = conjSubgroupsBy S L)
    (hcase : (∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ S, conjSubgroupsBy S L = {L, conjByElt t L}) (hYX : Y ≤ X)
    (hodd : ∀ y ∈ Y, ∃ m : ℕ, Odd m ∧ y ^ m = 1) : Y ≤ Subgroup.normalizer (L : Set G) := by
  intro y hy
  obtain ⟨m, hm, hym⟩ := hodd y hy
  have hyΩ : conjByElt y L ∈ conjSubgroupsBy S L := by
    rw [← hXS]
    exact ⟨y, hYX hy, rfl⟩
  rcases hcase with hnorm | ⟨t, htS, hset⟩
  · refine mem_normalizer_of_conjByElt_eq_aux ?_
    obtain ⟨s, hs, hse⟩ := hyΩ
    rw [hse]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm s hs)
  · refine mem_normalizer_of_conjByElt_eq_aux
      (conjByElt_eq_self_of_pair (L' := conjByElt t L) hm hym ?_ ?_)
    · rw [hset] at hyΩ
      exact hyΩ
    · have hLt : conjByElt t L ∈ conjSubgroupsBy X L := by
        rw [hXS, hset]
        exact Or.inr rfl
      obtain ⟨g, hg, hge⟩ := hLt
      have : conjByElt y (conjByElt t L) ∈ conjSubgroupsBy X L := by
        refine ⟨y * g, X.mul_mem (hYX hy) hg, ?_⟩
        show _ = conjByElt (y * g) L
        rw [conjByElt_mul_aux]
        rw [show conjByElt g L = L.map (MulAut.conj g).toMonoidHom from rfl, ← hge]
      rw [hXS, hset] at this
      exact this

theorem exists_odd_pow_eq_one_of_isPGroup {Y : Subgroup G} {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hY : IsPGroup p Y) : ∀ a ∈ Y, ∃ m : ℕ, Odd m ∧ a ^ m = 1 := by
  intro a ha
  obtain ⟨k, hk⟩ := hY ⟨a, ha⟩
  refine ⟨p ^ k, ?_, by simpa using congrArg Subtype.val hk⟩
  rcases hp with rfl | rfl <;> exact Odd.pow (by decide)

end CFSG.Quasithin
