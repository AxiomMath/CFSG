module

public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem foldr_rep {letters : Array Table} {lG : ℕ → G} {lv : Array ℕ}
    (hrep : ∀ l ∈ lv, Rep n letters[l]! (lG l)) :
    ∀ (w : List ℕ), (∀ l ∈ w, l ∈ lv) → ∀ x < n,
      w.foldr (fun l z => ap letters[l]! z) x = idx n (w.map lG).prod x ∧
        (w.map lG).prod ∈ lettersGroup lv lG
  | [], _, x, _ => ⟨by rw [List.map_nil, List.prod_nil, idx_one]; rfl, (lettersGroup lv lG).one_mem⟩
  | l :: w, hw, x, hx => by
    obtain ⟨ih1, ih2⟩ := foldr_rep hrep w (fun l' h => hw l' (List.mem_cons_of_mem l h)) x hx
    have hl := hw l List.mem_cons_self
    refine ⟨?_, ?_⟩
    · rw [List.foldr_cons, ih1, hrep l hl _ (idx_lt _ hx), List.map_cons, List.prod_cons, idx_mul]
    · rw [List.map_cons, List.prod_cons]
      exact (lettersGroup lv lG).mul_mem (lG_mem hl) ih2

theorem orbit_of_set {letters : Array Table} {lG : ℕ → G} {lv : Array ℕ}
    (hrep : ∀ l ∈ lv, Rep n letters[l]! (lG l)) {y : ℕ} (hy : y < n) (P : Finset ℕ)
    (hyP : y ∈ P) (hPn : ∀ x ∈ P, x < n) (hcl : ∀ x ∈ P, ∀ l ∈ lv, ap letters[l]! x ∈ P)
    (hw : ∀ x ∈ P, ∃ w : List ℕ, (∀ l ∈ w, l ∈ lv) ∧ w.foldr (fun l z => ap letters[l]! z) x = y) :
    MulAction.orbit (lettersGroup lv lG) (⟨y, hy⟩ : Fin n) = {p | p.val ∈ P} ∧
      Nat.card (MulAction.orbit (lettersGroup lv lG) (⟨y, hy⟩ : Fin n)) = P.card := by
  classical
  set Q : Finset (Fin n) := Finset.univ.filter fun p => p.val ∈ P with hQ
  have memQ : ∀ p : Fin n, p ∈ Q ↔ p.val ∈ P := fun p => by simp [hQ]
  have gen : ∀ l ∈ lv, ∀ p ∈ Q, lG l • p ∈ Q := by
    intro l hl p hp
    rw [memQ] at hp ⊢
    rw [← idx_of_lt (lG l) p.isLt, ← hrep l hl _ p.isLt]
    exact hcl _ hp l hl
  have inv : ∀ g : G, (∀ p ∈ Q, g • p ∈ Q) → ∀ p ∈ Q, g⁻¹ • p ∈ Q := by
    intro g hg p hp
    have hsub : Q.image (g • ·) ⊆ Q := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
      exact hg r hr
    have hcard : Q.card ≤ (Q.image (g • ·)).card := by
      rw [Finset.card_image_of_injective _ (MulAction.injective g)]
    have he := Finset.eq_of_subset_of_card_le hsub hcard
    rw [← he] at hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
    rwa [inv_smul_smul]
  have keep : ∀ g ∈ lettersGroup lv lG, ∀ p ∈ Q, g • p ∈ Q := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact gen l hl
    | one => intro p hp; rwa [one_smul]
    | mul x z _ _ hx hz => intro p hp; rw [mul_smul]; exact hx _ (hz p hp)
    | inv x _ hx => exact inv x hx
  have hset : MulAction.orbit (lettersGroup lv lG) (⟨y, hy⟩ : Fin n) = {p | p.val ∈ P} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      exact (memQ _).1 (keep g hg _ ((memQ _).2 hyP))
    · intro hp
      obtain ⟨w, hwl, hwy⟩ := hw p.val hp
      obtain ⟨e, hm⟩ := foldr_rep hrep w hwl p.val p.isLt
      refine ⟨⟨((w.map lG).prod)⁻¹, (lettersGroup lv lG).inv_mem hm⟩, ?_⟩
      change ((w.map lG).prod)⁻¹ • (⟨y, hy⟩ : Fin n) = p
      rw [inv_smul_eq_iff]
      apply Fin.ext
      rw [← idx_of_lt _ p.isLt, ← e, hwy]
  refine ⟨hset, ?_⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
  have hmap : (Finset.univ.filter fun p : Fin n => p.val ∈ P).map Fin.valEmbedding = P := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hx; exact ⟨⟨x, hPn x hx⟩, hx, rfl⟩
  have hto : Set.toFinset {p : Fin n | p.val ∈ P} =
      Finset.univ.filter fun p : Fin n => p.val ∈ P := by
    ext p
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hto]
  conv_rhs => rw [← hmap]
  rw [Finset.card_map]

theorem chain_of_orbits [Finite G] {letters : Array Table} {lG : ℕ → G} {base : Array ℕ}
    (hrep : ∀ l < letters.size, Rep n letters[l]! (lG l))
    (hb : ∀ i < base.size, base[i]! < n) (s : ℕ → ℕ)
    (horb : ∀ i (hi : i < base.size), Nat.card (MulAction.orbit (levelGroup letters base lG i)
      (⟨base[i]!, hb i hi⟩ : Fin n)) = s i)
    (htop : levelGroup letters base lG 0 = ⊤)
    (hcard : Nat.card G = ∏ l ∈ Finset.range base.size, s l) :
    (∀ i < base.size, ∀ g ∈ levelGroup letters base lG i,
      idx n g base[i]! = base[i]! ↔ g ∈ levelGroup letters base lG (i + 1)) ∧
      ∀ i ≤ base.size, Nat.card (levelGroup letters base lG i) =
        ∏ l ∈ Finset.Ico i base.size, s l := by
  set H := levelGroup letters base lG with hH
  set m := base.size with hm
  have fixes : ∀ i < m, ∀ g ∈ H (i + 1), idx n g base[i]! = base[i]! := by
    intro i hi g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      have h2 := (mem_levelLetters_succ.1 hl).2
      rw [← hrep l (levelLetters_lt hl) _ (hb i hi), h2]
    | one => exact idx_one _
    | mul x z _ _ hx hz => rw [idx_mul, hz, hx]
    | inv x _ hx =>
      have := idx_inv_idx (n := n) x base[i]!
      rwa [hx] at this
  have fix_iff : ∀ i (hi : i < m) (g : G), g • (⟨base[i]!, hb i hi⟩ : Fin n) =
      ⟨base[i]!, hb i hi⟩ ↔ idx n g base[i]! = base[i]! := by
    intro i hi g
    rw [idx_of_lt g (hb i hi)]
    exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  set S : ℕ → Subgroup G := fun i =>
    if hi : i < m then H i ⊓ MulAction.stabilizer G (⟨base[i]!, hb i hi⟩ : Fin n) else H i
    with hS
  have hSi : ∀ i (hi : i < m), S i = H i ⊓ MulAction.stabilizer G (⟨base[i]!, hb i hi⟩ : Fin n) :=
    fun i hi => by simp only [hS, dif_pos hi]
  have orbS : ∀ i (hi : i < m), Nat.card (H i) = s i * Nat.card (S i) := by
    intro i hi
    rw [← horb i hi, hSi i hi]
    exact card_eq_orbit_mul (H i) _ _ inf_le_left (fun l hl => (Subgroup.mem_inf.1 hl).2)
      (fun h hh hp => Subgroup.mem_inf.2 ⟨hh, hp⟩)
  have leS : ∀ i (hi : i < m), H (i + 1) ≤ S i := by
    intro i hi g hg
    rw [hSi i hi]
    refine Subgroup.mem_inf.2 ⟨levelGroup_anti lG (Nat.le_succ i) hg, ?_⟩
    rw [MulAction.mem_stabilizer_iff, fix_iff i hi]
    exact fixes i hi g hg
  have spos : ∀ i (hi : i < m), 0 < s i := by
    intro i hi
    rw [← horb i hi]
    exact Nat.card_pos_iff.2 ⟨⟨_, MulAction.mem_orbit_self _⟩, inferInstance⟩
  have lower : ∀ k ≤ m, ∏ l ∈ Finset.Ico (m - k) m, s l ≤ Nat.card (H (m - k)) := by
    intro k
    induction k with
    | zero => intro _; simp only [Nat.sub_zero, Finset.Ico_self, Finset.prod_empty]; exact Nat.card_pos
    | succ k ih =>
      intro hk
      have hi : m - (k + 1) < m := by omega
      have e : m - (k + 1) + 1 = m - k := by omega
      rw [Finset.prod_eq_prod_Ico_succ_bot hi, e, orbS _ hi]
      refine Nat.mul_le_mul_left _ ((ih (by omega)).trans ?_)
      rw [← e]
      exact Subgroup.card_le_of_le (leS _ hi)
  have lower' : ∀ i ≤ m, ∏ l ∈ Finset.Ico i m, s l ≤ Nat.card (H i) := by
    intro i hi
    have := lower (m - i) (by omega)
    rwa [show m - (m - i) = i by omega] at this
  have exact : ∀ i ≤ m, Nat.card (H i) = ∏ l ∈ Finset.Ico i m, s l ∧
      (0 < i → ∀ g ∈ H (i - 1), idx n g base[i - 1]! = base[i - 1]! ↔ g ∈ H i) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
      rw [htop, Subgroup.card_top, hcard, Finset.range_eq_Ico]
    | succ i ih =>
      intro hi
      have hi' : i < m := by omega
      obtain ⟨h1, -⟩ := ih (by omega)
      rw [orbS i hi', Finset.prod_eq_prod_Ico_succ_bot hi'] at h1
      have hS' : Nat.card (S i) = ∏ l ∈ Finset.Ico (i + 1) m, s l :=
        Nat.eq_of_mul_eq_mul_left (spos i hi') h1
      have hle := Subgroup.card_le_of_le (leS i hi')
      have hge := lower' (i + 1) hi
      have hc : Nat.card (H (i + 1)) = ∏ l ∈ Finset.Ico (i + 1) m, s l := by omega
      have heq : H (i + 1) = S i := Subgroup.eq_of_le_of_card_ge (leS i hi') (by omega)
      refine ⟨hc, fun _ g hg => ?_⟩
      simp only [Nat.add_sub_cancel]
      rw [heq, hSi i hi', Subgroup.mem_inf, MulAction.mem_stabilizer_iff, fix_iff i hi']
      exact ⟨fun h => ⟨hg, h⟩, fun h => h.2⟩
  refine ⟨fun i hi g hg => ?_, fun i hi => (exact i hi).1⟩
  have := (exact (i + 1) (by omega)).2 (Nat.succ_pos i) g
  simp only [Nat.add_sub_cancel] at this
  exact this hg

end CFSG.Perm
