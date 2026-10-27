module

public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Quasithin
open scoped Pointwise

theorem smul_eq_of_pow_eq_one {Γ α : Type*} [Group Γ] [MulAction Γ α] {g : Γ} {r : ℕ}
    (hr : r.Prime) (hg : g ^ r = 1) {Y : Finset α} (hY : ∀ y ∈ Y, g • y ∈ Y)
    (hcard : Y.card < r) {x : α} (hx : x ∈ Y) : g • x = x := by
  classical
  have hmaps : ∀ k : ℕ, (g ^ k) • x ∈ Y := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ', mul_smul]
      exact hY _ ih
  have key : ∀ i j : ℕ, i < j → j < r → (g ^ i) • x = (g ^ j) • x → g • x = x := by
    intro i j hij hjr he
    have hd0 : 0 < j - i := Nat.sub_pos_of_lt hij
    have hfix : (g ^ (j - i)) • x = x := by
      have h1 : g ^ j = g ^ i * g ^ (j - i) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h1, mul_smul] at he
      exact (smul_left_cancel _ he).symm
    have hcop : Nat.Coprime (j - i) r :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hr).mpr fun h =>
        absurd (Nat.le_of_dvd hd0 h) (by omega))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
    have hiter : ∀ n : ℕ, (g ^ ((j - i) * n)) • x = x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.mul_succ, pow_add, mul_smul, hfix, ih]
    have hgm : g ^ ((j - i) * m) = g := by rw [pow_eq_pow_mod _ hg, hm, pow_one]
    rw [← hgm]
    exact hiter m
  obtain ⟨i, hi, j, hj, hij, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range r) (t := Y) (by rwa [Finset.card_range]) (f := fun k => (g ^ k) • x)
    (fun k _ => hmaps k)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h (Finset.mem_range.mp hj) he
  · exact key j i h (Finset.mem_range.mp hi) he.symm

theorem eq_one_of_mem_stabilizer {n r : ℕ} (hr : r.Prime) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ^ r = 1) {sizes : Multiset ℕ} (hs : ∀ k ∈ sizes, k < r)
    (hcard : Multiset.card sizes < r) {P : Finset (Finset (Fin n))}
    (hP : IsPartitionOfType P sizes) (hstab : σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) P) :
    σ = 1 := by
  classical
  obtain ⟨-, -, hcover, hsizes⟩ := hP
  have hPσ : σ • P = P := hstab
  have hPcard : P.card < r := by
    have h1 := congrArg Multiset.card hsizes
    rw [Multiset.card_map, Finset.card_val] at h1
    rw [← h1] at hcard
    exact hcard
  have hblock : ∀ B ∈ P, σ • B = B := by
    intro B hB
    refine smul_eq_of_pow_eq_one hr hσ (fun C hC => ?_) hPcard hB
    rw [← hPσ]
    exact Finset.smul_mem_smul_finset hC
  ext x
  have hx : x ∈ P.biUnion id := by
    rw [hcover]
    exact Finset.mem_univ x
  obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp hx
  have hBr : B.card < r := hs _ (hsizes ▸ Multiset.mem_map_of_mem _ hB)
  have h1 : σ • x = x := by
    refine smul_eq_of_pow_eq_one hr hσ (fun y hy => ?_) hBr hxB
    rw [← hblock B hB]
    exact Finset.smul_mem_smul_finset hy
  simpa using congrArg Fin.val h1

theorem eq_one_of_commute_swap {n r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hnr : n < r + 2)
    {c σ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap) (hc : c ^ r = 1) (hcomm : c * σ = σ * c) :
    c = 1 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := hσ
  have hr3 : 2 < r := lt_of_le_of_ne hr.two_le (Ne.symm hr2)
  have hcomm' : ∀ x, c (Equiv.swap a b x) = Equiv.swap a b (c x) := fun x =>
    congrArg (fun f : Equiv.Perm (Fin n) => f x) hcomm
  have hin : ∀ x, x = a ∨ x = b → c x = a ∨ c x = b := by
    intro x hx
    by_contra hne
    push Not at hne
    have h1 := hcomm' x
    rw [Equiv.swap_apply_of_ne_of_ne hne.1 hne.2] at h1
    have h2 : Equiv.swap a b x = x := c.injective h1
    rcases hx with rfl | rfl
    · rw [Equiv.swap_apply_left] at h2
      exact hab h2.symm
    · rw [Equiv.swap_apply_right] at h2
      exact hab h2
  have hab' : ∀ x ∈ ({a, b} : Finset (Fin n)), c • x ∈ ({a, b} : Finset (Fin n)) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact hin x hx
  have hcardab : ({a, b} : Finset (Fin n)).card < r := by
    rw [Finset.card_pair hab]
    exact hr3
  set Y : Finset (Fin n) := Finset.univ \ {a, b} with hY
  have hYc : ∀ y ∈ Y, c • y ∈ Y := by
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    refine ⟨Finset.mem_univ _, fun h => hy.2 ?_⟩
    have hca : c a = a := smul_eq_of_pow_eq_one hr hc hab' hcardab (by simp)
    have hcb : c b = b := smul_eq_of_pow_eq_one hr hc hab' hcardab (by simp)
    rcases h with h | h
    · left
      exact c.injective (h.trans hca.symm)
    · right
      exact c.injective (h.trans hcb.symm)
  have hYcard : Y.card < r := by
    rw [hY, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_pair hab]
    omega
  ext x
  by_cases hx : x = a ∨ x = b
  · have hmem : x ∈ ({a, b} : Finset (Fin n)) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact hx
    have := smul_eq_of_pow_eq_one hr hc hab' hcardab hmem
    simpa using congrArg Fin.val this
  · have hmem : x ∈ Y := by
      rw [hY, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨Finset.mem_univ _, hx⟩
    have := smul_eq_of_pow_eq_one hr hc hYc hYcard hmem
    simpa using congrArg Fin.val this

end CFSG.Quasithin.H13.Ch4.T425C27
