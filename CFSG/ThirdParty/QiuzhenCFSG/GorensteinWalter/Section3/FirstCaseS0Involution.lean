module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUniformReflection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The involution in the cyclic half of the fixed dihedral Sylow subgroup
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private lemma unique_involution_of_cyclic_two_group_local
    {A : Type*} [Group A] [Finite A]
    (hcyc : IsCyclic A) {m : ℕ} (hm : 1 ≤ m)
    (hcard : Nat.card A = 2 ^ m) :
    ∀ x y : A, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y := by
  classical
  let : IsCyclic A := hcyc
  rcases IsCyclic.exists_monoid_generator (α := A) with ⟨g, hg⟩
  have hord : orderOf g = 2 ^ m := by
    rw [← hcard]
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    rcases hg x with ⟨k, rfl⟩
    exact ⟨k, zpow_natCast g k⟩
  have hmm : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h2m : 2 * 2 ^ (m - 1) = 2 ^ m := by
    calc
      2 * 2 ^ (m - 1) = 2 ^ (m - 1) * 2 := by rw [Nat.mul_comm]
      _ = 2 ^ (m - 1 + 1) := by exact (pow_succ 2 (m - 1)).symm
      _ = 2 ^ m := by rw [hmm]
  have hgpow : g ^ (2 ^ m) = 1 := by
    exact (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 ^ m)).1 (by simp [hord])
  have h2h : (g ^ (2 ^ (m - 1))) ^ 2 = 1 := by
    calc
      (g ^ (2 ^ (m - 1))) ^ 2 = g ^ (2 ^ (m - 1) * 2) := by
        exact (pow_mul g (2 ^ (m - 1)) 2).symm
      _ = g ^ (2 * 2 ^ (m - 1)) := by rw [Nat.mul_comm]
      _ = g ^ (2 ^ m) := by rw [h2m]
      _ = 1 := hgpow
  have h_pow_odd : ∀ k : ℕ,
      (g ^ (2 ^ (m - 1))) ^ (2 * k + 1) = g ^ (2 ^ (m - 1)) := by
    intro k
    calc
      (g ^ (2 ^ (m - 1))) ^ (2 * k + 1) =
          (g ^ (2 ^ (m - 1))) ^ (2 * k) * g ^ (2 ^ (m - 1)) := by
        exact pow_succ (g ^ (2 ^ (m - 1))) (2 * k)
      _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k * g ^ (2 ^ (m - 1)) := by
        exact congrArg (fun z : A => z * g ^ (2 ^ (m - 1)))
          (pow_mul (g ^ (2 ^ (m - 1))) 2 k)
      _ = 1 ^ k * g ^ (2 ^ (m - 1)) := by rw [h2h]
      _ = g ^ (2 ^ (m - 1)) := by simp
  intro x y hx1 hx2 hy1 hy2
  rcases hg x with ⟨a, rfl⟩
  rcases hg y with ⟨b, rfl⟩
  have hxa : orderOf g ∣ 2 * a := by
    apply (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 * a)).2
    simpa [pow_mul, Nat.mul_comm] using hx2
  have hya : orderOf g ∣ 2 * b := by
    apply (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 * b)).2
    simpa [pow_mul, Nat.mul_comm] using hy2
  have hdiv_a : 2 ^ (m - 1) ∣ a := by
    rw [hord] at hxa
    rw [← h2m] at hxa
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hxa
  have hdiv_b : 2 ^ (m - 1) ∣ b := by
    rw [hord] at hya
    rw [← h2m] at hya
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hya
  rcases hdiv_a with ⟨a', rfl⟩
  rcases hdiv_b with ⟨b', rfl⟩
  have hx_ne : (g ^ (2 ^ (m - 1))) ^ a' ≠ 1 := by
    simpa [pow_mul] using hx1
  have hy_ne : (g ^ (2 ^ (m - 1))) ^ b' ≠ 1 := by
    simpa [pow_mul] using hy1
  have hodd_a : Odd a' := by
    rcases Nat.even_or_odd a' with he | ho
    · exfalso
      rcases he with ⟨k, rfl⟩
      have hkk : (g ^ (2 ^ (m - 1))) ^ (k + k) = 1 := by
        calc
          (g ^ (2 ^ (m - 1))) ^ (k + k) =
              (g ^ (2 ^ (m - 1))) ^ (2 * k) := by rw [Nat.two_mul]
          _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k := by
            exact pow_mul (g ^ (2 ^ (m - 1))) 2 k
          _ = 1 ^ k := by rw [h2h]
          _ = 1 := by simp
      exact hx_ne hkk
    · exact ho
  have hodd_b : Odd b' := by
    rcases Nat.even_or_odd b' with he | ho
    · exfalso
      rcases he with ⟨k, rfl⟩
      have hkk : (g ^ (2 ^ (m - 1))) ^ (k + k) = 1 := by
        calc
          (g ^ (2 ^ (m - 1))) ^ (k + k) =
              (g ^ (2 ^ (m - 1))) ^ (2 * k) := by rw [Nat.two_mul]
          _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k := by
            exact pow_mul (g ^ (2 ^ (m - 1))) 2 k
          _ = 1 ^ k := by rw [h2h]
          _ = 1 := by simp
      exact hy_ne hkk
    · exact ho
  rcases hodd_a with ⟨ka, rfl⟩
  rcases hodd_b with ⟨kb, rfl⟩
  calc
    g ^ (2 ^ (m - 1) * (2 * ka + 1)) =
        (g ^ (2 ^ (m - 1))) ^ (2 * ka + 1) := by
      exact pow_mul g (2 ^ (m - 1)) (2 * ka + 1)
    _ = g ^ (2 ^ (m - 1)) := h_pow_odd ka
    _ = (g ^ (2 ^ (m - 1))) ^ (2 * kb + 1) := (h_pow_odd kb).symm
    _ = g ^ (2 ^ (m - 1) * (2 * kb + 1)) := by
      exact (pow_mul g (2 ^ (m - 1)) (2 * kb + 1)).symm

public theorem firstCase_S0_involution_eq_t
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G}
    (hsS0 : s ∈ c.S0) (hs : IsInvolution s) : s = c.t := by
  classical
  have hcardS : Nat.card (↥(c.S : Subgroup G)) = 2 * 2 ^ c.m := by
    rcases c.dihedralEquiv with ⟨e⟩
    calc
      Nat.card ↥(c.S : Subgroup G) = Nat.card (DihedralGroup (2 ^ c.m)) :=
        Nat.card_congr e.toEquiv
      _ = 2 * 2 ^ c.m := by
        rw [Nat.card_eq_fintype_card]
        exact DihedralGroup.card
  have hcardS0 : Nat.card ↥c.S0 = 2 ^ c.m := by
    have h1 : Nat.card ↥(c.S : Subgroup G) = 2 * Nat.card ↥c.S0 := c.S_index_two
    rw [hcardS] at h1
    exact (Nat.mul_left_cancel (by norm_num) h1).symm
  have huniq : ∀ x y : ↥c.S0, x ≠ 1 → x ^ 2 = 1 →
      y ≠ 1 → y ^ 2 = 1 → x = y :=
    unique_involution_of_cyclic_two_group_local c.S0_cyclic c.one_le_m hcardS0
  have htne : (⟨c.t, c.t_mem_S0⟩ : ↥c.S0) ≠ 1 := by
    intro h
    exact c.t_involution.1 (by simpa using congrArg Subtype.val h)
  have hteq : (⟨s, hsS0⟩ : ↥c.S0) = ⟨c.t, c.t_mem_S0⟩ := by
    apply huniq
    · intro h
      exact hs.1 (by simpa using congrArg Subtype.val h)
    · simpa [pow_two] using hs.2
    · exact htne
    · simpa [pow_two] using c.t_involution.2
  exact congrArg Subtype.val hteq

end CFSG.GorensteinWalter
