module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

namespace S153EB6

theorem card_two_cases {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (c : K) :
    c = 0 ∨ c = 1 := by
  rw [Nat.card_eq_two_iff] at hK
  obtain ⟨u, v, huv, hs⟩ := hK
  by_contra hcon
  push Not at hcon
  have h0 : (0 : K) ∈ ({u, v} : Set K) := by rw [hs]; trivial
  have h1 : (1 : K) ∈ ({u, v} : Set K) := by rw [hs]; trivial
  have hc : c ∈ ({u, v} : Set K) := by rw [hs]; trivial
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1 hc
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases hc with hc | hc <;>
    first
    | exact absurd (h0.trans h1.symm) zero_ne_one
    | exact absurd (hc.trans h0.symm) hcon.1
    | exact absurd (hc.trans h1.symm) hcon.2

theorem two_eq_zero_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    (2 : K) = 0 := by
  rcases card_two_cases hK (1 + 1) with h | h
  · rw [one_add_one_eq_two] at h; exact h
  · exact absurd (add_eq_right.mp h) one_ne_zero

theorem exists_three_agree {K : Type} [Finite K] (hK : Nat.card K = 2) (n : ℕ) (hn : 5 ≤ n)
    (x : Fin n → K) :
    ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x a = x b ∧ x a = x c := by
  classical
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card x
    (n := 2) (by simp [hcard]; omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  exact ⟨a, b, c, hab, hac, hbc, ha.trans hb.symm, ha.trans hc.symm⟩

theorem cyc3_pow {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1 := by
  ext x
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id_eq]
  by_cases hxa : x = a
  · subst hxa
    simp [Equiv.swap_apply_def, hab, hac, hac.symm, hbc.symm]
  by_cases hxb : x = b
  · subst hxb
    simp [Equiv.swap_apply_def, hab, hac, hac.symm, hbc.symm]
  by_cases hxc : x = c
  · subst hxc
    simp [Equiv.swap_apply_def, hab, hac, hac.symm, hbc.symm]
  simp [Equiv.swap_apply_def, hxa, hxb, hxc]

theorem cyc3_inv {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Equiv.swap a b * Equiv.swap b c)⁻¹ a = c ∧ (Equiv.swap a b * Equiv.swap b c)⁻¹ b = a ∧
    (Equiv.swap a b * Equiv.swap b c)⁻¹ c = b ∧
    ∀ x, x ≠ a → x ≠ b → x ≠ c → (Equiv.swap a b * Equiv.swap b c)⁻¹ x = x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp [Equiv.swap_apply_def, hab, hac]
  · simp [Equiv.swap_apply_def, hac.symm, hbc.symm]
  · intro x hxa hxb hxc
    simp [Equiv.swap_apply_def, hxa, hxb, hxc]

theorem perm_cyc (n : ℕ) (hn : 5 ≤ n) (m : G6.PermMod n) :
    ∃ γ : Equiv.Perm (Fin n), γ ^ 3 = 1 ∧ G6.permAct n γ m = m ∧
      ∃ m' ∈ G6.coreMod n, G6.permAct n γ m' * m'⁻¹ ∉ Subgroup.zpowers (G6.allOnes n) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hmb, hmc⟩ := exists_three_agree (K := ZMod 2) (by simp) n hn
    (Multiplicative.toAdd m)
  obtain ⟨d, hda, hdb, hdc⟩ : ∃ d : Fin n, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := by
      intro d _
      by_cases h1 : d = a
      · simp [h1]
      by_cases h2 : d = b
      · simp [h2]
      simp [hcon d h1 h2]
    have h1 := Finset.card_le_card hsub
    have h3 : ({a, b, c} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨hia, hib, hic, hio⟩ := cyc3_inv hab hac hbc
  refine ⟨Equiv.swap a b * Equiv.swap b c, cyc3_pow hab hac hbc, ?_, ?_⟩
  · apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply]
    by_cases h1 : i = a
    · subst h1; rw [hia]; exact hmc.symm
    by_cases h2 : i = b
    · subst h2; rw [hib]; exact hmb
    by_cases h3 : i = c
    · subst h3; rw [hic]; exact hmb.symm.trans hmc
    rw [hio i h1 h2 h3]
  · refine ⟨Multiplicative.ofAdd (Pi.single a 1 + Pi.single d 1), ?_, ?_⟩
    · rw [G6.mem_coreMod]
      simp [Finset.sum_add_distrib]
      decide
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      have hA := congrFun (congrArg Multiplicative.toAdd hk) a
      have hD := congrFun (congrArg Multiplicative.toAdd hk) d
      simp [G6.permAct_apply, G6.allOnes, Equiv.swap_apply_of_ne_of_ne hda hdb,
        Equiv.swap_apply_of_ne_of_ne hdb hdc, hac.symm, hdc.symm, hda.symm] at hA hD
      rw [hA] at hD
      revert hD
      decide

end S153EB6

end CFSG.Quasithin
