module

public import CFSG.RankThree.PartTwo.Sec10.Item108
public import CFSG.RankThree.PartTwo.Sec11.Final
public import CFSG.RankThree.PartTwo.KFacts.K73Lines

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Group

variable {G : Type*} [Group G]

theorem conj_pow_odd_eq {g y z : G} (hz : g * z * g⁻¹ = z) (hzy : z * y = y * z)
    (hg : g * y * g⁻¹ = z * y⁻¹) (n : ℕ) :
    g ^ (2 * n + 1) * y * (g ^ (2 * n + 1))⁻¹ = z * y⁻¹ := by
  have h2 : g ^ 2 * y * (g ^ 2)⁻¹ = y := by
    have e : g ^ 2 * y * (g ^ 2)⁻¹ = (g * z * g⁻¹) * (g * y * g⁻¹)⁻¹ := by
      calc g ^ 2 * y * (g ^ 2)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by
            simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = g * (z * y⁻¹) * g⁻¹ := by rw [hg]
        _ = (g * z * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
    rw [e, hz, hg, mul_inv_rev, inv_inv, ← mul_assoc, hzy, mul_assoc, mul_inv_cancel, mul_one]
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    have e : g ^ (2 * (n + 1) + 1) * y * (g ^ (2 * (n + 1) + 1))⁻¹ =
        g ^ (2 * n + 1) * (g ^ 2 * y * (g ^ 2)⁻¹) * (g ^ (2 * n + 1))⁻¹ := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add]
      group
    rw [e, h2, ih]

theorem exists_three_pow_eq_odd (k : ℕ) : ∃ n, 3 ^ k = 2 * n + 1 :=
  ⟨3 ^ k / 2, by have := Nat.odd_iff.mp (Odd.pow (by decide : Odd 3) : Odd (3 ^ k)); omega⟩

theorem conj_eq_self_of_threeElement {g y : G} (hy3 : y ^ 3 = 1) (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1)
    (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y) : g * y * g⁻¹ = y := by
  obtain ⟨k, hk⟩ := hg3
  have hle : Subgroup.zpowers y ≤ Subgroup.closure ({y, 1} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨i, j, hi, -, hij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair (d := (1 : G))
    (by group) hy3 (by group) (hle hgy)
  rw [one_pow, mul_one] at hij
  have hyinv : y⁻¹ = y ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hy3]
  interval_cases i
  · rw [pow_zero] at hij
    have hy : y = 1 := by
      have h1 : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [h1, hij]
      group
    rw [hij, hy]
  · rwa [pow_one] at hij
  · obtain ⟨n, hn⟩ := exists_three_pow_eq_odd k
    have h := conj_pow_odd_eq (g := g) (y := y) (z := 1) (by group) (by group)
      (by rw [hij, one_mul, hyinv]) n
    rw [← hn, hk, one_mul, inv_one, mul_one, one_mul] at h
    have hy : y = 1 := by
      have h1 : y * y = 1 := by
        calc y * y = y * y⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel y
      calc y = y ^ 3 * (y * y)⁻¹ := by group
        _ = 1 := by rw [hy3, h1]; group
    rw [hij, hy, one_pow]

end Group

section Data

variable {G : Type} [Group G] [Finite G]

theorem Sec11Data.htrans_of_mem_normalizer {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hgdN : g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} →
      Nat.card F = Nat.card (Subgroup.zpowers c) → F ≠ Subgroup.zpowers d →
        ∃ p ∈ sec11P R g, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom := by
  have hAe := h.mem_partTwoF.1
  have hcA : c ∈ A := h.mem_A
  have hdA : d ∈ A := by
    have : d ∈ A ⊓ L := by
      rw [h.inf_eq]
      exact Subgroup.mem_zpowers d
    exact this.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcd : c * d = d * c := congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩)
  have hgP : g ∈ sec11P R g :=
    (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)
  have hgd : g * d * g⁻¹ = d :=
    conj_eq_self_of_threeElement hd3 h.pow_eq_one
      ((Subgroup.mem_normalizer_iff.mp hgdN d).mp (Subgroup.mem_zpowers d))
  have hgdm : ∀ m : ℕ, g * d ^ m * g⁻¹ = d ^ m := fun m => by rw [← conj_pow, hgd]
  have hgdm' : ∀ m : ℕ, g⁻¹ * d ^ m * g = d ^ m := fun m => by
    calc g⁻¹ * d ^ m * g = g⁻¹ * (g * d ^ m * g⁻¹) * g := by rw [hgdm]
      _ = d ^ m := by group
  have hgc : g * c * g⁻¹ ∉ Subgroup.zpowers c := fun hmem =>
    h.g_not_mem (Sec10.mem_normalizer_zpowers_of_conj_mem hmem)
  have hcd' : ∀ m : ℕ, c ≠ d ^ m := by
    intro m hm
    apply hgc
    rw [hm, hgdm]
    exact Subgroup.mem_zpowers _
  obtain ⟨i, j, hi, hj, hij⟩ :=
    KFacts.exists_pow_mul_pow_of_mem_closure_pair hcd hc3 hd3 h.conj_mem
  have hcdj : c * d ^ j = d ^ j * c := (Commute.pow_right hcd j).eq
  have hi1 : i = 1 := by
    interval_cases i
    · exfalso
      rw [pow_zero, one_mul] at hij
      apply hcd' j
      calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
        _ = d ^ j := by rw [hij, hgdm']
    · rfl
    · exfalso
      obtain ⟨k, hk⟩ := h.pow_eq_one
      obtain ⟨n, hn⟩ := exists_three_pow_eq_odd k
      have hcinv : c⁻¹ = c ^ 2 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', hc3]
      have hcomm2 : c ^ 2 * d ^ j = d ^ j * c ^ 2 :=
        ((Commute.pow_right hcd j).pow_left 2).eq
      have hij' : g * c * g⁻¹ = d ^ j * c⁻¹ := by
        rw [hij, hcomm2, ← hcinv]
      have h1 := conj_pow_odd_eq (hgdm j) hcdj.symm hij' n
      rw [← hn, hk, one_mul, inv_one, mul_one] at h1
      have h2 : c * c = d ^ j := by
        calc c * c = d ^ j * c⁻¹ * c := by rw [← h1]
          _ = d ^ j := by group
      apply hcd' (j * 2)
      calc c = c ^ 3 * c := by rw [hc3, one_mul]
        _ = (c * c) ^ 2 := by rw [pow_two, pow_three]; simp only [mul_assoc]
        _ = d ^ (j * 2) := by rw [h2, ← pow_mul]
  subst hi1
  rw [pow_one] at hij
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hgc
    rw [hij, pow_zero, mul_one]
    exact Subgroup.mem_zpowers c
  have hzp : Subgroup.zpowers (d ^ j) = Subgroup.zpowers d := by
    interval_cases j
    · exact absurd rfl hj0
    · rw [pow_one]
    · exact KFacts.zpowers_sq_eq hd3
  have hcl : Subgroup.closure ({c, d ^ j} : Set G) = Subgroup.closure {c, d} := by
    have hdj : d ^ j ∈ Subgroup.closure ({c, d} : Set G) :=
      Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) j
    have hd : d ∈ Subgroup.closure ({c, d ^ j} : Set G) := by
      have h1 : d ∈ Subgroup.zpowers (d ^ j) := by
        rw [hzp]
        exact Subgroup.mem_zpowers d
      have h2 : Subgroup.zpowers (d ^ j) ≤ Subgroup.closure ({c, d ^ j} : Set G) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      exact h2 h1
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact hdj
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact hd
  have hdj3 : (d ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hd3, one_pow]
  have hxd : g * d ^ j = d ^ j * g := by
    calc g * d ^ j = g * d ^ j * g⁻¹ * g := by group
      _ = d ^ j * g := by rw [hgdm]
  have key := KFacts.exists_conj_eq_of_conj_eq_mul hgP hcdj hc3 hdj3 hij hxd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hc3 h.ne_one
  intro F hF hcard hFd
  exact key F (hcl ▸ hF) (hcard.trans h3) (hzp ▸ hFd)

theorem Sec11Data.htrans {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (_hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    ∀ F : Subgroup G, F ≤ Subgroup.closure {c, d} →
      Nat.card F = Nat.card (Subgroup.zpowers c) → F ≠ Subgroup.zpowers d →
        ∃ p ∈ sec11P R g, F = (Subgroup.zpowers c).map (MulAut.conj p).toMonoidHom :=
  h.htrans_of_mem_normalizer (hNd (Subgroup.le_normalizer
    ((le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g))))

end Data

end CFSG.RankThree.PartTwo.Sec11
