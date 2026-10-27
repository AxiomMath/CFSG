module

public import CFSG.Quasithin.Vol2.Ch10SecKL7k

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem le_four_of_dvd_105 {c : ℕ} (h : 2 ^ c - 1 ∣ 105) : c ≤ 4 := by
  by_contra hc
  rcases (show c = 5 ∨ c = 6 ∨ 7 ≤ c by omega) with rfl | rfl | h7
  · norm_num at h
  · norm_num at h
  · have h1 := Nat.le_of_dvd (by norm_num) h
    have h2 : 2 ^ 7 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) h7
    omega

variable {W : Type} [CommGroup W]

namespace Hyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem mul_mem_K {x y : MulAut W} (hx : x ∈ Mb) (hy : y ∈ Mb) :
    x * y ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) ↔
      (x ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) ↔
        y ∈ Subgroup.normalizer (L₁ : Set (MulAut W))) := by
  simp only [mem_normalizer_iff_map]
  exact h.map_conj_mul_iff hx hy

theorem mem_K_pow_iff (n : ℕ) :
    τ ^ n ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) ↔ Even n := by
  have hτ : τ ∉ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
    rw [mem_normalizer_iff_map, h.mapL]
    exact fun h1 => h.ne_L h1.symm
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, h.mul_mem_K (pow_mem h.memτ n) h.memτ, Nat.even_add_one]
    constructor
    · intro h2 h3
      exact hτ (h2.1 (ih.2 h3))
    · intro h2
      exact ⟨fun h3 => absurd (ih.1 h3) h2, fun h3 => absurd h3 hτ⟩

variable (hR : RHyp Mb L₁ L₂ R)
include hR

theorem orderOf_dvd_105 {y : MulAut W} (hy : y ∈ Mb) (hodd : Odd (orderOf y)) :
    orderOf y ∣ 105 := by
  obtain ⟨c₁⟩ := h.coord
  obtain ⟨c₂⟩ := h.swap.coord
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h.exists_decomp hy (h.map_conj_of_odd hy hodd)
  have hm := pow_orderOf_eq_one (a * b * c)
  rw [h.decomp_pow ha hb hc] at hm
  obtain ⟨-, -, hcm⟩ := h.decomp_eq_one (pow_mem ha _) (pow_mem hb _) (pow_mem hc _) hm
  have hcR : c ∈ R := hR.odd c hc (hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hcm))
  have h840 : (a * b * c) ^ 840 = 1 := by
    rw [h.decomp_pow ha hb hc]
    have ha' : a ^ 840 = 1 := by
      rw [show 840 = 168 * 5 by norm_num, pow_mul, orderOf_dvd_iff_pow_eq_one.1 (c₁.orderOf_dvd ha),
        one_pow]
    have hb' : b ^ 840 = 1 := by
      rw [show 840 = 168 * 5 by norm_num, pow_mul, orderOf_dvd_iff_pow_eq_one.1 (c₂.orderOf_dvd hb),
        one_pow]
    have hc' : c ^ 840 = 1 := by
      rw [show 840 = 5 * 168 by norm_num, pow_mul, hR.pow5 c hcR, one_pow]
    rw [ha', hb', hc', one_mul, one_mul]
  have hd := orderOf_dvd_of_pow_eq_one h840
  have hcop : (orderOf (a * b * c)).Coprime 8 :=
    Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hodd)
  exact hcop.dvd_of_dvd_mul_left (by simpa using hd)

theorem le_four_of_mem {c : ℕ} {Y B : Subgroup (MulAut W)} (hYB : Y ≤ B) (hBM : B ≤ Mb)
    (hY : IsCyclic Y) (hcard : Nat.card Y = 2 ^ c - 1) (hodd : Odd (Nat.card B)) : c ≤ 4 := by
  have := h.finite_aut
  obtain ⟨g, hg⟩ := hY.exists_generator
  have hord : orderOf (g : MulAut W) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hoddY : Odd (Nat.card Y) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hYB)
  rw [hcard, ← hord] at hoddY
  have h105 := h.orderOf_dvd_105 hR (hBM (hYB g.2)) hoddY
  rw [hord] at h105
  exact le_four_of_dvd_105 h105

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
