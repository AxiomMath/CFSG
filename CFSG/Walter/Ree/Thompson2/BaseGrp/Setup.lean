module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.NComp

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward
open scoped Pointwise

section Ree

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem
    (h : ReeTypeHyp G) (Q : Sylow 3 G) {y g : G}
    (hy : y ∈ (Q : Subgroup G)) (hy1 : y ≠ 1) (hyg : g⁻¹ * y * g ∈ (Q : Subgroup G)) :
    g ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
  have hmem : y ∈ (Q : Subgroup G) ⊓ (MulAut.conj g • (Q : Subgroup G)) :=
    Subgroup.mem_inf.mpr ⟨hy, WardLocal.mem_conj_smul_iff.mpr hyg⟩
  have heq : (Q : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
    rcases (WardLocal.ward_two_three h Q).2.1 g with h0 | h0
    · rw [h0] at hmem
      exact absurd ((Subgroup.mem_bot).mp hmem) hy1
    · exact Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h0) (by rw [WardLocal.card_conj_smul])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ z, z ∈ (Q : Subgroup G) ↔ g⁻¹ * z * g ∈ (Q : Subgroup G) := by
    intro z
    conv_lhs => rw [heq]
    rw [WardLocal.mem_conj_smul_iff]
  rw [key (g * x * g⁻¹)]
  simp [mul_assoc]

theorem mem_normalizer_of_commute
    (h : ReeTypeHyp G) (Q : Sylow 3 G) {y g : G}
    (hy : y ∈ (Q : Subgroup G)) (hy1 : y ≠ 1) (hc : g * y = y * g) :
    g ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem h Q hy hy1 (by
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]; exact hy)

theorem seven_not_dvd_q {n : ℕ} : ¬ 7 ∣ 3 ^ (2 * n + 1) ∧ ¬ 7 ∣ 3 ^ (2 * n + 1) - 1 := by
  have h : 3 ^ (2 * n + 1) % 7 = 3 ∨ 3 ^ (2 * n + 1) % 7 = 6 ∨ 3 ^ (2 * n + 1) % 7 = 5 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, pow_add, Nat.mul_mod]
      rcases ih with h | h | h <;> rw [h] <;> norm_num
  have hpos : 0 < 3 ^ (2 * n + 1) := by positivity
  omega

theorem seven_not_dvd
    (h : ReeTypeHyp G) (Q : Sylow 3 G) :
    ¬ 7 ∣ Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
  rw [(ward_thompsonIHyp h Q).card]
  obtain ⟨⟨n, -, hq⟩, -⟩ := ward_order h
  rw [hq]
  intro h7
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h7 | h7
  · exact (seven_not_dvd_q (n := n)).1 ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h7))
  · exact (seven_not_dvd_q (n := n)).2 h7

theorem not_commute_three_seven
    (h : ReeTypeHyp G) {y c : G} (hy : orderOf y = 3)
    (hc : orderOf c = 7) : c * y ≠ y * c := by
  intro hcy
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hy1 : y ≠ 1 := by rintro rfl; simp at hy
  have hcN := mem_normalizer_of_commute h Q (hQ (Subgroup.mem_zpowers y)) hy1 hcy
  apply seven_not_dvd h Q
  rw [← hc, ← Subgroup.orderOf_mk c hcN]
  exact orderOf_dvd_natCard _

end Ree

structure Ctx (G : Type) [Group G] [Finite G] (k : Type) [Field k] [CharP k 3]
    (σ : k ≃+* k) where
  h : ReeTypeHyp G
  P : Sylow 3 G
  e : Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ)

@[expose] def N : Subgroup G := Subgroup.normalizer ((C.P : Subgroup G) : Set G)

@[expose] def ι : ThompsonN k σ →* G := incl C.e

@[expose] def J : G := C.ι (ThompsonN.J σ)

@[expose] def T : G := C.ι (tT σ)

@[expose] def tor (t : kˣ) : G := C.ι (ThompsonN.torus σ t)

theorem ι_injective : Function.Injective C.ι := incl_injective C.e

theorem ι_mem (n : ThompsonN k σ) : C.ι n ∈ C.N := incl_mem C.e n

theorem exists_ι {g : G} (hg : g ∈ C.N) : ∃ n, g = C.ι n :=
  ⟨C.e ⟨g, hg⟩, by simp [ι, incl]⟩

theorem ι_eq_one {n : ThompsonN k σ} : C.ι n = 1 ↔ n = 1 :=
  ⟨fun h1 => C.ι_injective (h1.trans (map_one _).symm), fun h1 => by rw [h1, map_one]⟩

theorem J_ne_one : C.J ≠ 1 := fun h1 => thompsonJ_ne_one σ (C.ι_eq_one.mp h1)

theorem J_mul_J : C.J * C.J = 1 := by
  rw [J, ← map_mul, ← sq, thompsonJ_sq, map_one]

theorem J_inv : C.J⁻¹ = C.J := inv_eq_of_mul_eq_one_right C.J_mul_J

theorem orderOf_J : orderOf C.J = 2 :=
  orderOf_eq_prime (by rw [sq, C.J_mul_J]) C.J_ne_one

theorem T_pow_three : C.T ^ 3 = 1 := by rw [T, ← map_pow, tT_pow_three, map_one]

theorem T_ne_one : C.T ≠ 1 := by
  intro h1
  have := pp_eq_iff.mp (C.ι_eq_one.mp h1)
  simp at this

theorem orderOf_T : orderOf C.T = 3 :=
  orderOf_eq_prime C.T_pow_three C.T_ne_one

theorem J_mul_T : C.J * C.T = C.T * C.J := by
  have h := congrArg C.ι (thompsonJ_conj_tT σ)
  rw [map_mul, map_mul, map_inv] at h
  change C.J⁻¹ * C.T * C.J = C.T at h
  rw [C.J_inv] at h
  calc C.J * C.T = C.J * C.T * C.J * C.J := by rw [mul_assoc _ C.J, C.J_mul_J, mul_one]
    _ = C.T * C.J := by rw [h]

theorem J_eq_tor : C.J = C.tor (-1) := rfl

theorem tor_mul (s t : kˣ) : C.tor s * C.tor t = C.tor (s * t) := by
  rw [tor, tor, tor, ← map_mul, ← map_mul]

theorem tor_comm (s t : kˣ) : C.tor s * C.tor t = C.tor t * C.tor s := by
  rw [C.tor_mul, C.tor_mul, mul_comm]

theorem tor_inv (t : kˣ) : (C.tor t)⁻¹ = C.tor t⁻¹ := by
  rw [tor, tor, map_inv, map_inv]

theorem card_N :
    Nat.card C.N = C.h.q ^ 3 * (C.h.q - 1) :=
  (ward_thompsonIHyp C.h C.P).card

theorem q_eq :
    ∃ n ≥ 1, C.h.q = 3 ^ (2 * n + 1) := (ward_order C.h).1

theorem mem_N_of_commute
    {y g : G} (hy : y ∈ (C.P : Subgroup G)) (hy1 : y ≠ 1)
    (hc : g * y = y * g) : g ∈ C.N :=
  mem_normalizer_of_commute C.h C.P hy hy1 hc

variable [Finite k]

theorem card_k : Nat.card k = C.h.q := by
  have h1 : Nat.card k ^ 3 * (Nat.card k - 1) = C.h.q ^ 3 * (C.h.q - 1) := by
    rw [← ThompsonN.card σ, ← C.card_N]
    exact (Nat.card_congr C.e.toEquiv).symm
  have hk : 2 ≤ Nat.card k := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial k)
    omega
  have hq : 3 ≤ C.h.q := C.h.three_le_q
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have a1 : Nat.card k ^ 3 < C.h.q ^ 3 := Nat.pow_lt_pow_left hlt (by norm_num)
    have a2 : Nat.card k - 1 < C.h.q - 1 := by omega
    have : Nat.card k ^ 3 * (Nat.card k - 1) < C.h.q ^ 3 * (C.h.q - 1) :=
      Nat.mul_lt_mul'' a1 a2
    omega
  · have a1 : C.h.q ^ 3 < Nat.card k ^ 3 := Nat.pow_lt_pow_left hlt (by norm_num)
    have a2 : C.h.q - 1 < Nat.card k - 1 := by omega
    have : C.h.q ^ 3 * (C.h.q - 1) < Nat.card k ^ 3 * (Nat.card k - 1) :=
      Nat.mul_lt_mul'' a1 a2
    omega

include C in
theorem coprime_q :
    Nat.Coprime (Nat.card k ^ 3) (Nat.card k - 1) := by
  rw [C.card_k]
  refine Nat.Coprime.pow_left 3 ?_
  have h1 : 1 ≤ C.h.q := by have := C.h.three_le_q; omega
  rw [Nat.coprime_comm, Nat.coprime_self_sub_left h1]
  exact Nat.coprime_one_left _

theorem mem_P_iff
    (x : G) : x ∈ (C.P : Subgroup G) ↔ ∃ p ∈ ThompsonN.P σ, x = C.ι p := by
  set Q : Subgroup G := (ThompsonN.P σ).map C.ι with hQ
  have hle : (C.P : Subgroup G) ≤ Q := by
    intro x hx
    obtain ⟨n, rfl⟩ := C.exists_ι (Subgroup.le_normalizer hx)
    refine ⟨n, ?_, rfl⟩
    apply RType.mem_P_of_orderOf_dvd C.coprime_q
    have h1 : orderOf (C.ι n) ∣ Nat.card (C.P : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hx
    rw [orderOf_injective C.ι C.ι_injective n] at h1
    have hP : Nat.card (C.P : Subgroup G) = C.h.q ^ 3 := (WardLocal.ward_two_three C.h C.P).1
    rwa [hP, ← C.card_k] at h1
  have hcard : Nat.card Q ≤ Nat.card (C.P : Subgroup G) := by
    rw [hQ, Subgroup.card_map_of_injective C.ι_injective, ThompsonN.card_P,
      (WardLocal.ward_two_three C.h C.P).1, C.card_k]
  have heq : (C.P : Subgroup G) = Q := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq, hQ, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

theorem ι_mem_P
    {p : ThompsonN k σ} (hp : p ∈ ThompsonN.P σ) : C.ι p ∈ (C.P : Subgroup G) :=
  (C.mem_P_iff _).mpr ⟨p, hp, rfl⟩

theorem ι_pp_mem_P
    (α β γ : k) : C.ι (pp σ α β γ) ∈ (C.P : Subgroup G) :=
  C.ι_mem_P (pp_mem_P α β γ)

theorem T_mem_P :
    C.T ∈ (C.P : Subgroup G) := C.ι_pp_mem_P 0 1 0

theorem mem_P_of_pow
    {x : G} (hx : x ∈ C.N) {j : ℕ} (hj : j ≤ 3) (h3 : x ^ 3 ^ j = 1) :
    x ∈ (C.P : Subgroup G) := by
  obtain ⟨n, rfl⟩ := C.exists_ι hx
  apply C.ι_mem_P
  apply RType.mem_P_of_orderOf_dvd C.coprime_q
  have h1 : orderOf n ∣ 3 ^ j :=
    orderOf_dvd_of_pow_eq_one (C.ι_injective (by rw [map_pow, h3, map_one]))
  refine h1.trans ?_
  rw [C.card_k]
  obtain ⟨m, -, hq⟩ := C.q_eq
  rw [hq, ← pow_mul]
  exact Nat.pow_dvd_pow 3 (by omega)

section Fintype

variable [Fintype k]

omit [Finite k] in
include C in
theorem card_k_eq :
    ∃ n ≥ 1, Fintype.card k = 3 ^ (2 * n + 1) := by
  obtain ⟨n, hn, hq⟩ := Ctx.q_eq C
  exact ⟨n, hn, by rw [Fintype.card_eq_nat_card, C.card_k, hq]⟩

end Fintype

end Ctx

end CFSG.Walter.Ree.T2.BaseGrp
