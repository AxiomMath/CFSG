module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Act

public section

namespace CFSG.Quasithin.A312U3

open CFSG.Assembly.LowTwoRank

section Pair

variable {G : Type*} [Group G] {c d : G}

theorem QuatPair.sq_mul_pow (h : QuatPair c d) (k : ℕ) : (d * c ^ k) ^ 2 = c ^ 2 := by
  calc (d * c ^ k) ^ 2 = d * (c ^ k * d) * c ^ k := by simp only [pow_two, mul_assoc]
    _ = d * (d * c ^ (3 * k)) * c ^ k := by rw [h.c_pow_mul_d]
    _ = d ^ 2 * c ^ (4 * k) := by
      simp only [pow_two, mul_assoc, ← pow_add]
      rw [show 3 * k + k = 4 * k by ring]
    _ = c ^ 2 := by rw [h.2.2.1, pow_mul, h.1, one_pow, mul_one]

theorem QuatPair.eq_or_sq_eq (h : QuatPair c d) {g : G}
    (hg : g ∈ Subgroup.closure ({c, d} : Set G)) (hg1 : g ≠ 1) : g = c ^ 2 ∨ g ^ 2 = c ^ 2 := by
  obtain ⟨k, rfl | rfl⟩ := h.closure_elem hg
  · have hk : c ^ k = c ^ (k % 4) := by rw [pow_eq_pow_mod k h.1]
    rw [hk] at hg1 ⊢
    have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hm : k % 4
    · exact absurd (pow_zero c) hg1
    · right
      rw [pow_one]
    · left
      rfl
    · right
      rw [← pow_mul, show 3 * 2 = 4 + 2 from rfl, pow_add, h.1, one_mul]
  · right
    exact h.sq_mul_pow k

end Pair

theorem quatPair_not_perm (n : ℕ) (hn : n ≤ 7) (c d : Equiv.Perm (Fin n)) : ¬ QuatPair c d := by
  intro h
  classical
  set Q : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure ({c, d} : Set (Equiv.Perm (Fin n)))
    with hQ
  have hcQ : c ∈ Q := Subgroup.subset_closure (by simp)
  have hdQ : d ∈ Q := Subgroup.subset_closure (by simp)
  have hz : c ^ 2 ≠ 1 := h.2.1
  obtain ⟨x, hx⟩ : ∃ x : Fin n, (c ^ 2) x ≠ x := by
    by_contra hno
    push Not at hno
    exact hz (Equiv.ext hno)
  have hfix : ∀ g ∈ Q, g x = x → g = 1 := by
    intro g hg hgx
    by_contra hg1
    rcases h.eq_or_sq_eq hg hg1 with e | e
    · exact hx (by rw [← e]; exact hgx)
    · apply hx
      rw [← e, pow_two, Equiv.Perm.mul_apply, hgx, hgx]
  have hinj : Function.Injective (fun g : Q => (g : Equiv.Perm (Fin n)) x) := by
    intro g g' hgg
    have h1 : ((g'⁻¹ * g : Q) : Equiv.Perm (Fin n)) x = x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
      simp only at hgg
      rw [hgg]
      simp
    have := hfix _ (g'⁻¹ * g : Q).2 h1
    exact inv_mul_eq_one.mp (Subtype.ext this) |>.symm
  have hle : Nat.card Q ≤ n := by
    simpa using Nat.card_le_card_of_injective _ hinj
  have hord : orderOf c = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := c) (by simpa using hz)
      (by simpa using h.1)
    simpa using this
  have hdnot : d ∉ Subgroup.zpowers c := by
    intro hd
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have h1 : c ^ m * c * (c ^ m)⁻¹ = c := by group
    have h2 := h.2.2.2
    rw [h1] at h2
    apply hz
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h2
  have hzp : Subgroup.zpowers c ≤ Q := (Subgroup.zpowers_le).mpr hcQ
  have hdvd : Nat.card (Subgroup.zpowers c) ∣ Nat.card Q := Subgroup.card_dvd_of_le hzp
  rw [Nat.card_zpowers, hord] at hdvd
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have h4 : Nat.card Q = 4 := by omega
  have heq : Subgroup.zpowers c = Q :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [Nat.card_zpowers, hord, h4])
  exact hdnot (heq ▸ hdQ)

theorem su3_not_alt7 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) {M : Subgroup ↥(StatedSU 3 (p ^ 1) K)}
    {H : Subgroup (GL (Fin 3) K)} (h : QCtx p K M H)
    (e : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨c, d, hcd⟩ := exists_quaternion_pair hp2 hK M h.odd
  have hpair := quatPair_qAct hK h hcd
  have hpair2 := hpair.map (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  let ee : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective _ hbij
  have hpair3 := hpair2.map ee.symm.toMonoidHom ee.symm.injective
  exact quatPair_not_perm 7 le_rfl _ _ hpair3

end CFSG.Quasithin.A312U3
