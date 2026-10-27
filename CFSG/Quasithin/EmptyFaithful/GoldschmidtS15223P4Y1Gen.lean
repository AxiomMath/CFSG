module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.S15223P4.Y1

variable {G : Type} [Group G]

theorem mem_oPrimeResidualOf_three {N : Subgroup G} {x : G} (hx : x ∈ N) {k : ℕ}
    (hk : orderOf x = 3 ^ k) : x ∈ oPrimeResidualOf 3 N :=
  Subgroup.subset_closure ⟨hx, k, hk⟩

theorem oPrimeResidualOf_le_of_forall {N W : Subgroup G} {p : ℕ}
    (h : ∀ x ∈ N, ∀ k : ℕ, orderOf x = p ^ k → x ∈ W) : oPrimeResidualOf p N ≤ W :=
  (Subgroup.closure_le W).mpr fun _ hx => h _ hx.1 hx.2.choose hx.2.choose_spec

theorem oTwoUpper_oPrimeResidualOf_three (N : Subgroup G) :
    oTwoUpper (oPrimeResidualOf 3 N) = oPrimeResidualOf 3 N := by
  refine le_antisymm (oTwoUpper_le _) (oPrimeResidualOf_le_of_forall fun x hx k hk => ?_)
  exact mem_oTwoUpper_of_odd (mem_oPrimeResidualOf_three hx hk)
    (by rw [hk]; exact Odd.pow (by decide))

theorem mem_of_orderOf_pow_of_not_dvd_relIndex {N K : Subgroup G} (hKN : K ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (K : Set G)) {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ K.relIndex N) {x : G} (hx : x ∈ N) {k : ℕ} (hk : orderOf x = p ^ k) :
    x ∈ K := by
  have hnormal : (K.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hnorm
  set q : ↥N ⧸ K.subgroupOf N := QuotientGroup.mk ⟨x, hx⟩ with hq
  have hxk : x ^ p ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hqk : q ^ p ^ k = 1 := by
    rw [hq, ← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : ↥N) ^ p ^ k = 1 := Subtype.ext hxk
    rw [this]
    rfl
  have h1 : orderOf q ∣ p ^ k := orderOf_dvd_of_pow_eq_one hqk
  have h2 : orderOf q ∣ K.relIndex N := orderOf_dvd_natCard q
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
  have hj0 : j = 0 := by
    by_contra hne
    exact hidx (dvd_trans (hj ▸ dvd_pow_self p hne) h2)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hj)

theorem le_normalizer_of_forall_conj {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) :
    A ≤ Subgroup.normalizer (B : Set G) := fun a ha => by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h a ha b, fun hb => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hb
  simpa [mul_assoc] using this

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

end CFSG.Quasithin.S15223P4.Y1
