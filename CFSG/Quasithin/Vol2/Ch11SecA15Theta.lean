module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem map_conj_closure (S : Set G) (y : G) :
    (Subgroup.closure S).map (MulAut.conj y).toMonoidHom =
      Subgroup.closure ((MulAut.conj y).toMonoidHom '' S) :=
  MonoidHom.map_closure _ _

theorem conj_le_of_oPrimeResidualOf_eq {M L : Subgroup G} {p : ℕ}
    (hp : oPrimeResidualOf p M = L) {y : G}
    (hy : L.map (MulAut.conj y).toMonoidHom ≤ M) : L.map (MulAut.conj y).toMonoidHom ≤ L := by
  have hS : ∀ x, x ∈ M → (∃ k : ℕ, orderOf x = p ^ k) → x ∈ L := fun x hx hk =>
    hp ▸ Subgroup.subset_closure ⟨hx, hk⟩
  have hL : L = Subgroup.closure {x : G | x ∈ M ∧ ∃ k : ℕ, orderOf x = p ^ k} := hp.symm
  intro z hz
  have hz' := hz
  rw [hL, map_conj_closure] at hz'
  refine (Subgroup.closure_le L).mpr ?_ hz'
  rintro _ ⟨x, ⟨hxM, k, hk⟩, rfl⟩
  have hxL : x ∈ L := hS x hxM ⟨k, hk⟩
  refine hS _ (hy ⟨x, hxL, rfl⟩) ⟨k, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]

theorem conj_le_of_order_three {M L : Subgroup G}
    (h3 : ∀ x ∈ M, orderOf x = 3 → x ∈ L)
    (hL : L = Subgroup.closure {x : G | x ∈ L ∧ orderOf x = 3}) {y : G}
    (hy : L.map (MulAut.conj y).toMonoidHom ≤ M) : L.map (MulAut.conj y).toMonoidHom ≤ L := by
  intro z hz
  have hz' := hz
  rw [hL, map_conj_closure] at hz'
  refine (Subgroup.closure_le L).mpr ?_ hz'
  rintro _ ⟨x, ⟨hxL, hx3⟩, rfl⟩
  refine h3 _ (hy ⟨x, hxL, rfl⟩) ?_
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hx3]

theorem three_dvd_two_pow_two_mul_sub_one (n : ℕ) : 3 ∣ 2 ^ (2 * n) - 1 := by
  have := Nat.sub_dvd_pow_sub_pow 4 1 n
  rw [one_pow] at this
  rw [pow_mul]
  simpa using this

theorem exists_prime_gt_three_dvd {n : ℕ} (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ 3 < p := by
  by_contra hcon
  push Not at hcon
  have hpos : 2 ^ n - 1 ≠ 0 := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hodd : ¬ 2 ∣ 2 ^ n - 1 := by
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have h3 := Nat.eq_prime_pow_of_unique_prime_dvd hpos (p := 3) (fun {d} hd hdd => by
    have := hcon d hd hdd
    interval_cases d
    · exact absurd hd (by norm_num)
    · exact absurd hd (by norm_num)
    · exact absurd hdd hodd
    · rfl)
  have h8 : (2 ^ n - 1) % 8 = 7 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [pow_add]
    have : 1 ≤ 2 ^ k * 2 ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have h38 : ∀ m : ℕ, 3 ^ m % 8 = 1 ∨ 3 ^ m % 8 = 3 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> simp
  rcases h38 (2 ^ n - 1).primeFactorsList.length with h | h <;> rw [← h3] at h <;> omega

end CFSG.Quasithin.Vol2.Ch11.SecA
