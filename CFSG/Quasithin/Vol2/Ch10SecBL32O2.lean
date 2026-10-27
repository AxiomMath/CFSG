module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Vol2.Ch10SecBL32K

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.L32

open CFSG.Quasithin

theorem isKa_of_odd {x : Γ} (hx : IsPa x) (ho : Odd (orderOf x)) : IsKa x := by
  by_contra hK
  have h4 : x ^ 4 = 1 := by
    have := ka_out x hx hK
    simpa [pow_succ, mul_assoc] using this
  have hd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have h1 : orderOf x = 1 := by
    have hc : Nat.Coprime (orderOf x) 4 :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ho)
    exact Nat.Coprime.eq_one_of_dvd hc hd
  rw [orderOf_eq_one_iff] at h1
  exact hK (h1 ▸ isKa_one)

theorem isKb_of_odd {x : Γ} (hx : IsPb x) (ho : Odd (orderOf x)) : IsKb x := by
  by_contra hK
  have h4 : x ^ 4 = 1 := by
    have := kb_out x hx hK
    simpa [pow_succ, mul_assoc] using this
  have hd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have h1 : orderOf x = 1 := by
    have hc : Nat.Coprime (orderOf x) 4 :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ho)
    exact Nat.Coprime.eq_one_of_dvd hc hd
  rw [orderOf_eq_one_iff] at h1
  exact hK (h1 ▸ isKb_one)

theorem odd_of_cube {G : Type*} [Group G] {x : G} (h : x * x * x = 1) : Odd (orderOf x) :=
  Odd.of_dvd_nat (by decide : Odd 3)
    (orderOf_dvd_of_pow_eq_one (by simpa [pow_succ, mul_assoc] using h))

theorem oTwoUpper_prod_of {P K : Subgroup Γ} (hKP : K ≤ P)
    (hodd : ∀ x ∈ P, Odd (orderOf x) → x ∈ K)
    (hgen : ∀ k ∈ K, ∃ a ∈ K, a * a * a = 1 ∧ a⁻¹ * k * (a⁻¹ * k) * (a⁻¹ * k) = 1) :
    oTwoUpper (P.prod P) = K.prod K := by
  apply le_antisymm
  · rw [oTwoUpper, Subgroup.closure_le]
    intro p hp
    obtain ⟨hpP, ho⟩ := hp
    obtain ⟨hx, hy⟩ := Subgroup.mem_prod.mp hpP
    exact Subgroup.mem_prod.mpr ⟨hodd p.1 hx (ho.of_dvd_nat orderOf_fst_dvd_orderOf),
      hodd p.2 hy (ho.of_dvd_nat orderOf_snd_dvd_orderOf)⟩
  · have h1 : ∀ k ∈ K, ((k, (1 : Γ)) : Γ × Γ) ∈ oTwoUpper (P.prod P) ∧
        (((1 : Γ), k) : Γ × Γ) ∈ oTwoUpper (P.prod P) := by
      intro k hk
      obtain ⟨a, ha, ha3, hb3⟩ := hgen k hk
      have haP := hKP ha
      have hbP := hKP (K.mul_mem (K.inv_mem ha) hk)
      have hk' : k = a * (a⁻¹ * k) := by group
      constructor
      · rw [show ((k, (1 : Γ)) : Γ × Γ) = (a, 1) * (a⁻¹ * k, 1) by rw [Prod.mk_mul_mk, ← hk',
          mul_one]]
        refine (oTwoUpper (P.prod P)).mul_mem (mem_oTwoUpper_of_odd ⟨haP, P.one_mem⟩ ?_)
          (mem_oTwoUpper_of_odd ⟨hbP, P.one_mem⟩ ?_)
        · exact odd_of_cube (by simp [ha3])
        · exact odd_of_cube (by simp [hb3])
      · rw [show (((1 : Γ), k) : Γ × Γ) = (1, a) * (1, a⁻¹ * k) by rw [Prod.mk_mul_mk, ← hk',
          mul_one]]
        refine (oTwoUpper (P.prod P)).mul_mem (mem_oTwoUpper_of_odd ⟨P.one_mem, haP⟩ ?_)
          (mem_oTwoUpper_of_odd ⟨P.one_mem, hbP⟩ ?_)
        · exact odd_of_cube (by simp [ha3])
        · exact odd_of_cube (by simp [hb3])
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have := (oTwoUpper (P.prod P)).mul_mem (h1 x hx).1 (h1 y hy).2
    simpa using this

theorem oTwoUpper_pa_prod : oTwoUpper (Pa.prod Pa) = Ka.prod Ka :=
  oTwoUpper_prod_of (fun _ h => h.1) (fun x hx ho => isKa_of_odd hx ho)
    (fun k hk => by
      obtain ⟨a, ha, h3, h3'⟩ := ka_gen k hk
      exact ⟨a, ha, h3, h3'⟩)

theorem oTwoUpper_pb_prod : oTwoUpper (Pb.prod Pb) = Kb.prod Kb :=
  oTwoUpper_prod_of (fun _ h => h.1) (fun x hx ho => isKb_of_odd hx ho)
    (fun k hk => by
      obtain ⟨a, ha, h3, h3'⟩ := kb_gen k hk
      exact ⟨a, ha, h3, h3'⟩)

theorem ka_six : ∀ k : Γ, IsKa k → k * k * k * (k * k * k) = 1 := by decide +kernel
theorem kb_six : ∀ k : Γ, IsKb k → k * k * k * (k * k * k) = 1 := by decide +kernel

theorem sq_eq_one_of {G : Type*} [Group G] {x : G} (h6 : x * x * x * (x * x * x) = 1) {n : ℕ}
    (hn : x ^ 2 ^ n = 1) : x * x = 1 := by
  have h6' : x ^ 6 = 1 := by simpa [pow_succ, mul_assoc] using h6
  have hd6 : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one h6'
  have hd2 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  have h2 : orderOf x ∣ 2 := by
    rw [hm] at hd6 ⊢
    rcases m with _ | _ | m
    · simp
    · simp
    · exfalso
      have : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ m + 2)).trans hd6
      omega
  have := orderOf_dvd_iff_pow_eq_one.mp h2
  simpa [pow_two] using this

theorem isEa_of_two_pow {k : Γ} (hk : IsKa k) {n : ℕ} (hn : k ^ 2 ^ n = 1) : IsEa k := by
  have h2 := sq_eq_one_of (ka_six k hk) hn
  exact ka_two k hk (by rw [mul_assoc k k, h2, mul_one, h2])

theorem isEb_of_two_pow {k : Γ} (hk : IsKb k) {n : ℕ} (hn : k ^ 2 ^ n = 1) : IsEb k := by
  have h2 := sq_eq_one_of (kb_six k hk) hn
  exact kb_two k hk (by rw [mul_assoc k k, h2, mul_one, h2])

end CFSG.Quasithin.Vol2.Ch10.SecB.L32
