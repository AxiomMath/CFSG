module

public import CFSG.Walter.J1.Classify

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

omit [Finite G] in
theorem prime_of_three_or_five {p : ℕ} (hp : p = 3 ∨ p = 5) : p.Prime := by
  rcases hp with rfl | rfl <;> norm_num

omit [Finite G] in
theorem odd_of_three_or_five {p : ℕ} (hp : p = 3 ∨ p = 5) : Odd p := by
  rcases hp with rfl | rfl <;> decide

omit [Finite G] in
theorem exists_gen {U : Subgroup G} {p : ℕ} (hp : p = 3 ∨ p = 5) (hUp : Nat.card U = p) :
    ∃ u ∈ U, u ≠ 1 ∧ U = Subgroup.zpowers u ∧ u ^ p = 1 := by
  have hpp := prime_of_three_or_five hp
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card hUp hpp.one_lt
  exact ⟨u, hu, hu1, eq_zpowers_of_card_prime hpp hUp hu hu1, by
    rw [← hUp]; exact pow_card_eq_one_of_mem hu⟩

theorem mem_of_commute_F {U : Subgroup G} (hUF : U ≤ h.F) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hUp : Nat.card U = p) {f : G} (hf : f ∈ h.F)
    (hfU : f ∈ Subgroup.centralizer (U : Set G)) : f ∈ U := by
  obtain ⟨u, hu, hu1, hUu, hup⟩ := exists_gen hp hUp
  have hc : u * f = f * u := Subgroup.mem_centralizer_iff.mp hfU u hu
  rw [hUu]
  rcases hp with rfl | rfl
  · exact A5Sub.mem_zpowers_of_commute_three h.iso (hUF hu) hf hup hu1 hc
  · exact A5Sub.mem_zpowers_of_commute_five h.iso (hUF hu) hf hup hu1 hc

theorem mem_centralizer_of_mem_centralizer_t {U : Subgroup G} (hUF : U ≤ h.F) {p : ℕ}
    (hp : p = 3 ∨ p = 5) (hUp : Nat.card U = p) {x : G}
    (hxU : x ∈ Subgroup.centralizer (U : Set G))
    (hxt : x ∈ Subgroup.centralizer ({h.t} : Set G)) : x ∈ U ∨ h.t * x ∈ U := by
  have htU : h.t ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact h.commute_of_mem_F (hUF hu)
  rcases h.mem_centralizer_t.mp hxt with hxF | hxF
  · exact Or.inl (h.mem_of_commute_F hUF hp hUp hxF hxU)
  · exact Or.inr (h.mem_of_commute_F hUF hp hUp hxF (Subgroup.mul_mem _ htU hxU))

theorem t_mem_centralizer_of_le_F {U : Subgroup G} (hUF : U ≤ h.F) :
    h.t ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact h.commute_of_mem_F (hUF hu)

omit [Finite G] in
theorem eq_one_of_two_of_odd {X : Subgroup G} (hX : Odd (Nat.card X)) {x : G} (hx : x ∈ X)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hx
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (Nat.card X) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hX)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop)
    h2)

theorem eq_zpowers_t {U : Subgroup G} (hUF : U ≤ h.F) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hUp : Nat.card U = p) {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRU : R ≤ Subgroup.centralizer (U : Set G)) (htR : Subgroup.zpowers h.t ≤ R) :
    R = Subgroup.zpowers h.t := by
  have hUodd : Odd (Nat.card U) := hUp ▸ odd_of_three_or_five hp
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have hSab := h.abelian_sylow S
  have htS : h.t ∈ S := hRS (htR (Subgroup.mem_zpowers _))
  refine le_antisymm (fun x hx => ?_) htR
  have hxt : x ∈ Subgroup.centralizer ({h.t} : Set G) := h.sylow_le_centralizer S htS (hRS hx)
  rw [mem_zpowers_of_orderOf_eq_two h.orderOf_t]
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rcases h.mem_centralizer_of_mem_centralizer_t hUF hp hUp (hRU hx) hxt with hxU | hxU
  · exact Or.inl (eq_one_of_two_of_odd hUodd hxU hk')
  · right
    obtain ⟨j, hj⟩ := hR ⟨h.t * x, R.mul_mem (htR (Subgroup.mem_zpowers _)) hx⟩
    have hj' : (h.t * x) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have := eq_one_of_two_of_odd hUodd hxU hj'
    have hx' : x = h.t⁻¹ := eq_inv_of_mul_eq_one_right this
    rw [hx', h.t_inv]

theorem exists_oddPart {U : Subgroup G} (hUF : U ≤ h.F) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hUp : Nat.card U = p) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer (U : Set G) ∧
      (A.subgroupOf (Subgroup.centralizer (U : Set G))).Normal ∧ ¬ 2 ∣ Nat.card A ∧
      Nat.card A * 2 = Nat.card (Subgroup.centralizer (U : Set G)) ∧
      ∀ x ∈ Subgroup.centralizer (U : Set G), Odd (orderOf x) → x ∈ A := by
  have htU := h.t_mem_centralizer_of_le_F hUF
  have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_t, pow_one])
  obtain ⟨A, hAK, hAN, hA2, hAcard, hAodd⟩ := exists_odd_complement
    (K := Subgroup.centralizer (U : Set G)) (T := Subgroup.zpowers h.t)
    ((Subgroup.zpowers_le).mpr htU) ht2
    (fun R hRK hR2 htR => h.eq_zpowers_t hUF hp hUp hR2 hRK htR)
    (by
      intro n _ hnT x hx
      have hnt : n * h.t * n⁻¹ = h.t := by
        rcases (mem_zpowers_of_orderOf_eq_two h.orderOf_t).mp
          ((Subgroup.mem_normalizer_iff.mp hnT h.t).mp (Subgroup.mem_zpowers _)) with h1 | h1
        · exfalso
          apply h.t_ne_one
          have := congrArg (fun w => n⁻¹ * w * n) h1
          simpa [mul_assoc] using this
        · exact h1
      have hnt' : n * h.t = h.t * n := by
        calc n * h.t = (n * h.t * n⁻¹) * n := by group
          _ = h.t * n := by rw [hnt]
      obtain ⟨k, rfl⟩ := hx
      exact (Commute.zpow_right hnt' k).eq)
  refine ⟨A, hAK, hAN, hA2, ?_, hAodd⟩
  rw [← hAcard, Nat.card_zpowers, h.orderOf_t]

theorem exists_inv_of_le_F {U : Subgroup G} (hUF : U ≤ h.F) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hUp : Nat.card U = p) :
    ∃ τ ∈ h.F, orderOf τ = 2 ∧ ∀ u ∈ U, τ * u * τ⁻¹ = u⁻¹ := by
  obtain ⟨u, hu, hu1, hUu, hup⟩ := exists_gen hp hUp
  obtain ⟨τ, hτF, hτ2, hτ1, hτu⟩ := A5Sub.exists_inv h.iso (hUF hu) hu1 (by
    rcases hp with rfl | rfl
    · rw [show (15 : ℕ) = 3 * 5 by norm_num, pow_mul, hup, one_pow]
    · rw [show (15 : ℕ) = 5 * 3 by norm_num, pow_mul, hup, one_pow])
  refine ⟨τ, hτF, orderOf_eq_prime hτ2 hτ1, fun v hv => ?_⟩
  rw [hUu] at hv
  obtain ⟨k, rfl⟩ := hv
  change τ * u ^ k * τ⁻¹ = (u ^ k)⁻¹
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hτu, inv_zpow]

theorem oddPart_classify {U : Subgroup G} (hUF : U ≤ h.F) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hUp : Nat.card U = p) :
    ∃ τ ∈ h.F, ∃ A : Subgroup G, IsFour h.t τ ∧ (∀ u ∈ U, τ * u * τ⁻¹ = u⁻¹) ∧
      IsMaxInv h.t τ A ∧ A ≤ Subgroup.centralizer (U : Set G) ∧ U ≤ A ∧
      A ⊓ Subgroup.centralizer ({h.t} : Set G) = U ∧
      Nat.card A * 2 = Nat.card (Subgroup.centralizer (U : Set G)) ∧
      (∀ x ∈ Subgroup.centralizer (U : Set G), Odd (orderOf x) → x ∈ A) ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      (Nat.card A = 3 ∨ Nat.card A = 5 ∨ Nat.card A = 15 ∨ Nat.card A = 27 ∨
        Nat.card A = 125) := by
  have hpp := prime_of_three_or_five hp
  have hUodd : Odd (Nat.card U) := hUp ▸ odd_of_three_or_five hp
  obtain ⟨τ, hτF, hτ, hτU⟩ := h.exists_inv_of_le_F hUF hp hUp
  obtain ⟨A, hAK, hAN, hA2, hAcard, hAodd⟩ := h.exists_oddPart hUF hp hUp
  have hAoddc : Odd (Nat.card A) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hA2)
  have hT : IsFour h.t τ := ⟨h.orderOf_t, hτ, fun h1 => h.t_not_mem (h1 ▸ hτF),
    (h.commute_of_mem_F hτF).symm⟩
  obtain ⟨u, hu, hu1, hUu, hup⟩ := exists_gen hp hUp
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    rw [hUu]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self u i j).eq
  have hUC : U ≤ Subgroup.centralizer (U : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hUab y hy x hx
  have hUA : U ≤ A := fun x hx => hAodd x (hUC hx)
    (Odd.of_dvd_nat hUodd (Subgroup.orderOf_dvd_natCard U hx))
  have htC := h.t_mem_centralizer_of_le_F hUF
  have hτN : τ ∈ Subgroup.normalizer ((Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G) := by
    refine mem_normalizer_of_conj_mem fun x hx => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hv' : τ⁻¹ * v * τ ∈ U := by
      have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right ((orderOf_eq_two_iff).mp hτ).1
      have e : τ⁻¹ * v * τ = τ * v * τ⁻¹ := by rw [hτinv]
      rw [e, hτU v hv]
      exact U.inv_mem hv
    have := Subgroup.mem_centralizer_iff.mp hx _ hv'
    calc v * (τ * x * τ⁻¹) = τ * ((τ⁻¹ * v * τ) * x) * τ⁻¹ := by group
      _ = τ * (x * (τ⁻¹ * v * τ)) * τ⁻¹ := by rw [this]
      _ = τ * x * τ⁻¹ * v := by group
  have hnormA : ∀ s ∈ Subgroup.normalizer ((Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G), s ∈ Subgroup.normalizer (A : Set G) := by
    intro s hs
    refine mem_normalizer_of_conj_mem fun x hx => hAodd _
      ((Subgroup.mem_normalizer_iff.mp hs x).mp (hAK hx)) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat hAoddc (Subgroup.orderOf_dvd_natCard A hx)
  have hAinv : IsInv h.t τ A := ⟨hAoddc, hnormA _ (Subgroup.le_normalizer htC), hnormA τ hτN⟩
  obtain ⟨M, hAM, hM⟩ := exists_isMaxInv hAinv
  obtain ⟨hMab, hMcard⟩ := h.abelian_and_card hT hM
  have hMC : M ≤ Subgroup.centralizer (U : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hMab y (hAM (hUA hy)) x hx
  have hMA : M ≤ A := fun x hx => hAodd x (hMC hx)
    (Odd.of_dvd_nat hM.1.1 (Subgroup.orderOf_dvd_natCard M hx))
  have hAeq : M = A := le_antisymm hMA hAM
  subst hAeq
  have hCt : M ⊓ Subgroup.centralizer ({h.t} : Set G) = U := by
    refine le_antisymm (fun x hx => ?_) (le_inf hUA fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_mem_F (hUF hx)))
    rcases h.mem_centralizer_of_mem_centralizer_t hUF hp hUp (hMC hx.1) hx.2 with hxU | hxU
    · exact hxU
    · exfalso
      have h1 : h.t = (h.t * x) * x⁻¹ := by group
      have hodd : Odd (orderOf h.t) := by
        have hc : Commute (h.t * x) x⁻¹ := by
          have hxt : x * h.t = h.t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
          show (h.t * x) * x⁻¹ = x⁻¹ * (h.t * x)
          calc (h.t * x) * x⁻¹ = h.t := by group
            _ = x⁻¹ * (x * h.t) := by group
            _ = x⁻¹ * (h.t * x) := by rw [hxt]
        have h2 : orderOf (h.t * x) ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hxU
        have h3 : orderOf x⁻¹ ∣ Nat.card M := by
          rw [orderOf_inv]; exact Subgroup.orderOf_dvd_natCard M hx.1
        have h4 := Commute.orderOf_mul_dvd_mul_orderOf hc
        rw [h1]
        exact Odd.of_dvd_nat (hUodd.mul hM.1.1) (h4.trans (Nat.mul_dvd_mul h2 h3))
      rw [h.orderOf_t] at hodd
      exact absurd hodd (by decide)
  refine ⟨τ, hτF, M, hT, hτU, hM, hMC, hUA, hCt, hAcard, hAodd, hMab, ?_⟩
  rcases hMcard with h1 | h1 | h1 | h1 | h1 | h1
  · exfalso
    have := Subgroup.card_le_of_le hUA
    rw [h1, hUp] at this
    exact absurd this (by rcases hp with rfl | rfl <;> norm_num)
  all_goals simp [h1]

end JankoHyp

end CFSG.Walter.J1
