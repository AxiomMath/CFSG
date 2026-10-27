module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18

public section

namespace CFSG.Quasithin.H13.U43

theorem u43_card_sylow_two {J : Type} [Group J] [Finite J] {m : ℕ} (hm : Odd m)
    (h : Nat.card J = 4 * m) (P : Sylow 2 J) : Nat.card P = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have h1 : Nat.card P * (P : Subgroup J).index = Nat.card J := Subgroup.card_mul_index _
  have h2 : ¬ 2 ∣ (P : Subgroup J).index := P.not_dvd_index
  rw [h, hn] at h1
  obtain ⟨k, hk⟩ := hm
  have hlt : n < 3 := by
    by_contra hge
    push Not at hge
    have : 2 ^ 3 ∣ 4 * m := by
      rw [← h1]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 hge) _
    omega
  interval_cases n
  · exfalso; apply h2; omega
  · exfalso; apply h2; omega
  · rw [hn]; norm_num

theorem u43_pow24_centralizes {K : Type} [Group K] {Q : Subgroup K} (hQ : Nat.card Q = 4)
    {y : K} (hy : y ∈ Subgroup.normalizer (Q : Set K)) :
    y ^ 24 ∈ Subgroup.centralizer (Q : Set K) := by
  set φ := Q.normalizerMonoidHom with hφ
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have h1 : (φ ⟨y, hy⟩) ^ 24 = 1 := by
    have hp : (MulAut.toPerm Q (φ ⟨y, hy⟩)) ^ 24 = 1 := by
      have := pow_card_eq_one' (G := Equiv.Perm Q) (x := MulAut.toPerm Q (φ ⟨y, hy⟩))
      rwa [Nat.card_perm, hQ, show Nat.factorial 4 = 24 by decide] at this
    have : MulAut.toPerm Q ((φ ⟨y, hy⟩) ^ 24) = MulAut.toPerm Q 1 := by
      rw [map_pow, hp, map_one]
    exact MulEquiv.toEquiv_injective this
  have h2 : φ ((⟨y, hy⟩ : ↥(Subgroup.normalizer (Q : Set K))) ^ 24) = 1 := by
    rw [map_pow, h1]
  have h3 : ((⟨y, hy⟩ : ↥(Subgroup.normalizer (Q : Set K))) ^ 24) ∈ φ.ker := h2
  rw [hφ, Subgroup.normalizerMonoidHom_ker] at h3
  exact h3

theorem u43_exists_order_three {J : Type} [Group J] [Finite J]
    (hNC : ¬ CFSG.HasNormalPComplement 2 J) {Q : Subgroup J} (hQ : Nat.card Q = 4)
    (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) {m : ℕ} (hm : Odd m) (hJ : Nat.card J = 4 * m)
    (hC : ∀ x : J, (∀ q ∈ Q, x * q = q * x) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    ∃ y ∈ Subgroup.normalizer (Q : Set J), orderOf y = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 2) (by rw [hQ]; norm_num)
  obtain ⟨P, hQP⟩ := hQ2.exists_le_sylow
  have hP4 : Nat.card P = 4 := u43_card_sylow_two hm hJ P
  have hPQ : (P : Subgroup J) = Q :=
    (Subgroup.eq_of_le_of_card_ge hQP (by rw [hP4, hQ])).symm
  have hPQset : (P : Set J) = (Q : Set J) := by rw [← hPQ]; rfl
  by_contra hno
  push Not at hno
  have hcen : ∀ g ∈ Subgroup.normalizer (Q : Set J), ∀ q ∈ Q, g * q = q * g := by
    intro g hg
    have hord : ∀ p : ℕ, p.Prime → p ∣ orderOf g → p = 2 := by
      intro p hp hpd
      by_contra hp2
      have hy : g ^ (orderOf g / p) ∈ Subgroup.normalizer (Q : Set J) :=
        Subgroup.pow_mem _ hg _
      have hyord : orderOf (g ^ (orderOf g / p)) = p :=
        orderOf_pow_orderOf_div (orderOf_pos g).ne' hpd
      have h24 := u43_pow24_centralizes hQ hy
      obtain ⟨k, hk⟩ := hC ((g ^ (orderOf g / p)) ^ 24)
        (fun q hq => (Subgroup.mem_centralizer_iff.mp h24 q hq).symm)
      have hp24 : p ∣ 24 * 2 ^ k := by
        rw [← hyord]
        apply orderOf_dvd_of_pow_eq_one
        rw [pow_mul]
        exact hk
      have hp3 : p = 3 := by
        rcases (Nat.Prime.dvd_mul hp).mp hp24 with h | h
        · have h' : p ∣ 2 ^ 3 * 3 := by norm_num; exact h
          rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
              (hp.dvd_of_dvd_pow h'')) hp2
          · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h''
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (hp.dvd_of_dvd_pow h)) hp2
      exact hno _ hy (by rw [hyord, hp3])
    have hpow : orderOf g = 2 ^ (orderOf g).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos g).ne' (fun hp hd => hord _ hp hd)
    have hT : IsPGroup 2 (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := (orderOf g).primeFactorsList.length)
        (by rw [Nat.card_zpowers]; exact hpow)
    have h1 := hT.inf_normalizer_sylow P
    have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (P : Set J) := by
      rw [Subgroup.zpowers_le, hPQset]
      exact hg
    rw [inf_eq_left.mpr hle] at h1
    have hgP : g ∈ (P : Subgroup J) := (inf_le_right : Subgroup.zpowers g ⊓ (P : Subgroup J) ≤ _)
      (h1 ▸ Subgroup.mem_zpowers g)
    rw [hPQ] at hgP
    intro q hq
    exact hab _ hgP _ hq
  have hS : (P : Subgroup J) ≤ CFSG.centerIn (G := J) (Subgroup.normalizer (P : Subgroup J)) := by
    intro s hs
    refine ⟨Subgroup.le_normalizer hs, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    have hs' : s ∈ Q := by rw [← hPQ]; exact hs
    have hh' : h ∈ Subgroup.normalizer (Q : Set J) := by rw [← hPQset]; exact hh
    exact hcen h hh' s hs'
  exact hNC (CFSG.hasNormalPComplement_of_sylow_le_center_normalizer 2 P hS)

end CFSG.Quasithin.H13.U43
