module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.RankThree.PartTwo.Sec17

namespace Proof17Res3

open CFSG CFSG.RankThree.PartTwo

variable {X : Type} [Group X] [Finite X]

theorem eq_bot_of_isPGroup_of_card_dvd {p : ℕ} (hp : p.Prime) {R : Subgroup X}
    (hR : IsPGroup p R) {n : ℕ} (hRn : Nat.card R ∣ n) (hpn : ¬ p ∣ n) : R = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq R (by rw [hk, pow_zero])
  · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans (hk ▸ hRn)) hpn

theorem j2_eq_bot_of_le_normalizer (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {E R : Subgroup X}
    (hE9 : Nat.card E = 9) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hR : IsPGroup p R)
    (hER : E ≤ Subgroup.normalizer (R : Set X)) : R = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hEP, hZE, -⟩ := KFacts.KS14.j2_exists_sylow_of_card_nine h415 hX hE9
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZdef
  obtain ⟨hZ3, -, hext⟩ := Sec14.j2_sylow_facts h415 hX P
  have hC1080 : Nat.card (Subgroup.centralizer (Z : Set X)) = 1080 :=
    KFacts.KS14.card_eq_of_isExtOf_alternating_six hext
  obtain ⟨⟨hHeis, -⟩, -, -, h4, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hp2 : ¬ p ∣ 2 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    omega
  have hp3' : ¬ p ∣ 3 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    omega
  have hcop3 : Nat.Coprime 3 (Nat.card R) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega))
  have hfix : ∀ a ∈ E, a ∉ Z → R ⊓ Subgroup.centralizer ({a} : Set X) = ⊥ := by
    intro a ha haZ
    obtain ⟨-, ⟨e⟩, -⟩ := h4 E ⟨hEP, hE9⟩ a ha haZ
    have h72 : Nat.card (Subgroup.normalizer (Subgroup.zpowers a : Set X)) = 72 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin, KFacts.KS14.card_alternatingGroup_four]
      norm_num
    have hCN : R ⊓ Subgroup.centralizer ({a} : Set X) ≤
        Subgroup.normalizer (Subgroup.zpowers a : Set X) := by
      refine inf_le_right.trans ?_
      rw [← KFacts.KS14.centralizer_zpowers_eq]
      exact Subgroup.centralizer_le_normalizer _
    refine eq_bot_of_isPGroup_of_card_dvd hp (hR.to_le inf_le_left)
      (h72 ▸ Subgroup.card_dvd_of_le hCN) ?_
    intro h
    have h' : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h3
    · exact hp2 (hp.dvd_of_dvd_pow h2)
    · exact hp3' (hp.dvd_of_dvd_pow h3)
  have hEel : CFSG.Open.IsElemAbelian 3 E := by
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE9]; norm_num),
      fun x hx => ?_⟩
    have hexp := hHeis.2.2
    have h1 : (⟨x, hEP hx⟩ : (P : Subgroup X)) ^ Monoid.exponent (P : Subgroup X) = 1 :=
      Monoid.pow_exponent_eq_one _
    rw [hexp] at h1
    simpa using congrArg Subtype.val h1
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E R hEel (by rw [hE9]; norm_num) hER hcop3
  have hRZ : R ≤ Subgroup.centralizer (Z : Set X) := by
    rw [← hgen]
    refine iSup₂_le fun D hD => ?_
    obtain ⟨hDE, hD3⟩ := hD
    by_cases hDZ : D = Z
    · rw [hDZ]
      exact inf_le_right
    · obtain ⟨a, haD, haZ⟩ : ∃ a ∈ D, a ∉ Z := by
        by_contra hcon
        push Not at hcon
        exact hDZ (Subgroup.eq_of_le_of_card_ge hcon (by rw [hZ3, hD3, pow_one]))
      have hle : R ⊓ Subgroup.centralizer (D : Set X) ≤
          R ⊓ Subgroup.centralizer ({a} : Set X) :=
        inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD))
      rw [hfix a (hDE haD) haZ] at hle
      exact hle.trans bot_le
  have hR1080 : Nat.card R ∣ 1080 := hC1080 ▸ Subgroup.card_dvd_of_le hRZ
  by_cases hp5 : p = 5
  · subst hp5
    rcases k with _ | _ | k
    · exact Subgroup.eq_bot_of_card_eq R (by rw [hk, pow_zero])
    ·
      obtain ⟨a, haE, haZ⟩ : ∃ a ∈ E, a ∉ Z := by
        by_contra hcon
        push Not at hcon
        have := Subgroup.card_le_of_le hcon
        rw [hE9, hZ3] at this
        omega
      have hR5 : Nat.card R = 5 := by rw [hk, zero_add, pow_one]
      have : IsCyclic R := isCyclic_of_prime_card hR5
      set σ := R.normalizerMonoidHom ⟨a, hER haE⟩ with hσ
      have ha3 : a ^ 3 = 1 := hEel.2 a haE
      have hσ3 : σ ^ 3 = 1 := by
        have e1 : (⟨a, hER haE⟩ : Subgroup.normalizer (R : Set X)) ^ 3 = 1 :=
          Subtype.ext (by simpa using ha3)
        rw [hσ, ← map_pow, e1, map_one]
      have hσ4 : orderOf σ ∣ 4 := by
        have h := orderOf_dvd_natCard σ
        rwa [IsCyclic.card_mulAut, hR5] at h
      have hσ1 : σ = 1 := by
        have h1 : orderOf σ ∣ Nat.gcd 3 4 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσ3) hσ4
        rw [show Nat.gcd 3 4 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h1
        exact h1
      have hRC : R ≤ R ⊓ Subgroup.centralizer ({a} : Set X) := by
        intro r hr
        refine ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h1 := congrArg (fun τ : MulAut R => ((τ ⟨r, hr⟩ : R) : X)) hσ1
        simp only [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h1
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      rw [hfix a haE haZ] at hRC
      exact le_bot_iff.mp hRC
    · exfalso
      have h25 : 5 ^ 2 ∣ 1080 := (pow_dvd_pow 5 (by omega)).trans (hk ▸ hR1080)
      norm_num at h25
  · refine eq_bot_of_isPGroup_of_card_dvd hp hR hR1080 ?_
    intro h
    have h' : p ∣ (2 ^ 3 * 3 ^ 3) * 5 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hp).mp h' with h23 | h5
    · rcases (Nat.Prime.dvd_mul hp).mp h23 with h2 | h3
      · exact hp2 (hp.dvd_of_dvd_pow h2)
      · exact hp3' (hp.dvd_of_dvd_pow h3)
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)

end Proof17Res3

end CFSG.RankThree.PartTwo.Sec17
