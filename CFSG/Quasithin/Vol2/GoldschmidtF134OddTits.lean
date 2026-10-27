module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddTitsData
public import CFSG.Quasithin.Vol2.F134TitsE9
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.Quasithin.F134 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open

theorem tits_not_mem_of_bad5 {H : Subgroup (GL (Fin 26) (ZMod 2))} (hTH : titsSyl ≤ H)
    (hp : ∀ p, (p = 3 ∨ p = 13) → ¬ p ∣ Nat.card H) {j : ℕ} (hj : j < 18) (hj0 : j ≠ 0)
    (hj2 : j ≠ 2) (hD : titsDP j ∈ H) : False := by
  obtain ⟨hp', hu, hpow, hne⟩ := tits_bad5_check j hj hj0 hj2
  set p := titsBad5 j % 32 with hpdef
  have hprime : p.Prime := by rcases hp' with h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  let x : H := ⟨(titsDP j * titsNFE (titsBad5 j / 1024)) ^ (titsBad5 j / 32 % 32),
    pow_mem (mul_mem hD (hTH (titsNFE_mem _))) _⟩
  have hcode : glCode26 (x : GL (Fin 26) (ZMod 2)) = titsPow (titsBad5 j / 32 % 32)
      (mulF26 (titsDC j) (titsNFC (titsBad5 j / 1024))) := by
    show glCode26 ((titsDP j * titsNFE (titsBad5 j / 1024)) ^ (titsBad5 j / 32 % 32)) = _
    rw [glCode26_pow, glCode26_mul, glCode26_titsDP hj, glCode26_titsNFE hu, glCode26_one]
    rfl
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_glCode26
    rw [Subgroup.coe_pow, glCode26_pow, hcode, Subgroup.coe_one, glCode26_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hcode, h, Subgroup.coe_one, glCode26_one]
  exact hp p hp' (orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x)

theorem titsDP_two : titsDP 2 = titsRhoN 0 := by
  rw [titsDP, show titsDW.getD 2 [] = [0] from rfl, titsWord, titsWord, mul_one]

theorem tits_card_le_five {H : Subgroup (GL (Fin 26) (ZMod 2))} (hTH : titsSyl ≤ H)
    (hH : H ≤ titsGroup) (hp : ∀ p, (p = 3 ∨ p = 13) → ¬ p ∣ Nat.card H) :
    Nat.card H ≤ 5 * Nat.card titsSyl := by
  have : Finite titsSyl := Subgroup.instFiniteSubtypeMem _
  refine card_le_of_cover ![1, titsRhoN 0, titsNFE (titsR 0 1) * titsRhoN 0,
    titsNFE (titsR 0 2) * titsRhoN 0, titsNFE (titsR 0 3) * titsRhoN 0] fun h hh => ?_
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := titsGroup_subset_cover (hH hh)
  have hD : titsDP j ∈ H := by
    have e : titsDP j = t⁻¹ * (t * titsDP j * t') * t'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hTH ht)) hh) (inv_mem (hTH ht'))
  by_cases hj0 : j = 0
  · subst hj0
    exact ⟨0, t * t', mul_mem ht ht', by rw [titsDP_zero]; simp⟩
  by_cases hj2 : j = 2
  · subst hj2
    obtain ⟨s, hs, v, hv, e⟩ := tits_coset_g (c := 0) (by norm_num) ht
    have hM : titsM 0 = 4 := by decide +kernel
    rw [hM] at hs
    have h0 : titsR 0 0 = 0 := (tits_gcl_check 0 (by norm_num)).2.1
    rw [titsDP_two]
    interval_cases s
    · refine ⟨1, v * t', mul_mem hv ht', ?_⟩
      rw [e, h0, titsNFE_zero]
      simp [mul_assoc]
    · exact ⟨2, v * t', mul_mem hv ht', by rw [e]; simp [mul_assoc]⟩
    · exact ⟨3, v * t', mul_mem hv ht', by rw [e]; simp [mul_assoc]⟩
    · exact ⟨4, v * t', mul_mem hv ht', by rw [e]; simp [mul_assoc]⟩
  · exact (tits_not_mem_of_bad5 hTH hp hj hj0 hj2 hD).elim

theorem exists_hom_le_map_of_sylow {X Y : Type*} [Group X] [Group Y] [Finite X] {S : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) {G T₀ : Subgroup Y} {φ₀ : X →* Y}
    (hφ₀ : Function.Injective φ₀) (hφ₀G : ∀ x, φ₀ x ∈ G) (hφ₀s : ∀ y ∈ G, ∃ x, φ₀ x = y)
    (hT₀G : T₀ ≤ G) (hT₀ : IsPGroup 2 T₀) :
    ∃ ψ : X →* Y, Function.Injective ψ ∧ (∀ x, ψ x ∈ G) ∧ T₀ ≤ S.map ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup X, R = T₀.comap φ₀ := ⟨_, rfl⟩
  have hRmap : R.map φ₀ = T₀ := by
    rw [hRdef]
    refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
    obtain ⟨x, rfl⟩ := hφ₀s y (hT₀G hy)
    exact ⟨x, hy, rfl⟩
  have hRp : IsPGroup 2 R :=
    hT₀.of_equiv ((R.equivMapOfInjective _ hφ₀).trans (MulEquiv.subgroupCongr hRmap)).symm
  obtain ⟨Q, hQ⟩ := hRp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hS2.toSylow hSi) Q
  have hQS : ∀ x ∈ (Q : Subgroup X), (MulAut.conj g)⁻¹ x ∈ S := by
    intro x hx
    have hx' : x ∈ ((g • hS2.toSylow hSi : Sylow 2 X) : Subgroup X) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    exact hx'
  have hback : ∀ x : X, (φ₀.comp (MulAut.conj g).toMonoidHom) ((MulAut.conj g)⁻¹ x) = φ₀ x := by
    intro x
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MulAut.mul_apply, mul_inv_cancel,
      MulAut.one_apply]
  refine ⟨φ₀.comp (MulAut.conj g).toMonoidHom, hφ₀.comp (MulAut.conj g).injective,
    fun x => hφ₀G _, ?_⟩
  intro y hy
  rw [← hRmap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨_, hQS x (hQ hx), hback x⟩

theorem not_dvd_five_sq_mul_two_pow {q k : ℕ} (hq : q = 3 ∨ q = 13) : ¬ q ∣ 5 ^ 2 * 2 ^ k := by
  have hprime : q.Prime := by rcases hq with h | h <;> rw [h] <;> norm_num
  intro h
  rcases (Nat.Prime.dvd_mul hprime).1 h with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_five).1 (hprime.dvd_of_dvd_pow h1)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).1 (hprime.dvd_of_dvd_pow h1)
    omega

theorem eq_five_of_pow_dvd_ordTits {p a : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (ha : a = 2 ∨ a = 3)
    (h : p ^ a ∣ ordTits) : p = 5 ∧ a = 2 := by
  have hord : ordTits = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := rfl
  have hpd : p ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 :=
    hord ▸ (dvd_pow_self p (by omega)).trans h
  have hp5 : p = 5 ∨ p = 13 := by
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
          omega
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)
  rcases hp5 with rfl | rfl
  · refine ⟨rfl, ?_⟩
    rcases ha with rfl | rfl
    · rfl
    · exact absurd h (by rw [hord]; norm_num)
  · exfalso
    have h169 : 13 ^ 2 ∣ ordTits := (Nat.pow_dvd_pow 13 (by omega)).trans h
    rw [hord] at h169
    revert h169
    norm_num

theorem noPowerOvergroup_tits :
    NoPowerOvergroup fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1 := by
  intro X _ _ hX p a hp hp5 ha H S hS2 hSi hSH hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₀, hφ₀, hφ₀mem, hφ₀surj⟩ := tits_embedding hX
  have hX' : Nat.card X = ordTits := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hX
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
  have hdvd : p ^ a ∣ ordTits := by
    have h1 : p ^ a ∣ Nat.card H := hH ▸ dvd_mul_right _ _
    have h2 : Nat.card H ∣ Nat.card X := Subgroup.card_subgroup_dvd_card H
    rw [hX'] at h2
    exact h1.trans h2
  obtain ⟨rfl, rfl⟩ := eq_five_of_pow_dvd_ordTits hp hp5 ha hdvd
  obtain ⟨ψ, hψ, hψG, hTψ⟩ := exists_hom_le_map_of_sylow hS2 hSi hφ₀ hφ₀mem hφ₀surj titsSyl_le
    titsSyl_isPGroup
  have hKc : Nat.card (H.map ψ) = 5 ^ 2 * 2 ^ k := by
    rw [Subgroup.card_map_of_injective hψ, hH, hk]
  have hTK : titsSyl ≤ H.map ψ := hTψ.trans (Subgroup.map_mono hSH)
  have hKM : H.map ψ ≤ titsGroup := by
    rintro _ ⟨x, -, rfl⟩
    exact hψG x
  have hle := tits_card_le_five hTK hKM fun q hq => by
    rw [hKc]
    exact not_dvd_five_sq_mul_two_pow hq
  have hTS : Nat.card titsSyl ≤ Nat.card S := by
    have h1 : Nat.card (S.map ψ) = Nat.card S := Subgroup.card_map_of_injective hψ
    have : Finite (S.map ψ) := Subgroup.instFiniteSubtypeMem _
    rw [← h1]
    exact Subgroup.card_le_of_le hTψ
  have hpos : 0 < 2 ^ k := by positivity
  rw [hKc] at hle
  rw [hk] at hTS
  omega

theorem lieTits :
    LieTits :=
  noOddConfigQ_of_noPowerOvergroup noPowerOvergroup_tits

end CFSG.Quasithin.H13.NQCore
