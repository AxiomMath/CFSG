module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofOrderLocal
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGenHJ
public import CFSG.RankThree.PartTwo.KFacts.ONanKS17J2CentralizerNine
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Res6Order

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem arith_cases {h k n : ℕ} (hh : 1728 ∣ h) (hh' : h ∣ 604800) (hk : 27 ∣ k)
    (hk' : k ∣ 2160) (hnk : n * k = h) (hn : n % 9 = 1) (hn' : n ≤ 280) :
    (h = 1728 ∧ k = 27) ∨ (h = 3456 ∧ k = 54) ∨ (h = 8640 ∧ k = 135) ∨
      (h = 17280 ∧ k = 270) ∨ (h = 12096 ∧ k = 432) ∨ (h = 43200 ∧ k = 432) ∨ h = 60480 ∨
      h = 120960 ∨ h = 302400 ∨ h = 604800 := by
  obtain ⟨m, rfl⟩ := hh
  obtain ⟨j, rfl⟩ := hk
  have hm : m ∈ Nat.divisors 350 := Nat.mem_divisors.mpr
    ⟨(Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 1728)).mp (by simpa using hh'), by norm_num⟩
  have hj : j ∈ Nat.divisors 80 := Nat.mem_divisors.mpr
    ⟨(Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 27)).mp (by simpa using hk'), by norm_num⟩
  rw [show Nat.divisors 350 = {1, 2, 5, 7, 10, 14, 25, 35, 50, 70, 175, 350} from by decide]
    at hm
  rw [show Nat.divisors 80 = {1, 2, 4, 5, 8, 10, 16, 20, 40, 80} from by decide] at hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm hj
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

omit [Finite X] in
theorem le_normalizer_center (P : Subgroup X) :
    P ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (P : Set X) : Subgroup X) : Set X) := by
  intro p hp
  refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
  constructor
  · intro hz
    have hzp : p * z = z * p := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 p hp
    have : p * z * p⁻¹ = z := by rw [hzp, mul_inv_cancel_right]
    rw [this]
    exact hz
  · intro hz
    have hw : p * (p * z * p⁻¹) = (p * z * p⁻¹) * p :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 p hp
    have : z = p * z * p⁻¹ := by
      calc z = p⁻¹ * ((p * z * p⁻¹) * p) := by group
        _ = p⁻¹ * (p * (p * z * p⁻¹)) := by rw [hw]
        _ = p * z * p⁻¹ := by group
    rw [this]
    exact hz

theorem relIndex_modEq_one (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {H : Subgroup X}
    (hPH : (P : Subgroup X) ≤ H) :
    (Subgroup.normalizer (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) :
      Subgroup X) : Set X)).relIndex H ≡ 1 [MOD 9] := by
  classical
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  set N := Subgroup.normalizer (Z : Set X) with hN
  set NH := N.subgroupOf H with hNH
  set PH := (P : Subgroup X).subgroupOf H with hPHdef
  have h27 := (card_sylow_center h415 hX P).1
  have hPN : (P : Subgroup X) ≤ N := le_normalizer_center (P : Subgroup X)
  have hPH27 : Nat.card PH = 27 := by
    rw [hPHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, h27]
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  refine card_modEq_one_of_orbit_dvd (G := PH) ((1 : H) : H ⧸ NH) (fun p => ?_) fun a ha => ?_
  ·
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
      mul_one]
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa using inv_mem (hPN (Subgroup.mem_subgroupOf.mp p.2)))
  · obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
    set T := MulAction.stabilizer PH ((h : H) : H ⧸ NH) with hT
    set T' := (T.map PH.subtype).map H.subtype with hT'
    have hT'P : T' ≤ P := by
      rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mp t.2
    have hT'card : Nat.card T' = Nat.card T := by
      rw [hT', Subgroup.card_map_of_injective H.subtype_injective,
        Subgroup.card_map_of_injective PH.subtype_injective]
    have horb : Nat.card (MulAction.orbit PH ((h : H) : H ⧸ NH)) * Nat.card T = 27 := by
      have h1 := MulAction.index_stabilizer PH ((h : H) : H ⧸ NH)
      rw [← Nat.card_coe_set_eq] at h1
      rw [← h1, ← hPH27, mul_comm, ← hT]
      exact T.card_mul_index
    have hT9 : ¬ 9 ∣ Nat.card T := by
      intro h9
      apply ha
      have hZT : Z ≤ T' := le_of_nine_dvd h415 hX P hT'P (hT'card ▸ h9)
      have hconj : conjugate Z (h : X) ≤ N := by
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨_, ⟨t, ht, rfl⟩, htz⟩ := hZT (inv_mem hz)
        have ht' : (t : H) • ((h : H) : H ⧸ NH) = ((h : H) : H ⧸ NH) := ht
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at ht'
        have ht'' : (((t : H) : X) * (h : X))⁻¹ * (h : X) ∈ N := by
          simpa using Subgroup.mem_subgroupOf.mp ht'
        have htz' : ((t : H) : X) = z⁻¹ := htz
        rw [htz'] at ht''
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        simpa [mul_assoc] using ht''
      have heq := conjugate_eq_of_le_normalizer h415 hX P hconj
      have hhN : (h : X) ∈ N := conjugate_eq_iff_mem_normalizer.mp heq
      rw [QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using inv_mem hhN)
    have hTd : Nat.card T ∣ 3 ^ 3 := Dvd.intro_left _ (by rw [horb]; norm_num)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hTd
    rw [hk'] at horb hT9
    interval_cases k
    · exact ⟨3, by omega⟩
    · exact ⟨1, by omega⟩
    · exact absurd (dvd_refl _) hT9
    · exact absurd ⟨3, by norm_num⟩ hT9

theorem le_normalizer_of_solvable (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hC9 : ∀ E : Subgroup X, Nat.card E = 9 → Subgroup.centralizer (E : Set X) ≤ E)
    (P : Sylow 3 X) {H : Subgroup X} (hPH : (P : Subgroup X) ≤ H)
    (hH : Nat.card H = 2 ^ 6 * 3 ^ 3 ∨ Nat.card H = 2 ^ 7 * 3 ^ 3) :
    H ≤ Subgroup.normalizer (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) :
      Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  have hZ3 : Nat.card Z = 3 := (j2_sylow_facts h415 hX P).1
  have hwc : ∀ g : X, conjugate Z g ≤ P → conjugate Z g = Z := (j2_sylow_facts h415 hX P).2.1
  have h27 := (card_sylow_center h415 hX P).1
  have hsolv : Group.IsSolvable H := by
    let _ := Fintype.ofFinite H
    rcases hH with h | h
    · exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h])
    · exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h])
  have hnt : Nontrivial H :=
    Finite.one_lt_card_iff_nontrivial.mp (by rcases hH with h | h <;> rw [h] <;> norm_num)
  obtain ⟨p, hp, hpH, U, hUn, hU1, hUp⟩ := exists_normal_isPGroup_of_isSolvable hsolv
  have hp23 : p = 2 ∨ p = 3 := by
    have hpH' : p ∣ 2 ^ 7 * 3 ^ 3 := by
      rcases hH with h | h
      · rw [h] at hpH
        exact hpH.trans ⟨2, by norm_num⟩
      · rwa [h] at hpH
    rcases (Nat.Prime.dvd_mul hp).mp hpH' with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  set U' := U.map H.subtype with hU'
  have hU'p : IsPGroup p U' := hUp.map _
  have hU'1 : U' ≠ ⊥ := fun h => hU1 ((Subgroup.map_eq_bot_iff_of_injective U
    H.subtype_injective).mp h)
  have hU'H : U' ≤ H := Subgroup.map_subtype_le U
  have hHN : H ≤ Subgroup.normalizer (U' : Set X) := by
    have hsub : U'.subgroupOf H = U := Subgroup.comap_map_eq_self_of_injective
      H.subtype_injective U
    have : (U'.subgroupOf H).Normal := hsub ▸ hUn
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hU'H).mp this
  rcases hp23 with rfl | rfl
  · exact absurd (hPH.trans hHN) fun h => false_of_le_normalizer_isPGroup_two h415 hX hC9 P hU'p
      hU'1 h
  have hfac : (Nat.card H).factorization 3 = 3 := by
    rcases hH with h | h <;> rw [h]
    · exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 2 ^ 6 * 3 ^ 3 = 3 ^ 3 * 64 by norm_num) (by norm_num)
    · exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 2 ^ 7 * 3 ^ 3 = 3 ^ 3 * 128 by norm_num) (by norm_num)
  set PH : Sylow 3 H := Sylow.ofCard ((P : Subgroup X).subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, h27, hfac]; norm_num)
  have hUP : U ≤ PH := IsPGroup.le_sylow_of_normal hUp PH
  have hU'P : U' ≤ P := by
    refine (Subgroup.map_mono hUP).trans ?_
    change ((P : Subgroup X).subgroupOf H).map H.subtype ≤ P
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hZU : Z ≤ U' := by
    have hdvd : Nat.card U' ∣ 3 ^ 3 := by
      rw [← show Nat.card (P : Subgroup X) = 3 ^ 3 by rw [h27]; norm_num]
      exact Subgroup.card_dvd_of_le hU'P
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hU'1 (Subgroup.eq_bot_of_card_eq U' (by simpa using hj'))
    by_cases hj1 : j = 1
    · subst hj1
      have hPC : (P : Subgroup X) ≤ Subgroup.centralizer (U' : Set X) :=
        le_centralizer_of_card_three P.isPGroup' (by simpa using hj') (hPH.trans hHN)
      have hU'Z : U' ≤ Z := le_inf hU'P (Subgroup.le_centralizer_iff.mp hPC)
      exact (Subgroup.eq_of_le_of_card_ge hU'Z (by rw [hZ3, hj', pow_one])).ge
    · refine le_of_nine_dvd h415 hX P hU'P ?_
      rw [hj']
      interval_cases j <;> omega
  intro g hg
  refine conjugate_eq_iff_mem_normalizer.mp (hwc g ?_)
  refine (Subgroup.map_mono hZU).trans ?_
  change conjugate U' g ≤ P
  rw [conjugate_eq_of_mem_normalizer (hHN hg)]
  exact hU'P

theorem false_of_card_five
    (hC9 : ∀ E : Subgroup X, Nat.card E = 9 → Subgroup.centralizer (E : Set X) ≤ E)
    {K : Subgroup X} (hK : Nat.card K = 135 ∨ Nat.card K = 270) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F⟩ := (Sylow.nonempty : Nonempty (Sylow 5 K))
  have hfac : (Nat.card K).factorization 5 = 1 := by
    rcases hK with h | h <;> rw [h]
    · exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq (by norm_num)
        (show (135 : ℕ) = 5 ^ 1 * 27 by norm_num) (by norm_num)
    · exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq (by norm_num)
        (show (270 : ℕ) = 5 ^ 1 * 54 by norm_num) (by norm_num)
  have hF5 : Nat.card (F : Subgroup K) = 5 := by
    rw [Sylow.card_eq_multiplicity, hfac, pow_one]
  set n5 := Nat.card (Sylow 5 K) with hn5
  have hn5mod : n5 % 5 = 1 := card_sylow_modEq_one 5 K
  have hn5dvd : n5 ∣ (F : Subgroup K).index := Sylow.card_dvd_index F
  have hidx : (F : Subgroup K).index * 5 = Nat.card K := by
    have h := (F : Subgroup K).card_mul_index
    rw [hF5] at h
    rw [← h, mul_comm]
  have hn5N : n5 = (Subgroup.normalizer ((F : Subgroup K) : Set K)).index :=
    Sylow.card_eq_index_normalizer F
  set N5 := Subgroup.normalizer ((F : Subgroup K) : Set K) with hN5
  have hN5card : Nat.card N5 * n5 = Nat.card K := by
    rw [hn5N]
    exact N5.card_mul_index
  have h54 : n5 ∣ 54 := by
    refine hn5dvd.trans ?_
    rcases hK with h | h
    · exact ⟨2, by omega⟩
    · exact ⟨1, by omega⟩
  have hn5' : n5 ∈ Nat.divisors 54 := Nat.mem_divisors.mpr ⟨h54, by norm_num⟩
  rw [show Nat.divisors 54 = {1, 2, 3, 6, 9, 18, 27, 54} from by decide] at hn5'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn5'
  have h9 : 9 ∣ Nat.card N5 := by
    rcases hn5' with h | h | h | h | h | h | h | h <;> rw [h] at hN5card hn5mod <;>
      rcases hK with hK | hK <;> omega
  obtain ⟨Q₀, hQ₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := N5) 3 (n := 2)
    (by norm_num; exact h9)
  set Q := Q₀.map N5.subtype with hQ
  have hQcard : Nat.card Q = 9 := by
    rw [hQ, Subgroup.card_map_of_injective N5.subtype_injective, hQ₀]
    norm_num
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := 2) (by rw [hQcard]; norm_num)
  have hQN : Q ≤ N5 := Subgroup.map_subtype_le Q₀
  obtain ⟨f, hfF, hf1, hfQ⟩ := exists_ne_one_commute_of_card_mod_three hQ3 (by rw [hF5])
    hQN
  set E := Q.map K.subtype with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective K.subtype_injective, hQcard]
  have hfE : (f : X) ∈ E := by
    refine hC9 E hE9 (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨q, hq, rfl⟩
    exact congrArg Subtype.val (hfQ q hq)
  have hf9 : (f : X) ^ 9 = 1 := by
    have h := pow_card_eq_one' (G := E) (x := ⟨(f : X), hfE⟩)
    rw [hE9] at h
    exact congrArg Subtype.val h
  have hf5 : f ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := (F : Subgroup K)) (x := ⟨f, hfF⟩)
    rw [hF5] at h
    exact congrArg Subtype.val h
  have hf5' : (f : X) ^ 5 = 1 := by rw [← Subgroup.coe_pow, hf5, Subgroup.coe_one]
  have hord : orderOf (f : X) ∣ Nat.gcd 9 5 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf9) (orderOf_dvd_of_pow_eq_one hf5')
  have h1 : (f : X) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hord))
  exact hf1 (Subtype.ext h1)

theorem false_of_card_four_three_two (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {H : Subgroup X}
    (hPH : (P : Subgroup X) ≤ H)
    (hk : Nat.card (Subgroup.normalizer (((P : Subgroup X) ⊓
      Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) : Set X) ⊓ H :
        Subgroup X) = 432) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card X = 604800 := KFacts.KS14.card_eq_of_j2 hX
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  set N := Subgroup.normalizer (Z : Set X) with hN
  have hZ3 : Nat.card Z = 3 := (j2_sylow_facts h415 hX P).1
  have hN2160 : Nat.card N = 2160 := card_normalizer_center h415 hX P
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Z = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hall x hx)
    rw [this, Subgroup.card_bot] at hZ3
    omega
  have hzpow : Subgroup.zpowers z = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_
    rw [hZ3, Nat.card_zpowers]
    have h3 : z ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Z) (x := ⟨z, hzZ⟩)
      rw [hZ3] at h
      exact congrArg Subtype.val h
    rw [orderOf_eq_prime h3 hz1]
  have hzP : z ∈ (P : Subgroup X) := (Subgroup.mem_inf.mp hzZ).1
  have hPC : (P : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZ).2 p hp)
  set C := Subgroup.centralizer ({z} : Set X) with hC
  obtain ⟨-, hN'3, hN'n, ⟨e⟩⟩ := KFacts.KS14.j2_centralizer_quotient h415 hX hz1 ⟨P, hzP, hPC⟩
  set N' := (Subgroup.zpowers z).subgroupOf C with hN'
  have : N'.Normal := hN'n
  have hC1080 : Nat.card C = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N', Nat.card_congr e.toEquiv, hN'3,
      Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hCN : C ≤ N := by
    intro x hx
    rw [hN, ← hzpow, Subgroup.mem_normalizer_iff]
    intro y
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      simp only
      rw [(Commute.zpow_right hxz k).eq, mul_inv_cancel_right]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simp only at hk ⊢
      have hc : x * z ^ k = z ^ k * x := (Commute.zpow_right hxz k).eq
      calc z ^ k = x⁻¹ * (x * z ^ k) := by group
        _ = x⁻¹ * (z ^ k * x) := by rw [hc]
        _ = x⁻¹ * (x * y * x⁻¹ * x) := by rw [hk]
        _ = y := by group
  have hNidx : N.index = 280 := by
    have h := N.card_mul_index
    rw [hN2160, hcard] at h
    omega
  have hCidx : C.index = 560 := by
    have h := C.card_mul_index
    rw [hC1080, hcard] at h
    omega
  have hCrel : C.relIndex N = 2 := by
    have h := Subgroup.relIndex_mul_index hCN
    rw [hNidx, hCidx] at h
    omega
  set K := N ⊓ H with hK
  have hrel : C.relIndex K ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hCrel]; norm_num)).trans_eq hCrel
  have hmul := Subgroup.relIndex_mul_card C K
  rw [hk] at hmul
  have hK₀dvd : Nat.card (C ⊓ K : Subgroup X) ∣ 1080 := hC1080 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hK₀ : Nat.card (C ⊓ K : Subgroup X) = 216 := by
    have hrel0 : C.relIndex K ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      omega
    have hr12 : C.relIndex K = 1 ∨ C.relIndex K = 2 := by omega
    rcases hr12 with hr | hr <;> rw [hr] at hmul
    · exfalso
      have hc : Nat.card (C ⊓ K : Subgroup X) = 432 := by omega
      rw [hc] at hK₀dvd
      norm_num at hK₀dvd
    · omega
  have hPK₀ : (P : Subgroup X) ≤ C ⊓ K :=
    le_inf hPC (le_inf (le_normalizer_center (P : Subgroup X)) hPH)
  have hzK₀ : Subgroup.zpowers z ≤ C ⊓ K := hzpow ▸ (inf_le_left.trans hPK₀)
  set K₀' := (C ⊓ K).subgroupOf C with hK₀'
  have hK₀'card : Nat.card K₀' = 216 := by
    rw [hK₀', Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hK₀]
  have hK₀'idx : K₀'.index = 5 := by
    have h := K₀'.card_mul_index
    rw [hK₀'card, hC1080] at h
    omega
  have hN'K₀' : N' ≤ K₀' := Subgroup.comap_mono hzK₀
  set I := K₀'.map (QuotientGroup.mk' N') with hI
  have hIidx : I.index = 5 := by
    rw [hI, Subgroup.index_map_eq K₀' (QuotientGroup.mk'_surjective N')
      (by rw [QuotientGroup.ker_mk']; exact hN'K₀'), hK₀'idx]
  set J := I.map (e : (C ⧸ N') →* alternatingGroup (Fin 6)) with hJ
  have hJidx : J.index = 5 := by
    rw [hJ, Subgroup.index_map_equiv, hIidx]
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  refine false_of_factorial_index_lt J ?_ ?_
  · intro htop
    rw [htop, Subgroup.index_top] at hJidx
    omega
  · rw [hJidx, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide

theorem eq_top_of_dvd (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) [IsSimpleGroup X]
    (hC9 : ∀ E : Subgroup X, Nat.card E = 9 → Subgroup.centralizer (E : Set X) ≤ E)
    (H : Subgroup X) (hH : 2 ^ 6 * 3 ^ 3 ∣ Nat.card H) : H = ⊤ := by
  classical
  have hcard : Nat.card X = 604800 := KFacts.KS14.card_eq_of_j2 hX
  obtain ⟨P, hPH⟩ := exists_sylow_le hcard H (dvd_trans ⟨64, by norm_num⟩ hH)
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  set N := Subgroup.normalizer (Z : Set X) with hN
  have h27 := (card_sylow_center h415 hX P).1
  have hN2160 : Nat.card N = 2160 := card_normalizer_center h415 hX P
  have hn : N.relIndex H ≡ 1 [MOD 9] := relIndex_modEq_one h415 hX P hPH
  have hnk := Subgroup.relIndex_mul_card N H
  have hNidx : N.index = 280 := by
    have h := N.card_mul_index
    rw [hN2160, hcard] at h
    omega
  have hn280 : N.relIndex H ≤ 280 := by
    have h := Subgroup.relIndex_le_of_le_right (H := N) (le_top : H ≤ ⊤)
      (by rw [Subgroup.relIndex_top_right, hNidx]; norm_num)
    rwa [Subgroup.relIndex_top_right, hNidx] at h
  have hk27 : 27 ∣ Nat.card (N ⊓ H : Subgroup X) :=
    h27 ▸ Subgroup.card_dvd_of_le (le_inf (le_normalizer_center (P : Subgroup X)) hPH)
  have hk2160 : Nat.card (N ⊓ H : Subgroup X) ∣ 2160 :=
    hN2160 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hH' : Nat.card H ∣ 604800 := hcard ▸ Subgroup.card_subgroup_dvd_card H
  have hidx : Nat.card H * H.index = 604800 := hcard ▸ H.card_mul_index
  have hHtop : H ≠ ⊤ → ∀ i : ℕ, H.index = i → i.factorial < 604800 → False := by
    intro hne i hi hlt
    exact false_of_factorial_index_lt H hne (by rw [hi, hcard]; exact hlt)
  rcases arith_cases (by simpa using hH) hH' hk27 hk2160 hnk hn hn280 with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1 | h1 | h1 | h1
  · exfalso
    have hle := le_normalizer_of_solvable h415 hX hC9 P hPH (Or.inl (by rw [h1]; norm_num))
    rw [inf_of_le_right hle, h1] at h2
    omega
  · exfalso
    have hle := le_normalizer_of_solvable h415 hX hC9 P hPH (Or.inr (by rw [h1]; norm_num))
    rw [inf_of_le_right hle, h1] at h2
    omega
  · exact (false_of_card_five hC9 (Or.inl h2)).elim
  · exact (false_of_card_five hC9 (Or.inr h2)).elim
  · exact (false_of_card_four_three_two h415 hX P hPH h2).elim
  · exact (false_of_card_four_three_two h415 hX P hPH h2).elim
  · exfalso
    exact false_of_index_ten hcard H (by rw [h1] at hidx; omega)
  · by_contra hne
    exact hHtop hne 5 (by rw [h1] at hidx; omega) (by decide)
  · by_contra hne
    exact hHtop hne 2 (by rw [h1] at hidx; omega) (by decide)
  · exact Subgroup.eq_top_of_card_eq H (by rw [h1, hcard])

end Res6Order

open Res6Order in
set_option maxHeartbeats 1000000 in
theorem ks142J2Order :
    KS142J2Order := by
  intro H hH
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  exact eq_top_of_dvd Sec4.Sporadic.rank3II_4_15 ⟨MulEquiv.refl _⟩
    (KFacts.ks17J2CentralizerNine _ ⟨MulEquiv.refl _⟩) H hH

end CFSG.RankThree.PartTwo.Sec14
