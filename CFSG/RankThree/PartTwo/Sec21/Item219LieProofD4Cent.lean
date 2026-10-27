module

public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Torus
import CFSG.RankThree.PartOne.K133H.D4Plane
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Arith
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofRoots
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS219.Tools
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofSL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  Subgroup

namespace Item219LieProof


variable {K : Type} [Field K] {σ : K ≃+* K}

theorem trialityTorusHom_injective (hσ3 : σ ^ 3 = 1) :
    Function.Injective (trialityTorusHom σ) := by
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  intro p p' h
  apply e.injective
  apply Subtype.ext
  rw [he, he]
  exact h

theorem trialityTorusHom_mem (hσ3 : σ ^ 3 = 1) (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ p ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have h := (e p).2
  rwa [he] at h

theorem exists_trialityTorusHom_eq (hσ3 : σ ^ 3 = 1) {y : ModGL TwistTag.D4.tag K}
    (hy : y ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom) :
    ∃ p, trialityTorusHom σ p = y := by
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  obtain ⟨p, hp⟩ := e.surjective ⟨y, hy⟩
  refine ⟨p, ?_⟩
  have h := congrArg Subtype.val hp
  rw [show p = (p.1, p.2) from rfl, he] at h
  exact h

theorem rotT_conj_of_cube (hσ3 : σ ^ 3 = 1) {c : (trialityFixedField K σ.toRingHom)ˣ}
    (hc : c ^ 3 = 1) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    rotT K * trialityTorusHom σ (trialityFixedUnit K σ c, b) * (rotT K)⁻¹ =
      trialityTorusHom σ (trialityFixedUnit K σ (c * b), b) := by
  rw [rotT_conj hσ3, trialityNorm_fixedUnit, hc, inv_one, one_mul, map_mul]

theorem conj_eq_iff_commute {G : Type*} [Group G] {x y : G} : x * y * x⁻¹ = y ↔ x * y = y * x := by
  constructor
  · intro h
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h]
  · intro h
    rw [h, mul_inv_cancel_right]

theorem rotT_pow_three_mem (hσ3 : σ ^ 3 = 1) {ζ : (trialityFixedField K σ.toRingHom)ˣ}
    (hζ : orderOf (trialityFixedUnit K σ ζ) = 3) :
    rotT K ^ 3 ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  have hinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  have hζ3 : ζ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one, ← hζ]
    exact pow_orderOf_eq_one _)
  have hcube : ∀ y : ModGL TwistTag.D4.tag K, rotT K ^ 3 * y * (rotT K ^ 3)⁻¹ =
      rotT K * (rotT K * (rotT K * y * (rotT K)⁻¹) * (rotT K)⁻¹) * (rotT K)⁻¹ := fun y => by
    rw [pow_succ, pow_two]
    group
  refine mem_graphFixedRootTorus_of_commute hζ (pow_mem rotT_mem 3) ?_ ?_
  · rw [← conj_eq_iff_commute, hcube, ← trialityTorusHom_one_right]
    rw [rotT_conj_of_cube hσ3 hζ3, mul_one, rotT_conj_of_cube hσ3 hζ3, mul_one,
      rotT_conj_of_cube hσ3 hζ3, mul_one]
  · rw [← conj_eq_iff_commute, hcube, ← trialityTorusHom_one_left]
    have h1 : (1 : Kˣ) = trialityFixedUnit K σ 1 := (map_one _).symm
    rw [h1, rotT_conj_of_cube hσ3 (one_pow 3), one_mul,
      rotT_conj_of_cube hσ3 hζ3, rotT_conj_of_cube hσ3 (by rw [mul_pow, hζ3, one_mul] :
        (ζ * ζ) ^ 3 = 1)]
    congr 2
    rw [← pow_two, ← pow_succ, hζ3]

theorem rotT_not_mem (hσ3 : σ ^ 3 = 1) {ζ : (trialityFixedField K σ.toRingHom)ˣ}
    (hζ : orderOf (trialityFixedUnit K σ ζ) = 3) :
    rotT K ∉ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  intro ht
  have hc := CFSG.RankThree.PartOne.K133H.graphFixedRootTorus_comm σ.toRingHom ht
    (trialityTorusHom_mem hσ3 (1, ζ))
  have h := rotT_conj hσ3 1 ζ
  rw [hc, mul_inv_cancel_right, map_one, inv_one, one_mul, one_mul] at h
  have h2 := congrArg Prod.fst (trialityTorusHom_injective hσ3 h)
  simp only at h2
  rw [← h2, orderOf_one] at hζ
  exact absurd hζ (by norm_num)

theorem fixed_of_rotT_conj (hσ3 : σ ^ 3 = 1) {a : Kˣ} {b : (trialityFixedField K σ.toRingHom)ˣ}
    (h : rotT K * trialityTorusHom σ (a, b) * (rotT K)⁻¹ = trialityTorusHom σ (a, b)) :
    b = 1 ∧ trialityNorm σ hσ3 a = 1 := by
  have hinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  rw [rotT_conj hσ3] at h
  have h' := trialityTorusHom_injective hσ3 h
  have h1 := congrArg Prod.fst h'
  have h2 := congrArg Prod.snd h'
  simp only at h1 h2
  have hN : trialityNorm σ hσ3 a = 1 := by
    have : (trialityNorm σ hσ3 a)⁻¹ = 1 := by
      calc (trialityNorm σ hσ3 a)⁻¹ = (trialityNorm σ hσ3 a)⁻¹ * b * b⁻¹ := by group
        _ = 1 := by rw [h2, mul_inv_cancel]
    rwa [inv_eq_one] at this
  rw [hN, inv_one, one_mul] at h1
  refine ⟨?_, hN⟩
  apply hinj
  rw [map_one]
  calc trialityFixedUnit K σ b = a⁻¹ * (a * trialityFixedUnit K σ b) := by group
    _ = 1 := by rw [h1, inv_mul_cancel]

theorem pow_three_of_norm_eq_one (hσ3 : σ ^ 3 = 1) {q : ℕ} (hσ : ∀ c, σ c = c ^ q)
    (hq : q % 3 = 1) {a : Kˣ} {m : ℕ} (ham : a ^ 3 ^ m = 1) (hN : trialityNorm σ hσ3 a = 1) :
    a ^ 3 = 1 := by
  have hσu : ∀ x : Kˣ, Units.map σ.toRingHom.toMonoidHom x = x ^ q := fun x =>
    Units.ext (by simp [hσ])
  have h := trialityFixedUnit_norm hσ3 a
  rw [hN, map_one, hσu, hσu, ← pow_mul, ← pow_succ', ← pow_add] at h
  refine pow_three_eq_one_of_pow_sq_add hq ham ?_
  rw [show q ^ 2 + q + 1 = q + 1 + q * q by ring, ← h]

theorem exists_sylow_center [Finite K] {n : ℕ} (hn : 0 < n) (hev : Even n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {ζ : (trialityFixedField K σ.toRingHom)ˣ} (hζ : orderOf (trialityFixedUnit K σ ζ) = 3) :
    ∃ P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Nat.card P =
        3 ^ (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization 3 ∧
      ∀ y ∈ P, (∀ p ∈ P, p * y = y * p) → ∃ j : ℕ,
        (y : ModGL TwistTag.D4.tag K) = trialityOuterTorus K σ (trialityFixedUnit K σ ζ) ^ j := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  set q := 2 ^ n with hqdef
  have hq3 : q % 3 = 1 := two_pow_mod_three hev
  have hq1 : 1 < q := Nat.one_lt_two_pow (by omega)
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set H₁ := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hH₁
  have hH₁C : H₁ ≤ C := graphFixedRootTorus_le _ _ _
  have hcommH₁ : ∀ x ∈ H₁, ∀ y ∈ H₁, x * y = y * x := fun x hx y hy =>
    CFSG.RankThree.PartOne.K133H.graphFixedRootTorus_comm σ.toRingHom hx hy
  obtain ⟨hCcard, hHcard, -⟩ := triality_both_orientations_exact_finite_order 2 n Nat.prime_two hn K
    hK 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  set H : Subgroup C := H₁.subgroupOf C with hH
  have hmemH : ∀ y : C, y ∈ H ↔ (y : ModGL TwistTag.D4.tag K) ∈ H₁ := fun y =>
    Subgroup.mem_subgroupOf
  have hHcard' : Nat.card H = (q ^ 3 - 1) * (q - 1) := by
    rw [hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₁C).toEquiv, hHcard]
  have hconj : ∀ x ∈ H₁, rotT K * x * (rotT K)⁻¹ ∈ H₁ := by
    intro x hx
    obtain ⟨⟨a, b⟩, rfl⟩ := exists_trialityTorusHom_eq hσ3 hx
    rw [rotT_conj hσ3]
    exact trialityTorusHom_mem hσ3 _
  have ht3 : rotT K ^ 3 ∈ H₁ := rotT_pow_three_mem hσ3 hζ
  have hconj' : ∀ x ∈ H₁, (rotT K)⁻¹ * x * rotT K ∈ H₁ := by
    intro x hx
    have hc := hcommH₁ _ ht3 x hx
    have e1 : (rotT K)⁻¹ * x * rotT K =
        rotT K ^ 2 * ((rotT K ^ 3)⁻¹ * x * rotT K ^ 3) * (rotT K ^ 2)⁻¹ := by group
    have e2 : (rotT K ^ 3)⁻¹ * x * rotT K ^ 3 = x := by
      rw [mul_assoc, ← hc, inv_mul_cancel_left]
    have e3 : rotT K ^ 2 * x * (rotT K ^ 2)⁻¹ =
        rotT K * (rotT K * x * (rotT K)⁻¹) * (rotT K)⁻¹ := by
      rw [pow_two]
      group
    rw [e1, e2, e3]
    exact hconj _ (hconj x hx)
  set t : C := ⟨rotT K, rotT_mem⟩ with htdef
  have htN : t ∈ normalizer (H : Set C) := by
    rw [mem_normalizer_iff]
    intro y
    rw [hmemH, hmemH]
    constructor
    · intro hy
      exact hconj _ hy
    · intro hy
      have h := hconj' _ hy
      have e : (rotT K)⁻¹ * ((t * y * t⁻¹ : C) : ModGL TwistTag.D4.tag K) * rotT K =
          (y : ModGL TwistTag.D4.tag K) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, htdef]
        group
      rwa [e] at h
  have hle : zpowers t ≤ normalizer (H : Set C) := zpowers_le.2 htN
  have htH : t ∉ H := fun h => rotT_not_mem hσ3 hζ ((hmemH t).1 h)
  have ht3H : t ^ 3 ∈ H := (hmemH _).2 (by simpa using ht3)
  have hpowH : ∀ k : ℤ, t ^ k ∈ H ↔ (3 : ℤ) ∣ k := by
    intro k
    constructor
    · intro hk
      have e : t ^ (k % 3) = ((t ^ 3) ^ (k / 3))⁻¹ * t ^ k := by
        rw [Int.emod_def, sub_eq_neg_add, zpow_add, zpow_neg, zpow_mul]
        norm_cast
      have hr : t ^ (k % 3) ∈ H := by
        rw [e]
        exact mul_mem (inv_mem (zpow_mem ht3H _)) hk
      rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
      · exact Int.dvd_of_emod_eq_zero h0
      · rw [h1, zpow_one] at hr
        exact absurd hr htH
      · rw [h2] at hr
        have : t = t ^ 3 * (t ^ (2 : ℤ))⁻¹ := by group
        exact absurd (this ▸ mul_mem ht3H (inv_mem hr)) htH
    · rintro ⟨j, rfl⟩
      rw [zpow_mul]
      exact zpow_mem (by simpa using ht3H) j
  have hcard := Sec6.card_sup_mul_card_inf hle
  have hinf : zpowers t ⊓ H = zpowers (t ^ 3) := by
    ext x
    rw [mem_inf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩
      obtain ⟨j, rfl⟩ := (hpowH k).1 hk
      exact ⟨j, by rw [zpow_mul]; norm_cast⟩
    · rintro ⟨j, rfl⟩
      refine ⟨⟨3 * j, by rw [zpow_mul]; norm_cast⟩, zpow_mem ht3H j⟩
  have hord3 : 3 ∣ orderOf t := by
    have h1 := (hpowH (orderOf t)).1 (by rw [zpow_natCast, pow_orderOf_eq_one]; exact one_mem _)
    exact_mod_cast h1
  have hcard3 : Nat.card (zpowers (t ^ 3)) = orderOf t / 3 := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) hord3]
  rw [hinf, hcard3, Nat.card_zpowers, sup_comm] at hcard
  have hNcard : Nat.card (H ⊔ zpowers t : Subgroup C) = 3 * Nat.card H := by
    obtain ⟨m, hm⟩ := hord3
    have hm0 : 0 < m := by
      have := orderOf_pos t
      rw [hm] at this
      omega
    rw [hm, Nat.mul_div_cancel_left _ (by norm_num)] at hcard
    refine Nat.eq_of_mul_eq_mul_right hm0 ?_
    rw [hcard]
    ring
  have hvH : padicValNat 3 (Nat.card H) = 2 * padicValNat 3 (q - 1) + 1 := by
    rw [hHcard']
    exact padicValNat_torus hq3 hq1
  have hvN : padicValNat 3 (Nat.card (H ⊔ zpowers t : Subgroup C)) =
      2 * padicValNat 3 (q - 1) + 2 := by
    rw [hNcard, padicValNat.mul (by norm_num) Nat.card_pos.ne', hvH, padicValNat_self]
    ring
  have hvC : padicValNat 3 (Nat.card C) = 2 * padicValNat 3 (q - 1) + 2 := by
    rw [hCcard]
    exact padicValNat_trialityD4 hq3 hq1
  have hfac : (Nat.card (H ⊔ zpowers t : Subgroup C)).factorization 3 =
      (Nat.card C).factorization 3 := by
    rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three, hvN,
      hvC]
  set zA : C := ⟨trialityOuterTorus K σ (trialityFixedUnit K σ ζ), hH₁C (by
    rw [← trialityTorusHom_one_right]
    exact trialityTorusHom_mem hσ3 _)⟩ with hzA
  set zB : C := ⟨trialityMiddleTorus K σ ζ, hH₁C (by
    rw [← trialityTorusHom_one_left]
    exact trialityTorusHom_mem hσ3 _)⟩ with hzB
  have hinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  have hζ3 : ζ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one, ← hζ]
    exact pow_orderOf_eq_one _)
  have hzAH : zA ∈ H := (hmemH _).2 (by
    show trialityOuterTorus K σ (trialityFixedUnit K σ ζ) ∈ H₁
    rw [← trialityTorusHom_one_right]
    exact trialityTorusHom_mem hσ3 _)
  have hzBH : zB ∈ H := (hmemH _).2 (by
    show trialityMiddleTorus K σ ζ ∈ H₁
    rw [← trialityTorusHom_one_left]
    exact trialityTorusHom_mem hσ3 _)
  have hzA3 : zA ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show trialityOuterTorus K σ (trialityFixedUnit K σ ζ) ^ 3 = 1
    rw [← trialityTorusHom_one_right, ← map_pow (trialityTorusHom σ), Prod.pow_mk, one_pow,
      ← map_pow, hζ3, map_one, ← Prod.one_eq_mk, map_one])
  have hzB3 : zB ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show trialityMiddleTorus K σ ζ ^ 3 = 1
    rw [← trialityTorusHom_one_left, ← map_pow (trialityTorusHom σ), Prod.pow_mk, one_pow,
      hζ3, ← Prod.one_eq_mk, map_one])
  have hzAB : zA * zB = zB * zA := Subtype.ext (hcommH₁ _ ((hmemH _).1 hzAH) _ ((hmemH _).1 hzBH))
  set V : Subgroup C := zpowers zA ⊔ zpowers zB with hV
  have hVp : IsPGroup 3 V := by
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three hzA3)
      (isPGroup_zpowers_of_pow_three hzB3) (zpowers_le.2 ?_)
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [((Commute.zpow_right hzAB k).eq), mul_inv_cancel_right]
      exact hy
    · intro hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
      have hc : Commute zA (zA * y * zA⁻¹) := by
        rw [← hk]
        exact Commute.zpow_right hzAB k
      have : y = zA * y * zA⁻¹ := by
        calc y = zA⁻¹ * (zA * y * zA⁻¹) * zA := by group
          _ = zA⁻¹ * zA * (zA * y * zA⁻¹) := by rw [mul_assoc zA⁻¹, hc.symm.eq, ← mul_assoc]
          _ = zA * y * zA⁻¹ := by group
      rw [this]
      exact hy
  set N : Subgroup C := H ⊔ zpowers t with hN
  have hVN : V ≤ N := sup_le (zpowers_le.2 (mem_sup_left hzAH)) (zpowers_le.2 (mem_sup_left hzBH))
  have hVNp : IsPGroup 3 (V.subgroupOf N) := hVp.comap_of_injective N.subtype N.subtype_injective
  obtain ⟨Q, hQ⟩ := hVNp.exists_le_sylow
  set P : Subgroup C := (Q : Subgroup N).map N.subtype with hP
  have hPN : P ≤ N := map_subtype_le _
  have hVP : V ≤ P := fun v hv => ⟨⟨v, hVN hv⟩, hQ (Subgroup.mem_subgroupOf.2 hv), rfl⟩
  have hPcard : Nat.card P = 3 ^ (Nat.card N).factorization 3 := by
    rw [hP, card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
  refine ⟨P, by rw [hPcard, hfac], fun y hyP hyc => ?_⟩
  have hyA : zA * y = y * zA := hyc zA (hVP (mem_sup_left (mem_zpowers zA)))
  have hyB : zB * y = y * zB := hyc zB (hVP (mem_sup_right (mem_zpowers zB)))
  have hyH₁ : (y : ModGL TwistTag.D4.tag K) ∈ H₁ := by
    refine mem_graphFixedRootTorus_of_commute hζ y.2 ?_ ?_
    · have := congrArg Subtype.val hyA
      simp only [Subgroup.coe_mul] at this
      exact this.symm
    · have := congrArg Subtype.val hyB
      simp only [Subgroup.coe_mul] at this
      exact this.symm
  have hyH : y ∈ H := (hmemH y).2 hyH₁
  obtain ⟨p, hpP, hpH⟩ : ∃ p ∈ P, p ∉ H := by
    by_contra hcon
    push Not at hcon
    have hdvd : Nat.card P ∣ Nat.card H := card_dvd_of_le hcon
    rw [hPcard, Nat.factorization_def _ Nat.prime_three, hvN,
      padicValNat_dvd_iff_le Nat.card_pos.ne', hvH] at hdvd
    omega
  have hset := coe_mul_of_left_le_normalizer_right (zpowers t) H hle
  have hpN' : p ∈ ((zpowers t ⊔ H : Subgroup C) : Set C) := by
    rw [sup_comm]
    exact hPN hpP
  rw [hset] at hpN'
  obtain ⟨s, hs, h, hh, rfl⟩ := hpN'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
  have hk : ¬ (3 : ℤ) ∣ k := fun h3 => hpH (mul_mem ((hpowH k).2 h3) hh)
  have hhy : h * y = y * h := Subtype.ext (hcommH₁ _ ((hmemH _).1 hh) _ hyH₁)
  have hck : Commute (t ^ k) y := by
    have hyp := hyc _ hpP
    have : t ^ k * y * h = y * t ^ k * h := by
      calc t ^ k * y * h = t ^ k * (y * h) := by group
        _ = t ^ k * (h * y) := by rw [hhy]
        _ = t ^ k * h * y := by group
        _ = y * (t ^ k * h) := hyp
        _ = y * t ^ k * h := by group
    exact mul_right_cancel this
  have hc3 : Commute (t ^ 3) y := Subtype.ext (hcommH₁ _ ((hmemH _).1 ht3H) _ hyH₁)
  have hcr : Commute (t ^ (k % 3)) y := by
    have e : t ^ (k % 3) = ((t ^ 3) ^ (k / 3))⁻¹ * t ^ k := by
      rw [Int.emod_def, sub_eq_neg_add, zpow_add, zpow_neg, zpow_mul]
      norm_cast
    rw [e]
    exact ((hc3.zpow_left _).inv_left).mul_left hck
  have hct : Commute t y := by
    rcases (show k % 3 = 1 ∨ k % 3 = 2 by omega) with h1 | h2
    · rwa [h1, zpow_one] at hcr
    · rw [h2] at hcr
      have e : t = t ^ 3 * (t ^ (2 : ℤ))⁻¹ := by group
      rw [e]
      exact hc3.mul_left hcr.inv_left
  obtain ⟨⟨a, b⟩, hab⟩ := exists_trialityTorusHom_eq hσ3 hyH₁
  have hfix : rotT K * trialityTorusHom σ (a, b) * (rotT K)⁻¹ = trialityTorusHom σ (a, b) := by
    rw [hab, conj_eq_iff_commute]
    have := congrArg Subtype.val hct.eq
    simpa using this
  obtain ⟨rfl, hNa⟩ := fixed_of_rotT_conj hσ3 hfix
  have hPp : IsPGroup 3 P := Q.isPGroup'.map N.subtype
  obtain ⟨m, hm⟩ := hPp ⟨y, hyP⟩
  have hym : (y : ModGL TwistTag.D4.tag K) ^ 3 ^ m = 1 := by
    have h1 := congrArg (fun u : P => ((u : C) : ModGL TwistTag.D4.tag K)) hm
    simpa using h1
  have ham : a ^ 3 ^ m = 1 := by
    have h1 : trialityTorusHom σ (a, 1) ^ 3 ^ m = trialityTorusHom σ 1 := by
      rw [hab, hym, map_one]
    rw [← map_pow, Prod.pow_mk, one_pow] at h1
    exact congrArg Prod.fst (trialityTorusHom_injective hσ3 h1)
  have ha3 : a ^ 3 = 1 := pow_three_of_norm_eq_one hσ3 hσ hq3 ham hNa
  have hω3 : trialityFixedUnit K σ ζ ^ 3 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one _
  have hω1 : trialityFixedUnit K σ ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  have key : ∀ j : ℕ, a = trialityFixedUnit K σ ζ ^ j → ∃ j' : ℕ,
      (y : ModGL TwistTag.D4.tag K) = trialityOuterTorus K σ (trialityFixedUnit K σ ζ) ^ j' := by
    intro j hj
    refine ⟨j, ?_⟩
    rw [← hab, hj, ← trialityTorusHom_one_right, ← map_pow (trialityTorusHom σ), Prod.pow_mk,
      one_pow]
  rcases Sec11.KS11Lie4Proof.cube_root_cases hω3 hω1 ha3 with h0 | h1 | h2
  · exact key 0 (by rw [h0, pow_zero])
  · exact key 1 (by rw [h1, pow_one])
  · exact key 2 h2

theorem trialityOuterTorus_mem_range (hσ3 : σ ^ 3 = 1) (z : Kˣ) :
    trialityOuterTorus K σ z ∈
      (orbitRankOneHom TwistTag.D4 K σ.toRingHom Sec11.KS11Lie4Proof.d4Outer).range := by
  refine ⟨HSL (trialityOuterParam hσ3 z), ?_⟩
  rw [orbitRankOneHom_HSL]
  have h := trialityTorusHom_eq_orbitH hσ3 z 1
  have h1 : trialityMiddleParam (σ := σ) 1 = 1 :=
    Units.ext (Subtype.ext (by simp only [trialityMiddleParam, map_one]; rfl))
  rw [h1, orbitH_one', mul_one, trialityTorusHom_one_right] at h
  exact h.symm

theorem ks219D4ThreeCentral_holds : KS219D4ThreeCentral := by
  intro K _ _ n σ hn hev hK hσ z hz1 hzc
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have hq3 : 2 ^ n % 3 = 1 := two_pow_mod_three hev
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 := by
    refine exists_prime_orderOf_dvd_card' 3 ?_
    rw [Nat.card_units, hK]
    have h1 : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    have h2 : (2 ^ n) ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hσω : σ (ω : K) = ω := by
    rw [hσ]
    obtain ⟨r, hr⟩ : ∃ r, 2 ^ n = 3 * r + 1 := ⟨2 ^ n / 3, by omega⟩
    have hω3' : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    rw [hr, pow_succ, pow_mul, hω3', one_pow, one_mul]
  set ζ : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨(ω : K), (mem_trialityFixedField).2 hσω⟩
      (fun h => ω.ne_zero (congrArg Subtype.val h)) with hζdef
  have hζω : trialityFixedUnit K σ ζ = ω := Units.ext rfl
  have hζ : orderOf (trialityFixedUnit K σ ζ) = 3 := by rw [hζω, hω]
  obtain ⟨P, hPcard, hPcen⟩ := exists_sylow_center hn hev hK hσ hζ
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219.exists_conj_mem_center_of_isCentral218 hPcard hzc
  obtain ⟨hgP, hgC⟩ := mem_inf.mp hg
  obtain ⟨j, hj⟩ := hPcen _ hgP (fun p hp => mem_centralizer_iff.mp hgC p hp)
  have hwC : trialityOuterTorus K σ (trialityFixedUnit K σ ζ) ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← trialityTorusHom_one_right]
    exact graphFixedRootTorus_le _ _ _ (trialityTorusHom_mem hσ3 _)
  set w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    ⟨trialityOuterTorus K σ (trialityFixedUnit K σ ζ), hwC⟩ with hwdef
  have hgw : g⁻¹ * z * g = w ^ j := Subtype.ext (by rw [hj, Subgroup.coe_pow])
  have hw3 : w ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show trialityOuterTorus K σ (trialityFixedUnit K σ ζ) ^ 3 = 1
    rw [← trialityTorusHom_one_right, ← map_pow (trialityTorusHom σ), Prod.pow_mk, one_pow, hζω,
      hω3, ← Prod.one_eq_mk, map_one])
  have hwS : w ∈ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
    rw [Sec11.KS11Lie4Proof.d4ShortSL2, Subgroup.mem_comap]
    exact trialityOuterTorus_mem_range hσ3 _
  refine ⟨?_, g⁻¹, ?_⟩
  · have h1 : (g⁻¹ * z * g) ^ 3 = 1 := by
      rw [hgw, ← pow_mul, mul_comm, pow_mul, hw3, one_pow]
    have h2 : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [h2, conj_pow, h1, mul_one, mul_inv_cancel]
  · rw [inv_inv, hgw]
    exact pow_mem hwS j

theorem ks219D4_holds : KS219D4 :=
  ks219D4_of ks219D4ThreeCentral_holds

end Item219LieProof

end CFSG.RankThree.PartTwo.Sec21
