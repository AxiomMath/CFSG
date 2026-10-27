module

public import CFSG.RankThree.PartTwo.KFacts.KS167D4Model
public import CFSG.RankThree.PartTwo.KFacts.KS167D4
public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL3
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Torus
public import CFSG.Models.PGLSimple
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.ExtendProps
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS167D4Proof

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res417Seven
  CFSG.RankThree.PartTwo.Sec8.Item8ModelProof CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec21.Item219LieProof
  CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ordTrialityD4_eq_ordA_mul {n : ℕ} (hn : 1 ≤ n) (hev : Even n) :
    ordTrialityD4 (2 ^ n) = ordA 2 (2 ^ n) *
      (3 * (2 ^ n) ^ 9 * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) * ((2 ^ n) ^ 3 + 1)) := by
  set q := 2 ^ n with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq1 : 1 ≤ q := by omega
  have hq31 : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q (by omega)
  have hmod : q % 3 = 1 := by
    rw [hq]
    exact two_pow_mod_three_of_even hev
  have h3q : 3 ∣ q - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hg : Nat.gcd 3 (q - 1) = 3 := by
    rw [Nat.gcd_eq_left h3q]
  have hA : ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 := by
    rw [ordA, show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num),
      show 2 * (2 + 1) / 2 = 3 by norm_num, hg]
  have hdvd : 3 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
      (h3q.trans (Nat.sub_one_dvd_pow_sub_one q 3)) (q ^ 2 - 1)) (q ^ 3)
  have hN : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 * 3 =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.div_mul_cancel hdvd
  have h6 : (q ^ 3 - 1) * (q ^ 3 + 1) = q ^ 6 - 1 := by
    rw [mul_comm, ← Nat.sq_sub_sq, one_pow, ← pow_mul]
  have hRHS : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 *
      (3 * q ^ 9 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1)) = ordTrialityD4 q := by
    rw [ordTrialityD4]
    calc q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 *
          (3 * q ^ 9 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1))
        = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 * 3 *
            (q ^ 9 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1)) := by ring
      _ = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) *
            (q ^ 9 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1)) := by rw [hN]
      _ = q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
            rw [← h6]
            ring
  rw [hA, hRHS]

private theorem dvd_eighteen_of_dvd {r q : ℕ} (hr : r.Prime) (hq : q % r = 1)
    (hX : r ∣ 3 * q ^ 9 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1)) : r ∣ 18 := by
  have hr1 : 1 < r := hr.one_lt
  have hone : 1 % r = 1 := Nat.mod_eq_of_lt hr1
  have hqM : q ≡ 1 [MOD r] := by
    show q % r = 1 % r
    rw [hq, hone]
  have h9 : q ^ 9 ≡ 1 [MOD r] := by simpa using hqM.pow 9
  have hsum : q ^ 8 + q ^ 4 + 1 ≡ 3 [MOD r] := by
    have h : q ^ 8 + q ^ 4 + 1 ≡ 1 + 1 + 1 [MOD r] :=
      ((hqM.pow 8).add (hqM.pow 4)).add (Nat.ModEq.refl 1)
    simpa using h
  have h3p : q ^ 3 + 1 ≡ 2 [MOD r] := by
    have h : q ^ 3 + 1 ≡ 1 + 1 [MOD r] := (hqM.pow 3).add (Nat.ModEq.refl 1)
    simpa using h
  have hXmod : 3 * q ^ 9 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1) ≡ 18 [MOD r] := by
    have h : 3 * q ^ 9 * (q ^ 8 + q ^ 4 + 1) * (q ^ 3 + 1) ≡
        3 * 1 * (1 + 1 + 1) * (1 + 1) [MOD r] :=
      (((Nat.ModEq.refl 3).mul h9).mul hsum).mul h3p
    simpa using h
  exact Nat.dvd_of_mod_eq_zero ((hXmod ▸ Nat.mod_eq_zero_of_dvd hX))


section Certs


variable {K : Type} [Field K] [Finite K]

private theorem card_trialityFixedField {n : ℕ} (hn : 1 ≤ n) {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hσ3 : σ ^ 3 = 1) :
    Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n := by
  obtain ⟨-, -, -, hL2, -, -, -, -, -⟩ :=
    triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  rw [← hL2, card_orbitField_D4_orientation Nat.prime_two hn hK (Or.inl rfl)
    (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) ⟨1, by decide⟩,
    show (TwistTag.D4.orbit (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)).card = 1
      by decide,
    pow_one]

private theorem delta_fixes_trialityFixedField {n : ℕ} (hn3 : ¬ 3 ∣ n)
    {σ δ : K ≃+* K} (hδ3 : δ ^ 3 = 1)
    (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n) :
    ∀ x : trialityFixedField K σ.toRingHom, δ (x : K) = x := by
  let δ' : RingAut (fixSubfield σ) := fixSubfieldRestrict δ σ
  have hδ'3 : δ' ^ 3 = 1 := fixSubfieldRestrict_pow_eq_one (σ := δ) (δ := σ) hδ3
  have hcard : Nat.card (RingAut (fixSubfield σ)) = n := by
    have hk' : Nat.card (fixSubfield σ) = 2 ^ n := hk
    exact (card_ringAut_and_isCyclic Nat.prime_two (fixSubfield σ) hk').1
  have h1 : orderOf δ' ∣ 3 := orderOf_dvd_of_pow_eq_one hδ'3
  have h2 : orderOf δ' ∣ n := by
    rw [← hcard]
    exact orderOf_dvd_natCard δ'
  have h3 : orderOf δ' ∣ Nat.gcd 3 n := Nat.dvd_gcd h1 h2
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3
  have h4 : orderOf δ' = 1 := by
    rw [hcop.gcd_eq_one] at h3
    exact Nat.dvd_one.mp h3
  have hδ'1 : δ' = 1 := orderOf_eq_one_iff.mp h4
  intro x
  have h := congrArg (fun f : RingAut (fixSubfield σ) => ((f ⟨x, x.2⟩ : fixSubfield σ) : K))
    hδ'1
  simpa [δ', coe_fixSubfieldRestrict] using h

private theorem three_dvd_card_trialityFixedField_sub_one {n : ℕ} (hev : Even n)
    {σ : K ≃+* K} (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n) :
    3 ∣ Nat.card (trialityFixedField K σ.toRingHom) - 1 := by
  rw [hk, Nat.dvd_iff_mod_eq_zero]
  have := two_pow_mod_three_of_even hev
  omega

private theorem trialityOuterTorus_mem_d4Torsion {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1)
    {ζ : (trialityFixedField K σ.toRingHom)ˣ} (hζ : orderOf ζ = 3) :
    trialityOuterTorus K σ (trialityFixedUnit K σ ζ) ∈ K133H.d4Torsion σ.toRingHom 3 := by
  set z : Kˣ := trialityFixedUnit K σ ζ with hz
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, hζ3, map_one]
  have hT1 : trialityTorusHom σ (z, 1) = trialityOuterTorus K σ z := by
    rw [trialityTorusHom_apply, trialityMiddleTorus, map_one, torusElt_one, mul_one]
  rw [K133H.mem_d4Torsion_iff]
  refine ⟨?_, ?_⟩
  · rw [← hT1]
    rw [← graphFixedTorus_eq_graphFixedRootTorus_D4 (K := K) hσ3]
    exact trialityTorusHom_mem_graphFixedTorus hσ3 (z, 1)
  · rw [hz, trialityOuterTorus_eq_outerTuple (σ := σ) ζ, ← hz,
      show rootDiagUnit TwistTag.D4.tag (outerTuple z) =
        rootDiagUnitHom TwistTag.D4.tag K (outerTuple z) from rfl,
      ← map_pow (rootDiagUnitHom TwistTag.D4.tag K) (outerTuple z) 3]
    have h1 : (z ^ (2 : ℤ)) ^ 3 = 1 := by
      rw [show (z ^ (2 : ℤ)) = z ^ 2 from zpow_natCast z 2,
        show (z ^ 2) ^ 3 = (z ^ 3) ^ 2 by group, hz3, one_pow]
    have h2 : (z ^ (-3 : ℤ)) ^ 3 = 1 := by
      rw [show z ^ (-3 : ℤ) = (z ^ 3)⁻¹ by
        rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, zpow_neg,
          show z ^ (3 : ℤ) = z ^ 3 from zpow_natCast z 3],
        hz3, inv_one, one_pow]
    have hmap : outerTuple z ^ 3 = d4Tuple ((z ^ (2 : ℤ)) ^ 3) ((z ^ (2 : ℤ)) ^ 3)
        ((z ^ (-3 : ℤ)) ^ 3) ((z ^ (2 : ℤ)) ^ 3) := by
      funext i
      rw [Pi.pow_apply]
      obtain ⟨k, hk⟩ := i
      have hk4 : k < 4 := hk
      interval_cases k <;> rfl
    rw [hmap, h1, h2, vec4_one, map_one]

private theorem trialityMiddleTorus_mem_d4Torsion {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1)
    {ζ : (trialityFixedField K σ.toRingHom)ˣ} (hζ : orderOf ζ = 3) :
    trialityMiddleTorus K σ ζ ∈ K133H.d4Torsion σ.toRingHom 3 := by
  set z : Kˣ := trialityFixedUnit K σ ζ with hz
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, hζ3, map_one]
  have hT2 : trialityTorusHom σ (1, ζ) = trialityMiddleTorus K σ ζ := by
    rw [trialityTorusHom_apply, trialityOuterTorus_eq]
    simp only [map_one, torusElt_one, one_mul]
  rw [K133H.mem_d4Torsion_iff]
  refine ⟨?_, ?_⟩
  · rw [← hT2]
    rw [← graphFixedTorus_eq_graphFixedRootTorus_D4 (K := K) hσ3]
    exact trialityTorusHom_mem_graphFixedTorus hσ3 (1, ζ)
  · rw [trialityMiddleTorus_eq_middleTuple (σ := σ) ζ, ← hz,
      show rootDiagUnit TwistTag.D4.tag (middleTuple z) =
        rootDiagUnitHom TwistTag.D4.tag K (middleTuple z) from rfl,
      ← map_pow (rootDiagUnitHom TwistTag.D4.tag K) (middleTuple z) 3]
    have h1 : (z ^ (-1 : ℤ)) ^ 3 = 1 := by
      rw [show z ^ (-1 : ℤ) = z⁻¹ by
        rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num, zpow_neg, zpow_one],
        inv_pow, hz3, inv_one]
    have h2 : (z ^ (2 : ℤ)) ^ 3 = 1 := by
      rw [show (z ^ (2 : ℤ)) = z ^ 2 from zpow_natCast z 2,
        show (z ^ 2) ^ 3 = (z ^ 3) ^ 2 by group, hz3, one_pow]
    have hmap : middleTuple z ^ 3 = d4Tuple ((z ^ (-1 : ℤ)) ^ 3) ((z ^ (-1 : ℤ)) ^ 3)
        ((z ^ (2 : ℤ)) ^ 3) ((z ^ (-1 : ℤ)) ^ 3) := by
      funext i
      rw [Pi.pow_apply]
      obtain ⟨k, hk⟩ := i
      have hk4 : k < 4 := hk
      interval_cases k <;> rfl
    rw [hmap, h1, h2, vec4_one, map_one]

private theorem exists_zeta_order_three {σ : K ≃+* K}
    (h3 : 3 ∣ Nat.card (trialityFixedField K σ.toRingHom) - 1) :
    ∃ ζ : (trialityFixedField K σ.toRingHom)ˣ, orderOf ζ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (trialityFixedField K σ.toRingHom)ˣ)
    3 (by rw [Nat.card_units (trialityFixedField K σ.toRingHom)]; exact h3)
  exact ⟨ζ, hζ⟩

private theorem fieldActor_outerTuple_fixed {δ : K ≃+* K} {z : Kˣ}
    (hδz : Units.map δ.toRingHom.toMonoidHom z = z) :
    Units.map (entrywiseHom δ.toRingHom)
        (rootDiagUnit TwistTag.D4.tag (outerTuple z)) =
      rootDiagUnit TwistTag.D4.tag (outerTuple z) := by
  rw [units_map_entrywiseHom_rootDiagUnit]
  congr 1
  have hmap : (fun i => Units.map δ.toRingHom.toMonoidHom
        (d4Tuple (z ^ (2 : ℤ)) (z ^ (2 : ℤ)) (z ^ (-3 : ℤ)) (z ^ (2 : ℤ)) i)) =
      d4Tuple (Units.map δ.toRingHom.toMonoidHom (z ^ (2 : ℤ)))
        (Units.map δ.toRingHom.toMonoidHom (z ^ (2 : ℤ)))
        (Units.map δ.toRingHom.toMonoidHom (z ^ (-3 : ℤ)))
        (Units.map δ.toRingHom.toMonoidHom (z ^ (2 : ℤ))) := by
    funext i
    obtain ⟨k, hk⟩ := i
    have hk4 : k < 4 := hk
    interval_cases k <;> rfl
  rw [hmap]
  congr 1 <;> rw [map_zpow, hδz]

private theorem fieldActor_middleTuple_fixed {δ : K ≃+* K} {z : Kˣ}
    (hδz : Units.map δ.toRingHom.toMonoidHom z = z) :
    Units.map (entrywiseHom δ.toRingHom)
        (rootDiagUnit TwistTag.D4.tag (middleTuple z)) =
      rootDiagUnit TwistTag.D4.tag (middleTuple z) := by
  rw [units_map_entrywiseHom_rootDiagUnit]
  congr 1
  have hmap : (fun i => Units.map δ.toRingHom.toMonoidHom
        (d4Tuple (z ^ (-1 : ℤ)) (z ^ (-1 : ℤ)) (z ^ (2 : ℤ)) (z ^ (-1 : ℤ)) i)) =
      d4Tuple (Units.map δ.toRingHom.toMonoidHom (z ^ (-1 : ℤ)))
        (Units.map δ.toRingHom.toMonoidHom (z ^ (-1 : ℤ)))
        (Units.map δ.toRingHom.toMonoidHom (z ^ (2 : ℤ)))
        (Units.map δ.toRingHom.toMonoidHom (z ^ (-1 : ℤ))) := by
    funext i
    obtain ⟨k, hk⟩ := i
    have hk4 : k < 4 := hk
    interval_cases k <;> rfl
  rw [hmap]
  congr 1 <;> rw [map_zpow, hδz]

private theorem fieldActor_fixes_outerTorus {σ δ : K ≃+* K} {a : Kˣ}
    (hσa : σ (a : K) = (a : K))
    (hδa : Units.map δ.toRingHom.toMonoidHom a = a)
    (hC : trialityOuterTorus K σ a ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    fieldActor (t := TwistTag.D4) σ δ ⟨trialityOuterTorus K σ a, hC⟩ =
      ⟨trialityOuterTorus K σ a, hC⟩ := by
  let ζ : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 (⟨(a : K), hσa⟩ : trialityFixedField K σ.toRingHom)
      (fun h => a.ne_zero (by simpa using congrArg Subtype.val h))
  have hζa : trialityFixedUnit K σ ζ = a := Units.ext rfl
  have houter : trialityOuterTorus K σ a = rootDiagUnit TwistTag.D4.tag (outerTuple a) := by
    have h := trialityOuterTorus_eq_outerTuple (σ := σ) ζ
    rwa [hζa] at h
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom δ.toRingHom) (trialityOuterTorus K σ a) =
    trialityOuterTorus K σ a
  rw [houter]
  exact fieldActor_outerTuple_fixed hδa

private theorem fieldActor_fixes_middleTorus {σ δ : K ≃+* K}
    {b : (trialityFixedField K σ.toRingHom)ˣ}
    (hδb : Units.map δ.toRingHom.toMonoidHom (trialityFixedUnit K σ b) =
      trialityFixedUnit K σ b)
    (hC : trialityMiddleTorus K σ b ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    fieldActor (t := TwistTag.D4) σ δ ⟨trialityMiddleTorus K σ b, hC⟩ =
      ⟨trialityMiddleTorus K σ b, hC⟩ := by
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom δ.toRingHom) (trialityMiddleTorus K σ b) =
    trialityMiddleTorus K σ b
  rw [trialityMiddleTorus_eq_middleTuple (σ := σ) b]
  exact fieldActor_middleTuple_fixed hδb

private theorem fieldActor_fixes_d4Torsion {n : ℕ} (hev : Even n) (hn3 : ¬ 3 ∣ n)
    {σ δ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hδ3 : δ ^ 3 = 1) (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n) :
    ∀ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (v : ModGL TwistTag.D4.tag K) ∈ K133H.d4Torsion σ.toRingHom 3 →
      fieldActor (t := TwistTag.D4) σ δ v = v := by
  have hδk : ∀ x : K, σ x = x → δ x = x := fun x hx =>
    delta_fixes_trialityFixedField hn3 hδ3 hk ⟨x, hx⟩
  obtain ⟨-, ⟨e, he⟩, -, -, -, -, -, -, -⟩ :=
    triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  intro v hv
  have hvH : (v : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom := hv.1
  set x : graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    ⟨(v : ModGL TwistTag.D4.tag K), hvH⟩ with hx
  obtain ⟨p, hp⟩ := e.surjective x
  obtain ⟨a, b⟩ := p
  have hxab : (e (a, b) : ModGL TwistTag.D4.tag K) =
      trialityOuterTorus K σ a * trialityMiddleTorus K σ b := he a b
  have hve : (v : ModGL TwistTag.D4.tag K) =
      trialityOuterTorus K σ a * trialityMiddleTorus K σ b := by
    calc (v : ModGL TwistTag.D4.tag K) = (x : ModGL TwistTag.D4.tag K) := rfl
      _ = (e (a, b) : ModGL TwistTag.D4.tag K) := by rw [← hp]
      _ = _ := hxab
  have hv3 : ((v : ModGL TwistTag.D4.tag K)) ^ 3 = 1 := hv.2
  have hpair3 : (a, b) ^ 3 = 1 := by
    apply trialityTorusHom_injective_all hσ3
    rw [map_pow, map_one]
    show (trialityTorusHom σ (a, b)) ^ 3 = 1
    rw [trialityTorusHom_apply, ← hve]
    exact hv3
  have ha3 : a ^ 3 = 1 := congrArg Prod.fst hpair3
  have haK3 : (a : K) ^ 3 = 1 := congrArg Units.val ha3
  have hσa : σ (a : K) = (a : K) := by
    calc σ (a : K) = (a : K) ^ (2 ^ n) := hσ _
      _ = (a : K) ^ ((2 ^ n) % 3) :=
        pow_eq_pow_mod (a := (a : K)) (n := 3) (m := 2 ^ n) haK3
      _ = (a : K) ^ 1 := by rw [two_pow_mod_three_of_even hev]
      _ = (a : K) := pow_one _
  have hδaK : δ (a : K) = (a : K) := hδk a hσa
  have hδa : Units.map δ.toRingHom.toMonoidHom a = a := Units.ext hδaK
  have hδb : Units.map δ.toRingHom.toMonoidHom (trialityFixedUnit K σ b) =
      trialityFixedUnit K σ b := by
    apply Units.ext
    change δ ((b : K)) = (b : K)
    exact hδk (b : K) b.val.2
  have hC1 : trialityOuterTorus K σ a ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← trialityTorusHom_one_right (σ := σ) a]
    exact trialityTorusHom_mem_graphFixedRootGroup hσ3 (a, 1)
  have hC2 : trialityMiddleTorus K σ b ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← trialityTorusHom_one_left (σ := σ) b]
    exact trialityTorusHom_mem_graphFixedRootGroup hσ3 (1, b)
  have hfix1 := fieldActor_fixes_outerTorus (σ := σ) (δ := δ) hσa hδa hC1
  have hfix2 := fieldActor_fixes_middleTorus (σ := σ) (δ := δ) hδb hC2
  have hvprod : v = ⟨trialityOuterTorus K σ a, hC1⟩ *
      ⟨trialityMiddleTorus K σ b, hC2⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hve]
  rw [hvprod, map_mul, hfix1, hfix2]


section ExtraCerts


private theorem exists_t_of_even {J : Type} [Group J] [Finite J] {n : ℕ}
    (hn4 : 4 ≤ n) (hn3 : ¬ 3 ∣ n) (hev : Even n)
    (hJ : ChevalleyExceptionalModel J .trialityD4 2 n)
    {α : MulAut J} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α)
    {L : Subgroup J} (hLα : L ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J))
    {E : Subgroup J} (hEL : E ≤ L) (hEab : CFSG.Open.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {T : Subgroup J} (hT2 : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hET : E ≤ Subgroup.normalizer (T : Set J)) :
    ∃ t : J, α t = t ∧ t ≠ 1 ∧ Nat.Coprime (orderOf t) 3 ∧ t ^ (2 ^ n - 1) = 1 ∧
      ∀ e ∈ E, e * t = t * e := by
  classical
  obtain ⟨K, instField, instFinite, instCharP, σ, hK, hσ, hσ3, hn1, -, ⟨φ⟩⟩ :=
    exists_graphFixedRootGroup_of_trialityD4 hJ
  letI : Field K := instField
  letI : Finite K := instFinite
  letI : CharP K 2 := instCharP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set V := K133H.d4Torsion σ.toRingHom 3 with hV
  have hk := card_trialityFixedField hn1 hK hσ hσ3
  have hk3 : 3 ∣ Nat.card (trialityFixedField K σ.toRingHom) - 1 :=
    three_dvd_card_trialityFixedField_sub_one hev hk
  set F : Subgroup C := E.map φ.toMonoidHom with hF
  set T' : Subgroup C := T.map φ.toMonoidHom with hT'
  have hF3 : ∀ x ∈ F, x ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hEab.2 e he, map_one]
  have hF9 : Nat.card F = 9 := by
    rw [hF, Subgroup.card_map_of_injective φ.injective, hE9]
  have hTp : IsPGroup 2 T' := by
    rw [hT']
    exact hT2.map φ.toMonoidHom
  have hT1 : T' ≠ ⊥ := by
    rw [hT']
    exact fun h => hTne ((Subgroup.map_eq_bot_iff_of_injective T φ.injective).1 h)
  have hFT : F ≤ Subgroup.normalizer (T' : Set C) := by
    rw [hF, hT']
    exact (Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map φ.toMonoidHom)
  obtain ⟨g, hgV⟩ := KS167D4Model.exists_map_conj_eq_d4Torsion_three hev hn1 hK hσ hσ3
    (F := F) (T := T') hF3 hF9 hTp hT1 hFT
  let ψ : J ≃* C := φ.trans (MulAut.conj g)
  have hψE : E.map ψ.toMonoidHom = V.subgroupOf C := by
    rw [show ψ.toMonoidHom = (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom from rfl,
      ← Subgroup.map_map]
    exact hgV
  let β : MulAut C := (MulAut.congr ψ) α
  have hβ3 : β ^ 3 = 1 := by
    rw [show β = MulAut.congr ψ α from rfl, ← map_pow, hα3, map_one]
  have hβout : ¬ IsInnerAut β := by
    intro h
    exact hout ((isInnerAut_congr ψ α).1 h)
  have hβfixV : ∀ v : C, (v : ModGL TwistTag.D4.tag K) ∈ V → β v = v := by
    intro v hv
    have hvV : v ∈ V.subgroupOf C := Subgroup.mem_subgroupOf.2 hv
    rw [← hψE] at hvV
    obtain ⟨e, he, rfl⟩ := hvV
    have hαe : α e = e := (MonoidHom.mem_eqLocusM.mp (hLα (hEL he)))
    show β (ψ e) = ψ e
    have hβψ : β (ψ e) = ψ (α e) := by
      rw [show β = MulAut.congr ψ α from rfl, MulAut.congr_apply]
      simp
    rw [hβψ, hαe]
  obtain ⟨y, δ, hβy⟩ := exists_conj_mul_fieldActor hn1 hK hσ β
  have hδ1 : δ ≠ 1 := by
    intro h
    apply hβout
    refine ⟨y, ?_⟩
    rw [hβy, h, fieldActor_one, mul_one]
  have hδ3 : δ ^ 3 = 1 := by
    have hinner : IsInnerAut (fieldActor (t := TwistTag.D4) σ (δ ^ 3)) := by
      have h1 : fieldActor (t := TwistTag.D4) σ (δ ^ 3) =
          fieldActor (t := TwistTag.D4) σ δ ^ 3 :=
        map_pow (fieldActorHom (t := TwistTag.D4) σ) δ 3
      rw [h1]
      change fieldActor (t := TwistTag.D4) σ δ ^ 3 ∈ (MulAut.conj : C →* MulAut C).range
      set I := (MulAut.conj : C →* MulAut C).range with hI
      have hIn : I.Normal := ⟨fun d hd β' => by
        obtain ⟨w, rfl⟩ := hd
        exact ⟨β' w, (mul_mulAutConj_mul_inv β' w).symm⟩⟩
      have hcI : MulAut.conj y ∈ I := ⟨y, rfl⟩
      have hmk : ((MulAut.conj y * fieldActor σ δ : MulAut C) : MulAut C ⧸ I) =
          ((fieldActor (t := TwistTag.D4) σ δ : MulAut C) : MulAut C ⧸ I) := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hcI, one_mul]
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hmk, ← QuotientGroup.mk_pow,
        ← hβy, hβ3, QuotientGroup.mk_one]
    exact (isInnerAut_fieldActor_iff hn1 hK hσ).1 hinner
  have hδk : ∀ x : K, σ x = x → δ x = x := fun x hx =>
    delta_fixes_trialityFixedField (n := n) hn3 hδ3 hk ⟨x, hx⟩
  have hfixV : ∀ v : C, (v : ModGL TwistTag.D4.tag K) ∈ V → fieldActor σ δ v = v :=
    fieldActor_fixes_d4Torsion hev hn3 hσ3 hσ hδ3 hk
  have hyfixV : ∀ v : C, (v : ModGL TwistTag.D4.tag K) ∈ V → MulAut.conj y v = v := by
    intro v hv
    have h1 : MulAut.conj y = β * (fieldActor (t := TwistTag.D4) σ δ)⁻¹ := by
      rw [hβy]
      group
    have hfinv : (fieldActor (t := TwistTag.D4) σ δ)⁻¹ v = v := by
      calc (fieldActor (t := TwistTag.D4) σ δ)⁻¹ v =
          (fieldActor (t := TwistTag.D4) σ δ)⁻¹ ((fieldActor σ δ) v) := by rw [hfixV v hv]
        _ = v := (fieldActor (t := TwistTag.D4) σ δ).symm_apply_apply v
    rw [h1, MulAut.mul_apply, hfinv]
    exact hβfixV v hv
  have hyH : (y : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
    refine KS167D4Model.mem_graphFixedRootTorus_of_commute_d4Torsion_three σ hσ3 hk3 y.2 ?_
    intro v hv
    have hvc : v ∈ C := graphFixedRootTorus_le _ _ _ hv.1
    have h4 : MulAut.conj y ((⟨v, hvc⟩ : C)) = ⟨v, hvc⟩ := hyfixV ⟨v, hvc⟩ hv
    have h5 : (y : ModGL TwistTag.D4.tag K) * v * (y : ModGL TwistTag.D4.tag K)⁻¹ = v := by
      have h6 : ((y * (⟨v, hvc⟩ : C) * y⁻¹ : C) : ModGL TwistTag.D4.tag K) =
          ((⟨v, hvc⟩ : C) : ModGL TwistTag.D4.tag K) :=
        congrArg (fun w : C => (w : ModGL TwistTag.D4.tag K)) (by
          change (MulAut.conj y) (⟨v, hvc⟩ : C) = (⟨v, hvc⟩ : C)
          exact h4)
      exact h6
    calc (y : ModGL TwistTag.D4.tag K) * v =
        ((y : ModGL TwistTag.D4.tag K) * v * (y : ModGL TwistTag.D4.tag K)⁻¹) *
          (y : ModGL TwistTag.D4.tag K) := by group
      _ = v * (y : ModGL TwistTag.D4.tag K) := by rw [h5]
  obtain ⟨s, hsH, hsfield, hsne, hscop, hspow⟩ :=
    KS167D4Model.exists_fieldActor_fixed_mem_graphFixedRootTorus (n := n) (by omega) hK hσ hσ3
  have hsfixδ : fieldActor (t := TwistTag.D4) σ δ s = s := by
    have hchar : ringChar K = 2 := ringChar.eq K 2
    have hsimg : (s : ModGL TwistTag.D4.tag K) ∈ trialityFixImage σ :=
      (fieldActor_eq_self_iff σ hchar s).1 hsfield
    obtain ⟨g', -, hgs⟩ := hsimg
    apply Subtype.ext
    rw [coe_fieldActor, ← hgs]
    exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.units_map_entrywiseHom_baseChangeGL_fix
      (fixSubfield σ).subtype δ.toRingHom (fun x => hδk (x : K) x.2) g'
  have hβs : β s = s := by
    have hcomm : (y : C) * s = s * y := by
      apply Subtype.ext
      exact K133H.graphFixedRootTorus_comm σ.toRingHom hyH hsH
    rw [hβy, MulAut.mul_apply, hsfixδ, MulAut.conj_apply]
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨ψ.symm s, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun w : C => ψ.symm w) hβs
    simpa [β, MulAut.congr_apply, MulEquiv.trans_apply] using h
  · intro h
    apply hsne
    have h1 := congrArg (fun w : J => ψ w) h
    rwa [MulEquiv.apply_symm_apply, map_one] at h1
  · have hord : orderOf (ψ.symm s) = orderOf s :=
      orderOf_injective (ψ.symm : C →* J) ψ.symm.injective s
    rw [hord]
    exact hscop
  · rw [← map_pow, hspow, map_one]
  · intro e he
    have hψeV : (ψ e : ModGL TwistTag.D4.tag K) ∈ V := by
      have hmem : ψ e ∈ V.subgroupOf C := by rw [← hψE]; exact ⟨e, he, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hmem
    have hcomm : ψ e * s = s * ψ e := by
      apply Subtype.ext
      exact K133H.graphFixedRootTorus_comm σ.toRingHom hψeV.1 hsH
    have h := congrArg (fun w : C => ψ.symm w) hcomm
    simpa only [map_mul, MulEquiv.symm_apply_apply] using h


private theorem even_contradiction
    {J : Type} [Group J] [Finite J] {n : ℕ} (hn4 : 4 ≤ n) (hn3 : ¬ 3 ∣ n) (hev : Even n)
    (hJ : ChevalleyExceptionalModel J .trialityD4 2 n)
    {α : MulAut J} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α)
    {L : Subgroup J} (hLα : L ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J))
    (hLiso : Sec4.IsoLThreePi ↥L 2 n)
    (hLsn : (L.subgroupOf (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J))).IsSubnormal)
    {E : Subgroup J} (hEL : E ≤ L) (hEab : CFSG.Open.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9)
    {t : J} (hαt : α t = t) (ht1 : t ≠ 1) (hcop : Nat.Coprime (orderOf t) 3)
    (hpow : t ^ (2 ^ n - 1) = 1) (hcent : ∀ e ∈ E, e * t = t * e) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htord1 : orderOf t ≠ 1 := fun h => ht1 (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd htord1
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop.symm) hrdvd
  have hrdvd2 : r ∣ 2 ^ n - 1 :=
    hrdvd.trans (orderOf_dvd_of_pow_eq_one hpow)
  have heven2 : Even (2 ^ n) := ⟨2 ^ (n - 1), by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega⟩
  have hodd2 : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow heven2 odd_one
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hodd2.not_two_dvd_nat hrdvd2
  set N := orderOf t with hN
  set t₀ : J := t ^ (N / r) with ht₀
  have ht0ord : orderOf t₀ = r := orderOf_pow_orderOf_div (orderOf_pos t).ne' hrdvd
  have ht0ne : t₀ ≠ 1 := by
    intro h
    have h1 : r = 1 := by rw [← ht0ord, h, orderOf_one]
    exact hr.ne_one h1
  have ht0α : α t₀ = t₀ := by
    rw [ht₀, map_pow, hαt]
  have ht0cent : ∀ e ∈ E, e * t₀ = t₀ * e := by
    intro e he
    rw [ht₀]
    exact (Commute.pow_right (hcent e he) (N / r)).eq
  set C := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J) with hC
  have ht0C : t₀ ∈ C := ht0α
  have hmemconj : ∀ H : Subgroup J, ∀ x, x ∈ CFSG.conjugate H t₀ ↔
      t₀ * x * t₀⁻¹ ∈ H := by
    intro H x
    rw [conjugate, Subgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      change t₀ * ((MulAut.conj t₀⁻¹) l) * t₀⁻¹ ∈ H
      rw [MulAut.conj_apply, inv_inv]
      have e : t₀ * (t₀⁻¹ * l * t₀) * t₀⁻¹ = l := by group
      rwa [e]
    · intro hx
      refine ⟨t₀ * x * t₀⁻¹, hx, ?_⟩
      change (MulAut.conj t₀⁻¹) (t₀ * x * t₀⁻¹) = x
      rw [MulAut.conj_apply, inv_inv]
      group
  have hCnorm : ∀ x, x ∈ C ↔ t₀ * x * t₀⁻¹ ∈ C := by
    intro x
    have hx1 : x ∈ C ↔ α x = x := by
      rw [hC]
      exact MonoidHom.mem_eqLocusM
    have hx2 : t₀ * x * t₀⁻¹ ∈ C ↔ α (t₀ * x * t₀⁻¹) = t₀ * x * t₀⁻¹ := by
      rw [hC]
      exact MonoidHom.mem_eqLocusM
    rw [hx1, hx2, map_mul, map_mul, map_inv, ht0α]
    constructor
    · intro h
      rw [h]
    · intro h
      have h' : t₀⁻¹ * (t₀ * α x * t₀⁻¹) * t₀ = t₀⁻¹ * (t₀ * x * t₀⁻¹) * t₀ :=
        congrArg (fun z => t₀⁻¹ * z * t₀) h
      rwa [show t₀⁻¹ * (t₀ * α x * t₀⁻¹) * t₀ = α x by group,
        show t₀⁻¹ * (t₀ * x * t₀⁻¹) * t₀ = x by group] at h'
  have hconjC : CFSG.conjugate C t₀ = C := by
    ext x
    rw [hmemconj C x, hCnorm x]
  have hL'C : CFSG.conjugate L t₀ ≤ C := by
    have h : CFSG.conjugate L t₀ ≤ CFSG.conjugate C t₀ := Subgroup.map_mono hLα
    rwa [hconjC] at h
  have hLsn' : ((CFSG.conjugate L t₀).subgroupOf C).IsSubnormal := by
    have h := CFSG.GroupTheory.isSubnormal_subgroupOf_conjugate t₀ hLsn
    rwa [hconjC] at h
  have hinf : ((L ⊓ CFSG.conjugate L t₀).subgroupOf C).IsSubnormal := by
    have h := Subgroup.IsSubnormal.inf hLsn hLsn'
    rwa [← inf_subgroupOf] at h
  have hsubL : ((L ⊓ CFSG.conjugate L t₀).subgroupOf L).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hLα hinf
  have hEsub : E ≤ L ⊓ CFSG.conjugate L t₀ := by
    intro e he
    refine Subgroup.mem_inf.2 ⟨hEL he, ?_⟩
    rw [hmemconj L e]
    rw [show t₀ * e * t₀⁻¹ = e from ?_]
    exact hEL he
    have hc : e * t₀ = t₀ * e := ht0cent e he
    rw [← hc]
    group
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE9
    omega
  have hne : (L ⊓ CFSG.conjugate L t₀).subgroupOf L ≠ ⊥ := by
    intro hbot
    apply hEne
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    have hmem : (⟨e, hEL he⟩ : L) ∈ (L ⊓ CFSG.conjugate L t₀).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact hEsub he
    rw [hbot] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hLsimple : IsSimpleGroup ↥L := by
    rcases hLiso with ⟨-, ⟨e⟩⟩ | ⟨h2, -⟩
    · haveI : IsSimpleGroup (CFSG.PGLModel.projSL 3 (GaloisField 2 n)) :=
        CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 n) (by norm_num)
          (Or.inl (by norm_num)) (Or.inl (by norm_num))
      exact MulEquiv.isSimpleGroup e
    · exact absurd h2 (by rw [two_pow_mod_three_of_even hev]; norm_num)
  have htop : (L ⊓ CFSG.conjugate L t₀).subgroupOf L = ⊤ :=
    (Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hLsimple hsubL).resolve_left hne
  have hLle : L ≤ CFSG.conjugate L t₀ := by
    intro x hx
    have hmem : (⟨x, hx⟩ : L) ∈ (L ⊓ CFSG.conjugate L t₀).subgroupOf L := by
      rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 hmem).2
  have hcardconj : Nat.card (CFSG.conjugate L t₀) = Nat.card ↥L := by
    rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj t₀⁻¹).injective]
  have hLeq : CFSG.conjugate L t₀ = L :=
    (Subgroup.eq_of_le_of_card_ge hLle (le_of_eq hcardconj)).symm
  have ht0N : t₀ ∈ Subgroup.normalizer (L : Set J) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hiff : x ∈ L ↔ x ∈ CFSG.conjugate L t₀ := by rw [hLeq]
    exact hiff.trans (hmemconj L x)
  have h9 : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8) := by
    have hn3' : n % 3 ≠ 0 := by
      intro h
      exact hn3 (Nat.dvd_iff_mod_eq_zero.2 h)
    have h2 : n % 2 = 0 := Nat.even_iff.mp hev
    have h6 : n % 6 = 2 ∨ n % 6 = 4 := by omega
    have hpow9 : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
      conv_lhs => rw [← Nat.div_add_mod n 6]
      rw [pow_add, pow_mul, Nat.mul_mod,
        show (2 ^ 6) ^ (n / 6) % 9 = 1 by
          rw [Nat.pow_mod, show 2 ^ 6 % 9 = 1 by norm_num, one_pow]
          norm_num,
        one_mul]
      exact Nat.mod_mod _ _
    rw [hpow9]
    rcases h6 with h | h <;> rw [h] <;> norm_num
  have ht0L : t₀ ∉ L := by
    intro hmem
    have hEab' : CFSG.Open.IsElemAbelian 3 (E.subgroupOf L) :=
      CFSG.Open.IsElemAbelian.subgroupOf hEab L
    have hE9' : Nat.card (E.subgroupOf L) = 9 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv).trans hE9
    have hp3 : IsPGroup 3 (Subgroup.centralizer ((E.subgroupOf L : Subgroup L) : Set L)) :=
      kS169HessCent (X := ↥L) (n := n) (by omega) hLiso h9 (E.subgroupOf L) hEab' hE9'
    have hcentL : (⟨t₀, hmem⟩ : L) ∈
        Subgroup.centralizer ((E.subgroupOf L : Subgroup L) : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subtype.ext (ht0cent (e : J) (Subgroup.mem_subgroupOf.1 he))
    obtain ⟨m, hm⟩ := hp3 ⟨⟨t₀, hmem⟩, hcentL⟩
    have hordL : orderOf (⟨t₀, hmem⟩ : L) = r := by
      rw [← Subgroup.orderOf_coe ⟨t₀, hmem⟩, ht0ord]
    have hdiv : r ∣ 3 ^ m := by
      have hordc : orderOf (⟨⟨t₀, hmem⟩, hcentL⟩ :
          Subgroup.centralizer ((E.subgroupOf L : Subgroup L) : Set L)) = r := by
        have hcoee := Subgroup.orderOf_coe (⟨⟨t₀, hmem⟩, hcentL⟩ :
          Subgroup.centralizer ((E.subgroupOf L : Subgroup L) : Set L))
        rw [← hcoee]
        exact hordL
      rw [← hordc]
      exact orderOf_dvd_of_pow_eq_one hm
    have h3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (Nat.Prime.dvd_of_dvd_pow hr hdiv)
    exact hr3 h3
  have hinfbot : L ⊓ Subgroup.zpowers t₀ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    haveI : Fact r.Prime := ⟨hr⟩
    have hcardP : Nat.card ↥(Subgroup.zpowers t₀) = r := by rw [Nat.card_zpowers, ht0ord]
    have ht0mem : t₀ ∈ Subgroup.zpowers x := by
      have h := mem_zpowers_of_prime_card (G := ↥(Subgroup.zpowers t₀)) hcardP
        (g := (⟨x, hx.2⟩ : Subgroup.zpowers t₀)) (g' := (⟨t₀, Subgroup.mem_zpowers t₀⟩ :
          Subgroup.zpowers t₀)) (by
          intro h
          exact hx1 (Subtype.ext_iff.mp h))
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hle : Subgroup.zpowers x ≤ L := (Subgroup.zpowers_le (g := x) (H := L)).2 hx.1
    exact ht0L (hle ht0mem)
  have hNle : L ⊔ Subgroup.zpowers t₀ ≤ Subgroup.normalizer (L : Set J) :=
    sup_le Subgroup.le_normalizer
      ((Subgroup.zpowers_le (g := t₀) (H := Subgroup.normalizer (L : Set J))).2 ht0N)
  have hnormal : (L.subgroupOf (L ⊔ Subgroup.zpowers t₀)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff le_sup_left]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hNle hk) h).1 hh
  have hdisj : Disjoint
      ((L.subgroupOf (L ⊔ Subgroup.zpowers t₀) : Subgroup ↥(L ⊔ Subgroup.zpowers t₀)))
      (((Subgroup.zpowers t₀).subgroupOf (L ⊔ Subgroup.zpowers t₀) :
        Subgroup ↥(L ⊔ Subgroup.zpowers t₀))) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    obtain ⟨hxL, hxP⟩ := Subgroup.mem_inf.1 hx
    have hx' : (x : J) ∈ L ⊓ Subgroup.zpowers t₀ :=
      ⟨Subgroup.mem_subgroupOf.1 hxL, Subgroup.mem_subgroupOf.1 hxP⟩
    rw [hinfbot] at hx'
    exact Subgroup.mem_bot.1 hx'
  have hsup : (L.subgroupOf (L ⊔ Subgroup.zpowers t₀) : Subgroup ↥(L ⊔ Subgroup.zpowers t₀)) ⊔
      (Subgroup.zpowers t₀).subgroupOf (L ⊔ Subgroup.zpowers t₀) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hcompl := CFSG.isComplement'_of_disjoint_sup_eq_top_of_normal
    (L.subgroupOf (L ⊔ Subgroup.zpowers t₀))
    ((Subgroup.zpowers t₀).subgroupOf (L ⊔ Subgroup.zpowers t₀)) hdisj hsup
  have hcardjoin : Nat.card ↥(L ⊔ Subgroup.zpowers t₀) = Nat.card ↥L * r := by
    have h := Subgroup.IsComplement'.card_mul_card hcompl
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        L ≤ L ⊔ Subgroup.zpowers t₀)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        Subgroup.zpowers t₀ ≤ L ⊔ Subgroup.zpowers t₀)).toEquiv,
      Nat.card_zpowers, ht0ord] at h
    exact h.symm
  obtain ⟨K, instField, instFinite, instCharP, σ, hK, hσ, hσ3, hn1, -, ⟨φ⟩⟩ :=
    exists_graphFixedRootGroup_of_trialityD4 hJ
  letI : Field K := instField
  letI : Finite K := instFinite
  letI : CharP K 2 := instCharP
  have hcardJ : Nat.card J = ordTrialityD4 (2 ^ n) := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hn1 hK
      σ.toRingHom (fun c => hσ c)
  have hcardL : Nat.card ↥L = ordA 2 (2 ^ n) := by
    rcases hLiso with ⟨-, ⟨e⟩⟩ | ⟨h2, -⟩
    · rw [Nat.card_congr e.toEquiv, card_projSL_three_galois (by omega)]
    · exact absurd h2 (by rw [two_pow_mod_three_of_even hev]; norm_num)
  have hdvd : ordA 2 (2 ^ n) * r ∣ ordTrialityD4 (2 ^ n) := by
    rw [← hcardL, ← hcardjoin, ← hcardJ]
    have hcardtop : Nat.card ↥(⊤ : Subgroup J) = Nat.card J :=
      Nat.card_congr (Subgroup.topEquiv (G := J)).toEquiv
    have hle : L ⊔ Subgroup.zpowers t₀ ≤ (⊤ : Subgroup J) := le_top
    have h := Subgroup.card_dvd_of_le hle
    rwa [hcardtop] at h
  have hX : r ∣ 3 * (2 ^ n) ^ 9 * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) * ((2 ^ n) ^ 3 + 1) := by
    have hident := ordTrialityD4_eq_ordA_mul (n := n) (by omega) hev
    rw [hident] at hdvd
    have hpos : 0 < ordA 2 (2 ^ n) := by
      rw [← hcardL]
      exact (Finite.card_pos_iff.mpr ⟨1⟩)
    exact Nat.dvd_of_mul_dvd_mul_left hpos hdvd
  have h2n : (2 ^ n) % r = 1 := by
    have hle : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hd' : ((r : ℤ) ∣ ((2 ^ n - 1 : ℕ) : ℤ)) := by exact_mod_cast hrdvd2
    have hz : ((r : ℤ) ∣ (2 ^ n : ℤ) - 1) := by
      rwa [Nat.cast_sub hle, Nat.cast_one] at hd'
    have hz' : ((r : ℤ) ∣ (1 : ℤ) - (2 ^ n : ℤ)) := by
      rw [show (1 : ℤ) - (2 ^ n : ℤ) = -((2 ^ n : ℤ) - 1) by ring]
      exact dvd_neg.mpr hz
    have hme : (2 ^ n) ≡ 1 [MOD r] := Nat.modEq_iff_dvd.mpr hz'
    have h' : (2 ^ n) % r = 1 % r := hme
    rwa [Nat.mod_eq_of_lt hr.one_lt] at h'
  have h18 : r ∣ 18 := dvd_eighteen_of_dvd hr h2n hX
  have hdvd6 : r ∣ 2 * 9 := by norm_num; exact h18
  have h23 : r = 2 ∨ r = 3 := by
    rcases hr.dvd_mul.mp hdvd6 with h | h
    · left; exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h
    · have h3 : r ∣ 3 ^ 2 := by norm_num; exact h
      right
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
        (Nat.Prime.dvd_of_dvd_pow hr h3)
  rcases h23 with h | h
  · exact hr2 h
  · exact hr3 h


theorem ks167D4_holds : CFSG.RankThree.PartTwo.KFacts.KS167D4 := by
  intro J _ _ n hn4 hn3 hJ α hα3 hout L hLα hLiso hLsn E hEL hEab hE9 T hT2 hTα hET
  by_cases hodd : Odd n
  · exact KS167D4Model.eq_bot_of_le_normalizer_of_odd hodd hJ hEab.2 (by omega) hT2 hET
  · rw [Nat.not_odd_iff_even] at hodd
    by_contra hTne
    obtain ⟨t, hαt, ht1, hcop, hpow, hcent⟩ :=
      exists_t_of_even hn4 hn3 hodd hJ hα3 hout hLα hEL hEab hE9 hT2 hTne hET
    exact even_contradiction hn4 hn3 hodd hJ hα3 hout hLα hLiso hLsn hEL hEab hE9
      hαt ht1 hcop hpow hcent

end ExtraCerts

end Certs

end CFSG.RankThree.PartTwo.KFacts.KS167D4Proof

