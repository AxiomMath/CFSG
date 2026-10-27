module

public import CFSG.RankThree.PartOne.S11c.HNProps
public import CFSG.RankThree.PartOne.S11c.HSPairCentralize
public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.Sporadic.HNSchreier.FullAut

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier IsSporadic)
open scoped Matrix

section SL2

theorem sl2_data {T : Type*} [Group T] (Y : Subgroup T)
    (φ : Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    ∃ t y : T, t ∈ Y ∧ y ∈ Y ∧ orderOf t = 2 ∧ orderOf y = 5 ∧ (∀ z ∈ Y, z * t = t * z) ∧
      ∀ z ∈ Y, (∀ z' ∈ Y, z * z' = z' * z) → z ^ 2 = 1 := by
  classical
  let tM : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![-1, 0; 0, -1], by rw [Matrix.det_fin_two_of]; decide⟩
  let yM : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩
  have htM2 : tM ^ 2 = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_one, tM]
    decide +kernel
  have htM1 : tM ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) h
    simp [tM] at this
    revert this
    decide
  have hyM5 : yM ^ 5 = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_one, yM]
    decide +kernel
  have hyM1 : yM ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1) h
    simp [yM] at this
  have htcen : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), g * tM = tM * g := by
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    show (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) * !![-1, 0; 0, -1] =
      !![-1, 0; 0, -1] * (g : Matrix (Fin 2) (Fin 2) (ZMod 5))
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hcenter : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5),
      (∀ g', g * g' = g' * g) → g ^ 2 = 1 := by
    intro g hg
    have hmem : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
      Subgroup.mem_center_iff.2 fun z => (hg z).symm
    obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrg, Matrix.SpecialLinearGroup.coe_one]
    simp only [Fintype.card_fin] at hr
    rw [← map_pow, hr]
    simp
  refine ⟨(φ.symm tM : T), (φ.symm yM : T), (φ.symm tM).2, (φ.symm yM).2, ?_, ?_, ?_, ?_⟩
  · have h1 : orderOf (φ.symm tM) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime htM2 htM1
    rw [← Subgroup.orderOf_coe] at h1
    exact h1
  · have h1 : orderOf (φ.symm yM) = 5 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hyM5 hyM1
    rw [← Subgroup.orderOf_coe] at h1
    exact h1
  · intro z hz
    have := htcen (φ ⟨z, hz⟩)
    have h2 := congrArg (fun g => (φ.symm g : T)) this
    simpa using h2
  · intro z hz hzc
    have h1 : (φ ⟨z, hz⟩) ^ 2 = 1 := hcenter _ fun g' => by
      have := hzc (φ.symm g' : T) (φ.symm g').2
      have h2 : (⟨z, hz⟩ : Y) * φ.symm g' = φ.symm g' * ⟨z, hz⟩ := Subtype.ext this
      have h3 := congrArg φ h2
      simpa using h3
    have h4 : (⟨z, hz⟩ : Y) ^ 2 = 1 := by
      apply φ.injective
      rw [map_pow, h1, map_one]
    exact congrArg Subtype.val h4

end SL2

section Group

theorem commutator_ne_involution {G : Type*} [Group G] (w r t : G) (hw : w ^ 5 = 1)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htw : t * w = w * t) :
    w * r * w⁻¹ * r⁻¹ ≠ t := by
  intro h
  have h1 : w * r * w⁻¹ = t * r := by
    calc w * r * w⁻¹ = (w * r * w⁻¹ * r⁻¹) * r := by group
      _ = t * r := by rw [h]
  have hit : ∀ k : ℕ, w ^ k * r * (w ^ k)⁻¹ = t ^ k * r := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : w ^ (k + 1) * r * (w ^ (k + 1))⁻¹ = w * (w ^ k * r * (w ^ k)⁻¹) * w⁻¹ := by
        group
      rw [e1, ih]
      have hcomm : w * t ^ k = t ^ k * w :=
        (Commute.pow_right (show Commute w t from htw.symm) k).eq
      calc w * (t ^ k * r) * w⁻¹ = (w * t ^ k) * r * w⁻¹ := by group
        _ = (t ^ k * w) * r * w⁻¹ := by rw [hcomm]
        _ = t ^ k * (w * r * w⁻¹) := by group
        _ = t ^ k * (t * r) := by rw [h1]
        _ = t ^ (k + 1) * r := by rw [pow_succ]; group
  have h5 := hit 5
  rw [hw, inv_one, one_mul, mul_one] at h5
  have h6 : t ^ 5 = 1 := by
    have : t ^ 5 * r = 1 * r := by rw [one_mul]; exact h5.symm
    exact mul_right_cancel this
  have h7 : t ^ 5 = t := by
    calc t ^ 5 = (t ^ 2) ^ 2 * t := by group
      _ = t := by rw [ht2]; simp
  exact ht1 (by rw [← h7]; exact h6)

theorem independent_of_subgroup {G : Type*} [Group G] (Y : Subgroup G) (w y t : G)
    (hw5 : orderOf w = 5) (hy5 : orderOf y = 5) (ht2 : orderOf t = 2) (htY : t ∈ Y)
    (hyY : y ∈ Y) (hwY : ∀ i : ℕ, w ^ i ∈ Y → 5 ∣ i) :
    ∀ i j : ℕ, (w ^ i * y ^ j = 1 ∨ w ^ i * y ^ j = t) → 5 ∣ i ∧ 5 ∣ j := by
  intro i j h
  have hw5' : w ^ 5 = 1 := by rw [← hw5]; exact pow_orderOf_eq_one w
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hwi : w ^ i ∈ Y := by
    rcases h with h | h
    · have : w ^ i = (y ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact Y.inv_mem (Y.pow_mem hyY j)
    · have : w ^ i = t * (y ^ j)⁻¹ := by rw [← h]; group
      rw [this]
      exact Y.mul_mem htY (Y.inv_mem (Y.pow_mem hyY j))
  have hi : 5 ∣ i := hwY i hwi
  have hwi1 : w ^ i = 1 := by
    obtain ⟨m, rfl⟩ := hi
    rw [pow_mul, hw5', one_pow]
  rw [hwi1, one_mul] at h
  refine ⟨hi, ?_⟩
  rcases h with h | h
  · have := orderOf_dvd_of_pow_eq_one h
    rwa [hy5] at this
  · exfalso
    have h2 : t ^ 5 = 1 := by
      rw [← h, ← pow_mul, mul_comm, pow_mul, hy5', one_pow]
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [ht2] at h3
    omega

end Group

section Main

@[expose] def HNInvolutionTransport : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    IsSporadic T .HN → ∀ (β : MulAut T), orderOf β = 5 → ∀ K : Subgroup T,
      (∀ k ∈ K, β k = k) → StatedClassicalModel K .PSU 3 5 1 → ∀ t ∈ K, orderOf t = 2 →
        ∃ q : ↥(Subgroup.centralizer ({t} : Set T)) →* MulAut (Carrier .HS),
          ∀ x : ↥(Subgroup.centralizer ({t} : Set T)), q x = 1 → (x : T) = 1 ∨ (x : T) = t

theorem hnPrescribedBlockNormalizedTwo_of_transport
    (hH4 : HNInvolutionTransport) : HNPrescribedBlockNormalizedTwo := by
  classical
  intro T _ _ hsimple hnab hHN β hβ K hKfix hKmod Y hYK hYsl U hU2 hUβ hUY
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : IsSimpleGroup T := hsimple
  obtain ⟨e⟩ := hHN
  have hOut : ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) := by
    have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Carrier .HN)) = 2 :=
      CFSG.Sporadic.HNSchreier.card_outer_HN
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      h2]
    norm_num
  obtain ⟨w, hwβ⟩ := CFSG.RankThree.PartOne.exists_inner_of_pow_eq_one_of_not_dvd_card_outer
    Nat.prime_five hOut β (by rw [← hβ]; exact pow_orderOf_eq_one β)
  have hcen : Subgroup.center T = ⊥ := CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab
  have hinj := CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot hcen
  have hw5 : orderOf w = 5 := by
    have h1 := orderOf_injective _ hinj w
    rw [hwβ] at h1
    rw [← h1]
    exact hβ
  have hw5' : w ^ 5 = 1 := by rw [← hw5]; exact pow_orderOf_eq_one w
  have hwK : ∀ k ∈ K, w * k * w⁻¹ = k := fun k hk => by
    have h1 := hKfix k hk
    rw [← hwβ, MulAut.conj_apply] at h1
    exact h1
  obtain ⟨φ⟩ := hYsl
  obtain ⟨t, y, htY, hyY, ht2, hy5, htcen, hYcen⟩ := sl2_data Y φ
  have htK : t ∈ K := hYK htY
  have hyK : y ∈ K := hYK hyY
  have hwt : w * t = t * w := mul_inv_eq_iff_eq_mul.1 (hwK t htK)
  have hwy : w * y = y * w := mul_inv_eq_iff_eq_mul.1 (hwK y hyK)
  have hyt : y * t = t * y := htcen y hyY
  have hwY : ∀ i : ℕ, w ^ i ∈ Y → 5 ∣ i := by
    intro i hi
    by_contra h5
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm (by norm_num : 1 < 5)
    have hwY' : w ∈ Y := by
      have h1 : (w ^ i) ^ m ∈ Y := Y.pow_mem hi m
      rw [← pow_mul, pow_eq_pow_mod _ hw5', hm, pow_one] at h1
      exact h1
    have h2 := hYcen w hwY' fun z' hz' => mul_inv_eq_iff_eq_mul.1 (hwK z' (hYK hz'))
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hw5] at h3
    omega
  have hind' := independent_of_subgroup Y w y t hw5 hy5 ht2 htY hyY hwY
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  obtain ⟨q, hq⟩ := hH4 T hsimple hnab ⟨e⟩ β hβ K hKfix hKmod t htK ht2
  let C : Subgroup T := Subgroup.centralizer ({t} : Set T)
  have hwC : w ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hwt
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hyt
  let wC : C := ⟨w, hwC⟩
  let yC : C := ⟨y, hyC⟩
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hwyC : wC * yC = yC * wC := Subtype.ext hwy
  have hwC5 : wC ^ 5 = 1 := Subtype.ext hw5'
  have hyC5 : yC ^ 5 = 1 := Subtype.ext hy5'
  have hab : q wC * q yC = q yC * q wC := by rw [← map_mul, ← map_mul, hwyC]
  have ha : (q wC) ^ 5 = 1 := by rw [← map_pow, hwC5, map_one]
  have hb : (q yC) ^ 5 = 1 := by rw [← map_pow, hyC5, map_one]
  have hind : ∀ i j : ℕ, (q wC) ^ i * (q yC) ^ j = 1 → 5 ∣ i ∧ 5 ∣ j := by
    intro i j h
    have h1 : q (wC ^ i * yC ^ j) = 1 := by rw [map_mul, map_pow, map_pow]; exact h
    apply hind' i j
    have h2 := hq _ h1
    simpa [wC, yC] using h2
  let S : Subgroup (MulAut (Carrier .HS)) := (U.subgroupOf C).map q
  have hUC : IsPGroup 2 (U.subgroupOf C) := hU2.comap_subtype
  have hS2 : IsPGroup 2 S := hUC.map q
  have hSa : ∀ s ∈ S, q wC * s * (q wC)⁻¹ ∈ S := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨wC * c * wC⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hc' : c ∈ U.subgroupOf C := hc
    have h1 := hUβ _ (Subgroup.mem_subgroupOf.1 hc')
    rw [← hwβ, MulAut.conj_apply] at h1
    exact Subgroup.mem_subgroupOf.2 h1
  have hSb : ∀ s ∈ S, q yC * s * (q yC)⁻¹ ∈ S := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨yC * c * yC⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hc' : c ∈ U.subgroupOf C := hc
    exact Subgroup.mem_subgroupOf.2 (hUY y hyY _ (Subgroup.mem_subgroupOf.1 hc'))
  have hcen' := hs_pair_centralizes (q wC) (q yC) hab ha hb hind S hS2 hSa hSb
  have hfixC : ∀ r ∈ U, r * t = t * r → w * r * w⁻¹ = r := by
    intro r hr hrt
    have hrC : r ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hrt
    let rC : C := ⟨r, hrC⟩
    have hrS : q rC ∈ S := ⟨rC, Subgroup.mem_subgroupOf.2 hr, rfl⟩
    have h1 := hcen' _ hrS
    have h2 : q (wC * rC * wC⁻¹ * rC⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc q wC * q rC * (q wC)⁻¹ * (q rC)⁻¹ = (q wC * q rC) * (q wC)⁻¹ * (q rC)⁻¹ := by group
        _ = (q rC * q wC) * (q wC)⁻¹ * (q rC)⁻¹ := by rw [h1]
        _ = 1 := by group
    have h3 := hq _ h2
    have h4 : w * r * w⁻¹ * r⁻¹ = 1 ∨ w * r * w⁻¹ * r⁻¹ = t := by simpa [wC, rC] using h3
    rcases h4 with h4 | h4
    · exact mul_inv_eq_one.1 (by simpa [mul_assoc] using h4)
    · exact absurd h4 (commutator_ne_involution w r t hw5' ht2' ht1 hwt.symm)
  have hw1 : ∀ n ∈ U, w * n * w⁻¹ ∈ U := fun n hn => by
    have h1 := hUβ n hn
    rwa [← hwβ, MulAut.conj_apply] at h1
  have hwN : w ∈ Subgroup.normalizer (U : Set T) :=
    mem_normalizer_of_conj_mem hw1 (inv_conj_mem_of_pow_five hw5' hw1)
  have htN : t ∈ Subgroup.normalizer (U : Set T) :=
    mem_normalizer_of_conj_mem (hUY t htY) fun n hn => by
      have h1 := hUY t⁻¹ (Y.inv_mem htY) n hn
      simpa using h1
  let A : Subgroup T := Subgroup.zpowers w
  let B : Subgroup T := Subgroup.zpowers t
  have hAN : A ≤ Subgroup.normalizer (U : Set T) := (Subgroup.zpowers_le).2 hwN
  have hBN : B ≤ Subgroup.normalizer (U : Set T) := (Subgroup.zpowers_le).2 htN
  let αh : A →* MulAut U := (U.normalizerMonoidHom).comp (Subgroup.inclusion hAN)
  let βh : B →* MulAut U := (U.normalizerMonoidHom).comp (Subgroup.inclusion hBN)
  have hαapp : ∀ (a : A) (u : U), ((αh a u : U) : T) = (a : T) * u * (a : T)⁻¹ := fun a u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U ⟨(a : T), hAN a.2⟩ u
  have hβapp : ∀ (b : B) (u : U), ((βh b u : U) : T) = (b : T) * u * (b : T)⁻¹ := fun b u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U ⟨(b : T), hBN b.2⟩ u
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : ¬ 2 ∣ Nat.card A := by
    have : Nat.card A = 5 := by rw [Nat.card_zpowers]; exact hw5
    rw [this]
    norm_num
  have hB2 : IsPGroup 2 B :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hcomm : ∀ a b, αh a * βh b = βh b * αh a := by
    intro a b
    ext u
    show ((αh a (βh b u) : U) : T) = ((βh b (αh a u) : U) : T)
    rw [hαapp, hβapp, hβapp, hαapp]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    have hab : (a : T) * (b : T) = (b : T) * (a : T) := by
      rw [← hm, ← hn]
      exact (Commute.zpow_zpow (show Commute w t from hwt) m n).eq
    calc (a : T) * ((b : T) * u * (b : T)⁻¹) * (a : T)⁻¹ =
          ((a : T) * b) * u * ((a : T) * b)⁻¹ := by group
      _ = ((b : T) * a) * u * ((b : T) * a)⁻¹ := by rw [hab]
      _ = (b : T) * ((a : T) * u * (a : T)⁻¹) * (b : T)⁻¹ := by group
  have hfix : ∀ a r, (∀ b, βh b r = r) → αh a r = r := by
    intro a r hr
    have h1 := hr ⟨t, Subgroup.mem_zpowers t⟩
    have h2 : t * (r : T) * t⁻¹ = r := by
      have := congrArg Subtype.val h1
      rwa [hβapp] at this
    have hrt : (r : T) * t = t * r := (mul_inv_eq_iff_eq_mul.1 h2).symm
    have hwr : w * (r : T) * w⁻¹ = r := hfixC r r.2 hrt
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    apply Subtype.ext
    rw [hαapp, ← hm]
    have hcw : Commute (w ^ m) (r : T) :=
      (show Commute w (r : T) from mul_inv_eq_iff_eq_mul.1 hwr).zpow_left m
    exact mul_inv_eq_iff_eq_mul.2 hcw.eq
  have key := CFSG.GroupTheory.thompson_A_times_B (p := 2) hU2 hA hB2 αh βh hcomm hfix
    ⟨w, Subgroup.mem_zpowers w⟩
  intro u hu
  have h1 := congrArg (fun m : MulAut U => ((m ⟨u, hu⟩ : U) : T)) key
  have h2 : w * u * w⁻¹ = u := by
    have h3 : ((αh ⟨w, Subgroup.mem_zpowers w⟩ ⟨u, hu⟩ : U) : T) = u := by
      simpa using h1
    rwa [hαapp] at h3
  rw [← hwβ, MulAut.conj_apply]
  exact h2

end Main

end CFSG.RankThree.PartOne.HNRed
