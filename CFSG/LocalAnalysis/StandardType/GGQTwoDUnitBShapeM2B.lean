module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public section

namespace CFSG.StandardType.QTwo

open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

private theorem qtwoDB3_m2b_mem_range_iff_uFactor_eq_one (h : UnitaryFieldData 2 1 F0)
    (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ 2 ^ 1 = 2))
    (γ : MulAut (StatedProj (StatedSU m (2 ^ 1) F0))) :
    γ ∈ (uConjAut h (by omega : 1 ≤ m)).range ↔ uFactor h hm hq γ = 1 := by
  constructor
  · rintro ⟨A, rfl⟩
    have h1 := uFactor_apply h hm hq A (1 : F0 ≃+* F0)
    rwa [map_one, mul_one] at h1
  · intro hγ
    obtain ⟨A, φ, hAφ⟩ := exists_uConjAut_mul_uFieldAut h hm hq γ
    have hφ : φ = 1 := by
      have h1 := congrArg (uFactor h hm hq) hAφ
      rw [uFactor_apply h hm hq A φ, hγ] at h1
      exact h1.symm
    exact ⟨A, by rw [hAφ, hφ, map_one, mul_one]⟩

theorem qtwoDB3_range_normal (h : UnitaryFieldData 2 1 F0) (hm : 5 ≤ m)
    (α β : MulAut (StatedProj (StatedSU m (2 ^ 1) F0)))
    (hβ : β ∈ (uConjAut h (by omega : 1 ≤ m)).range) :
    ⁅α, β⁆ ∈ (uConjAut h (by omega : 1 ≤ m)).range := by
  have hm3 : 3 ≤ m := by omega
  have hq : ¬(m = 3 ∧ 2 ^ 1 = 2) := by omega
  have hβ' : uFactor h hm3 hq β = 1 :=
    (qtwoDB3_m2b_mem_range_iff_uFactor_eq_one h hm3 hq β).1 hβ
  rw [qtwoDB3_m2b_mem_range_iff_uFactor_eq_one h hm3 hq, map_commutatorElement, hβ',
    commutatorElement_one_right]

private theorem qtwoDB3_m2b_diag_conjTr_mul (hF0 : Nat.card F0 = 4) (c : Fin m → F0ˣ) :
    CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1)
        ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
      ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hcard : Fintype.card F0 = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF0
  have h3 : ∀ i : Fin m, (c i : F0) ^ 3 = 1 := by
    intro i
    have h := FiniteField.pow_card_sub_one_eq_one (c i : F0) (c i).ne_zero
    rw [hcard] at h
    simpa using h
  have hval : ((qTwoChartTwoThree_diag c : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (fun i => (c i : F0)) := rfl
  rw [hval, CFSG.LieType.Steinberg.conjTr_diagonal,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, show (2 : ℕ) ^ 1 = 2 from rfl]
  rw [show (c i : F0) ^ 2 * (c i : F0) = (c i : F0) ^ 3 by ring, h3 i]

private theorem qtwoDB3_m2b_diag_mem_uU (h : UnitaryFieldData 2 1 F0)
    (hF0 : Nat.card F0 = 4) (c : Fin m → F0ˣ) : qTwoChartTwoThree_diag c ∈ uU h m := by
  rw [mem_uU]
  have hbar : (h.bar : F0 → F0) =
      fun x => CFSG.LieType.BorelTits.unitaryInvolution F0 2 1 x := by
    funext x
    rw [UnitaryFieldData.bar_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hbar]
  simpa [CFSG.LieType.Universal.Unitary.conjTr] using qtwoDB3_m2b_diag_conjTr_mul hF0 c

private theorem qtwoDB3_m2b_card_comap {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (S : Subgroup H) (hS : S ≤ f.range) :
    Nat.card (S.comap f) = Nat.card f.ker * Nat.card S := by
  classical
  let f' : ↥(S.comap f) →* S :=
    { toFun := fun x => ⟨f (x : G), x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : G) (b : G)) }
  have hsurj : Function.Surjective f' := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hS y.2)
    exact ⟨⟨x, by show f x ∈ S; rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  have hker_le : f.ker ≤ S.comap f := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact S.one_mem
  have hker : f'.ker = (f.ker).subgroupOf (S.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hker_card : Nat.card f'.ker = Nat.card f.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj (f := f')
  rw [hker_card] at h
  exact h.symm

private theorem qtwoDB3_m2b_ker_le_center (h : UnitaryFieldData 2 1 F0) (hm : 3 ≤ m) :
    (uConjAut h (by omega : 1 ≤ m)).ker ≤ Subgroup.center ↥(uU h m) := by
  intro A hA
  rw [MonoidHom.mem_ker] at hA
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hm (A : uU h m)).1 hA
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, Matrix.GeneralLinearGroup.scalar_commute]

private theorem qtwoDB3_m2b_card_ker_dvd_three (h : UnitaryFieldData 2 1 F0)
    (hF0 : Nat.card F0 = 4) (hm : 3 ≤ m) :
    Nat.card (uConjAut h (by omega : 1 ≤ m)).ker ∣ 3 := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin m) : F0ˣ →* GL (Fin m) F0) := by
    intro a b hab
    apply Units.ext
    have h := congrFun (congrFun (congrArg (fun M : GL (Fin m) F0 =>
      (M : Matrix (Fin m) (Fin m) F0)) hab) ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h
  have hrange_card : Nat.card (Matrix.GeneralLinearGroup.scalar (Fin m) :
      F0ˣ →* GL (Fin m) F0).range = 3 := by
    rw [MonoidHom.range_eq_map, ← Nat.card_congr (Subgroup.equivMapOfInjective
      (⊤ : Subgroup F0ˣ) _ hscalar_inj).toEquiv, Subgroup.card_top, Nat.card_units, hF0]
  let ψ : (uConjAut h (by omega : 1 ≤ m)).ker →*
      (Matrix.GeneralLinearGroup.scalar (Fin m) : F0ˣ →* GL (Fin m) F0).range :=
    MonoidHom.codRestrict
      (((uU h m).subtype).comp (uConjAut h (by omega : 1 ≤ m)).ker.subtype) _
      (fun z => by
        have hz : uConjAut h (by omega : 1 ≤ m) (z : uU h m) = 1 := MonoidHom.mem_ker.1 z.2
        obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hm (z : uU h m)).1 hz
        exact ⟨c, hc.symm⟩)
  have hψinj : Function.Injective ψ := by
    intro z1 z2 h12
    have h12' : (z1 : GL (Fin m) F0) = (z2 : GL (Fin m) F0) := by
      have := congrArg (fun w : (Matrix.GeneralLinearGroup.scalar (Fin m) :
          F0ˣ →* GL (Fin m) F0).range => (w : GL (Fin m) F0)) h12
      simpa [ψ] using this
    apply Subtype.ext
    apply Subtype.ext
    exact h12'
  have hdvd := Subgroup.card_dvd_of_injective ψ hψinj
  rwa [hrange_card] at hdvd

private theorem qtwoDB3_m2b_coprime_two_pow_of_dvd_three (k d : ℕ) (hd : d ∣ 3) :
    Nat.Coprime (2 ^ k) d := by
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · rw [h]
    exact Nat.coprime_one_right _
  · rw [h]
    simpa using Nat.coprime_pow_primes k 1 Nat.prime_two Nat.prime_three (by norm_num)

private theorem qtwoDB3_m2b_le_of_isPGroup_two {C : Type*} [Group C] [Finite C]
    {S Z T : Subgroup C} (hS2 : IsPGroup 2 S) (hZc : Z ≤ Subgroup.center C)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) (hcompl : S.IsComplement' Z) (hT : IsPGroup 2 T) : T ≤ S := by
  obtain ⟨n₁, hk₁⟩ := isPGroup_iff_exists_pow_pow_eq_one.1 hS2
  obtain ⟨n₂, hk₂⟩ := isPGroup_iff_exists_pow_pow_eq_one.1 hT
  have hpow_of_le : ∀ {n N : ℕ}, n ≤ N → ∀ (x : C), x ^ 2 ^ n = 1 → x ^ 2 ^ N = 1 := by
    intro n N hle x hx
    rw [← Nat.add_sub_cancel' hle, pow_add, pow_mul, hx, one_pow]
  intro t ht
  obtain ⟨⟨s, z⟩, hsz, -⟩ := hcompl.existsUnique t
  have hsz' : (s : C) * (z : C) = t := hsz
  have hcomm : Commute (s : C) t := by
    rw [← hsz']
    exact (Commute.refl (s : C)).mul_right (Subgroup.mem_center_iff.1 (hZc z.2) (s : C))
  have hsN : (s : C) ^ 2 ^ max n₁ n₂ = 1 :=
    hpow_of_le (le_max_left _ _) _ (by simpa using congrArg Subtype.val (hk₁ s))
  have hzpow : (z : C) ^ 2 ^ max n₁ n₂ = 1 := by
    have hzt : (z : C) = (s : C)⁻¹ * t := by rw [← hsz']; group
    rw [hzt, (hcomm.inv_left).mul_pow, inv_pow, hsN, inv_one, one_mul]
    exact hpow_of_le (le_max_right _ _) _ (by simpa using congrArg Subtype.val (hk₂ ⟨t, ht⟩))
  have hz1 : (z : C) = 1 := by
    have hcop : Nat.Coprime (2 ^ max n₁ n₂) 3 :=
      qtwoDB3_m2b_coprime_two_pow_of_dvd_three _ _ (dvd_refl 3)
    have hdvd : orderOf (z : C) ∣ Nat.gcd (2 ^ max n₁ n₂) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzpow)
        (orderOf_dvd_iff_pow_eq_one.2 (hZ3 z z.2))
    rw [hcop.gcd_eq_one] at hdvd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
  rw [← hsz', hz1, mul_one]
  exact s.2

theorem qtwoDB3_exists_U (h : UnitaryFieldData 2 1 F0) (hF0 : Nat.card F0 = 4) (hm : 5 ≤ m)
    (Kb : Subgroup (MulAut (StatedProj (StatedSU m (2 ^ 1) F0)))) (hK2 : IsPGroup 2 Kb)
    (hK1 : Kb ≠ ⊥) (hKI : Kb ≤ (uConjAut h (by omega : 1 ≤ m)).range)
    (Dh : Subgroup (Fin m → F0ˣ))
    (hDh : ∀ c ∈ Dh, ∀ A : uU h m, (A : GL (Fin m) F0) = qTwoChartTwoThree_diag c →
      uConjAut h (by omega : 1 ≤ m) A ∈ Subgroup.normalizer (Kb : Set _)) :
    ∃ U : Subgroup (GL (Fin m) F0), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ u ∈ U, CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1)
          ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1) ∧
      ∀ c ∈ Dh, qTwoChartTwoThree_diag c ∈ Subgroup.normalizer (U : Set (GL (Fin m) F0)) := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  have hm3 : 3 ≤ m := by omega
  let ι : ↥(uU h m) →* MulAut (StatedProj (StatedSU m (2 ^ 1) F0)) :=
    uConjAut h (by omega : 1 ≤ m)
  let C : Subgroup ↥(uU h m) := Kb.comap ι
  let Z : Subgroup ↥(uU h m) := ι.ker
  have hZC : Z ≤ C := by
    intro z hz
    change ι z ∈ Kb
    rw [MonoidHom.mem_ker.1 hz]
    exact Kb.one_mem
  have hcardC : Nat.card C = Nat.card Z * Nat.card Kb := by
    simpa [C, Z] using qtwoDB3_m2b_card_comap ι Kb hKI
  have hZcenter : Z ≤ Subgroup.center ↥(uU h m) := by
    simpa [Z, ι] using qtwoDB3_m2b_ker_le_center h hm3
  have hZ_dvd : Nat.card Z ∣ 3 := by
    simpa [Z, ι] using qtwoDB3_m2b_card_ker_dvd_three h hF0 hm3
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    exact orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard Z hz).trans hZ_dvd)
  let Zc : Subgroup ↥C := Z.subgroupOf C
  have hZc_card : Nat.card Zc = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv
  have hZc_dvd : Nat.card Zc ∣ 3 := by rw [hZc_card]; exact hZ_dvd
  have hZc_center : Zc ≤ Subgroup.center ↥C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hz' : (z : ↥(uU h m)) ∈ Z := Subgroup.mem_subgroupOf.1 hz
    exact Subtype.ext ((Subgroup.mem_center_iff.1 (hZcenter hz')) (g : ↥(uU h m)))
  have hZ3c : ∀ z ∈ Zc, z ^ 3 = 1 := by
    intro z hz
    exact Subtype.ext (hZ3 (z : ↥(uU h m)) (Subgroup.mem_subgroupOf.1 hz))
  obtain ⟨k, hk⟩ := hK2.exists_card_eq
  have hkpos : 0 < k := by
    have hlt : 1 < 2 ^ k := by
      rw [← hk]
      exact (Subgroup.one_lt_card_iff_ne_bot Kb).2 hK1
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0] at hlt
    simp at hlt
  have hdvd : 2 ^ k ∣ Nat.card ↥C := by
    rw [hcardC, hk]
    exact dvd_mul_left _ _
  obtain ⟨S₁, hS₁card⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have hS₁2 : IsPGroup 2 S₁ := IsPGroup.of_card hS₁card
  have hS₁ne : S₁ ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot S₁).1
    (by rw [hS₁card]; exact Nat.one_lt_pow hkpos.ne' (by norm_num))
  have hcop : Nat.Coprime (Nat.card S₁) (Nat.card Zc) := by
    rw [hS₁card]
    exact qtwoDB3_m2b_coprime_two_pow_of_dvd_three k _ hZc_dvd
  have hcompl : S₁.IsComplement' Zc := by
    refine Subgroup.isComplement'_of_coprime ?_ hcop
    rw [hS₁card, hZc_card, hcardC, hk]
    exact Nat.mul_comm _ _
  let S : Subgroup ↥(uU h m) := S₁.map C.subtype
  have hS2 : IsPGroup 2 S := by simpa [S] using hS₁2.map C.subtype
  have hScard : Nat.card S = 2 ^ k := by
    have h1 : Nat.card S = Nat.card S₁ :=
      (Nat.card_congr (Subgroup.equivMapOfInjective S₁ C.subtype
        Subtype.coe_injective).toEquiv).symm
    rw [h1, hS₁card]
  let U : Subgroup (GL (Fin m) F0) := S.map (uU h m).subtype
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have hSbot : S = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective S (f := (uU h m).subtype)
        Subtype.coe_injective).1 (by simpa [U] using hbot)
    exact hS₁ne ((Subgroup.map_eq_bot_iff_of_injective S₁ (f := C.subtype)
      Subtype.coe_injective).1 (by simpa [S] using hSbot))
  · exact hS2.map (uU h m).subtype
  · intro u hu
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 hu
    have hbar : (h.bar : F0 → F0) =
        fun x => CFSG.LieType.BorelTits.unitaryInvolution F0 2 1 x := by
      funext x
      rw [UnitaryFieldData.bar_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]
    have hmem : (((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0).map h.bar)ᵀ *
        ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 := (mem_uU h).1 y.2
    have hmem' : CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F0 2 1)
        ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        ((y : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 := by
      simpa [CFSG.LieType.Universal.Unitary.conjTr, hbar] using hmem
    have hyu' : (y : GL (Fin m) F0) = u := hyu
    rw [← hyu']
    exact hmem'
  · intro c hc
    have hAd_mem : qTwoChartTwoThree_diag c ∈ uU h m := qtwoDB3_m2b_diag_mem_uU h hF0 c
    let A : ↥(uU h m) := ⟨qTwoChartTwoThree_diag c, hAd_mem⟩
    have hA_normKb : ι A ∈ Subgroup.normalizer (Kb : Set _) := by
      simpa [ι, A] using hDh c hc A (by rfl)
    have hnormC : ∀ B : ↥(uU h m), ι B ∈ Subgroup.normalizer (Kb : Set _) →
        B ∈ Subgroup.normalizer (C : Set ↥(uU h m)) := by
      intro B hB
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_normalizer_iff] at hB
      constructor
      · intro hx
        change ι (B * x * B⁻¹) ∈ Kb
        rw [map_mul, map_mul, map_inv]
        exact (hB (ι x)).1 hx
      · intro hx
        have hBinv : ι B⁻¹ ∈ Subgroup.normalizer (Kb : Set _) := by
          rw [map_inv]
          exact Subgroup.inv_mem _ hB
        rw [Subgroup.mem_normalizer_iff] at hBinv
        have hx' := (hBinv (ι (B * x * B⁻¹))).1 hx
        have heq : ι B⁻¹ * ι (B * x * B⁻¹) * (ι B⁻¹)⁻¹ = ι x := by
          rw [map_mul, map_mul, map_inv]
          group
        change ι x ∈ Kb
        rwa [← heq]
    have hAnormC : A ∈ Subgroup.normalizer (C : Set ↥(uU h m)) := hnormC A hA_normKb
    have hAinv_normKb : ι A⁻¹ ∈ Subgroup.normalizer (Kb : Set _) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hA_normKb
    have hAinvnormC : A⁻¹ ∈ Subgroup.normalizer (C : Set ↥(uU h m)) :=
      hnormC A⁻¹ hAinv_normKb
    have hpowS₁ : ∀ b : ↥C, b ∈ S₁ → (b : ↥(uU h m)) ^ 2 ^ k = 1 := by
      intro b hb
      have h1 : orderOf (b : ↥(uU h m)) ∣ 2 ^ k := by
        rw [Subgroup.orderOf_coe, ← hS₁card]
        exact Subgroup.orderOf_dvd_natCard S₁ hb
      exact orderOf_dvd_iff_pow_eq_one.1 h1
    have hApres : ∀ b : ↥C, b ∈ S₁ →
        (⟨A * (b : ↥(uU h m)) * A⁻¹,
          (Subgroup.mem_normalizer_iff.1 hAnormC (b : ↥(uU h m))).1 b.2⟩ : ↥C) ∈ S₁ := by
      intro b hb
      let b' : ↥C := ⟨A * (b : ↥(uU h m)) * A⁻¹,
        (Subgroup.mem_normalizer_iff.1 hAnormC (b : ↥(uU h m))).1 b.2⟩
      have hb'2 : IsPGroup 2 (Subgroup.zpowers b') := by
        have hpow : b' ^ 2 ^ k = 1 := by
          apply Subtype.ext
          change (A * (b : ↥(uU h m)) * A⁻¹) ^ 2 ^ k = 1
          rw [conj_pow, hpowS₁ b hb]
          group
        exact IsPGroup.of_card_dvd_pow (p := 2) (n := k)
          (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)
      exact qtwoDB3_m2b_le_of_isPGroup_two hS₁2 hZc_center hZ3c hcompl hb'2
        (Subgroup.mem_zpowers b')
    have hApres_inv : ∀ b : ↥C, b ∈ S₁ →
        (⟨A⁻¹ * (b : ↥(uU h m)) * A,
          (Subgroup.mem_normalizer_iff.1 hAinvnormC (b : ↥(uU h m))).1 b.2⟩ : ↥C) ∈ S₁ := by
      intro b hb
      let b' : ↥C := ⟨A⁻¹ * (b : ↥(uU h m)) * A,
        (Subgroup.mem_normalizer_iff.1 hAinvnormC (b : ↥(uU h m))).1 b.2⟩
      have hb'2 : IsPGroup 2 (Subgroup.zpowers b') := by
        have hpow : b' ^ 2 ^ k = 1 := by
          apply Subtype.ext
          change (A⁻¹ * (b : ↥(uU h m)) * A) ^ 2 ^ k = 1
          have hc : A⁻¹ * (b : ↥(uU h m)) * A =
              A⁻¹ * (b : ↥(uU h m)) * (A⁻¹)⁻¹ := by group
          rw [hc, conj_pow, hpowS₁ b hb]
          group
        exact IsPGroup.of_card_dvd_pow (p := 2) (n := k)
          (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)
      exact qtwoDB3_m2b_le_of_isPGroup_two hS₁2 hZc_center hZ3c hcompl hb'2
        (Subgroup.mem_zpowers b')
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 hu
      obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 hy
      let b' : ↥C := ⟨A * (b : ↥(uU h m)) * A⁻¹,
        (Subgroup.mem_normalizer_iff.1 hAnormC (b : ↥(uU h m))).1 b.2⟩
      have hb'S : b' ∈ S₁ := hApres b hb
      have hb'U : ((b' : ↥C) : GL (Fin m) F0) ∈ U :=
        Subgroup.mem_map.2 ⟨C.subtype b', Subgroup.mem_map.2 ⟨b', hb'S, rfl⟩, rfl⟩
      have heq : qTwoChartTwoThree_diag c * u * (qTwoChartTwoThree_diag c)⁻¹ =
          ((b' : ↥C) : GL (Fin m) F0) := by
        rw [← hyu, ← hby]
        rfl
      rwa [heq]
    · intro hu
      obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 hu
      obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 hy
      let b' : ↥C := ⟨A⁻¹ * (b : ↥(uU h m)) * A,
        (Subgroup.mem_normalizer_iff.1 hAinvnormC (b : ↥(uU h m))).1 b.2⟩
      have hb'S : b' ∈ S₁ := hApres_inv b hb
      have hb'U : ((b' : ↥C) : GL (Fin m) F0) ∈ U :=
        Subgroup.mem_map.2 ⟨C.subtype b', Subgroup.mem_map.2 ⟨b', hb'S, rfl⟩, rfl⟩
      have heq : u = ((b' : ↥C) : GL (Fin m) F0) := by
        have h1 : u = (qTwoChartTwoThree_diag c)⁻¹ *
            (qTwoChartTwoThree_diag c * u * (qTwoChartTwoThree_diag c)⁻¹) *
            qTwoChartTwoThree_diag c := by group
        rw [h1, ← hyu, ← hby]
        rfl
      rwa [heq]

end CFSG.StandardType.QTwo

end
