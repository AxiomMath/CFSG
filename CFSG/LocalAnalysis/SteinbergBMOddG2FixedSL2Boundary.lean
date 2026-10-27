module

public import CFSG.LieType.AlgebraicGroups.OddG2F4E8InvolutionCases
import CFSG.LocalAnalysis.SteinbergBMOddG2InnerFixedNoSimple
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBM

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog (map_eq_one_of_commutator_eq_top)
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (ReeTag)

theorem two_pow_mul_ne_G2_order {n r : ℕ} (hn : 1 ≤ n) (hr : Odd r) (hr3 : 3 ≤ r) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ r ^ 6 * (r ^ 6 - 1) * (r ^ 2 - 1) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : 9 ≤ r ^ 2 := by nlinarith
  have hR6 : 729 ≤ r ^ 6 :=
    calc 729 = 3 ^ 6 := by norm_num
      _ ≤ r ^ 6 := Nat.pow_le_pow_left hr3 6
  have hq4 : 4 ≤ (2 ^ n) ^ 2 := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    nlinarith
  have hq2 : Odd ((2 ^ n) ^ 2 - 1) := by
    have hev : Even ((2 ^ n) ^ 2) :=
      Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  have hfac : r ^ 6 - 1 = (r ^ 2 - 1) * (r ^ 4 + r ^ 2 + 1) := by
    have h1 : 1 ≤ r ^ 2 := by omega
    have h6 : 1 ≤ r ^ 6 := by omega
    zify [h1, h6]
    ring
  have hodd4 : Odd (r ^ 4 + r ^ 2 + 1) := (Odd.add_odd hr.pow hr.pow).add_one
  have hA : r ^ 2 - 1 ≠ 0 := by omega
  have hB : r ^ 4 + r ^ 2 + 1 ≠ 0 := by positivity
  have hC : r ^ 6 ≠ 0 := by positivity
  have hD : (2 ^ n) ^ 2 - 1 ≠ 0 := by omega
  have vL : padicValNat 2 (2 ^ n * ((2 ^ n) ^ 2 - 1)) = n := by
    rw [padicValNat.mul (by positivity) hD, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hq2.not_two_dvd_nat, add_zero]
  have vR : padicValNat 2 (r ^ 6 * (r ^ 6 - 1) * (r ^ 2 - 1)) =
      2 * padicValNat 2 (r ^ 2 - 1) := by
    rw [hfac, padicValNat.mul (mul_ne_zero hC (mul_ne_zero hA hB)) hA,
      padicValNat.mul hC (mul_ne_zero hA hB), padicValNat.mul hA hB,
      padicValNat.eq_zero_of_not_dvd hr.pow.not_two_dvd_nat,
      padicValNat.eq_zero_of_not_dvd hodd4.not_two_dvd_nat]
    ring
  have hv : n = 2 * padicValNat 2 (r ^ 2 - 1) := by rw [← vL, h, vR]
  have hle : 2 ^ padicValNat 2 (r ^ 2 - 1) ≤ r ^ 2 - 1 :=
    Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have hq : 2 ^ n ≤ (r ^ 2 - 1) ^ 2 := by
    rw [hv, pow_mul']
    exact Nat.pow_le_pow_left hle 2
  have hL : 2 ^ n * ((2 ^ n) ^ 2 - 1) < r ^ 12 :=
    calc 2 ^ n * ((2 ^ n) ^ 2 - 1) ≤ 2 ^ n * (2 ^ n) ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (2 ^ n) ^ 3 := by ring
      _ ≤ ((r ^ 2 - 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hq 3
      _ < ((r ^ 2) ^ 2) ^ 3 :=
        Nat.pow_lt_pow_left (Nat.pow_lt_pow_left (by omega) (by norm_num)) (by norm_num)
      _ = r ^ 12 := by ring
  have hR : r ^ 12 ≤ r ^ 6 * (r ^ 6 - 1) * (r ^ 2 - 1) := by
    have h8 : (r ^ 6 - 1) * 8 ≤ (r ^ 6 - 1) * (r ^ 2 - 1) := Nat.mul_le_mul_left _ (by omega)
    have h7 : r ^ 6 ≤ (r ^ 6 - 1) * 8 := by omega
    calc r ^ 12 = r ^ 6 * r ^ 6 := by ring
      _ ≤ r ^ 6 * ((r ^ 6 - 1) * (r ^ 2 - 1)) := Nat.mul_le_mul_left _ (h7.trans h8)
      _ = r ^ 6 * (r ^ 6 - 1) * (r ^ 2 - 1) := by ring
  exact lt_irrefl _ (lt_of_lt_of_le (h ▸ hL) hR)

theorem two_pow_mul_ne_ree_order {n a : ℕ} (hn : 1 ≤ n) (ha : 1 ≤ a) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠
      (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) * ((3 ^ (2 * a + 1)) ^ 3 + 1) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := 3 ^ (2 * a + 1) with hs
  have hs8 : s % 8 = 3 := by
    rw [hs, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hs27 : 27 ≤ s :=
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs3 : s ^ 3 % 8 = 3 := by
    rw [Nat.pow_mod, hs8]
  have hsodd : Odd (s ^ 3) := Nat.odd_iff.mpr (by omega)
  have hq4 : 4 ≤ (2 ^ n) ^ 2 := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    nlinarith
  have hq2 : Odd ((2 ^ n) ^ 2 - 1) := by
    have hev : Even ((2 ^ n) ^ 2) :=
      Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  have hu : s - 1 = 2 * ((s - 1) / 2) := by omega
  have huo : Odd ((s - 1) / 2) := Nat.odd_iff.mpr (by omega)
  have hw : s ^ 3 + 1 = 4 * ((s ^ 3 + 1) / 4) := by omega
  have hwo : Odd ((s ^ 3 + 1) / 4) := Nat.odd_iff.mpr (by omega)
  have hD : (2 ^ n) ^ 2 - 1 ≠ 0 := by omega
  have hs0 : s ^ 3 ≠ 0 := by positivity
  have hu0 : (s - 1) / 2 ≠ 0 := huo.pos.ne'
  have hw0 : (s ^ 3 + 1) / 4 ≠ 0 := hwo.pos.ne'
  have vL : padicValNat 2 (2 ^ n * ((2 ^ n) ^ 2 - 1)) = n := by
    rw [padicValNat.mul (by positivity) hD, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hq2.not_two_dvd_nat, add_zero]
  have vR : padicValNat 2 (s ^ 3 * (2 * ((s - 1) / 2)) * (4 * ((s ^ 3 + 1) / 4))) = 3 := by
    rw [padicValNat.mul (mul_ne_zero hs0 (mul_ne_zero two_ne_zero hu0))
        (mul_ne_zero four_ne_zero hw0),
      padicValNat.mul hs0 (mul_ne_zero two_ne_zero hu0), padicValNat.mul two_ne_zero hu0,
      padicValNat.mul four_ne_zero hw0, padicValNat.eq_zero_of_not_dvd hsodd.not_two_dvd_nat,
      padicValNat.eq_zero_of_not_dvd huo.not_two_dvd_nat,
      padicValNat.eq_zero_of_not_dvd hwo.not_two_dvd_nat, padicValNat.self (by norm_num),
      show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have vR' : padicValNat 2 (s ^ 3 * (s - 1) * (s ^ 3 + 1)) = 3 := by
    rw [hu, hw]
    exact vR
  have hv : n = 3 := by
    have h1 := vL
    rw [h, vR'] at h1
    exact h1.symm
  subst hv
  have hRHS : s ^ 3 ≤ s ^ 3 * (s - 1) * (s ^ 3 + 1) := by
    have h1 : 1 ≤ (s - 1) * (s ^ 3 + 1) :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by positivity))
    calc s ^ 3 = s ^ 3 * 1 := (mul_one _).symm
      _ ≤ s ^ 3 * ((s - 1) * (s ^ 3 + 1)) := Nat.mul_le_mul_left _ h1
      _ = s ^ 3 * (s - 1) * (s ^ 3 + 1) := by ring
  have hs3' : 27 ^ 3 ≤ s ^ 3 := Nat.pow_le_pow_left hs27 3
  have h504 : (2 : ℕ) ^ 3 * ((2 ^ 3) ^ 2 - 1) = 504 := by norm_num
  rw [h504] at h
  omega

theorem eq_three_of_two_pow_mul_eq {n : ℕ} (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 504) : n = 3 := by
  have hn : n ≤ 3 := by
    by_contra hlt
    have h16 : 16 ≤ 2 ^ n :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h256 : 256 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 16 * 255 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h16 (by omega)
    omega
  interval_cases n <;> first | rfl | norm_num at h

theorem odd_card_and_three_le {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2) :
    Odd (Nat.card k) ∧ 3 ≤ Nat.card k := by
  have : Fintype k := Fintype.ofFinite k
  have hodd : Odd (Nat.card k) := by
    rw [Nat.card_eq_fintype_card, ← Nat.not_even_iff_odd]
    exact fun h => hk (FiniteField.even_card_iff_char_two.2 (Nat.even_iff.1 h))
  have h1 : 1 < Nat.card k := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨m, hm⟩ := hodd
  exact ⟨⟨m, hm⟩, by omega⟩

theorem not_SL_two_of_quadratic
    {F : Type} [Field F] [Finite F] (hF2 : ringChar F ≠ 2)
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hFe : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup .G2 F)} {g : adjointGroup .G2 F}
    {a : Fin Tag.G2.rank → Fˣ}
    (hαg : ∀ h : adjointGroup .G2 F, (α h : ModGL .G2 F) = (g : ModGL .G2 F) *
      rootDiagUnit .G2 a * Units.map (entrywiseHom δ.toRingHom) (h : ModGL .G2 F) *
        (rootDiagUnit .G2 a)⁻¹ * (g : ModGL .G2 F)⁻¹)
    (hα : α ^ 2 = 1) {n : ℕ} (hn : 1 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F)))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (i : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he F hFe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 .G2
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F))).map
      (adjointGroup .G2 F).subtype = entrywiseFixedGroup .G2 δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL .G2 F) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL .G2 F) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F))) ≃*
      ↥(entrywiseFixedGroup .G2 δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  obtain ⟨S₁, hS₁n, hS₁s, hS₁nab, ⟨eS⟩⟩ :=
    exists_normal_simple_of_mulEquiv (e₁.trans e₂) S hSn hSs hSnab
  obtain ⟨-, -, -, hJΓ, -, hJn, hab, -⟩ := Chevalley_coordinate_field_fixed_structure .G2 F hF2 δ
  have : ((fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ)).Normal := hJn
  have : Group.IsSolvable (↥(entrywiseFixedGroup .G2 δ) ⧸
      (fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ)) :=
    Group.isSolvable_of_comm hab
  have : Group.IsPerfect S₁ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.isPerfect_of_isSimpleGroup_of_noncomm hS₁nab
  have hS₁J : S₁ ≤ (fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ) :=
    fun x hx => by
      have h := map_eq_one_of_commutator_eq_top
        Group.IsPerfect.commutator_eq_top
        ((QuotientGroup.mk' ((fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ))).comp
          S₁.subtype) ⟨x, hx⟩
      rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have : Finite (fixSubfield δ) := Subtype.finite
  have hF₀2 : ringChar (fixSubfield δ) ≠ 2 := ringChar_fixSubfield_ne_two hF2 δ
  obtain ⟨hJs, -, -⟩ := odd_pinned_Chevalley_p_components .G2 (fixSubfield δ) hF₀2
  let eJ : adjointGroup .G2 (fixSubfield δ) ≃*
      (fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ) :=
    ((adjointGroup .G2 (fixSubfield δ)).equivMapOfInjective _ (baseChangeGL_injective _)).trans
      (subgroupOfEquivOfLe hJΓ).symm
  have : IsSimpleGroup ((fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ)) :=
    eJ.symm.isSimpleGroup
  have hN : (S₁.subgroupOf ((fixedFieldImage .G2 δ).subgroupOf
      (entrywiseFixedGroup .G2 δ))).Normal := hS₁n.subgroupOf _
  have hSJ : S₁ = (fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ) := by
    rcases hN.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : S₁)
      apply hx
      have hx' : (⟨x, hS₁J x.2⟩ : (fixedFieldImage .G2 δ).subgroupOf
          (entrywiseFixedGroup .G2 δ)) ∈ S₁.subgroupOf ((fixedFieldImage .G2 δ).subgroupOf
            (entrywiseFixedGroup .G2 δ)) := mem_subgroupOf.mpr x.2
      rw [h, mem_bot] at hx'
      have hx'' : (x : entrywiseFixedGroup .G2 δ) = 1 := congrArg Subtype.val hx'
      exact Subtype.ext hx''
    · refine le_antisymm hS₁J fun x hx => ?_
      have hx' : (⟨x, hx⟩ : (fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ)) ∈
          S₁.subgroupOf ((fixedFieldImage .G2 δ).subgroupOf (entrywiseFixedGroup .G2 δ)) :=
        h ▸ mem_top _
      exact hx'
  have hcard : Nat.card K * (Nat.card K ^ 2 - 1) =
      Nat.card (adjointGroup .G2 (fixSubfield δ)) := by
    rw [← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, ← Nat.card_congr i.toEquiv,
      Nat.card_congr eS.toEquiv, hSJ, Nat.card_congr eJ.toEquiv]
  rw [(exact_G2_finite_order (fixSubfield δ) rfl).2.1, hK] at hcard
  obtain ⟨hodd, h3⟩ := odd_card_and_three_le hF₀2
  exact two_pow_mul_ne_G2_order hn hodd h3 hcard

theorem normal_simple_map_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (S : Subgroup X) (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x) :
    (S.map e.toMonoidHom).Normal ∧ IsSimpleGroup (S.map e.toMonoidHom) ∧
      ∃ x y : S.map e.toMonoidHom, x * y ≠ y * x := by
  let eS : S ≃* S.map e.toMonoidHom := S.equivMapOfInjective _ e.injective
  refine ⟨hSn.map _ e.surjective, eS.symm.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := hSnab
  exact ⟨eS x, eS y, fun h' => hxy (eS.injective (by rw [map_mul, map_mul, h']))⟩

theorem map_subtype_map_equivMapOfInjective_trans {X : Type*} [Group X] {A T : Subgroup X}
    (ψ : MulAut X) (hmap : A.map ψ.toMonoidHom = T) (S : Subgroup A) :
    (S.map ((A.equivMapOfInjective _ ψ.injective).trans
        (MulEquiv.subgroupCongr hmap)).toMonoidHom).map T.subtype =
      (S.map A.subtype).map ψ.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl


theorem exceptional_coset_SL_two
    {F : Type} [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    {a : ℕ} (hF : Nat.card F = 3 ^ (2 * a + 1)) (g : adjointGroup ReeTag.G2.tag F)
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut F a) ^ 2 = 1) {n : ℕ} (hn : 1 ≤ n)
    (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (S : Subgroup ((MulAut.conj g * ReeTag.G2.finiteReeAut F a).toMonoidHom.eqLocus
      (MonoidHom.id (adjointGroup ReeTag.G2.tag F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (i : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    a = 0 ∧ n = 3 ∧ ∃ ψ : MulAut (adjointGroup ReeTag.G2.tag F),
      ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut F a) * ψ⁻¹ = ReeTag.G2.finiteReeAut F a ∧
      (S.map ((MulAut.conj g * ReeTag.G2.finiteReeAut F a).toMonoidHom.eqLocus
          (MonoidHom.id (adjointGroup ReeTag.G2.tag F))).subtype).map ψ.toMonoidHom =
        (commutator (ReeTag.G2.finiteReeFixedGroup F a)).map
          (ReeTag.G2.finiteReeFixedGroup F a).subtype := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
    CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components a F hF g hα
  have hmap : ((MulAut.conj g * ReeTag.G2.finiteReeAut F a).toMonoidHom.eqLocus
      (MonoidHom.id (adjointGroup ReeTag.G2.tag F))).map ψ.toMonoidHom =
      ReeTag.G2.finiteReeFixedGroup F a := by
    rw [map_eqLocus_mulAut_conj, hψ]
    rfl
  let ι := (((MulAut.conj g * ReeTag.G2.finiteReeAut F a).toMonoidHom.eqLocus
      (MonoidHom.id (adjointGroup ReeTag.G2.tag F))).equivMapOfInjective _ ψ.injective).trans
    (MulEquiv.subgroupCongr hmap)
  obtain ⟨hS₁n, hS₁s, hS₁nab⟩ := normal_simple_map_of_mulEquiv ι S hSn hSs hSnab
  let eS : S ≃* S.map ι.toMonoidHom := S.equivMapOfInjective _ ι.injective
  obtain ⟨-, -, -, hΓmap, -, hzero⟩ :=
    CFSG.LieType.Ree.G2_exceptional_field_involution_fixed_p_components a F hF
  let eΓ : ReeTag.G2.finiteReeFixedGroup F a ≃* ReeTag.G2.reeGamma F a :=
    ((ReeTag.G2.finiteReeFixedGroup F a).equivMapOfInjective _
      (adjointGroup ReeTag.G2.tag F).subtype_injective).trans (MulEquiv.subgroupCongr hΓmap)
  obtain ⟨hDs, -, -, htop, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components a F hF
  have hDmap : (commutator (ReeTag.G2.finiteReeFixedGroup F a)).map eΓ.toMonoidHom =
      commutator (ReeTag.G2.reeGamma F a) := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ eΓ.surjective]
  let eD : commutator (ReeTag.G2.finiteReeFixedGroup F a) ≃*
      commutator (ReeTag.G2.reeGamma F a) :=
    ((commutator (ReeTag.G2.finiteReeFixedGroup F a)).equivMapOfInjective _
      eΓ.injective).trans (MulEquiv.subgroupCongr hDmap)
  have : IsSimpleGroup (commutator (ReeTag.G2.finiteReeFixedGroup F a)) := eD.isSimpleGroup
  have : Group.IsPerfect (S.map ι.toMonoidHom) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.isPerfect_of_isSimpleGroup_of_noncomm hS₁nab
  have hS₁D : S.map ι.toMonoidHom ≤ commutator (ReeTag.G2.finiteReeFixedGroup F a) := by
    have h1 : ⁅S.map ι.toMonoidHom, S.map ι.toMonoidHom⁆ = S.map ι.toMonoidHom :=
      Subgroup.commutator_eq_self
    rw [← h1, _root_.commutator_def]
    exact commutator_mono le_top le_top
  have hN : ((S.map ι.toMonoidHom).subgroupOf
      (commutator (ReeTag.G2.finiteReeFixedGroup F a))).Normal := hS₁n.subgroupOf _
  have hSD : S.map ι.toMonoidHom = commutator (ReeTag.G2.finiteReeFixedGroup F a) := by
    rcases hN.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : S.map ι.toMonoidHom)
      apply hx
      have hx' : (⟨x, hS₁D x.2⟩ : commutator (ReeTag.G2.finiteReeFixedGroup F a)) ∈
          (S.map ι.toMonoidHom).subgroupOf (commutator (ReeTag.G2.finiteReeFixedGroup F a)) :=
        mem_subgroupOf.mpr x.2
      rw [h, mem_bot] at hx'
      have hx'' : (x : ReeTag.G2.finiteReeFixedGroup F a) = 1 := congrArg Subtype.val hx'
      exact Subtype.ext hx''
    · refine le_antisymm hS₁D fun x hx => ?_
      have hx' : (⟨x, hx⟩ : commutator (ReeTag.G2.finiteReeFixedGroup F a)) ∈
          (S.map ι.toMonoidHom).subgroupOf (commutator (ReeTag.G2.finiteReeFixedGroup F a)) :=
        h ▸ mem_top _
      exact hx'
  have hcard : 2 ^ n * ((2 ^ n) ^ 2 - 1) = Nat.card (commutator (ReeTag.G2.reeGamma F a)) := by
    rw [← hK, ← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      ← Nat.card_congr i.toEquiv, Nat.card_congr eS.toEquiv, hSD, Nat.card_congr eD.toEquiv]
  have ha0 : a = 0 := by
    by_contra ha
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
    obtain ⟨-, -, -, -, -, -, -, -, -, hΓcard, -⟩ :=
      CFSG.LieType.Ree.small_Ree_Borel_coset_Sylow_action a F hF w₀ hw₀
    rw [htop ha1, card_top, hΓcard] at hcard
    exact two_pow_mul_ne_ree_order hn ha1 hcard
  subst ha0
  obtain ⟨-, hD504, -, -⟩ := hzero rfl
  have hn3 : n = 3 := by
    apply eq_three_of_two_pow_mul_eq
    rw [hcard, ← Nat.card_congr eD.toEquiv, hD504]
  refine ⟨rfl, hn3, ψ, hψ, ?_⟩
  rw [← map_subtype_map_equivMapOfInjective_trans ψ hmap S, hSD]

theorem odd_G2_involution_fixed_normal_even_SL2_parameter_boundary
    {p f n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (α : MulAut (adjointGroup .G2 F)) (hα1 : α ≠ 1) (hα : α ^ 2 = 1) (hn : 2 ≤ n) (K : Type*)
    [Field K] (hK : Nat.card K = 2 ^ n)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    p = 3 ∧ f = 1 ∧ Nat.card K = 8 ∧
      ∃ (_ : CharP F ReeTag.G2.prime) (β : MulAut (adjointGroup .G2 F)),
        β * α * β⁻¹ = ReeTag.G2.finiteReeAut F 0 ∧
        (S.map (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .G2 F))).subtype).map
            β.toMonoidHom =
          (commutator (ReeTag.G2.finiteReeFixedGroup F 0)).map
            (ReeTag.G2.finiteReeFixedGroup F 0).subtype ∧
        Nat.card (commutator (ReeTag.G2.finiteReeFixedGroup F 0)) = 504 ∧
        (commutator (ReeTag.G2.finiteReeFixedGroup F 0)).index = 3 ∧
        Nat.card (ReeTag.G2.finiteReeFixedGroup F 0) = 1512 := by
  classical
  have : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hF
  have hchar : ringChar F = p := ringChar.eq F p
  have hF2 : ringChar F ≠ 2 := hchar ▸ hp2
  have hFodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨i⟩ := hSK
  by_cases hp3 : p = 3
  · subst hp3
    have hR : CharP F ReeTag.G2.prime := ‹CharP F 3›
    rcases G2_three_involution_inner_quadratic_or_exceptional hf hF hα with
      ⟨g, a, hαg⟩ | ⟨e, he, hFe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, rfl⟩
    · exact (not_normal_simple_of_inner_diagonal hFodd hαg hα hα1 S hSn hSs hSnab).elim
    · exact (not_SL_two_of_quadratic hF2 Nat.prime_three he hFe δ hδ hαg hα (by omega) K hK S
        hSn hSs hSnab i).elim
    · have hFb : Nat.card F = 3 ^ (2 * b + 1) := by rw [hF, hfb]
      obtain ⟨hb0, hn3, ψ, hψ, hSψ⟩ :=
        exceptional_coset_SL_two hFb g hα (by omega) K hK S hSn hSs hSnab i
      subst hb0
      obtain ⟨-, -, -, -, -, hzero⟩ :=
        CFSG.LieType.Ree.G2_exceptional_field_involution_fixed_p_components 0 F hFb
      obtain ⟨h1512, h504, -, -⟩ := hzero rfl
      have hidx : (commutator (ReeTag.G2.finiteReeFixedGroup F 0)).index = 3 := by
        have h := (commutator (ReeTag.G2.finiteReeFixedGroup F 0)).card_mul_index
        rw [h504, h1512] at h
        omega
      refine ⟨rfl, by omega, by rw [hK, hn3]; norm_num, hR, ψ, hψ, hSψ, h504, hidx, h1512⟩
  · rcases odd_F4_E8_G2_involution_inner_or_quadratic (τ := .G2)
      (Or.inr (Or.inr ⟨rfl, fun h => hp3 (hchar.symm.trans h)⟩)) hFodd hα with
      ⟨g, a, hαg⟩ | ⟨p', e, hp', he, hFe, δ, hδ, g, a, hαg⟩
    · exact (not_normal_simple_of_inner_diagonal hFodd hαg hα hα1 S hSn hSs hSnab).elim
    · exact (not_SL_two_of_quadratic hF2 hp' he hFe δ hδ hαg hα (by omega) K hK S hSn hSs
        hSnab i).elim

end CFSG.LocalAnalysis.SteinbergBM
