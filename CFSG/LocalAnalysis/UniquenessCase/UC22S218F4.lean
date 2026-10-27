module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsF4
import CFSG.RankThree.PartOne.AUTSL.FieldExt
import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33ExceptionalRanks
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
import CFSG.Blueprint.LieModelAPI
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.SeitzGeneration.Lift
import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
import CFSG.Quasithin.Background.A3Structure318Defs
import CFSG.Quasithin.Background.B4Statement
import CFSG.Quasithin.Background.B5Statement
import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
import CFSG.RankThree.PartOne.BRANCH.RankRee
import CFSG.RankThree.PartOne.KE.A2Family
import CFSG.RankThree.PartOne.KE.A2Shape
import CFSG.RankThree.PartOne.KE.StabGeneral
import CFSG.RankThree.PartOne.KLR.Master
import CFSG.RankThree.PartOne.KLR.SectorAssembly
import CFSG.RankThree.PartOne.N143.Weyl613Defs
import CFSG.RankThree.PartOne.N143X.KF64WSimple
import CFSG.RankThree.PartOne.S8.Statements
import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint (LieModel)
open CFSG.LieType.Ree.ReeTag (F4)
open CFSG.LieType.Ree.LargeReeCover (torusPair torusPair_mem_reeGamma)
open CFSG.LieType.Ree.LargeReeInvolution (rankOne_exists_torusPair_eq
  rankOne_torusPair_mem_reeFixedTorus)
open CFSG.RankThree.LargeReeOrder (torusPair_injective card_reeFixedBorel
  large_Ree_exact_native_order_and_prime_factor_exhaustion)
open CFSG.Quasithin.H13.Sec53F.ReeF4 (borelAutData_f4 entry_torusPair f4_H_comm f4_sylow)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 (pRank_three_eq_two_of_lieModel_twistedF4)

set_option linter.unusedSectionVars false


section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem uc22s218_f4_fieldAut_pow (hK : Nat.card K = 2 ^ (2 * a + 1))
    {σ : MulAut ↥(F4.reeGamma K a)} (hσ : σ ∈ (F4.reeGammaFieldAutHom K a).range) :
    ∃ j : ℕ, ∀ h ∈ (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a), σ h = h ^ 2 ^ j := by
  obtain ⟨β, rfl⟩ := hσ
  obtain ⟨j, hj⟩ := CFSG.RankThree.PartOne.AUTSL.exists_ringEquiv_eq_pow_two β
  refine ⟨j, fun h hh => ?_⟩
  obtain ⟨u, v, huv⟩ := rankOne_exists_torusPair_eq hK (Subgroup.mem_subgroupOf.1 hh)
  have e1 : ∀ w : Kˣ, Units.map β.toRingHom.toMonoidHom w = w ^ 2 ^ j := fun w => by
    ext
    simp [hj]
  have e2 : torusPair a (u ^ 2 ^ j, v ^ 2 ^ j) = torusPair (K := K) a (u, v) ^ 2 ^ j := by
    rw [← map_pow]
    rfl
  apply Subtype.ext
  rw [F4.reeGammaFieldAutHom_apply, F4.coe_reeGammaFieldAut, Subgroup.coe_pow, ← huv,
    entry_torusPair, e1, e1, e2]

theorem uc22s218_f4_torus_pow (hK : Nat.card K = 2 ^ (2 * a + 1)) {h : ↥(F4.reeGamma K a)}
    (hh : h ∈ (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a)) :
    h ^ (2 ^ (2 * a + 1) - 1) = 1 := by
  obtain ⟨u, v, huv⟩ := rankOne_exists_torusPair_eq hK (Subgroup.mem_subgroupOf.1 hh)
  have hu : ∀ w : Kˣ, w ^ (2 ^ (2 * a + 1) - 1) = 1 := fun w => by
    rw [← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← huv, ← map_pow, show (u, v) ^ (2 ^ (2 * a + 1) - 1) = 1 from
    Prod.ext (hu u) (hu v), map_one]
  rfl

theorem uc22s218_f4_exists_orderOf_torus {s : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hsn : s ∣ 2 * a + 1) :
    ∃ d ∈ (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a), orderOf d = 2 ^ s - 1 := by
  obtain ⟨t, ht⟩ := uc22p218c_exists_orderOf_units hK hsn
  have hK' : Nat.card K = F4.prime ^ (2 * a + 1) := hK
  refine ⟨⟨torusPair a (t, 1), torusPair_mem_reeGamma a hK' (t, 1)⟩,
    Subgroup.mem_subgroupOf.2 (rankOne_torusPair_mem_reeFixedTorus hK t 1), ?_⟩
  rw [Subgroup.orderOf_mk, orderOf_injective (torusPair a) (torusPair_injective hK) (t, 1),
    Prod.orderOf, orderOf_one, Nat.lcm_one_right, ht]

theorem uc22s218_f4_fieldBorelData_model (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    FieldBorelData (2 * a + 1) (2 ^ (2 * a + 1) - 1)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
      ((F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a))
      (F4.reeGammaFieldAutHom K a).range where
  borel := borelAutData_f4 hK ha
  pow := fun _ hσ => uc22s218_f4_fieldAut_pow hK hσ
  exp := fun _ hh => uc22s218_f4_torus_pow hK hh
  exists_d := fun _ hsn => uc22s218_f4_exists_orderOf_torus hK hsn

theorem uc22s218_f4_model_elemAbelian {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hℓK : ℓ ∣ Nat.card K - 1) :
    ∃ A : Subgroup ↥(F4.reeGamma K a),
      A ≤ (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a) ∧ IsElemAbelian ℓ A ∧
        Nat.card A = ℓ ^ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) ℓ (by rw [Nat.card_units]; exact hℓK)
  have hK' : Nat.card K = F4.prime ^ (2 * a + 1) := hK
  let φ : Kˣ × Kˣ →* ↥(F4.reeGamma K a) :=
    (torusPair a).codRestrict _ (torusPair_mem_reeGamma a hK')
  have hφ : Function.Injective φ := fun x y h => torusPair_injective hK (congrArg Subtype.val h)
  let f : (↥(zpowers ζ) × ↥(zpowers ζ)) →* ↥(F4.reeGamma K a) :=
    φ.comp ((zpowers ζ).subtype.prodMap (zpowers ζ).subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 := hφ hxy
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h1)) (Subtype.ext (congrArg Prod.snd h1))
  have hpow : ∀ x : ↥(zpowers ζ), x ^ ℓ = 1 := fun x => by
    rw [← hζ, ← Nat.card_zpowers]
    exact pow_card_eq_one'
  refine ⟨(⊤ : Subgroup (↥(zpowers ζ) × ↥(zpowers ζ))).map f, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (rankOne_torusPair_mem_reeFixedTorus hK x.1.1 x.2.1)
  · exact CFSG.SectionRank.isElemAbelian_map
      ⟨inferInstance, fun x _ => Prod.ext (hpow x.1) (hpow x.2)⟩ f
  · rw [Subgroup.card_map_of_injective hf, Subgroup.card_top, Nat.card_prod, Nat.card_zpowers, hζ,
      sq]

theorem uc22s218_f4_model_index (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (normalizer (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :
      Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a))).index =
        (2 ^ (2 * a + 1) + 1) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) ^ 2 *
          ((2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1) *
            ((2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1) := by
  rw [CFSG.LieType.Ree.ReeTag.normalizer_reeFixedPosUnipotent_subgroupOf]
  have hBΓ : F4.reeFixedBorel K a ≤ F4.reeGamma K a := inf_le_right
  have hN : Nat.card ((F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a)) =
      (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBΓ).toEquiv, card_reeFixedBorel hK]
  have hmul := Subgroup.card_mul_index ((F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a))
  rw [hN, (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1] at hmul
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) ^ 2 :=
    Nat.mul_pos (pow_pos (by omega) 12) (pow_pos (by omega) 2)
  refine Nat.eq_of_mul_eq_mul_left hpos (hmul.trans ?_)
  ring

end Model

theorem uc22s218_f4_not_dvd_index {q r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : 1 ≤ q)
    (hrq : r ∣ q - 1) :
    ¬ r ∣ (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have hq1 : (q : ZMod r) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (q - 1) r).2 hrq
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
    exact h
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub hq2, Nat.cast_sub hq4]
  rw [hq1]
  norm_num
  intro h
  have h16 : ((16 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff, show (16 : ℕ) = 2 ^ 4 by norm_num] at h16
  have h2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h16)
  omega

theorem uc22s218_f4_not_three_dvd {s : ℕ} (hs : Odd s) : ¬ 3 ∣ 2 ^ s - 1 := by
  obtain ⟨k, rfl⟩ := hs
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have h3 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [h2]
    omega
  generalize 2 ^ (2 * k + 1) = X at h3 ⊢
  omega

section Rank

theorem uc22s218_f4_exists_model {Y : Type} [Group Y] {n : ℕ}
    (hY : LieModel Y .twistedF4 0 2 n) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (_ : CharP K F4.prime), Nat.card K = 2 ^ n ∧ Nonempty (Y ≃* ↥(F4.reeGamma K a)) := by
  obtain ⟨-, a, ha, hfa, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma (hY.reeTitsModel (by decide)).2
  exact ⟨a, ha, hfa, K, inferInstance, inferInstance, inferInstance, by rw [hK, hfa], ⟨e⟩⟩

theorem uc22s218_f4_fieldBorel {Y : Type} [Group Y] {n : ℕ}
    (hY : LieModel Y .twistedF4 0 2 n) : FieldBorel Y n (2 ^ n - 1) := by
  obtain ⟨a, ha, rfl, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_f4_exists_model hY
  exact FieldBorel.of_mulEquiv (Y := ↥(F4.reeGamma K a))
    ⟨_, _, _, uc22s218_f4_fieldBorelData_model ha hK⟩ e.symm

theorem uc22s218_f4_torus {Y : Type} [Group Y] {n : ℕ} (hY : LieModel Y .twistedF4 0 2 n) :
    ∃ T : Subgroup Y, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 →
        ∃ A : Subgroup Y, A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2 := by
  obtain ⟨a, ha, rfl, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_f4_exists_model hY
  refine ⟨((F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a)).map e.symm.toMonoidHom, ?_,
    fun ℓ hℓ hℓn => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, f4_H_comm x hx y hy]
  · obtain ⟨A, hAT, hAe, hAc⟩ := uc22s218_f4_model_elemAbelian hℓ hK (by rw [hK]; exact hℓn)
    refine ⟨A.map e.symm.toMonoidHom, Subgroup.map_mono hAT,
      CFSG.SectionRank.isElemAbelian_map hAe _, ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hAc]

theorem uc22s218_f4_pRank_le_two_of_five_le {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : LieModel Y .twistedF4 0 2 n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  have hX := (hY.reeTitsModel (by decide)).2
  have h2 : CFSG.LieType.SeitzGeneration.RankLE2 p Y :=
    CFSG.LieType.SeitzGeneration.rankLE2_of_noPowThree hp fun E hE hc =>
      CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five hX hp hp5 hE hc
  exact CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => h2 E hE

theorem uc22s218_f4_pRank_le_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : LieModel Y .twistedF4 0 2 n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  by_cases hp3 : p = 3
  · subst hp3
    exact (pRank_three_eq_two_of_lieModel_twistedF4 hY).le
  · exact uc22s218_f4_pRank_le_two_of_five_le hY hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3)

theorem uc22s218_f4_pRank_eq_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : LieModel Y .twistedF4 0 2 n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) : CFSG.Open.pRank r (⊤ : Subgroup Y) = 2 := by
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hr3 : r ≠ 3 := fun h => uc22s218_f4_not_three_dvd hs (h ▸ hrs)
  refine le_antisymm (uc22s218_f4_pRank_le_two_of_five_le hY hr
    (hr.five_le_of_ne_two_of_ne_three hr2 hr3)) ?_
  obtain ⟨T, -, hT⟩ := uc22s218_f4_torus hY
  obtain ⟨A, -, hAe, hAc⟩ := hT r hr (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
  exact CFSG.SectionRank.le_pRank hr.one_lt le_top hAe hAc

theorem uc22s218_f4_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : LieModel Y .twistedF4 0 2 n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) : ¬ r ∣ Nat.card (Sylow 2 Y) := by
  obtain ⟨a, ha, rfl, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_f4_exists_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(F4.reeGamma K a) := Finite.of_equiv Y e.toEquiv
  rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv e 2]
  have hU : IsSylowTwoOf ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ :=
    f4_sylow
  have hidx : ¬ 2 ∣ ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).index := by
    have h := hU.2.2
    rwa [show (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).subgroupOf ⊤).index =
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)).index from
        Subgroup.relIndex_top_right _] at h
  let P : Sylow 2 ↥(F4.reeGamma K a) := hU.2.1.toSylow hidx
  have hP : (P : Subgroup ↥(F4.reeGamma K a)) =
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :=
    IsPGroup.toSylow_coe hU.2.1 hidx
  rw [Sylow.card_eq_index_normalizer P]
  have hnorm : normalizer (P : Set ↥(F4.reeGamma K a)) =
      normalizer (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :
        Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a)) := by
    rw [← hP]
    rfl
  rw [hnorm, uc22s218_f4_model_index hK]
  exact uc22s218_f4_not_dvd_index hr (uc22p218c_ne_two_of_dvd hs.pos hrs) Nat.one_le_two_pow
    (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))

theorem torusFacts218_2F4 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : LieModel Y .twistedF4 0 2 n) :
    TorusFacts218 Y n (fun p => p ∣ 2 ^ n - 1) (fun p => ¬ p ∣ 2 ^ n - 1) :=
  torusFacts218_of_fieldBorel (E := 2 ^ n - 1) (uc22s218_f4_fieldBorel hY)
    (fun _ hsn _ hrs => hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
    (fun _ _ h => h) (uc22s218_f4_torus hY)
    (fun hs hsn hr hrs => uc22s218_f4_pRank_eq_two hY hs hsn hr hrs)
    (fun hs hsn hr hrs => uc22s218_f4_not_dvd_card_sylow hY hs hsn hr hrs)
    (fun hp hp2 _ => uc22s218_f4_pRank_le_two hY hp hp2)

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22
