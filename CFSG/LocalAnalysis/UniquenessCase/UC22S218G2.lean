module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2CartanRank
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevG2Rank
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
import CFSG.RankThree.PartOne.AUTSL.FieldExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint.Chevalley (Tag adjointGroup ModGL entrywiseHom)
open CFSG.LieType.Chevalley (posUnipotentSub torusSub)
open CFSG.Quasithin.H13.Sec53F.G2 (fieldAut fieldAut_apply entrywise_torusElt g2_H_comm g2_H_le
  g2_U_inf_H g2_B_eq g2_sylow borelAutData_g2)
open CFSG.AGLEmbedding.KFactProofs.G2Q (tz tz_pow tz_one_one tz_injective tz_mem_adjointGroup
  tz_mem_torusGroup exists_tz_of_mem_torusGroup)

set_option linter.unusedSectionVars false


section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem uc22s218_g2_fieldAut_pow {σ : MulAut ↥(adjointGroup Tag.G2 K)}
    (hσ : σ ∈ (fieldAut K).range) :
    ∃ j : ℕ, ∀ h ∈ torusSub Tag.G2 K, σ h = h ^ 2 ^ j := by
  obtain ⟨σ₀, rfl⟩ := hσ
  obtain ⟨j, hj⟩ := CFSG.RankThree.PartOne.AUTSL.exists_ringEquiv_eq_pow_two σ₀
  refine ⟨j, fun h hh => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hh
  obtain ⟨s, t, hst⟩ := exists_tz_of_mem_torusGroup hh
  have e1 : Units.map (entrywiseHom σ₀.toRingHom) (tz s t) =
      tz (Units.map σ₀.toRingHom.toMonoidHom s) (Units.map σ₀.toRingHom.toMonoidHom t) := by
    unfold tz
    rw [map_mul, entrywise_torusElt, entrywise_torusElt]
  have e2 : ∀ u : Kˣ, Units.map σ₀.toRingHom.toMonoidHom u = u ^ 2 ^ j := fun u => by
    ext
    simp [hj]
  apply Subtype.ext
  rw [fieldAut_apply, Subgroup.coe_pow, hst, tz_pow, e1, e2, e2]

theorem uc22s218_g2_torus_pow {n : ℕ} (hK : Nat.card K = 2 ^ n) {h : ↥(adjointGroup Tag.G2 K)}
    (hh : h ∈ torusSub Tag.G2 K) : h ^ (2 ^ n - 1) = 1 := by
  rw [Subgroup.mem_subgroupOf] at hh
  obtain ⟨s, t, hst⟩ := exists_tz_of_mem_torusGroup hh
  have hu : ∀ u : Kˣ, u ^ (2 ^ n - 1) = 1 := fun u => by
    rw [← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  apply Subtype.ext
  rw [Subgroup.coe_pow, hst, tz_pow, hu, hu, tz_one_one]
  rfl

theorem uc22s218_g2_exists_orderOf_torus {n s : ℕ} (hK : Nat.card K = 2 ^ n) (hsn : s ∣ n) :
    ∃ d ∈ torusSub Tag.G2 K, orderOf d = 2 ^ s - 1 := by
  obtain ⟨t, ht⟩ := uc22p218c_exists_orderOf_units hK hsn
  refine ⟨⟨tz t 1, tz_mem_adjointGroup t 1⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact tz_mem_torusGroup t 1
  · rw [← ht, ← Subgroup.orderOf_coe]
    show orderOf (tz t 1 : ModGL Tag.G2 K) = orderOf t
    rw [orderOf_eq_orderOf_iff]
    intro m
    rw [tz_pow, one_pow, ← tz_one_one]
    constructor
    · intro h
      exact (tz_injective h).1
    · intro h
      rw [h]

theorem uc22s218_g2_fieldBorelData_model {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    FieldBorelData n (2 ^ n - 1) (posUnipotentSub Tag.G2 K) (torusSub Tag.G2 K)
      (fieldAut K).range where
  borel := borelAutData_g2 hn hK
  pow := fun _ hσ => uc22s218_g2_fieldAut_pow hσ
  exp := fun _ hh => uc22s218_g2_torus_pow hK hh
  exists_d := fun _ hsn => uc22s218_g2_exists_orderOf_torus hK hsn

theorem uc22s218_g2_model_elemAbelian {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : ℓ ∣ Nat.card K - 1) :
    ∃ A : Subgroup ↥(adjointGroup Tag.G2 K), A ≤ torusSub Tag.G2 K ∧ IsElemAbelian ℓ A ∧
      Nat.card A = ℓ ^ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) ℓ (by rw [Nat.card_units]; exact hℓK)
  let e := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.g2TorusEquivUnits K
  let f : (↥(zpowers ζ) × ↥(zpowers ζ)) →* ↥(adjointGroup Tag.G2 K) :=
    ((CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K).subtype).comp
      ((e.symm : Kˣ × Kˣ →* _).comp ((zpowers ζ).subtype.prodMap (zpowers ζ).subtype))
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := e.symm.injective (Subtype.ext hab)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h1)) (Subtype.ext (congrArg Prod.snd h1))
  have hpow : ∀ x : ↥(zpowers ζ), x ^ ℓ = 1 := fun x => by
    rw [← hζ, ← Nat.card_zpowers]
    exact pow_card_eq_one'
  refine ⟨(⊤ : Subgroup (↥(zpowers ζ) × ↥(zpowers ζ))).map f, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact Subtype.mem (e.symm (a.1.1, a.2.1))
  · refine CFSG.SectionRank.isElemAbelian_map ⟨inferInstance, fun x _ => ?_⟩ f
    exact Prod.ext (hpow x.1) (hpow x.2)
  · rw [Subgroup.card_map_of_injective hf, Subgroup.card_top, Nat.card_prod, Nat.card_zpowers, hζ,
      sq]

theorem uc22s218_g2_model_index :
    (normalizer ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
      Set ↥(adjointGroup Tag.G2 K))).index * (Nat.card K - 1) ^ 2 =
        (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := by
  set U := posUnipotentSub Tag.G2 K with hUdef
  have hU : Nat.card U = Nat.card K ^ 6 := by
    rw [hUdef, CFSG.LieType.Chevalley.card_subgroupOf_of_le
      CFSG.LieType.Chevalley.posUnipotent_le_adjointGroup,
      CFSG.LieType.Chevalley.card_posUnipotent,
      CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2]
  obtain ⟨eC⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.normalizerQuotient_equiv_of_complement
      (U := U) (H := torusSub Tag.G2 K) g2_H_le g2_U_inf_H g2_B_eq
  have hq : Nat.card (TauCeti.Subgroup.normalizerQuotient U) = (Nat.card K - 1) ^ 2 := by
    rw [Nat.card_congr eC.toEquiv]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.g2Torus_card
  have hN : Nat.card (normalizer (U : Set ↥(adjointGroup Tag.G2 K))) =
      (Nat.card K - 1) ^ 2 * Nat.card K ^ 6 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (U.subgroupOf (normalizer (U : Set ↥(adjointGroup Tag.G2 K))))
    rw [CFSG.LieType.Chevalley.card_subgroupOf_of_le Subgroup.le_normalizer, hU] at h
    rw [h]
    exact congrArg (· * Nat.card K ^ 6) hq
  have hC : Nat.card ↥(adjointGroup Tag.G2 K) = ordG2 (Nat.card K) :=
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2
  have hmul := Subgroup.card_mul_index (normalizer (U : Set ↥(adjointGroup Tag.G2 K)))
  rw [hN, hC] at hmul
  unfold ordG2 at hmul
  have hq6 : 0 < Nat.card K ^ 6 := pow_pos Nat.card_pos 6
  apply Nat.eq_of_mul_eq_mul_left hq6
  calc Nat.card K ^ 6 * ((normalizer (U : Set ↥(adjointGroup Tag.G2 K))).index *
        (Nat.card K - 1) ^ 2)
      = (Nat.card K - 1) ^ 2 * Nat.card K ^ 6 *
        (normalizer (U : Set ↥(adjointGroup Tag.G2 K))).index := by ring
    _ = Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := hmul
    _ = Nat.card K ^ 6 * ((Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1)) := by ring

end Model

theorem uc22s218_g2_not_dvd_index {q r idx : ℕ} (hq : 2 ≤ q) (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hrq : r ∣ q - 1) (h : idx * (q - 1) ^ 2 = (q ^ 6 - 1) * (q ^ 2 - 1)) :
    ¬ r ∣ idx := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hrq h
  have ha : 0 < a := by omega
  have h6 : (a + 1) ^ 6 - 1 = a * (a ^ 5 + 6 * a ^ 4 + 15 * a ^ 3 + 20 * a ^ 2 + 15 * a + 6) := by
    have h1 : 1 ≤ (a + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    zify [h1]
    ring
  have h2 : (a + 1) ^ 2 - 1 = a * (a + 2) := by
    have h1 : 1 ≤ (a + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1]
    ring
  rw [h6, h2] at h
  have hidx : idx = 12 + a * (a ^ 5 + 8 * a ^ 4 + 27 * a ^ 3 + 50 * a ^ 2 + 55 * a + 36) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < a ^ 2 by positivity)
    rw [h]
    ring
  intro hdvd
  rw [hidx] at hdvd
  have h12 : r ∣ 12 := (Nat.dvd_add_left (dvd_mul_of_dvd_left hrq _)).1 hdvd
  have hle : r ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases r <;> first | omega | exact absurd hr (by norm_num)

theorem uc22s218_g2_not_three_dvd {s : ℕ} (hs : Odd s) : ¬ 3 ∣ 2 ^ s - 1 := by
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


theorem uc22s218_g2_exists_model {Y : Type} [Group Y] {n : ℕ} (hY : IsG2 Y n) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (Y ≃* ↥(adjointGroup Tag.G2 K)) := by
  obtain ⟨hn, K, hF, hFin, hcp, hK, e⟩ := CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model
    (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide))
  exact ⟨hn, K, hF, hFin, hcp, hK, e⟩

theorem uc22s218_g2_fieldBorel {Y : Type} [Group Y] {n : ℕ} (hY : IsG2 Y n) :
    FieldBorel Y n (2 ^ n - 1) := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_g2_exists_model hY
  exact FieldBorel.of_mulEquiv (Y := ↥(adjointGroup Tag.G2 K))
    ⟨_, _, _, uc22s218_g2_fieldBorelData_model hn hK⟩ e.symm

theorem uc22s218_g2_torus {Y : Type} [Group Y] {n : ℕ} (hY : IsG2 Y n) :
    ∃ T : Subgroup Y, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 →
        ∃ A : Subgroup Y, A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2 := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_g2_exists_model hY
  refine ⟨(torusSub Tag.G2 K).map e.symm.toMonoidHom, ?_, fun ℓ hℓ hℓn => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, g2_H_comm a ha b hb]
  · obtain ⟨A, hAT, hAe, hAc⟩ := uc22s218_g2_model_elemAbelian hℓ (by rw [hK]; exact hℓn)
    refine ⟨A.map e.symm.toMonoidHom, Subgroup.map_mono hAT,
      CFSG.SectionRank.isElemAbelian_map hAe _, ?_⟩
    rw [Subgroup.card_map_of_injective e.symm.injective, hAc]

theorem uc22s218_g2_pRank_eq_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsG2 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup Y) = 2 := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_g2_exists_model hY
  have := Fintype.ofFinite K
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e,
    CFSG.LocalAnalysis.RankThreeUC.S15.pRank_adjointG2_eq K hK' hn hr hr2]
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  have h1 : r ∣ Fintype.card K ^ 2 - 1 := by
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [hK', hfac]
    exact dvd_mul_of_dvd_right hrn _
  unfold CFSG.LocalAnalysis.RankThreeUC.S15.rkG2
  rw [if_pos ((CFSG.LocalAnalysis.RankThreeUC.S15.eS_eq_one_iff hq1).2 h1)]

theorem uc22s218_g2_pRank_le_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsG2 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_g2_exists_model hY
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    CFSG.LocalAnalysis.RankThreeUC.S15.pRank_adjointG2_eq K hK' hn hp hp2]
  unfold CFSG.LocalAnalysis.RankThreeUC.S15.rkG2
  split_ifs <;> omega

theorem uc22s218_g2_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsG2 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ¬ r ∣ Nat.card (Sylow 2 Y) := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_g2_exists_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(adjointGroup Tag.G2 K) := Finite.of_equiv Y e.toEquiv
  rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv e 2]
  have hU : IsSylowTwoOf (posUnipotentSub Tag.G2 K) ⊤ := g2_sylow
  have hidx : ¬ 2 ∣ (posUnipotentSub Tag.G2 K).index := by
    have h := hU.2.2
    rwa [show ((posUnipotentSub Tag.G2 K).subgroupOf ⊤).index =
      (posUnipotentSub Tag.G2 K).index from Subgroup.relIndex_top_right _] at h
  let P : Sylow 2 ↥(adjointGroup Tag.G2 K) := hU.2.1.toSylow hidx
  have hP : (P : Subgroup ↥(adjointGroup Tag.G2 K)) = posUnipotentSub Tag.G2 K :=
    IsPGroup.toSylow_coe hU.2.1 hidx
  rw [Sylow.card_eq_index_normalizer P]
  have hnorm : normalizer (P : Set ↥(adjointGroup Tag.G2 K)) =
      normalizer ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
        Set ↥(adjointGroup Tag.G2 K)) := by
    rw [← hP]
    rfl
  rw [hnorm]
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hr3 : r ≠ 3 := fun h => uc22s218_g2_not_three_dvd hs (h ▸ hrs)
  have hrq : r ∣ Nat.card K - 1 := by
    rw [hK]
    exact hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hq2 : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact uc22s218_g2_not_dvd_index hq2 hr hr2 hr3 hrq uc22s218_g2_model_index

theorem torusFacts218_G2 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsG2 Y n) :
    TorusFacts218 Y n (fun p => p ∣ 2 ^ n - 1) (fun p => ¬ p ∣ 2 ^ n - 1) :=
  torusFacts218_of_fieldBorel (E := 2 ^ n - 1) (uc22s218_g2_fieldBorel hY)
    (fun _ hsn _ hrs => hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
    (fun _ _ h => h) (uc22s218_g2_torus hY)
    (fun hs hsn hr hrs => uc22s218_g2_pRank_eq_two hY hs hsn hr hrs)
    (fun hs hsn hr hrs => uc22s218_g2_not_dvd_card_sylow hY hs hsn hr hrs)
    (fun hp hp2 _ => uc22s218_g2_pRank_le_two hY hp hp2)

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22
