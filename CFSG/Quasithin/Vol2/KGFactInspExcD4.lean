module

public import CFSG.Quasithin.Vol2.KGFactInspExcCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.Background.A318PD4

public section

namespace CFSG.Quasithin.H13.KGInsp4316.Exc

open CFSG.Quasithin (perfectCore isSolvable_iff_perfectCore_eq_bot)
open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

section D4

open CFSG.QuasithinUnique.Setup.X6 (fixedPosWeylGroup)


theorem fixed_perfectCore_eq_bot {t : TwistTag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (a : Fin t.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent t K σ.toRingHom))
    (h2 : Nat.card ↥(orbitField t K σ.toRingHom a) = 2) :
    perfectCore ((graphFixedParabolic t K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup t K σ.toRingHom)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨R, hVN, hNV, hsup, hRV, -⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.fixed_structure σ a
  have hVU : graphFixedSimpleComplement t K σ.toRingHom a ≤
      graphFixedPosUnipotent t K σ.toRingHom := graphFixedSimpleComplement_le a
  have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement t K σ.toRingHom a) :=
    IsPGroup.of_injective hU (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  have hVs : Group.IsSolvable ↥(graphFixedSimpleComplement t K σ.toRingHom a) := by
    have := hV2.isNilpotent
    infer_instance
  have hsolvSL : Group.IsSolvable (SL2 ↥(orbitField t K σ.toRingHom a)) := by
    refine CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h2]
    norm_num
  have hMs : Group.IsSolvable ↥R.range :=
    Group.isSolvable_of_surjective (f := R.rangeRestrict) (MonoidHom.rangeRestrict_surjective R)
  have hNs : Group.IsSolvable ↥(fixedPosWeylGroup t K σ.toRingHom a) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_of_levi hVN hNV hsup hVs hMs
  have hpcN : perfectCore (fixedPosWeylGroup t K σ.toRingHom a) = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp hNs
  have hPC : graphFixedParabolic t K σ.toRingHom {a} ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  apply Subgroup.map_injective (graphFixedRootGroup t K σ.toRingHom).subtype_injective
  rw [CFSG.QuasithinUnique.Vol2Native.A312L.perfectCore_map_subgroupOf hPC,
    CFSG.QuasithinUnique.Vol2Native.A312L.fixed_perfectCore_eq σ a, hpcN, Subgroup.map_bot]

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X} {n : ℕ} {x : X}

theorem two_le_pRank_d4
    (h : Cfg4316 S R K n x) (hRS : R ≤ S) {f : ℕ}
    (hm : ChevalleyExceptionalModel ↥S .trialityD4 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) : 2 ≤ CFSG.Open.pRank p S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, L, _, _, σ, hL, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hm
  have hL3 : Nat.card L = 2 ^ (3 * f) := by rw [hL, ← pow_mul, mul_comm]
  have : CharP L 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hL3
  have : Finite (ModGL TwistTag.D4.tag L) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 L 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 L σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 L σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 L σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 L σ.toRingHom) := by
    refine CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hUsyl
  have hBT : CFSG.LieType.BorelTits.Holds ↥(graphFixedRootGroup TwistTag.D4 L σ.toRingHom) 2 :=
    (CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hm).of_mulEquiv e
  obtain ⟨j, D, hD, hdvd⟩ := exists_le_perfectCore h hRS e hBT hU₀
    (CFSG.QuasithinUnique.Setup.X6.triality_residualOvergroupsAt σ)
  have hn2 := h.two_le
  have hodd : Odd (4 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
      ((Nat.even_pow' (by omega)).mpr (by decide)) odd_one
  set a := CFSG.QuasithinUnique.Setup.X6.d4Index j with ha
  set La := orbitField TwistTag.D4 L σ.toRingHom a with hLa
  obtain ⟨m, hm'⟩ : ∃ m : ℕ, Nat.card ↥La = 2 ^ m := by
    have : Fintype ↥La := Fintype.ofFinite _
    obtain ⟨m, -, hm⟩ := FiniteField.card ↥La 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card]; exact hm⟩
  have hsub : 2 ^ m - 1 ∣ 2 ^ (3 * f) - 1 := by
    have hinj : Function.Injective (Units.map La.subtype.toMonoidHom) :=
      Units.map_injective La.subtype.injective
    have h1 := Subgroup.card_dvd_of_injective _ hinj
    rwa [Nat.card_units, Nat.card_units, hm', hL3] at h1
  have hmn : n ∣ m := by
    by_cases hm2 : 2 ≤ m
    · have hL4 : ∃ s : Finset ↥La, s.card = 4 := by
        refine CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four ?_
        rw [hm']
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      obtain ⟨g, hg, hker⟩ :=
        CFSG.QuasithinUnique.Vol2Native.A312L.exists_levi_hom_fixed σ a hUsyl.2.1 hL4
      have h1 := odd_dvd_card_of_le hD g hker hodd hdvd
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hm', ← pow_mul, mul_comm m 2,
        pow_mul] at h1
      norm_num at h1
      exact dvd_of_four_pow_sub_one_dvd (by omega) h1
    · exfalso
      have hm0 : m ≠ 0 := by
        intro h0
        have : 1 < Nat.card ↥La := Finite.one_lt_card
        rw [hm', h0] at this
        norm_num at this
      have hm1 : m = 1 := by omega
      have hbot := fixed_perfectCore_eq_bot σ a hUsyl.2.1 (by rw [hm', hm1, pow_one])
      rw [hbot, le_bot_iff] at hD
      rw [hD, Subgroup.card_bot, Nat.dvd_one] at hdvd
      have : 4 ^ 2 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
  have hp3f : p ∣ 2 ^ (3 * f) - 1 :=
    hpn.trans ((Nat.pow_sub_one_dvd_pow_sub_one 2 hmn).trans hsub)
  have hfac : 2 ^ (3 * f) - 1 = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 2 ^ f + 1) := by
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [mul_comm 3 f, pow_mul]
    generalize 2 ^ f = q at h1 ⊢
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  rw [hfac] at hp3f
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨E, hE, hEel, -⟩ :=
      CFSG.Quasithin.A318P.exists_nine_d4 σ.toRingHom (RingEquiv.refl L)
    have h2 : 2 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 L σ.toRingHom)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hEel (by rw [hE]; norm_num)
    exact CFSG.QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv e (by norm_num) h2
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by decide)
      omega
    have hcl : CFSG.Quasithin.R3c18.D4Cl p ((2 : ℤ) ^ f) := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      rcases (Nat.Prime.dvd_mul hp).mp hp3f with h3 | h3
      · left
        have h4 : ((p : ℕ) : ℤ) ∣ ((2 ^ f - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h3
        push_cast [h1] at h4
        exact h4
      · right; right; left
        have h4 : ((p : ℕ) : ℤ) ∣ (((2 ^ f) ^ 2 + 2 ^ f + 1 : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr h3
        push_cast at h4
        exact h4
    have h2 := CFSG.Quasithin.R3c18.d4Rank_holds σ hf hL hσ hp hp5 hcl
    obtain ⟨E, hE, hEel⟩ := CFSG.Quasithin.R3c18.exists_sq_of_two_le_pRank hp h2
    have h2' : 2 ≤ CFSG.Open.pRank p
        (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 L σ.toRingHom)) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_top hEel hE
    exact CFSG.QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv e hp.one_lt h2'

end D4

end CFSG.Quasithin.H13.KGInsp4316.Exc
