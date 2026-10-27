module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeTypes
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeOddAct
public import CFSG.GH74.GLS.IVK.Defs
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeHyp
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeSimple
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2Odd
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2OddGroup
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3OddGroup
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L35
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U37
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.GH74.GLS.IVK.L2.Lemma12
import CFSG.Models.PGL
public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAsc1411

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Step204AscL3OddMeet : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
        ((∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ p ^ e % 3 = 2 ∧
            Nonempty (↥(yAlpha M X T c) ≃* projSL 3 (GaloisField p e))) ∨
          (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ p ^ e % 3 = 1 ∧
            Nonempty (↥(yAlpha M X T c) ≃* projSU 3 p e))) →
        rAlpha M X T c ⊓ yAlpha M X T c ≠ ⊥ →
          CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j

namespace AscBridge

variable {G : Type} [Group G] [Finite G]
variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P X : Subgroup G}

theorem exists_outer_involution_of_inf_eq_bot (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    (hYK : ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c) [(yAlpha M X T c).Normal]
    (hKY : kTwenty M c ≤ yTwenty X c) (hD : rAlpha M X T c ⊓ yAlpha M X T c = ⊥)
    (hcard : Nat.card ((rAlpha M X T c).map (MulAut.conjNormal (H := yAlpha M X T c))) ≤ 2) :
    ∃ r ∈ rAlpha M X T c, Nat.card (rAlpha M X T c) = 2 ∧
      MulAut.conjNormal (H := yAlpha M X T c) r * MulAut.conjNormal (H := yAlpha M X T c) r = 1 ∧
      MulAut.conjNormal (H := yAlpha M X T c) r ∉
        (MulAut.conj : ↥(yAlpha M X T c) →* MulAut ↥(yAlpha M X T c)).range ∧
      (kToYAlpha (T := T) hKY).range ≤
        CFSG.GH74.GLS.fixedSubgroup ↥(yAlpha M X T c) (MulAut.conjNormal r) ∧
      ∀ y ∈ CFSG.GH74.GLS.fixedSubgroup ↥(yAlpha M X T c) (MulAut.conjNormal r),
        ∀ l ∈ (kToYAlpha (T := T) hKY).range, y * l * y⁻¹ ∈ (kToYAlpha (T := T) hKY).range := by
  have hinj := conjNormal_yAlpha_injective hX hnab
  set R' := (rAlpha M X T c).map (MulAut.conjNormal (H := yAlpha M X T c)) with hR'def
  have hR'inn := rAut_inf_innAut_eq_bot hX hnab hD
  have hR'1 : R' ≠ ⊥ := by
    intro h
    apply rAlpha_ne_bot hset hX hYK
    rwa [hR'def, Subgroup.map_eq_bot_iff_of_injective _ hinj] at h
  have hR'card : Nat.card R' = 2 := by
    have h1 : 1 < Nat.card R' := (Subgroup.one_lt_card_iff_ne_bot _).mpr hR'1
    omega
  haveI : Nontrivial ↥R' := (Subgroup.nontrivial_iff_ne_bot _).mpr hR'1
  obtain ⟨⟨u, huR'⟩, hu1⟩ := exists_ne (1 : ↥R')
  have hu2 : orderOf u = 2 := by
    have hdvd : orderOf (⟨u, huR'⟩ : ↥R') ∣ 2 := by
      have h := orderOf_dvd_natCard (⟨u, huR'⟩ : ↥R')
      rwa [hR'card] at h
    rw [Subgroup.orderOf_mk] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      apply hu1
      rw [orderOf_eq_one_iff] at h
      exact Subtype.ext h
    · exact h
  have huu : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu2, sq] at h
    exact h
  have hout : u ∉ (MulAut.conj : ↥(yAlpha M X T c) →* MulAut ↥(yAlpha M X T c)).range := by
    intro h
    have h' : u ∈ R' ⊓ (MulAut.conj : ↥(yAlpha M X T c) →* MulAut ↥(yAlpha M X T c)).range :=
      ⟨huR', h⟩
    rw [hR'inn, Subgroup.mem_bot] at h'
    exact hu1 (Subtype.ext h')
  obtain ⟨r, hr, rfl⟩ := huR'
  have hRcard : Nat.card (rAlpha M X T c) = 2 := by
    rw [← Subgroup.card_map_of_injective hinj]
    exact hR'card
  have hr2 : orderOf r = 2 := by
    rw [← orderOf_injective _ hinj r]
    exact hu2
  have hRgen : Subgroup.zpowers r = rAlpha M X T c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hr) ?_
    rw [Nat.card_zpowers, hr2, hRcard]
  have hKR : kAlpha M X T c ⊓ rAlpha M X T c = ⊥ := by
    rw [eq_bot_iff, ← hD]
    exact fun z hz => ⟨hz.2, kAlpha_le_yAlpha hset hX hz.1⟩
  have hfix := range_le_fixedSubgroup_of_commute hKY
    (commute_of_kAlpha_inf_rAlpha_eq_bot hset hKR)
  refine ⟨r, hr, hRcard, huu, hout, hfix _ ⟨r, hr, rfl⟩, ?_⟩
  intro y hy l hl
  have hry := commute_of_mem_fixedSubgroup hy
  have hyN : Subtype.val y ∈ Subgroup.normalizer (SetLike.coe (rAlpha M X T c)) := by
    rw [← hRgen]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute (Subtype.val y) r := hry.symm
    rw [(hc.zpow_right n).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers r n
  have hyK := normalizer_rAlpha_le_normalizer_kAlpha hset hX hyN
  have hlK : Subtype.val l ∈ kAlpha M X T c := by
    rw [← map_range_kToYAlpha hKY]
    exact ⟨l, hl, rfl⟩
  have hmem := (Subgroup.mem_normalizer_iff.mp hyK _).mp hlK
  rw [← map_range_kToYAlpha hKY] at hmem
  obtain ⟨l', hl', hl'e⟩ := hmem
  have hl'eq : l' = y * l * y⁻¹ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hl'e)
  rw [← hl'eq]
  exact hl'

theorem pow_eq_five_or_seven_of_kAlpha_mulEquiv
    (hset : Setting204 G A M L N c T i j P) (hKY : kTwenty M c ≤ yTwenty X c)
    {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (he : 1 ≤ e)
    (eK : ↥(kToYAlpha (T := T) hKY).range ≃* CFSG.GH74.GLS.IVK.L2 (GaloisField p e)) :
    p ^ e = 5 ∨ p ^ e = 7 := by
  have hp := (Fact.out : p.Prime)
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    push Not at h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  have hFcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hq5 : 5 ≤ p ^ e := le_trans hp5 (Nat.le_self_pow (by omega) p)
  have hF : CFSG.GH74.GLS.IVK.L2Field (GaloisField p e) := by
    refine ⟨?_, ?_⟩
    · rw [hFcard]
      exact (hp.odd_of_ne_two hp2).pow
    · omega
  have hKperf := isPerfect_range_kToYAlpha hset hKY
  obtain ⟨φ, hφ⟩ := exists_surjective_kBar hset hKY
  haveI : Group.IsPerfect ↥(kToYAlpha (T := T) hKY).range := hKperf
  set τ : ↥(⊤ : Subgroup ↥(kToYAlpha (T := T) hKY).range) ≃* ↥(kToYAlpha (T := T) hKY).range :=
    Subgroup.topEquiv with hτ
  have hTperf : Group.IsPerfect ↥(⊤ : Subgroup ↥(kToYAlpha (T := T) hKY).range) :=
    Group.IsPerfect.ofSurjective (f := τ.symm.toMonoidHom) τ.symm.surjective
  have hT1 : (⊤ : Subgroup ↥(kToYAlpha (T := T) hKY).range) ≠ ⊥ := by
    have : Nontrivial ↥(kToYAlpha (T := T) hKY).range :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr (range_kToYAlpha_ne_bot hset hKY)
    exact top_ne_bot
  obtain ⟨-, -, hcard⟩ := L2OddGroup.isSimpleGroup_and_card_of_surjective hF eK hTperf hT1
    (φ.comp τ.toMonoidHom) (hφ.comp τ.surjective)
    hset.kType.symm
  rw [Subgroup.card_top] at hcard
  have hL2 := CFSG.GH74.GLS.IVK.ivk_1_2b (GaloisField p e) hF _ eK
  rw [hFcard] at hL2
  have hev : 2 ∣ p ^ e * ((p ^ e) ^ 2 - 1) := by
    have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
    have : Even ((p ^ e) ^ 2 - 1) := by
      have h1 : Odd ((p ^ e) ^ 2) := hodd.pow
      exact Nat.Odd.sub_odd h1 odd_one
    exact Dvd.dvd.mul_left (even_iff_two_dvd.mp this) _
  have h2 : p ^ e * ((p ^ e) ^ 2 - 1) = 2 * Nat.card ↥(kToYAlpha (T := T) hKY).range := by
    rw [hL2, Nat.mul_div_cancel' hev]
  have harith := @five_or_seven_of_mul_sq_sub_one (p ^ e)
  rcases hcard with h | h
  · exact Or.inl (harith.1 (by rw [h2, h]))
  · exact Or.inr (harith.2 (by rw [h2, h]))

theorem covered_of_asc1411_cyclic (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    {Lm : Type} [Group Lm] (eY : ↥(yAlpha M X T c) ≃* Lm)
    (hcyc : IsCyclic ↥(rAlpha M X T c))
    (h1411 : ∀ (X' : Type) [Group X'] [Finite X'] (L' S' : Subgroup X'), Hyp1411 X' L' S' →
      Nonempty (L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X')) ≃* Lm) →
      IsCyclic ↥(S'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X'))) →
      ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S' i₁).Normal ∧
        (Sec18.fourChar S' i₂).Normal) :
    CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j := by
  obtain ⟨G₀, hG₀⟩ := exists_minimal_coverYR M X T c
  obtain ⟨hhyp, Ψ, hS, hL⟩ := hyp1411_of_simple hset hX hnab hG₀
  have hLiso : Nonempty ((perfectResidual ↥G₀).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀)) ≃*
      Lm) :=
    ⟨(Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
      ((MulEquiv.subgroupCongr hL).trans eY)⟩
  have hScyc : IsCyclic ↥(((CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)).subgroupOf G₀).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥G₀))) := by
    have e₁ := (Subgroup.equivMapOfInjective _ Ψ.toMonoidHom Ψ.injective).trans
      (MulEquiv.subgroupCongr hS)
    exact isCyclic_of_surjective e₁.symm.toMonoidHom e₁.symm.surjective
  obtain ⟨i₁, i₂, h12, h1, h2, hn1, hn2⟩ := h1411 ↥G₀ _ _ hhyp hLiso hScyc
  exact covered_of_fourChar_normal hset hX
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1 hG₀ h12 h1 h2 hn1 hn2

section Rank


theorem eq_one_of_yAlpha_mulEquiv_U3 (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 1 ≤ e)
    (eY : ↥(yAlpha M X T c) ≃* projSU 3 p e) : e = 1 := by
  have hp := (Fact.out : p.Prime)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 p e := by
    refine ⟨hp, he, le_rfl, fun h => ?_⟩
    have h2 : p ^ e = 2 := congrArg Prod.snd h
    have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    omega
  have hmod := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm eY
  have hrk := pRank_yAlpha_le_two hset hX hnab hp hp5
  obtain ⟨-, -, h⟩ := CFSG.SectionRank.classical_model_rank (by omega) hmod
  rcases h with ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | h
  · exact absurd h (by decide)
  · omega
  · omega
  · exact absurd h (by decide)
  · omega

end Rank

end AscBridge

section Main


open AscBridge in
theorem step204AscL3Odd_of_meet (hmeet : Step204AscL3OddMeet) : Step204AscL3Odd := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hL2m hYK h
  by_cases hD : rAlpha M X T c ⊓ yAlpha M X T c = ⊥
  swap
  · exact hmeet G A M L N c T i j P hset X hX hXM hm hL2m hYK h hD
  obtain ⟨hs, hnab⟩ := isSimpleGroup_yAlpha hset hX hm
  haveI := hs
  haveI := yAlpha_normal hX
  have hinj := conjNormal_yAlpha_injective hX hnab
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKY : kTwenty M c ≤ yTwenty X c :=
    Res6.kTwenty_le_yTwenty hset (le_sup_left.trans hKTX)
  have hKperf := isPerfect_range_kToYAlpha hset hKY
  have hK1 := range_kToYAlpha_ne_bot hset hKY
  have hR2 : IsPGroup 2 (rAlpha M X T c) :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype
      (K := yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map _
  have hR'2 : IsPGroup 2 ((rAlpha M X T c).map (MulAut.conjNormal (H := yAlpha M X T c))) :=
    hR2.map _
  have hR'inn := rAut_inf_innAut_eq_bot hX hnab hD
  have hcyc : ∀ {r}, r ∈ rAlpha M X T c → Nat.card (rAlpha M X T c) = 2 →
      IsCyclic ↥(rAlpha M X T c) := fun _ hc => by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card hc
  have hp3 : ∀ {p e : ℕ}, 1 ≤ e → p ^ e % 3 ≠ 0 → p ≠ 3 := by
    intro p e he hq h3
    subst h3
    apply hq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
    rw [pow_add, pow_one, Nat.mul_mod_right]
  rcases h with ⟨p, e, hpF, hp2, he, hq, ⟨eY⟩⟩ | ⟨p, e, hpF, hp2, he, hq, ⟨eY⟩⟩
  ·
    have hp3' : p ≠ 3 := hp3 he (by omega)
    obtain ⟨r, hr, hRcard, hrr, hrout, hfix, hn⟩ :=
      exists_outer_involution_of_inf_eq_bot hset hX hnab hYK hKY hD
        (L3OddGroup.card_le_two_of_inf_inn_eq_bot_L3 hq eY hR'2 hR'inn)
    obtain ⟨eK⟩ := L3OddGroup.nonempty_mulEquiv_L2_of_normal_fixed_L3 hp2 hq eY hrr hrout hKperf
      hK1 hfix hn
    rcases pow_eq_five_or_seven_of_kAlpha_mulEquiv hset hKY hp2 hp3' he eK with h5 | h7
    · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h5
      exact covered_of_asc1411_cyclic hset hX hnab eY (hcyc hr hRcard)
        fun X' _ _ L' S' h hL hS => asc82Item1411_L3_5 X' L' S' h hL hS
    · rw [h7] at hq
      norm_num at hq
  ·
    have hp3' : p ≠ 3 := hp3 he (by omega)
    have hp5 : 5 ≤ p := by
      have h2 := hpF.out.two_le
      by_contra h
      push Not at h
      interval_cases p
      · exact hp2 rfl
      · exact hp3' rfl
      · exact absurd hpF.out (by norm_num)
    obtain rfl := eq_one_of_yAlpha_mulEquiv_U3 hset hX hnab hp5 he eY
    have hq' : p % 3 = 1 := by simpa using hq
    obtain ⟨r, hr, hRcard, hrr, hrout, hfix, hn⟩ :=
      exists_outer_involution_of_inf_eq_bot hset hX hnab hYK hKY hD
        (L3OddGroup.card_le_two_of_inf_inn_eq_bot_U3 hq' eY hR'inn)
    obtain ⟨eK⟩ := L3OddGroup.nonempty_mulEquiv_L2_of_normal_fixed_U3 hq' eY hrr hrout hKperf
      hK1 hfix hn
    rcases pow_eq_five_or_seven_of_kAlpha_mulEquiv hset hKY hp2 hp3' le_rfl eK with h5 | h7
    · rw [pow_one] at h5
      subst h5
      norm_num at hq'
    · rw [pow_one] at h7
      subst h7
      exact covered_of_asc1411_cyclic hset hX hnab eY (hcyc hr hRcard)
        fun X' _ _ L' S' h hL hS => asc82Item1411_U3_7 X' L' S' h hL hS

end Main

end CFSG.RankThree.PartTwo.Sec20
