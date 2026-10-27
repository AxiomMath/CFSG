module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveReduce
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCases
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoAltFive
open CFSG.ComponentClassification.RankTwoAlt
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

@[expose] def Asc08Lemma310LocalNF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)) →
    Odd (Nat.card (center ↥A)) → ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    (∀ x : G, ¬ rightConjugate R x ≤ A) → rankTwoX A ⊔ R = ⊤ →
    ∀ (g : G) (T V₀ : Subgroup G), Case310Local A R g T V₀ →
      NativeSporadic.IsSporadic (rankTwoX A) .J2 ∨
        (NativeSporadic.IsSporadic (rankTwoX A) .M12 ∧
          ∃ t : G, t ^ 2 = 1 ∧ t ∈ normalizer (A : Set G) ∧ t ∈ normalizer (R : Set G) ∧
            ¬ ∃ a ∈ A, ∀ y ∈ A, t * y * t⁻¹ = a * y * a⁻¹)

theorem asc08Lemma310LocalNF_of_cases
    (ha : RankTwoAltFive.Asc310IIa) (hb : RankTwoAltFive.Asc310IIb) :
    Asc08Lemma310LocalNF := by
  intro G _ _ A hH hO hA5 hodd R hR hno hXR g T V₀ hloc
  have hS := RankTwoAltFive.setting310_ofNF hH hO hA5 hodd hR hno hXR hloc
  by_cases hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G)
  · exact Or.inr (hb G A R g T V₀ hS hIIb)
  · obtain ⟨y, hy, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hIIb
    have hX := RankTwoAltFive.rankTwoX_eq_top_of_IIa hR hS.elemR hS.cardR hXR (mem_inf.mp hy).1
      (mem_inf.mp hy).2 hyC
    exact Or.inl (ha G A R g T V₀ hS hX hIIb)

@[expose] def Asc08Lemma310NF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)) →
    Odd (Nat.card (center ↥A)) → ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    (∀ x : G, ¬ rightConjugate R x ≤ A) →
      NativeSporadic.IsSporadic (rankTwoX A) .J2 ∨
        (NativeSporadic.IsSporadic (rankTwoX A) .M12 ∧
          ∃ t : G, t ^ 2 = 1 ∧ t ∈ normalizer (A : Set G) ∧ t ∈ normalizer (R : Set G) ∧
            ¬ ∃ a ∈ A, ∀ y ∈ A, t * y * t⁻¹ = a * y * a⁻¹)

theorem asc08Lemma310NF_of_local
    (hL : Asc08Lemma310LocalNF) (h32 : Lemma32) (h332 : Lemma33Two) (hcfg : Section3Config) :
    Asc08Lemma310NF := by
  intro G _ _ A hH hO hA5 hodd R hR hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA5
  have hAperf : commutator ↥A = ⊤ := hH.standard.1.1
  have hZ : center ↥A = ⊥ := RankTwoAlt.center_eq_bot_of_odd_five hAperf e hodd
  let eA : ↥A ≃* A5 :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hA31 : Hyp31 A :=
    ⟨hH.standard, hypIIAlt5 ↥A hAperf ⟨e⟩, hO, by have := hH.rank; omega, hH.not_normal⟩
  have hstd := hH.standard
  obtain ⟨hXF, hXs⟩ := AS76b.asc08Lemma34 G A hA31
  have hXsimple : IsSimpleGroup ↥(rankTwoX A) := by
    rw [show rankTwoX A = CFSG.generalizedFitting G from hXF]
    exact hXs
  set H := rankTwoX A ⊔ R with hHdef
  have hAX : A ≤ rankTwoX A := le_normalClosure
  have hAG₁ : A ≤ H := hAX.trans le_sup_left
  have hRG₁ : R ≤ H := le_sup_right
  have hAc : Nat.card A = 60 := by rw [Nat.card_congr eA.toEquiv, card_A5]
  have hA1 : ∀ {B : Subgroup G}, A ≤ B → B = ⊥ → False := by
    intro B hAB hB1
    rw [hB1, le_bot_iff] at hAB
    apply hH.not_normal
    rw [hAB]
    infer_instance
  have heven : Even (Nat.card (centralizer (A : Set G) ⊓ H : Subgroup G)) := by
    have hR1 : R ≠ ⊥ :=
      AS76b.isSylowOf_ne_bot_of_even hR (AS76b.tightlyEmbedded_centralizer hstd).1
    have h2R : 2 ∣ Nat.card R := by
      rcases hR.isPGroup.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hR1
      · exact h
    exact even_iff_two_dvd.mpr (h2R.trans (Subgroup.card_dvd_of_le (le_inf hR.le hRG₁)))
  have hstd₁ := GMS78.standard_subgroupOf hstd hAG₁ heven
  have hnn : ¬ (A.subgroupOf H).Normal := by
    intro hn
    have hnX : (A.subgroupOf (rankTwoX A)).Normal := by
      constructor
      intro a ha x
      have h1 := hn.conj_mem ⟨(a : G), hAG₁ ha⟩ ha ⟨(x : G), le_sup_left (b := R) x.2⟩
      rw [mem_subgroupOf] at h1 ⊢
      simpa using h1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf (rankTwoX A)) with h | h
    · rw [subgroupOf_eq_bot] at h
      exact hA1 le_rfl (le_bot_iff.mp fun a ha => h.le_bot ⟨ha, hAX ha⟩)
    · apply hH.not_normal
      rw [le_antisymm hAX (subgroupOf_eq_top.mp h)]
      infer_instance
  have hrank₁ : 2 ≤ Open.pRank 2 (centralizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H)) := by
    obtain ⟨U, hUK, hU, hU4⟩ := RankTwoSporadic.exists_four_le_of_two_le_pRank hH.rank
    obtain ⟨c, -, hcU⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR
      (fun v => ⟨1, Subtype.ext (by simpa using hU.2 v v.2)⟩) hUK
    have hEG₁ : rightConjugate U c ≤ H := hcU.trans hRG₁
    have hUc := AS76b.isElemAbelian_rightConjugate hU c
    refine CFSG.SectionRank.le_pRank one_lt_two
      (E := (rightConjugate U c).subgroupOf H) ?_ ?_ ?_
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp (hR.le (hcU (mem_subgroupOf.mp hx))) y
        (mem_subgroupOf.mp hy))
    · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        simpa using
          congrArg Subtype.val (hUc.1.is_comm.comm ⟨((x : ↥H) : G), x.2⟩ ⟨((y : ↥H) : G), y.2⟩)
      · rw [mem_subgroupOf] at hx
        exact Subtype.ext (by simpa using hUc.2 _ hx)
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hU4, ← rightConjugate_card U c]
      exact Nat.card_congr (subgroupOfEquivOfLe hEG₁).toEquiv
  have hH₁ : RankTwoHypNF ↥H (A.subgroupOf H) := ⟨hstd₁, hnn, hrank₁⟩
  let eA₁ : ↥(A.subgroupOf H) ≃* ↥A := subgroupOfEquivOfLe hAG₁
  have hO₁ : standardComponentOddCore ↥H = ⊥ :=
    oddCore_sup_eq_bot hXF hXsimple (by rw [hAc]; decide)
  let e₁ : rankTwoQuot (A.subgroupOf H) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr (center _) (center _) eA₁ (Subgroup.map_center_eq eA₁)).trans e
  have hodd₁ : Odd (Nat.card (center ↥(A.subgroupOf H))) := by
    rwa [Nat.card_congr (Subgroup.centerCongr eA₁).toEquiv]
  have hR₁ : IsSylowOf 2 (R.subgroupOf H) (centralizer ((A.subgroupOf H : Subgroup ↥H) :
      Set ↥H)) := by
    rw [GMS78.centralizer_subgroupOf_eq hAG₁, ← isSylowOf_map_subtype_iff H,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hRG₁,
      inf_eq_left.mpr inf_le_right]
    exact hR.of_le (le_inf hR.le hRG₁) inf_le_left
  have hno₁ : ∀ x : ↥H, ¬ rightConjugate (R.subgroupOf H) x ≤ A.subgroupOf H := by
    intro x hx
    apply hno x
    intro r hr
    have hrH : r ∈ H := by
      have h1 : (x : G) * r * (x : G)⁻¹ ∈ H := hRG₁ ((mem_rightConjugate_iff _ _ _).mp hr)
      have h2 := H.mul_mem (H.mul_mem (H.inv_mem x.2) h1) x.2
      simpa [mul_assoc] using h2
    have h := hx ((mem_rightConjugate_subgroupOf x ⟨r, hrH⟩).mpr hr)
    exact mem_subgroupOf.mp h
  have hle : (rankTwoX (A.subgroupOf H)).map H.subtype ≤ rankTwoX A := by
    rw [map_le_iff_le_comap]
    have : ((rankTwoX A).comap H.subtype).Normal :=
      (normalClosure_normal (s := (A : Set G))).comap _
    exact normalClosure_le_normal fun a ha => hAX (mem_subgroupOf.mp ha)
  have hX₁ : (rankTwoX (A.subgroupOf H)).map H.subtype = rankTwoX A := by
    refine le_antisymm hle ?_
    have hnN : (((rankTwoX (A.subgroupOf H)).map H.subtype).subgroupOf (rankTwoX A)).Normal := by
      constructor
      intro n hn x
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨m, hm, hmn⟩ := hn
      have hx₁ : (x : G) ∈ H := le_sup_left (b := R) x.2
      refine ⟨⟨x, hx₁⟩ * m * ⟨x, hx₁⟩⁻¹, (normalClosure_normal).conj_mem m hm _, ?_⟩
      simp [← hmn]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((rankTwoX (A.subgroupOf H)).map H.subtype).subgroupOf (rankTwoX A)) with h | h
    · exfalso
      rw [subgroupOf_eq_bot] at h
      refine hA1 (B := ⊥) (fun a ha => h.le_bot ⟨?_, hAX ha⟩) rfl
      exact ⟨⟨a, hAG₁ ha⟩, le_normalClosure ha, rfl⟩
    · exact subgroupOf_eq_top.mp h
  have hXR₁ : rankTwoX (A.subgroupOf H) ⊔ R.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, hX₁, subgroupOf_map_subtype, inf_eq_left.mpr hRG₁,
      ← MonoidHom.range_eq_map, range_subtype]
  let eX : ↥(rankTwoX (A.subgroupOf H)) ≃* ↥(rankTwoX A) :=
    ((rankTwoX (A.subgroupOf H)).equivMapOfInjective _ H.subtype_injective).trans
      (MulEquiv.subgroupCongr hX₁)
  have hA31₁ : Hyp31 (A.subgroupOf H) :=
    ⟨hstd₁, hypIIAlt5 _ hstd₁.1.1 ⟨e₁⟩, hO₁, by omega, hnn⟩
  obtain ⟨g, hg, T, hT, hTN, hTR⟩ := exists_sec3 hcfg hA31₁ hR₁
  have hloc := case310Local_of h32 h332 hA31₁ (eA₁.trans eA) hR₁ hno₁ hg hT hTN hTR
  have h1 := hL ↥H (A.subgroupOf H) hH₁ hO₁ ⟨e₁⟩ hodd₁ (R.subgroupOf H) hR₁ hno₁ hXR₁ g T _ hloc
  rcases h1 with ⟨⟨eJ⟩⟩ | ⟨⟨eM⟩, t, ht2, htA, htR, htout⟩
  · exact Or.inl ⟨eX.symm.trans eJ⟩
  refine Or.inr ⟨⟨eX.symm.trans eM⟩, t, by simpa using congrArg Subtype.val ht2, ?_, ?_, ?_⟩
  · rw [← subgroupOf_normalizer_eq hAG₁] at htA
    exact mem_subgroupOf.mp htA
  · rw [← subgroupOf_normalizer_eq hRG₁] at htR
    exact mem_subgroupOf.mp htR
  · rintro ⟨a, ha, hta⟩
    apply htout
    refine ⟨⟨a, hAG₁ ha⟩, ha, fun y hy => Subtype.ext ?_⟩
    simpa using hta y hy

end CFSG.ComponentClassification.RankTwoClassical
