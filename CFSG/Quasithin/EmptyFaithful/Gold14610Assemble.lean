module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Props
public import CFSG.Quasithin.EmptyFaithful.S152YF
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.Quasithin.EmptyFaithful.T1531InspBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gold14610

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_eq_self_of_perfect {K : Subgroup G} (hK : ⁅K, K⁆ = K) : oTwoUpper K = K := by
  refine le_antisymm (oTwoUpper_le K) ?_
  let N : Subgroup ↥K := (oTwoUpper K).subgroupOf K
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_oTwoUpper (X := K) (g := (g : G)) (Subgroup.le_normalizer g.2) hn
    simpa using this⟩
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  have hP : IsPGroup 2 (↥K ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper K g.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have : Group.IsNilpotent (↥K ⧸ N) := hP.isNilpotent
  have : Subsingleton (↥K ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥K ⧸ N) ‹_›
  intro g hg
  have : (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at this
  exact this

theorem eq_oTwoUpper_of_perfect {I K S : Subgroup G} (hN : I ≤ Subgroup.normalizer (K : Set G))
    (hperf : ⁅K, K⁆ = K) (hS : IsPGroup 2 ↥S) (hsup : I = K ⊔ S) : K = oTwoUpper I := by
  have hSN : S ≤ Subgroup.normalizer (K : Set G) := (hsup ▸ le_sup_right : S ≤ I).trans hN
  rw [hsup]
  exact (oTwoUpper_sup_eq (oTwoUpper_eq_self_of_perfect hperf).symm hS hSN).symm

omit [Finite G] in
theorem isAlt_of_isAltBlockType {K : Subgroup G} {m : ℕ} (h : IsAltBlockType K m) :
    IsAlt m (OTwoQuot K) := by
  obtain ⟨-, α, hsurj, hker, -⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj))⟩

omit [Finite G] in
theorem isAlt_seven_of_isExcA7Block {K : Subgroup G} (h : IsExcA7Block K) :
    IsAlt 7 (OTwoQuot K) := by
  obtain ⟨-, ⟨α, hsurj, hker⟩, -⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj))⟩

theorem input14610ListW_of_pieces (p0 : Gold14610NoCase12) (p1 : Gold14610Lift)
    (p3 : Gold14610Compare) (p5 : Gold14610BlockOrders) : Input14610ListW := by
  intro G _ _ T M H u I I₂ h27 c hsyl hLT hT hF
  obtain ⟨h1, h1', h2⟩ := p0 G T M H u I I₂ c hsyl hLT hT
  obtain ⟨K, hK⟩ := p1 G T M H u I I₂ c hsyl hLT hT hF h1 h1' h2
  have S : Setting146 G T M := c.setting
  obtain ⟨hRad, hSyl⟩ := S152Y.c23_of_facts c hsyl hLT
  have hSQ := S.isSQTKTC_of_pCoreOf_ne_bot c.hI.1.1.2
  set R₁ : Subgroup G := pCoreOf 2 (i1Of1469 T M I) with hR₁
  have hyp : HypC23 I R₁ (M ⊓ I) :=
    { sqtk := (show SQTKGroup ↥I from ⟨hSQ.2, hSQ.1⟩)
      radical := hRad
      le := inf_le_right
      cgs := S152Y.cgsIn_le_of_CGS_le' c.c1
      sylow := hSyl }
  have hct : CharTwo K := CharTwo.of_normal c.c4 hK.le
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hK.le).mpr hK.normal)
  have hRN : R₁ ≤ Subgroup.normalizer (K : Set G) := hRad.1.trans hK.normal
  have hnot : ¬ K ≤ M ⊓ I := fun h => hK.not_le (h.trans inf_le_left)
  have hC := c27Concl_of_statement h27 hyp hK.comp hK.quasi hct hnot hRN rfl
  obtain ⟨hAllowed, hn3⟩ :=
    p3 G I R₁ (M ⊓ I) K _ hC hK.comp hK.quasi hct hK.le hK.normal hRN hK.cat
  have hindex : I = K ⊔ (T ⊓ I) := hK.index.resolve_right hn3
  have hKeq : K = oTwoUpper I :=
    eq_oTwoUpper_of_perfect hK.normal (perfect_of_mem_cComp hK.comp) hsyl.2.1 hindex
  rw [← hKeq]
  refine ⟨?_⟩
  rcases hAllowed with hL32 | ⟨hb, hHat | hG2 | h6 | h7 | hE⟩
  · exact Or.inl hL32
  · exact Or.inr ⟨hb, Or.inl hHat⟩
  · exact Or.inr ⟨hb, Or.inr (Or.inl hG2)⟩
  · exact Or.inr ⟨hb, Or.inr (Or.inr (Or.inl ⟨isAlt_of_isAltBlockType h6, (p5 G K).1 h6⟩))⟩
  · exact Or.inr ⟨hb, Or.inr (Or.inr (Or.inr
      ⟨isAlt_of_isAltBlockType h7, Or.inr ((p5 G K).2.1 h7)⟩))⟩
  · exact Or.inr ⟨hb, Or.inr (Or.inr (Or.inr
      ⟨isAlt_seven_of_isExcA7Block hE, Or.inl ((p5 G K).2.2 hE)⟩))⟩

end Gold14610

end CFSG.Quasithin
