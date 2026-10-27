module

public import CFSG.Quasithin.EmptyFaithful.R3c9Ctx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def Input15340TwoNoU34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) →
      CFSG.Open.pRank 3 L = 1 →
      ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
          (∃ n : ℕ, Even n ∧ n ≠ 2 ∧ IsPSU 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
          IsPSL 3 2 1 (↥L ⧸ Subgroup.center ↥L)) →
      Yp = oTwoUpper (Yp ⊓ L) ⊔ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) →
      padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ L))) = 1 →
      padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))) = 1 →
      IsElemAbelianOfRank 3 2 (OTwoQuot Yp) →
      ¬ Yp ≤ L → False

@[expose] def Input15340U34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) →
      CFSG.Open.pRank 3 L = 1 →
      IsPSU 3 2 2 (↥L ⧸ Subgroup.center ↥L) →
      Yp = oTwoUpper (Yp ⊓ L) ⊔ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) →
      padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ L))) = 1 →
      padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))) = 1 →
      IsElemAbelianOfRank 3 2 (OTwoQuot Yp) →
      ¬ Yp ≤ L → False

namespace R3c9

section Main

theorem input15340TwoNoU34_holds (h113 : StageLemma14113)
    (hnine : ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Hyp153 G T Mc M →
      VZ T M < pCoreOf 2 (Y153 Mc M))
    (hlist : Lemma115_3_List) (hA : R3c2.Input15333Two) : Input15340TwoNoU34 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hr hfam hY h3L h3C hE9 hnot
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  obtain ⟨z, hz⟩ := hA G T Mc M V₁ V₂ Yp I t c.toCtxComp
  have hcomp : IsComponentIn L I :=
    Id2519.isComponentIn_of_mem_cComp c.c33.mem c.c33.quasisimple
  have hsimpleG : IsSimpleGroup G := hq.simple
  have hcore : QTKECore G := qtkeCore_of_cat hq.nonabelian hq.qtke
  have hcases : Lemma115Cases L z :=
    (Lemma115_3_List.component_cases hlist hsimpleG hq.nonabelian hcore hz hcomp).2.2.2
  have hLs : IsSimpleGroup ↥L := isSimple_of_lemma115_rankOne hcases c.c33.center_eq hr
  have hperf : Group.IsPerfect ↥L := c.c33.quasisimple.1
  let eC := R3c3.quotCenterEquivOfSimple hLs hperf
  have hfam' : (∃ n : ℕ, Even n ∧ IsPSL 2 2 n ↥L) ∨ (∃ n : ℕ, Even n ∧ n ≠ 2 ∧ IsPSU 3 2 n ↥L) ∨
      IsPSL 3 2 1 ↥L := by
    rcases hfam with ⟨n, hn, h⟩ | ⟨n, hn, hn2, h⟩ | h
    · exact Or.inl ⟨n, hn, R3c3.isPSL_of_mulEquiv eC.symm h⟩
    · exact Or.inr (Or.inl ⟨n, hn, hn2, R3c3.isPSU_of_mulEquiv eC.symm h⟩)
    · exact Or.inr (Or.inr (R3c3.isPSL_of_mulEquiv eC.symm h))
  exact noU34_core c hL0 hLs hY h3L h3C hE9 h113 hnine hfam'

end Main

end R3c9

namespace S153I

theorem input15340_of_narrow (kR : RankTwoFamilies153) (k1 : Input15340TwoNoU34)
    (k2 : Input15340U34) : Input15340 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c37 h38 hL0
  by_contra hY
  have hq := c.hyp.hyp.qtfe
  have h1 : 1 ≤ CFSG.Open.pRank 3 L := c.c34.rank
  have h2 : CFSG.Open.pRank 3 L ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) (le_of_mem_cComp c.c33.mem)).trans
      (pRank_le_two_of_pCoreOf_ne_bot hq.qtke c.inH.1.2 Nat.prime_three (by norm_num))
  have hr1 : CFSG.Open.pRank 3 L = 1 := by
    rcases (by omega : CFSG.Open.pRank 3 L = 1 ∨ CFSG.Open.pRank 3 L = 2) with h | h
    · exact h
    · exact absurd (h38 h) hY
  rcases c37 with h | ⟨-, hlist, hdec, h3L, h3C, hE9⟩ | ⟨-, hlist, -⟩
  · exact hY (hL0 ▸ h)
  · rcases hlist with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h
    · exact k1 G T Mc M V₁ V₂ Yp I L t c hL0 hr1 (Or.inl ⟨n, hn, h⟩) hdec h3L h3C hE9 hY
    · by_cases h2 : n = 2
      · subst h2
        exact k2 G T Mc M V₁ V₂ Yp I L t c hL0 hr1 h hdec h3L h3C hE9 hY
      · exact k1 G T Mc M V₁ V₂ Yp I L t c hL0 hr1 (Or.inr (Or.inl ⟨n, hn, h2, h⟩)) hdec h3L h3C hE9
          hY
    · exact k1 G T Mc M V₁ V₂ Yp I L t c hL0 hr1 (Or.inr (Or.inr h)) hdec h3L h3C hE9 hY
  · have h := kR ↥L (isPGroup_two_center_of_center_eq c.c33.center_eq) hlist
    rw [pRank_top_subtype] at h
    omega

end S153I

end CFSG.Quasithin
