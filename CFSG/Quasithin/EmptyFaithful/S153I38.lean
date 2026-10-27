module

public import CFSG.Quasithin.Vol2.Ch1Rank
public import CFSG.Quasithin.EmptyFaithful.S153D35

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def RankOneFamilies153 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPGroup 2 ↥(Subgroup.center X) →
    ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n (X ⧸ Subgroup.center X)) ∨
      (∃ n : ℕ, Even n ∧ IsPSU 3 2 n (X ⧸ Subgroup.center X)) ∨
      IsPSL 3 2 1 (X ⧸ Subgroup.center X)) →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1

@[expose] def RankTwoFamilies153 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPGroup 2 ↥(Subgroup.center X) →
    ((∃ n : ℕ, Even n ∧ IsPSL 3 2 n (X ⧸ Subgroup.center X)) ∨ IsPSL 3 2 2 (X ⧸ Subgroup.center X)) →
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

@[expose] def Input15339Diag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L ≠ conjClosure L (Sgp153 T V₁) →
      Yp ≤ conjClosure L (Sgp153 T V₁) → CFSG.Open.pRank 3 L = 1 → False

namespace S153I

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem isPGroup_two_center_of_center_eq (hc : centerOf L = pCoreOf 2 L) :
    IsPGroup 2 ↥(Subgroup.center ↥L) := by
  have hle : Subgroup.center ↥L ≤ CFSG.pCore 2 ↥L := by
    intro z hz
    rw [S153D.mem_pCore_iff]
    rw [← hc]
    refine ⟨z.2, ?_⟩
    show (z : G) ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_le hle

omit [Finite G] in
theorem conjClosure_le_of_normal {S : Subgroup G} (hLI : L ≤ I) (hSI : S ≤ I)
    (hn : (L.subgroupOf I).Normal) : conjClosure L S ≤ L := by
  have hN := (Subgroup.normal_subgroupOf_iff_le_normalizer hLI).mp hn
  exact conjClosure_le fun s hs z hz => (Subgroup.mem_normalizer_iff.mp (hN (hSI hs)) z).mp hz

theorem pRank_eq_one_of_ne (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hrank : Lemma122Rank)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hne : L ≠ conjClosure L (Sgp153 T V₁)) :
    CFSG.Open.pRank 3 L = 1 := by
  have hq := c.hyp.hyp.qtfe
  have h1 : 1 ≤ CFSG.Open.pRank 3 L := c.c34.rank
  have h2 : CFSG.Open.pRank 3 L ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) (le_of_mem_cComp c.c33.mem)).trans
      (pRank_le_two_of_pCoreOf_ne_bot hq.qtke c.inH.1.2 Nat.prime_three (by norm_num))
  by_contra h
  have hr : CFSG.Open.pRank 3 L = 2 := by omega
  have hn := lemma_1_2_2_b hq.qtke hq.simple hq.nonabelian h37 h38 hrank c.inH.1.2 c.c33.mem
    Nat.prime_three (by norm_num) hr
  exact hne (le_antisymm (le_conjClosure _ _)
    (conjClosure_le_of_normal (le_of_mem_cComp c.c33.mem) (le_sup_right.trans c.inH.1.1) hn))

theorem input15339_of_named_inputs (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hrank : Lemma122Rank)
    (kD : Input15339Diag) : Input15339 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c37 _
  by_contra hne
  have hY : Yp ≤ conjClosure L (Sgp153 T V₁) := by
    rcases c37 with h | ⟨hL0, -⟩ | ⟨hL0, -⟩
    · exact h
    · exact absurd hL0 hne
    · exact absurd hL0 hne
  exact kD G T Mc M V₁ V₂ Yp I L t c hne hY (pRank_eq_one_of_ne h37 h38 hrank c hne)

end S153I

end CFSG.Quasithin
