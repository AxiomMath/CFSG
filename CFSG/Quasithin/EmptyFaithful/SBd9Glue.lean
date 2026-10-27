module

public import CFSG.Quasithin.EmptyFaithful.SBd9Pre
public import CFSG.Quasithin.EmptyFaithful.SBd9Lie
public import CFSG.Quasithin.EmptyFaithful.SBd9Sym

public section

namespace CFSG.Quasithin.SBd9

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem prefix38_of_psl (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hL0 : L = conjClosure L (Sgp153 T V₁))
    (hlist : (∃ n : ℕ, Even n ∧ IsPSL 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
      IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L))
    (hYL : oTwoUpper (Yp ⊓ L) ≠ ⊥) :
    IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L) ∧ Yp = Y153 Mc M ∧
      (Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ∧
        L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I ∧
        Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G)) ∧
      ((V₁ ≤ Subgroup.centralizer (L : Set G) ∧
          (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) ∧ V₂ ≤ oTwoUpper (Yp ⊓ L) ∧
          ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∨
        (V₂ ≤ Subgroup.centralizer (L : Set G) ∧
          (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∧ V₁ ≤ oTwoUpper (Yp ⊓ L) ∧
          ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y)) := by
  obtain ⟨n, hn2, hmodel⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n (↥L ⧸ Subgroup.center ↥L) := by
    rcases hlist with ⟨n, hev, h⟩ | h
    · have h1 : 1 ≤ n := h.1.2.1
      obtain ⟨m, hm⟩ := hev
      exact ⟨n, by omega, h⟩
    · exact ⟨2, le_rfl, h⟩
  have hQ := sylow_inf_Sgp c hL0
  have hLie : LieL3 L (Sgp153 T V₁ ⊓ L) (2 ^ n) :=
    lieL3_of_psl hn2 c.c33.quasisimple c.c33.center_eq hQ hmodel
  obtain ⟨hn, hY, hcase⟩ := prefix38 h113 h37 h38 c hL0 hn2 hLie hYL
  subst hn
  exact ⟨hmodel, hY, ⟨borel_stage h37 h38 c hL0 hLie, borel_le_MI h37 h38 c hL0 hLie,
    sylow_le_centralizer_V h37 h38 c hL0 hLie⟩, hcase⟩

@[expose] def Input15338Mid : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) →
      IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L) → oTwoUpper (Yp ⊓ L) ≠ ⊥ →
      (∃ y ∈ Yp, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
        Yp = oTwoUpper (Yp ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Yp) → ¬ Yp ≤ L →
      I ≤ Subgroup.normalizer (L : Set G) → Yp = Y153 Mc M →
      Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) →
      L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I →
      Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G) →
      V₁ ≤ Subgroup.centralizer (L : Set G) →
      (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) → V₂ ≤ oTwoUpper (Yp ⊓ L) →
      (¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) →
        V₁ = centerOf L ∧ I = Subgroup.normalizer (V₁ : Set G)

@[expose] def Input15338Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) →
      IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L) → oTwoUpper (Yp ⊓ L) ≠ ⊥ →
      (∃ y ∈ Yp, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
        Yp = oTwoUpper (Yp ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Yp) → ¬ Yp ≤ L →
      I ≤ Subgroup.normalizer (L : Set G) → Yp = Y153 Mc M →
      Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) →
      L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I →
      Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G) →
      V₁ ≤ Subgroup.centralizer (L : Set G) →
      (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) → V₂ ≤ oTwoUpper (Yp ⊓ L) →
      (¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) → False

theorem input15338_of_rest (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hrank : Lemma122Rank) (kR : RankOneFamilies153) (kRest : Input15338Rest) : Input15338 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c37 hr
  by_contra hY
  have hq := c.hyp.hyp.qtfe
  have hLI := c.c33.mem
  rcases c37 with h1 | ⟨hL0, hlist, -⟩ | ⟨hL0, hlist, hYL, hy⟩
  ·
    have hn := lemma_1_2_2_b hq.qtke hq.simple hq.nonabelian h37 h38 hrank c.inH.1.2 hLI
      Nat.prime_three (by norm_num) hr
    exact hY (h1.trans (S153I.conjClosure_le_of_normal (le_of_mem_cComp hLI)
      (le_sup_right.trans c.inH.1.1) hn))
  ·
    have h := kR ↥L (S153I.isPGroup_two_center_of_center_eq c.c33.center_eq) hlist
    rw [pRank_top_subtype] at h
    omega
  ·
    have hNL : I ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hLI)).mp
        (lemma_1_2_2_b hq.qtke hq.simple hq.nonabelian h37 h38 hrank c.inH.1.2 hLI Nat.prime_three
          (by norm_num) hr)
    obtain ⟨hn2, hYY, ⟨hB, hBM, hQV⟩, hcase⟩ := prefix38_of_psl h113 h37 h38 c hL0 hlist hYL
    rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact kRest G T Mc M V₁ V₂ Yp I L t c hL0 hn2 hYL hy hY hNL hYY hB hBM hQV h1 h2 h3 h4
    ·
      have hS := sgp153_swap c.hyp.hyp c.hyp.decomp
      have c' := ctxComp2_swap c hYY
      have hL0' : L = conjClosure L (Sgp153 T V₂) := by rw [hS]; exact hL0
      rw [← hS] at hB hBM hQV
      exact kRest G T Mc M V₂ V₁ Yp I L t c' hL0' hn2 hYL hy hY hNL hYY hB hBM hQV h1 h2 h3 h4

end CFSG.Quasithin.SBd9
