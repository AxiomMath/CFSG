module

public import CFSG.Quasithin.EmptyFaithful.S153D51

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def Input21Rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    (IsAltBlockType L 6 ∨ IsG2Block L ∨ IsHatA6Block L ∨ IsAltBlockType L 7 ∨ IsExcA7Block L) →
      CFSG.Open.pRank 3 L = 2

@[expose] def Input21ProperRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S₀ X : Subgroup G),
    (IsAltBlockType L 6 ∨ IsG2Block L) → IsSylowTwoOf S₀ L → S₀ ≤ X → X ≤ L → X ≠ L →
      CFSG.Open.pRank 3 X ≤ 1

@[expose] def Input15321Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → Concl15317 T V₁ Yp I L → ¬ IsLin2Block I L →
      ¬ IsLin2Quot L → ¬ IsSL3Quot L → ¬ IsSp4Quot L →
        ¬ IsHatA6Block L ∧ ¬ IsAltBlockType L 7 ∧ ¬ IsExcA7Block L

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem quot_equiv_autOn_of_ctx (hcover : AsA36NoOddCover)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hH : IsL345Type ↥(autOn L (VL153 T V₁ Yp L))) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L (VL153 T V₁ Yp L))) := by
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hRL := c.c16.R_norm
  have hO := pCoreOf_sup_R153_le c.facts hLI hLq hRL
  obtain ⟨⟨h1a, -, h1c⟩, -, -⟩ := c.c16.desc
  have hLN : L ≤ Subgroup.normalizer (VL153 T V₁ Yp L : Set G) := le_sup_left.trans h1c.2.1
  have hker : pCoreOf 2 L ≤ Subgroup.centralizer (VL153 T V₁ Yp L : Set G) :=
    (pCoreOf_le_pCoreOf_sup hRL).trans fun x hx => (h1a hx).2
  have hnt : ¬ L ≤ Subgroup.centralizer (VL153 T V₁ Yp L : Set G) := fun hc' =>
    not_le_centralizer_VZ c.ctx.hyp (le_of_mem_cComp hLI) hLn
      (hc'.trans (Subgroup.centralizer_le (VZ_le_VL153 c.ctx.hyp c.ctx c.facts hLI hO)))
  have hsqI : SQTKGroup ↥I :=
    (lemma_15_3_15_one c.ctx.hyp c.ctx.inH c.facts).sqtk
  have hsq : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    sqtkGroup_quot_pCore (B5.sqtk_of_le hsqI (le_of_mem_cComp hLI))
  exact nonempty_quot_mulEquiv_autOn hcover hLN hLq hsq hker hnt hH

theorem Yp_le_of_concl15317 (hcover : AsA36NoOddCover) (c : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (c17 : Concl15317 T V₁ Yp I L) (hrank : CFSG.Open.pRank 3 L = 2) (n20 : ¬ IsSL3Quot L) :
    Yp ≤ L := by
  rcases c17 with ⟨h1, -⟩ | ⟨-, hY, hθ⟩ | ⟨-, n, F, hF, hFin, hn, hcard, ⟨e⟩⟩
  · omega
  · exact hθ ▸ hY
  · exfalso
    have hH : IsL345Type ↥(autOn L (VL153 T V₁ Yp L)) :=
      Or.inl ⟨n, F, hF, Finite.of_fintype F, by rw [Nat.card_eq_fintype_card]; exact hcard, ⟨e⟩⟩
    obtain ⟨e'⟩ := quot_equiv_autOn_of_ctx hcover c hH
    have hn1 : 1 < n := by
      have h2 : 2 ≤ 2 ^ n := by
        rw [← hcard]
        exact Fintype.one_lt_card
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, pow_zero] at h2
        omega
      · obtain ⟨k, hk⟩ := hn
        omega
    exact n20 ⟨n, F, hF, hFin, hn1, hcard, ⟨e'.trans e⟩⟩

theorem not_A6_G2_of_kernels (hcover : AsA36NoOddCover) (kR : Input21Rank)
    (kP : Input21ProperRank) (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (c17 : Concl15317 T V₁ Yp I L)
    (n20 : ¬ IsSL3Quot L) (hblock : IsAltBlockType L 6 ∨ IsG2Block L) : False := by
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hF : Facts15311 T M V₁ Yp I := c.facts
  obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hrk : CFSG.Open.pRank 3 L = 2 :=
    kR G L (hblock.elim Or.inl fun h => Or.inr (Or.inl h))
  have hYL : Yp ≤ L := Yp_le_of_concl15317 hcover c c17 hrk n20
  have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLI) hF.sylow
  have hXL : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≤ L := sup_le hYL inf_le_right
  have hXM : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≤ M :=
    sup_le (hh.Yp_le_Y153.trans (Y153_le Mc M)) (inf_le_left.trans (inf_le_left.trans hh.hyp.T_le))
  have hXne : Yp ⊔ (Sgp153 T V₁ ⊓ L) ≠ L := fun h => hLn (le_inf (h ▸ hXM) hLle)
  have h1 := kP G L (Sgp153 T V₁ ⊓ L) (Yp ⊔ (Sgp153 T V₁ ⊓ L)) hblock hSL le_sup_right hXL hXne
  have h2 : CFSG.Open.pRank 3 Yp ≤ CFSG.Open.pRank 3 (Yp ⊔ (Sgp153 T V₁ ⊓ L)) :=
    CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left
  have h3 := c.ctx.rank
  omega

theorem input15321_of_kernels (hcover : AsA36NoOddCover) (kR : Input21Rank)
    (kP : Input21ProperRank) (kRest : Input15321Rest) : Input15321 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c17 n18 n19 n20a n20b
  obtain ⟨hHat, hA7, hExc⟩ := kRest G T Mc M V₁ V₂ Yp I L t c c17 n18 n19 n20a n20b
  refine ⟨fun h => not_A6_G2_of_kernels hcover kR kP c c17 n20a (Or.inl h) |>.elim,
    fun h => not_A6_G2_of_kernels hcover kR kP c c17 n20a (Or.inr h) |>.elim, hHat, hA7, hExc⟩

end S153D

end CFSG.Quasithin
