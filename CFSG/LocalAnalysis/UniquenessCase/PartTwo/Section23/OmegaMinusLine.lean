module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveLine
public import CFSG.Quasithin.Background.HStandard
public import CFSG.Quasithin.EmptyFaithful.S146zUF1Ker

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isOmegaMinus_of_natOmegaMinus_four {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {m : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 4 m) :
    IsOmegaMinus ↥H 4 m := by
  obtain ⟨-, K, hKfield, hKfin, b, c, hKcard, hirr, hR⟩ := h
  rw [show (4 / 2 : ℕ) = 2 from rfl] at hR
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  obtain ⟨π₀, hπ₀⟩ := hR
  let π : ↥(StatedOmega (StatedQuadMinus 2 K b c)) →* ↥H := π₀
  have hπ : (CFSG.Quasithin.FFModel.nat
      (StatedOmega (StatedQuadMinus 2 K b c))).RealizesVia H ⊤ ⊥ π := hπ₀
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.exists_mulEquiv_of_realizesVia
    (StatedOmega (StatedQuadMinus 2 K b c)) hπ
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hnat : CFSG.Quasithin.H.natAut (StatedOmega (StatedQuadMinus 2 K b c)) γ = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨v, rfl⟩ := e.surjective x
      rw [CFSG.Quasithin.H.natAut_apply]
      have h2 := he γ v
      rw [hγ] at h2
      simpa using h2.symm
    apply Subtype.ext
    show (γ : Matrix.GeneralLinearGroup (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) = 1
    exact CFSG.Quasithin.H.matHom_injective (by rw [map_one]; exact hnat)
  let P : HypPair (quadMinus 2 K b c) := minusPair K b c (⟨0, by norm_num⟩ : Fin 1)
  have hv₀ : quadMinus 2 K b c (P.e + P.f) ≠ 0 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (Q := quadMinus 2 K b c) (Q₀ := StatedQuadMinus 2 K b c)
    (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c) ⟨P.e + P.f, hv₀⟩
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus 2 K b c)) ≃*
      StatedOmega (StatedQuadMinus 2 K b c) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨by norm_num, K, hKfield, hKfin, b, c, hKcard, hirr, ?_⟩
  change Nonempty (↥H ≃* StatedProj (StatedOmega (StatedQuadMinus 2 K b c)))
  exact ⟨(MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩).symm.trans eΩ.symm⟩

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem ker_phiL_eq_pCore_of_isSimpleGroup (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {k : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) k)
    (hSimple : IsSimpleGroup (Bar2 c.L)) : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L := by
  haveI : IsSimpleGroup (↥c.L ⧸ CFSG.pCore 2 ↥c.L) := hSimple
  haveI : Nontrivial ↥(c.H hV) := hK.2.1 hnat
  have hO : CFSG.pCore 2 ↥c.L ≤ (c.phiL hV).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (c.phiL_eq_one_iff hV x).2
      (c.pCoreOf_le_centralizer_V hV hK hnat (Subgroup.mem_map_of_mem c.L.subtype hx))
  have hkertop : (c.phiL hV).ker ≠ ⊤ := by
    intro htop
    have hbot : (⊤ : Subgroup ↥(c.H hV)) = ⊥ := by
      rw [← MonoidHom.range_eq_top.mpr (c.phiL_surjective hV)]
      exact MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ker_eq_top_iff.mp htop)
    have hne : (⊤ : Subgroup ↥(c.H hV)) ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup ↥(c.H hV))).mp inferInstance
    exact hne hbot
  exact CFSG.Quasithin.S146zU.UF1.ker_eq_of_isSimpleGroup_quotient (c.phiL hV) hO hkertop

theorem nonempty_bar2_mulEquiv_of_isSimpleGroup (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {k : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) k)
    (hSimple : IsSimpleGroup (Bar2 c.L)) : Nonempty (Bar2 c.L ≃* ↥(c.H hV)) := by
  have hker := c.ker_phiL_eq_pCore_of_isSimpleGroup hV hK hnat hSimple
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (c.phiL hV) (c.phiL_surjective hV))⟩

theorem inf_centralizer_V_eq_pCoreOf (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (hK : KOrdNatural) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    c.L ⊓ Subgroup.centralizer (c.V : Set G) = CFSG.Open.pCoreOf 2 c.L := by
  obtain ⟨hV, hnat⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  have hn1 : 1 ≤ CFSG.Open.pRank 2 D.Z := by
    obtain ⟨-, K, hKfield, hKfin, b, q, hKcard, -, -⟩ := hOm
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hKgt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hKcard] at hKgt
    exact Nat.one_le_iff_ne_zero.mpr (Nat.one_lt_two_pow_iff.mp hKgt)
  have hSimple : IsSimpleGroup (Bar2 c.L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two
      (isL2_two_mul_of_isOmegaMinus_four hn1 hOm)
  have hker := c.ker_phiL_eq_pCore_of_isSimpleGroup hV hK hnat hSimple
  ext x
  constructor
  · intro hx
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    have hmem : (⟨x, hxL⟩ : ↥c.L) ∈ (c.phiL hV).ker := by
      rw [MonoidHom.mem_ker]
      exact (c.phiL_eq_one_iff hV ⟨x, hxL⟩).2 hxC
    rw [hker] at hmem
    exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hmem, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hyx]
      exact y.2
    · rw [← hyx]
      exact c.pCoreOf_le_centralizer_V hV hK hnat (Subgroup.mem_map_of_mem c.L.subtype hy)

theorem omegaMinus_lineData (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h209 : S20_9 D) (hK : KOrdNatural) (hA : KTab23a)
    (hB : KTab23b) (hS : KSchurL2) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    ∃ hV : IsElemAbelian 2 c.V, IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) ∧
      IsOmegaMinus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) ∧
      c.L = c.L0 ∧ IsL2 (Bar2 (c.Y0 hV)) (2 * CFSG.Open.pRank 2 D.Z) ∧
      IsL2 (Bar2 c.L0) (2 * CFSG.Open.pRank 2 D.Z) := by
  obtain ⟨hV, hnat⟩ := exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  have hn1 : 1 ≤ CFSG.Open.pRank 2 D.Z := by
    obtain ⟨-, K, hKfield, hKfin, b, q, hKcard, -, -⟩ := hOm
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hKgt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hKcard] at hKgt
    exact Nat.one_le_iff_ne_zero.mpr (Nat.one_lt_two_pow_iff.mp hKgt)
  have hSimple : IsSimpleGroup (Bar2 c.L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two
      (isL2_two_mul_of_isOmegaMinus_four hn1 hOm)
  obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv_of_isSimpleGroup hV hK hnat hSimple
  have hcard : Nat.card ↥(c.H hV) = Nat.card (Bar2 c.L) :=
    (Nat.card_congr e.toEquiv).symm
  have hNatOm : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) :=
    hK.2.2.2 hnat hOm hcard
  have hOmH : IsOmegaMinus ↥(c.H hV) 4 (CFSG.Open.pRank 2 D.Z) :=
    isOmegaMinus_of_natOmegaMinus_four hNatOm
  obtain ⟨P, hP, hL0P⟩ := (h209 h1930 c.L c.hL.1 c.L0).1 ⟨c.hL0, c.hL0L⟩
  have hmin := c.minimal_good_Pstar hV hA h4 h1930 hnat P hP
  have hY0 : Hinf (Pstar c hV P) = c.Y0 hV := c.Hinf_Pstar hV P hP hL0P
  have hTab := hB (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
    (c.sylowStar hV) (c.Tstar hV) (c.Tstar_le_normalizer hV) (c.isPGroup_Tstar hV)
    (c.sylowStar_le_Tstar hV)
  obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11⟩ := hTab
  have h := hT2 ⟨hOmH, hNatOm⟩ (Pstar c hV P) hmin
  have hL2Y : IsL2 (Bar2 (c.Y0 hV)) (2 * CFSG.Open.pRank 2 D.Z) := hY0 ▸ h.2
  have hLL0 : c.L = c.L0 := L_eq_L0_of_Pstar_eq_top c hV hK hnat hP hL0P h.1
  have hL2L0 : IsL2 (Bar2 c.L0) (2 * CFSG.Open.pRank 2 D.Z) :=
    c.isL2_bar2_L0_of hV hK hnat hS hL2Y
  exact ⟨hV, hnat, hOmH, hNatOm, hLL0, hL2Y, hL2L0⟩

end Ctx23L

theorem s23_5_2Omega_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h209 : S20_9 D) (hK : KOrdNatural) (hA : KTab23a)
    (hB : KTab23b) (hS : KSchurL2) (hN : KNshape) : S23_5_2Omega D Ch := by
  intro h1930 c hOm
  obtain ⟨_, _, _, _, hLL0, _, hL2L0⟩ :=
    Ctx23L.omegaMinus_lineData D Ch h2 h3 h4 h209 hK hA hB hS h1930 c hOm
  exact ⟨hLL0, hN G c.L0 c.n (2 * CFSG.Open.pRank 2 D.Z) c.hn (Or.inl hL2L0)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
