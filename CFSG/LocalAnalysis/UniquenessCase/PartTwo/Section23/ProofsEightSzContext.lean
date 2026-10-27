module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_ctx23L_of_mem_calLLow (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (h20_8 : S20_8 D) (h20_10 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI D.U) {L₀ : Subgroup G} (hL₀ : L₀ ∈ calLLow D.T D.M) :
    ∃ c : Ctx23L D Ch, c.L0 = L₀ ∧ c.B = c.B0 := by
  classical
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  haveI : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  obtain ⟨n, hn⟩ := uc22main1_nParam D h20_10 h1930 hL₀
  obtain ⟨B0, hch, hB0, hpi, hα, hBM⟩ := hCh L₀ hL₀ n hn
  obtain ⟨L, hL0L, hLmax⟩ := Finite.exists_le_maximal
    (p := fun L : Subgroup G => L ∈ calL D.T D.M) (a := L₀) hL₀.prop
  let c21 : Ctx21 D Ch :=
    { L0 := L₀, B0 := B0, B := B0, n := n, hL0 := hL₀, hn := hn, hB0 := hB0, hpi := hpi,
      hα := hα, hBM := hBM, hch := hch, hB := hB0, hle := le_rfl }
  let c23 : Ctx23 D Ch := { toCtx21 := c21, hTI := hTI }
  let Nc : Subgroup G :=
    normalizer ((⨆ K ∈ calLOf D.T D.M (normalizer (L : Set G)), K : Subgroup G) : Set G)
  let c : Ctx23L D Ch := Ctx23L.mk c23 L hLmax hL0L Nc (h20_8 h1930 L hLmax)
  exact ⟨c, rfl, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
