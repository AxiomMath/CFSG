module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Milestones.ASVolI.B6
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

theorem burnsideC121_Jj_zero {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.ASVolI.ChB.Jj H 0 = CFSG.Quasithin.thompsonJ H := by
  unfold CFSG.ASVolI.ChB.Jj
  rw [if_pos (Nat.zero_le _), CFSG.higherElemThompson_zero,
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ]

theorem burnsideC121_baumOf {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.ASVolI.ChB.baumOf H = CFSG.Quasithin.baum H := by
  unfold CFSG.ASVolI.ChB.baumOf CFSG.Quasithin.baum
  rw [burnsideC121_Jj_zero]

theorem burnsideC121_b610 (h610 : B_6_10) {G : Type} [Group G] [Finite G]
    {H T M V L : Subgroup G} {n : ℕ} (hM : MinParabolic H T M) (hF : CharTwo H)
    (hV : IsTwoReducedIn H V) (hL : IsSubnormal L H) (hnat : IsNaturalL2Prime n L V)
    (hJ : ⁅V, thompsonJ T⁆ ≠ ⊥) :
    IsSylowTwoOf (baum T) (⨆ l ∈ L, (baum T).map (MulAut.conj l).toMonoidHom) ∧
      (twoResidual L = L →
        omegaOneCenterOf (thompsonJ T) =
          (⁅V, L⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
            (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (L : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFq : quasithinGenFitting H = pCoreOf 2 H :=
    (CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff H 2).2 hF
  have hJ' : ⁅V, CFSG.ASVolI.ChB.Jj T 0⁆ ≠ ⊥ := by rwa [burnsideC121_Jj_zero]
  obtain ⟨-, h2, h3⟩ := h610 G H T M V L n hM hFq hV hL hnat hJ'
  rw [burnsideC121_baumOf] at h2
  refine ⟨h2, fun hres => ?_⟩
  have := h3 hres
  rwa [burnsideC121_Jj_zero] at this

end CFSG.ASVolI
