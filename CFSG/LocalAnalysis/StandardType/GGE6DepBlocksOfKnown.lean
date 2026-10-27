module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownData
public import CFSG.LocalAnalysis.StandardType.GGE6DepPairBlock
public import CFSG.LocalAnalysis.StandardType.GGE6DepKFive
public import CFSG.LocalAnalysis.StandardType.GGE6DepBlocksOfPairs
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6DepBlockCfg_of_known (hRig : GGLabelRigidInput) (hKG : GGE6DepBlockKnown) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hnt : GGNoTransvection p Bs) (hinn : GGInnerDiagOn Bs L) {y : G} {K : Subgroup G}
    (hK : GGNbr p B x D J y K) (hE : GGE6DepPerpCfg p Bs L K)
    (hconj : GGE6DepConjSetting p Bs x y L) : GGE6DepBlockCfg p Bs x J (x * y) := by
  obtain rfl : p = 3 := hE.1
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  have hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hcfg.bstar_inf_centralizer_L
  obtain ⟨hBsN, R, _, I, ψ, hBl, hTB, hcard⟩ := ggE6Dep_known_data hRig hKG hcfg hinn hE
  obtain ⟨hZ, hBsL, _, _, _, _, _, _, hy, _, _, _, _, _, _, _, hyL, _, _, horth2, _⟩ := id hconj
  have hpb : ∀ a b : ↥Bs, (a : G) ∈ L → (b : G) ∈ L → GGCorootOrth 3 (ggAutomizer L Bs) a b →
      ∃ Dv N : Subgroup G, GGE6DepPairBlock 3 Bs L a b Dv N :=
    fun a b haL hbL hab => ggE6Dep_pairBlock hBs hBsN hker hZ hBsL hnt hTB hcard hBl haL hbL hab
  have hDcl : D = Subgroup.closure {x, y} := hK.2.1
  have hyD : y ∈ D := by
    rw [hDcl]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left L (Subgroup.centralizer_le (by simpa using hyD))
    · rintro g ⟨hgL, hgy⟩
      refine ⟨hgL, ?_⟩
      rw [hDcl]
      have hgx : g ∈ Subgroup.centralizer ({x} : Set G) := hLx hgL
      have hsub : ({x, y} : Set G) ⊆ Subgroup.centralizer ({g} : Set G) := by
        intro h hh
        rcases hh with rfl | hh
        · exact Subgroup.mem_centralizer_iff.mpr fun m hm => by
            rw [Set.mem_singleton_iff.mp hm]
            exact ((Subgroup.mem_centralizer_iff.mp hgx) _ rfl).symm
        · rw [Set.mem_singleton_iff.mp hh]
          exact Subgroup.mem_centralizer_iff.mpr fun m hm => by
            rw [Set.mem_singleton_iff.mp hm]
            exact ((Subgroup.mem_centralizer_iff.mp hgy) _ rfl).symm
      exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
        (Subgroup.mem_centralizer_iff.mp
          ((Subgroup.closure_le (Subgroup.centralizer ({g} : Set G))).mpr hsub hh) g rfl).symm
  have hJ : J = LargeEvenLayer (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [← hLD]
    exact hcfg.2.2.1.2.2.2.2.1
  have hlayer : ∀ P : Subgroup G, P ≤ L ⊓ Subgroup.centralizer ({y} : Set G) → ⁅P, P⁆ = P →
      P ≤ J := by
    intro P hP hPP
    have hc : GGCorootPt 3 (ggAutomizer L Bs) ⟨y, hy⟩ :=
      ggCorootPt_of_orth_left Nat.prime_three horth2
    rw [hJ]
    exact ggE6Dep_perfect_le_layer hBs hBsN hker hZ hBsL hnt hTB hcard hBl hyL hc hP hPP
  exact ggE6DepBlockCfg_of_pairBlocks hBs hxBs hL hconj hpb hlayer

theorem ggE6DepBlockCfgInput_of_known (hRig : GGLabelRigidInput) (hKG : GGE6DepBlockKnown)
    (hConj : GGE6DepConj) : GGE6DepBlockCfgInput := by
  intro G _ _ p B Bs x L D J hcfg hop hinn hnt y K hK hE
  exact ggE6DepBlockCfg_of_known hRig hKG hcfg hnt hinn.1 hK hE
    (hConj G p B Bs x L D J hcfg hop hinn hnt y K hK hE)

end CFSG.StandardType

end
