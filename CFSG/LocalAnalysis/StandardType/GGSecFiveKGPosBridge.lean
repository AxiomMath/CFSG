module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section Bridge

variable {G : Type} [Group G] [Finite G]

theorem ggRouteCfg_isElemAbelian {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    IsElemAbelian p Bs :=
  h.1.1.2.1.2.1

theorem ggRouteCfg_noTransvection {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    GGNoTransvection p Bs :=
  h.1.2.2.2.1

theorem ggAutomizer_le_top (X Bs : Subgroup G) : ggAutomizer X Bs ≤ ggAutomizer ⊤ Bs :=
  ggAutomizer_mono Bs le_top

theorem ggAutomizerJoin_le_top (L Bs : Subgroup G) (𝒦 : Finset (Subgroup G)) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer ⊤ Bs :=
  sup_le (ggAutomizer_le_top L Bs) (iSup₂_le fun K _ => ggAutomizer_le_top K Bs)

theorem ggAutomizer_le_ggAutomizerJoin {L Bs X : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : X = L ∨ X ∈ 𝒦) : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  rcases hX with rfl | hK
  · exact le_sup_left
  · exact le_sup_of_le_right
      (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => ggAutomizer K Bs) X hK)

theorem ggCoxRefl_of_cfg {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggAutomizer ⊤ Bs) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥A} (hpres : GGCoxeterPres p A M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r : MulAut ↥Bs} (hrA : r ∈ A) (hr : GGIsReflection p r) : r ∈ ggCoxRefl M e := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  exact ggCoxRefl_of_isReflection hp hodd (ggRouteCfg_isElemAbelian hcfg) hpres h3
    (ggNoTransvection_of_le_automizer (ggRouteCfg_noTransvection hcfg) hA) hrA hr

end Bridge

end CFSG.StandardType
