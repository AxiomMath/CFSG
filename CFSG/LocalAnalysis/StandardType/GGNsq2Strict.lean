module

public import CFSG.LocalAnalysis.StandardType.GGPhanSmallStrict
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggPhanStrict_card_lt_join_of_wA (hWA : GGTBFixNbrXInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    Nat.card ↥(ggAutomizer L Bs) < Nat.card ↥(ggAutomizerJoin L Bs 𝒦) := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hS : LargeEvenSStar p B x L := hconf.1.2.2.2.2.2.2.1
  have hx : x ∈ Bs := hconf.2.1.1 hS.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨y, K, hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
  have hrefl : GGReflGenerated p (ggAutomizer K Bs) := hcfg.2.1 y K hN
  obtain ⟨φ, hφK, hφx⟩ : ∃ φ ∈ ggAutomizer K Bs, φ ⟨x, hx⟩ ≠ ⟨x, hx⟩ := by
    by_contra hno
    push Not at hno
    exact hS.2.2.1 (hWA G p B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y K hN hrefl
      (Or.inr hcfg.2.1) ⟨x, hx⟩ (Subgroup.mem_zpowers x) hno)
  have hWey : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    hcfg.1.2.2.2.2.1 y K hN hrefl (Or.inr hcfg.2.1)
  have hjoin : ggAutomizerJoin L Bs {K} = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    simp [ggAutomizerJoin]
  have hmax : Nat.card ↥(ggAutomizerJoin L Bs {K}) ≤ Nat.card ↥(ggAutomizerJoin L Bs 𝒦) :=
    hcfg.2.2.2.2.2 {K} (ggNbrSet_singleton hN) (by rw [hjoin]; exact hWey)
  have hlt : ggAutomizer L Bs < ggAutomizerJoin L Bs {K} := by
    rw [hjoin]
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hmem : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := Subgroup.mem_sup_right hφK
    rw [← h] at hmem
    exact hφx (MulAction.mem_stabilizer_iff.mp
      (ggAutomizer_le_stabilizer_of_centralizes hx hxL hmem))
  haveI : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun φ : MulAut ↥Bs => (φ : ↥Bs → ↥Bs)) DFunLike.coe_injective
  exact lt_of_lt_of_le (Subgroup.card_lt_of_lt hlt) hmax

theorem ggPhanStrict_card_lt_join_of_nbr (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {X : Subgroup G}
    (hnbr : GGNbr p B x D J y X) (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    Nat.card ↥(ggAutomizer X Bs) < Nat.card ↥(ggAutomizerJoin L Bs 𝒦) := by
  by_contra hle
  push Not at hle
  haveI : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun φ : MulAut ↥Bs => (φ : ↥Bs → ↥Bs)) DFunLike.coe_injective
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hyBs : y ∈ Bs := hconf.2.1.1 hnbr.1.2.1
  have hyx : y ∉ Subgroup.zpowers x := GGConfig.not_mem_zpowers_of_ggNbr hconf hnbr
  have heq : ggAutomizer X Bs = ggAutomizerJoin L Bs 𝒦 := Subgroup.eq_of_le_of_card_ge hXA hle
  have hLJ : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  have hLX : ggAutomizer L Bs ≤ ggAutomizer X Bs := hLJ.trans heq.ge
  have hXy := ggAutomizer_le_stabilizer_of_centralizes hyBs hnbr.1.2.2.2.1
  exact hyx (hFix G p B Bs x L D J hconf hcfg.1.2.1 hcfg.1.2.2.1 hcfg.1.2.2.2.1 y X hnbr
    (hcfg.2.1 y X hnbr) (Or.inr hcfg.2.1) ⟨y, hyBs⟩ fun φ hφ =>
      MulAction.mem_stabilizer_iff.mp (hXy (hLX hφ)))

end CFSG.StandardType

end
