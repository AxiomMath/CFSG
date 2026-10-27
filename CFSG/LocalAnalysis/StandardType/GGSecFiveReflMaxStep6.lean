module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRM_of_witness {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hmax : GGMaximalJoin p B Bs x L D J 𝒦)
    (hw : GGSecFiveInfWitness p B Bs x L D J) :
    ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' → ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  obtain ⟨hW, 𝒦', h𝒦', hjoin⟩ := hw
  obtain ⟨hnbr, _hWeyl, hbest⟩ := hmax
  have hW' : GGWeylReflectionGroup p (ggAutomizerJoin L Bs 𝒦') := hjoin ▸ hW
  have hcard : Nat.card (ggAutomizerJoin L Bs 𝒦') ≤ Nat.card (ggAutomizerJoin L Bs 𝒦) :=
    hbest 𝒦' h𝒦' hW'
  have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAInf p B Bs x L D J := by
    rw [ggAutomizerJoin, ggAInf]
    refine sup_le le_sup_left ?_
    refine iSup_le fun K => iSup_le fun hK => ?_
    obtain ⟨y, hy⟩ := hnbr.2 K hK
    refine le_sup_of_le_right ?_
    exact (le_iSup (fun _ : GGNbr p B x D J y K => ggAutomizer K Bs) hy).trans
      ((le_iSup (fun K' : Subgroup G =>
          ⨆ (_ : GGNbr p B x D J y K'), ggAutomizer K' Bs) K).trans
        (le_iSup (fun y' => ⨆ K' : Subgroup G,
          ⨆ (_ : GGNbr p B x D J y' K'), ggAutomizer K' Bs) y))
  have hle' : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizerJoin L Bs 𝒦' := by
    rw [hjoin]; exact hle
  have heq : ggAutomizerJoin L Bs 𝒦 = ggAutomizerJoin L Bs 𝒦' :=
    Subgroup.eq_of_le_of_card_ge hle' hcard
  intro y K' hy
  have hK'le : ggAutomizer K' Bs ≤ ggAInf p B Bs x L D J := by
    rw [ggAInf]
    refine le_sup_of_le_right ?_
    exact (le_iSup (fun _ : GGNbr p B x D J y K' => ggAutomizer K' Bs) hy).trans
      ((le_iSup (fun K'' : Subgroup G =>
          ⨆ (_ : GGNbr p B x D J y K''), ggAutomizer K'' Bs) K').trans
        (le_iSup (fun y' => ⨆ K'' : Subgroup G,
          ⨆ (_ : GGNbr p B x D J y' K''), ggAutomizer K'' Bs) y))
  rw [heq, hjoin]
  exact hK'le

end CFSG.StandardType

end
