module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartHubBlk
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartHubIso
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartHubChart
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartHubSwap

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoChart_hubAssembly (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (hF0 : Nat.card F0 = 4)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (ψ : Su F0 2 1 m →* G) (hψ : QTwoOrdModel Bs L ψ)
    (ε0 : Fin m ↪ Fin (n + 1)) (hε0 : QTwoFrameMatch S ψ ε0)
    (hlifts : ∀ π : Equiv.Perm (Fin (n + 1)), ∃ g : G,
      QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    (hunique : ∀ {g g' : G} {π π' : Equiv.Perm (Fin (n + 1))} {J J' : Finset (Fin m)},
      QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π → QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g' π' →
      2 ≤ J.card → J.card ≤ 4 → J'.card = J.card →
      qTwoFrameSet ε0 π J = qTwoFrameSet ε0 π' J' → qTwoBlockOf ψ g J = qTwoBlockOf ψ g' J')
    (hgen : QTwoH L 𝒦 =
      ⨆ (π : Equiv.Perm (Fin (n + 1))) (g : G) (_ : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π),
        L.map (MulAut.conj g).toMonoidHom)
    (e : Su F0 2 1 m ≃* Su K 2 1 m)
    (he : ∀ J : Finset (Fin m),
      (coordBlockSU F0 2 1 J).map e.toMonoidHom = coordBlockSU K 2 1 J) :
    Nonempty (QTwoCanonBlocks K m (n + 1) (QTwoH L 𝒦)) := by
  obtain ⟨blk, hblk⟩ := qTwoChartHub_exists_blk S ψ ε0 hunique
  exact ⟨{ blk := blk
           blk_le := fun I h2 h4 => qTwoChartHub_blk_le S hψ hlifts hblk h2 h4
           blk_iso := fun I h2 h4 => qTwoChartHub_blk_iso S hF0 hK hψ hε0 hlifts hblk h2 h4
           chart := fun ε => qTwoChartHub_chart S hψ hlifts hblk e he ε
           swap := qTwoChartHub_swap S hψ hε0 hlifts hblk
           gen := qTwoChartHub_gen S hF0 hψ hlifts hblk hgen }⟩

end CFSG.StandardType.QTwo

end
