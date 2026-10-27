module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartMatch
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartLifts
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartFour
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThree
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartExtend
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartField
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartHub

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoChart_blockUnique (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (hF0 : Nat.card F0 = 4)
    (ψ : Su F0 2 1 m →* G) (hψ : QTwoOrdModel Bs L ψ)
    (ε0 : Fin m ↪ Fin (n + 1)) (hε0 : QTwoFrameMatch S ψ ε0)
    {g g' : G} {π π' : Equiv.Perm (Fin (n + 1))} {J J' : Finset (Fin m)}
    (hg : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    (hg' : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g' π')
    (hJ2 : 2 ≤ J.card) (hJ4 : J.card ≤ 4) (hJ'card : J'.card = J.card)
    (hframe : qTwoFrameSet ε0 π J = qTwoFrameSet ε0 π' J') :
    qTwoBlockOf ψ g J = qTwoBlockOf ψ g' J' := by
  by_cases h4 : J.card = 4
  · exact qTwoChart_fourBlock_unique S hF0 ψ hψ ε0 hε0 hg hg' h4 (by omega) hframe
  · have hJ3 : J.card ≤ 3 := by omega
    have hJ'2 : 2 ≤ J'.card := by omega
    have hJ'3 : J'.card ≤ 3 := by omega
    obtain ⟨Q, Q', hQ, hQ', hJQ, hJ'Q', hframeQ⟩ :=
      qTwoChart_extendFrame S ε0 hJ'card hJ4 hframe
    have hQeq : qTwoBlockOf ψ g Q = qTwoBlockOf ψ g' Q' :=
      qTwoChart_fourBlock_unique S hF0 ψ hψ ε0 hε0 hg hg' hQ hQ' hframeQ
    have hJeq := qTwoChart_twoThreeBlock S hF0 ψ hψ ε0 hε0 hg hJ2 hJ3 hQ hJQ
    have hJ'eq := qTwoChart_twoThreeBlock S hF0 ψ hψ ε0 hε0 hg' hJ'2 hJ'3 hQ' hJ'Q'
    rw [hJeq, hJ'eq, hQeq, hframe]

theorem qTwo_canonBlocks
    (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hodd6 : m = 6 → Odd (Nat.card (Subgroup.center ↥L)))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    Nonempty (QTwoCanonBlocks K m (n + 1) (QTwoH L 𝒦)) := by
  obtain ⟨F0, i1, i2, i3, ψ, hF0, hψ⟩ := qTwoChart_ordinaryModel S hFrameL hFm hodd6
  obtain ⟨ε0, hε0⟩ := qTwoChart_frameMatching S hF0 ψ hψ
  have hlifts := qTwoChart_liftsExist S
  have hunique : ∀ {g g' : G} {π π' : Equiv.Perm (Fin (n + 1))} {J J' : Finset (Fin m)},
      QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π → QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g' π' →
      2 ≤ J.card → J.card ≤ 4 → J'.card = J.card →
      qTwoFrameSet ε0 π J = qTwoFrameSet ε0 π' J' → qTwoBlockOf ψ g J = qTwoBlockOf ψ g' J' := by
    intro g g' π π' J J' hg hg' hJ2 hJ4 hJ'card hframe
    exact qTwoChart_blockUnique S hF0 ψ hψ ε0 hε0 hg hg' hJ2 hJ4 hJ'card hframe
  have hgen := qTwoChart_generation S
  obtain ⟨e, he⟩ := qTwoChart_fieldTransport hF0 hK m
  exact qTwoChart_hubAssembly S hF0 hK ψ hψ ε0 hε0 hlifts hunique hgen e he

end CFSG.StandardType.QTwo

end
