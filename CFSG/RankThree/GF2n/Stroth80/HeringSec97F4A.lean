module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F3D
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Sec97FourCore94Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.TwoConcl M Q B X → HS9.ThreeConcl M Q B X →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
        (∃ s ∈ Z0, ∃ g ∈ M, g * s * g⁻¹ ∈ LB M Q B ⊓ hc.CN t ∧ g * s * g⁻¹ ∉ Z0) →
        ∀ h ∈ M, conjSubgroup h B ≤ QB B →
          (∀ x ∈ LB M Q B ⊓ X, x ∉ Q →
            h * x * h⁻¹ ∉ LB M Q B ∧ x ∉ conjSubgroup h (LB M Q B)) →
          HS9.LineGeom M Q Z B h →
          IsTIMod (LB M Q B ⊔ LB M Q (conjSubgroup h B)) Q (LB M Q B ⊓ X) → False

theorem sec97FourCore_of_core94 (h94 : Stroth94Statement)
    (hC : Sec97FourCore94Statement) : Sec97FourCoreStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1 h2 h3 h hh hFB hhard hline hTI
  have ht : t ∈ LB M Q B := hs.mem
  obtain ⟨Z0, hZ0⟩ := exists_isCentrePre (Q := Q) (hc.Q_le_Rt ht)
  have h94' := h94 G M Q Z B hc n t hs Z0 hZ0
  unfold StronglyClosedMod at h94'
  push Not at h94'
  obtain ⟨s, hs0, g, hg, hL, hZ⟩ := h94'
  exact hC G M Q Z B hc n t hs X Y hsplit h4 h1 h2 h3 Z0 hZ0 ⟨s, hs0, g, hg, hL, hZ⟩ h hh hFB
    hhard hline hTI

theorem sec97Four_of_core94 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h94 : Stroth94Statement) (hC : Sec97FourCore94Statement) : Sec97FourStatement :=
  sec97Four_of_core h34 h311a (sec97FourCore_of_core94 h94 hC)

end CFSG.RankThree.GF2n.Stroth80
