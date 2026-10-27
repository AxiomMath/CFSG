module

public import CFSG.RankThree.GF2n.Tim79a34ResidualX
public import CFSG.RankThree.GF2n.Tim79a34TwoEnd

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem le_pResidual_of_twoEnd (hI : Sec34IWStatement) [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hn : ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) :
    H ≤ pResidual 2 G := by
  obtain ⟨n, hn3, ⟨e⟩⟩ := hn
  have hperf : Group.IsPerfect (Xbar V H) := isPerfect_xbar_of_statedSp hn3 hZ e
  have hX : xOf V H ≤ pResidual 2 G := xOf_le_pResidual_two hH.setup.mc.toMinCex hperf
  have hHX : xOf V H = H := xOf_eq_H_of_iw hI hH hZ
  rw [← hHX]
  exact hX

@[expose] def NTQEOutResidualStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ →
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) →
    P.relIndex Q = 2 →
    (∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 (G ⧸ N) ∧ ¬ Q ≤ N) →
    ∃ (M₀ V₀ H₀ : Subgroup ↥(pResidual 2 G)),
      TwoEndHyp M₀ V₀ (P.subgroupOf (pResidual 2 G)) (P.subgroupOf (pResidual 2 G)) H₀ ∧
      Subgroup.center (Xbar V₀ H₀) = ⊥ ∧
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V₀ H₀))

end CFSG.RankThree.GF2n.Tim79a
