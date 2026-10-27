module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Pieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Local
public import CFSG.LocalAnalysis.StandardType.FS81.WeakClosureFusion
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbOrth
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Open.StatedDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.GroupTheory.WeirSylow

theorem rowFacts_twD5_of_mulEquiv {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (φ : ↥K ≃* ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1))) (hAK : A ≤ K)
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 5) :
    (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ 5) ∧
      (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ 5 →
        ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = A) := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by
    intro s
    fin_cases s <;> decide
  have hnd : (QuadraticMap.polarBilin
      (CFSG.LieType.Universal.Spin.quadMinus 5 (ZMod 2) 1 1)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 5 (ZMod 2) hirr
  have hnp : ¬ IsPlusType (CFSG.LieType.Universal.Spin.quadMinus 5 (ZMod 2) 1 1) :=
    not_isPlusType_quadMinus (by norm_num) hirr
  have hcard : Fintype.card (Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2) = 2 * 5 := by simp
  exact rowFacts_of_statedOmega φ
    (CFSG.LieType.Universal.Spin.coe_quadMinus 5 (ZMod 2) 1 1) hnd (n := 5) (by norm_num)
    hcard ⟨fun h => absurd h hnp, fun h => absurd h (by decide)⟩ hAK hA hAcard

theorem t5Fus42_of
    (hOut : ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsTwD5 K →
      Subgroup.center K = ⊥ → ¬ 3 ∣ Nat.card (Outer K))
    (hφ : ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), IsTwD5 K →
      Subgroup.center K = ⊥ →
        Nonempty (↥K ≃* ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1)))) :
    T5Fus42 := by
  intro G _ _ b₀ K E hStd B hAd hLoc
  obtain ⟨-, ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -, hEmax, -, hEcard, hX⟩, -,
    hsup, hEKmax, hEKcard, -⟩ := hStd
  obtain ⟨hspan, -, -⟩ := hAd
  have hOut' := hOut G K hKmark hKz
  obtain ⟨φ⟩ := hφ G K hKmark hKz
  obtain ⟨hrank, hconj⟩ := rowFacts_twD5_of_mulEquiv (A := E ⊓ K) φ inf_le_right
    hEKmax.2.1 hEKcard
  exact fus42_of_facts hb₀ hKC hKn hKz hOut' hA2 hEmax hEcard hsup hrank hconj hspan
    (lt_of_le_of_lt (card_realized_normalizer_le_of_localOrth hLoc) hX)

theorem t5Fus42_holds : T5Fus42 :=
  t5Fus42_of (fun _ _ _ _ hm hZ => not_three_dvd_card_outer_of_isTwD5 hm hZ)
    (fun _ _ _ _ hm hZ => nonempty_mulEquiv_omegaMinus_of_marking (r := 5) (by norm_num) hm hZ)

end CFSG.StandardType.FrameRoute.FS81

end
