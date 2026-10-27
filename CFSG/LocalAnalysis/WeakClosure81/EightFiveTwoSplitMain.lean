module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSetup
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitRank
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitBridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAct
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAltB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

theorem barFacts_of_dispatchHyp_at3 (hRU : UnitaryRootCommutatorRankAt 3)
    (hRL : L2RootCommutatorRank)
    {V H T U : Subgroup G} (hD : DispatchHyp V H T U) {X : Type} [Group X]
    {φ : ↥(kGenIn V H) →* X} (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) :
    ∃ (φ' : ↥(ambK V H T) →* X) (A : Subgroup (MulAut X)) (Z₁ : Subgroup X),
      IsBarMap (ambK V H T) (pCoreOf 2 (ambK V H T)) φ' ∧
      barSub (ambK V H T) φ' (ambV V H) = barSub (kGenIn V H) φ V ∧
      BarFacts X (barSub (kGenIn V H) φ V) A Z₁ (rk ↥V) ∧
      ∀ k : ↥(kGenIn V H),
        φ k ∈ Z₁ ↔ (k : G) ∈ Subgroup.centralizer (eSub V H T : Set G) := by
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hKT := hD.eq_sup
  obtain ⟨φ', hφ', hS⟩ := exists_ambient_barMap h83 hKT hφ
  obtain ⟨A, Z₁, hAct, hZ⟩ := exists_action hD hφ
  refine ⟨φ', A, Z₁, hφ', hS, ?_, hZ⟩
  refine { toActionFacts := hAct, situation := ?_, central := ?_, rank_unitary := ?_
           rank_l2 := ?_ }
  · rw [← hS]
    exact barSituation_of_hyp711 (AmbientH.hyp711 h83 hKT) hφ'
  · intro h2
    rw [← hS] at h2 ⊢
    exact centralInSylow_of_hyp83 h83 hKT hφ' h2
  · intro n hX hroot
    rw [← hS] at hroot
    exact rank_unitary_of_hyp83_at3 hRU h83 hKT hφ' n hX hroot
  · intro n hX
    exact rank_l2_of_hyp83 hRL h83 hKT hφ' n hX

theorem w3Lem85TwoDispatch_of_split_at3 (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hRU : UnitaryRootCommutatorRankAt 3) (hRL : L2RootCommutatorRank)
    (g1 : W3Lem85TwoGap1) (g2 : W3Lem85TwoGap2) (g3 : W3Lem85TwoGap3 G)
    (g4 : W3Lem85TwoGap4) (g5 : W3Lem85TwoGap5 G) (g6 : W3Lem85TwoGap6) :
    W3Lem85TwoDispatch G := by
  rw [w3Lem85TwoDispatch_iff]
  intro V H T U hD
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hKT := hD.eq_sup
  obtain ⟨X, _, φ, hφ⟩ : ∃ (X : Type) (_ : Group X) (φ : ↥(kGenIn V H) →* X),
      IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ :=
    ⟨_, inferInstance, QuotientGroup.mk' (CFSG.pCore 2 ↥(kGenIn V H)), isBarMap_mk_pCore _⟩
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨φ', A, Z₁, hφ', hS, hF, hZ⟩ := barFacts_of_dispatchHyp_at3 hRU hRL hD hφ
  have hAlt := ((h711 H) _ _ _ (AmbientH.hyp711 h83 hKT)).2 X φ' hφ'
  rw [hS] at hAlt
  rcases hAlt with h1 | h2 | ⟨h3c, h3s⟩ | h4 | ⟨h5c, h5s⟩ | h6
  · exact dispatchConcl_of_barConcl h83 hKT hφ' (barConcl_of_alt1 hF g1 h1)
  · exact (false_of_alt2 hF g2 h2).elim
  · have hc := center_eq_of_alt3 hF g3 h3c h3s
    exact absurd (kBarShape_of_central hφ hZ hc
      (P := fun Y _ => Nonempty (Y ≃* alternatingGroup (Fin 6))) h3s.1) (g3.2 V H T U hD)
  · exact dispatchConcl_of_barConcl h83 hKT hφ' (barConcl_of_alt4 hF g1 g4 h4)
  · exact ⟨4, 1, by norm_num, Or.inl (g5 V H T U hD X φ hφ h5c h5s)⟩
  · exact (false_of_alt6 hF g6 h6).elim

theorem w3Lem85TwoDispatch_of_split (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hRU : UnitaryRootCommutatorRank) (hRL : L2RootCommutatorRank)
    (g1 : W3Lem85TwoGap1) (g2 : W3Lem85TwoGap2) (g3 : W3Lem85TwoGap3 G)
    (g4 : W3Lem85TwoGap4) (g5 : W3Lem85TwoGap5 G) (g6 : W3Lem85TwoGap6) :
    W3Lem85TwoDispatch G :=
  w3Lem85TwoDispatch_of_split_at3 h711 (unitaryRootCommutatorRank_iff_at.1 hRU 3 le_rfl) hRL
    g1 g2 g3 g4 g5 g6

end CFSG.LocalAnalysis.WeakClosure81

end
