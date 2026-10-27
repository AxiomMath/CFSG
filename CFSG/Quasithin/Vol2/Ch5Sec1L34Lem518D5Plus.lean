module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5SPlus
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518DL

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement Pointwise

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [Finite G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem D₅_le_normalizer_parabolic_plus (hF : L2TorusFact)
    (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first) (h510 : Stmt5_1_10) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) (hDSC : DSCStatementPlus) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts)
    (hFive : A314FiveNormFact) {U U' : Subgroup G} (hUU' : U ≠ U')
    (hU : ParData518 T H B D U)
    (hK : oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U' : Set G)))
    (hperm : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        (U.map (MulAut.conj g).toMonoidHom = U ∨ U.map (MulAut.conj g).toMonoidHom = U') ∧
        (U'.map (MulAut.conj g).toMonoidHom = U ∨ U'.map (MulAut.conj g).toMonoidHom = U')) :
    D₅ ≤ Subgroup.normalizer
      (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) : Set G) := by
  by_cases hO : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) = ⊥
  · exact (s.false_of_pCoreOf_eq_bot_plus hF h311 h5114 h510 h331 hR hDSC hU hO).elim
  · exact s.D₅_le_normalizer_of_sylow hF h510 h331 hR h36 h37 h38 h39 h312 h314 hFive hU rfl
      (s.isSylowTwoOf_T₀ hF h311 h5114 h510 h331 hR hUU' hU hK hperm hO)
      (s.pCoreOf_X₁_ne_bot hF h510 h331 hR hO)

theorem false_of_setting_plus (hTP : L34TwoParabolicFact)
    (hTA : L34TwoAutFact) (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first)
    (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hDSC : DSCStatementPlus)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts) (hFive : A314FiveNormFact) : False := by
  obtain ⟨U₂, U₃, hne, hpar, hK, hperm⟩ := s.exists_two_parabolics hTP hTA h510 h331 hR
  have h2 := s.D₅_le_normalizer_parabolic_plus hF h311 h5114 h510 h331 hR hDSC h36 h37 h38 h39 h312
    h314 hFive hne (hpar U₂ (Or.inl rfl)) hK hperm
  have hK' : oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₃ : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₂ : Set G)) := by
    rw [sup_comm]
    exact hK
  have h3 := s.D₅_le_normalizer_parabolic_plus hF h311 h5114 h510 h331 hR hDSC h36 h37 h38 h39 h312
    h314 hFive hne.symm (hpar U₃ (Or.inr rfl)) hK'
    (fun g hg1 hg2 => ⟨(hperm g hg1 hg2).2.symm, (hperm g hg1 hg2).1.symm⟩)
  have hJ : oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₂ : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₃ : Set G)) = oTwoUpper H :=
    le_antisymm (sup_le ((oTwoUpper_le _).trans inf_le_left)
      ((oTwoUpper_le _).trans inf_le_left)) hK
  apply s.D₅_not_le
  have h23 := le_normalizer_sup_of_le h2 h3
  rw [hJ] at h23
  exact h23

end Setting518D5

theorem stmt5_1_18_D5_of_inputs_plus (hTP : L34TwoParabolicFact)
    (hTA : L34TwoAutFact) (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first)
    (h510 : Stmt5_1_10) (h516 : Stmt5_1_16) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hDSC : DSCStatementPlus) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (hFive : A314FiveNormFact) :
    Stmt5_1_18_D5 := by
  intro G _ _ T M L V H B D n h _ D₃ hD₃ h3 hD₃M hne _ D₅ hD₅ h5
  by_contra hD5
  by_cases hin : ∀ d ∈ D₃, ∃ k ∈ oTwoUpper H, d * k⁻¹ ∈ centralizerModO2 (oTwoUpper H)
  · exact hne (h.eq_B_of_inner hF h510 h516 hD₃ h3 hD₃M hin)
  · push Not at hin
    exact (Setting518D5.mk h hD₃ h3 hD₃M hin hD₅ h5 hD5).false_of_setting_plus hTP hTA hF h311 h5114
      h510 h331 hR hDSC h36 h37 h38 h39 h312 h314 hFive

end Setting

end CFSG.Quasithin.H13
