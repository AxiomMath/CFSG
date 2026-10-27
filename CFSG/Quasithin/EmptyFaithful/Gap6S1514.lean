module

public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.EmptyFaithful.S146Defs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6

section Lattice

variable {G : Type} [Group G] [Finite G]

theorem exists_minimal_oTwoUpper_not_le (T C CW : Subgroup G) (hTC : T ≤ C)
    (h : ¬ oTwoUpper C ≤ CW) :
    ∃ K : Subgroup G, T ≤ K ∧ K ≤ C ∧ ¬ oTwoUpper K ≤ CW ∧
      ∀ L : Subgroup G, T ≤ L → L < K → oTwoUpper L ≤ CW := by
  obtain ⟨K, ⟨hTK, hKC, hK⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {K : Subgroup G | T ≤ K ∧ K ≤ C ∧ ¬ oTwoUpper K ≤ CW} ⟨C, hTC, le_rfl, h⟩
  refine ⟨K, hTK, hKC, hK, fun L hTL hLK => ?_⟩
  by_contra hL
  exact hmin L ⟨hTL, hLK.le.trans hKC, hL⟩ hLK

end Lattice

@[expose] def Step1514GenResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M →
    oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G) →
    ¬ oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) :
        Subgroup G) : Set G) →
    ∀ K : Subgroup G, T ≤ K → K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      ¬ oTwoUpper K ≤ Subgroup.centralizer ((V154 T Mc M ⊓ Subgroup.centralizer
        (thompsonJi T 1 : Set G) : Subgroup G) : Set G) →
      (∀ L : Subgroup G, T ≤ L → L < K → oTwoUpper L ≤ Subgroup.centralizer
        ((V154 T Mc M ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) : Subgroup G) : Set G)) →
      (∃ L : Subgroup G, T ≤ L ∧ L < K ∧ ¬ L ≤ M) →
      ¬ Case3bOf T Mc M →
      ∃ H : Subgroup G, IsHStar T M H ∧
        H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
        ¬ oTwoUpper H ≤ oTwoUpper (Subgroup.centralizer ((V154 T Mc M ⊓
          Subgroup.centralizer (thompsonJi T 1 : Set G) : Subgroup G) : Set G))

theorem step1514Gen_of_residual (hRes : Step1514GenResidual) : Step1514Gen := by
  intro G _ _ T Mc M h hMf hCE hyp1 hyp2 hnb
  have hTC : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    le_centralizer_quasithinOmegaOneCenter T hx
  obtain ⟨K, hTK, hKC, hK, hmin⟩ := exists_minimal_oTwoUpper_not_le T _ _ hTC hyp2
  by_cases hA : ∀ L : Subgroup G, T ≤ L → L < K → L ≤ M
  · have hKM : ¬ K ≤ M := fun hKM => hK ((oTwoUpper_mono (le_inf hKM hKC)).trans hyp1)
    have hZT : quasithinOmegaOneCenter T ≤ T :=
      (quasithinOmegaOneCenter_le_center T).trans inf_le_left
    have hZK : quasithinOmegaOneCenter T ≤ pCoreOf 2 K :=
      le_pCoreOf_of_le_normalizer 2 (hZT.trans hTK)
        (fun x hx => Subgroup.centralizer_le_normalizer _ (hKC hx))
        (h.sylow.1.to_le hZT)
    refine ⟨K, ⟨⟨hTK, fun hbot => h.omegaOneCenter_ne_bot (le_bot_iff.1 (hZK.trans hbot.le))⟩,
      hKM, fun Y hY hYK hYM => ?_⟩, hKC, fun hK' => hK (hK'.trans (oTwoUpper_le _))⟩
    by_contra hne
    exact hYM (hA Y hY.1 (lt_of_le_of_ne hYK hne))
  · push Not at hA
    exact hRes G T Mc M h hMf hCE hyp1 hyp2 K hTK hKC hK hmin hA hnb

end Gap6

end CFSG.Quasithin
