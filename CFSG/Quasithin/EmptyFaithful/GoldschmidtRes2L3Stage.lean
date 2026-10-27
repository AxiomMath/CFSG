module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Core
public import CFSG.Quasithin.EmptyFaithful.Gap6R2Push
public import CFSG.Quasithin.EmptyFaithful.S151b111

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6R2

variable {G : Type} [Group G] [Finite G]

section Stage

variable {T Mc M K N : Subgroup G}

theorem NonBorelK.setup_l3 (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M)
    (hCE : IsCE1513 T M) (h1511one : StageLemma15111One) (hK : NonBorelK T Mc M K N)
    (hab : ∀ a ∈ N, Odd (orderOf a) → ∀ b ∈ N, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 N) :
    L3.Setup T N (V154 T Mc M) (pCoreOf 2 N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hMf.1.1.2
  have hTN : T ≤ N := hK.T_le_N
  have hNK : N ≤ K := hK.N_lt_K.le
  have hsylN : IsSylowTwoOf T N := Gap6.isSylowTwoOf_of_le_gap6 h.sylow hTN
  have hVT : V154 T Mc M ≤ T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hMf.1.1).2
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  refine
    { PN := pCoreOf_le 2 N
      Pnorm := le_normalizer_pCoreOf 2 N
      P2 := pCoreOf_isPGroup 2 N
      Pmax := fun W hWN hNW hW2 => le_pCoreOf_of_le_normalizer 2 hWN hNW hW2
      TN := hTN
      T2 := h.sylow.1
      PT := F7.isSylowTwoOf_pCoreOf_le hsylN
      gen := eq_oTwoUpper_sup_of_isSylowTwoOf hsylN
      VT := hVT
      TV := hTM.trans (le_normalizer_V154 T Mc M)
      ab := hab
      dich := fun H hTH hHN hminH => ?_ }
  by_cases hHM : H ≤ M
  · exact Or.inl (hHM.trans (le_normalizer_V154 T Mc M))
  · refine Or.inr ?_
    have hHK : H ≤ K := hHN.trans hNK
    have hZH : quasithinOmegaOneCenter T ≤ pCoreOf 2 H :=
      le_pCoreOf_of_le_normalizer 2 (hZT.trans hTH)
        (fun x hx => Subgroup.centralizer_le_normalizer _ (hK.le_centralizer (hHK hx)))
        (h.sylow.1.to_le hZT)
    have hInH : InH T H :=
      ⟨hTH, fun hbot => h.omegaOneCenter_ne_bot (le_bot_iff.1 (hZH.trans hbot.le))⟩
    have hStar : IsHStar T M H := by
      refine ⟨hInH, hHM, fun Y hY hYH hYM => ?_⟩
      rcases hminH Y hY.1 hYH with hYT | hYH'
      · exact absurd (hYT ▸ hTM) hYM
      · exact hYH'
    exact ⟨pCoreOf 2 H, h1511one G T Mc M h hMf hCE H hStar, pCoreOf_le 2 H,
      pCoreOf_isPGroup 2 H, le_normalizer_pCoreOf 2 H⟩

theorem NonBorelK.V_le_pCoreOf_of_oddComm (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M)
    (hCE : IsCE1513 T M) (h1511one : StageLemma15111One) (hK : NonBorelK T Mc M K N)
    (hab : ∀ a ∈ N, Odd (orderOf a) → ∀ b ∈ N, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 N) :
    V154 T Mc M ≤ pCoreOf 2 N :=
  (hK.setup_l3 h hMf hCE h1511one hab).le

end Stage

end Gap6R2

end CFSG.Quasithin
