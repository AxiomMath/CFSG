module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAutSp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerU

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.E6Pilot (IsAutConj IsAutConjIn)
open CFSG.Quasithin (perfectCore)

section Orders

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem lieModel_map_conj {G : Type} [Group G] {H : Subgroup G}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : LieModel H t n p f) (g : G) :
    LieModel (H.map (MulAut.conj g).toMonoidHom) t n p f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) h

theorem card_su6Levi_map_conj (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (n : graphFixedRootGroup TwistTag.E6 K σ) :
    Nat.card (((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj n).toMonoidHom) = CFSG.Open.ordTwistedA 5 (2 ^ f) :=
  F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
    (lieModel_map_conj (lieModel_su6Levi_subgroupOf (k := k) hf hk hK hσ) n)

theorem card_uLevi_map_conj (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (n : graphFixedRootGroup TwistTag.E6 K σ) :
    Nat.card (((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      (MulAut.conj n).toMonoidHom) = CFSG.Open.ordBC 3 (2 ^ f) :=
  F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
    (lieModel_map_conj (lieModel_uLevi_subgroupOf (k := k) hf hk hK hσ) n)

theorem ordTwistedA_five_ne_ordBC_three (hf : 1 ≤ f) :
    CFSG.Open.ordTwistedA 5 (2 ^ f) ≠ CFSG.Open.ordBC 3 (2 ^ f) :=
  (CFSG.Timmesfeld.Orders.ordBC_ne_ordTwistedA (n := 3) (u := 5) (by norm_num) hf (by norm_num)
    hf).symm

theorem eq_of_mulEquiv_of_card_ne {G : Type*} [Group G] {M : Fin 2 → Subgroup G}
    (hc : Nat.card (M 0) ≠ Nat.card (M 1)) {κ κ' : Fin 2} (ι : M κ ≃* M κ') : κ = κ' := by
  have hcard : Nat.card (M κ) = Nat.card (M κ') := Nat.card_congr ι.toEquiv
  match κ, κ' with
  | 0, 0 => rfl
  | 1, 1 => rfl
  | 0, 1 => exact absurd hcard hc
  | 1, 0 => exact absurd hcard.symm hc

end Orders

section F5

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem isAutConjIn_leviX (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : Fin 2) :
    IsAutConjIn (![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom] κ)
      ((E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)) := by
  match κ with
  | 0 => exact isAutConjIn_levi_tX hf hK hσ hk
  | 1 => exact isAutConjIn_levi_uX hf hk hK hσ

theorem factF5_leviX (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ κ' : Fin 2)
    (ι : (![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom] κ) ≃*
      (![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom] κ')) :
    κ = κ' ∧ ∃ m ∈ (![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom] κ'),
      ((((E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).subgroupOf _).map ι.toMonoidHom).map
          (Subgroup.subtype _) =
        ((E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ)).map (MulAut.conj m).toMonoidHom := by
  have hc : Nat.card (![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom] 0) ≠
      Nat.card (![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom] 1) := by
    change Nat.card (((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom) ≠
      Nat.card (((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom)
    rw [card_su6Levi_map_conj hf hk hK hσ, card_uLevi_map_conj hf hk hK hσ]
    exact ordTwistedA_five_ne_ordBC_three hf
  obtain rfl := eq_of_mulEquiv_of_card_ne hc ι
  exact ⟨rfl, isAutConjIn_leviX hf hk hK hσ κ ι⟩

end F5

end CFSG.SeitzReduction.TwistedE6Pilot
