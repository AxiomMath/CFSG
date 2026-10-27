module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayerAux
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec21.Item219LieProof (d4_threeA_model d4_threeA_model_unitary)

namespace CFSG.RankThree.PartTwo.Sec19

section Layer


variable {n : ℕ} {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem classX_layer (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x) :
    x ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆ ∧
    ∀ z ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆,
      z ^ 3 = 1 →
      (∀ d ∈ ⁅Subgroup.centralizer ({x} : Set (C0 σ)), Subgroup.centralizer ({x} : Set (C0 σ))⁆,
        z * d = d * z) →
      z ∈ Subgroup.zpowers x := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hy1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have hf : 1 ≤ n := by omega
  have h2n : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hK : Nat.card X = (2 ^ n) ^ 3 := P.card
  have hσ : ∀ c : X, σ c = c ^ (2 ^ n) := P.frob
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · have hq1 : 2 ^ n % 3 = 1 := by
      rw [hm]
      exact TorusLayerAux.two_pow_mod_three_even m
    obtain ⟨c, R, hcR, hRc, hcomm, hq, F, hFi, hFf, -, ⟨e⟩⟩ :=
      d4_threeA_model Nat.prime_two hf (by norm_num) hq1 hK hσ hg hy3 hy1
    have hL : TorusLayerAux.LayerProp (c * (g * x * g⁻¹) * c⁻¹) :=
      TorusLayerAux.layer_of_SL _ R hq.1 hcR hRc hcomm
        (TorusLayerAux.conj_pow_eq_one (g := c) hy3)
        (TorusLayerAux.conj_ne_one (c := c) hy1) e
    exact TorusLayerAux.layerProp_of_conj g x (TorusLayerAux.layerProp_of_conj c _ hL)
  · have hq1 : 2 ^ n % 3 = 2 := by
      rw [hm]
      exact TorusLayerAux.two_pow_mod_three_odd m
    obtain ⟨c, R, hcR, hRc, hcomm, hq, U, -, e, hcen⟩ :=
      d4_threeA_model_unitary Nat.prime_two hf (by norm_num) hq1 h2n hK hσ hg hy3 hy1
    have hL : TorusLayerAux.LayerProp (c * (g * x * g⁻¹) * c⁻¹) :=
      TorusLayerAux.layer_of_SU _ R hq.1 hcR hRc hcomm
        (TorusLayerAux.conj_pow_eq_one (g := c) hy3)
        (TorusLayerAux.conj_ne_one (c := c) hy1) U e hcen
    exact TorusLayerAux.layerProp_of_conj g x (TorusLayerAux.layerProp_of_conj c _ hL)

end Layer

end CFSG.RankThree.PartTwo.Sec19
