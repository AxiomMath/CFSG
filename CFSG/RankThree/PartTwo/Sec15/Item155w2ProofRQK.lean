module

public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorrDefs
import CFSG.RankThree.PartTwo.Sec15.Item155wProof
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof155w2

omit [Finite G] in
theorem isPerfect_sup {X Z : Subgroup G} (hX : Group.IsPerfect ↥X) (hZ : Group.IsPerfect ↥Z) :
    Group.IsPerfect ↥(X ⊔ Z) := by
  rw [Subgroup.isPerfect_iff] at hX hZ ⊢
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [Subgroup.commutator_le]
    intro x hx z hz
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hz) (inv_mem hx)) (inv_mem hz)
  · calc X = ⁅X, X⁆ := hX.symm
      _ ≤ ⁅X ⊔ Z, X ⊔ Z⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc Z = ⁅Z, Z⁆ := hZ.symm
      _ ≤ ⁅X ⊔ Z, X ⊔ Z⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem le_normalizer_of_isPGroup_of_le_normalizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A))
    {K X D : Subgroup G} (hK : K ∈ scriptY0Star A (lB A)) (hXp : Group.IsPerfect ↥X)
    (hX1 : X ≠ ⊥) (hXK : X ≤ K) (hD2 : IsPGroup 2 D) (hDN : D ≤ n155 A K)
    (hXD : X ≤ Subgroup.normalizer (D : Set G)) : D ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  set N := n155 A K with hN
  have hXN : X ≤ N := hXK.trans (Subgroup.le_normalizer.trans (normalizer_le_n155w h153 hK))
  set Xy := X.map (MulAut.conj y).toMonoidHom with hXy
  have hXyp : Group.IsPerfect ↥Xy := by
    have := hXp
    exact Group.IsPerfect.map (MulAut.conj y).toMonoidHom
  have hXy1 : Xy ≠ ⊥ := fun h0 =>
    hX1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj y).injective).mp h0)
  have hyD : y ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hy
  have hXyN : Xy ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem (hDN hy) (hXN hx)) (inv_mem (hDN hy))
  have hXyXD : Xy ≤ X ⊔ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hx))
      (inv_mem (Subgroup.mem_sup_right hy))
  have hXyD : Xy ≤ Subgroup.normalizer (D : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hyD (hXD hx)) (inv_mem hyD)
  set W := X ⊔ Xy with hW
  have hWp : Group.IsPerfect ↥W := isPerfect_sup hXp hXyp
  have hWN : W ≤ N := sup_le hXN hXyN
  have hWK : W ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_isPerfect_of_le_n155 h h152 h153 hK hWp hWN
  have hWD : W ≤ Subgroup.normalizer (D : Set G) := sup_le hXD hXyD
  have hWXD : W ≤ X ⊔ (W ⊓ D) :=
    Proof155w.le_sup_inf_of_le hXD le_sup_left (sup_le le_sup_left hXyXD)
  have hWDs : Group.IsSolvable ↥(W ⊓ D) := by
    have : Group.IsNilpotent ↥(W ⊓ D) := (hD2.to_le inf_le_right).isNilpotent
    infer_instance
  have hWleK : W ≤ K := Sec17.Proof171Steps.le_of_isPerfect_of_le_sup hWp le_sup_left
    (Late.le_normalizer_inf Subgroup.le_normalizer hWD) hWDs inf_le_left hWXD hXK hWK
  have hXyK : Xy ≤ K := le_sup_right.trans hWleK
  have hK𝓛 : K ∈ thetaComponentsIn N :=
    mem_thetaComponentsIn_of_item152 h h152 hK (n155_mem_maximalTwoLocalsContaining h153 hK)
  have hyN : y ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer (hDN hy)
  have hKy𝓛 := map_conj_mem_thetaComponentsIn hyN hK𝓛
  have hXyKy : Xy ≤ K.map (MulAut.conj y).toMonoidHom := Subgroup.map_mono hXK
  have heq := Sec6.eq_of_mem_thetaComponentsIn_of_le hK𝓛 hKy𝓛 hXyp hXy1 hXyK hXyKy
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm

end Proof155w2

theorem step155RQKW_of {A : Subgroup G} {c : G} {L : Subgroup G} (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) : Step155RQKW A c L := by
  intro h X K Y M T P J hC _ _ _ _ hXJ _
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hXQ : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (P ⊔ J) : Set G) :=
    (hXJ.trans le_sup_right).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hXN : X ≤ Subgroup.normalizer (n155 A K : Set G) :=
    (hC.le_k.trans (Subgroup.le_normalizer.trans (normalizer_le_n155w h153 hC.mem_k))).trans
      Subgroup.le_normalizer
  exact Proof155w2.le_normalizer_of_isPGroup_of_le_normalizer h h152 h153 hC.mem_k
    (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hC.le_k
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _).to_le inf_le_left) inf_le_right
    (Late.le_normalizer_inf hXQ hXN)

end CFSG.RankThree.PartTwo.Sec15
