module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem le_normalizer_inf_of_le_normalizer {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    X ≤ Subgroup.normalizer ((X ⊓ N : Subgroup G) : Set G) := by
  intro x hx
  have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx)
  have h2 := Subgroup.mem_normalizer_iff.mp (hXN hx)
  exact Subgroup.mem_normalizer_iff.mpr fun g => by
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
    exact and_congr (h1 g) (h2 g)

theorem pCoreOf_le_pCoreOf_of_le_sup {X K : Subgroup G} (hXK : X ≤ K)
    (hK : K ≤ X ⊔ CFSG.Open.pCoreOf p K) :
    CFSG.Open.pCoreOf p X ≤ CFSG.Open.pCoreOf p K := by
  set U := CFSG.Open.pCoreOf p X
  set V := CFSG.Open.pCoreOf p K
  have hXV : X ≤ Subgroup.normalizer (V : Set G) :=
    hXK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p K)
  have hUX : U ≤ X := CFSG.LieType.BorelTits.pCoreOf_le p X
  have hN : IsPGroup p ↥(U ⊔ V) :=
    IsPGroup.to_sup_of_normal_right' (CFSG.LieType.BorelTits.pCoreOf_isPGroup p X)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p K) (hUX.trans hXV)
  have hXN : X ≤ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_sup U V
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf p X hx, hXV hx⟩
  have hKN : K ≤ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) :=
    hK.trans (sup_le hXN (le_sup_right.trans Subgroup.le_normalizer))
  have hle : U ⊔ V ≤ V :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
      (sup_le (hUX.trans hXK) (CFSG.LieType.BorelTits.pCoreOf_le p K)) hKN hN
  exact le_sup_left.trans hle

theorem inf_pCoreOf_eq_pCoreOf_of_le_sup {X K : Subgroup G} (hXK : X ≤ K)
    (hK : K ≤ X ⊔ CFSG.Open.pCoreOf p K) :
    X ⊓ CFSG.Open.pCoreOf p K = CFSG.Open.pCoreOf p X := by
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le p X)
    (pCoreOf_le_pCoreOf_of_le_sup hXK hK))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p inf_le_left
    (le_normalizer_inf_of_le_normalizer
      (hXK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p K)))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup p K).to_le inf_le_right)

theorem eq_sup_pCoreOf_of_le {L X K : Subgroup G} (hLX : L ≤ X) (hXK : X ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf p K) :
    X = L ⊔ CFSG.Open.pCoreOf p X := by
  have hK : K ≤ X ⊔ CFSG.Open.pCoreOf p K := hKL.le.trans (sup_le_sup_right hLX _)
  refine le_antisymm (fun x hx => ?_)
    (sup_le hLX (CFSG.LieType.BorelTits.pCoreOf_le p X))
  have hxK : x ∈ L ⊔ CFSG.Open.pCoreOf p K := by
    rw [← hKL]
    exact hXK hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L _
    ((hLX.trans hXK).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p K))] at hxK
  obtain ⟨l, hl, v, hv, rfl⟩ := hxK
  have hvX : v ∈ X := by
    have h := X.mul_mem (X.inv_mem (hLX hl)) hx
    rwa [inv_mul_cancel_left] at h
  have hvU : v ∈ CFSG.Open.pCoreOf p X := by
    rw [← inf_pCoreOf_eq_pCoreOf_of_le_sup hXK hK]
    exact ⟨hvX, hv⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hvU)

theorem inf_centralizer_le_pCoreOf {L X : Subgroup G} (hX : IsCharacteristicP p ↥X)
    (hLX : L ≤ X) :
    L ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf p X : Set G) ≤ CFSG.Open.pCoreOf p L := by
  have hCU : X ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf p X : Set G) ≤
      CFSG.Open.pCoreOf p X := by
    rintro x ⟨hxX, hxC⟩
    have hcent : (⟨x, hxX⟩ : ↥X) ∈ Subgroup.centralizer (CFSG.pCore p ↥X : Set ↥X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzU : (z : G) ∈ CFSG.Open.pCoreOf p X := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC z hzU)
    exact Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, hX hcent, rfl⟩
  have hLU : L ⊓ CFSG.Open.pCoreOf p X ≤ CFSG.Open.pCoreOf p L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p inf_le_left
      (le_normalizer_inf_of_le_normalizer
        (hLX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p X)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup p X).to_le inf_le_right)
  exact fun x hx => hLU ⟨hx.1, hCU ⟨hLX hx.1, hx.2⟩⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
