module

import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofTypeOne

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open scoped Pointwise

namespace Proof1413Res6

theorem odd_card_centralizer_of_two {X : Type} [Group X] [Finite X] {e : ℕ}
    [Fact (Nat.Prime 2)] (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X 2 e) {E : Subgroup X}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {x : X} (hx : x ∈ E) (hx1 : x ≠ 1) :
    ¬ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) := by
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
  have := hK.finite
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) := by
    unfold Matrix.ProjGenLinGroup
    infer_instance
  have hEψ : CFSG.Assembly.IsElemAbelian 3 (E.map ψ.toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ψ.toMonoidHom E hEe
  have hEψ9 : Nat.card (E.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hE9]
  have htrψ : ∀ y₀ ∈ E.map ψ.toMonoidHom, y₀ ≠ 1 → ∀ y₁ ∈ E.map ψ.toMonoidHom, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer ((E.map ψ.toMonoidHom : Subgroup _) : Set _),
        w * y₀ * w⁻¹ = y₁ := by
    rintro _ ⟨y₀, hy₀, rfl⟩ hy₀1 _ ⟨y₁, hy₁, rfl⟩ hy₁1
    have hy₀1' : y₀ ≠ 1 := fun h => hy₀1 (by rw [h, map_one])
    have hy₁1' : y₁ ≠ 1 := fun h => hy₁1 (by rw [h, map_one])
    obtain ⟨w, hw, hwy⟩ := htr y₀ hy₀ hy₀1' y₁ hy₁ hy₁1'
    refine ⟨ψ w, ?_, ?_⟩
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨w, hw, rfl⟩
    · change ψ w * ψ y₀ * (ψ w)⁻¹ = ψ y₁
      rw [← map_inv, ← map_mul, ← map_mul, hwy]
  have hcube := Res8Hess.hasCubeOneLift_of_transitive hK hEψ hEψ9 htrψ
  have hψx1 : ψ x ≠ 1 := fun h => hx1 (ψ.injective (by rw [h, map_one]))
  have hdvd := Res8Hess.card_centralizer_dvd_of_hasCubeOneLift hK hq hψx1
    (hcube _ ⟨x, hx, rfl⟩ hψx1)
  have hcard : Nat.card (Subgroup.centralizer ({x} : Set X)) =
      Nat.card (Subgroup.centralizer ({ψ x} : Set (projImage (slPi π 3 (2 ^ e) K)))) := by
    rw [← CFSG.RankThree.PartTwo.map_centralizer_singleton ψ x,
      Subgroup.card_map_of_injective ψ.injective]
  rw [← hcard] at hdvd
  have hodd : ¬ 2 ∣ 3 * qSubPi π (2 ^ e) ^ 2 := by
    have h2e : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    have h1e : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have hq : ¬ 2 ∣ qSubPi π (2 ^ e) := by
      cases π
      · change ¬ 2 ∣ 2 ^ e + 1
        omega
      · change ¬ 2 ∣ 2 ^ e - 1
        omega
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h3 | h3
    · omega
    · exact hq (Nat.prime_two.dvd_of_dvd_pow h3)
  exact fun h => hodd (h.trans hdvd)

theorem eq_bot_of_isPGroup_two_of_hess {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hodd : ∀ x ∈ E, x ≠ 1 → ¬ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)))
    {V : Subgroup X} (hV2 : IsPGroup 2 V) (hEV : E ≤ Subgroup.normalizer (V : Set X)) :
    V = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 3 ↥E := Proof1413Res2.isElementaryAbelian_of_isElemAbelian hEe
  have : Nontrivial ↥E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE9]
    norm_num
  have hV3 : ¬ 3 ∣ Nat.card V := Proof1413Res3.not_three_dvd_of_isPGroup_two hV2
  have hle := PartOne.KE8F.le_iSup_hyperplane_centralizers hEV hV3
  rw [eq_bot_iff]
  refine hle.trans (iSup₂_le fun B hB => ?_)
  have hB3 : Nat.card B = 3 := by
    have h := Subgroup.card_mul_index B
    rw [hB, hE9] at h
    omega
  obtain ⟨b, hb1⟩ : ∃ b : ↥B, b ≠ 1 := by
    have : Nontrivial ↥B := by
      rw [← Finite.one_lt_card_iff_nontrivial, hB3]
      norm_num
    exact exists_ne 1
  have hbE : ((b : ↥E) : X) ∈ E := (b : ↥E).2
  have hb1' : ((b : ↥E) : X) ≠ 1 := by
    intro h
    apply hb1
    exact Subtype.ext (Subtype.ext h)
  have hle' : V ⊓ Subgroup.centralizer ((B.map E.subtype : Subgroup X) : Set X) ≤
      V ⊓ Subgroup.centralizer ({((b : ↥E) : X)} : Set X) :=
    inf_le_inf_left V (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr ⟨(b : ↥E), b.2, rfl⟩))
  refine hle'.trans (le_of_eq ?_)
  exact Proof1413Res3.eq_bot_of_isPGroup_two_of_le (hV2.to_le inf_le_left) inf_le_right
    (hodd _ hbE hb1')

variable {G : Type} [Group G]

end Proof1413Res6

end CFSG.RankThree.PartTwo.Sec14
