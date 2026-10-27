module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenGen
public import CFSG.RankThree.PartTwo.CTU6.Long
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpEquiv
import CFSG.RankThree.PartTwo.CTU6.WeakCT
public import CFSG.RankThree.PartOne.CTP.SpNode
public import CFSG.RankThree.PartOne.CTP.SpPos

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open CFSG.RankThree.PartTwo
open scoped MatrixGroups

private theorem su_card_range_comp {G H F : Type} [Group G] [Group H] [Field F]
    {ρ : H →* G} {r : SL(2, F) →* H} (hρ : Function.Injective ρ)
    (hr : Function.Injective r) : Nat.card (ρ.comp r).range = Nat.card (SL(2, F)) := by
  have hinj : Function.Injective (ρ.comp r) := hρ.comp hr
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem su_agreement_crossing_of_range_le {G : Type} [Group G] [Finite G]
    {p n a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ha : 2 ≤ a)
    {Bs L : Subgroup G} {x : G}
    (hBc : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b)
    (hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxB : x ∈ Bs) (hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin 4 ≃ Fin n}
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {σ : SL(4, GaloisField 2 (2 * a)) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 (2 * a))ˣ}
    (hσ : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    {ρ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G}
    (hρ : Function.Injective ρ)
    (hK0 : (ρ.comp (CTU6.rS0 _ (unitaryInvolution_involutive
        (card_galoisField_two_mul 2 a (by omega))))).range ≤
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆)
    (hK1 : (ρ.comp (CTU6.rS1 _ (unitaryInvolution_involutive
        (card_galoisField_two_mul 2 a (by omega))))).range ≤
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 3) : Set G), Bs⁆)
    (hK2 : ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π 3) : Set G), Bs⁆ =
      (ρ.comp (CTU6.rL (GaloisField 2 (2 * a)) a)).range) :
    (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
        (ρ.comp (CTU6.rS0 _ (unitaryInvolution_involutive
          (card_galoisField_two_mul 2 a (by omega))))).range ∧
    (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
        (ρ.comp (CTU6.rS1 _ (unitaryInvolution_involutive
          (card_galoisField_two_mul 2 a (by omega))))).range ∧
    ∀ u ∈ (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ v ∈ (ρ.comp (CTU6.rL (GaloisField 2 (2 * a)) a)).range, u * v = v * u := by
  have hF := card_galoisField_two_mul 2 a (by omega)
  have hC0 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 0) (π 1) : Set G), Bs⁆ =
      (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range :=
    ggSecFiveBPermSp_reflComm_L (r := 2) hp2 (by decide) hBc hBsmax hxB hL hσ 0
  have hC1 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆ =
      (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range :=
    ggSecFiveBPermSp_reflComm_L (r := 2) hp2 (by decide) hBc hBsmax hxB hL hσ 1
  have hC2 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 3) : Set G), Bs⁆ =
      (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range :=
    ggSecFiveBPermSp_reflComm_L (r := 2) hp2 (by decide) hBc hBsmax hxB hL hσ 2
  have hcard0 : Nat.card (ρ.comp (CTU6.rS0 _ (unitaryInvolution_involutive hF))).range =
      Nat.card (SL(2, GaloisField 2 (2 * a))) :=
    su_card_range_comp hρ (CTU6.rS0_injective (unitaryInvolution_involutive hF))
  have hcard1 : Nat.card (ρ.comp (CTU6.rS1 _ (unitaryInvolution_involutive hF))).range =
      Nat.card (SL(2, GaloisField 2 (2 * a))) :=
    su_card_range_comp hρ (CTU6.rS1_injective (unitaryInvolution_involutive hF))
  have hcardL (i : Fin 3) : Nat.card (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 i)).range ≤
      Nat.card (SL(2, GaloisField 2 (2 * a))) :=
    Nat.card_le_card_of_surjective (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 i)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hAgree0 : (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
      (ρ.comp (CTU6.rS0 _ (unitaryInvolution_involutive hF))).range := by
    rw [hC1] at hK0
    exact (Subgroup.eq_of_le_of_card_ge hK0 (by rw [hcard0]; exact hcardL 1)).symm
  have hAgree1 : (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
      (ρ.comp (CTU6.rS1 _ (unitaryInvolution_involutive hF))).range := by
    rw [hC2] at hK1
    exact (Subgroup.eq_of_le_of_card_ge hK1 (by rw [hcard1]; exact hcardL 2)).symm
  refine ⟨hAgree0, hAgree1, ?_⟩
  obtain ⟨w, φ, g, hw_eq, hwcoord, hgconj⟩ :=
    ggSecFiveBSp_conjData (r := 2) (L := L) (Bs := Bs) (π := π) (by decide) hA
  have hw0 : w (π 0) = π 2 := by rw [hw_eq]; exact Equiv.swap_apply_left _ _
  have hw1 : w (π 1) = π 1 := by
    rw [hw_eq]
    exact Equiv.swap_apply_of_ne_of_ne (π.injective.ne (by decide : (1 : Fin 4) ≠ 0))
      (π.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  have hw3 : w (π 3) = π 3 := by
    rw [hw_eq]
    exact Equiv.swap_apply_of_ne_of_ne (π.injective.ne (by decide : (3 : Fin 4) ≠ 0))
      (π.injective.ne (by decide : (3 : Fin 4) ≠ 2))
  have hfirst : (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range.map
      (MulAut.conj g).toMonoidHom =
      (ρ.comp (CTU6.rS0 _ (unitaryInvolution_involutive hF))).range := by
    calc (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range.map
          (MulAut.conj g).toMonoidHom =
        (⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 0) (π 1) : Set G), Bs⁆).map
          (MulAut.conj g).toMonoidHom := by rw [hC0]
      _ = ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (w (π 0)) (w (π 1)) : Set G), Bs⁆ :=
        ggReflComm_map_conj hgconj hwcoord (π 0) (π 1)
      _ = (ρ.comp (CTU6.rS0 _ (unitaryInvolution_involutive hF))).range := by
        rw [hw0, hw1, ggBsCoordEq_comm, hC1, hAgree0]
  have hlast : (ρ.comp (CTU6.rL (GaloisField 2 (2 * a)) a)).range.map
      (MulAut.conj g).toMonoidHom =
      (ρ.comp (CTU6.rL (GaloisField 2 (2 * a)) a)).range := by
    calc (ρ.comp (CTU6.rL (GaloisField 2 (2 * a)) a)).range.map
          (MulAut.conj g).toMonoidHom =
        (⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π 3) : Set G), Bs⁆).map
          (MulAut.conj g).toMonoidHom := by rw [hK2]
      _ = ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (w (π 3)) : Set G), Bs⁆ :=
        ggSingletonComm_map_conj hgconj hwcoord (π 3)
      _ = (ρ.comp (CTU6.rL (GaloisField 2 (2 * a)) a)).range := by rw [hw3, hK2]
  intro u hu v hv
  have hgu : (MulAut.conj g) u ∈
      (ρ.comp (CTU6.rS0 _ (unitaryInvolution_involutive hF))).range := by
    rw [← hfirst]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hu
  have hgv : (MulAut.conj g) v ∈ (ρ.comp (CTU6.rL (GaloisField 2 (2 * a)) a)).range := by
    rw [← hlast]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hv
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hgu
  obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp hgv
  apply (MulAut.conj g).injective
  rw [map_mul, map_mul, ← hA, ← hB]
  exact ((CTU6.commute_rS0_rL hF A B).map ρ).eq

theorem ggSecFiveBPermSU_agreement_crossing_of_frames {G : Type} [Group G] [Finite G]
    {p n a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ha : 2 ≤ a)
    {Bs L K : Subgroup G} {x : G}
    (hBc : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b)
    (hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxB : x ∈ Bs) (hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin 4 ≃ Fin n}
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {σ : SL(4, GaloisField 2 (2 * a)) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 (2 * a))ˣ}
    (hσ : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (h : UnitaryFieldData 2 a (GaloisField 2 (2 * a))) {κ : hypSU h 3 0 →* G}
    (hκ : Function.Injective κ ∧ κ.range = K)
    (hK0 : ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
        (CTU6.rS0 _ (unitaryInvolution_involutive
          (card_galoisField_two_mul 2 a (by omega))))).range ≤
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 1) (π 2) : Set G), Bs⁆)
    (hK1 : ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
        (CTU6.rS1 _ (unitaryInvolution_involutive
          (card_galoisField_two_mul 2 a (by omega))))).range ≤
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 3) : Set G), Bs⁆)
    (hK2 : ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π 3) : Set G), Bs⁆ =
      ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
        (CTU6.rL (GaloisField 2 (2 * a)) a)).range) :
    let ρ := κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom
    (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
        (ρ.comp (CTU6.rS0 _ (unitaryInvolution_involutive
          (card_galoisField_two_mul 2 a (by omega))))).range ∧
    (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
        (ρ.comp (CTU6.rS1 _ (unitaryInvolution_involutive
          (card_galoisField_two_mul 2 a (by omega))))).range ∧
    ∀ u ∈ (σ.comp (blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
      ∀ v ∈ (ρ.comp (CTU6.rL (GaloisField 2 (2 * a)) a)).range, u * v = v * u := by
  exact su_agreement_crossing_of_range_le hp2 ha hBc hBsmax hxB hL hA hσ
    (hκ.1.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.injective) hK0 hK1 hK2

end CFSG.StandardType

end
