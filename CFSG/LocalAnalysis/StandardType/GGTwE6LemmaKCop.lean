module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKDefs
public import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll

public noncomputable section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

namespace Aux

private def zeta7 : (ZMod 7)ˣ := Units.mk0 (2 : ZMod 7) (by decide)

private theorem orderOf_zeta7 : orderOf zeta7 = 3 := by
  unfold zeta7
  apply orderOf_eq_prime <;> decide

private theorem cubeTuple_pow_three {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (v : Fin 6 → ZMod 3) : cubeTuple ζ v ^ 3 = 1 := by
  funext i
  simp only [Pi.pow_apply, Pi.one_apply, cubeTuple]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]

end Aux

theorem rootChar_cubeTuple_eq_one_iff {K : Type} [Field K] {ζ : Kˣ} (hζ : orderOf ζ = 3)
    (y : Fin 6 → ZMod 3) (α : Fin Tag.E6.rank → ℤ) :
    rootChar (cubeTuple ζ y) α = 1 ↔ ∑ i : Fin 6, ((α (e6Idx i) : ℤ) : ZMod 3) * y i = 0 := by
  have hroot : rootChar (cubeTuple ζ y) α =
      ζ ^ (∑ i : Fin Tag.E6.rank, ((y (e6Idx.symm i)).val : ℤ) * α i) := by
    simp only [rootChar, cubeTuple]
    rw [← Finset.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
  have hm : ((∑ i : Fin Tag.E6.rank, ((y (e6Idx.symm i)).val : ℤ) * α i : ℤ) : ZMod 3) =
      ∑ i : Fin 6, ((α (e6Idx i) : ℤ) : ZMod 3) * y i := by
    push_cast
    refine Fintype.sum_equiv e6Idx.symm _ _ fun i => ?_
    rw [Equiv.apply_symm_apply, ZMod.natCast_zmod_val]
    ring
  rw [hroot, ← orderOf_dvd_iff_zpow_eq_one, hζ, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hm]

section Cop


private theorem famKernel_cubeTuple_subset (Y : Set (Fin 6 → ZMod 3)) :
    CFSG.RankThree.PartOne.KE8F.famKernel (cubeTuple Aux.zeta7 '' Y) ⊆ sigmaZ3 Y := by
  intro α hα
  obtain ⟨hroot, hker⟩ := hα
  exact ⟨hroot, fun y hy =>
    (rootChar_cubeTuple_eq_one_iff Aux.orderOf_zeta7 y α).1 (hker _ ⟨y, hy, rfl⟩)⟩

theorem mem_closure_sigmaZ3_of_coprime (Y : Set (Fin 6 → ZMod 3)) {u : WeylGroup Tag.E6}
    (hu : ∀ y ∈ Y, e6WeylMat u *ᵥ y = y) (hcop : Nat.Coprime (orderOf u) 3) :
    u ∈ Subgroup.closure {s | ∃ α ∈ sigmaZ3 Y, s = rootReflection α} := by
  have h3 : Aux.zeta7 ^ 3 = 1 := by
    rw [← Aux.orderOf_zeta7]
    exact pow_orderOf_eq_one _
  have hF : ∀ a ∈ cubeTuple Aux.zeta7 '' Y, ∃ n : ℕ, a ^ 3 ^ n = 1 := by
    rintro a ⟨y, -, rfl⟩
    exact ⟨1, by simpa only [pow_one] using Aux.cubeTuple_pow_three h3 y⟩
  have hstab : u ∈ CFSG.StandardType.LayerExc.famStabilizerSubgroup (cubeTuple Aux.zeta7 '' Y) := by
    show ∀ a ∈ cubeTuple Aux.zeta7 '' Y, ∀ v, rootChar a (u • v) = rootChar a v
    rintro a ⟨y, hy, rfl⟩ v
    have hmat : e6WeylMat u⁻¹ *ᵥ y = y := by
      calc e6WeylMat u⁻¹ *ᵥ y
          = e6WeylMat u⁻¹ *ᵥ (e6WeylMat u *ᵥ y) := by rw [hu y hy]
        _ = (e6WeylMat u⁻¹ * e6WeylMat u) *ᵥ y := by rw [Matrix.mulVec_mulVec]
        _ = y := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    have h1 : rootChar (cubeTuple Aux.zeta7 y) (u • v) =
        rootChar (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct u⁻¹ (cubeTuple Aux.zeta7 y)) v := by
      conv_lhs => rw [← inv_inv u]
      rw [← rootChar_weylAct]
    rw [h1, weylAct_cubeTuple Aux.orderOf_zeta7, hmat]
  have hmem : u ∈ CFSG.StandardType.LayerExc.famReflectionGroup (cubeTuple Aux.zeta7 '' Y) :=
    CFSG.StandardType.LayerExc.mem_famReflectionGroup_of_coprime_orderOf
      Nat.prime_three (cubeTuple Aux.zeta7 '' Y) hF hstab hcop
  have hmem' : u ∈ Subgroup.closure
      {s | ∃ α ∈ CFSG.RankThree.PartOne.KE8F.famKernel (cubeTuple Aux.zeta7 '' Y),
        s = rootReflection α} := hmem
  refine Subgroup.closure_mono ?_ hmem'
  rintro s ⟨α, hα, rfl⟩
  exact ⟨α, famKernel_cubeTuple_subset Y hα, rfl⟩

end Cop

end CFSG.StandardType.TwE6LemmaK
