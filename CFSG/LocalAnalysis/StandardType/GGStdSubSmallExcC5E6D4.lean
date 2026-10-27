module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6D4Layer

public section

namespace CFSG.StandardType.SmallExc.E6Node

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.StandardType.TableBExc.E6Three CFSG.SeitzReduction

@[expose] def coordD4 : Multiplicative (Fin 4 → ZMod 3) →* Multiplicative (ZMod 3) where
  toFun w := Multiplicative.ofAdd (Multiplicative.toAdd w 0 + Multiplicative.toAdd w 1)
  map_one' := by simp
  map_mul' w w' := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
    abel

theorem mem_ker_coordD4 (w : Multiplicative (Fin 4 → ZMod 3)) :
    w ∈ coordD4.ker ↔ Multiplicative.toAdd w 0 + Multiplicative.toAdd w 1 = 0 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd (Multiplicative.toAdd w 0 + Multiplicative.toAdd w 1) = 1 ↔ _
  exact ofAdd_eq_one

theorem card_ker_coordD4 : Nat.card coordD4.ker = 27 := by
  have hs : Function.Surjective coordD4 := fun a =>
    ⟨Multiplicative.ofAdd (Pi.single 0 (Multiplicative.toAdd a)), by
      change Multiplicative.ofAdd ((Pi.single 0 (Multiplicative.toAdd a) : Fin 4 → ZMod 3) 0 +
        (Pi.single 0 (Multiplicative.toAdd a) : Fin 4 → ZMod 3) 1) = a
      simp⟩
  have h := Subgroup.card_ker_mul_card_of_surjective hs
  have h1 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h2 : Nat.card (Multiplicative (Fin 4 → ZMod 3)) = 81 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [h1, h2] at h
  omega

theorem eq_of_add_eq_zero_d4 : ∀ v : Fin 4 → ZMod 3, v 0 + v 1 = 0 →
    v = (v 0).val • (Pi.single 0 1 - Pi.single 1 1) + (v 2).val • Pi.single 2 1 +
      (v 3).val • Pi.single 3 1 := by
  decide +kernel

section F


theorem liftConj_nD4_uE6Two {K : Type} [Field K] [Finite K] [CharP K 2]
    {P : SL2 (FiniteField.Extension K 2 2)} {l : (FiniteField.Extension K 2 2)ˣ}
    (hP : P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL (1 : K) * vSL 1) * P = HSL l) :
    liftConj (nD4 P) (uE6Two 0) = rootDiagUnit .E6 (hChar (bE6 0) l) ∧
      liftConj (nD4 P) (uE6Two 1) = rootDiagUnit .E6 (hChar (bE6 1) l) ∧
      liftConj (nD4 P) (uE6Two 2) = rootSL2 .E6 _ (bE6 2)
        (Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL 1 * vSL 1)) ∧
      liftConj (nD4 P) (uE6Two 3) = rootSL2 .E6 _ (bE6 3)
        (Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL 1 * vSL 1)) := by
  have e : ∀ i : Fin 4, liftConj (nD4 P) (uE6Two i) =
      (rootSL2 .E6 _ (bE6 1) P)⁻¹ * ((rootSL2 .E6 _ (bE6 0) P)⁻¹ *
        rootSL2 .E6 _ (bE6 i) (Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL 1 * vSL 1)) *
          rootSL2 .E6 _ (bE6 0) P) * rootSL2 .E6 _ (bE6 1) P :=
    fun i => by simp only [liftConj_apply, nD4, baseChangeGL_uE6Two, mul_inv_rev, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, conj_rootSL2_self, hP, conj_rootSL2_bE6_of_ne (by decide : (0 : Fin 4) ≠ 1),
      rootSL2_HSL_eq (isRoot_bE6 0)]
  · rw [e, conj_rootSL2_bE6_of_ne (by decide : (1 : Fin 4) ≠ 0), conj_rootSL2_self, hP,
      rootSL2_HSL_eq (isRoot_bE6 1)]
  · rw [e, conj_rootSL2_bE6_of_ne (by decide : (2 : Fin 4) ≠ 0),
      conj_rootSL2_bE6_of_ne (by decide : (2 : Fin 4) ≠ 1)]
  · rw [e, conj_rootSL2_bE6_of_ne (by decide : (3 : Fin 4) ≠ 0),
      conj_rootSL2_bE6_of_ne (by decide : (3 : Fin 4) ≠ 1)]

theorem liftConj_nD4_torusE6Two {K : Type} [Field K] [Finite K] [CharP K 2] (h2 : (2 : K) = 0)
    {P : SL2 (FiniteField.Extension K 2 2)} {l : (FiniteField.Extension K 2 2)ˣ}
    (hl : orderOf l = 3)
    (hP : P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL (1 : K) * vSL 1) * P = HSL l) :
    liftConj (nD4 P) (torusE6Two h2 (.ofAdd d2E6)) = rootDiagUnit .E6 (chiD4 l) ∧
      ∀ v : Fin 4 → ZMod 3, v 0 + v 1 = 0 → torusE6Two h2 (.ofAdd v) ∈
        (rootSpan .E6 _ (rootCharKernel (chiD4 l))).comap (liftConj (nD4 P)) := by
  obtain ⟨h0, h1, hu2, hu3⟩ := liftConj_nD4_uE6Two hP
  have hu : ∀ i : Fin 4, torusE6Two h2 (.ofAdd (Pi.single i 1)) = uE6Two (K := K) i := fun i => by
    rw [torusE6Two_single, CFSG.RankThree.CentralCover.zmodPowHom_apply, ZMod.val_one, pow_one]
  refine ⟨?_, fun v hv => ?_⟩
  · rw [show d2E6 = Pi.single 0 1 + Pi.single 1 1 by decide +kernel, chiD4, rootDiagUnit_mul]
    simp only [ofAdd_add, map_mul, hu, h0, h1]
  have hw : torusE6Two h2 (.ofAdd (Pi.single 0 1 - Pi.single 1 1)) ∈
      (rootSpan .E6 _ (rootCharKernel (chiD4 l))).comap (liftConj (nD4 P)) := by
    rw [Subgroup.mem_comap, ofAdd_sub, map_div, hu, hu, map_div, h0, h1, div_eq_mul_inv]
    exact rootDiagUnit_hChar_mem_rootSpan_d4 hl
  have hw2 : torusE6Two h2 (.ofAdd (Pi.single 2 1)) ∈
      (rootSpan .E6 _ (rootCharKernel (chiD4 l))).comap (liftConj (nD4 P)) := by
    rw [Subgroup.mem_comap, hu, hu2]
    exact rootSL2_mem_rootSpan_d4 hl (by simp [d4Roots]) (by simp [d4Roots]) _
  have hw3 : torusE6Two h2 (.ofAdd (Pi.single 3 1)) ∈
      (rootSpan .E6 _ (rootCharKernel (chiD4 l))).comap (liftConj (nD4 P)) := by
    rw [Subgroup.mem_comap, hu, hu3]
    exact rootSL2_mem_rootSpan_d4 hl (by simp [d4Roots]) (by simp [d4Roots]) _
  rw [eq_of_add_eq_zero_d4 v hv, ofAdd_add, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, ofAdd_nsmul,
    map_mul, map_mul, map_pow, map_pow, map_pow]
  exact mul_mem (mul_mem (pow_mem hw _) (pow_mem hw2 _)) (pow_mem hw3 _)

theorem ggE6TwoD4NodeInput_holds : GGE6TwoD4NodeInput := by
  rintro K _ _ h2 hK - -
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  obtain ⟨-, l, hl, -⟩ := exists_inv_mul_map_uvSL_mul_eq_HSL hK
  have hx := TableBExcTwoFusion.sq_add_self_add_one_eq_zero hl
  obtain ⟨ha, hv⟩ := liftConj_nD4_torusE6Two h2 hl (P := TableBExcTwoFusion.langP hx) (by
    rw [TableBExcTwoFusion.map_uSL_mul_vSL, mul_assoc, ← TableBExcTwoFusion.langP_mul_HSL hx,
      inv_mul_cancel_left])
  have hQC : (rootSpan .E6 _ (rootCharKernel (chiD4 l))).comap
      (liftConj (nD4 (TableBExcTwoFusion.langP hx))) ≤
        Subgroup.centralizer {torusE6Two h2 (.ofAdd d2E6)} := fun c hc => by
    have h := (mem_toralCentralizer.1
      (rootSpan_rootCharKernel_le_toralCentralizer _ (Subgroup.mem_comap.1 hc))).2
    rw [← ha, ← map_inv, ← map_mul, ← map_mul] at h
    exact Subgroup.mem_centralizer_singleton_iff.2
      (mul_inv_eq_iff_eq_mul.1 (liftConj_injective _ h)).symm
  have hQE := le_largeEvenLayer ⟨hQC, Assembly.IsSubnormal.step hQC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQC).2 (centralizer_le_normalizer_comap
      (nD4_mem _) ha (toralCentralizer_le_normalizer_rootSpan _))) (Assembly.IsSubnormal.refl _),
    isQuasisimple_comap_liftConj_nD4 hK hx hl⟩
  have hle : coordD4.ker.map (torusE6Two h2) ≤ (torusE6Two (K := K) h2).range ⊓
      LargeEvenLayer (Subgroup.centralizer {torusE6Two h2 (.ofAdd d2E6)}) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, rfl⟩, hQE (hv _ ((mem_ker_coordD4 w).1 hw))⟩
  calc 3 ^ 3 = Nat.card (coordD4.ker.map (torusE6Two h2)) := by
        rw [Subgroup.card_map_of_injective (torusE6Two_injective h2), card_ker_coordD4]
        norm_num
    _ ≤ _ := Subgroup.card_le_of_le hle

end F

end CFSG.StandardType.SmallExc.E6Node

end
