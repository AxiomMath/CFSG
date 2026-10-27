module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6IsoRoots

public section

namespace CFSG.StandardType.SmallExc.E6Node

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.StandardType.TableBExc.E6Three CFSG.SeitzReduction

section R


section RL

variable {L : Type} [Field L]

@[expose] noncomputable def nIso (P : SL2 L) : ModGL .E6 L :=
  rootSL2 .E6 L (bE6 0) P * rootSL2 .E6 L (bE6 1) P * rootSL2 .E6 L (bE6 2) P

theorem nIso_mem (P : SL2 L) : nIso P ∈ adjointGroup .E6 L :=
  mul_mem (mul_mem (rootSL2_mem_adjointGroup (isRoot_bE6 0) P)
    (rootSL2_mem_adjointGroup (isRoot_bE6 1) P)) (rootSL2_mem_adjointGroup (isRoot_bE6 2) P)

theorem rootDiagUnit_hChar_mem_rootSpan (l : Lˣ) :
    rootDiagUnit .E6 (hChar (bE6 0) l) * (rootDiagUnit .E6 (hChar (bE6 1) l))⁻¹ ∈
      rootSpan .E6 L {γ | γ ∈ isoRoots} := by
  obtain ⟨hE1, hE2, hB1, hB2⟩ := mem_isoRoots
  have e : hChar (bE6 0) l * (hChar (bE6 1) l)⁻¹ = hChar eIso l * (hChar bIso l)⁻¹ := by
    funext j
    simp only [hChar, Pi.mul_apply, Pi.inv_apply, ← zpow_neg, ← zpow_add, ← sub_eq_add_neg,
      iform_sub_iso j]
  rw [rootDiagUnit_inv, ← rootDiagUnit_mul, e, rootDiagUnit_mul, ← rootDiagUnit_inv,
    ← rootSL2_HSL_eq (isRoot_of_mem_isoRoots hE1), ← rootSL2_HSL_eq (isRoot_of_mem_isoRoots hB1)]
  exact mul_mem (rootSL2_mem_rootSpan (isRoot_of_mem_isoRoots hE1) hE1 hE2 _)
    (inv_mem (rootSL2_mem_rootSpan (isRoot_of_mem_isoRoots hB1) hB1 hB2 _))

end RL

section F


theorem torusE6Two_not_mem_zpowers {K : Type} [Field K] (h2 : (2 : K) = 0)
    {v w : Fin 4 → ZMod 3} (hw : ∀ k : ZMod 3, w ≠ k • v) :
    torusE6Two (K := K) h2 (.ofAdd w) ∉ Subgroup.zpowers (torusE6Two h2 (.ofAdd v)) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← map_zpow, ← ofAdd_zsmul] at hk
  have h' := Multiplicative.ofAdd.injective (torusE6Two_injective h2 hk)
  exact hw k (by rw [← h', Int.cast_smul_eq_zsmul])

theorem liftConj_nIso_uE6Two {K : Type} [Field K] [Finite K] [CharP K 2]
    {P : SL2 (FiniteField.Extension K 2 2)} {l : (FiniteField.Extension K 2 2)ˣ}
    (hP : P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL (1 : K) * vSL 1) * P = HSL l) :
    liftConj (nIso P) (uE6Two 0) = rootDiagUnit .E6 (hChar (bE6 0) l) ∧
      liftConj (nIso P) (uE6Two 1) = rootDiagUnit .E6 (hChar (bE6 1) l) ∧
      liftConj (nIso P) (uE6Two 2) = rootDiagUnit .E6 (hChar (bE6 2) l) ∧
      liftConj (nIso P) (uE6Two 3) = rootSL2 .E6 _ (bE6 3)
        (Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL 1 * vSL 1)) := by
  have e : ∀ i : Fin 4, liftConj (nIso P) (uE6Two i) =
      (rootSL2 .E6 _ (bE6 2) P)⁻¹ * ((rootSL2 .E6 _ (bE6 1) P)⁻¹ * ((rootSL2 .E6 _ (bE6 0) P)⁻¹ *
        rootSL2 .E6 _ (bE6 i) (Matrix.SpecialLinearGroup.map (algebraMap K _) (uSL 1 * vSL 1)) *
          rootSL2 .E6 _ (bE6 0) P) * rootSL2 .E6 _ (bE6 1) P) * rootSL2 .E6 _ (bE6 2) P :=
    fun i => by simp only [liftConj_apply, nIso, baseChangeGL_uE6Two, mul_inv_rev, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, conj_rootSL2_self, hP, conj_rootSL2_bE6_of_ne (by decide : (0 : Fin 4) ≠ 1),
      conj_rootSL2_bE6_of_ne (by decide : (0 : Fin 4) ≠ 2), rootSL2_HSL_eq (isRoot_bE6 0)]
  · rw [e, conj_rootSL2_bE6_of_ne (by decide : (1 : Fin 4) ≠ 0), conj_rootSL2_self, hP,
      conj_rootSL2_bE6_of_ne (by decide : (1 : Fin 4) ≠ 2), rootSL2_HSL_eq (isRoot_bE6 1)]
  · rw [e, conj_rootSL2_bE6_of_ne (by decide : (2 : Fin 4) ≠ 0),
      conj_rootSL2_bE6_of_ne (by decide : (2 : Fin 4) ≠ 1), conj_rootSL2_self, hP,
      rootSL2_HSL_eq (isRoot_bE6 2)]
  · rw [e, conj_rootSL2_bE6_of_ne (by decide : (3 : Fin 4) ≠ 0),
      conj_rootSL2_bE6_of_ne (by decide : (3 : Fin 4) ≠ 1),
      conj_rootSL2_bE6_of_ne (by decide : (3 : Fin 4) ≠ 2)]

theorem ggE6TwoIsoNodeInput_holds : GGE6TwoIsoNodeInput := by
  rintro K _ _ h2 hK ⟨hE, hcent⟩
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  obtain ⟨P, l, hl, hP⟩ := exists_inv_mul_map_uvSL_mul_eq_HSL hK
  obtain ⟨h0, h1, h2', h3⟩ := liftConj_nIso_uE6Two hP
  have hu : ∀ i : Fin 4, torusE6Two h2 (.ofAdd (Pi.single i 1)) = uE6Two (K := K) i := fun i => by
    rw [torusE6Two_single, CFSG.RankThree.CentralCover.zmodPowHom_apply, ZMod.val_one, pow_one]
  have ha : liftConj (nIso P) (torusE6Two h2 (.ofAdd d0E6)) = rootDiagUnit .E6 (chiIso l) := by
    rw [show d0E6 = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 by decide +kernel, chiIso,
      rootDiagUnit_mul, rootDiagUnit_mul]
    simp only [ofAdd_add, map_mul, hu, h0, h1, h2']
  have hw : liftConj (nIso P) (torusE6Two h2 (.ofAdd (Pi.single 0 1 - Pi.single 1 1))) ∈
      rootSpan .E6 _ {γ | γ ∈ isoRoots} := by
    rw [ofAdd_sub, map_div, hu, hu, map_div, h0, h1, div_eq_mul_inv]
    exact rootDiagUnit_hChar_mem_rootSpan l
  rcases comm_of_double_dichotomy (liftConj_injective (nIso P)) hE
      (le_normalizer_inf (centralizer_le_normalizer_comap (nIso_mem P) ha
        (toralCentralizer_le_normalizer_rootSpan _)))
      (rootSpan_kernel_le_normalizer hl) (rootSpan_isoRoots_le hl)
      (Subgroup.mem_centralizer_singleton_iff.2 (by exact ((Commute.all _ _).map _).eq)) hw
      (t := uE6Two 3) (by
        rw [h3]
        exact rootSL2_mem_centralizer_rootSpan (isRoot_bE6 3) (isRoot_neg_bE6 3)
          (fun _ hδ => isRoot_of_mem_isoRoots hδ) (fun δ hδ => (isoRoots_spec δ hδ).2.2) _)
      with h | h
  · exact torusE6Two_not_mem_zpowers h2 (by decide +kernel)
      ((hcent _ ⟨_, rfl⟩).1 h)
  · rw [← hu] at h
    exact torusE6Two_not_mem_zpowers h2 (by decide +kernel)
      ((hcent _ ⟨_, rfl⟩).1 h)

end F

end R

end CFSG.StandardType.SmallExc.E6Node

end
