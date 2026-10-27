module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Lin2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56AsetA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem aSet_succ_eq_empty {m : ℕ} (hSK : Nat.card S.K = 2 ^ m) {X : Subgroup (MulAut W)}
    (hX : X ≤ Subgroup.normalizer (S.omega : Set (MulAut W))) : E3.aSet (m + 1) X = ∅ := by
  classical
  haveI : Finite W := Finite.of_injective S.vec S.vec_injective
  refine Set.eq_empty_iff_forall_notMem.2 fun A hA => ?_
  have hm2 : 2 ≤ m := by
    have h := S.four_le
    rw [hSK] at h
    by_contra hm
    push Not at hm
    interval_cases m <;> norm_num at h
  have hA2 : A ∈ E3.aSet 2 X := E3.aSet_anti (by omega : 2 ≤ m + 1) X hA
  have hlin := S.linear_of_mem_aSet_two hX hA2
  have hiso := S.isometry_of_mem_aSet_two hX hA2
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact S.mul_self_eq_one w
  have hFsub : S.IsSub (fixV A) := by
    intro c u hu
    refine mem_fixV.2 fun g hg => ?_
    rw [hlin g hg c u, mem_fixV.1 hu g hg]
  have hFtop : fixV A ≠ ⊤ := fixV_ne_top hA.2.1
  have hcomm : ∀ g ∈ A, ∀ w : W, g w * w⁻¹ ∈ S.perp (fixV A) :=
    fun g hg w => S.commutator_mem_perp_fixV hiso hg w
  obtain ⟨w₁, hw₁F, hw₁⟩ := exists_mem_secondLayer hW2 hAel (le_refl (fixV A)) hFtop
  have hk1 := le_mQuot_stabAt_of_mem_aSet hA hw₁F
  have hb1 := two_pow_mQuot_stabAt_le hAel (U := fixV A ⊓ S.perp (fixV A)) (w := w₁)
    (fun g hg => ⟨hw₁ g hg, hcomm g hg w₁⟩)
  have hbig : Nat.card S.K < Nat.card ↥(fixV A ⊓ S.perp (fixV A)) :=
    calc Nat.card S.K = 2 ^ m := hSK
      _ < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m)
      _ ≤ 2 ^ E3.mQuot A (stabAt A w₁) := Nat.pow_le_pow_right (by norm_num) hk1
      _ ≤ _ := hb1
  obtain ⟨hFeq, hFcard⟩ := S.eq_perp_of_card_inf_gt hFsub (by have := S.four_le; omega) hbig
  have hiso' : ∀ x ∈ fixV A, ∀ y ∈ fixV A, S.pol x y = 0 := fun x hx y hy =>
    (hFeq.le hx) y hy
  have hqlt : Nat.card S.K < Nat.card ↥(fixV A) := by
    rw [hFcard]
    calc Nat.card S.K = Nat.card S.K ^ 1 := (pow_one _).symm
      _ < Nat.card S.K ^ 2 := Nat.pow_lt_pow_right (by have := S.four_le; omega) (by norm_num)
  obtain ⟨θ, hθF, hθ1, hθQ⟩ := S.exists_singular_of_isotropic hiso' hqlt
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : W, S.pol w₂ θ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hθ1 (S.eq_one_of_pol_eq_zero fun w' => by rw [S.pol_comm]; exact hcon w')
  have hw₂F : w₂ ∉ fixV A := fun h => hw₂ (hiso' w₂ h θ hθF)
  obtain ⟨N, hNF, hNcard, hN⟩ := S.exists_subgroup_card_le hFsub hiso' hFcard hθF hθQ hw₂
  have hk2 := le_mQuot_stabAt_of_mem_aSet hA hw₂F
  have hb2 := two_pow_mQuot_stabAt_le hAel (U := N) (w := w₂) (fun g hg =>
    hN _ (hFeq.ge (hcomm g hg w₂)) (S.Q_commutator_eq_pol (hiso g hg) w₂))
  have hle : 2 ^ (m + 1) ≤ 2 ^ m :=
    calc 2 ^ (m + 1) ≤ 2 ^ E3.mQuot A (stabAt A w₂) := Nat.pow_le_pow_right (by norm_num) hk2
      _ ≤ Nat.card N := hb2
      _ ≤ Nat.card S.K := hNcard
      _ = 2 ^ m := hSK
  have hlt : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self m)
  omega

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
