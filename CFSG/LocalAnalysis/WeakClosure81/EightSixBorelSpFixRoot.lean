module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.RankThree.PartOne.CTP.SpSwap
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)
open CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.Classical
open scoped MatrixGroups
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock longBlockEquivOne mat_longBlock)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

variable {k n : ℕ} {F : Type} [Field F]

theorem borel86_spr_fieldSp_spTransvection (σ : F ≃+* F) (v : Fin k ⊕ Fin k → F) (t : F) :
    fieldSp k F σ (spTransvection v t) = spTransvection (σ ∘ v) (σ t) := by
  refine eq_of_spEnd_eq fun y => ?_
  obtain ⟨z, rfl⟩ : ∃ z, σ ∘ z = y := ⟨fun i => σ.symm (y i), by ext i; simp⟩
  rw [spEnd_fieldSp, spEnd_spTransvection, spEnd_spTransvection]
  have h1 := CFSG.RankThree.PartOne.KCSpFull.spForm_comp_ringEquiv (r := k) σ z v
  ext i
  simp only [Function.comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, h1]

theorem borel86_spr_mem_range_conj_of_eq_conj_mul_fieldSp {α : MulAut ↥(StatedSp k F)}
    {g : ↥(StatedSp k F)} {σ : F ≃+* F} (hg : ∀ x, α x = g * fieldSp k F σ x * g⁻¹)
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0)
    (hα : ∀ t : F, α (spTransvection a t) = spTransvection a t) :
    α ∈ (MulAut.conj : ↥(StatedSp k F) →* MulAut ↥(StatedSp k F)).range := by
  have key : ∀ t : F, spTransvection (spEnd g (σ ∘ a)) (σ t) = spTransvection a t := by
    intro t
    have h1 : spTransvection a t = g * fieldSp k F σ (spTransvection a t) * g⁻¹ :=
      (hα t).symm.trans (hg (spTransvection a t))
    rw [borel86_spr_fieldSp_spTransvection,
      CFSG.RankThree.PartOne.CTP.spTransvection_conj] at h1
    exact h1.symm
  have h1 : spTransvection (spEnd g (σ ∘ a)) 1 = spTransvection a 1 := by
    simpa using key 1
  obtain ⟨μ, hμ0, hμb, hμ1⟩ :=
    borel86_spn_exists_smul_of_spTransvection_eq (a := a) (b := spEnd g (σ ∘ a)) (s := 1)
      (t := 1) ha one_ne_zero h1
  have hμsq : μ * μ = 1 := by simpa using hμ1
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have ha1 : ∀ ν : F, spEnd g (σ ∘ a) = ν • a → ν = μ := by
    intro ν hν
    have h : μ • a = ν • a := hμb.symm.trans hν
    have h' := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at h'
    exact (mul_right_cancel₀ hi h').symm
  have hσt : ∀ t : F, σ t = t := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · obtain ⟨ν, hν0, hνb, hν⟩ :=
        borel86_spn_exists_smul_of_spTransvection_eq (a := a) (b := spEnd g (σ ∘ a)) (s := σ t)
          (t := t) ha ht (key t)
      rw [ha1 ν hνb] at hν
      rw [hμsq, one_mul] at hν
      exact hν
  have hσ : σ = RingEquiv.refl F := RingEquiv.ext hσt
  have hfield : fieldSp k F σ = 1 := by
    rw [hσ]
    exact map_one (fieldSp k F)
  refine MonoidHom.mem_range.mpr ⟨g, ?_⟩
  refine MulEquiv.ext fun x => ?_
  rw [hg x, hfield, MulAut.one_apply, MulAut.conj_apply]

private theorem fieldSp_longBlock_one (σ : F ≃+* F) (A : SL(2, F)) :
    fieldSp 1 F σ (longBlock F 1 0 A) =
      longBlock F 1 0 (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_fieldSp]
  change (mat 1 F (longBlock F 1 0 A)).map σ =
    mat 1 F (longBlock F 1 0 (Matrix.SpecialLinearGroup.map σ.toRingHom A))
  rw [mat_longBlock, mat_longBlock]
  exact CFSG.RankThree.PartOne.CTP.blockMat_map_ringHom _ _ _ σ.toRingHom

theorem borel86_spr_exists_eq_conj_mul_fieldSp [Finite F] (hF : Nat.card F = 2 ^ n) (hk : 1 ≤ k)
    (hk2 : k ≠ 2) (α : MulAut ↥(StatedSp k F)) :
    ∃ (g : ↥(StatedSp k F)) (σ : F ≃+* F), ∀ x, α x = g * fieldSp k F σ x * g⁻¹ := by
  have hn1 : 1 ≤ n := by
    have h2 : 1 < 2 ^ n := by rw [← hF]; exact Finite.one_lt_card
    have h3 : n ≠ 0 := Nat.one_lt_two_pow_iff.mp h2
    omega
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (K := F) Nat.prime_two hn1 hF
  rcases (show k = 1 ∨ 3 ≤ k by omega) with rfl | hk3
  · let e : SL(2, F) ≃* ↥(StatedSp 1 F) := longBlockEquivOne F
    let β : MulAut SL(2, F) := MulAut.congr e.symm α
    obtain ⟨⟨h, σ⟩, hp, -⟩ :=
      (even_SL2_full_automorphism_semilinear_model hn1 hF).2.2.2.2 β
    have he : ∀ A : SL(2, F), e A = longBlock F 1 0 A := fun A => rfl
    have hmain : ∀ A : SL(2, F),
        e (Matrix.SpecialLinearGroup.map σ.toRingHom A) = fieldSp 1 F σ (e A) := by
      intro A
      rw [he A, fieldSp_longBlock_one σ A, he]
    have hx : ∀ x : ↥(StatedSp 1 F), e (β (e.symm x)) = α x := by
      intro x
      show e (e.symm (α (e (e.symm x)))) = α x
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    refine ⟨e h, σ, fun x => ?_⟩
    calc α x = e (β (e.symm x)) := (hx x).symm
      _ = e (h * Matrix.SpecialLinearGroup.map σ.toRingHom (e.symm x) * h⁻¹) := by
            rw [hp (e.symm x)]
      _ = e h * e (Matrix.SpecialLinearGroup.map σ.toRingHom (e.symm x)) * (e h)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
      _ = e h * fieldSp 1 F σ (e (e.symm x)) * (e h)⁻¹ := by
            rw [hmain (e.symm x)]
      _ = e h * fieldSp 1 F σ x * (e h)⁻¹ := by rw [MulEquiv.apply_symm_apply]
  · exact CFSG.SeitzReduction.F4Pilot.exists_eq_conj_mul_fieldSp hk3 α

theorem borel86_spr_mem_range_conj_two [Finite F] (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {a : Fin 2 ⊕ Fin 2 → F} (ha : a ≠ 0) (α : MulAut ↥(StatedSp 2 F))
    (hα : ∀ t : F, α (spTransvection a t) = spTransvection a t) :
    α ∈ (MulAut.conj : ↥(StatedSp 2 F) →* MulAut ↥(StatedSp 2 F)).range := by
  have hn1 : 1 ≤ n := by
    have h2 : 1 < 2 ^ n := by rw [← hF]; exact Finite.one_lt_card
    have h3 : n ≠ 0 := Nat.one_lt_two_pow_iff.mp h2
    omega
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (K := F) Nat.prime_two hn1 hF
  have hπ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := 2) (K := F)
  set πe := MulEquiv.ofBijective (proj 2 F) hπ with hπe
  let β : MulAut (StatedProj (StatedSp 2 F)) := MulAut.congr πe α
  have hβ : ∀ t : F, β (proj 2 F (spTransvection a t)) =
      proj 2 F (spTransvection a t) := by
    intro t
    have h1 : β (proj 2 F (spTransvection a t)) = proj 2 F (α (spTransvection a t)) := by
      change πe (α (πe.symm (πe (spTransvection a t)))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    rw [h1, hα t]
  have hβin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F)) :=
    even_symplectic_rank_two_inner_of_fixes_transvections (f := n) (by omega) hF a ha β hβ
  have hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedSp 2 F) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.congr_mem_inner_iff πe α).mp hβin
  simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hin

theorem borel86_spr_mem_range_conj [Finite F] (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hk : 1 ≤ k)
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) (α : MulAut ↥(StatedSp k F))
    (hα : ∀ s : F, α (spTransvection a s) = spTransvection a s) :
    α ∈ (MulAut.conj : ↥(StatedSp k F) →* MulAut ↥(StatedSp k F)).range := by
  rcases eq_or_ne k 2 with rfl | hk2
  · exact borel86_spr_mem_range_conj_two hF hn ha α hα
  · obtain ⟨g, σ, hg⟩ := borel86_spr_exists_eq_conj_mul_fieldSp hF hk hk2 α
    exact borel86_spr_mem_range_conj_of_eq_conj_mul_fieldSp hg ha hα

end CFSG.LocalAnalysis.WeakClosure81

end
