module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

private theorem ggRootKer_weylLift_simple {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) {ν : GGWeyl D →* K} (hν : GGWeylLift D ν)
    (i : Fin D.rank) :
    ∃ b : kˣ,
      ν ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) = weylElement x i b := by
  obtain ⟨φ, hφ, hu, hl⟩ := hE.rankOne i
  have hpar := (hE.param _ (single_mem_roots (D := D) i)).1
  have hpar' := (hE.param _ (neg_single_mem_roots (D := D) i)).1
  have hle : rankOne D.rootGroup i ≤ φ.range := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨c, rfl⟩ := (hpar z).mp hz
      exact ⟨sl2Upper c, hu c⟩
    · obtain ⟨c, rfl⟩ := (hpar' z).mp hz
      exact ⟨sl2Lower c, hl c⟩
  obtain ⟨M, hM⟩ := hle (hν.simple_mem i)
  have hs1 := weylAction_simple_single D.isFiniteType i
  have hs2 : weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)
      (-Pi.single i 1) = Pi.single i 1 := by rw [map_neg, hs1, neg_neg]
  have c1 := hν.conj_mem ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) _
    (single_mem_roots i) (x (Pi.single i 1) 1) ((hpar _).mpr ⟨1, rfl⟩)
  rw [hs1] at c1
  obtain ⟨c', hc'⟩ := (hpar' _).mp c1
  have c2 := hν.conj_mem ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) _
    (neg_single_mem_roots i) (x (-Pi.single i 1) 1) ((hpar' _).mpr ⟨1, rfl⟩)
  rw [hs2] at c2
  obtain ⟨c'', hc''⟩ := (hpar _).mp c2
  have e1 : M * sl2Upper 1 = sl2Lower c' * M := by
    apply hφ
    rw [map_mul, map_mul, hM, hu, hl, hc']
    group
  have e2 : M * sl2Lower 1 = sl2Upper c'' * M := by
    apply hφ
    rw [map_mul, map_mul, hM, hu, hl, hc'']
    group
  have h00 : (M : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
    have := congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) k =>
      (N : Matrix (Fin 2) (Fin 2) k) 0 1) e1
    simpa [Matrix.SpecialLinearGroup.coe_mul, PsiDiag.coe_sl2Upper, PsiDiag.coe_sl2Lower,
      Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (M : Matrix (Fin 2) (Fin 2) k) 1 1 = 0 := by
    have := congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) k =>
      (N : Matrix (Fin 2) (Fin 2) k) 1 0) e2
    simpa [Matrix.SpecialLinearGroup.coe_mul, PsiDiag.coe_sl2Upper, PsiDiag.coe_sl2Lower,
      Matrix.mul_apply, Fin.sum_univ_two] using this
  have hdet := M.prop
  rw [Matrix.det_fin_two, h00, h11, zero_mul, zero_sub] at hdet
  have h01 : (M : Matrix (Fin 2) (Fin 2) k) 0 1 ≠ 0 := by
    intro h
    rw [h, zero_mul, neg_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk0 _ h01, ?_⟩
  rw [← hM]
  simp only [weylElement, ← hu, ← hl, ← map_mul]
  congr 1
  ext a b
  have h10 : (M : Matrix (Fin 2) (Fin 2) k) 1 0 =
      -((M : Matrix (Fin 2) (Fin 2) k) 0 1)⁻¹ := by
    field_simp
    linear_combination -hdet
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, PsiDiag.coe_sl2Upper, PsiDiag.coe_sl2Lower,
      Matrix.mul_apply, Fin.sum_univ_two, h00, h11, h10, h01]

theorem ggRootKer_weylLift_conj {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*}
    [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) {ν : GGWeyl D →* K} (hν : GGWeylLift D ν) (w : GGWeyl D)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    ∃ a : kˣ, ∀ c : k,
      ν w * x β c * (ν w)⁻¹ = x (weylAction D.isFiniteType w β) ((a : k) * c) := by
  induction w using (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_induction_left with
  | one => exact ⟨1, fun c => by rw [map_one, map_one, Module.End.one_apply, Units.val_one,
      one_mul, one_mul, inv_one, mul_one]⟩
  | mul_simple_left w i ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := ggRootKer_weylLift_simple hE hν i
    obtain ⟨ε, hε, hw⟩ := hE.weyl i _ (weylAction_mem_roots hβ w)
    have key : ∀ c : k, ν ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i * w) *
        x β c * (ν ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i * w))⁻¹ =
          x (weylAction D.isFiniteType
            ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i * w) β)
          ((ε : k) *
            ((b ^ (-(∑ j, D.cartan i j * weylAction D.isFiniteType w β j)) : kˣ) : k) *
              ((a : k) * c)) := by
      intro c
      rw [map_mul, hb, weylAction_mul_apply, weylAction_simple, ← hw b ((a : k) * c), ← ha c]
      group
    rcases hε with rfl | rfl
    · refine ⟨b ^ (-(∑ j, D.cartan i j * weylAction D.isFiniteType w β j)) * a, fun c => ?_⟩
      rw [key c, Units.val_mul, Int.cast_one, one_mul, mul_assoc]
    · refine ⟨-(b ^ (-(∑ j, D.cartan i j * weylAction D.isFiniteType w β j)) * a),
        fun c => ?_⟩
      rw [key c, Units.val_neg, Units.val_mul, Int.cast_neg, Int.cast_one]
      ring_nf

end CFSG.StandardType

end
