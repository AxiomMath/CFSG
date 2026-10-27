module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Forms
public import CFSG.Fischer.Classification.Orthogonal3.Model
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigid
import CFSG.LocalAnalysis.StandardType.ZS.OrthClass

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}

local instance (priority := high) zrb_zmodThreeAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

private lemma zrb_f_nondegenerate {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f) :
    f.Nondegenerate :=
  ⟨hf.nondeg, fun y hy => hf.nondeg y fun x => by rw [hf.symm]; exact hy x⟩

private lemma zrb_Q_apply {m : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U) (x : Fin m → ZMod 3) :
    (LinearMap.BilinForm.congr L f).toQuadraticMap (L x) = f x x := by
  rw [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinForm.congr_apply]
  simp only [LinearEquiv.symm_apply_apply]

private lemma zrb_polar_nondegenerate {m : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U) (hf : IsF3Form f) :
    (QuadraticMap.polarBilin (LinearMap.BilinForm.congr L f).toQuadraticMap).Nondegenerate := by
  let B : LinearMap.BilinForm (ZMod 3) U := LinearMap.BilinForm.congr L f
  change (QuadraticMap.polarBilin B.toQuadraticMap).Nondegenerate
  have hsymm : ∀ y z : U, B y z = B z y := by
    intro y z
    change LinearMap.BilinForm.congr L f y z = LinearMap.BilinForm.congr L f z y
    rw [LinearMap.BilinForm.congr_apply]
    exact hf.symm (L.symm y) (L.symm z)
  have hBnd : B.Nondegenerate := (zrb_f_nondegenerate hf).congr L
  have hpolar : ∀ x y : U, QuadraticMap.polarBilin B.toQuadraticMap x y = 2 * B x y := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, LinearMap.BilinMap.polar_toQuadraticMap, hsymm y x]
    ring
  constructor
  · intro x hx
    refine hBnd.1 x fun y => ?_
    have h2 : (2 : ZMod 3) * B x y = 0 := by
      rw [← hpolar x y]
      exact hx y
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  · intro y hy
    refine hBnd.2 y fun x => ?_
    have h2 : (2 : ZMod 3) * B x y = 0 := by
      rw [← hpolar x y]
      exact hy x
    exact (mul_eq_zero.mp h2).resolve_left (by decide)

private lemma zrb_reflect_apply {m : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U) (hf : IsF3Form f)
    {u : Fin m → ZMod 3} (hu : f u u = 1) (x : Fin m → ZMod 3) :
    CFSG.ClassicalGroups.Orthogonal.reflect
        (LinearMap.BilinForm.congr L f).toQuadraticMap (L u) (L x) =
      L (x + f x u • u) := by
  have hB : ∀ y z : U, LinearMap.BilinForm.congr L f y z = f (L.symm y) (L.symm z) :=
    fun y z => LinearMap.BilinForm.congr_apply L f y z
  have hQa : (LinearMap.BilinForm.congr L f).toQuadraticMap (L u) = 1 := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hB (L u) (L u)]
    simp only [LinearEquiv.symm_apply_apply]
    exact hu
  have hpolar : QuadraticMap.polar ((LinearMap.BilinForm.congr L f).toQuadraticMap)
      (L u) (L x) = 2 * f x u := by
    rw [LinearMap.BilinMap.polar_toQuadraticMap, hB (L u) (L x), hB (L x) (L u)]
    simp only [LinearEquiv.symm_apply_apply, hf.symm u x]
    ring
  have hneg : ∀ c : ZMod 3, -(2 * c) = c := by decide
  calc CFSG.ClassicalGroups.Orthogonal.reflect
        (LinearMap.BilinForm.congr L f).toQuadraticMap (L u) (L x)
      = L x - (2 * f x u) • L u := by
        rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply (by rw [hQa]; exact one_ne_zero),
          hQa, hpolar, div_one]
    _ = L x + f x u • L u := by
        rw [sub_eq_add_neg, ← neg_smul, hneg]
    _ = L (x + f x u • u) := by
        rw [← map_smul, ← map_add]

theorem family_of_mulEquiv_R3_of_eq_three (hp3 : p = 3) (hn : 4 ≤ Module.finrank (ZMod p) U)
    (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : 5 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f) (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 f) :
    Family p A := by
  subst hp3
  obtain ⟨L, hL⟩ := exists_linearEquiv_of_mulEquiv_R3 hn hgen hirr h3 hm hf φ hφ
  let B : LinearMap.BilinForm (ZMod 3) U := LinearMap.BilinForm.congr L f
  let Q : QuadraticForm (ZMod 3) U := B.toQuadraticMap
  have hone : (1 : ZMod 3) ≠ 0 := by norm_num
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := zrb_polar_nondegenerate L hf
  have hAle : A ≤ Subgroup.closure (ClassRefl 3 Q 1) := by
    rw [hgen]
    refine (Subgroup.closure_le (Subgroup.closure (ClassRefl 3 Q 1))).mpr ?_
    intro t ht
    obtain ⟨u, hu, htu⟩ := (hL t).mp ht
    refine Subgroup.subset_closure
      ((mem_classRefl_iff (p := 3) (U := U) (by norm_num) hQnd hone t).mpr ⟨L u, ?_, ?_⟩)
    · change (LinearMap.BilinForm.congr L f).toQuadraticMap (L u) = 1
      rw [zrb_Q_apply L u]
      exact hu
    · ext y
      obtain ⟨x, rfl⟩ := L.surjective y
      rw [htu x, zrb_reflect_apply L hf hu x]
  have hAcl : Subgroup.closure (ClassRefl 3 Q 1) ≤ A := by
    refine (Subgroup.closure_le A).mpr ?_
    intro t ht
    obtain ⟨a, hQa, ht_eq⟩ :=
      (mem_classRefl_iff (p := 3) (U := U) (by norm_num) hQnd hone t).mp ht
    obtain ⟨u, rfl⟩ : ∃ u, L u = a := ⟨L.symm a, L.apply_symm_apply a⟩
    have hu : f u u = 1 := by
      have h := hQa
      change (LinearMap.BilinForm.congr L f).toQuadraticMap (L u) = 1 at h
      rwa [zrb_Q_apply L u] at h
    exact ((hL t).mpr ⟨u, hu, fun x => by rw [ht_eq, zrb_reflect_apply L hf hu x]⟩).1
  exact Family.orthClass (p := 3) (U := U) Q 1 hQnd hone (le_antisymm hAle hAcl)

end CFSG.StandardType.ZS
