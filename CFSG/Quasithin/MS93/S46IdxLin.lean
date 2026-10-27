module

public import CFSG.Quasithin.MS93.ML3Facts
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

open Matrix

namespace CFSG.Quasithin.MS93.S46.Idx

open scoped commutatorElement

variable {F : Type} [Field F]

private theorem coe_mul' (A B : SL3 F) :
    ((A * B : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) :=
  rfl

private theorem rootElt20_mul_rootElt10 (s t : F) :
    rootElt 2 0 t * rootElt 1 0 s = rootElt 1 0 s * rootElt 2 0 t :=
  (rootElt_commute (i := 2) (j := 0) (k := 1) (l := 0) (by decide) (by decide) t s).eq

theorem mem_rH_iff {g : SL3 F} :
    g ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) ↔
      ∃ s t : F, rootElt 1 0 s * rootElt 2 0 t = g := by
  let P : Subgroup (SL3 F) :=
    { carrier := {g | ∃ s t : F, rootElt 1 0 s * rootElt 2 0 t = g}
      mul_mem' := by
        rintro _ _ ⟨s, t, rfl⟩ ⟨s', t', rfl⟩
        refine ⟨s + s', t + t', ?_⟩
        have e : rootElt 2 0 t * (rootElt 1 0 s' * rootElt 2 0 t') =
            rootElt 1 0 s' * (rootElt 2 0 t * rootElt 2 0 t') := by
          rw [← mul_assoc, ← mul_assoc, rootElt20_mul_rootElt10]
        rw [rootElt_add, rootElt_add]
        simp only [mul_assoc, e]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨s, t, rfl⟩
        refine ⟨-s, -t, ?_⟩
        rw [rootElt_neg, rootElt_neg, ← _root_.mul_inv_rev, rootElt20_mul_rootElt10] }
  constructor
  · intro hg
    have hle : (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) ≤ P := by
      refine sup_le ?_ ?_
      · rintro _ ⟨s, rfl⟩
        exact ⟨s, 0, by simp⟩
      · rintro _ ⟨t, rfl⟩
        exact ⟨0, t, by simp⟩
    exact hle hg
  · rintro ⟨s, t, rfl⟩
    exact Subgroup.mul_mem_sup (rootElt_mem_rootGroup _ _ _) (rootElt_mem_rootGroup _ _ _)

theorem rootElt10_mul_rootElt20_mulVec (s t : F) (x : Fin 3 → F) :
    ((rootElt 1 0 s * rootElt 2 0 t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
      x + ![0, s * x 0, t * x 0] := by
  rw [coe_mul', ← Matrix.mulVec_mulVec, rootElt_mulVec (show (2 : Fin 3) ≠ 0 by decide),
    rootElt_mulVec (show (1 : Fin 3) ≠ 0 by decide)]
  funext k
  fin_cases k <;> simp

theorem rH_mulVec_single_one {g : SL3 F}
    (hg : g ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F))) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 = Pi.single 1 1 := by
  obtain ⟨s, t, rfl⟩ := mem_rH_iff.mp hg
  rw [rootElt10_mul_rootElt20_mulVec]
  funext k
  fin_cases k <;> simp

theorem eq_top_of_normal_of_mem_rH {N : Subgroup (SL3 F)} (hN : N.Normal) {g : SL3 F}
    (hgN : g ∈ N) (hgR : g ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F))) (hg1 : g ≠ 1) :
    N = ⊤ := by
  have hgc : g ∉ Subgroup.center (SL3 F) := by
    intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have h1 := congrFun (rH_mulVec_single_one hgR) 1
    rw [← hr] at h1
    simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.single_eq_same, mul_one] at h1
    apply hg1
    apply Subtype.ext
    rw [← hr, h1, map_one, coe_one_SL3]
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl
  have hq' : CFSG.Open.IsQuasisimple (SL3 F) := ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
  rcases @CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top _ _ hq' N hN with
    h1 | h1
  · exact absurd (h1 hgN) hgc
  · exact h1

end CFSG.Quasithin.MS93.S46.Idx
