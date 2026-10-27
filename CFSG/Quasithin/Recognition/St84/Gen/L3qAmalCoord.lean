module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

import CFSG.CGT.PushingUpLit.BHS6.ThreeEightSL
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.ClassicalGroups.PCoreSection
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldUnipotent
import CFSG.CGT.PushingUpLit.BHS6.ThreeEightGaps

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS6
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.ClassicalGroups
open scoped MatrixGroups commutatorElement

section

variable {G : Type*} [Group G]

structure VertexCoord (L S : Subgroup G) (F : Type*) [Field F] where
  α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F
  β : ↥(pCoreOf 2 L) ≃* Multiplicative (Fin 2 → F)
  surjective : Function.Surjective α
  eq_one_iff : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L
  equivariant : ∀ (x : ↥L) (u v : ↥(pCoreOf 2 L)), (v : G) = x * u * x⁻¹ →
    Multiplicative.toAdd (β v) =
      (α x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))
  mem_iff : ∀ x : ↥L, (x : G) ∈ S ↔ ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]

end

variable {G : Type} [Group G]

section MatrixHelpers

variable {F : Type*} [Field F]

private abbrev upperU : Subgroup (SL(2, F)) := (upperUnipotent (F := F)).range

private def e0 : Fin 2 → F := Pi.single 0 1

private theorem mulVec_unitriangular_apply (t : F) (v : Fin 2 → F) :
    (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F).mulVec v = ![v 0 + t * v 1, v 1] := by
  funext i
  fin_cases i <;> simp [vecHead, vecTail, Matrix.mulVec, Fin.sum_univ_two]

private theorem mem_upperU_iff {g : SL(2, F)} :
    g ∈ upperU (F := F) ↔ ∃ t : F, (g : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  rw [← sl2_fixes_first_iff (F := F) g]
  constructor
  · intro h
    have h0 := congrFun h 0
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at h0
    have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simpa [e0] using h0
    have h1 := congrFun h 1
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at h1
    have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa [e0] using h1
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
      rw [Matrix.det_fin_two, h00, h10] at hdet
      simpa using hdet
    refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  · rintro ⟨t, ht⟩
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, ht,
      mulVec_unitriangular_apply]
    funext i
    fin_cases i <;> simp [e0]

private def uOne : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem coe_uOne : (uOne (F := F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] :=
  rfl

private theorem uOne_mem : uOne (F := F) ∈ upperU (F := F) := mem_upperU_iff.mpr ⟨1, coe_uOne⟩

private theorem smul_e0_eq (A : SL(2, F)) : A • e0 (F := F) = ![A 0 0, A 1 0] := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, e0]
  funext i
  fin_cases i <;> simp [vecHead, vecTail, Matrix.mulVec, Fin.sum_univ_two]

private theorem upperU_smul_e0 (g : SL(2, F)) (hg : g ∈ upperU (F := F)) :
    g • e0 (F := F) = e0 :=
  (sl2_fixes_first_iff (F := F) g).mpr hg

private theorem uOne_smul_apply (v : Fin 2 → F) :
    uOne (F := F) • v = ![v 0 + v 1, v 1] := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  change (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).mulVec v = ![v 0 + v 1, v 1]
  rw [mulVec_unitriangular_apply]
  simp

private theorem second_coord_eq_zero_of_fixed_by_uOne {v : Fin 2 → F}
    (h : uOne (F := F) • v = v) : v 1 = 0 := by
  have h0 : v 0 + v 1 = v 0 := by
    simpa [uOne_smul_apply] using congrFun h 0
  have h0' : v 0 + v 1 = v 0 + 0 := by simpa using h0
  exact add_left_cancel h0'

private theorem smul_eq_self_of_second_coord_zero {v : Fin 2 → F} {t : F} {A : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) (hv : v 1 = 0) : A • v = v := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, hA,
    mulVec_unitriangular_apply]
  funext i
  fin_cases i <;> simp [vecHead, vecTail, hv]

private theorem second_coord_eq_zero_of_mulVec_fixed {v : Fin 2 → F}
    (h : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : v 1 = 0 := by
  have h0 : v 0 + 1 * v 1 = v 0 := by
    have := congrFun h 0
    rw [mulVec_unitriangular_apply] at this
    simpa [vecHead, vecTail] using this
  have h0' : v 0 + v 1 = v 0 + 0 := by simpa using h0
  exact add_left_cancel h0'

private theorem exists_smul_e0_of_mem_normalizer {A : SL(2, F)}
    (hA : A ∈ Subgroup.normalizer (upperU (F := F) : Set (SL(2, F)))) :
    ∃ c : F, A • e0 (F := F) = c • e0 := by
  have hfix : ∀ u ∈ upperU (F := F), u • (A • e0 (F := F)) = A • e0 := by
    intro u hu
    have hAu : A⁻¹ * u * A ∈ upperU (F := F) := by
      have hAinv : A⁻¹ ∈ Subgroup.normalizer (upperU (F := F) : Set (SL(2, F))) :=
        Subgroup.inv_mem _ hA
      have := (Subgroup.mem_normalizer_iff.mp hAinv u).mp hu
      simpa using this
    calc u • (A • e0 (F := F)) = (u * A) • e0 (F := F) := (mul_smul u A _).symm
      _ = (A * (A⁻¹ * u * A)) • e0 (F := F) := by
            rw [show u * A = A * (A⁻¹ * u * A) by group]
      _ = A • ((A⁻¹ * u * A) • e0 (F := F)) := mul_smul A (A⁻¹ * u * A) _
      _ = A • e0 (F := F) := by rw [upperU_smul_e0 _ hAu]
  have h1 : uOne (F := F) • (A • e0 (F := F)) = A • e0 (F := F) := hfix _ uOne_mem
  have hsecond : (A • e0 (F := F)) 1 = 0 :=
    second_coord_eq_zero_of_fixed_by_uOne h1
  refine ⟨(A • e0 (F := F)) 0, funext fun i => ?_⟩
  fin_cases i
  · simp [e0]
  · simpa [e0] using hsecond

private theorem exists_upperTriangular_of_smul_e0 {A : SL(2, F)} {c : F}
    (h : A • e0 (F := F) = c • e0) :
    ∃ ν : Fˣ, ∃ r : F,
      (A : Matrix (Fin 2) (Fin 2) F) = !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] := by
  have hA : A • e0 (F := F) = ![A 0 0, A 1 0] := smul_e0_eq A
  have hc : c • e0 (F := F) = ![c, 0] := by
    funext i
    fin_cases i <;> simp [e0]
  rw [hA, hc] at h
  have h0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
    simpa [vecHead, vecTail] using congrFun h 0
  have h1 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simpa [vecHead, vecTail] using congrFun h 1
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two, h0, h1] at hdet
  have hdet' : c * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by simpa using hdet
  have hcne : c ≠ 0 := by
    rintro rfl
    simpa using hdet'
  have hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = c⁻¹ :=
    (inv_eq_of_mul_eq_one_right hdet').symm
  refine ⟨Units.mk0 c hcne, (A : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  have hν : ((Units.mk0 c hcne : Fˣ) : F) = c := Units.val_mk0 hcne
  have hνinv : (((Units.mk0 c hcne : Fˣ)⁻¹ : Fˣ) : F) = c⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hν]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hν, hνinv, h0, h1, hA11]

private theorem diag2_conj_mem_upperU (a : F) (ha : a ≠ 0) {X : SL(2, F)}
    (hX : X ∈ upperU (F := F)) :
    Matrix.SpecialLinearGroup.diag2 a ha * X * (Matrix.SpecialLinearGroup.diag2 a ha)⁻¹ ∈
      upperU (F := F) := by
  obtain ⟨t, ht⟩ := mem_upperU_iff.mp hX
  refine mem_upperU_iff.mpr ⟨a * a * t, ?_⟩
  have hDinv : (Matrix.SpecialLinearGroup.diag2 a ha)⁻¹ =
      Matrix.SpecialLinearGroup.diag2 a⁻¹ (inv_ne_zero ha) :=
    Matrix.SpecialLinearGroup.diag2_inv a ha
  change ((Matrix.SpecialLinearGroup.diag2 a ha * X *
    (Matrix.SpecialLinearGroup.diag2 a ha)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![1, a * a * t; 0, 1]
  rw [hDinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht,
    Matrix.SpecialLinearGroup.diag2_coe', Matrix.SpecialLinearGroup.diag2_coe']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha] <;> ring

private theorem mulVec_conj (X A : SL(2, F)) (v : Fin 2 → F) :
    (X : Matrix (Fin 2) (Fin 2) F).mulVec ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
      ((X * A * X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec
        ((X : Matrix (Fin 2) (Fin 2) F).mulVec v) := by
  have h : (X : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      ((X * A * X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        (X : Matrix (Fin 2) (Fin 2) F) := by
    have hSL : X * A = (X * A * X⁻¹) * X := by group
    calc
      (X : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)
          = ((X * A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) :=
            (Matrix.SpecialLinearGroup.coe_mul X A).symm
      _ = (((X * A * X⁻¹) * X : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) :=
            congrArg Subtype.val hSL
      _ = ((X * A * X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
            (X : Matrix (Fin 2) (Fin 2) F) := Matrix.SpecialLinearGroup.coe_mul _ _
  rw [Matrix.mulVec_mulVec v (X : Matrix (Fin 2) (Fin 2) F)
      (A : Matrix (Fin 2) (Fin 2) F),
    Matrix.mulVec_mulVec v ((X * A * X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      (X : Matrix (Fin 2) (Fin 2) F)]
  exact congrArg (fun M => M.mulVec v) h

end MatrixHelpers

section VertexCoordLemmas

variable {L S : Subgroup G} {F : Type*} [Field F]

theorem VertexCoord.mem_centralizer_iff (c : VertexCoord L S F) (hSL : S ≤ L)
    (x : ↥(pCoreOf 2 L)) :
    (∀ s ∈ S, s * (x : G) = (x : G) * s) ↔
      Multiplicative.toAdd (c.β x) 1 = 0 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := c.surjective (uOne (F := F))
    have hbS : (b : G) ∈ S :=
      (c.mem_iff b).mpr ⟨1, by simpa [uOne] using congrArg Subtype.val hb⟩
    have hbx : (b : G) * (x : G) * (b : G)⁻¹ = (x : G) := by
      have h' := h (b : G) hbS
      calc (b : G) * (x : G) * (b : G)⁻¹ = ((x : G) * (b : G)) * (b : G)⁻¹ := by rw [h']
        _ = (x : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]
    let vx : ↥(pCoreOf 2 L) :=
      ⟨(b : G) * (x : G) * (b : G)⁻¹, PCoreSection.conj_mem_pCoreOf b.2 x.2⟩
    have hvx : vx = x := Subtype.ext hbx
    have heq := c.equivariant b x vx (by rfl)
    rw [hvx] at heq
    have hmat : (c.α b : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := by
      simpa [uOne] using congrArg Subtype.val hb
    rw [hmat] at heq
    exact second_coord_eq_zero_of_mulVec_fixed heq.symm
  · intro hv s hs
    let sL : ↥L := ⟨s, hSL hs⟩
    have hαsU : c.α sL ∈ upperU (F := F) :=
      mem_upperU_iff.mpr ((c.mem_iff sL).mp hs)
    obtain ⟨t, ht⟩ := mem_upperU_iff.mp hαsU
    let vx : ↥(pCoreOf 2 L) := ⟨s * (x : G) * s⁻¹, PCoreSection.conj_mem_pCoreOf sL.2 x.2⟩
    have heq := c.equivariant sL x vx (by rfl)
    have hfix : (c.α sL : SL(2, F)) • Multiplicative.toAdd (c.β x) =
        Multiplicative.toAdd (c.β x) :=
      smul_eq_self_of_second_coord_zero ht hv
    have heq' : Multiplicative.toAdd (c.β vx) = Multiplicative.toAdd (c.β x) := by
      calc Multiplicative.toAdd (c.β vx)
          = (c.α sL : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (c.β x)) :=
              heq
        _ = (c.α sL : SL(2, F)) • Multiplicative.toAdd (c.β x) := by
              rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
        _ = Multiplicative.toAdd (c.β x) := hfix
    have hvx : vx = x := c.β.injective (Multiplicative.toAdd.injective heq')
    have hcx : s * (x : G) * s⁻¹ = (x : G) := by
      have h := congrArg (fun z : ↥(pCoreOf 2 L) => (z : G)) hvx
      simpa [vx] using h
    calc s * (x : G) = s * (x : G) * s⁻¹ * s := by group
      _ = (x : G) * s := by rw [hcx]

theorem VertexCoord.commutator (c : VertexCoord L S F) {s : ↥L} {t : F}
    (hs : (c.α s : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    (x v : ↥(pCoreOf 2 L)) (hv : (v : G) = s * x * s⁻¹ * x⁻¹) :
    Multiplicative.toAdd (c.β v) = ![t * Multiplicative.toAdd (c.β x) 1, 0] := by
  let u : ↥(pCoreOf 2 L) := ⟨s * (x : G) * s⁻¹, PCoreSection.conj_mem_pCoreOf s.2 x.2⟩
  have hvu : v = u * x⁻¹ := Subtype.ext (by simpa [u] using hv)
  have hβu : Multiplicative.toAdd (c.β u) =
      (c.α s : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (c.β x)) := by
    simpa [u] using c.equivariant s x u (by rfl)
  have hβv : Multiplicative.toAdd (c.β v) =
      Multiplicative.toAdd (c.β u) - Multiplicative.toAdd (c.β x) := by
    rw [hvu, map_mul, map_inv]
    simp [toAdd_mul, toAdd_inv, sub_eq_add_neg]
  have hvec :
      (c.α s : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (c.β x)) -
        Multiplicative.toAdd (c.β x) =
          ![t * Multiplicative.toAdd (c.β x) 1, 0] := by
    rw [hs, mulVec_unitriangular_apply]
    funext i
    fin_cases i <;> simp
  calc Multiplicative.toAdd (c.β v)
      = Multiplicative.toAdd (c.β u) - Multiplicative.toAdd (c.β x) := hβv
    _ = (c.α s : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (c.β x)) - Multiplicative.toAdd (c.β x) := by rw [hβu]
    _ = ![t * Multiplicative.toAdd (c.β x) 1, 0] := hvec

private theorem alpha_mem_normalizer_upperU_of_mem_iff (α : ↥L →* SL(2, F))
    (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔
      ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    (hSL : S ≤ L) {b : ↥L} (hb : (b : G) ∈ Subgroup.normalizer (S : Set G)) :
    α b ∈ Subgroup.normalizer (upperU (F := F) : Set (SL(2, F))) := by
  refine Subgroup.mem_normalizer_iff.mpr fun X => ⟨?_, ?_⟩
  · intro hX
    obtain ⟨s, hsX⟩ := hα X
    have hsS : (s : G) ∈ S :=
      (hmem s).mpr (by rw [hsX]; exact mem_upperU_iff.mp hX)
    have hbs : (b : G) * (s : G) * (b : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hb (s : G)).mp hsS
    let t : ↥L := ⟨(b : G) * (s : G) * (b : G)⁻¹, hSL hbs⟩
    have hαt : α t = α b * α s * (α b)⁻¹ := by
      have ht_eq : t = b * s * b⁻¹ := Subtype.ext rfl
      rw [ht_eq, map_mul, map_mul, map_inv]
    have htU : α t ∈ upperU (F := F) := mem_upperU_iff.mpr ((hmem t).mp hbs)
    rw [hαt] at htU
    simpa [← hsX] using htU
  · intro hX
    obtain ⟨s, hsX⟩ := hα X
    let t : ↥L := ⟨(b : G) * (s : G) * (b : G)⁻¹,
      L.mul_mem (L.mul_mem b.2 s.2) (L.inv_mem b.2)⟩
    have hαt : α t = α b * X * (α b)⁻¹ := by
      have ht_eq : t = b * s * b⁻¹ := Subtype.ext rfl
      rw [ht_eq, map_mul, map_mul, map_inv, hsX]
    have htU : α t ∈ upperU (F := F) := by rw [hαt]; exact hX
    have htS : (t : G) ∈ S := (hmem t).mpr (mem_upperU_iff.mp htU)
    have hsS : (s : G) ∈ S := (Subgroup.mem_normalizer_iff.mp hb (s : G)).mpr htS
    rw [← hsX]
    exact mem_upperU_iff.mpr ((hmem s).mp hsS)

private theorem conj_mem_upperU_of_mem_iff (α : ↥L →* SL(2, F))
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔
      ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    (hSL : S ≤ L) {b : ↥L} {D : SL(2, F)} (hbD : α b = D)
    (hD : ∀ X ∈ upperU (F := F), D * X * D⁻¹ ∈ upperU (F := F)) {s : G} (hs : s ∈ S) :
    (b : G) * s * (b : G)⁻¹ ∈ S := by
  have hmemL : (b : G) * s * (b : G)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem b.2 (hSL hs)) (L.inv_mem b.2)
  let t : ↥L := ⟨(b : G) * s * (b : G)⁻¹, hmemL⟩
  have hαt : α t = D * α ⟨s, hSL hs⟩ * D⁻¹ := by
    have ht_eq : t = b * (⟨s, hSL hs⟩ : ↥L) * b⁻¹ := Subtype.ext rfl
    rw [ht_eq, map_mul, map_mul, map_inv, hbD]
  have hX : α ⟨s, hSL hs⟩ ∈ upperU (F := F) :=
    mem_upperU_iff.mpr ((hmem ⟨s, hSL hs⟩).mp hs)
  have htU : α t ∈ upperU (F := F) := by
    rw [hαt]
    exact hD _ hX
  exact (hmem t).mpr (mem_upperU_iff.mp htU)

theorem exists_of_mem_normalizer_of_mem_iff (α : ↥L →* SL(2, F))
    (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔
      ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    (hSL : S ≤ L) {b : ↥L} (hb : (b : G) ∈ Subgroup.normalizer (S : Set G)) :
    ∃ (ν : Fˣ) (r : F),
      (α b : Matrix (Fin 2) (Fin 2) F) = !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] := by
  obtain ⟨r, hr⟩ :=
    exists_smul_e0_of_mem_normalizer (alpha_mem_normalizer_upperU_of_mem_iff α hα hmem hSL hb)
  exact exists_upperTriangular_of_smul_e0 hr

theorem VertexCoord.exists_of_mem_normalizer (c : VertexCoord L S F) (hSL : S ≤ L)
    {b : ↥L} (hb : (b : G) ∈ Subgroup.normalizer (S : Set G)) :
    ∃ (ν : Fˣ) (r : F),
      (c.α b : Matrix (Fin 2) (Fin 2) F) = !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] :=
  exists_of_mem_normalizer_of_mem_iff c.α c.surjective c.mem_iff hSL hb

theorem exists_mem_normalizer_of_mem_iff (α : ↥L →* SL(2, F))
    (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L, (x : G) ∈ S ↔
      ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    (hSL : S ≤ L) (ν : Fˣ) :
    ∃ b : ↥L, (b : G) ∈ Subgroup.normalizer (S : Set G) ∧
      ∃ r : F, (α b : Matrix (Fin 2) (Fin 2) F) =
        !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] := by
  let a : F := (ν : F)
  have ha : a ≠ 0 := ν.ne_zero
  let D : SL(2, F) := Matrix.SpecialLinearGroup.diag2 a ha
  obtain ⟨b, hbD⟩ := hα D
  have hDconj : ∀ X ∈ upperU (F := F), D * X * D⁻¹ ∈ upperU (F := F) := by
    intro X hX
    exact diag2_conj_mem_upperU a ha hX
  have hDinvconj : ∀ X ∈ upperU (F := F), D⁻¹ * X * D ∈ upperU (F := F) := by
    intro X hX
    have h := diag2_conj_mem_upperU a⁻¹ (inv_ne_zero ha) hX
    simpa [D, Matrix.SpecialLinearGroup.diag2_inv] using h
  have hDinvconj' : ∀ X ∈ upperU (F := F), D⁻¹ * X * (D⁻¹)⁻¹ ∈ upperU (F := F) := by
    intro X hX
    simpa using hDinvconj X hX
  have hconj : ∀ s : G, s ∈ S → (b : G) * s * (b : G)⁻¹ ∈ S :=
    fun _ hs => conj_mem_upperU_of_mem_iff α hmem hSL hbD hDconj hs
  have hbDinv : α b⁻¹ = D⁻¹ := by rw [map_inv, hbD]
  have hconj_inv : ∀ s : G, s ∈ S → (b : G)⁻¹ * s * (b : G) ∈ S := by
    intro s hs
    have h := conj_mem_upperU_of_mem_iff α hmem hSL hbDinv hDinvconj' hs
    simpa using h
  refine ⟨b, ?_, 0, ?_⟩
  · refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨hconj s, fun hs => ?_⟩
    have h := hconj_inv ((b : G) * s * (b : G)⁻¹) hs
    have hsimpl : (b : G)⁻¹ * ((b : G) * s * (b : G)⁻¹) * (b : G) = s := by group
    rwa [hsimpl] at h
  · rw [hbD]
    change (Matrix.SpecialLinearGroup.diag2 a ha : Matrix (Fin 2) (Fin 2) F) =
      !![(ν : F), 0; 0, ((ν⁻¹ : Fˣ) : F)]
    rw [Matrix.SpecialLinearGroup.diag2_coe']
    simp [a, Units.val_inv_eq_inv_val]

theorem VertexCoord.exists_mem_normalizer (c : VertexCoord L S F) (hSL : S ≤ L) (ν : Fˣ) :
    ∃ b : ↥L, (b : G) ∈ Subgroup.normalizer (S : Set G) ∧
      ∃ r : F, (c.α b : Matrix (Fin 2) (Fin 2) F) =
        !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] :=
  exists_mem_normalizer_of_mem_iff c.α c.surjective c.mem_iff hSL ν

end VertexCoordLemmas

theorem exists_normalized_lin2 {L S : Subgroup G} {f : ℕ} [Finite G]
    (hf : 1 ≤ f) (hS : IsSylowTwoOf S L) (hL : IsLin2Type L f) :
    ∃ (α : ↥L →* SL(2, GaloisField 2 f))
      (β : ↥(blockU L) →* Multiplicative (Fin 2 → GaloisField 2 f)),
      Function.Surjective α ∧ (∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L) ∧
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      (∀ (x : ↥L) (u v : ↥(blockU L)), (v : G) = x * u * x⁻¹ →
        Multiplicative.toAdd (β v) =
          (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).mulVec
            (Multiplicative.toAdd (β u))) ∧
      ∀ x : ↥L, (x : G) ∈ S ↔
        ∃ t : GaloisField 2 f,
          (α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] := by
  classical
  let F := GaloisField 2 f
  have hf0 : f ≠ 0 := by omega
  obtain ⟨α₀, hα₀surj, hα₀ker, β₀, hβ₀surj, hβ₀ker, hβ₀eq⟩ :=
    isLin2TypeGF_of_isLin2Type hf0 hL
  have hS2 : IsPGroup 2 (S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hA2 : IsPGroup 2 ((S.subgroupOf L).map α₀) := hS2.map α₀
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent ((S.subgroupOf L).map α₀) hA2
  let X : SL(2, F) := x⁻¹
  let evec : Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → F) :=
    (SpecialLinearGroup.toLin' X).toAddEquiv.toMultiplicative
  let β : ↥(blockU L) →* Multiplicative (Fin 2 → F) := evec.toMonoidHom.comp β₀
  let α : ↥L →* SL(2, F) := (MulAut.conj X).toMonoidHom.comp α₀
  have hαsurj : Function.Surjective α := (MulAut.conj X).surjective.comp hα₀surj
  have hα1 : ∀ y : ↥L, α y = 1 ↔ (y : G) ∈ pCoreOf 2 L := by
    intro y
    have h1 : α y = 1 ↔ α₀ y = 1 := by
      change (MulAut.conj X) (α₀ y) = 1 ↔ α₀ y = 1
      exact (MulAut.conj X).map_eq_one_iff
    rw [h1, ← MonoidHom.mem_ker, hα₀ker]
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := L) y).symm
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    ext y
    rw [MonoidHom.mem_ker, hα1 y, CFSG.mem_openPCoreOf_iff]
  have hβapply : ∀ z : ↥(blockU L),
      Multiplicative.toAdd (β z) =
        (X : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β₀ z)) := by
    intro z
    change Multiplicative.toAdd (evec (β₀ z)) =
      (X : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β₀ z))
    simp [evec, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, Fin.sum_univ_two]
  have hαS_le_U : (S.subgroupOf L).map α ≤ upperU (F := F) := by
    have hmap : (S.subgroupOf L).map α =
        ((S.subgroupOf L).map α₀).map (MulAut.conj X).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [hmap]
    simpa [X] using hx
  let P : Sylow 2 ↥L := hS2.toSylow hS.2.2
  have hU2 : IsPGroup 2 (upperU (F := F)) := by
    refine IsPGroup.of_card (n := f) ?_
    rw [upperUnipotent_card, GaloisField.card 2 f hf0]
  have hαker2 : IsPGroup 2 α.ker := by
    rw [hαker]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥L)
  have hPle : (P : Subgroup ↥L) ≤ (upperU (F := F)).comap α := by
    intro y hy
    exact hαS_le_U (Subgroup.mem_map_of_mem α hy)
  have hH_eq : (upperU (F := F)).comap α = (S.subgroupOf L) :=
    P.is_maximal' (hU2.comap_of_ker_isPGroup α hαker2) hPle
  have hU_le_map : upperU (F := F) ≤ (S.subgroupOf L).map α := by
    intro u hu
    obtain ⟨y, hy⟩ := hαsurj u
    have hyH : y ∈ (upperU (F := F)).comap α := by
      rw [Subgroup.mem_comap, hy]
      exact hu
    rw [hH_eq] at hyH
    rw [← hy]
    exact Subgroup.mem_map_of_mem α hyH
  have hmem_iff : ∀ y : ↥L, (y : G) ∈ S ↔
      ∃ t : F, (α y : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
    intro y
    have h1 : (y : G) ∈ S ↔ y ∈ S.subgroupOf L := Iff.rfl
    rw [h1]
    constructor
    · intro hy
      exact mem_upperU_iff.mp (hαS_le_U (Subgroup.mem_map_of_mem α hy))
    · intro hy
      have hu : α y ∈ upperU (F := F) := mem_upperU_iff.mpr hy
      have hyH : y ∈ (upperU (F := F)).comap α := hu
      rw [hH_eq] at hyH
      exact hyH
  refine ⟨α, β, hαsurj, hα1, ?_, ?_, ?_, hmem_iff⟩
  · exact evec.surjective.comp hβ₀surj
  · ext z
    rw [MonoidHom.mem_ker]
    show evec (β₀ z) = 1 ↔ z ∈ (blockZ L).subgroupOf (blockU L)
    rw [evec.map_eq_one_iff, ← MonoidHom.mem_ker, hβ₀ker]
  · intro ℓ u v hv
    calc Multiplicative.toAdd (β v)
        = (X : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β₀ v)) := hβapply v
      _ = (X : Matrix (Fin 2) (Fin 2) F).mulVec
            ((α₀ ℓ : Matrix (Fin 2) (Fin 2) F).mulVec
              (Multiplicative.toAdd (β₀ u))) := by rw [hβ₀eq ℓ u v hv]
      _ = ((X * (α₀ ℓ) * X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec
            ((X : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β₀ u))) :=
            mulVec_conj X (α₀ ℓ) _
      _ = ((α ℓ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec
            (Multiplicative.toAdd (β u)) := by rw [hβapply u]; rfl

theorem exists_vertexCoord {L S : Subgroup G} {f : ℕ} [Finite G]
    (hf : 1 ≤ f) (hS : IsSylowTwoOf S L) (hL : IsLin2Type L f)
    (hU : blockU L = pCoreOf 2 L) (hZ : blockZ L = ⊥) :
    Nonempty (VertexCoord L S (GaloisField 2 f)) := by
  classical
  obtain ⟨α, β, hαsurj, hα1, hβsurj, hβker, hβeq, hmem⟩ := exists_normalized_lin2 hf hS hL
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, hZ]
    simp
  let eU : ↥(pCoreOf 2 L) ≃* ↥(blockU L) := (MulEquiv.subgroupCongr hU).symm
  let β₁ : ↥(pCoreOf 2 L) ≃* Multiplicative (Fin 2 → GaloisField 2 f) :=
    eU.trans (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
  refine ⟨⟨α, β₁, hαsurj, hα1, ?_, hmem⟩⟩
  intro ℓ u v hv
  have hv' : ((eU v : ↥(blockU L)) : G) = ℓ * ((eU u : ↥(blockU L)) : G) * ℓ⁻¹ := by
    rw [MulEquiv.subgroupCongr_symm_apply, MulEquiv.subgroupCongr_symm_apply]
    exact hv
  exact hβeq ℓ (eU u) (eU v) hv'

end CFSG.Quasithin.F112R.St84
