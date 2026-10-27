module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalCoord
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.ClassicalGroups CFSG.QuasithinUnique
open scoped MatrixGroups

structure Sp4VertexCoord {G : Type*} [Group G] (L S : Subgroup G) (F : Type*) [Field F] where
  α : ↥L →* SL(2, F)
  γ : ↥(pCoreOf 2 L) ≃* Multiplicative (Fin 3 → F)
  surjective : Function.Surjective α
  eq_one_iff : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L
  equivariant : ∀ (x : ↥L) (u v : ↥(pCoreOf 2 L)), (v : G) = x * u * x⁻¹ →
    Multiplicative.toAdd (γ v) = (sp4RadMat (α x)).mulVec (Multiplicative.toAdd (γ u))
  mem_iff : ∀ x : ↥L, (x : G) ∈ S ↔
    ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]

variable {G : Type} [Group G] {L S : Subgroup G} {F : Type*} [Field F]

private def uOne : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

private def lOne : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

private theorem sp4RadMat_upper {t : F} :
    sp4RadMat (⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, F)) =
      !![1, 0, t; 0, 1, t ^ 2; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp4RadMat]

private theorem sp4RadMat_of_upper {M : SL(2, F)} {t : F}
    (h : (M : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) :
    sp4RadMat M = !![1, 0, t; 0, 1, t ^ 2; 0, 0, 1] := by
  rw [show M = (⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, F)) from Subtype.ext h]
  exact sp4RadMat_upper

private theorem sp4RadMat_lower :
    sp4RadMat (⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, F)) =
      !![1, 1, 0; 0, 1, 0; 0, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp4RadMat]

private theorem sp4RadMat_of_lower {M : SL(2, F)}
    (h : (M : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1]) :
    sp4RadMat M = !![1, 1, 0; 0, 1, 0; 0, 1, 1] := by
  rw [show M = (⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, F)) from Subtype.ext h]
  exact sp4RadMat_lower

private theorem mulVec_upper (t : F) (v : Fin 3 → F) :
    (!![1, 0, t; 0, 1, t ^ 2; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).mulVec v =
      ![v 0 + t * v 2, v 1 + t ^ 2 * v 2, v 2] := by
  funext i
  fin_cases i <;> simp [vecHead, vecTail, Matrix.mulVec, Fin.sum_univ_three]

private theorem mulVec_lower (v : Fin 3 → F) :
    (!![1, 1, 0; 0, 1, 0; 0, 1, 1] : Matrix (Fin 3) (Fin 3) F).mulVec v =
      ![v 0 + v 1, v 1, v 1 + v 2] := by
  funext i
  fin_cases i <;> simp [vecHead, vecTail, Matrix.mulVec, Fin.sum_univ_three]

private theorem second_coord_eq_zero_of_conj (c : Sp4VertexCoord L S F) {b : ↥L}
    {x : ↥(pCoreOf 2 L)}
    (hb : (c.α b : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1])
    (hbx : (b : G) * (x : G) * (b : G)⁻¹ = (x : G)) :
    Multiplicative.toAdd (c.γ x) 2 = 0 := by
  let vx : ↥(pCoreOf 2 L) :=
    ⟨(b : G) * (x : G) * (b : G)⁻¹, PCoreSection.conj_mem_pCoreOf b.2 x.2⟩
  have hvx : vx = x := Subtype.ext hbx
  have heq := c.equivariant b x vx (by rfl)
  rw [hvx] at heq
  rw [sp4RadMat_of_upper hb, mulVec_upper] at heq
  have h1 := congrFun heq 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons,
    one_pow, one_mul] at h1
  have h2 : Multiplicative.toAdd (c.γ x) 1 + Multiplicative.toAdd (c.γ x) 2 =
      Multiplicative.toAdd (c.γ x) 1 + 0 := by simpa using h1.symm
  exact add_left_cancel h2

private theorem first_coord_eq_zero_of_conj (c : Sp4VertexCoord L S F) {b : ↥L}
    {x : ↥(pCoreOf 2 L)}
    (hb : (c.α b : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1])
    (hbx : (b : G) * (x : G) * (b : G)⁻¹ = (x : G)) :
    Multiplicative.toAdd (c.γ x) 1 = 0 := by
  let vx : ↥(pCoreOf 2 L) :=
    ⟨(b : G) * (x : G) * (b : G)⁻¹, PCoreSection.conj_mem_pCoreOf b.2 x.2⟩
  have hvx : vx = x := Subtype.ext hbx
  have heq := c.equivariant b x vx (by rfl)
  rw [hvx] at heq
  rw [sp4RadMat_of_lower hb, mulVec_lower] at heq
  have h1 := congrFun heq 0
  simp only [Matrix.cons_val_zero] at h1
  have h2 : Multiplicative.toAdd (c.γ x) 0 + Multiplicative.toAdd (c.γ x) 1 =
      Multiplicative.toAdd (c.γ x) 0 + 0 := by simpa using h1.symm
  exact add_left_cancel h2

private theorem conj_eq_of_mul_eq {b x : G} (h : b * x = x * b) :
    b * x * b⁻¹ = x := by
  calc b * x * b⁻¹ = (x * b) * b⁻¹ := by rw [h]
    _ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]

theorem Sp4VertexCoord.mem_centralizer_iff (c : Sp4VertexCoord L S F) (hSL : S ≤ L)
    (x : ↥(pCoreOf 2 L)) :
    (∀ s ∈ S, s * (x : G) = (x : G) * s) ↔
      Multiplicative.toAdd (c.γ x) 2 = 0 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := c.surjective uOne
    have hbS : (b : G) ∈ S :=
      (c.mem_iff b).mpr ⟨1, by simpa [uOne] using congrArg Subtype.val hb⟩
    have hmat : (c.α b : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := by
      simpa [uOne] using congrArg Subtype.val hb
    exact second_coord_eq_zero_of_conj c hmat (conj_eq_of_mul_eq (h (b : G) hbS))
  · intro hv s hs
    let sL : ↥L := ⟨s, hSL hs⟩
    obtain ⟨t, ht⟩ := (c.mem_iff sL).mp hs
    let vx : ↥(pCoreOf 2 L) :=
      ⟨s * (x : G) * s⁻¹, PCoreSection.conj_mem_pCoreOf sL.2 x.2⟩
    have heq := c.equivariant sL x vx (by rfl)
    rw [sp4RadMat_of_upper ht, mulVec_upper] at heq
    have heq' : Multiplicative.toAdd (c.γ vx) = Multiplicative.toAdd (c.γ x) := by
      rw [heq]
      funext i
      fin_cases i <;> simp [hv]
    have hvx : vx = x := c.γ.injective (Multiplicative.toAdd.injective heq')
    have hcx : s * (x : G) * s⁻¹ = (x : G) := by
      have h := congrArg (fun z : ↥(pCoreOf 2 L) => (z : G)) hvx
      simpa [vx] using h
    calc s * (x : G) = s * (x : G) * s⁻¹ * s := by group
      _ = (x : G) * s := by rw [hcx]

theorem Sp4VertexCoord.commutator (c : Sp4VertexCoord L S F) {s : ↥L} {t : F}
    (hs : (c.α s : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    (x v : ↥(pCoreOf 2 L)) (hv : (v : G) = s * x * s⁻¹ * x⁻¹) :
    Multiplicative.toAdd (c.γ v) =
      ![t * Multiplicative.toAdd (c.γ x) 2, t ^ 2 * Multiplicative.toAdd (c.γ x) 2, 0] := by
  let u : ↥(pCoreOf 2 L) := ⟨s * (x : G) * s⁻¹, PCoreSection.conj_mem_pCoreOf s.2 x.2⟩
  have hvu : v = u * x⁻¹ := Subtype.ext (by simpa [u] using hv)
  have hγu : Multiplicative.toAdd (c.γ u) =
      (sp4RadMat (c.α s)).mulVec (Multiplicative.toAdd (c.γ x)) := by
    simpa [u] using c.equivariant s x u (by rfl)
  have hγv : Multiplicative.toAdd (c.γ v) =
      Multiplicative.toAdd (c.γ u) - Multiplicative.toAdd (c.γ x) := by
    rw [hvu, map_mul, map_inv]
    simp [toAdd_mul, toAdd_inv, sub_eq_add_neg]
  calc Multiplicative.toAdd (c.γ v)
      = Multiplicative.toAdd (c.γ u) - Multiplicative.toAdd (c.γ x) := hγv
    _ = (sp4RadMat (c.α s)).mulVec (Multiplicative.toAdd (c.γ x)) -
          Multiplicative.toAdd (c.γ x) := by rw [hγu]
    _ = ![t * Multiplicative.toAdd (c.γ x) 2, t ^ 2 * Multiplicative.toAdd (c.γ x) 2, 0] := by
          rw [sp4RadMat_of_upper hs, mulVec_upper]
          funext i
          fin_cases i <;> simp [Pi.sub_apply] <;> ring

theorem Sp4VertexCoord.mem_blockZ_iff (c : Sp4VertexCoord L S F)
    (hU : blockU L = pCoreOf 2 L) (x : ↥(pCoreOf 2 L)) :
    (x : G) ∈ blockZ L ↔
      Multiplicative.toAdd (c.γ x) 1 = 0 ∧ Multiplicative.toAdd (c.γ x) 2 = 0 := by
  constructor
  · intro hx
    rw [blockZ, Subgroup.mem_inf] at hx
    obtain ⟨-, hxC⟩ := hx
    have hcomm : ∀ l : ↥L, (l : G) * (x : G) = (x : G) * (l : G) := fun l =>
      (Subgroup.mem_centralizer_iff.mp hxC) (l : G) l.2
    constructor
    · obtain ⟨b, hb⟩ := c.surjective lOne
      have hmat : (c.α b : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := by
        simpa [lOne] using congrArg Subtype.val hb
      exact first_coord_eq_zero_of_conj c hmat (conj_eq_of_mul_eq (hcomm b))
    · obtain ⟨b, hb⟩ := c.surjective uOne
      have hmat : (c.α b : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := by
        simpa [uOne] using congrArg Subtype.val hb
      exact second_coord_eq_zero_of_conj c hmat (conj_eq_of_mul_eq (hcomm b))
  · rintro ⟨h1, h2⟩
    rw [blockZ, Subgroup.mem_inf]
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · rw [hU]; exact x.2
    · intro l hl
      let lL : ↥L := ⟨l, hl⟩
      let vx : ↥(pCoreOf 2 L) :=
        ⟨l * (x : G) * l⁻¹, PCoreSection.conj_mem_pCoreOf lL.2 x.2⟩
      have heq := c.equivariant lL x vx (by rfl)
      have hfix : (sp4RadMat (c.α lL)).mulVec (Multiplicative.toAdd (c.γ x)) =
          Multiplicative.toAdd (c.γ x) := by
        rw [sp4RadMat_mulVec]
        funext i
        fin_cases i <;> simp [h1, h2]
      have hγ : Multiplicative.toAdd (c.γ vx) = Multiplicative.toAdd (c.γ x) := by
        rw [heq, hfix]
      have hvx : vx = x := c.γ.injective (Multiplicative.toAdd.injective hγ)
      have hcx : l * (x : G) * l⁻¹ = (x : G) := by
        have h := congrArg (fun z : ↥(pCoreOf 2 L) => (z : G)) hvx
        simpa [vx] using h
      calc l * (x : G) = l * (x : G) * l⁻¹ * l := by group
        _ = (x : G) * l := by rw [hcx]

theorem Sp4VertexCoord.exists_of_mem_normalizer (c : Sp4VertexCoord L S F) (hSL : S ≤ L)
    {b : ↥L} (hb : (b : G) ∈ Subgroup.normalizer (S : Set G)) :
    ∃ (ν : Fˣ) (r : F),
      (c.α b : Matrix (Fin 2) (Fin 2) F) = !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] :=
  exists_of_mem_normalizer_of_mem_iff c.α c.surjective c.mem_iff hSL hb

theorem Sp4VertexCoord.exists_mem_normalizer (c : Sp4VertexCoord L S F) (hSL : S ≤ L) (ν : Fˣ) :
    ∃ b : ↥L, (b : G) ∈ Subgroup.normalizer (S : Set G) ∧
      ∃ r : F, (c.α b : Matrix (Fin 2) (Fin 2) F) =
        !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] :=
  exists_mem_normalizer_of_mem_iff c.α c.surjective c.mem_iff hSL ν

end CFSG.Quasithin.F112R.St84
