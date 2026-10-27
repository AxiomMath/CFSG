module

public import CFSG.Quasithin.EmptyFaithful.S153QPC1

public section

namespace CFSG.Quasithin.QP

open Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem exists_noncommuting_sl2 : ∃ s t : SpecialLinearGroup (Fin 2) F, s * t ≠ t * s := by
  refine ⟨SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1,
    SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1, fun h => ?_⟩
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [SpecialLinearGroup.transvection, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.single_apply, Matrix.one_apply] at h1

theorem exists_scalar_of_abelian_normal [Finite F] (h4 : 4 ≤ Nat.card F) (Nb : Subgroup (GL (Fin 2) F))
    [Nb.Normal] (hab : ∀ a ∈ Nb, ∀ b ∈ Nb, a * b = b * a) {x : GL (Fin 2) F} (hx : x ∈ Nb) :
    ∃ c : Fˣ, (x : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (c : F) := by
  have hsimple := sl2_isSimpleGroup (K := F) h4
  set C : Subgroup (SpecialLinearGroup (Fin 2) F) :=
    Nb.comap (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F) with hC
  have hCn : C.Normal := inferInstance
  have hCbot : C = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal C with h | h
    · exact h
    · exfalso
      obtain ⟨s, t, hst⟩ := exists_noncommuting_sl2 (F := F)
      apply hst
      have hs : s ∈ C := h ▸ Subgroup.mem_top s
      have ht : t ∈ C := h ▸ Subgroup.mem_top t
      apply SpecialLinearGroup.toGL_injective
      rw [map_mul, map_mul]
      exact hab _ hs _ ht
  have hcomm : ∀ s : SpecialLinearGroup (Fin 2) F,
      x * SpecialLinearGroup.toGL s = SpecialLinearGroup.toGL s * x := by
    intro s
    set c : GL (Fin 2) F := x * SpecialLinearGroup.toGL s * x⁻¹ * (SpecialLinearGroup.toGL s)⁻¹ with hc
    have hcN : c ∈ Nb := by
      have h1 : SpecialLinearGroup.toGL s * x⁻¹ * (SpecialLinearGroup.toGL s)⁻¹ ∈ Nb :=
        Subgroup.Normal.conj_mem inferInstance _ (Nb.inv_mem hx) _
      have h2 := Nb.mul_mem hx h1
      convert h2 using 1
      rw [hc]
      group
    have hdet : Matrix.GeneralLinearGroup.det c = 1 := by
      rw [hc]
      simp [map_mul, map_inv]
    set s' : SpecialLinearGroup (Fin 2) F := ⟨(c : Matrix (Fin 2) (Fin 2) F), by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩ with hs'
    have hs'C : s' ∈ C := by
      show SpecialLinearGroup.toGL s' ∈ Nb
      have : SpecialLinearGroup.toGL s' = c := Units.ext rfl
      rw [this]
      exact hcN
    rw [hCbot, Subgroup.mem_bot] at hs'C
    have hc1 : c = 1 := by
      have : SpecialLinearGroup.toGL s' = 1 := by rw [hs'C, map_one]
      rw [← this]
      exact (Units.ext rfl : SpecialLinearGroup.toGL s' = c).symm ▸ rfl
    rw [hc] at hc1
    calc x * SpecialLinearGroup.toGL s = x * SpecialLinearGroup.toGL s * x⁻¹ * (SpecialLinearGroup.toGL s)⁻¹ *
        SpecialLinearGroup.toGL s * x := by group
      _ = SpecialLinearGroup.toGL s * x := by rw [hc1]; group
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := (x : Matrix (Fin 2) (Fin 2) F))
    (fun t => by
      have := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F))
        (hcomm (SpecialLinearGroup.transvection t.hij t.c))
      exact this.symm)
  have hr0 : r ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hr, h]
    simp
  exact ⟨Units.mk0 r hr0, by rw [← hr]; rfl⟩

end CFSG.Quasithin.QP
