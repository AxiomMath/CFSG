module

public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelOm
public import CFSG.LocalAnalysis.StandardType.FS81.RootS3Supp
public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalGroups.Orthogonal CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.GF2n.Smith81 CFSG.SeitzReduction.OmegaPilot

theorem lin_genGL_empty_apply {a b : Fin 6} (hab : a ≠ b) (v : V12) :
    lin (genGL hab ∅) v = v + v (Sum.inl b) • (Pi.single (Sum.inl a) 1 : V12) +
      v (Sum.inr a) • (Pi.single (Sum.inr b) 1 : V12) := by
  rw [lin, MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
    coe_genGL]
  have hmat : genMat a b (∅ : Finset (Fin 6)) =
      (1 : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)) +
        Matrix.single (Sum.inl a) (Sum.inl b) (1 : ZMod 2) +
        Matrix.single (Sum.inr b) (Sum.inr a) 1 := by
    ext x y
    rcases x with i | i <;> rcases y with j | j
    · simp only [genMat, flipPermFun, Finset.notMem_empty, if_false, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Sum.inl.injEq, Sum.inr.injEq, Matrix.transvection]
      by_cases hia : i = a <;> by_cases hjb : j = b <;> simp [hia, hjb, eq_comm]
    · simp [genMat, flipPermFun, Matrix.fromBlocks_apply₁₂, Matrix.one_apply,
        Matrix.single_apply]
    · simp [genMat, flipPermFun, Matrix.fromBlocks_apply₂₁, Matrix.one_apply,
        Matrix.single_apply]
    · simp only [genMat, flipPermFun, Finset.notMem_empty, if_false, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Sum.inl.injEq, Sum.inr.injEq, Matrix.transpose_apply, Matrix.transvection]
      by_cases hib : i = b <;> by_cases hja : j = a <;> simp [hib, hja, eq_comm, and_comm]
  rw [hmat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq, Matrix.single_mulVec_eq]
  simp [Pi.add_apply, one_mul, add_assoc]

theorem lin_genGL_empty_eq_eichler {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab ∅) =
      eichler Q12 (Pi.single (Sum.inl a) 1 : V12) (Pi.single (Sum.inr b) 1 : V12) := by
  refine LinearEquiv.ext fun v => ?_
  rw [lin_genGL_empty_apply hab v, eichler_apply]
  · rw [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inl,
      CFSG.LieType.Universal.Spin.polar_quadPlus_single_inr]
    have hQ : Q12 (Pi.single (Sum.inr b) 1 : V12) = 0 := by
      rw [Q12, CFSG.LieType.Universal.Spin.quadPlus_apply]
      simp [Pi.single_apply]
    rw [hQ, zero_mul, add_zero, sub_eq_add_vec (ZMod 2)]
    abel
  · rw [Q12, CFSG.LieType.Universal.Spin.quadPlus_apply]
    simp [Pi.single_apply]
  · rw [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inr]
    simp [Pi.single_apply, hab]

abbrev vecE (i : Fin 6) : V12 := Pi.single (Sum.inl i) 1

abbrev vecF (i : Fin 6) : V12 := Pi.single (Sum.inr i) 1

private theorem quadPlus_single_inl_zero (i : Fin 6) : Q12 (vecE i) = 0 := by
  rw [Q12, CFSG.LieType.Universal.Spin.quadPlus_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [vecE, Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl]

private theorem quadPlus_single_inr_zero (i : Fin 6) : Q12 (vecF i) = 0 := by
  rw [Q12, CFSG.LieType.Universal.Spin.quadPlus_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [vecF, Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl]

private theorem polar_Q12_vecE_vecF {a b : Fin 6} (hab : a ≠ b) :
    QuadraticMap.polar Q12 (vecE a) (vecF b) = 0 := by
  simp only [Q12, vecE, vecF]
  rw [CFSG.LieType.Universal.Spin.polar_quadPlus_single_inr]
  simp [Pi.single_apply, Ne.symm hab]

private theorem linearIndependent_vecE_vecF {a b : Fin 6} (hab : a ≠ b) :
    LinearIndependent (ZMod 2) ![vecE a, vecF b] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  constructor
  · have hc := congrArg (fun w : V12 => w (Sum.inl a)) h
    simpa [vecE, vecF, Pi.add_apply, Pi.smul_apply, Pi.single_apply] using hc
  · have hc := congrArg (fun w : V12 => w (Sum.inr b)) h
    simpa [vecE, vecF, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hab] using hc

theorem lin_genGL_empty_sq {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab ∅) * lin (genGL hab ∅) = 1 := by
  rw [lin_genGL_empty_eq_eichler hab]
  rw [eichler_mul (Q := Q12) (polar_Q12_vecE_vecF hab) (polar_Q12_vecE_vecF hab),
    add_self_vec (ZMod 2), eichler_zero_right]

theorem lin_genGL_symm_empty_sq {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab.symm ∅) * lin (genGL hab.symm ∅) = 1 := by
  rw [lin_genGL_empty_eq_eichler (a := b) (b := a) hab.symm]
  rw [eichler_mul (Q := Q12) (polar_Q12_vecE_vecF (a := b) (b := a) hab.symm)
      (polar_Q12_vecE_vecF (a := b) (b := a) hab.symm),
    add_self_vec (ZMod 2), eichler_zero_right]

private theorem lin_genGL_empty_mem_O12 {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab ∅) ∈ TauCeti.QuadraticMap.orthogonalGroup Q12 := by
  rw [lin_genGL_empty_eq_eichler hab]
  exact eichler_mem_orthogonalGroup Q12 (vecE a) (vecF b)

private theorem lin_genGL_symm_empty_mem_O12 {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab.symm ∅) ∈ TauCeti.QuadraticMap.orthogonalGroup Q12 := by
  rw [lin_genGL_empty_eq_eichler (a := b) (b := a) hab.symm]
  exact eichler_mem_orthogonalGroup Q12 (vecE b) (vecF a)

private theorem lin_genGL_empty_apply_vecE_self {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab ∅) (vecE a) = vecE a := by
  rw [lin_genGL_empty_apply hab]
  simp [vecE, vecF, Pi.single_apply, Ne.symm hab]

private theorem lin_genGL_empty_apply_vecE_other {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab ∅) (vecE b) = vecE b + vecE a := by
  rw [lin_genGL_empty_apply hab]
  simp [vecE, vecF, Pi.single_apply]

private theorem lin_genGL_empty_apply_vecF_other {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab ∅) (vecF a) = vecF a + vecF b := by
  rw [lin_genGL_empty_apply hab]
  simp [vecE, vecF, Pi.single_apply]

private theorem lin_genGL_symm_empty_apply_vecE_self {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab.symm ∅) (vecE b) = vecE b := by
  rw [lin_genGL_empty_apply (a := b) (b := a) hab.symm]
  simp [vecE, vecF, Pi.single_apply, hab]

private theorem lin_genGL_symm_empty_apply_vecE_other {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab.symm ∅) (vecE a) = vecE a + vecE b := by
  rw [lin_genGL_empty_apply (a := b) (b := a) hab.symm]
  simp [vecE, vecF, Pi.single_apply]

private theorem lin_genGL_symm_empty_apply_vecF_other {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab.symm ∅) (vecF b) = vecF b + vecF a := by
  rw [lin_genGL_empty_apply (a := b) (b := a) hab.symm]
  simp [vecE, vecF, Pi.single_apply]

private theorem lin_genGL_empty_mul_symm_mul {a b : Fin 6} (hab : a ≠ b) :
    lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅) =
      lin (genGL hab.symm ∅) * lin (genGL hab ∅) * lin (genGL hab.symm ∅) := by
  have hxinv : (lin (genGL hab ∅))⁻¹ = lin (genGL hab ∅) :=
    inv_eq_of_mul_eq_one_right (lin_genGL_empty_sq hab)
  have hyinv : (lin (genGL hab.symm ∅))⁻¹ = lin (genGL hab.symm ∅) :=
    inv_eq_of_mul_eq_one_right (lin_genGL_symm_empty_sq hab)
  have hxO : lin (genGL hab ∅) ∈ TauCeti.QuadraticMap.orthogonalGroup Q12 :=
    lin_genGL_empty_mem_O12 hab
  have hyO : lin (genGL hab.symm ∅) ∈ TauCeti.QuadraticMap.orthogonalGroup Q12 :=
    lin_genGL_symm_empty_mem_O12 hab
  have hx : lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅) =
      eichler Q12 (vecE b + vecE a) (vecF a + vecF b) := by
    calc lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅)
        = lin (genGL hab ∅) * lin (genGL hab.symm ∅) * (lin (genGL hab ∅))⁻¹ := by
            rw [hxinv]
      _ = lin (genGL hab ∅) * eichler Q12 (vecE b) (vecF a) *
            (lin (genGL hab ∅))⁻¹ := by
            rw [lin_genGL_empty_eq_eichler (a := b) (b := a) hab.symm]
      _ = eichler Q12 (lin (genGL hab ∅) (vecE b)) (lin (genGL hab ∅) (vecF a)) :=
            eichler_conj hxO (vecE b) (vecF a)
      _ = eichler Q12 (vecE b + vecE a) (vecF a + vecF b) := by
            rw [lin_genGL_empty_apply_vecE_other hab, lin_genGL_empty_apply_vecF_other hab]
  have hy : lin (genGL hab.symm ∅) * lin (genGL hab ∅) * lin (genGL hab.symm ∅) =
      eichler Q12 (vecE a + vecE b) (vecF b + vecF a) := by
    calc lin (genGL hab.symm ∅) * lin (genGL hab ∅) * lin (genGL hab.symm ∅)
        = lin (genGL hab.symm ∅) * lin (genGL hab ∅) * (lin (genGL hab.symm ∅))⁻¹ := by
            rw [hyinv]
      _ = lin (genGL hab.symm ∅) * eichler Q12 (vecE a) (vecF b) *
            (lin (genGL hab.symm ∅))⁻¹ := by
            rw [lin_genGL_empty_eq_eichler hab]
      _ = eichler Q12 (lin (genGL hab.symm ∅) (vecE a))
            (lin (genGL hab.symm ∅) (vecF b)) :=
            eichler_conj hyO (vecE a) (vecF b)
      _ = eichler Q12 (vecE a + vecE b) (vecF b + vecF a) := by
            rw [lin_genGL_symm_empty_apply_vecE_other hab,
              lin_genGL_symm_empty_apply_vecF_other hab]
  rw [hx, hy]
  have h1 : (vecE b + vecE a : V12) = vecE a + vecE b := by abel
  have h2 : (vecF a + vecF b : V12) = vecF b + vecF a := by abel
  rw [h1, h2]

theorem isOrthA2_genGL_empty {a b : Fin 6} (hab : a ≠ b) :
    IsOrthA2 Q12 (lin (genGL hab ∅)) ∧
      commSpace (lin (genGL hab ∅)) = Submodule.span (ZMod 2) {vecE a, vecF b} := by
  have hQ : (QuadraticMap.polarBilin Q12).Nondegenerate := by
    change (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2))).Nondegenerate
    exact CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)
  rw [lin_genGL_empty_eq_eichler hab]
  exact isOrthA2_eichler hQ (quadPlus_single_inl_zero a) (quadPlus_single_inr_zero b)
    (polar_Q12_vecE_vecF hab) (linearIndependent_vecE_vecF hab)

theorem isOrthA2_genGL_symm_empty {a b : Fin 6} (hab : a ≠ b) :
    IsOrthA2 Q12 (lin (genGL hab.symm ∅)) ∧
      commSpace (lin (genGL hab.symm ∅)) = Submodule.span (ZMod 2) {vecE b, vecF a} := by
  have hQ : (QuadraticMap.polarBilin Q12).Nondegenerate := by
    change (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2))).Nondegenerate
    exact CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)
  rw [lin_genGL_empty_eq_eichler (a := b) (b := a) hab.symm]
  exact isOrthA2_eichler hQ (quadPlus_single_inl_zero b) (quadPlus_single_inr_zero a)
    (polar_Q12_vecE_vecF (a := b) (b := a) hab.symm)
    (linearIndependent_vecE_vecF (a := b) (b := a) hab.symm)

theorem isOrthA2_genGL_empty_conj {a b : Fin 6} (hab : a ≠ b) :
    IsOrthA2 Q12 (lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅)) ∧
      commSpace (lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅)) =
        Submodule.span (ZMod 2) {vecE a + vecE b, vecF a + vecF b} := by
  have hxinv : (lin (genGL hab ∅))⁻¹ = lin (genGL hab ∅) :=
    inv_eq_of_mul_eq_one_right (lin_genGL_empty_sq hab)
  have hxO : lin (genGL hab ∅) ∈ TauCeti.QuadraticMap.orthogonalGroup Q12 :=
    lin_genGL_empty_mem_O12 hab
  constructor
  · have h := IsOrthA2.conj (Q := Q12) hxO (isOrthA2_genGL_symm_empty hab).1
    rwa [show lin (genGL hab ∅) * lin (genGL hab.symm ∅) * (lin (genGL hab ∅))⁻¹ =
      lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅) by rw [hxinv]] at h
  · rw [show lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅) =
      lin (genGL hab ∅) * lin (genGL hab.symm ∅) * (lin (genGL hab ∅))⁻¹ by rw [hxinv],
      commSpace_conj, (isOrthA2_genGL_symm_empty hab).2, Submodule.map_span, Set.image_pair]
    simp only [LinearEquiv.coe_coe]
    rw [lin_genGL_empty_apply_vecE_other hab, lin_genGL_empty_apply_vecF_other hab,
      show vecE b + vecE a = vecE a + vecE b by abel]

private theorem isTypeA_of_isOrthA2 {q : QuadraticForm (ZMod 2) V12}
    {t : V12 ≃ₗ[ZMod 2] V12} (h : IsOrthA2 q t) : IsTypeA q t 2 :=
  ⟨fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup h.mem v, h.ne_one,
    h.mul_self, h.finrank_eq, h.vanish⟩

private abbrev IsSixWord {G : Type*} [Group G] (x y z : G) : Prop :=
  z = 1 ∨ z = x ∨ z = y ∨ z = x * y ∨ z = y * x ∨ z = (x * y) * x

private theorem isSixWord_of_mem_closure {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (hrel : (x * y) * x = (y * x) * y) :
    ∀ z ∈ Subgroup.closure ({x, y} : Set G), IsSixWord x y z := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hmulx : ∀ z, IsSixWord x y z → IsSixWord x y (x * z) := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl (mul_one x))
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hx, one_mul])))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mul_assoc x y x).symm))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      calc x * ((x * y) * x) = (x * (x * y)) * x := (mul_assoc x (x * y) x).symm
        _ = ((x * x) * y) * x := by rw [← mul_assoc x x y]
        _ = y * x := by rw [hx, one_mul]
  have hmuly : ∀ z, IsSixWord x y z → IsSixWord x y (y * z) := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (mul_one y)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inl hy
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      calc y * (x * y) = (y * x) * y := (mul_assoc y x y).symm
        _ = (x * y) * x := hrel.symm
    · refine Or.inr (Or.inl ?_)
      calc y * (y * x) = (y * y) * x := (mul_assoc y y x).symm
        _ = x := by rw [hy, one_mul]
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      calc y * ((x * y) * x) = (y * (x * y)) * x := (mul_assoc y (x * y) x).symm
        _ = ((y * x) * y) * x := by rw [← mul_assoc y x y]
        _ = ((x * y) * x) * x := by rw [hrel.symm]
        _ = (x * y) * (x * x) := by rw [mul_assoc (x * y) x x]
        _ = x * y := by rw [hx, mul_one]
  intro z hz
  refine Subgroup.closure_induction_left (p := fun z _ => IsSixWord x y z) (Or.inl rfl)
    ?_ ?_ hz
  · intro g hg w hw ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hmulx w ih
    · exact hmuly w ih
  · intro g hg w hw ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · rw [hxinv]; exact hmulx w ih
    · rw [hyinv]; exact hmuly w ih

private theorem genGL_empty_mul_ne_one {a b : Fin 6} (hab : a ≠ b) :
    (lin (genGL hab ∅) * lin (genGL hab.symm ∅)) *
      (lin (genGL hab ∅) * lin (genGL hab.symm ∅)) ≠ 1 := by
  intro h
  have hxy : (lin (genGL hab ∅) * lin (genGL hab.symm ∅)) (vecE b) = vecE b + vecE a := by
    rw [LinearEquiv.mul_apply, lin_genGL_symm_empty_apply_vecE_self hab,
      lin_genGL_empty_apply_vecE_other hab]
  have hsq : (lin (genGL hab ∅) * lin (genGL hab.symm ∅))
      ((lin (genGL hab ∅) * lin (genGL hab.symm ∅)) (vecE b)) = vecE a := by
    rw [hxy, LinearEquiv.mul_apply, map_add,
      lin_genGL_symm_empty_apply_vecE_self hab, lin_genGL_symm_empty_apply_vecE_other hab,
      show vecE b + (vecE a + vecE b) = vecE a by
        rw [add_comm (vecE a) (vecE b), ← add_assoc, add_self_vec (ZMod 2), zero_add],
      lin_genGL_empty_apply_vecE_self hab]
  have hleft : (lin (genGL hab ∅) * lin (genGL hab.symm ∅))
      ((lin (genGL hab ∅) * lin (genGL hab.symm ∅)) (vecE b)) = vecE b := by
    change ((lin (genGL hab ∅) * lin (genGL hab.symm ∅)) *
      (lin (genGL hab ∅) * lin (genGL hab.symm ∅))) (vecE b) = vecE b
    rw [h]
    simp
  rw [hsq] at hleft
  have hcoord := congrArg (fun w : V12 => w (Sum.inl a)) hleft
  simp [vecE, Pi.single_apply] at hcoord
  exact hab hcoord

private theorem genGL_symm_empty_mul_ne_one {a b : Fin 6} (hab : a ≠ b) :
    (lin (genGL hab.symm ∅) * lin (genGL hab ∅)) *
      (lin (genGL hab.symm ∅) * lin (genGL hab ∅)) ≠ 1 := by
  intro h
  have hyx : (lin (genGL hab.symm ∅) * lin (genGL hab ∅)) (vecE b) = vecE a := by
    rw [LinearEquiv.mul_apply, lin_genGL_empty_apply_vecE_other hab, map_add,
      lin_genGL_symm_empty_apply_vecE_self hab, lin_genGL_symm_empty_apply_vecE_other hab,
      add_comm (vecE a) (vecE b), ← add_assoc, add_self_vec (ZMod 2), zero_add]
  have hsq : (lin (genGL hab.symm ∅) * lin (genGL hab ∅))
      ((lin (genGL hab.symm ∅) * lin (genGL hab ∅)) (vecE b)) = vecE a + vecE b := by
    rw [hyx, LinearEquiv.mul_apply, lin_genGL_empty_apply_vecE_self hab,
      lin_genGL_symm_empty_apply_vecE_other hab]
  have hleft : (lin (genGL hab.symm ∅) * lin (genGL hab ∅))
      ((lin (genGL hab.symm ∅) * lin (genGL hab ∅)) (vecE b)) = vecE b := by
    change ((lin (genGL hab.symm ∅) * lin (genGL hab ∅)) *
      (lin (genGL hab.symm ∅) * lin (genGL hab ∅))) (vecE b) = vecE b
    rw [h]
    simp
  rw [hsq] at hleft
  have hcoord := congrArg (fun w : V12 => w (Sum.inl a)) hleft
  simp [vecE, Pi.single_apply] at hcoord

theorem eq_of_sixWord_involution {a b : Fin 6} (hab : a ≠ b)
    {s : V12 ≃ₗ[ZMod 2] V12} (hs : s ∈ rootL ({a, b} : Finset (Fin 6)) ∅)
    (hss : s * s = 1) (hs1 : s ≠ 1) :
    s = lin (genGL hab ∅) ∨ s = lin (genGL hab.symm ∅) ∨
      s = lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅) := by
  have hsix : IsSixWord (lin (genGL hab ∅)) (lin (genGL hab.symm ∅)) s := by
    refine isSixWord_of_mem_closure (lin_genGL_empty_sq hab) (lin_genGL_symm_empty_sq hab)
      (lin_genGL_empty_mul_symm_mul hab) s ?_
    rwa [rootL_eq_closure hab ∅] at hs
  rcases hsix with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hs1
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd hss (genGL_empty_mul_ne_one hab)
  · exact absurd hss (genGL_symm_empty_mul_ne_one hab)
  · exact Or.inr (Or.inr rfl)

theorem isTypeA_genGL_empty {a b : Fin 6} (hab : a ≠ b) :
    IsTypeA Q12 (lin (genGL hab ∅)) 2 :=
  isTypeA_of_isOrthA2 (isOrthA2_genGL_empty hab).1

theorem isTypeA_genGL_symm_empty {a b : Fin 6} (hab : a ≠ b) :
    IsTypeA Q12 (lin (genGL hab.symm ∅)) 2 :=
  isTypeA_of_isOrthA2 (isOrthA2_genGL_symm_empty hab).1

theorem isTypeA_genGL_empty_conj {a b : Fin 6} (hab : a ≠ b) :
    IsTypeA Q12 (lin (genGL hab ∅) * lin (genGL hab.symm ∅) * lin (genGL hab ∅)) 2 :=
  isTypeA_of_isOrthA2 (isOrthA2_genGL_empty_conj hab).1

end CFSG.StandardType.FrameRoute.FS81.D6M
