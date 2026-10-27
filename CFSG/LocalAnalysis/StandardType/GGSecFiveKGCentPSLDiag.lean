module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LieType.Universal.SpecialLinearRoots

public section

namespace CFSG.StandardType.KGCentPSL

section StandardPosition

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem exists_isDiag_conj_of_stdPos {m : ℕ} (hm : 2 ≤ m) {F : Type} [Field F] {G : Type}
    [Group G] (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {d : G}
    (hstd : ∀ γ ∈ (SpecialLinear.rootDatum m F).roots,
      ∃ h ∈ ggTorus (SpecialLinear.rootDatum m F), ∀ z ∈ (SpecialLinear.rootDatum m F).rootGroup γ,
        d * ψ z * d⁻¹ = ψ (h * z * h⁻¹)) :
    ∃ D : GL (Fin (m + 1)) F,
      ((D : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag ∧
        ∀ u, d * ψ u * d⁻¹ = ψ (InnerDiagA.conjSL D u) := by
  have key : ∀ (i j : Fin (m + 1)) (hij : i ≠ j), ∃ χ : F, ∀ t : F,
      d * ψ (SpecialLinearGroup.transvection hij t) * d⁻¹ =
        ψ (SpecialLinearGroup.transvection hij (χ * t)) := by
    intro i j hij
    obtain ⟨h, hh, hz⟩ := hstd _ (InnerDiagA.typeARoot_mem_roots F hij)
    have hN : h ∈ Subgroup.normalizer (SpecialLinear.rootSubgroup m F hij :
        Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      have h1 : h ∈ Subgroup.normalizer (SpecialLinear.rootGroup m F (InnerDiagA.typeARoot i j) :
          Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :=
        hh _ (InnerDiagA.typeARoot_mem_roots F hij)
      rwa [InnerDiagA.rootGroup_typeARoot] at h1
    obtain ⟨χ, hχ⟩ := InnerDiagA.exists_conj_transvection_eq hij hN
    have hmem : ∀ t : F, Matrix.SpecialLinearGroup.transvection hij t ∈
        SpecialLinear.rootGroup m F (InnerDiagA.typeARoot i j) := fun t => by
      rw [InnerDiagA.rootGroup_typeARoot]
      exact SpecialLinear.transvection_mem_rootSubgroup hij t
    refine ⟨χ, fun t => ?_⟩
    rw [hz _ (hmem t), hχ]
  choose! χ hχ using key
  let β : SpecialLinearGroup (Fin (m + 1)) F →* G := (MulAut.conj d).toMonoidHom.comp ψ
  have hβ : ∀ u, β u = d * ψ u * d⁻¹ := fun u => by
    simp [β]
  have hχ' : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (t : F),
      β (SpecialLinearGroup.transvection hij t) =
        ψ (SpecialLinearGroup.transvection hij (χ i j * t)) :=
    fun i j hij t => (hβ _).trans (hχ i j hij t)
  have hne : ∀ i j : Fin (m + 1), i ≠ j → χ i j ≠ 0 := by
    intro i j hij h0
    have h1 := hχ i j hij 1
    rw [h0, zero_mul, SpecialLinearGroup.transvection_coeff_zero, map_one] at h1
    have h2 : ψ (SpecialLinearGroup.transvection hij 1) = 1 := by
      calc ψ (SpecialLinearGroup.transvection hij 1)
          = d⁻¹ * (d * ψ (SpecialLinearGroup.transvection hij 1) * d⁻¹) * d := by group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (InnerDiagA.eq_zero_of_transvection_mem_center hij (hker h2))
  obtain ⟨e, he⟩ := InnerDiagA.exists_diag_of_cocycle (χ := χ) hm
    (fun _ _ _ hij hjk hik => InnerDiagA.chi_cocycle ψ β hker hχ' hij hjk hik) hne
  refine ⟨InnerDiagA.diagGL e, ?_, fun u => ?_⟩
  · rw [InnerDiagA.coe_diagGL]
    exact isDiag_diagonal _
  · have hβψ : β = ψ.comp (InnerDiagA.conjSL (InnerDiagA.diagGL e)) := by
      refine MonoidHom.eq_of_eqOn_dense
        Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
      rintro _ ⟨⟨i, j, hij, t⟩, rfl⟩
      rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, hχ', MonoidHom.comp_apply,
        InnerDiagA.conjSL_diagGL_transvection, he i j hij, Units.val_inv_eq_inv_val,
        mul_right_comm (χ i j), mul_assoc _ _ ((e j : F))⁻¹, mul_inv_cancel₀ (e j).ne_zero,
        mul_one]
    rw [← hβ, hβψ, MonoidHom.comp_apply]

private theorem exists_diagGL_eq_of_isDiag {m : ℕ} {F : Type} [Field F] {D : GL (Fin (m + 1)) F}
    (hD : ((D : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) :
    ∃ e : Fin (m + 1) → Fˣ, D = InnerDiagA.diagGL e := by
  have hdet : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit).ne_zero
  rw [← hD.diagonal_diag, det_diagonal] at hdet
  have hne : ∀ k, (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k k ≠ 0 :=
    fun k h0 => hdet (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  refine ⟨fun k => Units.mk0 _ (hne k), Units.ext ?_⟩
  rw [InnerDiagA.coe_diagGL]
  exact hD.diagonal_diag.symm

theorem commute_transvection_iff_diag_eq {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {d : G}
    {D : GL (Fin (m + 1)) F}
    (hD : ((D : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag)
    (hconj : ∀ u, d * ψ u * d⁻¹ = ψ (InnerDiagA.conjSL D u)) {a b : Fin (m + 1)} (hab : a ≠ b) :
    (∀ c : F, d * ψ (SpecialLinearGroup.transvection hab c) =
        ψ (SpecialLinearGroup.transvection hab c) * d) ↔
      ((D : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a =
        ((D : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) b b := by
  obtain ⟨e, rfl⟩ := exists_diagGL_eq_of_isDiag hD
  have hconjt : ∀ c : F, d * ψ (SpecialLinearGroup.transvection hab c) * d⁻¹ =
      ψ (SpecialLinearGroup.transvection hab ((e a : F) * c * ((e b)⁻¹ : Fˣ))) := fun c => by
    rw [hconj, InnerDiagA.conjSL_diagGL_transvection]
  have hentry : ∀ k, ((InnerDiagA.diagGL e : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) k k = (e k : F) := fun k => by
    rw [InnerDiagA.coe_diagGL, diagonal_apply_eq]
  rw [hentry a, hentry b]
  constructor
  · intro hc
    have h3 : ψ (SpecialLinearGroup.transvection hab 1) =
        ψ (SpecialLinearGroup.transvection hab ((e a : F) * 1 * ((e b)⁻¹ : Fˣ))) :=
      (mul_inv_eq_iff_eq_mul.2 (hc 1)).symm.trans (hconjt 1)
    have h4 := InnerDiagA.eq_of_map_transvection_eq ψ hker hab h3
    rw [mul_one, Units.val_inv_eq_inv_val] at h4
    exact (mul_inv_eq_one₀ (e b).ne_zero).1 h4.symm
  · intro h c
    have h2 : (e a : F) * c * ((e b)⁻¹ : Fˣ) = c := by
      rw [h, Units.val_inv_eq_inv_val, mul_comm, ← mul_assoc, inv_mul_cancel₀ (e b).ne_zero,
        one_mul]
    have h3 := hconjt c
    rw [h2] at h3
    exact mul_inv_eq_iff_eq_mul.1 h3

end StandardPosition

section RootsOfA

open CFSG.LieType.Universal CFSG.LieType.RootSystem

private theorem toStd_add_of_sub {m : ℕ} (v w : Fin m → ℤ) :
    SpecialLinear.toStd m (v + w) = SpecialLinear.toStd m v + SpecialLinear.toStd m w := by
  have h := SpecialLinear.toStd_sub m v (-w)
  rwa [sub_neg_eq_add, SpecialLinear.toStd_neg, sub_neg_eq_add] at h

private theorem eq_or_eq_of_single_sub_add {m : ℕ} {i j k l p q : Fin (m + 1)} (hij : i ≠ j)
    (hkl : k ≠ l) (hpq : p ≠ q)
    (h : (Pi.single i 1 - Pi.single j 1 : Fin (m + 1) → ℤ) + (Pi.single k 1 - Pi.single l 1) =
      Pi.single p 1 - Pi.single q 1) :
    (j = k ∧ i ≠ l) ∨ (i = l ∧ k ≠ j) := by
  have hi := congrFun h i
  have hk := congrFun h k
  have hp := congrFun h p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply] at hi hk hp
  grind

theorem exists_distinct_of_roots_add_mem {m : ℕ} {β β' : Fin m → ℤ}
    (hβ : β ∈ roots (SpecialLinear.isFiniteType_A m) ∅)
    (hβ' : β' ∈ roots (SpecialLinear.isFiniteType_A m) ∅)
    (hs : β + β' ∈ roots (SpecialLinear.isFiniteType_A m) ∅) :
    ∃ a b c : Fin (m + 1), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ((SpecialLinear.toStd m β = Pi.single a 1 - Pi.single b 1 ∧
          SpecialLinear.toStd m β' = Pi.single b 1 - Pi.single c 1) ∨
        (SpecialLinear.toStd m β = Pi.single b 1 - Pi.single c 1 ∧
          SpecialLinear.toStd m β' = Pi.single a 1 - Pi.single b 1)) := by
  rw [SpecialLinear.roots_eq] at hβ hβ' hs
  obtain ⟨i, j, hij, h1⟩ := hβ
  obtain ⟨k, l, hkl, h2⟩ := hβ'
  obtain ⟨p, q, hpq, h3⟩ := hs
  rw [toStd_add_of_sub, h1, h2] at h3
  rcases eq_or_eq_of_single_sub_add hij hkl hpq h3 with ⟨rfl, hil⟩ | ⟨rfl, hkj⟩
  · exact ⟨i, j, l, hij, hkl, hil, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨k, i, j, hkl, hij, hkj, Or.inr ⟨h1, h2⟩⟩

end RootsOfA

end CFSG.StandardType.KGCentPSL

end
