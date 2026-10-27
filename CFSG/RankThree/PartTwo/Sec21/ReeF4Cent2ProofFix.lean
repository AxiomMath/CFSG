module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2ProofTorus
public import CFSG.RankThree.PartOne.SEITZQ1.Embed

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.SEITZQ1
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open scoped MatrixGroups

section Frames

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

omit [CharP L 2] in
theorem q1PsiRho_injective : Function.Injective (q1PsiRho F a) := by
  intro g h hgh
  apply q1Rho_injective
  rw [q1PsiRho_apply, q1PsiRho_apply, twistMap, twistMap, mul_left_inj, mul_right_inj,
    Fext_of_mem F (q1Rho_mem_adjoint g), Fext_of_mem F (q1Rho_mem_adjoint h)] at hgh
  exact congrArg Subtype.val (F.injective (Subtype.ext hgh))

theorem mem_center_of_q1Psi0_eq_one (hF : IsReeFrob a F) {g : SL(3, L)} (hg : q1Psi0 hF g = 1) :
    g ∈ Subgroup.center SL(3, L) := by
  rw [Subgroup.mem_center_iff]
  intro k
  apply q1Rho_injective
  have h1 : q1Rho L g = (q1PsiRho F a g)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← q1Psi0_apply]; exact hg)
  have h2 : Commute (q1Rho L k) (q1PsiRho F a g) := q1PsiRho_commute hF k g
  rw [map_mul, map_mul, h1]
  exact h2.inv_right.eq

variable [IsAlgClosed L]

theorem eq_of_q1Rho_eq_q1PsiRho (hF : IsReeFrob a F) {x y : SL(3, L)}
    (h : q1Rho L x = q1PsiRho F a y) : x = y ∧ x ∈ Subgroup.center SL(3, L) := by
  have hx : x ∈ Subgroup.center SL(3, L) := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply q1Rho_injective
    rw [map_mul, map_mul, h]
    exact q1PsiRho_commute hF k y
  have hy : y ∈ Subgroup.center SL(3, L) := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply q1PsiRho_injective
    rw [map_mul, map_mul, ← h]
    exact (q1PsiRho_commute hF x k).symm
  refine ⟨q1Rho_injective ?_, hx⟩
  rw [h]
  exact (q1Rho_eq_q1PsiRho_of_mem_center hF hy).symm

end Frames

section Theta

variable {L : Type} [Field L] [CharP L 2]

theorem three_dvd_two_pow_odd_add_one (a : ℕ) : 3 ∣ 2 ^ (2 * a + 1) + 1 := by
  have h : (2 ^ (2 * a + 1) + 1) % 3 = 0 := by
    rw [Nat.add_mod, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact Nat.dvd_of_mod_eq_zero h

omit [CharP L 2] in
theorem q1Tr_of_mem_center {a : ℕ} (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2 ^ (2 * a + 1))
    {z : SL(3, L)} (hz : z ∈ Subgroup.center SL(3, L)) : q1Tr Fr z = z := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr3
  have hq : Fr r * r = 1 := by
    obtain ⟨m, hm⟩ := three_dvd_two_pow_odd_add_one a
    rw [hFr, ← pow_succ, hm, pow_mul, hr3, one_pow]
  rw [q1Tr_apply, inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ← hr,
    Matrix.SpecialLinearGroup.coe_one, Matrix.scalar_apply, Matrix.diagonal_map (map_zero Fr),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  exact hq

end Theta

section Fixed

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
  {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

omit [CharP L 2] [IsAlgClosed L] in
theorem pow_three_of_mem_center {z : SL(3, L)} (hz : z ∈ Subgroup.center SL(3, L)) :
    z ^ 3 = 1 := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr3
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, ← map_pow, hr3, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem exists_q1Psi0_of_twist_fixed (hF : IsReeFrob a F) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ 2 ^ (2 * a + 1)) (g h : SL(3, L))
    (hfix : twistMap F (q1N L a) (q1Rho L g * q1PsiRho F a h) = q1Rho L g * q1PsiRho F a h) :
    ∃ g' : SL(3, L), q1Tr Fr g' = g' ∧ q1Rho L g * q1PsiRho F a h = q1Psi0 hF g' := by
  rw [twistMap_mul _ (q1Rho_mem_adjoint g) (q1PsiRho_mem_adjoint h), ← q1PsiRho_apply,
    q1Psi_psiRho hF Fr hFr h, (q1PsiRho_commute hF (q1Tr Fr h) g).symm] at hfix
  have h1 : q1Rho L (g⁻¹ * q1Tr Fr h) = q1PsiRho F a (h * g⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv]
    calc (q1Rho L g)⁻¹ * q1Rho L (q1Tr Fr h)
        = (q1Rho L g)⁻¹ * (q1Rho L (q1Tr Fr h) * q1PsiRho F a g) * (q1PsiRho F a g)⁻¹ := by
          group
      _ = (q1Rho L g)⁻¹ * (q1Rho L g * q1PsiRho F a h) * (q1PsiRho F a g)⁻¹ := by rw [hfix]
      _ = q1PsiRho F a h * (q1PsiRho F a g)⁻¹ := by group
  obtain ⟨hxy, hz⟩ := eq_of_q1Rho_eq_q1PsiRho hF h1
  set ζ := g⁻¹ * q1Tr Fr h with hζ
  have hcomm : ∀ k : SL(3, L), k * ζ = ζ * k := Subgroup.mem_center_iff.1 hz
  have hh : h = ζ * g := by
    rw [hxy]
    group
  have hθh : q1Tr Fr h = g * ζ := by
    rw [hζ]
    group
  have hθg : q1Tr Fr g = g := by
    have e : q1Tr Fr h = ζ * q1Tr Fr g := by
      conv_lhs => rw [hh]
      rw [map_mul, q1Tr_of_mem_center Fr hFr hz]
    rw [hθh, hcomm g] at e
    exact (mul_left_cancel e).symm
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_mem_center hz
  have hp : q1PsiRho F a ζ = q1Rho L ζ := (q1Rho_eq_q1PsiRho_of_mem_center hF hz).symm
  have hp3 : q1Rho L ζ ^ 3 = 1 := by rw [← map_pow, hζ3, map_one]
  have hpc : q1Rho L ζ * q1Rho L g = q1Rho L g * q1Rho L ζ := by
    rw [← map_mul, ← map_mul, hcomm g]
  refine ⟨ζ * ζ * g, ?_, ?_⟩
  · rw [map_mul, map_mul, q1Tr_of_mem_center Fr hFr hz, hθg]
  · have e4 : q1Rho L ζ * q1Rho L ζ * (q1Rho L ζ * q1Rho L ζ) = q1Rho L ζ := by
      have h3 := hp3
      rw [pow_three] at h3
      calc q1Rho L ζ * q1Rho L ζ * (q1Rho L ζ * q1Rho L ζ)
          = q1Rho L ζ * (q1Rho L ζ * q1Rho L ζ) * q1Rho L ζ := by simp only [mul_assoc]
        _ = q1Rho L ζ := by rw [h3, one_mul]
    rw [map_mul, map_mul, q1Psi0_apply hF ζ, q1Psi0_apply hF g, hp, hh, map_mul, hp, e4,
      ← mul_assoc, ← hpc, mul_assoc]

theorem q1Psi0_scalar (hF : IsReeFrob a F) {r : Lˣ} (hr : r ^ 3 = 1) :
    q1Psi0 hF (diag2 r r) = rootDiagUnit ReeTag.F4.tag (fun _ => r * r) := by
  rw [q1Psi0_apply, q1Rho_scalar hr, q1PsiRho_scalar hF hr, ← rootDiagUnit_mul]
  rfl

omit [CharP L 2] [IsAlgClosed L] in
theorem diag2_one : diag2 (1 : Lˣ) 1 = 1 := by
  apply Subtype.ext
  rw [coe_diag2, Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp

theorem q1Psi0_injective (hF : IsReeFrob a F) : Function.Injective (q1Psi0 hF) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨r, hr, rfl⟩ := eq_diag2_of_mem_center (mem_center_of_q1Psi0_eq_one hF hg)
  rw [q1Psi0_scalar hF hr] at hg
  have h1 : (fun _ : Fin ReeTag.F4.tag.rank => r * r) = 1 :=
    rootDiagUnit_injective (hg.trans rootDiagUnit_one.symm)
  have hr2 : r * r = 1 := congrFun h1 0
  have hr1 : r = 1 := by
    calc r = r ^ 3 * (r * r)⁻¹ := by group
      _ = 1 := by rw [hr, hr2, inv_one, one_mul]
  rw [hr1, diag2_one]

end Fixed

section Unitary

variable {f : ℕ} {K' : Type} [Field K'] {L : Type} [Field L]

theorem exists_eq_of_pow_card_eq [Finite K'] (ι : K' →+* L) {c : L}
    (hc : c ^ Nat.card K' = c) : ∃ x, ι x = c := by
  classical
  have := Fintype.ofFinite K'
  have hq : 1 < Fintype.card K' := Fintype.one_lt_card
  set P : Polynomial K' := Polynomial.X ^ Fintype.card K' - Polynomial.X with hP
  have hroots : P.roots = Finset.univ.val := FiniteField.roots_X_pow_card_sub_X K'
  have hdeg : P.natDegree = Fintype.card K' := FiniteField.X_pow_card_sub_X_natDegree_eq K' hq
  have hcard : Multiset.card P.roots = P.natDegree := by
    rw [hroots, hdeg, Finset.card_val, Finset.card_univ]
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree ι.injective hcard
  have hP0 : P.map ι ≠ 0 :=
    (Polynomial.map_ne_zero_iff ι.injective).2 (FiniteField.X_pow_card_sub_X_ne_zero K' hq)
  have hc' : c ∈ (P.map ι).roots := by
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, ← Nat.card_eq_fintype_card, hc, sub_self]
  rw [← hmap, hroots] at hc'
  obtain ⟨x, -, hx⟩ := Multiset.mem_map.1 hc'
  exact ⟨x, hx⟩

theorem exists_q1SUToSL_eq_of_fixed (h : UnitaryFieldData 2 f K') (ι : K' →+* L) (Fr : L →+* L)
    (hFr : ∀ c, Fr (ι c) = ι (h.bar c)) (hrange : ∀ c : L, Fr (Fr c) = c → ∃ x, ι x = c)
    {g : SL(3, L)} (hg : q1Tr Fr g = g) : ∃ u : unitarySU 2 f K' 3, q1SUToSL h ι u = g := by
  classical
  set M : Matrix (Fin 3) (Fin 3) L := (g : Matrix (Fin 3) (Fin 3) L) with hM
  have hu : (M.map Fr)ᵀ * M = 1 := by
    rw [q1Tr_apply, inv_eq_iff_mul_eq_one] at hg
    have := congrArg (fun A : SL(3, L) => (A : Matrix (Fin 3) (Fin 3) L)) hg
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.map_apply_coe] using this
  have hu2 : (M.map Fr)ᵀ * M.map (Fr.comp Fr) = 1 := by
    have h2 := congrArg (fun A => A.map Fr) hu
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one _ (map_zero Fr) (map_one Fr),
      Matrix.map_map] at h2
    have h3 := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h3
    simpa [Matrix.transpose_map, Function.comp_def] using h3
  have hfix : M.map (Fr.comp Fr) = M := (Matrix.right_inv_eq_right_inv hu hu2).symm
  have hent : ∀ i j, ∃ x, ι x = M i j := fun i j =>
    hrange (M i j) (by simpa using congrFun (congrFun hfix i) j)
  choose X hX using hent
  set U : Matrix (Fin 3) (Fin 3) K' := Matrix.of X with hU
  have hUM : U.map ι = M := by
    ext i j
    exact hX i j
  have hdet : U.det = 1 := by
    apply ι.injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hUM, map_one]
    exact g.2
  have hunit : (U.map h.bar)ᵀ * U = 1 := by
    apply Matrix.map_injective ι.injective
    show ((U.map h.bar)ᵀ * U).map ι = (1 : Matrix (Fin 3) (Fin 3) K').map ι
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ ι.map_zero ι.map_one,
      hUM]
    have e : (U.map (⇑ι ∘ ⇑h.bar)) = M.map Fr := by
      rw [← hUM, Matrix.map_map]
      congr 1
      funext c
      exact (hFr c).symm
    rw [e]
    exact hu
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL ⟨U, hdet⟩, (mem_unitarySU_iff h).2 ⟨hdet, hunit⟩⟩, ?_⟩
  apply Subtype.ext
  rw [coe_q1SUToSL]
  exact hUM

end Unitary

end CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof
