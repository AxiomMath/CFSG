module

public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KE.CTRational

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section Neg

variable {τ : Tag} {L : Type} [Field L]

theorem exists_rootSL2_neg_eq {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ a : Lˣ, ∀ A : SL2 L, rootSL2 τ L (-β) A =
      rootSL2 τ L β (conjSL (swapGL * diagUnitOne a) A) := by
  classical
  have hβ' : IsRoot τ (-β) := IsRoot.neg hβ
  have hinj := rootSL2_injective_of_field (τ := τ) (K := L) β
  have hR : (rootSL2 τ L (-β)).range = (rootSL2 τ L β).range := by
    rw [range_rootSL2_of_isRoot hβ', range_rootSL2_of_isRoot hβ, neg_neg, sup_comm]
  have hrange : ∀ A : SL2 L, rootSL2 τ L (-β) A ∈ (rootSL2 τ L β).range := fun A =>
    hR ▸ ⟨A, rfl⟩
  let T : SL2 L →* SL2 L := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    ((rootSL2 τ L (-β)).codRestrict _ hrange)
  have hT : ∀ A, rootSL2 τ L β (T A) = rootSL2 τ L (-β) A := fun A => by
    have := (MonoidHom.ofInjective hinj).apply_symm_apply ⟨rootSL2 τ L (-β) A, hrange A⟩
    exact congrArg Subtype.val this
  obtain ⟨u₁, hu₁, h₁⟩ := exists_unit_zsmul_eq_mul (K := L) (pinnedSign_eq τ (-β))
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  obtain ⟨ε₃, hε₃, h₃⟩ := exists_rootSL2_vSL_eq (K := L) hβ'
  obtain ⟨u₄, hu₄, h₄⟩ := exists_unit_zsmul_eq_mul (K := L) (pinnedSign_eq τ β)
  let a : Lˣ := Units.mkOfMulEqOne ε₂ ε₂ hε₂ * u₁
  let b : Lˣ := u₄ * Units.mkOfMulEqOne ε₃ ε₃ hε₃
  have hu : ∀ c, T (sl2Upper L c) = sl2Lower L ((a : L) * (RingEquiv.refl L) c) := by
    intro c
    apply hinj
    rw [hT]
    change rootSL2 τ L (-β) (uSL c) = rootSL2 τ L β (vSL _)
    rw [rootSL2_uSL_eq, h₂, h₁]
    congr 1
    simp only [a, Units.val_mul, Units.val_mkOfMulEqOne, RingEquiv.refl_apply]
    linear_combination (-((u₁ : L) * c)) * hε₂
  have hl : ∀ c, T (sl2Lower L c) = sl2Upper L ((b : L) * (RingEquiv.refl L) c) := by
    intro c
    apply hinj
    rw [hT]
    change rootSL2 τ L (-β) (vSL c) = rootSL2 τ L β (uSL _)
    rw [h₃, rootSL2_uSL_eq, h₄, neg_neg]
    congr 1
    have hu₄' : (u₄ : L) * u₄ = 1 := by rw [← Units.val_mul, hu₄, Units.val_one]
    simp only [b, Units.val_mul, Units.val_mkOfMulEqOne, RingEquiv.refl_apply]
    linear_combination (-(ε₃ * c)) * hu₄'
  obtain ⟨-, M, hM, hTM⟩ := sl2_semilinear_exchanged_root_compatibility (RingEquiv.refl L) a b T
    hu hl
  refine ⟨a, fun A => ?_⟩
  rw [← hT]
  congr 1
  apply Subtype.ext
  rw [hTM A, coe_conjSL]
  have hMe : M = swapGL * diagUnitOne a := Units.ext (by rw [hM, coe_swapGL_mul_diagUnitOne])
  rw [hMe]
  simp

end Neg

section Twist

variable {L : Type} [Field L]

theorem zsmul_zsmul_sign {ε : ℤ} (h : ε = 1 ∨ ε = -1) (x : L) : ε • ε • x = x := by
  rcases h with rfl | rfl <;> simp

theorem exists_conj_rootSL2_eq_twist {t : TwistTag} {n : ModGL t.tag L}
    (hn : n ∈ monomialSubgroup t.tag L) {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    ∃ s : Lˣ, ∀ A : SL2 L, n * diagramMap t L * rootSL2 t.tag L β A * (n * diagramMap t L)⁻¹ =
      rootSL2 t.tag L (weylQuotientHom t.tag L ⟨n, hn⟩ • permLattice t.perm β)
        (conjSL (diagUnitOne s) A) := by
  classical
  set m : ModGL t.tag L := n * diagramMap t L with hm
  set w := weylQuotientHom t.tag L ⟨n, hn⟩ with hw
  set γ := w • permLattice t.perm β with hγ
  have hρβ : IsRoot t.tag (permLattice t.perm β) := hβ.permLattice t.cartan_perm
  have hγroot : IsRoot t.tag γ := IsRoot.smul hρβ w
  have hX : ∀ α : Fin t.tag.rank → ℤ, IsRoot t.tag α → ∃ μ : Lˣ, ∀ c : L,
      m * pinnedX t.tag L α c * m⁻¹ = pinnedX t.tag L (w • permLattice t.perm α) (μ * c) := by
    intro α hα
    obtain ⟨e, he, hPX⟩ := diagramMap_conj_pinnedX (K := L) t hα
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn (hα.permLattice t.cartan_perm)
    refine ⟨μ * Units.mkOfMulEqOne e e he, fun c => ?_⟩
    calc m * pinnedX t.tag L α c * m⁻¹ =
          n * (diagramMap t L * pinnedX t.tag L α c * (diagramMap t L)⁻¹) * n⁻¹ := by
          simp only [hm]
          group
      _ = n * pinnedX t.tag L (permLattice t.perm α) (e * c) * n⁻¹ := by rw [hPX]
      _ = _ := by
          rw [hμ]
          simp only [Units.val_mul, Units.val_mkOfMulEqOne, mul_assoc]
          rfl
  have hinj := rootSL2_injective_of_field (τ := t.tag) (K := L) γ
  let Ψ : SL2 L →* ModGL t.tag L := (MulAut.conj m).toMonoidHom.comp (rootSL2 t.tag L β)
  obtain ⟨uβ, huβ, hεβ⟩ := exists_unit_zsmul_eq_mul (K := L) (pinnedSign_eq t.tag β)
  obtain ⟨uγ, huγ, hεγ⟩ := exists_unit_zsmul_eq_mul (K := L) (pinnedSign_eq t.tag γ)
  obtain ⟨εβ, hεβ', hvβ⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  obtain ⟨εγ, hεγ', hvγ⟩ := exists_rootSL2_vSL_eq (K := L) hγroot
  obtain ⟨μ₁, hμ₁⟩ := hX β hβ
  obtain ⟨μ₂, hμ₂⟩ := hX (-β) (IsRoot.neg hβ)
  have hneg : w • permLattice t.perm (-β) = -γ := by
    rw [hγ, permLattice_neg, smul_neg]
  rw [hneg] at hμ₂
  have huγ' : (uγ : L) * uγ = 1 := by rw [← Units.val_mul, huγ, Units.val_one]
  have hεγ'' : (εγ : L) * εγ = 1 := hεγ'
  let a : Lˣ := uγ⁻¹ * μ₁ * uβ
  let b : Lˣ := Units.mkOfMulEqOne εγ εγ hεγ' * μ₂ * Units.mkOfMulEqOne εβ εβ hεβ'
  have hΨu : ∀ c, Ψ (uSL c) = rootSL2 t.tag L γ (uSL ((a : L) * c)) := by
    intro c
    change m * rootSL2 t.tag L β (uSL c) * m⁻¹ = _
    rw [rootSL2_uSL_eq, hεβ, hμ₁, rootSL2_uSL_eq, hεγ]
    congr 1
    simp only [a, Units.val_mul, Units.val_inv_eq_inv_val]
    have : (uγ : L) ≠ 0 := uγ.ne_zero
    field_simp
  have hΨv : ∀ c, Ψ (vSL c) = rootSL2 t.tag L γ (vSL ((b : L) * c)) := by
    intro c
    change m * rootSL2 t.tag L β (vSL c) * m⁻¹ = _
    rw [hvβ, hμ₂, hvγ]
    congr 1
    simp only [b, Units.val_mul, Units.val_mkOfMulEqOne]
    linear_combination (-(μ₂ * (εβ * c))) * hεγ''
  have hrange : ∀ A : SL2 L, Ψ A ∈ (rootSL2 t.tag L γ).range := by
    intro A
    have hle : (⊤ : Subgroup (SL2 L)) ≤ (rootSL2 t.tag L γ).range.comap Ψ := by
      rw [← sl2_closure_upper_lower (K := L)]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨uSL ((a : L) * c), (hΨu c).symm⟩
      · exact ⟨vSL ((b : L) * c), (hΨv c).symm⟩
    exact hle (Subgroup.mem_top A)
  let T : SL2 L →* SL2 L := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    (Ψ.codRestrict _ hrange)
  have hT : ∀ A, rootSL2 t.tag L γ (T A) = Ψ A := fun A => by
    have := (MonoidHom.ofInjective hinj).apply_symm_apply ⟨Ψ A, hrange A⟩
    exact congrArg Subtype.val this
  have hu : ∀ c, T (sl2Upper L c) = sl2Upper L ((a : L) * (RingEquiv.refl L) c) := fun c =>
    hinj (by rw [hT]; exact hΨu c)
  have hl : ∀ c, T (sl2Lower L c) = sl2Lower L ((b : L) * (RingEquiv.refl L) c) := fun c =>
    hinj (by rw [hT]; exact hΨv c)
  obtain ⟨-, M, hM, hTM⟩ := sl2_semilinear_root_compatibility (RingEquiv.refl L) a b T hu hl
  refine ⟨a, fun A => ?_⟩
  have hMe : M = diagUnitOne a := Units.ext (by rw [hM, coe_diagUnitOne])
  have : T A = conjSL (diagUnitOne a) A := by
    apply Subtype.ext
    rw [hTM A, coe_conjSL, hMe]
    simp
  show Ψ A = _
  rw [← hT, this]

end Twist

section Lang

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L]

theorem exists_twist_antidiag (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (x y : Lˣ)
    (M : GL (Fin 2) L) (hM : (M : Matrix (Fin 2) (Fin 2) L) = !![0, (x : L); (y : L), 0]) :
    ∃ P : GL (Fin 2) L, P * GeneralLinearGroup.map Fr P⁻¹ = M := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hqL : (q : L) = 0 := by
    have h := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card] at h
    have h2 := congrArg (algebraMap K L) h
    rwa [map_natCast, map_zero] at h2
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  have hqpos : 0 < q ^ 2 - 1 := by omega
  have hq2L : ((q ^ 2 - 1 : ℕ) : L) ≠ 0 := by
    rw [Nat.cast_sub hq1]
    push_cast
    rw [hqL]
    simp
  have hc₁ : ((x : L) * (y : L) ^ q)⁻¹ * ((x : L) * (y : L) ^ q) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero x.ne_zero (pow_ne_zero _ y.ne_zero))
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq (((x : L) * (y : L) ^ q)⁻¹) hqpos
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_pow hqpos.ne'] at hp
    exact inv_ne_zero (mul_ne_zero x.ne_zero (pow_ne_zero _ y.ne_zero)) hp.symm
  have hpq2 : p ^ (q ^ 2) * ((x : L) * (y : L) ^ q) = p := by
    have h : q ^ 2 = (q ^ 2 - 1) + 1 := by omega
    rw [h, pow_succ, hp]
    calc ((x : L) * (y : L) ^ q)⁻¹ * p * ((x : L) * (y : L) ^ q)
        = (((x : L) * (y : L) ^ q)⁻¹ * ((x : L) * (y : L) ^ q)) * p := by ring
      _ = p := by rw [hc₁, one_mul]
  have : NeZero ((q ^ 2 - 1 : ℕ) : L) := ⟨hq2L⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (q ^ 2 - 1)
  have hμ0 : μ ≠ 0 := hμ.ne_zero hqpos.ne'
  have hμq2 : μ ^ (q ^ 2) = μ := by
    have h : q ^ 2 = (q ^ 2 - 1) + 1 := by omega
    rw [h, pow_succ, hμ.pow_eq_one, one_mul]
  have hμq : μ ^ q ≠ μ := by
    intro h
    have h1 : μ ^ (q - 1) = 1 := by
      have h2 : μ ^ q = μ ^ (q - 1) * μ := by
        rw [← pow_succ]
        congr 1
        omega
      rw [h2] at h
      exact (mul_eq_right₀ hμ0).1 h
    have h3 := hμ.dvd_of_pow_eq_one _ h1
    have h4 := Nat.le_of_dvd (by omega) h3
    have h5 : q < q ^ 2 := by nlinarith
    omega
  have hdet : (!![p, μ * p; (y : L) * p ^ q, (y : L) * (μ * p) ^ q] : Matrix (Fin 2) (Fin 2) L).det
      ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    have h : p * ((y : L) * (μ * p) ^ q) - μ * p * ((y : L) * p ^ q) =
        (y : L) * p ^ (q + 1) * (μ ^ q - μ) := by
      rw [mul_pow, pow_succ]
      ring
    rw [h]
    exact mul_ne_zero (mul_ne_zero y.ne_zero (pow_ne_zero _ hp0)) (sub_ne_zero.2 hμq)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
  rw [map_inv, mul_inv_eq_iff_eq_mul]
  have hmapP : ((GeneralLinearGroup.map Fr (GeneralLinearGroup.mkOfDetNeZero _ hdet) :
      GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![p ^ q, (μ * p) ^ q; ((y : L) * p ^ q) ^ q, ((y : L) * (μ * p) ^ q) ^ q] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.mkOfDetNeZero, GeneralLinearGroup.map, hFr]
  have e1 : p = (x : L) * ((y : L) * p ^ q) ^ q := by
    rw [mul_pow, ← pow_mul]
    calc p = p ^ (q ^ 2) * ((x : L) * (y : L) ^ q) := hpq2.symm
      _ = _ := by rw [sq]; ring
  have h1 : ((y : L) * (μ * p) ^ q) ^ q = (y : L) ^ q * (μ ^ (q ^ 2) * p ^ (q ^ 2)) := by ring
  have e2 : μ * p = (x : L) * ((y : L) * (μ * p) ^ q) ^ q := by
    calc μ * p = μ * (p ^ (q ^ 2) * ((x : L) * (y : L) ^ q)) := by rw [hpq2]
      _ = (x : L) * ((y : L) ^ q * (μ ^ (q ^ 2) * p ^ (q ^ 2))) := by rw [hμq2]; ring
      _ = (x : L) * ((y : L) * (μ * p) ^ q) ^ q := by rw [h1]
  apply Units.ext
  rw [Units.val_mul, hmapP, hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | exact e1 | exact e2

end Lang

end CFSG.RankThree.PartOne.KGD
