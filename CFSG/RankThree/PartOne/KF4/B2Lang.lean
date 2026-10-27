module

public import CFSG.RankThree.PartOne.KF4.B2SpFacts
public import CFSG.RankThree.PartOne.KF4.B2Twist
public import CFSG.RankThree.PartOne.KF4.B2Frame
public import CFSG.RankThree.SteinbergR3ESymplecticFrobeniusLang
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

section Matrices

variable {K L : Type} [Field K] [Field L]

theorem f4B2J0_map (f : K →+* L) : (f4B2J0 K).map f = f4B2J0 L := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f4B2J0]

@[expose] def f4B2J0GL (K : Type) [Field K] : GL (Fin 4) K :=
  ⟨f4B2J0 K, -f4B2J0 K, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [f4B2J0, Matrix.mul_apply, Fin.sum_univ_four], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [f4B2J0, Matrix.mul_apply, Fin.sum_univ_four]⟩

theorem map_mem_f4SpGroup (f : K →+* L) {Y : GL (Fin 4) K} (hY : Y ∈ f4SpGroup K) :
    GeneralLinearGroup.map f Y ∈ f4SpGroup L := by
  rw [mem_f4SpGroup] at hY ⊢
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map f) hY
  simp only [Matrix.map_mul, Matrix.transpose_map, f4B2J0_map] at h
  exact h

end Matrices

section Lang

variable {k L : Type} [Field k] [Finite k] [Field L] [Algebra k L] [IsAlgClosure k L]

omit [Finite k] [IsAlgClosure k L] in
theorem mem_matrixIsometryGroup_f4B2J0 (M : GL (Fin 4) L) :
    M ∈ matrixIsometryGroup (((f4B2J0GL k : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k).map
      (algebraMap k L)) ↔ M ∈ f4SpGroup L := by
  rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical.mem_matrixIsometryGroup,
    mem_f4SpGroup]
  rw [show ((f4B2J0GL k : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) = f4B2J0 k from rfl,
    f4B2J0_map]

theorem f4B2_lang (A : GL (Fin 4) L) (hA : A ∈ f4SpGroup L) :
    ∃ P ∈ f4SpGroup L, ∀ X : GL (Fin 4) L,
      (X ∈ f4SpGroup L ∧ (A : Matrix (Fin 4) (Fin 4) L) *
          (X : Matrix (Fin 4) (Fin 4) L).map (· ^ Nat.card k) *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) L) = X) ↔
        ∃ Y ∈ f4SpGroup k, X = P * GeneralLinearGroup.map (algebraMap k L) Y * P⁻¹ := by
  have hdiag : ∀ j : Fin 4, ((f4B2J0GL k : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) j j = 0 := by
    intro j
    fin_cases j <;> simp [f4B2J0GL, f4B2J0]
  have hskew : ∀ j l : Fin 4, ((f4B2J0GL k : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) l j =
      -((f4B2J0GL k : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) j l := by
    intro j l
    fin_cases j <;> fin_cases l <;> simp [f4B2J0GL, f4B2J0]
  obtain ⟨P, hP, -, hset, -⟩ :=
    CFSG.RankThree.SymplecticLang.symplectic_matrix_frobenius_lang_and_exact_fixed_group
      (K := k) (Ω := L) (n := 2) (by norm_num) (f4B2J0GL k) hdiag hskew A
      ((mem_matrixIsometryGroup_f4B2J0 A).2 hA)
  refine ⟨P, (mem_matrixIsometryGroup_f4B2J0 P).1 hP, fun X => ?_⟩
  have h := Set.ext_iff.1 hset X
  simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe] at h
  constructor
  · rintro ⟨hX, hfix⟩
    obtain ⟨Y, hY, hYX⟩ := h.1 ⟨(mem_matrixIsometryGroup_f4B2J0 X).2 hX, hfix⟩
    exact ⟨Y, hY, hYX.symm⟩
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨hX, hfix⟩ := h.2 ⟨Y, hY, rfl⟩
    exact ⟨(mem_matrixIsometryGroup_f4B2J0 _).1 hX, hfix⟩


theorem f4B2_fixed_iff {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k) (n A : ModGL Tag.F4 L)
    (hA : A ∈ subsystemGroup Tag.F4 L f4B2Support)
    (htw : ∀ g ∈ subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) g * n⁻¹ = A * Units.map (entrywiseHom Fr) g * A⁻¹) :
    ∃ P ∈ f4SpGroup L, ∀ g : subsystemGroup Tag.F4 L f4B2Support,
      (n * Units.map (entrywiseHom Fr) (g : ModGL Tag.F4 L) * n⁻¹ = g ↔
        ∃ Y ∈ f4SpGroup k, ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L) =
          P * GeneralLinearGroup.map (algebraMap k L) Y * P⁻¹) := by
  obtain ⟨P, hP, hiff⟩ := f4B2_lang (k := k) ((f4B2Equiv L ⟨A, hA⟩ : f4SpGroup L) : GL (Fin 4) L)
    (f4B2Equiv L ⟨A, hA⟩).2
  refine ⟨P, hP, fun g => ?_⟩
  set Ā : f4SpGroup L := f4B2Equiv L ⟨A, hA⟩ with hĀ
  set Φg : subsystemGroup Tag.F4 L f4B2Support :=
    ⟨baseChangeGL Fr (g : ModGL Tag.F4 L), baseChangeGL_mem_subsystemGroup Fr g.2⟩ with hΦg
  have hΦ : Units.map (entrywiseHom Fr) (g : ModGL Tag.F4 L) =
      baseChangeGL Fr (g : ModGL Tag.F4 L) :=
    units_map_entrywiseHom_eq_baseChangeGL_self Fr _
  have hmat : (((f4B2Equiv L Φg : f4SpGroup L) : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) =
      ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L).val.map (· ^ Nat.card k) := by
    have h := f4B2Equiv_baseChangeGL Fr g
    have e : (fun c : L => c ^ Nat.card k) = Fr := funext fun c => (hFr c).symm
    rw [e]
    exact h
  have key : (n * Units.map (entrywiseHom Fr) (g : ModGL Tag.F4 L) * n⁻¹ = g) ↔
      ((Ā : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) *
          ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L).val.map (· ^ Nat.card k) *
            (↑((Ā : GL (Fin 4) L)⁻¹) : Matrix (Fin 4) (Fin 4) L) =
        ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L) := by
    rw [htw g g.2, hΦ]
    have e1 : (A * baseChangeGL Fr (g : ModGL Tag.F4 L) * A⁻¹ = (g : ModGL Tag.F4 L)) ↔
        (⟨A, hA⟩ * Φg * ⟨A, hA⟩⁻¹ : subsystemGroup Tag.F4 L f4B2Support) = g := by
      rw [Subtype.ext_iff]
      rfl
    rw [e1, ← (f4B2Equiv L).injective.eq_iff, map_mul, map_mul, map_inv, Subtype.ext_iff,
      Units.ext_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hmat]
    exact Iff.rfl
  exact key.trans (((and_iff_right (f4B2Equiv L g).2).symm).trans (hiff _))

omit [Finite k] [IsAlgClosure k L]
  in
theorem map_injective_GL (Y₁ Y₂ : GL (Fin 4) k)
    (h : GeneralLinearGroup.map (algebraMap k L) Y₁ = GeneralLinearGroup.map (algebraMap k L) Y₂) :
    Y₁ = Y₂ := by
  apply Units.ext
  have := congrArg (fun Z : GL (Fin 4) L => (Z : Matrix (Fin 4) (Fin 4) L)) h
  exact Matrix.map_injective (algebraMap k L).injective this

@[expose] def f4B2Lift (P : GL (Fin 4) L) (hP : P ∈ f4SpGroup L) : f4SpGroup k →* f4SpGroup L where
  toFun Y := ⟨P * GeneralLinearGroup.map (algebraMap k L) Y.1 * P⁻¹,
    mul_mem (mul_mem hP (map_mem_f4SpGroup _ Y.2)) (inv_mem hP)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' Y Z := by
    apply Subtype.ext
    change P * GeneralLinearGroup.map (algebraMap k L) (Y.1 * Z.1) * P⁻¹ =
      (P * GeneralLinearGroup.map (algebraMap k L) Y.1 * P⁻¹) *
        (P * GeneralLinearGroup.map (algebraMap k L) Z.1 * P⁻¹)
    rw [map_mul]
    group

omit [Finite k] [IsAlgClosure k L]
  in
theorem f4B2Lift_injective (P : GL (Fin 4) L) (hP : P ∈ f4SpGroup L) :
    Function.Injective (f4B2Lift (k := k) P hP) := by
  intro Y Z h
  have h1 := congrArg Subtype.val h
  change P * GeneralLinearGroup.map (algebraMap k L) Y.1 * P⁻¹ =
    P * GeneralLinearGroup.map (algebraMap k L) Z.1 * P⁻¹ at h1
  exact Subtype.ext (map_injective_GL (L := L) _ _ (by simpa using h1))

theorem f4B2_fixed_equiv {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k) (n A : ModGL Tag.F4 L)
    (hA : A ∈ subsystemGroup Tag.F4 L f4B2Support)
    (htw : ∀ g ∈ subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) g * n⁻¹ = A * Units.map (entrywiseHom Fr) g * A⁻¹) :
    Nonempty (f4SpGroup k ≃*
      ↥(subsystemGroup Tag.F4 L f4B2Support ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)))) := by
  obtain ⟨P, hP, hiff⟩ := f4B2_fixed_iff (k := k) hFr n A hA htw
  let ψ1 : f4SpGroup k →* subsystemGroup Tag.F4 L f4B2Support :=
    (f4B2Equiv L).symm.toMonoidHom.comp (f4B2Lift P hP)
  have hψ1 : ∀ Y : f4SpGroup k, (ψ1 Y : ModGL Tag.F4 L) ∈ subsystemGroup Tag.F4 L f4B2Support ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
    intro Y
    refine Subgroup.mem_inf.2 ⟨(ψ1 Y).2, ?_⟩
    rw [mem_twistedFixedPoints]
    exact (hiff (ψ1 Y)).2 ⟨Y.1, Y.2, by simp [ψ1, f4B2Lift]⟩
  let Ψ : f4SpGroup k →* ↥(subsystemGroup Tag.F4 L f4B2Support ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr))) :=
    ((subsystemGroup Tag.F4 L f4B2Support).subtype.comp ψ1).codRestrict _ hψ1
  refine ⟨MulEquiv.ofBijective Ψ ⟨?_, ?_⟩⟩
  · intro Y Z h
    have h1 : ψ1 Y = ψ1 Z := Subtype.ext (congrArg (fun x : ↥(subsystemGroup Tag.F4 L f4B2Support ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr))) => (x : ModGL Tag.F4 L)) h)
    exact f4B2Lift_injective P hP ((f4B2Equiv L).symm.injective h1)
  · rintro ⟨z, hzG, hzR⟩
    obtain ⟨Y, hY, hYe⟩ := (hiff ⟨z, hzG⟩).1 (mem_twistedFixedPoints.1 hzR)
    refine ⟨⟨Y, hY⟩, Subtype.ext ?_⟩
    change ((f4B2Equiv L).symm (f4B2Lift P hP ⟨Y, hY⟩) : ModGL Tag.F4 L) = z
    have : f4B2Lift P hP ⟨Y, hY⟩ = f4B2Equiv L ⟨z, hzG⟩ := Subtype.ext (by
      change P * GeneralLinearGroup.map (algebraMap k L) Y * P⁻¹ = _
      exact hYe.symm)
    rw [this, MulEquiv.symm_apply_apply]

theorem conj_comm_aux (M Ym Pm Pi : Matrix (Fin 4) (Fin 4) L) (hPP : Pi * Pm = 1)
    (h : M * (Pm * Ym * Pi) = (Pm * Ym * Pi) * M) : Pi * M * Pm * Ym = Ym * (Pi * M * Pm) := by
  calc Pi * M * Pm * Ym
      = Pi * M * (Pm * Ym * (Pi * Pm)) := by rw [hPP, Matrix.mul_one, Matrix.mul_assoc]
    _ = Pi * (M * (Pm * Ym * Pi)) * Pm := by simp only [Matrix.mul_assoc]
    _ = Pi * ((Pm * Ym * Pi) * M) * Pm := by rw [h]
    _ = (Pi * Pm) * Ym * (Pi * M * Pm) := by simp only [Matrix.mul_assoc]
    _ = Ym * (Pi * M * Pm) := by rw [hPP, Matrix.one_mul]

theorem f4B2_commutant {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k) (n A : ModGL Tag.F4 L)
    (hA : A ∈ subsystemGroup Tag.F4 L f4B2Support)
    (htw : ∀ g ∈ subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) g * n⁻¹ = A * Units.map (entrywiseHom Fr) g * A⁻¹)
    (M : Matrix (Fin 4) (Fin 4) L)
    (hM : ∀ g : subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) (g : ModGL Tag.F4 L) * n⁻¹ = g →
        M * ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L).val =
          ((f4B2Equiv L g : f4SpGroup L) : GL (Fin 4) L).val * M) :
    ∃ c : L, M = c • (1 : Matrix (Fin 4) (Fin 4) L) := by
  obtain ⟨P, hP, hiff⟩ := f4B2_fixed_iff (k := k) hFr n A hA htw
  have hPP : (P⁻¹ : GL (Fin 4) L).val * P.val = 1 := Units.inv_mul P
  have hPP' : P.val * (P⁻¹ : GL (Fin 4) L).val = 1 := Units.mul_inv P
  obtain ⟨c, hc⟩ := scalar_of_commutes_f4SpGroup (K := k) (L := L)
    ((P⁻¹ : GL (Fin 4) L).val * M * P.val) (fun Y hY => by
      set X : f4SpGroup L := ⟨P * GeneralLinearGroup.map (algebraMap k L) Y * P⁻¹,
        mul_mem (mul_mem hP (map_mem_f4SpGroup _ hY)) (inv_mem hP)⟩ with hX
      set g : subsystemGroup Tag.F4 L f4B2Support := (f4B2Equiv L).symm X with hg
      have hge : f4B2Equiv L g = X := MulEquiv.apply_symm_apply _ _
      have hfix := (hiff g).2 ⟨Y, hY, by rw [hge]⟩
      have h := hM g hfix
      rw [hge] at h
      have hXv : ((X : f4SpGroup L) : GL (Fin 4) L).val = P.val *
          (Y : Matrix (Fin 4) (Fin 4) k).map (algebraMap k L) * (P⁻¹ : GL (Fin 4) L).val := rfl
      rw [hXv] at h
      exact conj_comm_aux M _ _ _ hPP h)
  refine ⟨c, ?_⟩
  have e1 : P.val * ((P⁻¹ : GL (Fin 4) L).val * M * P.val) * (P⁻¹ : GL (Fin 4) L).val =
      (P.val * (P⁻¹ : GL (Fin 4) L).val) * M * (P.val * (P⁻¹ : GL (Fin 4) L).val) := by
    simp only [Matrix.mul_assoc]
  calc M = P.val * ((P⁻¹ : GL (Fin 4) L).val * M * P.val) * (P⁻¹ : GL (Fin 4) L).val := by
        rw [e1, hPP', Matrix.one_mul, Matrix.mul_one]
    _ = c • (1 : Matrix (Fin 4) (Fin 4) L) := by
        rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP']

theorem simpleRootSL2_mem_f4B2 {K : Type} [Field K] {i : Fin Tag.F4.rank}
    (hi : i ∈ f4B2Support) (Y : SL2 K) :
    simpleRootSL2 Tag.F4 K i Y ∈ subsystemGroup Tag.F4 K f4B2Support := by
  have hY : Y ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  induction hY using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change simpleRootSL2 Tag.F4 K i (uSL c) ∈ _
      rw [simpleRootSL2_uSL]
      exact xUnit_mem_subsystemGroup hi c
    · change simpleRootSL2 Tag.F4 K i (vSL c) ∈ _
      rw [simpleRootSL2_vSL]
      exact yUnit_mem_subsystemGroup hi c
  | one =>
    rw [map_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [map_inv]
    exact inv_mem hx

theorem f4B2_sl2_mem {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card k) (n A : ModGL Tag.F4 L)
    (hA : A ∈ subsystemGroup Tag.F4 L f4B2Support)
    (htw : ∀ g ∈ subsystemGroup Tag.F4 L f4B2Support,
      n * Units.map (entrywiseHom Fr) g * n⁻¹ = A * Units.map (entrywiseHom Fr) g * A⁻¹) :
    ∃ h₀ ∈ subsystemGroup Tag.F4 L f4B2Support, ∀ Y : SL2 k,
      h₀ * simpleRootSL2 Tag.F4 L (f4Index 1) (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
        h₀⁻¹ ∈ subsystemGroup Tag.F4 L f4B2Support ⊓
          twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  obtain ⟨P, hP, hiff⟩ := f4B2_fixed_iff (k := k) hFr n A hA htw
  have hi1 : f4Index 1 ∈ f4B2Support := (mem_f4B2Support _).2 (Or.inl rfl)
  set h₀g : subsystemGroup Tag.F4 L f4B2Support := (f4B2Equiv L).symm ⟨P, hP⟩ with hh₀g
  refine ⟨h₀g.1, h₀g.2, fun Y => ?_⟩
  set gk : subsystemGroup Tag.F4 k f4B2Support :=
    ⟨simpleRootSL2 Tag.F4 k (f4Index 1) Y, simpleRootSL2_mem_f4B2 hi1 Y⟩ with hgk
  set gL : subsystemGroup Tag.F4 L f4B2Support :=
    ⟨baseChangeGL (algebraMap k L) (gk : ModGL Tag.F4 k),
      baseChangeGL_mem_subsystemGroup _ gk.2⟩ with hgL
  have hgLe : ((f4B2Equiv L gL : f4SpGroup L) : GL (Fin 4) L) =
      GeneralLinearGroup.map (algebraMap k L) ((f4B2Equiv k gk : f4SpGroup k) : GL (Fin 4) k) :=
    Units.ext (f4B2Equiv_baseChangeGL (algebraMap k L) gk)
  have hρ : (gL : ModGL Tag.F4 L) = simpleRootSL2 Tag.F4 L (f4Index 1)
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) :=
    baseChangeGL_simpleRootSL2_of_field (algebraMap k L) (f4Index 1) Y
  set z : subsystemGroup Tag.F4 L f4B2Support := h₀g * gL * h₀g⁻¹ with hz
  have hzmem : (z : ModGL Tag.F4 L) = h₀g.1 * simpleRootSL2 Tag.F4 L (f4Index 1)
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀g.1⁻¹ := by
    rw [← hρ]
    rfl
  refine Subgroup.mem_inf.2 ⟨hzmem ▸ z.2, ?_⟩
  rw [← hzmem, mem_twistedFixedPoints]
  refine (hiff z).2 ⟨((f4B2Equiv k gk : f4SpGroup k) : GL (Fin 4) k), (f4B2Equiv k gk).2, ?_⟩
  rw [hz, map_mul, map_mul, map_inv, hh₀g, MulEquiv.apply_symm_apply]
  change P * ((f4B2Equiv L gL : f4SpGroup L) : GL (Fin 4) L) * P⁻¹ = _
  rw [hgLe]

end Lang

end CFSG.RankThree.PartOne.KF4
