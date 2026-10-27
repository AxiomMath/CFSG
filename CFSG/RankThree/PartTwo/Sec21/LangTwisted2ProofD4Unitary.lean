module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Frob

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix Polynomial
open CFSG.Assembly.RankThreeEven (projImage)
open scoped MatrixGroups

variable {L : Type} [Field L] [CharP L 2]

theorem mem_range_of_pow_card_eq {K' : Type} [Field K'] [Fintype K'] (ι : K' →+* L) {x : L}
    (hx : x ^ Nat.card K' = x) : x ∈ ι.range := by
  have hq : 1 < Nat.card K' := Finite.one_lt_card
  have hne : (X ^ Nat.card K' - X : K'[X]).map ι ≠ 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
    exact FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hroot : x ∈ ((X ^ Nat.card K' - X : K'[X]).map ι).roots := by
    rw [Polynomial.mem_roots hne]
    simp [← Nat.card_eq_fintype_card, hx]
  rw [(Polynomial.splits_X_pow_nat_card_sub_X (K := K')).roots_map ι] at hroot
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hroot
  exact ⟨y, rfl⟩

@[expose] def unitFrobGL (Fr : L →+* L) : GL (Fin 3) L →* GL (Fin 3) L where
  toFun g :=
    { val := ((((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ
      inv := (((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ
      val_inv := by
        rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.map_one Fr (map_zero Fr) (map_one Fr), Matrix.transpose_one]
      inv_val := by
        rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.map_one Fr (map_zero Fr) (map_one Fr), Matrix.transpose_one] }
  map_one' := by
    refine Units.ext ?_
    simp only [inv_one, Units.val_one, Matrix.map_one Fr (map_zero Fr) (map_one Fr),
      Matrix.transpose_one]
  map_mul' g g' := by
    refine Units.ext ?_
    simp only [Units.val_mul, _root_.mul_inv_rev, Matrix.map_mul, Matrix.transpose_mul]

theorem coe_unitFrobGL (Fr : L →+* L) (g : GL (Fin 3) L) :
    ((unitFrobGL Fr g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      ((((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ := rfl

theorem secFrobGL_conj (μ : Lˣ) (Fr : L →+* L) {G₀ : GL (Fin 3) L}
    (hG : (G₀ : Matrix (Fin 3) (Fin 3) L) * ((G₀ : Matrix (Fin 3) (Fin 3) L).map Fr)ᵀ =
      secH (μ : L)) (x : GL (Fin 3) L) :
    secFrobGL μ Fr (G₀ * x * G₀⁻¹) = G₀ * unitFrobGL Fr x * G₀⁻¹ := by
  refine Units.ext ?_
  set A := (G₀ : Matrix (Fin 3) (Fin 3) L)
  set Ai := ((G₀⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
  have hAiA : Ai * A = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAAi : A * Ai = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hμ : (μ : L) ≠ 0 := Units.ne_zero μ
  have e1 : secH (μ : L) * (Ai.map Fr)ᵀ = A := by
    rw [← hG, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.map_mul, hAiA,
      Matrix.map_one Fr (map_zero Fr) (map_one Fr), Matrix.transpose_one, Matrix.mul_one]
  have e2 : (A.map Fr)ᵀ * secHinv (μ : L) = Ai := by
    calc (A.map Fr)ᵀ * secHinv (μ : L) = Ai * (A * (A.map Fr)ᵀ) * secHinv (μ : L) := by
          rw [← Matrix.mul_assoc Ai, hAiA, Matrix.one_mul]
      _ = Ai := by rw [hG, Matrix.mul_assoc, secH_mul_secHinv hμ, Matrix.mul_one]
  rw [coe_secFrobGL, Units.val_mul, Units.val_mul, coe_unitFrobGL, _root_.mul_inv_rev,
    _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [← Matrix.mul_assoc]
  rw [e1, Matrix.mul_assoc _ _ (secHinv (μ : L)), e2]

theorem unitFrobGL_unitFrobGL (Fr : L →+* L) (g : GL (Fin 3) L) :
    ((unitFrobGL Fr (unitFrobGL Fr g) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (g : Matrix (Fin 3) (Fin 3) L).map (Fr.comp Fr) := by
  rw [coe_unitFrobGL]
  change ((((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ.map Fr)ᵀ = _
  rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_map]
  rfl

theorem unitFrobGL_scalar (Fr : L →+* L) (c : Lˣ) :
    unitFrobGL Fr (Matrix.GeneralLinearGroup.scalar (Fin 3) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map Fr.toMonoidHom c)⁻¹ := by
  refine Units.ext ?_
  rw [coe_unitFrobGL, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero Fr), Matrix.diagonal_transpose]
  rfl

theorem exists_unitFrobGL_fixed [IsAlgClosed L] {q : ℕ} {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ q) (y : GL (Fin 3) L)
    (hy : ProjGenLinGroup.mk (unitFrobGL Fr y) = ProjGenLinGroup.mk y) :
    ∃ y' : GL (Fin 3) L, ProjGenLinGroup.mk y' = ProjGenLinGroup.mk y ∧ unitFrobGL Fr y' = y' := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.1 hy
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((u⁻¹ : Lˣ) : L) (Nat.succ_pos q)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero q)] at hc
    exact (Units.ne_zero _) hc.symm
  set cu : Lˣ := Units.mk0 c hc0
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) cu * y, ?_, ?_⟩
  · rw [map_mul, ProjGenLinGroup.mk_scalar, one_mul]
  · have hcen : ∀ g : GL (Fin 3) L, ∀ d : Lˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) d * g =
        g * Matrix.GeneralLinearGroup.scalar (Fin 3) d := fun g d => by
      have := Subgroup.mem_center_iff.1 (show Matrix.GeneralLinearGroup.scalar (Fin 3) d ∈
        Subgroup.center (GL (Fin 3) L) by
          rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨d, rfl⟩) g
      exact this.symm
    have hFy : unitFrobGL Fr y = y * (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ :=
      eq_mul_inv_of_mul_eq hu
    have hunit : (Units.map Fr.toMonoidHom cu)⁻¹ * u⁻¹ = cu := by
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, cu, Units.val_mk0, hFr]
      have hu0 : (u : L) ≠ 0 := Units.ne_zero u
      have hc' : c ^ q * c = (u : L)⁻¹ := by rw [← pow_succ, hc, Units.val_inv_eq_inv_val]
      have hcq : c ^ q ≠ 0 := pow_ne_zero _ hc0
      field_simp
      calc (1 : L) = (u : L) * (u : L)⁻¹ := (mul_inv_cancel₀ hu0).symm
        _ = (u : L) * (c ^ q * c) := by rw [hc']
        _ = _ := by ring
    set S : Lˣ →* GL (Fin 3) L := Matrix.GeneralLinearGroup.scalar (Fin 3) with hS
    calc unitFrobGL Fr (S cu * y) = S (Units.map Fr.toMonoidHom cu)⁻¹ * (y * (S u)⁻¹) := by
          rw [map_mul, unitFrobGL_scalar, hFy]
      _ = y * (S (Units.map Fr.toMonoidHom cu)⁻¹ * S u⁻¹) := by
          rw [← mul_assoc, hcen, mul_assoc, map_inv, map_inv]
      _ = y * S cu := by rw [← map_mul, hunit]
      _ = S cu * y := (hcen y cu).symm

@[expose] def secG0Mat (μ c : L) : Matrix (Fin 3) (Fin 3) L := !![1, 1, 0; 0, 0, c; μ, μ ^ 2, 0]

theorem det_secG0Mat {μ : L} (hμ : μ ^ 2 + μ + 1 = 0) (c : L) : (secG0Mat μ c).det = c := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  rw [secG0Mat, Matrix.det_fin_three]
  simp
  grind

theorem secG0_mul_frob_transpose {μ : L} (hμ : μ ^ 2 + μ + 1 = 0) {Fr : L →+* L}
    (hFr : Fr μ = μ ^ 2) {c : L} (hc : c * Fr c = μ) :
    secG0Mat μ c * ((secG0Mat μ c).map Fr)ᵀ = secH μ := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hμ4 : Fr (μ ^ 2) = μ := by
    rw [map_pow, hFr]
    grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secG0Mat, secH, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
      Matrix.transpose_apply, hFr, hμ4, hc] <;>
    grind

theorem unitFrobGL_eq_self_iff (Fr : L →+* L) (g : GL (Fin 3) L) :
    unitFrobGL Fr g = g ↔
      (((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ * (g : Matrix (Fin 3) (Fin 3) L) = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun x : GL (Fin 3) L =>
      ((x⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) h
    change (((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ = ((g⁻¹ : GL (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) at h'
    rw [h', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · intro h
    have hinv : ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        (((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ := by
      have := congrArg (· * ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) h
      simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one, Matrix.one_mul] at this
      exact this.symm
    refine inv_injective (Units.ext ?_)
    change (((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ = _
    exact hinv.symm

section Descent

variable {K' : Type} [Field K'] [Fintype K'] (ι : K' →+* L)

theorem exists_map_eq_of_mem_range (g : GL (Fin 3) L)
    (h : ∀ i j, (g : Matrix (Fin 3) (Fin 3) L) i j ∈ ι.range) :
    ∃ g' : GL (Fin 3) K', Matrix.GeneralLinearGroup.map ι g' = g := by
  choose N hN using h
  set M : Matrix (Fin 3) (Fin 3) K' := Matrix.of N
  have hM : M.map ι = (g : Matrix (Fin 3) (Fin 3) L) := by
    ext i j
    exact hN i j
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg ι h0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, map_zero] at this
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.val_map_apply]
  exact hM

@[expose] def pglMap : PGL(3, K') →* PGL(3, L) :=
  QuotientGroup.map _ _ (Matrix.GeneralLinearGroup.map ι) (by
    intro g hg
    rw [Subgroup.mem_comap]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg ⊢
    obtain ⟨c, rfl⟩ := hg
    refine ⟨Units.map ι.toMonoidHom c, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero ι)]
    rfl)

theorem pglMap_mk (g : GL (Fin 3) K') :
    pglMap ι (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map ι g) :=
  rfl

theorem pglMap_injective : Function.Injective (pglMap ι) := by
  refine (injective_iff_map_eq_one _).2 fun P hP => ?_
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective P
  rw [pglMap_mk, ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    at hP
  obtain ⟨c, hc⟩ := hP
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have hent : ∀ i j, ι ((g : Matrix (Fin 3) (Fin 3) K') i j) = if i = j then (c : L) else 0 := by
    intro i j
    have := congrArg (fun x : GL (Fin 3) L => (x : Matrix (Fin 3) (Fin 3) L) i j) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply] at this
    rw [← this, Matrix.diagonal_apply]
  have h00 : (g : Matrix (Fin 3) (Fin 3) K') 0 0 ≠ 0 := by
    intro h0
    have := hent 0 0
    rw [h0, map_zero, ite_eq_left rfl] at this
    exact Units.ne_zero c this.symm
  refine ⟨Units.mk0 _ h00, Units.ext ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
    Units.val_mk0]
  apply ι.injective
  rw [hent i j]
  split_ifs with hij
  · rw [hent 0 0, ite_eq_left rfl]
  · rw [map_zero]

end Descent

section Iso

variable {K' : Type} [Field K'] [Fintype K'] (ι : K' →+* L)

@[expose] def pguHom (G₀ : GL (Fin 3) L) : PGL(3, K') →* PGL(3, L) :=
  (MulAut.conj (ProjGenLinGroup.mk G₀)).toMonoidHom.comp (pglMap ι)

theorem pguHom_mk (G₀ : GL (Fin 3) L) (h : GL (Fin 3) K') :
    pguHom ι G₀ (ProjGenLinGroup.mk h) =
      ProjGenLinGroup.mk (G₀ * Matrix.GeneralLinearGroup.map ι h * G₀⁻¹) := by
  simp [pguHom, pglMap_mk, MulAut.conj_apply]

theorem pguHom_injective (G₀ : GL (Fin 3) L) : Function.Injective (pguHom ι G₀) :=
  (MulAut.conj (ProjGenLinGroup.mk G₀)).injective.comp (pglMap_injective ι)

variable {n : ℕ} (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K')
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 2 ^ n)

include hU hFr

theorem map_map_frob (M : Matrix (Fin 3) (Fin 3) K') :
    (M.map ι).map Fr = (M.map hU.bar).map ι := by
  ext i j
  simp only [Matrix.map_apply, hFr, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply,
    map_pow]

theorem unitary_form_map (M : Matrix (Fin 3) (Fin 3) K') :
    ((M.map ι).map Fr)ᵀ * M.map ι = ((M.map hU.bar)ᵀ * M).map ι := by
  rw [map_map_frob ι hU hFr, Matrix.map_mul, Matrix.transpose_map]

theorem unitFrobGL_map_of_mem_glPi {h : GL (Fin 3) K'}
    (hh : h ∈ Sec4.glPi false 3 (2 ^ n) K') :
    unitFrobGL Fr (Matrix.GeneralLinearGroup.map ι h) = Matrix.GeneralLinearGroup.map ι h := by
  rw [Sec4.mem_glPi_false hU] at hh
  rw [unitFrobGL_eq_self_iff, Matrix.GeneralLinearGroup.val_map_apply,
    unitary_form_map ι hU hFr, hh, Matrix.map_one ι (map_zero ι) (map_one ι)]

variable (μ : Lˣ) {G₀ : GL (Fin 3) L}
  (hG : (G₀ : Matrix (Fin 3) (Fin 3) L) * ((G₀ : Matrix (Fin 3) (Fin 3) L).map Fr)ᵀ =
    secH (μ : L))

include hG

theorem pguHom_mem_pglFix {P : PGL(3, K')} (hP : P ∈ projImage (Sec4.glPi false 3 (2 ^ n) K')) :
    pguHom ι G₀ P ∈ pglFix μ Fr := by
  obtain ⟨h, hh, rfl⟩ := hP
  change secFrobPGL μ Fr (pguHom ι G₀ (ProjGenLinGroup.mk h)) = pguHom ι G₀ (ProjGenLinGroup.mk h)
  rw [pguHom_mk, secFrobPGL_mk, secFrobGL_conj μ Fr hG,
    unitFrobGL_map_of_mem_glPi ι hU hFr hh]

theorem exists_pguHom_eq [IsAlgClosed L] {Q : PGL(3, L)} (hQ : Q ∈ pglFix μ Fr) :
    ∃ P ∈ projImage (Sec4.glPi false 3 (2 ^ n) K'), pguHom ι G₀ P = Q := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective Q
  set y := G₀⁻¹ * g * G₀ with hy
  have hgy : g = G₀ * y * G₀⁻¹ := by rw [hy]; group
  clear_value y
  have hQ' : secFrobPGL μ Fr (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk g := hQ
  rw [secFrobPGL_mk, hgy, secFrobGL_conj μ Fr hG] at hQ'
  rw [map_mul, map_mul, map_mul, map_mul] at hQ'
  have hy' : ProjGenLinGroup.mk (unitFrobGL Fr y) = ProjGenLinGroup.mk y :=
    mul_left_cancel (mul_right_cancel hQ')
  obtain ⟨y', hyy', hfix⟩ := exists_unitFrobGL_fixed hFr y hy'
  have hent : ∀ i j, (y' : Matrix (Fin 3) (Fin 3) L) i j ∈ ι.range := by
    intro i j
    have h2 := unitFrobGL_unitFrobGL Fr y'
    rw [hfix, hfix] at h2
    have hx := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply, RingHom.comp_apply, hFr, hFr, ← pow_mul, ← pow_add, ← two_mul,
      ← hU.card] at hx
    exact mem_range_of_pow_card_eq ι hx.symm
  obtain ⟨h, rfl⟩ := exists_map_eq_of_mem_range ι y' hent
  have hh : h ∈ Sec4.glPi false 3 (2 ^ n) K' := by
    rw [Sec4.mem_glPi_false hU]
    rw [unitFrobGL_eq_self_iff, Matrix.GeneralLinearGroup.val_map_apply,
      unitary_form_map ι hU hFr] at hfix
    refine Matrix.map_injective ι.injective ?_
    change (((h : Matrix (Fin 3) (Fin 3) K').map hU.bar)ᵀ * (h : Matrix (Fin 3) (Fin 3) K')).map ι =
      (1 : Matrix (Fin 3) (Fin 3) K').map ι
    rw [hfix, Matrix.map_one ι (map_zero ι) (map_one ι)]
  refine ⟨ProjGenLinGroup.mk h, ⟨h, hh, rfl⟩, ?_⟩
  rw [pguHom_mk, map_mul, map_mul, hyy', ← map_mul, ← map_mul, ← hgy]

@[expose] def pguFixHom : projImage (Sec4.glPi false 3 (2 ^ n) K') →* pglFix μ Fr where
  toFun P := ⟨pguHom ι G₀ P.1, pguHom_mem_pglFix ι hU hFr μ hG P.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[expose] def pguEquivPglFix [IsAlgClosed L] :
    projImage (Sec4.glPi false 3 (2 ^ n) K') ≃* pglFix μ Fr :=
  MulEquiv.ofBijective (pguFixHom ι hU hFr μ hG)
    ⟨fun P P' h => Subtype.ext (pguHom_injective ι G₀ (congrArg Subtype.val h)), fun Q => by
      obtain ⟨P, hP, hPQ⟩ := exists_pguHom_eq ι hU hFr μ hG Q.2
      exact ⟨⟨P, hP⟩, Subtype.ext hPQ⟩⟩

end Iso

end CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof
