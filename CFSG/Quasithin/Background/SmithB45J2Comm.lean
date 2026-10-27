module

public import CFSG.Quasithin.Background.SmithB45J2Syl
public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Quasithin.H
open scoped Matrix

@[expose] def v0 : BV := ⟨32, 0⟩

@[expose] def h2W : List (Fin 4) := [1, 3, 0, 3, 0, 3, 3, 0, 3, 0, 3, 0, 3, 3, 0, 3, 3]

@[expose] def h2 : BM := ⟨⟨3, 0⟩, ⟨34, 32⟩, ⟨29, 27⟩, ⟨8, 33⟩, ⟨56, 3⟩, ⟨32, 0⟩⟩

@[expose] def h2chain : List (Fin 6 × BV) :=
  [(0, ⟨0, 4⟩), (1, ⟨1, 0⟩), (3, ⟨9, 13⟩), (4, ⟨17, 12⟩), (5, ⟨0, 2⟩)]

@[expose] def gomW : List (Fin 4) := [3, 0, 3, 0, 3, 3, 0, 3, 3, 0, 0, 0]

@[expose] def basW : Fin 6 → List (Fin 4) := ![[], [3], [2], [0], [1], [3, 0]]

@[expose] def pBas : BM := ⟨⟨32, 0⟩, ⟨14, 46⟩, ⟨15, 7⟩, ⟨53, 47⟩, ⟨60, 62⟩, ⟨61, 44⟩⟩

@[expose] def pInv : BM := ⟨⟨10, 60⟩, ⟨41, 47⟩, ⟨19, 28⟩, ⟨59, 48⟩, ⟨47, 21⟩, ⟨1, 0⟩⟩

@[expose] def g0 : BM := ⟨⟨59, 7⟩, ⟨0, 29⟩, ⟨59, 4⟩, ⟨20, 29⟩, ⟨24, 3⟩, ⟨47, 29⟩⟩

@[expose] def g0i : BM := ⟨⟨59, 46⟩, ⟨62, 43⟩, ⟨44, 44⟩, ⟨51, 44⟩, ⟨38, 44⟩, ⟨56, 5⟩⟩

@[expose] def wA : List (Fin 4) :=
  [2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2]

@[expose] def wB : List (Fin 4) :=
  [0, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2]

set_option maxRecDepth 100000 in
theorem comm_check : (evalW h2W).eqv h2 = true ∧ (h2.mv v0).eqv v0 = true ∧
    chainOK h2 h2chain [] = true ∧ ((evalW gomW).mv v0).eqv (v0.smul ω) = true ∧
    (pBas.mul pInv).eqv BM.one = true ∧
    (List.finRange 6).all (fun k => ((evalW (basW k)).mv v0).eqv (pBas.col k)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem psi_check : (g0.mul g0i).eqv BM.one = true ∧ (g0i.mul g0).eqv BM.one = true ∧
    ((g0.mul a6.frob).mul g0i).eqv (evalW wA) = true ∧
    ((g0.mul b6.frob).mul g0i).eqv (evalW wB) = true := by
  decide +kernel

theorem toVec_v0_ne : v0.toVec ≠ 0 := by
  intro h
  have := congrFun h 5
  exact absurd this (by decide)

theorem coe_wordGL_mulVec (l : List (Fin 4)) (x : BV) :
    (wordGL l : M6) *ᵥ x.toVec = ((evalW l).mv x).toVec := by
  rw [coe_wordGL, BM.toVec_mv]

theorem hasScalarCommutant_Γ₆ : HasScalarCommutant Γ₆ := by
  intro f hf
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := comm_check
  have hfix0 : v0.toVec ∈ fixM h2.toMat := by
    rw [mem_fixM, ← BM.toVec_mv]
    exact (BV.eqv_iff _ _).mp c2
  have hh2 : ((wordGL h2W : GL6) : M6) = h2.toMat := by rw [coe_wordGL, toMat_eq_of_eqv c1]
  have hfix : f v0.toVec ∈ fixM h2.toMat := by
    rw [mem_fixM, ← hh2, ← hf _ (wordGL_mem _), hh2, mem_fixM.mp hfix0]
  have hcard := card_fixM_of_chainOK _ _ c3
  have h4 : Nat.card ↥(fixM h2.toMat) ≤ Nat.card FieldFour := by
    rw [FieldFour.natCard_eq]
    have e : h2chain.length = 5 := rfl
    rw [e] at hcard
    generalize Nat.card ↥(fixM h2.toMat) = n at hcard ⊢
    omega
  obtain ⟨c, hc⟩ : ∃ c : FieldFour, f v0.toVec = c • v0.toVec := by
    let φ : FieldFour → ↥(fixM h2.toMat) := fun c => ⟨c • v0.toVec, (fixM _).smul_mem c hfix0⟩
    have hφ : Function.Injective φ := fun a b hab =>
      smul_left_injective FieldFour toVec_v0_ne (congrArg Subtype.val hab)
    have hb := hφ.bijective_of_nat_card_le h4
    obtain ⟨c, hc⟩ := hb.2 ⟨f v0.toVec, hfix⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hω : f (ω • v0.toVec) = c • (ω • v0.toVec) := by
    have e : ω • v0.toVec = (wordGL gomW : M6) *ᵥ v0.toVec := by
      rw [coe_wordGL_mulVec, ← BV.toVec_smul]
      exact ((BV.eqv_iff _ _).mp c4).symm
    rw [e, hf _ (wordGL_mem _), hc, Matrix.mulVec_smul]
  have hl : ∀ l : FieldFour, f (l • v0.toVec) = c • (l • v0.toVec) := by
    intro l
    have hl4 : l = 0 ∨ l = 1 ∨ l = ω ∨ l = ω₂ := by revert l; decide
    rcases hl4 with rfl | rfl | rfl | rfl
    · rw [zero_smul, map_zero, smul_zero]
    · rw [one_smul, hc]
    · exact hω
    · have e : ω₂ • v0.toVec = v0.toVec + ω • v0.toVec := by
        rw [show ω₂ = 1 + ω by decide, add_smul, one_smul]
      rw [e, map_add, hc, hω, smul_add]
  have hcol : ∀ k : Fin 6, (pBas.col k).toVec = (wordGL (basW k) : M6) *ᵥ v0.toVec := by
    intro k
    simp only [List.all_eq_true, List.mem_finRange, forall_const] at c6
    rw [coe_wordGL_mulVec]
    exact ((BV.eqv_iff _ _).mp (c6 k)).symm
  have hmul : pBas.toMat * pInv.toMat = 1 := by
    rw [← BM.toMat_mul, toMat_eq_of_eqv c5, BM.toMat_one]
  refine ⟨c, fun v => ?_⟩
  have hv : v = ∑ k : Fin 6, (pInv.toMat *ᵥ v) k • (pBas.col k).toVec := by
    conv_lhs => rw [← Matrix.one_mulVec v, ← hmul, ← Matrix.mulVec_mulVec]
    funext i
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    rfl
  rw [hv, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hcol, ← Matrix.mulVec_smul, hf _ (wordGL_mem _), hl, Matrix.mulVec_smul]

@[expose] def frobE : FieldFour ≃+* FieldFour where
  toFun := FieldFour.frob
  invFun := FieldFour.frob
  left_inv := frob_frob
  right_inv := frob_frob
  map_mul' := map_mul FieldFour.frob
  map_add' := map_add FieldFour.frob

theorem frobE_apply (x : FieldFour) : frobE x = FieldFour.frob x := rfl

theorem frobE_ne_refl : frobE ≠ RingEquiv.refl FieldFour := by
  intro h
  have h1 := congrArg (fun σ : FieldFour ≃+* FieldFour => σ ω) h
  simp only [frobE_apply, frob_ω, RingEquiv.refl_apply] at h1
  exact ω_ne_ω₂ h1.symm

@[expose] def frobV (v : V6) : V6 := fun i => FieldFour.frob (v i)

theorem frobV_frobV (v : V6) : frobV (frobV v) = v := funext fun i => frob_frob (v i)

theorem frobV_add (v w : V6) : frobV (v + w) = frobV v + frobV w :=
  funext fun i => map_add FieldFour.frob (v i) (w i)

theorem frobV_smul (c : FieldFour) (v : V6) : frobV (c • v) = FieldFour.frob c • frobV v :=
  funext fun i => map_mul FieldFour.frob c (v i)

theorem frobV_mulVec (M : M6) (v : V6) : frobV (M *ᵥ v) = M.map FieldFour.frob *ᵥ frobV v :=
  funext fun i => RingHom.map_mulVec FieldFour.frob M v i

@[expose] noncomputable def G0 : GL6 :=
  ⟨g0.toMat, g0i.toMat, by rw [← BM.toMat_mul, toMat_eq_of_eqv psi_check.1, BM.toMat_one],
    by rw [← BM.toMat_mul, toMat_eq_of_eqv psi_check.2.1, BM.toMat_one]⟩

@[expose] noncomputable def psi0 : MulAut (StdMod (Fin 6) FieldFour) where
  toFun x := Multiplicative.ofAdd (g0.toMat *ᵥ frobV (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (frobV (g0i.toMat *ᵥ Multiplicative.toAdd x))
  left_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← BM.toMat_mul, toMat_eq_of_eqv psi_check.2.1, BM.toMat_one, Matrix.one_mulVec,
      frobV_frobV]
    rfl
  right_inv x := by
    simp only [toAdd_ofAdd]
    rw [frobV_frobV, Matrix.mulVec_mulVec, ← BM.toMat_mul, toMat_eq_of_eqv psi_check.1,
      BM.toMat_one, Matrix.one_mulVec]
    rfl
  map_mul' x y := by
    simp only [toAdd_mul, frobV_add, Matrix.mulVec_add, ofAdd_add]

theorem toAddMap_psi0 (v : V6) : toAddMap psi0 v = g0.toMat *ᵥ frobV v := rfl

theorem toAddMap_psi0_inv (v : V6) : toAddMap psi0⁻¹ v = frobV (g0i.toMat *ᵥ v) := rfl

theorem isSemilinear_psi0 : IsSemilinear psi0 frobE := by
  intro c v
  rw [toAddMap_psi0, toAddMap_psi0, frobV_smul, Matrix.mulVec_smul]
  rfl

@[expose] noncomputable def frobConj : GL6 →* GL6 :=
  (MulAut.conj G0).toMonoidHom.comp
    (Units.map (RingHom.mapMatrix FieldFour.frob : M6 →+* M6).toMonoidHom)

theorem coe_frobConj (γ : GL6) :
    (frobConj γ : M6) = g0.toMat * (γ : M6).map FieldFour.frob * g0i.toMat := rfl

theorem matHom_frobConj (γ : GL6) : matHom (frobConj γ) = psi0 * matHom γ * psi0⁻¹ := by
  refine toAddMap_injective fun v => ?_
  rw [toAddMap_mul, toAddMap_mul, toAddMap_psi0_inv, matHom_apply, matHom_apply, toAddMap_matAut,
    toAddMap_matAut, toAddMap_psi0, frobV_mulVec, frobV_frobV, coe_frobConj, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem frobConj_gA : frobConj gA = wordGL wA := by
  apply Units.ext
  rw [coe_frobConj, coe_wordGL, ← toMat_eq_of_eqv psi_check.2.2.1, BM.toMat_mul, BM.toMat_mul,
    BM.toMat_frob]
  rfl

theorem frobConj_gB : frobConj gB = wordGL wB := by
  apply Units.ext
  rw [coe_frobConj, coe_wordGL, ← toMat_eq_of_eqv psi_check.2.2.2, BM.toMat_mul, BM.toMat_mul,
    BM.toMat_frob]
  rfl

theorem map_frobConj_le : Γ₆.map frobConj ≤ Γ₆ := by
  rw [Γ₆, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, rfl⟩
  rcases hγ with rfl | hγ
  · rw [frobConj_gA]
    exact wordGL_mem _
  · rw [Set.mem_singleton_iff] at hγ
    subst hγ
    rw [frobConj_gB]
    exact wordGL_mem _

theorem frobConj_injective : Function.Injective frobConj := by
  have h1 : Function.Injective (RingHom.mapMatrix FieldFour.frob : M6 →+* M6).toMonoidHom := by
    intro M N h
    refine Matrix.ext fun i j => ?_
    have h2 := congrArg FieldFour.frob (congrFun (congrFun h i) j)
    simpa [frob_frob] using h2
  intro x y h
  exact Units.map_injective h1 ((MulAut.conj G0).injective h)

theorem map_frobConj_eq : Γ₆.map frobConj = Γ₆ := by
  have : Finite GL6 := inferInstance
  refine Subgroup.eq_of_le_of_card_ge map_frobConj_le ?_
  rw [Subgroup.card_map_of_injective frobConj_injective]

theorem psi0_mem_natNorm : psi0 ∈ natNorm Γ₆ := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [natImage_eq_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨frobConj γ, map_frobConj_le ⟨γ, hγ, rfl⟩, matHom_frobConj γ⟩
  · rintro ⟨δ, hδ, hδx⟩
    rw [← map_frobConj_eq] at hδ
    obtain ⟨γ, hγ, rfl⟩ := hδ
    refine ⟨γ, hγ, ?_⟩
    rw [matHom_frobConj] at hδx
    have := congrArg (fun y => psi0⁻¹ * y * psi0) hδx
    simpa [mul_assoc] using this

end CFSG.Quasithin.J2Row
