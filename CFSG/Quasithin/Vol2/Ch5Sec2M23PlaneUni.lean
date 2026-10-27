module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23GxRho
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Monster.B.Classical.Plane CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.MathieuExt
  CFSG.ComponentClassification.WittDesign
open scoped Matrix MatrixGroups

@[expose] def uniMat (a b c : F4) : Matrix (Fin 3) (Fin 3) F4 := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem det_uniMat (a b c : F4) : (uniMat a b c).det = 1 := by
  simp [uniMat, Matrix.det_fin_three]

theorem uniMat_mul (a b c a' b' c' : F4) :
    uniMat a b c * uniMat a' b' c' = uniMat (a + a') (b + a * c' + b') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uniMat_zero : uniMat 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def uniSL (a b c : F4) : Matrix.SpecialLinearGroup (Fin 3) F4 :=
  ⟨uniMat a b c, det_uniMat a b c⟩

@[expose] noncomputable def uniPerm (a b c : F4) : Equiv.Perm (Fin 21) :=
  pslPerm (uniSL a b c : PSL(3, F4))

theorem uniPerm_apply (a b c : F4) (i : Fin 21) :
    uniPerm a b c i = normIdx (uniMat a b c *ᵥ Ω i) :=
  pslPerm_mk_apply _ i

theorem uniPerm_mul (a b c a' b' c' : F4) :
    uniPerm a b c * uniPerm a' b' c' = uniPerm (a + a') (b + a * c' + b') (c + c') := by
  rw [uniPerm, uniPerm, uniPerm, ← map_mul]
  congr 1
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (uniMat_mul a b c a' b' c')

theorem uniPerm_zero : uniPerm 0 0 0 = 1 := by
  rw [uniPerm, show uniSL 0 0 0 = 1 from Subtype.ext uniMat_zero]
  exact map_one pslPerm

theorem f4_add_self : ∀ x : F4, x + x = 0 := by decide

theorem f4_add_add_self : ∀ x y : F4, x + y + (y + x) = 0 := by decide

theorem uniPerm_inv (a b c : F4) : (uniPerm a b c)⁻¹ = uniPerm a (a * c + b) c := by
  rw [inv_eq_iff_mul_eq_one, uniPerm_mul, f4_add_self a, f4_add_add_self b (a * c), f4_add_self c,
    uniPerm_zero]

theorem uniPerm_mem_P0 (a b c : F4) : uniPerm a b c ∈ P0 := ⟨_, rfl⟩

theorem exists_GL_of_mem_P0 {p : Equiv.Perm (Fin 21)} (hp : p ∈ P0) :
    ∃ M : GL (Fin 3) F4, (M : Matrix (Fin 3) (Fin 3) F4).det = 1 ∧
      p = planePerm (semΓ M (RingEquiv.refl F4)) := by
  obtain ⟨g, hg⟩ := hp
  obtain ⟨M, hM⟩ := QuotientGroup.mk_surjective g
  have hdet : ((Matrix.SpecialLinearGroup.toGL M : GL (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4).det = 1 := M.2
  refine ⟨Matrix.SpecialLinearGroup.toGL M, hdet, ?_⟩
  have e1 : semΓ (Matrix.SpecialLinearGroup.toGL M) (RingEquiv.refl F4) = slHom M :=
    semΓ_refl_eq_slHom _ hdet
  rw [e1, planePerm_slHom, ← hg, ← hM]

@[expose] noncomputable def U3 : Subgroup (Equiv.Perm (Fin 21)) where
  carrier := {p | ∃ a b c : F4, p = uniPerm a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, uniPerm_mul a b c a' b' c'⟩
  one_mem' := ⟨0, 0, 0, uniPerm_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, uniPerm_inv a b c⟩

@[expose] noncomputable def Ea : Subgroup (Equiv.Perm (Fin 21)) where
  carrier := {p | ∃ b c : F4, p = uniPerm 0 b c}
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
    refine ⟨b + b', c + c', ?_⟩
    rw [uniPerm_mul, zero_add, zero_mul, add_zero]
  one_mem' := ⟨0, 0, uniPerm_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨b, c, ?_⟩
    rw [uniPerm_inv, zero_mul, zero_add]

@[expose] noncomputable def Ec : Subgroup (Equiv.Perm (Fin 21)) where
  carrier := {p | ∃ a b : F4, p = uniPerm a b 0}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    refine ⟨a + a', b + b', ?_⟩
    rw [uniPerm_mul, mul_zero, add_zero, add_zero]
  one_mem' := ⟨0, 0, uniPerm_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    rw [uniPerm_inv, mul_zero, zero_add]

theorem U3_le_P0 : U3 ≤ P0 := by
  rintro _ ⟨a, b, c, rfl⟩
  exact uniPerm_mem_P0 a b c

theorem Ea_le_U3 : Ea ≤ U3 := by
  rintro _ ⟨b, c, rfl⟩
  exact ⟨0, b, c, rfl⟩

theorem Ec_le_U3 : Ec ≤ U3 := by
  rintro _ ⟨a, b, rfl⟩
  exact ⟨a, b, 0, rfl⟩

theorem uniMat_mulVec_one : ∀ a b c : F4, uniMat a b c *ᵥ Ω 1 = ![a, 1, 0] := by
  decide +kernel

theorem uniMat_mulVec_zero : ∀ a b c : F4, uniMat a b c *ᵥ Ω 0 = ![b, c, 1] := by
  decide +kernel

theorem uniPerm_apply_one (a b c : F4) : uniPerm a b c 1 = normIdx ![a, 1, 0] := by
  rw [uniPerm_apply, uniMat_mulVec_one]

theorem uniPerm_apply_zero (a b c : F4) : uniPerm a b c 0 = normIdx ![b, c, 1] := by
  rw [uniPerm_apply, uniMat_mulVec_zero]

theorem normIdx_a10_inj : ∀ a a' : F4, normIdx ![a, 1, 0] = normIdx ![a', 1, 0] → a = a' := by
  decide

theorem normIdx_bc1_inj : ∀ b c b' c' : F4, normIdx ![b, c, 1] = normIdx ![b', c', 1] →
    b = b' ∧ c = c' := by
  decide

theorem uniPerm_inj {a b c a' b' c' : F4} (h : uniPerm a b c = uniPerm a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := congrArg (fun p : Equiv.Perm (Fin 21) => p 1) h
  have h0 := congrArg (fun p : Equiv.Perm (Fin 21) => p 0) h
  simp only [uniPerm_apply_one, uniPerm_apply_zero] at h1 h0
  exact ⟨normIdx_a10_inj a a' h1, normIdx_bc1_inj b c b' c' h0⟩

theorem card_U3 : Nat.card U3 = 64 := by
  have hbij : Function.Bijective (fun x : F4 × F4 × F4 =>
      (⟨uniPerm x.1 x.2.1 x.2.2, x.1, x.2.1, x.2.2, rfl⟩ : ↥U3)) := by
    refine ⟨fun x y hxy => ?_, fun p => ?_⟩
    · have h := uniPerm_inj (congrArg Subtype.val hxy)
      exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
    · obtain ⟨_, a, b, c, rfl⟩ := p
      exact ⟨(a, b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_prod, F4.card]

theorem card_Ea : Nat.card Ea = 16 := by
  have hbij : Function.Bijective (fun x : F4 × F4 =>
      (⟨uniPerm 0 x.1 x.2, x.1, x.2, rfl⟩ : ↥Ea)) := by
    refine ⟨fun x y hxy => ?_, fun p => ?_⟩
    · have h := uniPerm_inj (congrArg Subtype.val hxy)
      exact Prod.ext h.2.1 h.2.2
    · obtain ⟨_, b, c, rfl⟩ := p
      exact ⟨(b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_prod,
    F4.card]

theorem card_Ec : Nat.card Ec = 16 := by
  have hbij : Function.Bijective (fun x : F4 × F4 =>
      (⟨uniPerm x.1 x.2 0, x.1, x.2, rfl⟩ : ↥Ec)) := by
    refine ⟨fun x y hxy => ?_, fun p => ?_⟩
    · have h := uniPerm_inj (congrArg Subtype.val hxy)
      exact Prod.ext h.1 h.2.1
    · obtain ⟨_, a, b, rfl⟩ := p
      exact ⟨(a, b), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_prod,
    F4.card]

theorem Ea_ne_Ec : Ea ≠ Ec := by
  intro h
  have hmem : uniPerm 0 0 1 ∈ Ec := h ▸ (⟨0, 1, rfl⟩ : uniPerm 0 0 1 ∈ Ea)
  obtain ⟨a, b, hab⟩ := hmem
  exact absurd (uniPerm_inj hab).2.2 (by decide)

theorem Ea_sq (p : Equiv.Perm (Fin 21)) (hp : p ∈ Ea) : p * p = 1 := by
  obtain ⟨b, c, rfl⟩ := hp
  rw [uniPerm_mul]
  simp only [zero_mul, add_zero, f4_add_self, uniPerm_zero]

theorem Ec_sq (p : Equiv.Perm (Fin 21)) (hp : p ∈ Ec) : p * p = 1 := by
  obtain ⟨a, b, rfl⟩ := hp
  rw [uniPerm_mul]
  simp only [mul_zero, add_zero, f4_add_self, uniPerm_zero]

theorem Ea_comm (p q : Equiv.Perm (Fin 21)) (hp : p ∈ Ea) (hq : q ∈ Ea) : p * q = q * p := by
  obtain ⟨b, c, rfl⟩ := hp
  obtain ⟨b', c', rfl⟩ := hq
  rw [uniPerm_mul, uniPerm_mul]
  congr 1 <;> ring

theorem Ec_comm (p q : Equiv.Perm (Fin 21)) (hp : p ∈ Ec) (hq : q ∈ Ec) : p * q = q * p := by
  obtain ⟨a, b, rfl⟩ := hp
  obtain ⟨a', b', rfl⟩ := hq
  rw [uniPerm_mul, uniPerm_mul]
  congr 1 <;> ring

theorem uniPerm_apply_five (a b c : F4) : uniPerm a b c 5 = 5 := by
  rw [uniPerm_apply]
  revert a b c
  decide

theorem fix_Ea_iff (j : Fin 21) : (∀ b c : F4, uniPerm 0 b c j = j) ↔ j ∈ projLine 0 := by
  simp only [uniPerm_apply]
  revert j
  decide

theorem fix_Ec_iff (j : Fin 21) : (∀ a b : F4, uniPerm a b 0 j = j) ↔ j = 5 := by
  simp only [uniPerm_apply]
  revert j
  decide

theorem apply_five_of_normalizes_Ec {x : Equiv.Perm (Fin 21)}
    (hx : ∀ p ∈ Ec, x * p * x⁻¹ ∈ Ec) : x 5 = 5 := by
  have h : ∀ a b : F4, uniPerm a b 0 (x⁻¹ 5) = x⁻¹ 5 := by
    intro a b
    obtain ⟨a', b', h'⟩ := hx _ ⟨a, b, rfl⟩
    have e : x (uniPerm a b 0 (x⁻¹ 5)) = 5 := by
      have := congrArg (fun p : Equiv.Perm (Fin 21) => p 5) h'
      simp only [Equiv.Perm.mul_apply, uniPerm_apply_five] at this
      exact this
    apply x.injective
    rw [e]
    simp
  have h5 : x⁻¹ 5 = 5 := (fix_Ec_iff _).mp h
  conv_lhs => rw [← h5]
  simp

theorem mem_projLine_zero_of_normalizes_Ea {x : Equiv.Perm (Fin 21)}
    (hx : ∀ p ∈ Ea, x⁻¹ * p * x ∈ Ea) {j : Fin 21} (hj : j ∈ projLine 0) : x j ∈ projLine 0 := by
  rw [← fix_Ea_iff]
  intro b c
  obtain ⟨b', c', h'⟩ := hx _ ⟨b, c, rfl⟩
  have e := congrArg (fun p : Equiv.Perm (Fin 21) => p j) h'
  simp only [Equiv.Perm.mul_apply] at e
  rw [(fix_Ea_iff j).mpr hj b' c'] at e
  have e2 := congrArg x e
  simpa using e2

@[expose] def lowMat : Matrix (Fin 3) (Fin 3) F4 := !![1, 0, 0; 1, 1, 0; 0, 0, 1]

theorem det_lowMat : lowMat.det = 1 := by
  simp [lowMat, Matrix.det_fin_three]

@[expose] def lowSL : Matrix.SpecialLinearGroup (Fin 3) F4 := ⟨lowMat, det_lowMat⟩

@[expose] noncomputable def lowPerm : Equiv.Perm (Fin 21) := pslPerm (lowSL : PSL(3, F4))

theorem lowPerm_mem_P0 : lowPerm ∈ P0 := ⟨_, rfl⟩

theorem lowPerm_apply_five : lowPerm 5 ≠ 5 := by
  rw [lowPerm, pslPerm_mk_apply]
  decide

@[expose] def diagMat (d : F4) : Matrix (Fin 3) (Fin 3) F4 := !![d, 0, 0; 0, 1, 0; 0, 0, 1]

theorem diagMat_mul_diagMat {d e : F4} (hde : d * e = 1) : diagMat d * diagMat e = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat, Matrix.mul_apply, Fin.sum_univ_three, hde]

@[expose] def diagGL (d : F4ˣ) : GL (Fin 3) F4 :=
  ⟨diagMat d, diagMat ↑d⁻¹, diagMat_mul_diagMat (Units.mul_inv d),
    diagMat_mul_diagMat (Units.inv_mul d)⟩

theorem det_diagGL (d : F4ˣ) :
    ((diagGL d : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = d := by
  simp [diagGL, diagMat, Matrix.det_fin_three]

theorem diag_uniMat_diag (d : F4ˣ) (a b c : F4) :
    diagMat d * uniMat a b c * diagMat ↑d⁻¹ = uniMat (d * a) (d * b) c := by
  have h1 : ((d⁻¹ : F4ˣ) : F4) * d = 1 := Units.inv_mul d
  have h2 : (d : F4) * ((d⁻¹ : F4ˣ) : F4) = 1 := Units.mul_inv d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagMat, uniMat, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem conj_diag_uniPerm (d : F4ˣ) (a b c : F4) :
    planePerm (semΓ (diagGL d) (RingEquiv.refl F4)) * uniPerm a b c *
        (planePerm (semΓ (diagGL d) (RingEquiv.refl F4)))⁻¹ = uniPerm (d * a) (d * b) c := by
  rw [uniPerm, uniPerm, ← planePerm_slHom, ← planePerm_slHom, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply semΓ_conj_slHom
  rw [show ((diagGL d)⁻¹ : GL (Fin 3) F4) = ⟨diagMat ↑d⁻¹, diagMat d,
    diagMat_mul_diagMat (Units.inv_mul d), diagMat_mul_diagMat (Units.mul_inv d)⟩ from rfl]
  change uniMat (d * a) (d * b) c = diagMat d * (uniMat a b c).map (RingEquiv.refl F4) *
    diagMat ↑d⁻¹
  rw [show (uniMat a b c).map (RingEquiv.refl F4) = uniMat a b c from Matrix.map_id' _,
    diag_uniMat_diag]

end CFSG.Quasithin.H13
