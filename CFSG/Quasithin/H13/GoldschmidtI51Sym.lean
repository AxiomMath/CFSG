module

public import CFSG.Quasithin.H13.GoldschmidtI51Symp
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.ClassicalGroups.Symplectic.Simple

public noncomputable section

namespace CFSG.Quasithin.H13.I51

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure FormData (G Ω : Type) [Group G] [MulAction G Ω] where
  f : Ω → Ω → ZMod 2
  symm : ∀ x y, f x y = f y x
  diag : ∀ x, f x x = 0
  inv : ∀ (g : G) x y, f (g • x) (g • y) = f x y
  ne : ∃ x y, f x y = 1
  add : ∀ x y, x ≠ y → ∃ z, ∀ p, f z p = f x p + f y p
  trans : MulAction.IsPretransitive G Ω

section Free

variable {Ω : Type} (f : Ω → Ω → ZMod 2)

@[expose] def formU : LinearMap.BilinForm (ZMod 2) (Ω →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) fun e : Ω =>
    Finsupp.linearCombination (ZMod 2) fun g : Ω => f e g

theorem formU_single (x y : Ω) (a c : ZMod 2) :
    formU f (Finsupp.single x a) (Finsupp.single y c) = a * (c * f x y) := by
  simp [formU, Finsupp.linearCombination_single]

variable (hsymm : ∀ x y, f x y = f y x) (hdiag : ∀ x, f x x = 0)
include hsymm

theorem formU_comm (u v : Ω →₀ ZMod 2) : formU f u v = formU f v u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp [h₁, h₂]
  | single e a =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp [h₁, h₂]
    | single g c =>
      rw [formU_single, formU_single, hsymm e g]
      ring

omit hsymm
include hsymm hdiag

theorem formU_self (u : Ω →₀ ZMod 2) : formU f u u = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, h₁, h₂, zero_add, add_zero]
    rw [formU_comm f hsymm u₂ u₁]
    exact CharTwo.add_self_eq_zero _
  | single e a => rw [formU_single, hdiag, mul_zero, mul_zero]

end Free

section Quot

variable {G Ω : Type} [Group G] [MulAction G Ω] (D : FormData G Ω)

@[expose] def Jsub : Submodule (ZMod 2) (Ω →₀ ZMod 2) := LinearMap.ker (formU D.f)

abbrev Vq : Type := (Ω →₀ ZMod 2) ⧸ Jsub D

@[expose] def BqAux : Vq D →ₗ[ZMod 2] (Ω →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (Jsub D).liftQ (formU D.f) le_rfl

theorem BqAux_mk (u v : Ω →₀ ZMod 2) :
    BqAux D (Submodule.Quotient.mk u) v = formU D.f u v := rfl

theorem Jsub_le_ker_flip : Jsub D ≤ LinearMap.ker (BqAux D).flip := by
  intro r hr
  rw [LinearMap.mem_ker]
  refine Submodule.linearMap_qext _ (LinearMap.ext fun φ => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
    BqAux_mk, LinearMap.zero_comp, LinearMap.zero_apply]
  rw [formU_comm D.f D.symm]
  exact hr ▸ rfl

@[expose] def Bq : LinearMap.BilinForm (ZMod 2) (Vq D) :=
  ((Jsub D).liftQ (BqAux D).flip (Jsub_le_ker_flip D)).flip

@[expose] def phi (x : Ω) : Vq D := Submodule.Quotient.mk (Finsupp.single x 1)

theorem Bq_mk (u v : Ω →₀ ZMod 2) :
    Bq D (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = formU D.f u v := rfl

theorem Bq_self (v : Vq D) : Bq D v v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | _ u => rw [Bq_mk, formU_self D.f D.symm D.diag]

theorem mk_eq_zero_iff (u : Ω →₀ ZMod 2) :
    (Submodule.Quotient.mk u : Vq D) = 0 ↔ ∀ y, formU D.f u (Finsupp.single y 1) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  show formU D.f u = 0 ↔ _
  constructor
  · intro h y
    rw [h]; rfl
  · intro h
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.zero_apply]
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => simp [h₁, h₂]
    | single y c => rw [← Finsupp.smul_single_one, map_smul, h y, smul_zero]

theorem Bq_nondeg (v : Vq D) (h : ∀ w, Bq D v w = 0) : v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | _ u =>
    rw [mk_eq_zero_iff]
    intro y
    have := h (Submodule.Quotient.mk (Finsupp.single y 1))
    rwa [Bq_mk] at this

theorem phi_eq_zero_iff (x : Ω) : phi D x = 0 ↔ ∀ y, D.f x y = 0 := by
  rw [phi, mk_eq_zero_iff]
  refine forall_congr' fun y => ?_
  rw [formU_single]; simp

theorem vq_add_self (v : Vq D) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem phi_ne_zero (x : Ω) : phi D x ≠ 0 := by
  intro h
  rw [phi_eq_zero_iff] at h
  obtain ⟨a, b, hab⟩ := D.ne
  obtain ⟨g, hg⟩ := D.trans.exists_smul_eq x a
  have h0 : D.f a b = 0 := by
    rw [← hg]
    have := D.inv g x (g⁻¹ • b)
    rw [smul_inv_smul] at this
    rw [this, h]
  rw [h0] at hab
  exact zero_ne_one hab

theorem phi_add_phi (x y : Ω) (hxy : x ≠ y) : ∃ z, phi D x + phi D y = phi D z := by
  obtain ⟨z, hz⟩ := D.add x y hxy
  refine ⟨z, ?_⟩
  have h : phi D x + phi D y + phi D z = 0 := by
    simp only [phi, ← Submodule.Quotient.mk_add]
    rw [mk_eq_zero_iff]
    intro p
    simp only [map_add, LinearMap.add_apply, formU_single, one_mul]
    rw [hz p]
    exact CharTwo.add_self_eq_zero _
  have h2 := vq_add_self D (phi D z)
  rw [add_eq_zero_iff_eq_neg, neg_eq_of_add_eq_zero_right h2] at h
  exact h

theorem phi_injective : Function.Injective (phi D) := by
  intro x y hxy
  by_contra hne
  obtain ⟨z, hz⟩ := phi_add_phi D x y hne
  rw [hxy, vq_add_self] at hz
  exact phi_ne_zero D z hz.symm

theorem Vq_cases (v : Vq D) : v = 0 ∨ ∃ x, v = phi D x := by
  let S : Submodule (ZMod 2) (Vq D) :=
    { carrier := {v | v = 0 ∨ ∃ x, v = phi D x}
      zero_mem' := Or.inl rfl
      add_mem' := by
        rintro a b (rfl | ⟨x, rfl⟩) (rfl | ⟨y, rfl⟩)
        · left; simp
        · right; exact ⟨y, by simp⟩
        · right; exact ⟨x, by simp⟩
        · by_cases hxy : x = y
          · left; subst hxy; exact vq_add_self D _
          · right
            obtain ⟨z, hz⟩ := phi_add_phi D x y hxy
            exact ⟨z, hz⟩
      smul_mem' := by
        intro c v hv
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · left; simp
        · simpa using hv }
  have hmem : ∀ x, phi D x ∈ S := fun x => Or.inr ⟨x, rfl⟩
  induction v using Submodule.Quotient.induction_on with
  | _ u =>
    have : (Submodule.Quotient.mk u : Vq D) ∈ S := by
      induction u using Finsupp.induction_linear with
      | zero => exact S.zero_mem
      | add u₁ u₂ h₁ h₂ =>
        rw [Submodule.Quotient.mk_add]; exact S.add_mem h₁ h₂
      | single x a =>
        have : (Submodule.Quotient.mk (Finsupp.single x a) : Vq D) = a • phi D x := by
          rw [phi, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]
        rw [this]; exact S.smul_mem a (hmem x)
    exact this

theorem card_Vq [Finite Ω] : Nat.card (Vq D) = Nat.card Ω + 1 := by
  have := Fintype.ofFinite Ω
  let e : Option Ω ≃ Vq D := Equiv.ofBijective (fun o => o.elim 0 (phi D)) ⟨?_, ?_⟩
  · rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option,
      Nat.card_eq_fintype_card]
  · rintro (_ | x) (_ | y) h
    · rfl
    · exact absurd h.symm (phi_ne_zero D y)
    · exact absurd h (phi_ne_zero D x)
    · exact congrArg some (phi_injective D h)
  · intro v
    rcases Vq_cases D v with rfl | ⟨x, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some x, rfl⟩

theorem finrank_Vq [Finite Ω] (hΩ : Nat.card Ω = 63) : Module.finrank (ZMod 2) (Vq D) = 6 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vq D)
  rw [card_Vq, Nat.card_zmod, hΩ] at h
  have h64 : (2 : ℕ) ^ 6 = 63 + 1 := by norm_num
  rw [← h64] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

end Quot

section Action

variable {G Ω : Type} [Group G] [MulAction G Ω] (D : FormData G Ω)

@[expose] def permLin (g : G) : (Ω →₀ ZMod 2) →ₗ[ZMod 2] (Ω →₀ ZMod 2) :=
  (Finsupp.domLCongr (MulAction.toPerm g) : (Ω →₀ ZMod 2) ≃ₗ[ZMod 2] (Ω →₀ ZMod 2)).toLinearMap

theorem permLin_single (g : G) (x : Ω) (a : ZMod 2) :
    permLin g (Finsupp.single x a) = Finsupp.single (g • x) a := by
  simp [permLin]

theorem permLin_mul (g h : G) :
    permLin (Ω := Ω) (g * h) = permLin (Ω := Ω) g ∘ₗ permLin (Ω := Ω) h := by
  refine Finsupp.lhom_ext fun x a => ?_
  simp [permLin_single, mul_smul]

theorem permLin_one : permLin (Ω := Ω) (1 : G) = LinearMap.id := by
  refine Finsupp.lhom_ext fun x a => ?_
  simp [permLin_single]

theorem formU_perm (g : G) (u v : Ω →₀ ZMod 2) :
    formU D.f (permLin g u) (permLin g v) = formU D.f u v := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp [h₁, h₂]
  | single x a =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp [h₁, h₂]
    | single y c => rw [permLin_single, permLin_single, formU_single, formU_single, D.inv]

theorem permLin_mem_J (g : G) {u : Ω →₀ ZMod 2} (hu : u ∈ Jsub D) : permLin g u ∈ Jsub D := by
  rw [Jsub, LinearMap.mem_ker] at hu ⊢
  refine LinearMap.ext fun w => ?_
  have hw : permLin g (permLin g⁻¹ w) = w := by
    rw [← LinearMap.comp_apply, ← permLin_mul, mul_inv_cancel, permLin_one]; rfl
  calc formU D.f (permLin g u) w = formU D.f (permLin g u) (permLin g (permLin g⁻¹ w)) := by
        rw [hw]
    _ = formU D.f u (permLin g⁻¹ w) := formU_perm D g _ _
    _ = 0 := by rw [hu]; rfl

@[expose] def rho (g : G) : Vq D →ₗ[ZMod 2] Vq D :=
  Submodule.mapQ (Jsub D) (Jsub D) (permLin g) (fun _ hu => permLin_mem_J D g hu)

theorem rho_mk (g : G) (u : Ω →₀ ZMod 2) :
    rho D g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (permLin g u) := rfl

theorem rho_phi (g : G) (x : Ω) : rho D g (phi D x) = phi D (g • x) := by
  rw [phi, rho_mk, permLin_single]; rfl

theorem Bq_rho (g : G) (v w : Vq D) : Bq D (rho D g v) (rho D g w) = Bq D v w := by
  induction v using Submodule.Quotient.induction_on with
  | _ u =>
    induction w using Submodule.Quotient.induction_on with
    | _ w => rw [rho_mk, rho_mk, Bq_mk, Bq_mk, formU_perm]

theorem rho_mul (g h : G) : rho D (g * h) = rho D g ∘ₗ rho D h := by
  refine LinearMap.ext fun v => ?_
  induction v using Submodule.Quotient.induction_on with
  | _ u => simp only [LinearMap.comp_apply, rho_mk, permLin_mul]

theorem rho_one : rho D (1 : G) = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  induction v using Submodule.Quotient.induction_on with
  | _ u => rw [rho_mk, permLin_one]; rfl

end Action

section Hom

variable {G Ω : Type} [Group G] [MulAction G Ω] (D : FormData G Ω)

theorem Bq_skew (v w : Vq D) : Bq D v w = - Bq D w v := alt_skew (Bq D) (Bq_self D) v w

theorem exists_symplectic_basis [Finite Ω] (hΩ : Nat.card Ω = 63) :
    ∃ b : Module.Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Vq D),
      LinearMap.BilinForm.toMatrix b (Bq D) = Matrix.J (Fin 3) (ZMod 2) := by
  have hd := finrank_Vq D hΩ
  obtain ⟨e, f, h1, h2, h3⟩ := exists_symplectic_family (ZMod 2) 3 (Vq D) (Bq D) (Bq_self D)
    (Bq_nondeg D) (by rw [hd])
  obtain ⟨b, hbe, hbf⟩ := exists_basis_of_symplectic_family (Bq D) 3 e f h1 h2 h3 (by rw [hd])
  refine ⟨b, ?_⟩
  ext (i | i) (j | j)
  · simp [LinearMap.BilinForm.toMatrix_apply, hbe, h2, Matrix.J]
  · simp [LinearMap.BilinForm.toMatrix_apply, hbe, hbf, h1, Matrix.J, Matrix.one_apply,
      CharTwo.neg_eq]
  · rw [LinearMap.BilinForm.toMatrix_apply, hbe, hbf, Bq_skew D, h1]
    simp [Matrix.J, Matrix.one_apply, eq_comm, CharTwo.neg_eq]
  · simp [LinearMap.BilinForm.toMatrix_apply, hbf, h3, Matrix.J]

end Hom

section Hom2

open Matrix

variable {G Ω : Type} [Group G] [MulAction G Ω] (D : FormData G Ω)
  (b : Module.Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Vq D))

@[expose] noncomputable def repMat (g : G) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  LinearMap.toMatrix b b (rho D g)

theorem repMat_J (hb : LinearMap.BilinForm.toMatrix b (Bq D) = Matrix.J (Fin 3) (ZMod 2))
    (g : G) :
    (repMat D b g)ᵀ * Matrix.J (Fin 3) (ZMod 2) * repMat D b g = Matrix.J (Fin 3) (ZMod 2) := by
  have h := LinearMap.BilinForm.toMatrix_comp (b := b) (c := b) (Bq D) (rho D g) (rho D g)
  have h2 : LinearMap.BilinForm.comp (Bq D) (rho D g) (rho D g) = Bq D := by
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    exact Bq_rho D g v w
  rw [h2, hb] at h
  exact h.symm

theorem repMat_mul (g h : G) : repMat D b (g * h) = repMat D b g * repMat D b h := by
  rw [repMat, rho_mul, repMat, repMat, LinearMap.toMatrix_comp b b b]

theorem repMat_one : repMat D b (1 : G) = 1 := by
  rw [repMat, rho_one, LinearMap.toMatrix_id]

@[expose] noncomputable def symHom
    (hb : LinearMap.BilinForm.toMatrix b (Bq D) = Matrix.J (Fin 3) (ZMod 2)) :
    G →* Matrix.symplecticGroup (Fin 3) (ZMod 2) where
  toFun g := ⟨(repMat D b g⁻¹)ᵀ, by
    rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose]
    exact repMat_J D b hb g⁻¹⟩
  map_one' := by
    refine Subtype.ext ?_
    simp [repMat_one]
  map_mul' g h := by
    refine Subtype.ext ?_
    simp only [_root_.mul_inv_rev, repMat_mul, Matrix.transpose_mul, Submonoid.coe_mul]

theorem symHom_injective (hb : LinearMap.BilinForm.toMatrix b (Bq D) = Matrix.J (Fin 3) (ZMod 2))
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1) :
    Function.Injective (symHom D b hb) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : repMat D b g⁻¹ = 1 := by
    have := congrArg (fun A : Matrix.symplecticGroup (Fin 3) (ZMod 2) =>
      (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ) hg
    simpa [symHom] using this
  have h2 : rho D g⁻¹ = LinearMap.id := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_id]
    exact h1
  have h3 : ∀ x : Ω, g⁻¹ • x = x := by
    intro x
    apply phi_injective D
    rw [← rho_phi, h2]; rfl
  have := hfaith g⁻¹ h3
  simpa using this

end Hom2

open CFSG.Blueprint

theorem isSimpleGroup_symplectic_three_two :
    IsSimpleGroup (Matrix.symplecticGroup (Fin 3) (ZMod 2)) := by
  rcases lieModel_symplecticGroup with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 3 2 1 h
  all_goals exact absurd h (by norm_num)

theorem lieModel_of_injective_symplectic {G : Type} [Group G]
    (A : G →* Matrix.symplecticGroup (Fin 3) (ZMod 2)) (hA : Function.Injective A)
    (hG : 725760 ≤ Nat.card G) : LieModel G .PSp 3 2 1 := by
  have hsimple := isSimpleGroup_symplectic_three_two
  have hSp := card_symplecticGroup_three_two
  have hfin : Finite (Matrix.symplecticGroup (Fin 3) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hSp]; norm_num)
  let H := A.range
  have hcard : Nat.card H = Nat.card G :=
    Nat.card_congr (MonoidHom.ofInjective hA).toEquiv.symm
  have hmul := Subgroup.card_mul_index H
  rw [hSp, hcard] at hmul
  have hidx0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx2 : H.index ≤ 2 := by
    by_contra h
    push Not at h
    nlinarith
  have hH : H = ⊤ := by
    rcases (show H.index = 1 ∨ H.index = 2 by omega) with h1 | h2
    · exact Subgroup.index_eq_one.1 h1
    · exfalso
      have : H.Normal := Subgroup.normal_of_index_eq_two h2
      rcases hsimple.eq_bot_or_eq_top_of_normal H with h | h
      · rw [h, Subgroup.card_bot] at hcard
        omega
      · rw [h, Subgroup.index_top] at h2
        omega
  exact lieModel_of_mulEquiv_symplecticGroup
    ((MonoidHom.ofInjective hA).trans ((MulEquiv.subgroupCongr hH).trans Subgroup.topEquiv))

theorem lieModel_sp62_of_formData {G Ω : Type} [Group G] [Fintype Ω] [DecidableEq Ω]
    [MulAction G Ω] [Finite Ω] (D : FormData G Ω) (hΩ : Nat.card Ω = 63)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1) (hG : 725760 ≤ Nat.card G) :
    LieModel G .PSp 3 2 1 := by
  obtain ⟨b, hb⟩ := exists_symplectic_basis D hΩ
  exact lieModel_of_injective_symplectic (symHom D b hb) (symHom_injective D b hb hfaith) hG

end CFSG.Quasithin.H13.I51
