module

public import CFSG.Quasithin.MS93.S4AEA
public import CFSG.Quasithin.Vol2.Ch4Sec3C136Off3

public section

namespace CFSG.Quasithin.MS93.S38D

open Matrix CFSG.Quasithin.H13.Ch4

variable {F : Type} [Field F]

section Conj

theorem mulVec_inv_mulVec (x : SL3 F) (v : Fin 3 → F) :
    ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (x : SL3 F) (v : Fin 3 → F) :
    (x : Matrix (Fin 3) (Fin 3) F) *ᵥ (((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]

theorem mulVec_conj_apply (x g : SL3 F) (v : Fin 3 → F) :
    (((MulAut.conj x).toMonoidHom g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      (x : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_mul_SL3, coe_mul_SL3,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end Conj

section Axis

theorem map_conj_eq_qLn [Finite F] [CharP F 2] {A : Subgroup (SL3 F)} {x : SL3 F}
    (hx : A.map (MulAut.conj x).toMonoidHom ≤ sStar) (h2 : ∀ g ∈ A, g * g = 1)
    (hcard : Nat.card A = Nat.card F ^ 2) (hfix : Module.finrank F (fixN A) = 2) :
    A.map (MulAut.conj x).toMonoidHom = qLn := by
  set A' := A.map (MulAut.conj x).toMonoidHom with hA'
  have h2' : ∀ g ∈ A', g * g = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, h2 g hg, map_one]
  have hcard' : Nat.card A' = Nat.card F ^ 2 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj x).injective, hcard]
  have hfix' : Module.finrank F (fixN A') = 2 := by
    rw [hA', finrank_fixN_map_conj, hfix]
  rcases le_qPt_or_le_qLn_of_mul_self_eq_one hx h2' with hP | hL
  · exfalso
    have hEq : A' = qPt := Subgroup.eq_of_le_of_card_ge hP (by rw [card_qPt, hcard'])
    rw [hEq, fixN_qPt, finrank_pt0] at hfix'
    exact absurd hfix' (by decide)
  · exact Subgroup.eq_of_le_of_card_ge hL (by rw [card_qLn, hcard'])

theorem isPGroup_of_mul_self {A : Subgroup (SL3 F)} (h2 : ∀ g ∈ A, g * g = 1) :
    IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by
  rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
  exact h2 g g.2)⟩

theorem eq_of_le_of_isPGroup [Finite F] [CharP F 2] {P A₁ A₂ : Subgroup (SL3 F)}
    (hP : IsPGroup 2 P) (h₁ : A₁ ≤ P) (h₂ : A₂ ≤ P) (h2₁ : ∀ g ∈ A₁, g * g = 1)
    (h2₂ : ∀ g ∈ A₂, g * g = 1) (hcard₁ : Nat.card A₁ = Nat.card F ^ 2)
    (hcard₂ : Nat.card A₂ = Nat.card F ^ 2) (hfix₁ : Module.finrank F (fixN A₁) = 2)
    (hfix₂ : Module.finrank F (fixN A₂) = 2) : A₁ = A₂ := by
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hP
  have e₁ := map_conj_eq_qLn ((Subgroup.map_mono h₁).trans hx) h2₁ hcard₁ hfix₁
  have e₂ := map_conj_eq_qLn ((Subgroup.map_mono h₂).trans hx) h2₂ hcard₂ hfix₂
  exact Subgroup.map_injective (MulAut.conj x).injective (e₁.trans e₂.symm)

abbrev e0 : Fin 3 → F := ![1, 0, 0]

abbrev e1 : Fin 3 → F := ![0, 1, 0]

abbrev e2 : Fin 3 → F := ![0, 0, 1]

theorem eq_sum_basis (v : Fin 3 → F) : v = v 0 • e0 + v 1 • e1 + v 2 • e2 := by
  funext k
  fin_cases k <;> simp

theorem exists_eq_smul_uniTri_of_commute {ψ : (Fin 3 → F) ≃+ (Fin 3 → F)} {σ : F ≃+* F}
    (hσ : ∀ (μ : F) (v : Fin 3 → F), ψ (μ • v) = σ μ • ψ v)
    (hc : ∀ g ∈ (qLn : Subgroup (SL3 F)), ∀ v,
      ψ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ψ v) :
    ∃ μ b c : F, ∀ v, ψ v = μ • (((uniTri 0 b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
  obtain ⟨w, hw⟩ : ∃ w, ψ e2 = w := ⟨_, rfl⟩
  have key : ∀ b c : F, σ b • ψ e0 + σ c • ψ e1 = w 2 • ![b, c, 0] := by
    intro b c
    have h1 := hc (uniTri 0 b c) (mem_qLn_iff_uniTri.mpr ⟨b, c, rfl⟩) e2
    have he : ((uniTri 0 b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e2 =
        e2 + b • e0 + c • e1 := by
      rw [uniTri_mulVec]
      funext k
      fin_cases k <;> simp
    have hw' : ((uniTri 0 b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
        w + w 2 • ![b, c, 0] := by
      rw [uniTri_mulVec]
      funext k
      fin_cases k <;> simp <;> ring
    rw [he, map_add, map_add, hσ, hσ, hw, hw', add_assoc] at h1
    exact add_left_cancel h1
  have h0 : ψ e0 = w 2 • e0 := by
    have := key 1 0
    rwa [map_one, map_zero, one_smul, zero_smul, add_zero] at this
  have h1 : ψ e1 = w 2 • e1 := by
    have := key 0 1
    rwa [map_one, map_zero, one_smul, zero_smul, zero_add] at this
  have hl0 : w 2 ≠ 0 := by
    intro hl0
    rw [hl0, zero_smul] at h0
    have := ψ.injective (h0.trans (map_zero ψ).symm)
    have h00 := congrFun this 0
    simp at h00
  have hlin : ∀ b : F, σ b = b := by
    intro b
    have h2 := key b 0
    rw [map_zero, zero_smul, add_zero, h0, smul_smul] at h2
    have h3 := congrFun h2 0
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h3
    have h4 : (σ b - b) * w 2 = 0 := by linear_combination h3
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hl0)
  refine ⟨w 2, w 0 / w 2, w 1 / w 2, fun v => ?_⟩
  conv_lhs => rw [eq_sum_basis v]
  rw [map_add, map_add, hσ, hσ, hσ, hlin, hlin, hlin, h0, h1, hw, uniTri_mulVec]
  funext k
  fin_cases k <;> simp <;> field_simp

theorem exists_eq_smul_of_commute [Finite F] [CharP F 2] {A : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ A, g * g = 1) (hcard : Nat.card A = Nat.card F ^ 2)
    (hfix : Module.finrank F (fixN A) = 2) {ψ : (Fin 3 → F) ≃+ (Fin 3 → F)} {σ : F ≃+* F}
    (hσ : ∀ (μ : F) (v : Fin 3 → F), ψ (μ • v) = σ μ • ψ v)
    (hc : ∀ g ∈ A, ∀ v,
      ψ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ψ v) :
    ∃ μ : F, ∃ X₀ ∈ A, ∀ v, ψ v = μ • ((X₀ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
  obtain ⟨x, hx⟩ := exists_conj_le_sStar (isPGroup_of_mul_self h2)
  have hq := map_conj_eq_qLn hx h2 hcard hfix
  set X := (x : Matrix (Fin 3) (Fin 3) F) with hX
  set Xi := ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) with hXi
  let ψ' : (Fin 3 → F) ≃+ (Fin 3 → F) :=
    { toFun := fun v => X *ᵥ ψ (Xi *ᵥ v)
      invFun := fun v => X *ᵥ ψ.symm (Xi *ᵥ v)
      left_inv := fun v => by
        simp only [hX, hXi, mulVec_inv_mulVec, AddEquiv.symm_apply_apply, mulVec_mulVec_inv]
      right_inv := fun v => by
        simp only [hX, hXi, mulVec_inv_mulVec, AddEquiv.apply_symm_apply, mulVec_mulVec_inv]
      map_add' := fun v w => by
        simp only [Matrix.mulVec_add, map_add] }
  have hψ' : ∀ v, ψ' v = X *ᵥ ψ (Xi *ᵥ v) := fun _ => rfl
  have hσ' : ∀ (μ : F) (v : Fin 3 → F), ψ' (μ • v) = σ μ • ψ' v := by
    intro μ v
    rw [hψ', hψ', Matrix.mulVec_smul, hσ, Matrix.mulVec_smul]
  have hc' : ∀ g ∈ (qLn : Subgroup (SL3 F)), ∀ v,
      ψ' ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ψ' v := by
    intro g hg v
    rw [← hq] at hg
    obtain ⟨Y, hY, rfl⟩ := hg
    rw [hψ', hψ', mulVec_conj_apply, mulVec_conj_apply, ← hXi, ← hX, mulVec_inv_mulVec,
      hc Y hY]
    simp only [hX, hXi, mulVec_inv_mulVec]
  obtain ⟨μ, b, c, hbc⟩ := exists_eq_smul_uniTri_of_commute hσ' hc'
  have hmem : uniTri 0 b c ∈ Subgroup.map (MulAut.conj x).toMonoidHom A := by
    rw [hq]
    exact mem_qLn_iff_uniTri.mpr ⟨b, c, rfl⟩
  obtain ⟨X₀, hX₀, hX₀e⟩ := hmem
  refine ⟨μ, X₀, hX₀, fun v => ?_⟩
  have h1 := hbc (X *ᵥ v)
  rw [hψ', hXi, hX, mulVec_inv_mulVec, ← hX₀e, mulVec_conj_apply, mulVec_inv_mulVec] at h1
  have h2 := congrArg (fun z => Xi *ᵥ z) h1
  simp only [hXi, mulVec_inv_mulVec, Matrix.mulVec_smul] at h2
  exact h2

end Axis

section Diag

@[expose] def dHom : SL3 F →* Equiv.Perm (Fin 2 → Fin 3 → F) where
  toFun X :=
    { toFun := dact (X : Matrix (Fin 3) (Fin 3) F)
      invFun := dact ((X⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)
      left_inv := fun v => by
        rw [dact_dact, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, dact_one]
      right_inv := fun v => by
        rw [dact_dact, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, dact_one] }
  map_one' := Equiv.ext fun v => by
    show dact _ v = v
    rw [coe_one_SL3, dact_one]
  map_mul' X Y := Equiv.ext fun v => by
    show dact _ v = dact _ (dact _ v)
    rw [dact_dact, coe_mul_SL3]

theorem dHom_apply (X : SL3 F) (v : Fin 2 → Fin 3 → F) :
    dHom X v = dact (X : Matrix (Fin 3) (Fin 3) F) v :=
  rfl

theorem dHom_apply_apply (X : SL3 F) (v : Fin 2 → Fin 3 → F) (i : Fin 2) :
    dHom X v i = (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v i :=
  rfl

theorem dHom_injective : Function.Injective (dHom : SL3 F →* Equiv.Perm _) := by
  intro X Y hXY
  apply Subtype.ext
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have := congrArg (fun e : Equiv.Perm (Fin 2 → Fin 3 → F) => e (fun _ => Pi.single j 1) 0) hXY
  exact this

theorem range_dHom : (dHom : SL3 F →* Equiv.Perm _).range = diagPerms F := by
  ext e
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X, fun v => rfl⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, Equiv.ext fun v => (hX v).symm⟩

theorem card_fixPts_map_dHom (A : Subgroup (SL3 F)) :
    Nat.card (fixPts ((A.map dHom : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F))) :
      Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) = Nat.card (fixN A) ^ 2 := by
  rw [← card_pairs_mem (fixN A)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  constructor
  · intro hv i g hg
    exact congrFun (hv _ ⟨g, hg, rfl⟩) i
  · rintro hv _ ⟨g, hg, rfl⟩
    funext i
    exact hv i g hg

theorem exists_mem_commute_dHom [Finite F] [CharP F 2] {A : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ A, g * g = 1) (hcard : Nat.card A = Nat.card F ^ 2)
    (hfix : Module.finrank F (fixN A) = 2) {τ : Equiv.Perm (Fin 2 → Fin 3 → F)}
    (hadd : τ ∈ addPerms F) (hn : NormalizesDact ⇑τ) (hn' : NormalizesDact ⇑τ⁻¹)
    (hcomm : ∀ X ∈ A, τ * dHom X = dHom X * τ) :
    ∃ X₀ ∈ A, ∀ X : SL3 F, (dHom X₀)⁻¹ * τ * dHom X = dHom X * ((dHom X₀)⁻¹ * τ) := by
  classical
  obtain ⟨ψ, σ, c, hψ, hτc⟩ := exists_normalForm (T := toAddEquivOf τ hadd) two_ne_zero hn hn'
  have hτ : ∀ v i, τ v i = ∑ j, c i j • ψ (v j) := hτc
  have hτ0 : ∀ v, τ v = 0 → v = 0 := by
    intro v hv
    have h00 : τ 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    exact τ.injective (hv.trans h00.symm)
  obtain ⟨i₀, j₀, hc0⟩ : ∃ i₀ j₀, c i₀ j₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : τ (Pi.single 0 e0) = 0 := by
      funext i
      rw [hτ]
      simp [hall]
    have := congrFun (congrFun (hτ0 _ h1) 0) 0
    simp at this
  have hτsingle : ∀ j (x : Fin 3 → F) i, τ (Pi.single j x) i = c i j • ψ x := by
    intro j x i
    rw [hτ, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, map_zero, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hψc : ∀ g ∈ A, ∀ x,
      ψ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ψ x := by
    intro g hg x
    have h1 := congrArg (fun e : Equiv.Perm (Fin 2 → Fin 3 → F) => e (Pi.single j₀ x) i₀)
      (hcomm g hg)
    simp only [Equiv.Perm.mul_apply, dHom_apply, dact_single, dHom_apply_apply] at h1
    rw [hτsingle, hτsingle, Matrix.mulVec_smul] at h1
    exact smul_right_injective _ hc0 h1
  obtain ⟨μ, X₀, hX₀, hψX⟩ := exists_eq_smul_of_commute h2 hcard hfix hψ hψc
  let κ : (Fin 2 → Fin 3 → F) → (Fin 2 → Fin 3 → F) := fun v i => ∑ j, (c i j * μ) • v j
  have hκ : ∀ v, τ v = dHom X₀ (κ v) := by
    intro v
    funext i
    rw [hτ, dHom_apply_apply, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hψX, Matrix.mulVec_smul, smul_smul]
  have hκX : ∀ (X : SL3 F) v, κ (dHom X v) = dHom X (κ v) := by
    intro X v
    funext i
    simp only [κ, dHom_apply_apply, Matrix.mulVec_sum, Matrix.mulVec_smul]
  refine ⟨X₀, hX₀, fun X => Equiv.ext fun v => ?_⟩
  have e1 : ∀ w, ((dHom X₀)⁻¹ * τ) w = κ w := by
    intro w
    rw [Equiv.Perm.mul_apply, hκ]
    exact (dHom X₀).symm_apply_apply _
  rw [Equiv.Perm.mul_apply, e1, Equiv.Perm.mul_apply, e1, hκX]

end Diag

end CFSG.Quasithin.MS93.S38D
