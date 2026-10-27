module

public import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.Quasithin.SimsE22

open CFSG.Open

section PrimeSubfield

variable (F : Type) [Field F]

@[expose] noncomputable def primeEmb : GL (Fin 2) (⊥ : Subfield F) →* GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.map (⊥ : Subfield F).subtype

@[expose] noncomputable def primeProj :
    GL (Fin 2) (⊥ : Subfield F) →* Matrix.ProjGenLinGroup (Fin 2) F :=
  Matrix.ProjGenLinGroup.mk.comp (primeEmb F)

theorem primeEmb_apply (B : GL (Fin 2) (⊥ : Subfield F)) (i j : Fin 2) :
    ((primeEmb F B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      (((B : Matrix (Fin 2) (Fin 2) (⊥ : Subfield F)) i j : (⊥ : Subfield F)) : F) :=
  Matrix.GeneralLinearGroup.map_apply _ i j B

theorem mem_range_primeEmb {A : GL (Fin 2) F} :
    A ∈ (primeEmb F).range ↔
      ∀ i j, (A : Matrix (Fin 2) (Fin 2) F) i j ∈ (⊥ : Subfield F) := by
  constructor
  · rintro ⟨B, rfl⟩ i j
    rw [primeEmb_apply]
    exact (B : Matrix (Fin 2) (Fin 2) (⊥ : Subfield F)) i j |>.2
  · intro hA
    let B : Matrix (Fin 2) (Fin 2) (⊥ : Subfield F) := Matrix.of fun i j => ⟨A i j, hA i j⟩
    have hBA : (⊥ : Subfield F).subtype.mapMatrix B = (A : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; rfl
    have hdet : B.det ≠ 0 := by
      intro h
      have := RingHom.map_det (⊥ : Subfield F).subtype B
      rw [h, map_zero, hBA] at this
      exact Matrix.GeneralLinearGroup.det_ne_zero A this.symm
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet, ?_⟩
    ext i j
    rw [primeEmb_apply]
    rfl

theorem coe_scalar_mul_apply (u : Fˣ) (A : GL (Fin 2) F) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u * A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j = (u : F) * (A : Matrix (Fin 2) (Fin 2) F) i j := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem coe_mul_scalar_apply (u : Fˣ) (A : GL (Fin 2) F) (i j : Fin 2) :
    ((A * Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j = (A : Matrix (Fin 2) (Fin 2) F) i j * (u : F) := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal]

theorem mk_mem_range_primeProj_iff {A : GL (Fin 2) F} :
    Matrix.ProjGenLinGroup.mk A ∈ (primeProj F).range ↔
      ∃ c : Fˣ, ∀ i j, (c : F) * (A : Matrix (Fin 2) (Fin 2) F) i j ∈ (⊥ : Subfield F) := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 hB
    refine ⟨u⁻¹, fun i j => ?_⟩
    have h1 : (A : Matrix (Fin 2) (Fin 2) F) i j =
        (primeEmb F B : Matrix (Fin 2) (Fin 2) F) i j * (u : F) := by
      rw [← coe_mul_scalar_apply, hu]
    have h2 : ((u⁻¹ : Fˣ) : F) * (A : Matrix (Fin 2) (Fin 2) F) i j =
        (primeEmb F B : Matrix (Fin 2) (Fin 2) F) i j := by
      rw [h1, Units.val_inv_eq_inv_val]
      field_simp
    rw [h2]
    exact (mem_range_primeEmb F).1 ⟨B, rfl⟩ i j
  · rintro ⟨c, hc⟩
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) c * A ∈ (primeEmb F).range :=
      (mem_range_primeEmb F).2 fun i j => by rw [coe_scalar_mul_apply]; exact hc i j
    obtain ⟨B, hB⟩ := h1
    refine ⟨B, ?_⟩
    simp only [primeProj, MonoidHom.comp_apply, hB]
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

@[expose] def primeScaled : Subgroup (GL (Fin 2) F) where
  carrier := {A | ∃ c : Fˣ, ∀ i j,
    (c : F) * (A : Matrix (Fin 2) (Fin 2) F) i j ∈ (⊥ : Subfield F)}
  one_mem' := (mk_mem_range_primeProj_iff F).1 (by rw [map_one]; exact one_mem _)
  mul_mem' := fun {A B} hA hB => (mk_mem_range_primeProj_iff F).1 (by
    rw [map_mul]
    exact mul_mem ((mk_mem_range_primeProj_iff F).2 hA) ((mk_mem_range_primeProj_iff F).2 hB))
  inv_mem' := fun {A} hA => (mk_mem_range_primeProj_iff F).1 (by
    rw [map_inv]
    exact inv_mem ((mk_mem_range_primeProj_iff F).2 hA))

theorem mem_primeScaled_iff_mk {A : GL (Fin 2) F} :
    A ∈ primeScaled F ↔ Matrix.ProjGenLinGroup.mk A ∈ (primeProj F).range :=
  (mk_mem_range_primeProj_iff F).symm

@[expose] def X0 : Subgroup (StatedProj (StatedSL 2 F)) :=
  ((primeScaled F).subgroupOf (StatedSL 2 F)).map (QuotientGroup.mk' _)

section Membership

variable {F}

theorem mk_mem_X0_iff (A : StatedSL 2 F) :
    (QuotientGroup.mk A : StatedProj (StatedSL 2 F)) ∈ X0 F ↔
      (A : GL (Fin 2) F) ∈ primeScaled F := by
  constructor
  · rintro ⟨A₀, hA₀, h⟩
    obtain ⟨u, hu⟩ := (StatedAPI.statedProj_mk_eq_iff (StatedSL 2 F) A₀ A).1 h
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 hA₀)
    refine ⟨c * u⁻¹, fun i j => ?_⟩
    have h1 : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
        (u : F) * ((A₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
      rw [hu]
      simp [Matrix.mul_smul]
    have h2 : ((c * u⁻¹ : Fˣ) : F) * ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
        (c : F) * ((A₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
      rw [h1, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    rw [h2]
    exact hc i j
  · intro h
    exact ⟨A, Subgroup.mem_subgroupOf.2 h, rfl⟩

end Membership

@[expose] noncomputable def toPGL :
    StatedProj (StatedSL 2 F) →* Matrix.ProjGenLinGroup (Fin 2) F :=
  ((StatedSL 2 F).map Matrix.ProjGenLinGroup.mk).subtype.comp
    (StatedAPI.mapMkEquivStatedProj (StatedSL 2 F)).symm.toMonoidHom

theorem toPGL_mk (A : StatedSL 2 F) :
    toPGL F (QuotientGroup.mk A) = Matrix.ProjGenLinGroup.mk (A : GL (Fin 2) F) :=
  StatedAPI.coe_mapMkEquivStatedProj_symm_mk (StatedSL 2 F) A

theorem toPGL_injective : Function.Injective (toPGL F) :=
  Subtype.val_injective.comp (MulEquiv.injective _)

theorem primeEmb_injective : Function.Injective (primeEmb F) := by
  intro A B h
  ext i j
  have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) i j) h
  simp only [primeEmb_apply] at this
  exact this

theorem scalar_fin_two_injective (K : Type) [Field K] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K) := by
  intro u v h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  exact Units.ext (by simpa [Matrix.scalar_apply] using this)

theorem ker_primeProj :
    (primeProj F).ker =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        (⊥ : Subfield F)ˣ →* GL (Fin 2) (⊥ : Subfield F)).range := by
  ext B
  rw [MonoidHom.mem_ker, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · intro h
    have h1 : primeEmb F B ∈ Subgroup.center (GL (Fin 2) F) :=
      Matrix.ProjGenLinGroup.mk_eq_one.1 h
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro g
    apply primeEmb_injective F
    rw [map_mul, map_mul]
    exact h1 (primeEmb F g)
  · intro h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
    obtain ⟨u, rfl⟩ := h
    simp only [primeProj, MonoidHom.comp_apply, primeEmb, Matrix.GeneralLinearGroup.map_scalar]
    exact Matrix.ProjGenLinGroup.mk_scalar _

theorem card_range_scalar_fin_two (K : Type) [Field K] :
    Nat.card (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range =
      Nat.card Kˣ :=
  (Nat.card_congr (MonoidHom.ofInjective (scalar_fin_two_injective K)).toEquiv).symm

theorem card_GL_two_bot (p : ℕ) [Fact p.Prime] [CharP F p] :
    Nat.card (GL (Fin 2) (⊥ : Subfield F)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  have hq : Nat.card (⊥ : Subfield F) = p := Subfield.card_bot F p
  have : Finite (⊥ : Subfield F) :=
    Nat.finite_of_card_ne_zero (by rw [hq]; exact (Fact.out : p.Prime).ne_zero)
  letI : Fintype (⊥ : Subfield F) := Fintype.ofFinite _
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hq]
  simp

theorem isSquare_det_primeEmb (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP F p]
    (hF : Nat.card F = p ^ 2) (B : GL (Fin 2) (⊥ : Subfield F)) :
    IsSquare (Matrix.GeneralLinearGroup.det (primeEmb F B)) := by
  have hp : p.Prime := Fact.out
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero 2 hp.ne_zero)
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  rw [primeEmb, Matrix.GeneralLinearGroup.map_det]
  set u : (⊥ : Subfield F)ˣ := Matrix.GeneralLinearGroup.det B with hu
  set x : F := (((u : (⊥ : Subfield F))) : F) with hx
  have hx0 : x ≠ 0 := by
    intro h0
    exact u.ne_zero (Subtype.ext h0)
  have hxp : x ^ p = x := (Subfield.mem_bot_iff_pow_eq_self F p).1 (u : (⊥ : Subfield F)).2
  have hx1 : x ^ (p - 1) = 1 := by
    have : x ^ (p - 1) * x = 1 * x := by rw [pow_sub_one_mul hp.ne_zero, hxp, one_mul]
    exact mul_right_cancel₀ hx0 this
  have hexp : p ^ 2 / 2 = (p - 1) * ((p + 1) / 2) := by
    obtain ⟨m, hm⟩ := hodd
    have h1 : p - 1 = 2 * m := by omega
    have h2 : (p + 1) / 2 = m + 1 := by omega
    have h3 : p ^ 2 = 2 * (2 * m * (m + 1)) + 1 := by rw [hm]; ring
    rw [h1, h2, h3]
    omega
  have hsq : IsSquare x := by
    rw [FiniteField.isSquare_iff (by rw [ringChar.eq F p]; exact hp2) hx0, hcard, hexp, pow_mul,
      hx1, one_pow]
  obtain ⟨y, hy⟩ := hsq
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (by simpa using hy)
  refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
  simpa [hx] using hy

theorem map_toPGL_X0 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP F p]
    (hF : Nat.card F = p ^ 2) : (X0 F).map (toPGL F) = (primeProj F).range := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
    rw [toPGL_mk]
    exact (mem_primeScaled_iff_mk F).1 ((mk_mem_X0_iff A).1 hx)
  · rintro ⟨B, rfl⟩
    obtain ⟨δ, hδ⟩ := isSquare_det_primeEmb F p hp2 hF B
    have hA : Matrix.GeneralLinearGroup.scalar (Fin 2) δ⁻¹ * primeEmb F B ∈ StatedSL 2 F := by
      rw [StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker, map_mul, hδ,
        Matrix.GeneralLinearGroup.det_scalar]
      simp [pow_two]
    have hmk : Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.scalar (Fin 2) δ⁻¹ * primeEmb F B) = primeProj F B := by
      rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
      rfl
    refine ⟨QuotientGroup.mk ⟨_, hA⟩, (mk_mem_X0_iff ⟨_, hA⟩).2 ?_, ?_⟩
    · rw [mem_primeScaled_iff_mk]
      exact ⟨B, hmk.symm⟩
    · rw [toPGL_mk]
      exact hmk

end PrimeSubfield

section MainResults

variable {F : Type} [Field F]

theorem card_X0 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP F p] (hF : Nat.card F = p ^ 2) :
    Nat.card (X0 F) = p * (p ^ 2 - 1) := by
  have hp : p.Prime := Fact.out
  have h1 : Nat.card (X0 F) = Nat.card (primeProj F).range := by
    rw [← map_toPGL_X0 F p hp2 hF, Subgroup.card_map_of_injective (toPGL_injective F)]
  have h2 := Subgroup.card_ker_mul_card_range (primeProj F)
  rw [ker_primeProj, card_range_scalar_fin_two, Nat.card_units, Subfield.card_bot F p,
    card_GL_two_bot F p] at h2
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  rw [h1]
  refine Nat.eq_of_mul_eq_mul_left hp1 ?_
  rw [h2]
  have e1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have e2 : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  have e3 : 1 ≤ p := hp.pos
  zify [e1, e2, e3]
  ring

theorem odd_index_X0 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP F p]
    (hF : Nat.card F = p ^ 2) : Odd (X0 F).index := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero 2 hp.ne_zero)
  have hc := StatedAPI.card_statedProj_statedSL_two_of_odd (F := F)
    (by rw [hF]; exact hodd.pow)
  have hm := Subgroup.card_mul_index (X0 F)
  rw [card_X0 p hp2 hF, hc, hF] at hm
  obtain ⟨m, hm'⟩ := hodd
  have hm1 : 1 ≤ m := by have := hp.two_le; omega
  generalize (X0 F).index = I at hm ⊢
  subst hm'
  have e1 : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : ((2 * m + 1) ^ 2) ^ 2 - 1 = 8 * (m * (m + 1)) * (2 * m ^ 2 + 2 * m + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e3 : (2 * m + 1) ^ 2 * (8 * (m * (m + 1)) * (2 * m ^ 2 + 2 * m + 1)) =
      ((2 * m + 1) * (4 * (m * (m + 1))) * ((2 * m + 1) * (2 * m ^ 2 + 2 * m + 1))) * 2 := by
    ring
  rw [e1, e2, e3, Nat.mul_div_cancel _ (by norm_num)] at hm
  have hT : 0 < (2 * m + 1) * (4 * (m * (m + 1))) := by positivity
  have hI := Nat.eq_of_mul_eq_mul_left hT hm
  rw [hI]
  exact Odd.mul (odd_two_mul_add_one m) ⟨m ^ 2 + m, by ring⟩

theorem X0_ne_top (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP F p]
    (hF : Nat.card F = p ^ 2) : X0 F ≠ ⊤ := by
  intro htop
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero 2 hp.ne_zero)
  have hc := StatedAPI.card_statedProj_statedSL_two_of_odd (F := F)
    (by rw [hF]; exact hodd.pow)
  have hm := Subgroup.card_mul_index (X0 F)
  rw [card_X0 p hp2 hF, hc, hF, htop, Subgroup.index_top, mul_one] at hm
  obtain ⟨m, hm'⟩ := hodd
  have hm1 : 1 ≤ m := by have := hp.two_le; omega
  subst hm'
  have e1 : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : ((2 * m + 1) ^ 2) ^ 2 - 1 = 8 * (m * (m + 1)) * (2 * m ^ 2 + 2 * m + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e3 : (2 * m + 1) ^ 2 * (8 * (m * (m + 1)) * (2 * m ^ 2 + 2 * m + 1)) =
      ((2 * m + 1) * (4 * (m * (m + 1))) * ((2 * m + 1) * (2 * m ^ 2 + 2 * m + 1))) * 2 := by
    ring
  rw [e1, e2, e3, Nat.mul_div_cancel _ (by norm_num)] at hm
  have hT : 0 < (2 * m + 1) * (4 * (m * (m + 1))) := by positivity
  have hI := Nat.eq_of_mul_eq_mul_left hT ((mul_one _).trans hm)
  nlinarith

theorem primeScaled_map (σ : F ≃+* F) {A : GL (Fin 2) F} (hA : A ∈ primeScaled F) :
    Matrix.GeneralLinearGroup.map σ.toRingHom A ∈ primeScaled F := by
  obtain ⟨c, hc⟩ := hA
  refine ⟨Units.map (σ.toRingHom : F →* F) c, fun i j => ?_⟩
  have h1 : ((Units.map (σ.toRingHom : F →* F) c : Fˣ) : F) *
      ((Matrix.GeneralLinearGroup.map σ.toRingHom A : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) i j =
      σ ((c : F) * (A : Matrix (Fin 2) (Fin 2) F) i j) := by
    rw [Matrix.GeneralLinearGroup.map_apply, map_mul]
    rfl
  rw [h1]
  have : (⊥ : Subfield F).map σ.toRingHom = ⊥ := Subfield.map_bot _
  rw [← this]
  exact Subfield.mem_map.2 ⟨_, hc i j, rfl⟩

theorem mem_statedSL_iff_det {X : GL (Fin 2) F} :
    X ∈ StatedSL 2 F ↔ Matrix.GeneralLinearGroup.det X = 1 := by
  rw [StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker]

theorem exists_conj_of_innerField (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (hg : IsSquare (Matrix.GeneralLinearGroup.det g)) (σ : F ≃+* F) :
    ∃ h : StatedProj (StatedSL 2 F), ∀ A B : ↥(StatedSL 2 F),
      (B : GL (Fin 2) F) =
          g * Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin 2) F) * g⁻¹ →
        (QuotientGroup.mk A : StatedProj (StatedSL 2 F)) ∈ X0 F →
          (QuotientGroup.mk B : StatedProj (StatedSL 2 F)) ∈
            (X0 F).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨δ, hδ⟩ := hg
  set z : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) δ⁻¹ with hz
  have hkSL : z * g ∈ StatedSL 2 F := by
    rw [mem_statedSL_iff_det, map_mul, hz, hδ, Matrix.GeneralLinearGroup.det_scalar]
    simp [pow_two]
  obtain ⟨k, hk⟩ : ∃ k : StatedSL 2 F, (k : GL (Fin 2) F) = z * g := ⟨⟨z * g, hkSL⟩, rfl⟩
  refine ⟨QuotientGroup.mk k, fun A B hB hA => ?_⟩
  have hA1 : Matrix.GeneralLinearGroup.det (A : GL (Fin 2) F) = 1 :=
    mem_statedSL_iff_det.1 A.2
  have hAσ : Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin 2) F) ∈ StatedSL 2 F := by
    rw [mem_statedSL_iff_det, Matrix.GeneralLinearGroup.map_det, hA1, map_one]
  obtain ⟨A', hA'⟩ : ∃ A' : StatedSL 2 F,
      (A' : GL (Fin 2) F) = Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin 2) F) :=
    ⟨⟨_, hAσ⟩, rfl⟩
  have hBeq : B = k * A' * k⁻¹ := by
    apply Subtype.ext
    have hc : ∀ X : GL (Fin 2) F, z * X * z⁻¹ = X := fun X => by
      rw [hz, Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hk, hA']
    rw [hB]
    calc g * Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin 2) F) * g⁻¹
        = z * (g * Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin 2) F) * g⁻¹) * z⁻¹ :=
          (hc _).symm
      _ = z * g * Matrix.GeneralLinearGroup.map σ.toRingHom (A : GL (Fin 2) F) * (z * g)⁻¹ := by
          group
  have hA'X : (QuotientGroup.mk A' : StatedProj (StatedSL 2 F)) ∈ X0 F := by
    rw [mk_mem_X0_iff] at hA ⊢
    rw [hA']
    exact primeScaled_map σ hA
  rw [hBeq]
  exact Subgroup.mem_map.2 ⟨QuotientGroup.mk A', hA'X, by simp [MulAut.conj_apply]⟩

end MainResults

section Unipotent

variable (F : Type) [Field F]

@[expose] def unipGL : GL (Fin 2) F where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipGL_val :
    ((unipGL F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] :=
  rfl

theorem unipGL_mem : unipGL F ∈ StatedSL 2 F :=
  StatedAPI.mem_statedSL_of_det (by simp [unipGL_val, Matrix.det_fin_two_of])

@[expose] def unipSL : StatedSL 2 F := ⟨unipGL F, unipGL_mem F⟩

@[expose] def unip : StatedProj (StatedSL 2 F) := QuotientGroup.mk (unipSL F)

theorem unip_mem_X0 : unip F ∈ X0 F := by
  rw [unip, mk_mem_X0_iff]
  refine ⟨1, fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp [unipSL, unipGL_val]

theorem unip_ne_one : unip F ≠ 1 := by
  intro h
  have h' : (QuotientGroup.mk (unipSL F) : StatedProj (StatedSL 2 F)) = QuotientGroup.mk 1 := h
  obtain ⟨u, hu⟩ := (StatedAPI.statedProj_mk_eq_iff (StatedSL 2 F) _ _).1 h'
  have h01 := congrFun (congrFun hu 0) 1
  simp [unipSL, unipGL_val, Matrix.mul_apply, Fin.sum_univ_two] at h01
  exact u.ne_zero h01.symm

variable {F}

theorem eq_one_of_commute_unip_of_two_ne_zero (h2 : (2 : F) ≠ 0)
    (z : StatedProj (StatedSL 2 F)) (hc : z * unip F = unip F * z) (hz : z * z = 1) : z = 1 := by
  induction z using QuotientGroup.induction_on with | H Z => ?_
  have hc' : (QuotientGroup.mk (Z * unipSL F) : StatedProj (StatedSL 2 F)) =
      QuotientGroup.mk (unipSL F * Z) := hc
  obtain ⟨u, hu⟩ := (StatedAPI.statedProj_mk_eq_iff (StatedSL 2 F) _ _).1 hc'
  have hz' : (QuotientGroup.mk (Z * Z) : StatedProj (StatedSL 2 F)) = QuotientGroup.mk 1 := hz
  obtain ⟨v, hv⟩ := (StatedAPI.statedProj_mk_eq_iff (StatedSL 2 F) _ _).1 hz'
  have hdet : ((Z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
    StatedAPI.det_of_mem_statedSL Z.2
  have e00 := congrFun (congrFun hu 0) 0
  have e01 := congrFun (congrFun hu 0) 1
  have e10 := congrFun (congrFun hu 1) 0
  have e11 := congrFun (congrFun hu 1) 1
  have f01 := congrFun (congrFun hv 0) 1
  simp [unipSL, unipGL_val, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11 f01
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨a, ha⟩ : ∃ a, ((Z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, ((Z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc1⟩ : ∃ c, ((Z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, ((Z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = d := ⟨_, rfl⟩
  simp only [ha, hb, hc1, hd] at e00 e01 e10 e11 f01 hdet
  have hc0 : c = 0 := by
    by_cases hu1 : (u : F) = 1
    · rw [hu1] at e00
      linear_combination e00
    · have h1u : (1 : F) - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu1)
      have : c * (1 - u) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right h1u
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, hc0] at hdet
    simp at hdet
  have hu1 : (u : F) = 1 := by
    have : a * u = a * 1 := by linear_combination (-1 : F) * e00 + hc0
    exact mul_left_cancel₀ ha0 this
  have hda : d = a := by linear_combination e01 + (a + b) * hu1
  have hb0 : b = 0 := by
    have : (2 * a) * b = 0 := by linear_combination f01 - b * hda
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 ha0)
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.mk0 a ha0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, ha, hb, hc1, hd, hb0, hc0, hda]

theorem two_ne_zero_of_charP (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP F p] : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h')

theorem eq_one_of_commute_unip (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP F p]
    (z : StatedProj (StatedSL 2 F)) (hc : z * unip F = unip F * z) (hz : z * z = 1) : z = 1 :=
  eq_one_of_commute_unip_of_two_ne_zero (two_ne_zero_of_charP p hp2) z hc hz

end Unipotent

end CFSG.Quasithin.SimsE22
