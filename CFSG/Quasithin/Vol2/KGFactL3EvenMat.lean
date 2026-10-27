module

public import CFSG.Quasithin.Vol2.KGFactL3EvenCore
public import CFSG.Quasithin.Vol2.KGFactSL3

public section

namespace CFSG.Quasithin.H13.KGL3Even

open Matrix CFSG.Quasithin.H13.Ch4.KGSL3

variable {F : Type} [Field F]

@[expose] def planeStab : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0}
  one_mem' := by
    show (1 : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (1 : Matrix (Fin 3) (Fin 3) F) 2 1 = 0
    simp
  mul_mem' := by
    rintro g h ⟨hg0, hg1⟩ ⟨hh0, hh1⟩
    show ((g : Matrix (Fin 3) (Fin 3) F) * h) 2 0 = 0 ∧ ((g : Matrix (Fin 3) (Fin 3) F) * h) 2 1 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1, hh0, hh1]
  inv_mem' := by
    rintro g ⟨hg0, hg1⟩
    show (adjugate (g : Matrix (Fin 3) (Fin 3) F)) 2 0 = 0 ∧
      (adjugate (g : Matrix (Fin 3) (Fin 3) F)) 2 1 = 0
    rw [adjugate_fin_three]
    simp [hg0, hg1]

theorem entry_two_two_ne_zero {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ planeStab) :
    (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h
  have hdet := g.2
  rw [det_fin_three, hg.1, hg.2, h] at hdet
  simp at hdet

theorem mul_uMat_of_planeStab {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ planeStab)
    (c₀ c₁ : F) :
    (g : Matrix (Fin 3) (Fin 3) F) * uMat c₀ c₁ =
      uMat (((g : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ *
          ((g : Matrix (Fin 3) (Fin 3) F) 0 0 * c₀ + (g : Matrix (Fin 3) (Fin 3) F) 0 1 * c₁))
        (((g : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ *
          ((g : Matrix (Fin 3) (Fin 3) F) 1 0 * c₀ + (g : Matrix (Fin 3) (Fin 3) F) 1 1 * c₁)) *
        (g : Matrix (Fin 3) (Fin 3) F) := by
  have hd := entry_two_two_ne_zero hg
  obtain ⟨h0, h1⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, h0, h1] <;> field_simp <;> ring

@[expose] def uOf (c : Fin 2 → F) : SpecialLinearGroup (Fin 3) F := uSL (c 0) (c 1)

@[expose] def levP (g : SpecialLinearGroup (Fin 3) F) : (Fin 2 → F) →ₗ[F] (Fin 2 → F) :=
  ((g : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ • Matrix.mulVecLin (blk (g : Matrix (Fin 3) (Fin 3) F))

theorem levP_apply (g : SpecialLinearGroup (Fin 3) F) (c : Fin 2 → F) (i : Fin 2) :
    levP g c i = ((g : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ *
      ((blk (g : Matrix (Fin 3) (Fin 3) F)).mulVec c) i := by
  simp [levP]

theorem conj_uOf {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ planeStab) (c : Fin 2 → F) :
    g * uOf c * g⁻¹ = uOf (levP g c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (g : Matrix (Fin 3) (Fin 3) F) * uMat (c 0) (c 1) =
    uMat (levP g c 0) (levP g c 1) * (g : Matrix (Fin 3) (Fin 3) F)
  rw [mul_uMat_of_planeStab hg, levP_apply, levP_apply]
  congr 2 <;> simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem uOf_add (c d : Fin 2 → F) : uOf (c + d) = uOf c * uOf d := by
  simp only [uOf, Pi.add_apply]
  rw [uSL_mul_uSL]

theorem uOf_mem (c : Fin 2 → F) : uOf c ∈ (uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :=
  ⟨c 0, c 1, rfl⟩

theorem uOf_injective : Function.Injective (uOf : (Fin 2 → F) → SpecialLinearGroup (Fin 3) F) := by
  intro c d h
  have h0 := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 2) h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 2) h
  simp [uOf, uSL, uMat] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

@[expose] noncomputable def planeCoord : LinCoord (uSub : Subgroup (SpecialLinearGroup (Fin 3) F))
    planeStab F where
  ι := uOf
  ι_add := uOf_add
  ι_mem := uOf_mem
  ι_surj := by
    rintro _ ⟨c₀, c₁, rfl⟩
    refine ⟨![c₀, c₁], ?_⟩
    simp [uOf]
  ι_inj := uOf_injective
  lev := levP
  conj := fun _ hg c => conj_uOf hg c

theorem entries_of_mul_eq {g : Matrix (Fin 3) (Fin 3) F} {c₀ c₁ d₀ d₁ : F}
    (h : g * uMat c₀ c₁ = uMat d₀ d₁ * g) :
    (d₀ = 0 ∨ g 2 0 = 0) ∧ (d₀ = 0 ∨ g 2 1 = 0) ∧ (d₁ = 0 ∨ g 2 0 = 0) ∧
      (d₁ = 0 ∨ g 2 1 = 0) := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

theorem normalizer_le_planeStab {R₀ : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hR : R₀ ≤ uSub) (hR1 : R₀ ≠ ⊥) :
    Subgroup.normalizer (R₀ : Set (SpecialLinearGroup (Fin 3) F)) ≤ planeStab := by
  intro g hg
  obtain ⟨r, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have hrR : (r : SpecialLinearGroup (Fin 3) F) ∈ R₀ := r.2
  have hr1' : (r : SpecialLinearGroup (Fin 3) F) ≠ 1 := fun h => hr1 (Subtype.ext h)
  obtain ⟨c₀, c₁, hc⟩ := hR hrR
  have hconj : g * r * g⁻¹ ∈ R₀ := (Subgroup.mem_normalizer_iff.mp hg r).mp hrR
  obtain ⟨d₀, d₁, hd⟩ := hR hconj
  have hd1 : d₀ ≠ 0 ∨ d₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hr1'
    have : g * r * g⁻¹ = 1 := by rw [hd, hcon.1, hcon.2, uSL_zero]
    rw [mul_inv_eq_one, mul_eq_left] at this
    exact this
  have hmul : (g : Matrix (Fin 3) (Fin 3) F) * uMat c₀ c₁ = uMat d₀ d₁ * g := by
    have h1 : g * r = uSL d₀ d₁ * g := by rw [← hd]; group
    rw [hc] at h1
    exact congrArg Subtype.val h1
  obtain ⟨e0, e1, e2, e3⟩ := entries_of_mul_eq hmul
  rcases hd1 with h | h
  · exact ⟨e0.resolve_left h, e1.resolve_left h⟩
  · exact ⟨e2.resolve_left h, e3.resolve_left h⟩

theorem entries_of_mem_centralizer {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ Subgroup.centralizer ((uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F))) :
    (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 2 2 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 1 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  have hc : ∀ c₀ c₁ : F, (g : Matrix (Fin 3) (Fin 3) F) * uMat c₀ c₁ =
      uMat c₀ c₁ * (g : Matrix (Fin 3) (Fin 3) F) := by
    intro c₀ c₁
    have := Subgroup.mem_centralizer_iff.mp hg (uSL c₀ c₁) ⟨c₀, c₁, rfl⟩
    exact (congrArg Subtype.val this).symm
  have e0 := congrFun (congrFun (hc 1 0) 0) 0
  have e1 := congrFun (congrFun (hc 1 0) 0) 1
  have h02 := congrFun (congrFun (hc 1 0) 0) 2
  have h12 := congrFun (congrFun (hc 1 0) 1) 2
  have h02' := congrFun (congrFun (hc 0 1) 0) 2
  have h12' := congrFun (congrFun (hc 0 1) 1) 2
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] at h02 h12 h02' h12' e0 e1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination e0
  · linear_combination e1
  · linear_combination h02'
  · linear_combination h12
  · linear_combination h02
  · linear_combination h12'

theorem centralizer_comm {g h : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ Subgroup.centralizer ((uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)))
    (hh : h ∈ Subgroup.centralizer ((uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F))) : g * h = h * g := by
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := entries_of_mem_centralizer hg
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := entries_of_mem_centralizer hh
  apply Subtype.ext
  change (g : Matrix (Fin 3) (Fin 3) F) * h = (h : Matrix (Fin 3) (Fin 3) F) * g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, g0, g1, g2, g3, g4, g5, h0, h1, h2, h3, h4, h5] <;>
    ring

theorem isPGroup_uSub [CharP F 2] :
    IsPGroup 2 (uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) := by
  rintro ⟨_, c₀, c₁, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  change uSL c₀ c₁ ^ 2 = 1
  rw [sq, uSL_mul_uSL, ← two_mul, ← two_mul, h2, zero_mul, zero_mul, uSL_zero]

theorem plane_case [CharP F 2] {R₀ K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hR : R₀ ≤ uSub) (hR1 : R₀ ≠ ⊥)
    (hKR : K ≤ Subgroup.normalizer (R₀ : Set (SpecialLinearGroup (Fin 3) F)))
    (hRK : Subgroup.normalizer (R₀ : Set (SpecialLinearGroup (Fin 3) F)) ≤
      Subgroup.normalizer (K : Set (SpecialLinearGroup (Fin 3) F)))
    (hcore : ∀ N : Subgroup (SpecialLinearGroup (Fin 3) F), N ≤ K →
      K ≤ Subgroup.normalizer (N : Set (SpecialLinearGroup (Fin 3) F)) → IsPGroup 2 N → N ≤ R₀) :
    R₀ = uSub ∨ ∀ a ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆, ∀ b ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆, a * b = b * a := by
  have hKP : K ≤ planeStab := hKR.trans (normalizer_le_planeStab hR hR1)
  have hUN : (uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤
      Subgroup.normalizer (K : Set (SpecialLinearGroup (Fin 3) F)) := by
    refine le_trans ?_ hRK
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have : u * r * u⁻¹ = r := by rw [uSub_comm hu (hR hr)]; group
      rw [this]
      exact hr
    · intro hr
      have hr' : r = u⁻¹ * (u * r * u⁻¹) * u := by group
      rw [hr']
      have hm : u * r * u⁻¹ ∈ (uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) := hR hr
      have : u⁻¹ * (u * r * u⁻¹) * u = u * r * u⁻¹ := by
        rw [uSub_comm (uSub.inv_mem hu) hm]
        group
      rw [this]
      exact hr
  have hcoreU : (uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) ⊓ K ≤ R₀ := by
    refine hcore _ inf_le_right ?_ (isPGroup_uSub.to_le inf_le_left)
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hkU := (planeCoord (F := F)).le_normalizer (hKP hk)
    have hkK : k ∈ Subgroup.normalizer (K : Set (SpecialLinearGroup (Fin 3) F)) :=
      Subgroup.le_normalizer hk
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hkU x,
      Subgroup.mem_normalizer_iff.mp hkK x]
  rcases (planeCoord (F := F)).eq_or_le_centralizer hR hKP hUN hcoreU with h | h
  · exact Or.inl h
  · exact Or.inr fun a ha b hb => centralizer_comm (h ha) (h hb)

@[expose] def jMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem det_jMat : (jMat : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [det_fin_three]
  simp [jMat]

theorem jMat_mul_self : (jMat : Matrix (Fin 3) (Fin 3) F) * jMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def jSL : SpecialLinearGroup (Fin 3) F := ⟨jMat, det_jMat⟩

theorem jSL_mul_self : (jSL : SpecialLinearGroup (Fin 3) F) * jSL = 1 :=
  Subtype.ext jMat_mul_self

@[expose] def thetaFun (A : SpecialLinearGroup (Fin 3) F) : SpecialLinearGroup (Fin 3) F :=
  jSL * (SpecialLinearGroup.transpose A⁻¹) * jSL

theorem transpose_mul' (A B : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.transpose (A * B) =
      SpecialLinearGroup.transpose B * SpecialLinearGroup.transpose A := by
  apply Subtype.ext
  change ((A : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F))ᵀ =
    (B : Matrix (Fin 3) (Fin 3) F)ᵀ * (A : Matrix (Fin 3) (Fin 3) F)ᵀ
  exact Matrix.transpose_mul _ _

theorem transpose_one' :
    SpecialLinearGroup.transpose (1 : SpecialLinearGroup (Fin 3) F) = 1 := by
  apply Subtype.ext
  change (1 : Matrix (Fin 3) (Fin 3) F)ᵀ = 1
  exact Matrix.transpose_one

theorem transpose_inv' (A : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.transpose A⁻¹ = (SpecialLinearGroup.transpose A)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul', mul_inv_cancel, transpose_one']

theorem transpose_transpose' (A : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.transpose (SpecialLinearGroup.transpose A) = A := by
  apply Subtype.ext
  change ((A : Matrix (Fin 3) (Fin 3) F)ᵀ)ᵀ = A
  exact Matrix.transpose_transpose _

theorem thetaFun_mul (A B : SpecialLinearGroup (Fin 3) F) :
    thetaFun (A * B) = thetaFun A * thetaFun B := by
  simp only [thetaFun, _root_.mul_inv_rev, transpose_mul']
  have hJ : (jSL : SpecialLinearGroup (Fin 3) F) * jSL = 1 := jSL_mul_self
  calc jSL * (SpecialLinearGroup.transpose A⁻¹ * SpecialLinearGroup.transpose B⁻¹) * jSL
      = jSL * SpecialLinearGroup.transpose A⁻¹ * (jSL * jSL) *
          SpecialLinearGroup.transpose B⁻¹ * jSL := by rw [hJ]; group
    _ = _ := by group

theorem thetaFun_thetaFun (A : SpecialLinearGroup (Fin 3) F) : thetaFun (thetaFun A) = A := by
  have hJ : (jSL : SpecialLinearGroup (Fin 3) F) * jSL = 1 := jSL_mul_self
  have hJi : (jSL : SpecialLinearGroup (Fin 3) F)⁻¹ = jSL := inv_eq_of_mul_eq_one_right hJ
  have hJt : SpecialLinearGroup.transpose (jSL : SpecialLinearGroup (Fin 3) F) = jSL := by
    apply Subtype.ext
    change (jMat : Matrix (Fin 3) (Fin 3) F)ᵀ = jMat
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jMat]
  have key : ∀ X : SpecialLinearGroup (Fin 3) F, jSL * (jSL * X * jSL) * jSL = X := fun X => by
    calc jSL * (jSL * X * jSL) * jSL = (jSL * jSL) * X * (jSL * jSL) := by group
      _ = X := by rw [hJ, one_mul, mul_one]
  change jSL * SpecialLinearGroup.transpose (jSL * SpecialLinearGroup.transpose A⁻¹ * jSL)⁻¹ *
    jSL = A
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hJi, transpose_mul', transpose_mul', hJt,
    transpose_inv', transpose_transpose', inv_inv]
  simpa only [mul_assoc] using key A

@[expose] def theta : SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F where
  toFun := thetaFun
  invFun := thetaFun
  left_inv := thetaFun_thetaFun
  right_inv := thetaFun_thetaFun
  map_mul' := thetaFun_mul

@[expose] def vMat (a c : F) : Matrix (Fin 3) (Fin 3) F := !![1, a, c; 0, 1, 0; 0, 0, 1]

theorem det_vMat (a c : F) : (vMat a c).det = 1 := by
  rw [det_fin_three]
  simp [vMat]

@[expose] def vSL (a c : F) : SpecialLinearGroup (Fin 3) F := ⟨vMat a c, det_vMat a c⟩

theorem theta_uSL (c₀ c₁ : F) : theta (uSL c₀ c₁) = vSL c₁ (-c₀) := by
  apply Subtype.ext
  change ((jSL * SpecialLinearGroup.transpose (uSL c₀ c₁)⁻¹ * jSL : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) = vMat c₁ (-c₀)
  rw [uSL_inv]
  change jMat * (uMat (-c₀) (-c₁))ᵀ * jMat = vMat c₁ (-c₀)
  have ht : (uMat (-c₀) (-c₁))ᵀ = !![1, 0, 0; 0, 1, 0; -c₀, -c₁, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.transpose_apply]
  rw [ht, jMat, Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vMat]

theorem theta_vSL (a c : F) : theta (vSL a c) = uSL (-c) a := by
  have h := theta_uSL (F := F) (-c) a
  rw [neg_neg] at h
  rw [← h]
  exact thetaFun_thetaFun _

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem unitri_entries {t : SpecialLinearGroup (Fin 3) F} (ht : t ∈ unitriangular 3 F) :
    (t : Matrix (Fin 3) (Fin 3) F) =
      !![1, (t : Matrix (Fin 3) (Fin 3) F) 0 1, (t : Matrix (Fin 3) (Fin 3) F) 0 2;
        0, 1, (t : Matrix (Fin 3) (Fin 3) F) 1 2; 0, 0, 1] := by
  obtain ⟨hl, hd⟩ := ht
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hl, hd]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem le_uSub_or_le_vSub [CharP F 2] {R : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hR : R ≤ unitriangular 3 F) (hsq : ∀ r ∈ R, r * r = 1)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r) :
    (∀ r ∈ R, (r : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) ∨
      (∀ r ∈ R, (r : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hprod : ∀ r ∈ R,
      (r : Matrix (Fin 3) (Fin 3) F) 0 1 * (r : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    intro r hr
    have h : ((r : Matrix (Fin 3) (Fin 3) F) * (r : Matrix (Fin 3) (Fin 3) F)) 0 2 =
        (1 : Matrix (Fin 3) (Fin 3) F) 0 2 :=
      congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 2)
        (hsq r hr)
    rw [unitri_entries (hR hr)] at h
    simp [Matrix.mul_apply, Fin.sum_univ_three] at h
    linear_combination h - (r : Matrix (Fin 3) (Fin 3) F) 0 2 * h2
  have hcross : ∀ r ∈ R, ∀ s ∈ R, (r : Matrix (Fin 3) (Fin 3) F) 0 1 *
      (s : Matrix (Fin 3) (Fin 3) F) 1 2 =
        (s : Matrix (Fin 3) (Fin 3) F) 0 1 * (r : Matrix (Fin 3) (Fin 3) F) 1 2 := by
    intro r hr s hs
    have h : ((r : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F)) 0 2 =
        ((s : Matrix (Fin 3) (Fin 3) F) * (r : Matrix (Fin 3) (Fin 3) F)) 0 2 :=
      congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 2)
        (hcomm r hr s hs)
    rw [unitri_entries (hR hr), unitri_entries (hR hs)] at h
    simp [Matrix.mul_apply, Fin.sum_univ_three] at h
    linear_combination h
  by_cases hex : ∃ r ∈ R, (r : Matrix (Fin 3) (Fin 3) F) 0 1 ≠ 0
  · right
    obtain ⟨r, hr, hr0⟩ := hex
    intro s hs
    have h := hcross r hr s hs
    have hr12 : (r : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 :=
      (mul_eq_zero.mp (hprod r hr)).resolve_left hr0
    rw [hr12, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hr0
  · left
    push Not at hex
    exact hex

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem eq_uSL_of_unitri {t : SpecialLinearGroup (Fin 3) F} (ht : t ∈ unitriangular 3 F)
    (h : (t : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) :
    t = uSL ((t : Matrix (Fin 3) (Fin 3) F) 0 2) ((t : Matrix (Fin 3) (Fin 3) F) 1 2) := by
  apply Subtype.ext
  change (t : Matrix (Fin 3) (Fin 3) F) = uMat _ _
  rw [unitri_entries ht, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem eq_vSL_of_unitri {t : SpecialLinearGroup (Fin 3) F} (ht : t ∈ unitriangular 3 F)
    (h : (t : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) :
    t = vSL ((t : Matrix (Fin 3) (Fin 3) F) 0 1) ((t : Matrix (Fin 3) (Fin 3) F) 0 2) := by
  apply Subtype.ext
  change (t : Matrix (Fin 3) (Fin 3) F) = vMat _ _
  rw [unitri_entries ht, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vMat]

end CFSG.Quasithin.H13.KGL3Even
