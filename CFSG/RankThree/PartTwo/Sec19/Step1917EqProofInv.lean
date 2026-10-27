module

public import CFSG.RankThree.PartTwo.Sec19.Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofPar
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix
open CFSG.Assembly.RankThreeEven (projSL)

namespace Step1917EqProof

variable {F : Type} [Field F]

@[expose] noncomputable def rhoSL (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin 3) F →* projSL 3 F :=
  Matrix.SpecialLinearGroup.toPGL.codRestrict (projSL 3 F) fun s =>
    ⟨Matrix.SpecialLinearGroup.toGL s, MonoidHom.mem_ker.mpr (Units.ext (by simp)), rfl⟩

theorem rhoSL_surjective : Function.Surjective (rhoSL F) := by
  rintro ⟨w, g, hg, rfl⟩
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
    simpa using this
  refine ⟨(⟨g, hdet⟩ : Matrix.SpecialLinearGroup (Fin 3) F), Subtype.ext ?_⟩
  change ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
    (⟨g, hdet⟩ : Matrix.SpecialLinearGroup (Fin 3) F)) = ProjGenLinGroup.mk g
  congr 1
  exact Units.ext rfl

theorem rhoSL_eq_one_iff (s : Matrix.SpecialLinearGroup (Fin 3) F) :
    rhoSL F s = 1 ↔ s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
  rw [← Matrix.SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem diagE_inv (e : Fˣ) : (Sec4.diagE e)⁻¹ = Sec4.diagE e⁻¹ := by
  refine inv_eq_of_mul_eq_one_left (Units.ext ?_)
  rw [Units.val_mul, Sec4.coe_diagE, Sec4.coe_diagE, diagonal_mul_diagonal, Units.val_one,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem false_of_type2_of_inv [CharP F 2] {p f : ℕ} (hK : Sec4.PiField true p f F)
    (hq : Sec4.ModThree true (p ^ f)) {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {x t : GL (Fin 3) F} (hdet : (x : Matrix (Fin 3) (Fin 3) F).det = 1)
    (h2 : Sec4.Type123 true (p ^ f) F x 2) {ν : F} (hν : ν ^ 3 = 1)
    (hinv : ((t * x * t⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ν • ((x⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) : False := by
  obtain ⟨e, he3, he1, z, hz, g, -, hD⟩ := h2
  obtain ⟨ζ, rfl⟩ := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hM : g⁻¹ * x * g = Sec4.diagE e * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by
    have h1 : g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) ζ) * g =
        g⁻¹ * x * g * GeneralLinearGroup.scalar (Fin 3) ζ := by
      rw [mul_assoc g⁻¹ (x * _) g, mul_assoc x _ g, ← hsc ζ g]
      group
    rw [← hD, h1, map_inv, mul_inv_cancel_right]
  have hMi : g⁻¹ * x⁻¹ * g = Sec4.diagE e⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ := by
    have : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
    rw [this, hM, _root_.mul_inv_rev, map_inv, inv_inv, diagE_inv, hsc]
  have t1 := Sec4.trace_inv_conj g x
  rw [hM, Sec4.trace_mul_scalar, Sec4.trace_diagE, h2F, add_zero] at t1
  have t2 := Sec4.trace_inv_conj g x⁻¹
  rw [hMi, Sec4.trace_mul_scalar, Sec4.trace_diagE, h2F, add_zero] at t2
  have t3 := Sec4.trace_inv_conj t⁻¹ x
  rw [inv_inv, hinv, Matrix.trace_smul, smul_eq_mul] at t3
  have hd := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F).det)
    (congrArg (fun A => g * A * g⁻¹) hM)
  simp only [(show g * (g⁻¹ * x * g) * g⁻¹ = x by group), Units.val_mul, Matrix.det_mul,
    Sec4.coe_diagE, Matrix.det_diagonal, Fin.prod_univ_three] at hd
  rw [hdet, Sec4.det_scalar_three] at hd
  have hg : (g : Matrix (Fin 3) (Fin 3) F).det * ((g⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  set E : F := (e : F) with hE
  set Z : F := (ζ : F) with hZ
  have hE0 : E ≠ 0 := e.ne_zero
  have hZ0 : Z ≠ 0 := ζ.ne_zero
  have hZi : ((ζ⁻¹ : Fˣ) : F) = Z⁻¹ := by simp [hZ]
  have hEi : ((e⁻¹ : Fˣ) : F) = E⁻¹ := by simp [hE]
  rw [hZi] at t1 hd
  rw [hEi] at t2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_one] at hd
  have hZ3 : Z ^ 3 = E := by
    have h1 : (1 : F) = E * Z⁻¹ ^ 3 := by
      calc (1 : F) = (g : Matrix (Fin 3) (Fin 3) F).det * (E * Z⁻¹ ^ 3) *
            ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det := hd
        _ = E * Z⁻¹ ^ 3 * ((g : Matrix (Fin 3) (Fin 3) F).det * ((g⁻¹ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F).det) := by ring
        _ = E * Z⁻¹ ^ 3 := by rw [hg, mul_one]
    field_simp at h1
    exact h1
  have hE2 : E ^ 2 = ν * Z ^ 2 := by
    have h4 : Z⁻¹ * E = ν * (Z * E⁻¹) := by rw [t1, t2]; exact t3.symm
    field_simp at h4
    linear_combination h4
  have hE6 : E ^ 6 = E ^ 2 := by
    calc E ^ 6 = (E ^ 2) ^ 3 := by ring
      _ = ν ^ 3 * (Z ^ 3) ^ 2 := by rw [hE2]; ring
      _ = E ^ 2 := by rw [hν, hZ3, one_mul]
  have hE4 : E ^ 4 = 1 := by
    have h2' : E ^ 2 ≠ 0 := pow_ne_zero 2 hE0
    have : E ^ 2 * E ^ 4 = E ^ 2 * 1 := by rw [mul_one, ← pow_add]; exact hE6
    exact mul_left_cancel₀ h2' this
  have hE3 : E ^ 3 = 1 := he3
  apply he1
  apply Units.ext
  change E = 1
  calc E = E ^ 4 * (E ^ 3)⁻¹ := by field_simp
    _ = 1 := by rw [hE4, hE3, inv_one, one_mul]

theorem toGL_not_mem_zPi {p f : ℕ} (hK : Sec4.PiField true p f F)
    (hq : Sec4.ModThree true (p ^ f)) {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {b : Matrix.SpecialLinearGroup (Fin 3) F}
    (hb : b ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    Matrix.SpecialLinearGroup.toGL b ∉ Sec4.zPi true 3 (p ^ f) F := by
  intro hz
  apply hb
  obtain ⟨u, hu⟩ := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have hmat : (b : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (u : F) := by
    have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hu
    simp only [GeneralLinearGroup.coe_scalar] at this
    exact this.symm
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨u, ?_, hmat.symm⟩
  have hdet := b.2
  rw [hmat, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
    at hdet
  exact hdet

theorem toGL_pow_mem_zPi {p f : ℕ} {τ : F} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {b : Matrix.SpecialLinearGroup (Fin 3) F}
    (hb : b ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    Matrix.SpecialLinearGroup.toGL b ^ 3 ∈ Sec4.zPi true 3 (p ^ f) F := by
  obtain ⟨r, hr3, hr⟩ := Step1911EndProof.exists_scalar_of_mem_center hb
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hr3
  rw [Sec4.zPi_eq (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hτ hτ1]
  refine ⟨Sec4.mem_glPi_true _ _, Units.mk0 r hr0, Units.ext ?_⟩
  rw [← map_pow, GeneralLinearGroup.coe_scalar]
  change scalar (Fin 3) r =
    ((b ^ 3 : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  rw [hr]

theorem conj_scalar (g : GL (Fin 3) F) (r : F) :
    ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) r *
      (g : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) r := by
  rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem diagTau_entries_ne {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {i j : Fin 3} (hij : i ≠ j) :
    (![τ, τ ^ 2, 1] : Fin 3 → F) i ≠ ![τ, τ ^ 2, 1] j := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hτ, h, inv_one, one_mul]
  have h12 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [mul_one, ← pow_two]; exact h.symm
    exact mul_left_cancel₀ hτ0 this
  fin_cases i <;> fin_cases j <;>
    simp [h12, h12.symm, h2, hτ1, Ne.symm h2, Ne.symm hτ1] at hij ⊢

theorem conj_eq_diagonal {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {x y g : GL (Fin 3) F} (ζ : Fˣ)
    (hD : g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) ζ) * g = Sec4.diagTau hτ)
    (hxy : y * x = x * y) :
    ((g⁻¹ * y * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal fun i => ((g⁻¹ * y * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i := by
  have hs : y * GeneralLinearGroup.scalar (Fin 3) ζ = GeneralLinearGroup.scalar (Fin 3) ζ * y :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ y).eq
  have hc : (g⁻¹ * y * g) * Sec4.diagTau hτ = Sec4.diagTau hτ * (g⁻¹ * y * g) := by
    rw [← hD]
    have e1 : y * (x * GeneralLinearGroup.scalar (Fin 3) ζ) =
        x * GeneralLinearGroup.scalar (Fin 3) ζ * y := by
      rw [← mul_assoc, hxy, mul_assoc, hs, ← mul_assoc]
    have e2 : (g⁻¹ * y * g) * (g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) ζ) * g) =
        g⁻¹ * (y * (x * GeneralLinearGroup.scalar (Fin 3) ζ)) * g := by group
    rw [e2, e1]
    group
  have hm : ((g⁻¹ * y * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![τ, τ ^ 2, 1] =
      diagonal ![τ, τ ^ 2, 1] * ((g⁻¹ * y * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Sec4.coe_diagTau_eq_diagonal hτ, ← Units.val_mul, ← Units.val_mul, hc]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hij]
    exact Sec4.entry_eq_zero_of_commute_diagonal hm (diagTau_entries_ne hτ hτ1 hij)

theorem ksJParInvert :
    ∀ n : ℕ, 1 ≤ n → 2 ^ n % 3 = 1 →
      ∀ P : Subgroup (projSL 3 (GaloisField 2 n)), IsProperParabolic P →
      ∀ B : Subgroup (projSL 3 (GaloisField 2 n)), CFSG.Assembly.IsElemAbelian 3 B →
        Nat.card B = 9 → (∀ b ∈ B, ∀ p ∈ P, b * p * b⁻¹ ∈ P) →
        ∀ t : projSL 3 (GaloisField 2 n), (∀ b ∈ B, t * b * t⁻¹ = b⁻¹) → False := by
  intro n hn hq3 P hP B hB hB9 hBP t ht
  classical
  set F := GaloisField 2 n with hFdef
  have hK : Sec4.PiField true 2 n F := ⟨Nat.prime_two, hn, by
    rw [GaloisField.card 2 n (by omega)]
    rfl⟩
  have hq : Sec4.ModThree true (2 ^ n) := hq3
  obtain ⟨τ, hτ3, hτ1⟩ := Sec4.exists_tau hK hq
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  set ρ := rhoSL F with hρdef
  have hρ : Function.Surjective ρ := rhoSL_surjective
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hBc : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  obtain ⟨W, hW0, hWtop, hWinv⟩ := exists_uniform_invariant_of_surjective ρ hρ hP
  set Bh := B.comap ρ with hBh
  have hBhW : ∀ b ∈ Bh, ∀ v ∈ W, (b : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
    intro b hb
    refine hWinv (Matrix.SpecialLinearGroup.toGL b) (fun s hs => ?_)
    rw [Step1911EndProof.glConj_toGL, map_mul, map_mul, map_inv]
    exact hBP _ hb _ hs
  have hd0 : Module.finrank F W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hd3 : Module.finrank F W < 3 := by
    have := Submodule.finrank_lt hWtop
    rwa [Module.finrank_fin_fun] at this
  have hcomm : ∀ b₁ ∈ Bh, ∀ b₂ ∈ Bh, b₁ * b₂ = b₂ * b₁ := by
    intro b₁ hb₁ b₂ hb₂
    have hc1 : ρ (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hBc _ hb₁ _ hb₂]
      group
    obtain ⟨r, hr3, hr⟩ := Step1911EndProof.exists_scalar_of_mem_center
      ((rhoSL_eq_one_iff _).mp hc1)
    have hAB : (b₁ : Matrix (Fin 3) (Fin 3) F) * b₂ =
        r • ((b₂ : Matrix (Fin 3) (Fin 3) F) * b₁) := by
      have e1 : b₁ * b₂ = (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * (b₂ * b₁) := by group
      have e2 := congrArg
        (fun s : Matrix.SpecialLinearGroup (Fin 3) F => (s : Matrix (Fin 3) (Fin 3) F)) e1
      rw [Matrix.SpecialLinearGroup.coe_mul b₁ b₂,
        Matrix.SpecialLinearGroup.coe_mul (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) (b₂ * b₁),
        Matrix.SpecialLinearGroup.coe_mul b₂ b₁, hr] at e2
      rw [e2, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    have hpow := Step1911EndProof.pow_finrank_eq_one (Matrix.SpecialLinearGroup.toGL b₁).isUnit
      (Matrix.SpecialLinearGroup.toGL b₂).isUnit hAB (hBhW b₁ hb₁) (hBhW b₂ hb₂)
    have hr1 : r = 1 := by
      have hdim : Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by omega
      rcases hdim with h | h
      · rw [h, pow_one] at hpow
        exact hpow
      · rw [h] at hpow
        linear_combination hr3 - r * hpow
    rw [hr1, one_smul] at hAB
    exact Subtype.ext hAB
  have hcube : ∀ b ∈ Bh, b ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    fun b hb => (rhoSL_eq_one_iff _).mp (by rw [map_pow]; exact hB.2 _ hb)
  obtain ⟨th, hth⟩ := hρ t
  have hinvc : ∀ b ∈ Bh,
      th * b * th⁻¹ * b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    fun b hb => (rhoSL_eq_one_iff _).mp (by
      rw [map_mul, map_mul, map_mul, map_inv, hth, ht _ hb, inv_mul_cancel])
  have htype : ∀ b ∈ Bh, b ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) →
      Sec4.Type123 true (2 ^ n) F (Matrix.SpecialLinearGroup.toGL b) 1 := by
    intro b hb hbc
    rcases Sec4.type123_exhaust hK hq (Sec4.mem_glPi_true _ _)
        (toGL_not_mem_zPi hK hq hτ3 hτ1 hbc) (toGL_pow_mem_zPi hτ3 hτ1 (hcube b hb)) with
      h1 | h2 | h3
    · exact h1
    · exfalso
      obtain ⟨ν, hν3, hν⟩ := Step1911EndProof.exists_scalar_of_mem_center (hinvc b hb)
      refine false_of_type2_of_inv hK hq hτ3 hτ1 (t := Matrix.SpecialLinearGroup.toGL th)
        (by simp) h2 hν3 ?_
      have e1 : th * b * th⁻¹ = (th * b * th⁻¹ * b) * b⁻¹ := by group
      change ((th * b * th⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = ν • ((b⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F)
      rw [e1, Matrix.SpecialLinearGroup.coe_mul (th * b * th⁻¹ * b) b⁻¹, hν, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    · exfalso
      rcases h3.2.2 W (hBhW b hb) with h | h
      · exact hW0 h
      · exact hWtop h
  obtain ⟨y, hyB, hy1⟩ : ∃ y ∈ B, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall B).mpr hcon, Subgroup.card_bot] at hB9
    norm_num at hB9
  obtain ⟨b₀, rfl⟩ := hρ y
  have hb₀ : b₀ ∈ Bh := hyB
  have hb₀c : b₀ ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    fun h => hy1 ((rhoSL_eq_one_iff _).mpr h)
  obtain ⟨τ', hτ', hτ'1, z, hz, g, -, hD⟩ := htype b₀ hb₀ hb₀c
  obtain ⟨ζ, rfl⟩ := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ3 hτ1 hz
  obtain ⟨N, hN⟩ : ∃ N : Matrix.SpecialLinearGroup (Fin 3) F → GL (Fin 3) F,
      ∀ b, N b = g⁻¹ * Matrix.SpecialLinearGroup.toGL b * g := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Matrix.SpecialLinearGroup (Fin 3) F → Fin 3 → F,
      ∀ b i, u b i = (N b : Matrix (Fin 3) (Fin 3) F) i i := ⟨_, fun _ _ => rfl⟩
  have hdiag : ∀ b ∈ Bh, (N b : Matrix (Fin 3) (Fin 3) F) = diagonal (u b) := by
    intro b hb
    rw [hN]
    refine (conj_eq_diagonal hτ' hτ'1 ζ hD (by rw [← map_mul, ← map_mul, hcomm b hb b₀ hb₀])).trans
      ?_
    congr 1
    funext i
    rw [hu, hN]
  have hNmul : ∀ b b', N (b * b') = N b * N b' := fun b b' => by
    rw [hN, hN, hN, map_mul]
    group
  have hmulu : ∀ b ∈ Bh, ∀ b' ∈ Bh, ∀ i, u (b * b') i = u b i * u b' i := by
    intro b hb b' hb' i
    rw [hu, hNmul, Units.val_mul, hdiag b hb, hdiag b' hb', diagonal_mul_diagonal,
      diagonal_apply_eq]
  have hone : ∀ i, u 1 i = 1 := fun i => by
    rw [hu, hN, map_one, mul_one, inv_mul_cancel, Units.val_one, one_apply_eq]
  have hinvu : ∀ b ∈ Bh, ∀ i, u b i * u b⁻¹ i = 1 := fun b hb i => by
    rw [← hmulu b hb b⁻¹ (Bh.inv_mem hb) i, mul_inv_cancel, hone]
  have hne0 : ∀ b ∈ Bh, ∀ i, u b i ≠ 0 := fun b hb i =>
    left_ne_zero_of_mul_eq_one (hinvu b hb i)
  have hcubeu : ∀ b ∈ Bh, u b 0 ^ 3 = u b 1 ^ 3 := by
    intro b hb
    obtain ⟨r, -, hr⟩ := Step1911EndProof.exists_scalar_of_mem_center (hcube b hb)
    have hb2 : b * b ∈ Bh := Bh.mul_mem hb hb
    have hpow : ∀ i, u b i ^ 3 = r := by
      intro i
      have e1 : u (b * b * b) i = u b i ^ 3 := by
        rw [hmulu _ hb2 _ hb, hmulu _ hb _ hb]
        ring
      rw [← e1, ← pow_three' b, hu, hN, Units.val_mul, Units.val_mul,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hr, conj_scalar, scalar_apply,
        diagonal_apply_eq]
    rw [hpow, hpow]
  have hker : ∀ c ∈ Bh, u c 0 = u c 1 →
      c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    intro c hc h01
    by_contra hcc
    have htr := Sec4.trace_eq_zero_of_type1 hK hq (htype c hc hcc)
    rw [← Sec4.trace_inv_conj g, ← hN, Matrix.trace_fin_three, ← hu, ← hu, ← hu, h01,
      ← two_mul, h2F, zero_mul, zero_add] at htr
    exact hne0 c hc 2 htr
  obtain ⟨sec, hsec⟩ : ∃ sec : projSL 3 F → Matrix.SpecialLinearGroup (Fin 3) F,
      ∀ y, ρ (sec y) = y := ⟨Function.surjInv hρ, Function.surjInv_eq hρ⟩
  have hsecB : ∀ y ∈ B, sec y ∈ Bh := fun y hy => by
    show ρ (sec y) ∈ B
    rw [hsec]
    exact hy
  let χ : B → rootsOfUnity 3 F := fun y =>
    ⟨Units.mk0 (u (sec y) 0 / u (sec y) 1)
      (div_ne_zero (hne0 _ (hsecB _ y.2) 0) (hne0 _ (hsecB _ y.2) 1)), by
      rw [mem_rootsOfUnity', Units.val_mk0, div_pow, hcubeu _ (hsecB _ y.2),
        div_self (pow_ne_zero _ (hne0 _ (hsecB _ y.2) 1))]⟩
  have hχ : Function.Injective χ := by
    intro y y' h
    have h' : u (sec y) 0 / u (sec y) 1 = u (sec y') 0 / u (sec y') 1 := by
      have := congrArg (fun w : rootsOfUnity 3 F => ((w : Fˣ) : F)) h
      simpa [χ] using this
    have hb := hsecB _ y.2
    have hb' := hsecB _ y'.2
    rw [div_eq_div_iff (hne0 _ hb 1) (hne0 _ hb' 1)] at h'
    have hcB : sec y * (sec y')⁻¹ ∈ Bh := Bh.mul_mem hb (Bh.inv_mem hb')
    have hc01 : u (sec y * (sec y')⁻¹) 0 = u (sec y * (sec y')⁻¹) 1 := by
      rw [hmulu _ hb _ (Bh.inv_mem hb'), hmulu _ hb _ (Bh.inv_mem hb')]
      have e0 := hinvu _ hb' 0
      have e1 := hinvu _ hb' 1
      linear_combination (-(u (sec y) 0 * u (sec y')⁻¹ 0)) * e1 +
        (u (sec y')⁻¹ 0 * u (sec y')⁻¹ 1) * h' + (u (sec y) 1 * u (sec y')⁻¹ 1) * e0
    have h1 : ρ (sec y * (sec y')⁻¹) = 1 := (rhoSL_eq_one_iff _).mpr (hker _ hcB hc01)
    rw [map_mul, map_inv, hsec, hsec, mul_inv_eq_one] at h1
    exact Subtype.ext h1
  have hle := (Nat.card_le_card_of_injective χ hχ).trans (card_rootsOfUnity (R := F) 3)
  rw [hB9] at hle
  norm_num at hle

end Step1917EqProof

end CFSG.RankThree.PartTwo.Sec19
