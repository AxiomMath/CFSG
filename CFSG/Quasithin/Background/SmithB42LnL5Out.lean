module

public import CFSG.Quasithin.Background.SmithB42LnL5Six
public import CFSG.Quasithin.Background.SmithB42LnL5Rad
public import CFSG.Quasithin.Background.SmithB42LnBase
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Background.SmithB51LnSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix
open CFSG.Assembly.LowTwoRank

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

theorem det_eq_one_GL (M : GL (Fin 5) (ZMod 2)) : (M : 𝕄).det = 1 := by
  have hu : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by decide
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact hu _

@[expose] def ofGL5 (M : GL (Fin 5) (ZMod 2)) : G5 := ⟨M, det_eq_one_GL M⟩

theorem GL_mul_inv (M : GL (Fin 5) (ZMod 2)) : (M : 𝕄) * ((M⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem GL_inv_mul (M : GL (Fin 5) (ZMod 2)) : ((M⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) * (M : 𝕄) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem ofGL5_inv (M : GL (Fin 5) (ZMod 2)) : (ofGL5 M)⁻¹ = ofGL5 M⁻¹ :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (GL_mul_inv M))

theorem add_self_mat (M : 𝕄) : M + M = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize M i j = a
  revert a
  decide

theorem mul_self_zmod2 (a : ZMod 2) : a * a = a := by
  revert a
  decide

theorem sum_sum_symm (f : Fin 5 → Fin 5 → ZMod 2) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, f i i := by
  simp only [Fin.sum_univ_five]
  rw [hf 1 0, hf 2 0, hf 3 0, hf 4 0, hf 2 1, hf 3 1, hf 4 1, hf 3 2, hf 4 2, hf 4 3]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 1 2 + f 1 3 + f 1 4 + f 2 3 + f 2 4 +
    f 3 4) * h2

theorem dotProduct_mulVec_self {M : 𝕄} (hM : Mᵀ = M) (x : Fin 5 → ZMod 2) :
    x ⬝ᵥ (M *ᵥ x) = (fun i => M i i) ⬝ᵥ x := by
  have hMs : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    rwa [transpose_apply] at this
  have hf : ∀ i j, x i * (M i j * x j) = x j * (M j i * x i) := fun i j => by
    rw [hMs i j]
    ring
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [sum_sum_symm _ hf]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc x i * (M i i * x i) = M i i * (x i * x i) := by ring
    _ = M i i * x i := by rw [mul_self_zmod2]

noncomputable abbrev E5 : G5 ≃* ↥(StatedSL 5 (ZMod 2)) :=
  specialLinearGroupEquivStatedSL 5 (ZMod 2)

theorem mat_E5 (x : G5) : B5.Ln.mat (E5 x) = (x : 𝕄) := rfl

theorem coe_E5_symm (y : ↥(StatedSL 5 (ZMod 2))) : ((E5.symm y : G5) : 𝕄) = B5.Ln.mat y := by
  conv_rhs => rw [← E5.apply_symm_apply y]
  rfl

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

noncomputable abbrev phiOf (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) : ↥L ≃* G5 := e.trans E5.symm

omit [Finite V] in
theorem phiOf_symm_apply (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (x : G5) :
    (phiOf e).symm x = e.symm (E5 x) := by
  simp [phiOf]

@[expose] noncomputable def conjG5 (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2)))
    {g : MulAut V} (hg : g ∈ G) : G5 ≃* G5 :=
  (E5.trans (conjAut h e hg)).trans E5.symm

theorem E5_conjG5 (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (x : G5) : E5 (conjG5 h e hg x) = conjAut h e hg (E5 x) := by
  simp [conjG5]

theorem conjG5_spec (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (x : G5) :
    (((phiOf e).symm (conjG5 h e hg x) : ↥L) : MulAut V) =
      g * (((phiOf e).symm x : ↥L) : MulAut V) * g⁻¹ := by
  rw [phiOf_symm_apply, phiOf_symm_apply, E5_conjG5, conjAut_spec]

theorem coe_conjG5 (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (x : G5) :
    ((conjG5 h e hg x : G5) : 𝕄) = B5.Ln.mat (conjAut h e hg (E5 x)) := by
  rw [← E5_conjG5]
  rfl

theorem exists_conjG5_eq (h : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {g : MulAut V} (hg : g ∈ G) (hgL : g ∉ L) :
    ∃ P : GL (Fin 5) (ZMod 2), ∀ x : G5, ((conjG5 h e hg x : G5) : 𝕄) =
      (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) := by
  obtain ⟨P, hP⟩ := outer_of_not_mem h hZ (by norm_num) e hg hgL
  refine ⟨P, fun x => ?_⟩
  rw [coe_conjG5, hP, B5.Ln.dmat, ← map_inv]
  rfl

theorem mem_of_conjG5_eq (h : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {g : MulAut V} (hg : g ∈ G) (M : GL (Fin 5) (ZMod 2))
    (hM : ∀ x : G5, ((conjG5 h e hg x : G5) : 𝕄) =
      (M : 𝕄) * (x : 𝕄) * ((M⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)) : g ∈ L := by
  set m : G5 := ofGL5 M
  have hm : ∀ x : G5, conjG5 h e hg x = m * x * m⁻¹ := fun x => by
    apply Subtype.ext
    rw [hM, ofGL5_inv]
    rfl
  refine mem_of_inner h hZ hg ((phiOf e).symm m).2 fun x hx => ?_
  obtain ⟨y, hy⟩ := (phiOf e).symm.surjective ⟨x, hx⟩
  have hx' : x = (((phiOf e).symm y : ↥L) : MulAut V) := by rw [hy]
  rw [hx', ← conjG5_spec h e hg y, hm y, map_mul, map_mul, map_inv]
  rfl

theorem mul_mem_of_not_mem (h : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {g₁ g₂ : MulAut V} (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G)
    (h₁ : g₁ ∉ L) (h₂ : g₂ ∉ L) : g₁ * g₂ ∈ L := by
  obtain ⟨P₁, hP₁⟩ := exists_conjG5_eq h hZ e hg₁ h₁
  obtain ⟨P₂, hP₂⟩ := exists_conjG5_eq h hZ e hg₂ h₂
  have hcomp : ∀ x, conjG5 h e (G.mul_mem hg₁ hg₂) x = conjG5 h e hg₁ (conjG5 h e hg₂ x) := by
    intro x
    apply (phiOf e).symm.injective
    apply Subtype.ext
    rw [conjG5_spec, conjG5_spec, conjG5_spec]
    group
  refine mem_of_conjG5_eq h hZ e (G.mul_mem hg₁ hg₂) (P₁ * B5.Ln.invT P₂) fun x => ?_
  rw [hcomp, hP₁, ← map_inv, hP₂, inv_inv]
  have e1 : ((P₁ * B5.Ln.invT P₂ : GL (Fin 5) (ZMod 2)) : 𝕄) =
      (P₁ : 𝕄) * ((P₂⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)ᵀ := rfl
  have e2 : (((P₁ * B5.Ln.invT P₂)⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) =
      (P₂ : 𝕄)ᵀ * ((P₁⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) := rfl
  rw [e1, e2, transpose_mul, transpose_mul, transpose_transpose]
  simp only [Matrix.mul_assoc]

theorem transpose_P (h : B4Hyp G L) (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {g : MulAut V}
    (hg : g ∈ G) (hg2 : g * g = 1) {P : GL (Fin 5) (ZMod 2)}
    (hP : ∀ x : G5, ((conjG5 h e hg x : G5) : 𝕄) =
      (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)) :
    (P : 𝕄)ᵀ = P := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hinv : ∀ x, conjG5 h e hg (conjG5 h e hg x) = x := by
    intro x
    apply (phiOf e).symm.injective
    apply Subtype.ext
    rw [conjG5_spec, conjG5_spec, hginv]
    calc g * (g * (((phiOf e).symm x : ↥L) : MulAut V) * g) * g =
        (g * g) * (((phiOf e).symm x : ↥L) : MulAut V) * (g * g) := by group
      _ = (((phiOf e).symm x : ↥L) : MulAut V) := by rw [hg2, one_mul, mul_one]
  set p : 𝕄 := (P : 𝕄) with hp
  set q : 𝕄 := ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) with hq
  have hqp : q * p = 1 := GL_inv_mul P
  have hN : ∀ x : G5, p * qᵀ * (x : 𝕄) = (x : 𝕄) * (p * qᵀ) := by
    intro x
    have h1 : ((conjG5 h e hg (conjG5 h e hg x) : G5) : 𝕄) = (x : 𝕄) := by rw [hinv x]
    rw [hP, ← map_inv, hP, inv_inv, transpose_mul, transpose_mul, transpose_transpose] at h1
    conv_rhs => rw [← h1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc q p, hqp, Matrix.one_mul, ← transpose_mul, hqp, transpose_one,
      Matrix.mul_one]
  have hN1 : P * B5.Ln.invT P = 1 := by
    have h1 := B5.Ln.eq_one_of_forall_commute (n := 5) (z := B5.Ln.ofGL (P * B5.Ln.invT P))
      fun γ => by
        apply B5.Ln.mat_injective
        rw [B5.Ln.mat_mul, B5.Ln.mat_mul, B5.Ln.mat_ofGL, ← coe_E5_symm γ]
        exact hN (E5.symm γ)
    have h2 := congrArg B5.Ln.mat h1
    rw [B5.Ln.mat_ofGL, B5.Ln.mat_one] at h2
    exact Units.ext h2
  have h3 : p * qᵀ = 1 := congrArg (fun M : GL (Fin 5) (ZMod 2) => (M : 𝕄)) hN1
  have h4 : qᵀ * p = 1 := (mul_eq_one_comm_of_card_eq (Fin 5) (Fin 5) (ZMod 2) rfl).mp h3
  calc pᵀ = pᵀ * (qᵀ * p) := by rw [h4, Matrix.mul_one]
    _ = (q * p)ᵀ * p := by rw [transpose_mul, Matrix.mul_assoc]
    _ = p := by rw [hqp, transpose_one, Matrix.one_mul]

section Graph

variable {σ : G5 ≃* G5} {P : GL (Fin 5) (ZMod 2)}

theorem IsTv.mul_self {b : G5} {v ψ : Fin 5 → ZMod 2} (h : IsTv b v ψ) : b * b = 1 := by
  apply Subtype.ext
  show (b : 𝕄) * (b : 𝕄) = 1
  rw [h.1, tv_mul_tv, h.2.2.2, zero_smul, add_zero, add_assoc, add_self_mat, add_zero]

theorem tv_fixed
    (hσ : ∀ x : G5, ((σ x : G5) : 𝕄) =
      (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄))
    {b : G5} (hb : σ b = b) {v ψ : Fin 5 → ZMod 2} (ht : IsTv b v ψ) :
    v = (P : 𝕄) *ᵥ ψ ∧ ψ = v ᵥ* ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) := by
  set p : 𝕄 := (P : 𝕄)
  set q : 𝕄 := ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)
  have hpq : p * q = 1 := GL_mul_inv P
  have hqp : q * p = 1 := GL_inv_mul P
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right ht.mul_self
  have hσb : ((σ b : G5) : 𝕄) = 1 + vecMulVec (p *ᵥ ψ) (v ᵥ* q) := by
    rw [hσ, hbinv, ht.1, transpose_add, transpose_one, transpose_vecMulVec, Matrix.mul_add,
      Matrix.mul_one, Matrix.add_mul, hpq, mul_vecMulVec, vecMulVec_mul]
  have ht' : IsTv b (p *ᵥ ψ) (v ᵥ* q) := by
    refine ⟨by rw [← hσb, hb], fun h0 => ?_, fun h0 => ?_, ?_⟩
    · apply ht.2.2.1
      have := congrArg (q *ᵥ ·) h0
      simpa [mulVec_mulVec, hqp] using this
    · apply ht.2.1
      have := congrArg (· ᵥ* p) h0
      simpa [vecMul_vecMul, hqp] using this
    · rw [dotProduct_mulVec, vecMul_vecMul, hqp, vecMul_one, dotProduct_comm]
      exact ht.2.2.2
  exact ht.unique ht'

theorem card_le_two_of_center
    (hσ : ∀ x : G5, ((σ x : G5) : 𝕄) =
      (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄))
    {E : Subgroup G5} (hfix : ∀ b ∈ E, σ b = b) {v : Fin 5 → ZMod 2}
    (hE : ∀ b ∈ E, b ≠ 1 → ∃ ψ, IsTv b v ψ) : Nat.card E ≤ 2 := by
  classical
  have key : ∀ b ∈ E, b ≠ 1 →
      (b : 𝕄) = 1 + vecMulVec v (v ᵥ* ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)) := by
    intro b hb hb1
    obtain ⟨ψ, hψ⟩ := hE b hb hb1
    rw [hψ.1, ← (tv_fixed hσ (hfix b hb) hψ).2]
  have hinj : Function.Injective fun b : ↥E => decide ((b : G5) = 1) := by
    intro b b' hbb
    by_cases h1 : (b : G5) = 1 <;> by_cases h1' : (b' : G5) = 1
    · exact Subtype.ext (h1.trans h1'.symm)
    · simp [h1, h1'] at hbb
    · simp [h1, h1'] at hbb
    · exact Subtype.ext (Subtype.ext ((key b b.2 h1).trans (key b' b'.2 h1').symm))
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem card_le_two_of_axis
    (hσ : ∀ x : G5, ((σ x : G5) : 𝕄) =
      (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄))
    {E : Subgroup G5} (hfix : ∀ b ∈ E, σ b = b) {ψ : Fin 5 → ZMod 2}
    (hE : ∀ b ∈ E, b ≠ 1 → ∃ v, IsTv b v ψ) : Nat.card E ≤ 2 := by
  classical
  have key : ∀ b ∈ E, b ≠ 1 → (b : 𝕄) = 1 + vecMulVec ((P : 𝕄) *ᵥ ψ) ψ := by
    intro b hb hb1
    obtain ⟨v, hv⟩ := hE b hb hb1
    rw [hv.1, ← (tv_fixed hσ (hfix b hb) hv).1]
  have hinj : Function.Injective fun b : ↥E => decide ((b : G5) = 1) := by
    intro b b' hbb
    by_cases h1 : (b : G5) = 1 <;> by_cases h1' : (b' : G5) = 1
    · exact Subtype.ext (h1.trans h1'.symm)
    · simp [h1, h1'] at hbb
    · simp [h1, h1'] at hbb
    · exact Subtype.ext (Subtype.ext ((key b b.2 h1).trans (key b' b'.2 h1').symm))
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem eT_mul_self (i j : Fin 5) (h : i ≠ j) : eT i j h * eT i j h = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_eT, eTM_mul_self i j h,
    Matrix.SpecialLinearGroup.coe_one]

theorem row_eq_zero_of_comm (M : 𝕄) (h0 : eTM 0 4 * M = M * (eTM 0 4)ᵀ)
    (h1 : eTM 1 4 * M = M * (eTM 1 4)ᵀ) : ∀ b, M 4 b = 0 := by
  intro b
  fin_cases b
  · have := congrFun (congrFun h1 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_five, eTMc] using this
  · have := congrFun (congrFun h0 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_five, eTMc] using this
  · have := congrFun (congrFun h0 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_five, eTMc] using this
  · have := congrFun (congrFun h0 0) 3
    simpa [Matrix.mul_apply, Fin.sum_univ_five, eTMc] using this
  · have := congrFun (congrFun h0 0) 4
    simpa [Matrix.mul_apply, Fin.sum_univ_five, eTMc] using this

theorem card_le_32_of_fixed
    (hσ : ∀ x : G5, ((σ x : G5) : 𝕄) =
      (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄))
    {E : Subgroup G5} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1)
    (hfix : ∀ b ∈ E, σ b = b) : Nat.card E ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq E h2
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have h64 := card_le_of_elemAbelian hc h2
  rw [hk] at h64 ⊢
  by_contra hgt
  have hk6 : k = 6 := by
    rcases Nat.lt_or_ge k 6 with hlt | hge
    · have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · rcases Nat.lt_or_ge 6 k with hlt' | hle
      · have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt'
        omega
      · omega
  subst hk6
  obtain ⟨h, hh⟩ := exists_conj_le_Ugrp hp
  set E' : Subgroup G5 := E.map (MulAut.conj h).toMonoidHom with hE'
  have hcard : Nat.card E' = 64 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective, hk]
    norm_num
  have hE'U : E' ≤ Ugrp := by
    rintro _ ⟨a, ha, rfl⟩
    exact hh a ha
  have hc' : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hc a ha b hb
    calc h * a * h⁻¹ * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
      _ = h * (b * a) * h⁻¹ := by rw [this]
      _ = h * b * h⁻¹ * (h * a * h⁻¹) := by group
  have h2' : ∀ a ∈ E', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
      _ = 1 := by rw [h2 a ha]; group
  obtain ⟨m0, m1⟩ := mem_of_card_eq_64 hE'U hc' h2' hcard
  set p : 𝕄 := (P : 𝕄)
  set q : 𝕄 := ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)
  have hqp : q * p = 1 := GL_inv_mul P
  set hm : 𝕄 := (h : 𝕄)
  set hi : 𝕄 := ((h⁻¹ : G5) : 𝕄)
  have hhi : hm * hi = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key : ∀ t ∈ E', t * t = 1 → (t : 𝕄) * (hm * p * hmᵀ) = (hm * p * hmᵀ) * (t : 𝕄)ᵀ := by
    rintro _ ⟨b, hb, rfl⟩ ht2
    set t : G5 := (MulAut.conj h).toMonoidHom b with ht
    have hbt : b = h⁻¹ * t * h := by
      rw [ht]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hbinv : b⁻¹ = h⁻¹ * t * h := by
      calc b⁻¹ = (h⁻¹ * t * h)⁻¹ := congrArg (·⁻¹) hbt
        _ = h⁻¹ * t⁻¹ * h := by group
        _ = h⁻¹ * t * h := by rw [htinv]
    have hfixm : hi * (t : 𝕄) * hm = p * (hmᵀ * (t : 𝕄)ᵀ * hiᵀ) * q := by
      have h1 := hσ b
      rw [hfix b hb, hbinv] at h1
      rw [hbt] at h1
      simp only [Matrix.SpecialLinearGroup.coe_mul, transpose_mul] at h1
      rw [h1]
      simp only [Matrix.mul_assoc]
      rfl
    calc (t : 𝕄) * (hm * p * hmᵀ) = hm * (hi * (t : 𝕄) * hm) * p * hmᵀ := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc hm hi, hhi, Matrix.one_mul]
      _ = hm * (p * (hmᵀ * (t : 𝕄)ᵀ * hiᵀ) * q) * p * hmᵀ := by rw [hfixm]
      _ = hm * p * hmᵀ * (t : 𝕄)ᵀ * (hiᵀ * (q * p) * hmᵀ) := by simp only [Matrix.mul_assoc]
      _ = hm * p * hmᵀ * (t : 𝕄)ᵀ := by
          rw [hqp, Matrix.mul_one, ← transpose_mul, hhi, transpose_one, Matrix.mul_one]
  have k0 := key _ m0 (eT_mul_self 0 4 _)
  have k1 := key _ m1 (eT_mul_self 1 4 _)
  rw [coe_eT] at k0 k1
  have hrow := row_eq_zero_of_comm _ k0 k1
  have hdet : (hm * p * hmᵀ).det = 0 := Matrix.det_eq_zero_of_row_eq_zero 4 hrow
  rw [det_mul, det_mul, det_transpose, h.2, det_eq_one_GL P] at hdet
  simp at hdet

theorem exists_v_ne : ∀ d : Fin 5 → ZMod 2, ∃ v : Fin 5 → ZMod 2, v ≠ 0 ∧ d ⬝ᵥ v = 0 := by
  decide

theorem eight_le_card_orth (d v : Fin 5 → ZMod 2) :
    8 ≤ Nat.card {ψ : Fin 5 → ZMod 2 // d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0} := by
  set f : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) := (Matrix.of ![d, v]).mulVecLin with hf
  have hker : ∀ ψ, ψ ∈ LinearMap.ker f ↔ d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0 := by
    intro ψ
    rw [LinearMap.mem_ker, hf, Matrix.mulVecLin_apply]
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i
      · exact h0
      · exact h1
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hr : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun] at hrank
  have hk : 3 ≤ Module.finrank (ZMod 2) (LinearMap.ker f) := by omega
  have : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hcard
  have e : ↥(LinearMap.ker f) ≃ {ψ : Fin 5 → ZMod 2 // d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0} :=
    Equiv.subtypeEquivRight hker
  rw [← Nat.card_congr e, hcard]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ _ := Nat.pow_le_pow_right (by norm_num) hk

theorem exists_orth_ne (d v u : Fin 5 → ZMod 2) :
    ∃ ψ : Fin 5 → ZMod 2, ψ ≠ 0 ∧ ψ ≠ u ∧ d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0 := by
  classical
  by_contra hall'
  have hall : ∀ ψ : Fin 5 → ZMod 2, ψ ≠ 0 → d ⬝ᵥ ψ = 0 → v ⬝ᵥ ψ = 0 → ψ = u :=
    fun ψ h0 hd hv => by_contra fun hne => hall' ⟨ψ, h0, hne, hd, hv⟩
  have hinj : Function.Injective fun ψ : {ψ : Fin 5 → ZMod 2 // d ⬝ᵥ ψ = 0 ∧ v ⬝ᵥ ψ = 0} =>
      decide ((ψ : Fin 5 → ZMod 2) = 0) := by
    intro ψ ψ' h
    by_cases h1 : (ψ : Fin 5 → ZMod 2) = 0 <;> by_cases h1' : (ψ' : Fin 5 → ZMod 2) = 0
    · exact Subtype.ext (h1.trans h1'.symm)
    · simp [h1, h1'] at h
    · simp [h1, h1'] at h
    · exact Subtype.ext ((hall ψ h1 ψ.2.1 ψ.2.2).trans (hall ψ' h1' ψ'.2.1 ψ'.2.2).symm)
  have h2 := Nat.card_le_card_of_injective _ hinj
  have h8 := eight_le_card_orth d v
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool] at h2 h8
  omega

theorem exists_conj_mul_inv (hPs : (P : 𝕄)ᵀ = P)
    (hσ : ∀ x : G5, ((σ x : G5) : 𝕄) =
      (P : 𝕄) * ((x⁻¹ : G5) : 𝕄)ᵀ * ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄)) :
    ∃ γ : G5, γ * γ = 1 ∧ σ γ * γ ≠ 1 ∧ σ γ * γ * (σ γ * γ) = 1 := by
  set p : 𝕄 := (P : 𝕄) with hp
  set q : 𝕄 := ((P⁻¹ : GL (Fin 5) (ZMod 2)) : 𝕄) with hq
  have hpq : p * q = 1 := GL_mul_inv P
  have hqp : q * p = 1 := GL_inv_mul P
  have hqs : qᵀ = q := by
    calc qᵀ = qᵀ * (p * q) := by rw [hpq, Matrix.mul_one]
      _ = (p * q)ᵀ * q := by rw [transpose_mul, hPs, Matrix.mul_assoc]
      _ = q := by rw [hpq, transpose_one, Matrix.one_mul]
  obtain ⟨v, hv0, hvq⟩ := exists_v_ne (fun i => q i i)
  obtain ⟨ψ, hψ0, hψq, hdψ, hvψ⟩ := exists_orth_ne (fun i => p i i) v (q *ᵥ v)
  have hψv : ψ ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact hvψ
  have hγ2 : (1 + vecMulVec v ψ) * (1 + vecMulVec v ψ) = 1 := by
    rw [tv_mul_tv, hψv, zero_smul, add_zero, add_assoc, add_self_mat, add_zero]
  set γ : G5 := ofMatInv (1 + vecMulVec v ψ) (1 + vecMulVec v ψ) hγ2 with hγdef
  have hγ : (γ : 𝕄) = 1 + vecMulVec v ψ := rfl
  have hγγ : γ * γ = 1 := Subtype.ext hγ2
  have hγinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγγ
  have hσγ : ((σ γ : G5) : 𝕄) = 1 + vecMulVec (p *ᵥ ψ) (v ᵥ* q) := by
    rw [hσ, hγinv, hγ, transpose_add, transpose_one, transpose_vecMulVec, Matrix.mul_add,
      Matrix.mul_one, Matrix.add_mul, hpq, mul_vecMulVec, vecMulVec_mul]
  have hA : (v ᵥ* q) ⬝ᵥ v = 0 := by
    rw [← dotProduct_mulVec, dotProduct_mulVec_self hqs]
    exact hvq
  have hB : ψ ⬝ᵥ (p *ᵥ ψ) = 0 := by
    rw [dotProduct_mulVec_self hPs]
    exact hdψ
  have hC : (v ᵥ* q) ⬝ᵥ (p *ᵥ ψ) = 0 := by
    rw [dotProduct_mulVec, vecMul_vecMul, hqp, vecMul_one]
    exact hvψ
  have hx : ((σ γ * γ : G5) : 𝕄) = 1 + vecMulVec (p *ᵥ ψ) (v ᵥ* q) + vecMulVec v ψ := by
    show ((σ γ : G5) : 𝕄) * (γ : 𝕄) = _
    rw [hσγ, hγ, tv_mul_tv, hA, zero_smul, add_zero]
  refine ⟨γ, hγγ, fun h1 => ?_, ?_⟩
  · have h1' := congrArg (fun y : G5 => (y : 𝕄)) h1
    simp only [Matrix.SpecialLinearGroup.coe_one] at h1'
    rw [hx] at h1'
    have h3 : vecMulVec (p *ᵥ ψ) (v ᵥ* q) = vecMulVec v ψ := by
      have h4 : vecMulVec (p *ᵥ ψ) (v ᵥ* q) + vecMulVec v ψ = 0 := by
        have h5 : 1 + (vecMulVec (p *ᵥ ψ) (v ᵥ* q) + vecMulVec v ψ) = 1 + 0 := by
          rw [← add_assoc, h1', add_zero]
        exact add_left_cancel h5
      calc vecMulVec (p *ᵥ ψ) (v ᵥ* q) =
          vecMulVec (p *ᵥ ψ) (v ᵥ* q) + (vecMulVec v ψ + vecMulVec v ψ) := by
            rw [add_self_mat, add_zero]
        _ = vecMulVec v ψ := by rw [← add_assoc, h4, zero_add]
    have hpψ0 : p *ᵥ ψ ≠ 0 := fun h0 => hψ0 (by
      have := congrArg (q *ᵥ ·) h0
      simpa [mulVec_mulVec, hqp] using this)
    have hvq0 : v ᵥ* q ≠ 0 := fun h0 => hv0 (by
      have := congrArg (· ᵥ* p) h0
      simpa [vecMul_vecMul, hqp] using this)
    obtain ⟨h4, -⟩ := vecMulVec_inj hpψ0 hvq0 hv0 h3
    apply hψq
    rw [← h4, mulVec_mulVec, hqp, one_mulVec]
  · apply Subtype.ext
    show ((σ γ * γ : G5) : 𝕄) * ((σ γ * γ : G5) : 𝕄) = 1
    rw [hx]
    set A := vecMulVec (p *ᵥ ψ) (v ᵥ* q)
    set B := vecMulVec v ψ
    have hAA : A * A = 0 := by rw [vecMulVec_mul_vecMulVec, hC, zero_smul, vecMulVec_zero]
    have hAB : A * B = 0 := by rw [vecMulVec_mul_vecMulVec, hA, zero_smul, vecMulVec_zero]
    have hBA : B * A = 0 := by rw [vecMulVec_mul_vecMulVec, hB, zero_smul, vecMulVec_zero]
    have hBB : B * B = 0 := by rw [vecMulVec_mul_vecMulVec, hψv, zero_smul, vecMulVec_zero]
    calc (1 + A + B) * (1 + A + B) = 1 + (A + A) + (B + B) + A * A + A * B + B * A + B * B := by
          noncomm_ring
      _ = 1 := by rw [add_self_mat, add_self_mat, hAA, hAB, hBA, hBB]; simp

end Graph

end CFSG.Quasithin.B42Ln
