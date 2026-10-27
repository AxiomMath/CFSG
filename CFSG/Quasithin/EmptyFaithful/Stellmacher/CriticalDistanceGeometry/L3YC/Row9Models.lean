module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row9Lift
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row9LinAlg
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.Stellmacher.CD.L3YC.Row9

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank Matrix

section Central

variable {F : Type} [Field F]

theorem centralExp3_proj (X : Subgroup (GL (Fin 3) F)) (hdet : ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) F).det = 1) :
    CentralExp3 (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf X)) := by
  refine ⟨QuotientGroup.mk'_surjective _, ?_, ?_⟩
  · intro x hx y
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    have hx' : (x : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := hx
    have hc : (x : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
      rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
      exact hx'
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hc (y : GL (Fin 3) F)).symm
  · intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    have hx' : (x : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := hx
    obtain ⟨l, hl⟩ := hx'
    have hd := hdet x x.2
    have hl3 : l ^ 3 = 1 := by
      apply Units.ext
      have h1 := Matrix.GeneralLinearGroup.det_scalar (n := Fin 3) (R := F) l
      have h2 : (((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) l) : Fˣ)) : F) = 1 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, hl]; exact hd
      rw [h1] at h2
      simpa using h2
    apply Subtype.ext
    show (x : GL (Fin 3) F) ^ 3 = 1
    rw [← hl, ← map_pow, hl3, map_one]

theorem centralExp3_id {X : Type*} [Group X] : CentralExp3 (MonoidHom.id X) := by
  refine ⟨Function.surjective_id, ?_, ?_⟩
  · intro x hx y; simp only [MonoidHom.id_apply] at hx; subst hx; simp
  · intro x hx; simp only [MonoidHom.id_apply] at hx; subst hx; simp

end Central

section TBound

variable {F : Type} [Field F] [CharP F 7] [Finite F]

def fAlpha (Z : Matrix (Fin 3) (Fin 3) F) (α : F) : Matrix (Fin 3) (Fin 3) F :=
  α • ((2 : F)⁻¹ • (1 - Z)) + (α ^ 2)⁻¹ • ((2 : F)⁻¹ • (1 + Z))

theorem T_card_le (X : Subgroup (GL (Fin 3) F))
    (hdet : ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) F).det = 1) (e : ℕ) (he : 0 < e)
    (hroot : ∀ (zt : ↥X), zt ^ 2 = 1 → zt ≠ 1 → ∀ c : ↥X, ∀ α : F, α ≠ 0 →
      (((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
        fAlpha (((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) α →
      (∃ n : ℕ, α ^ (2 ^ n) = 1) → α ^ e = 1)
    (zt gt : ↥X) (hz2 : zt ^ 2 = 1) (hz1 : zt ≠ 1) (hg7 : gt ^ 7 = 1) (hg1 : gt ≠ 1)
    (hzg : zt * gt = gt * zt) :
    Nat.card {c : ↥X // (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ c * zt = zt * c ∧ c * gt = gt * c} ≤ e := by
  have hZ : ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have := congrArg (fun x : ↥X => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hz2
    simpa [pow_two] using this
  have hZ1 : ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h =>
    hz1 (Subtype.ext (Units.ext h))
  have hG7 : ((gt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 7 = 1 := by
    have := congrArg (fun x : ↥X => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hg7
    simpa using this
  have hG1 : ((gt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h =>
    hg1 (Subtype.ext (Units.ext h))
  have hZG : ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((gt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((gt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : ↥X => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hzg
    simpa using this
  have hex : ∀ c : {c : ↥X // (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ c * zt = zt * c ∧ c * gt = gt * c},
      ∃ α : F, α ≠ 0 ∧ (∃ n : ℕ, α ^ (2 ^ n) = 1) ∧
        (((c.1 : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
          fAlpha (((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) α := by
    rintro ⟨c, ⟨n, hn⟩, hcz, hcg⟩
    have hCn : ((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ (2 ^ n) = 1 := by
      have := congrArg (fun x : ↥X => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hn
      simpa using this
    have hZC : ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have := congrArg (fun x : ↥X => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hcz
      simpa using this.symm
    have hGC : ((gt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((gt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have := congrArg (fun x : ↥X => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hcg
      simpa using this.symm
    obtain ⟨α, hα0, hα, hc⟩ := elt_form_matrix _ _ _ hZ (hdet zt zt.2) hZ1 hG7 hG1 hZG n hCn
      (hdet c c.2) hZC hGC
    exact ⟨α, hα0, ⟨n, hα⟩, hc⟩
  choose α hα0 hαn hαc using hex
  let f : {c : ↥X // (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ c * zt = zt * c ∧ c * gt = gt * c} →
      {a : F // a ^ e = 1} := fun c => ⟨α c, hroot zt hz2 hz1 c.1 (α c) (hα0 c) (hαc c) (hαn c)⟩
  have hinj : Function.Injective f := by
    intro c c' h
    have h1 : α c = α c' := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hαc c, hαc c', h1]
  refine (Nat.card_le_card_of_injective f hinj).trans ?_
  classical
  calc Nat.card {a : F // a ^ e = 1}
      = Nat.card ↥((Polynomial.nthRoots e (1 : F)).toFinset) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun a => by simp [Polynomial.mem_nthRoots he]))
    _ = ((Polynomial.nthRoots e (1 : F)).toFinset).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card (Polynomial.nthRoots e (1 : F)) := Multiset.toFinset_card_le _
    _ ≤ e := Polynomial.card_nthRoots e 1

omit [CharP F 7] [Finite F] in
theorem alpha_sq_eq_one (α : F) (h6 : α ^ 6 = 1) (n : ℕ) (hn : α ^ (2 ^ n) = 1) : α ^ 2 = 1 := by
  rcases n with _ | n
  · simp at hn; rw [hn]; simp
  · have h1 : (α ^ 2) ^ (2 ^ n) = 1 := by rw [← pow_mul, ← pow_succ']; exact hn
    have h2 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h6
    have hc : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by decide)
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hc, pow_one] at this

theorem hroot_SL (hF : Nat.card F = 7) (X : Subgroup (GL (Fin 3) F)) :
    ∀ (zt : ↥X), zt ^ 2 = 1 → zt ≠ 1 → ∀ c : ↥X, ∀ α : F, α ≠ 0 →
      (((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
        fAlpha (((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) α →
      (∃ n : ℕ, α ^ (2 ^ n) = 1) → α ^ 2 = 1 := by
  intro zt _ _ c α hα0 _ ⟨n, hn⟩
  have : Fintype F := Fintype.ofFinite F
  have h6 : α ^ 6 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one α hα0
    rwa [← Nat.card_eq_fintype_card, hF] at this
  exact alpha_sq_eq_one α h6 n hn

omit [Finite F] in
theorem two_inv_pow_seven : ((2 : F)⁻¹) ^ 7 = (2 : F)⁻¹ := by
  have h126 : ((126 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 7 126).mpr (by norm_num)
  have h2 : (2 : F) ^ 7 = 2 := by
    have : (2 : F) ^ 7 = 2 + (126 : ℕ) := by push_cast; norm_num
    rw [this, h126, add_zero]
  rw [inv_pow, h2]

omit [Finite F] in
theorem frob_transpose_fAlpha (Z : Matrix (Fin 3) (Fin 3) F) (hZ : (Z.map (· ^ 7))ᵀ = Z) (α : F) :
    ((fAlpha Z α).map (· ^ 7))ᵀ =
      α ^ 7 • ((2 : F)⁻¹ • (1 - Z)) + ((α ^ 2)⁻¹) ^ 7 • ((2 : F)⁻¹ • (1 + Z)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hZe : ∀ i j, Z j i ^ 7 = Z i j := fun i j => by
    have := congrFun (congrFun hZ i) j
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  ext i j
  simp only [fAlpha, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  rw [add_pow_char, mul_pow, mul_pow, mul_pow, mul_pow, two_inv_pow_seven]
  have hd : ((if j = i then (1 : F) else 0)) ^ 7 = if i = j then 1 else 0 := by
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [sub_pow_char, add_pow_char, hZe, hd]

omit [CharP F 7] [Finite F] in
theorem prod_proj {M : Type} [Ring M] [Algebra F M] (A B : M) (hAA : A * A = A) (hBB : B * B = B)
    (hAB : A * B = 0) (hBA : B * A = 0) (a b c d : F) :
    (a • A + b • B) * (c • A + d • B) = (a * c) • A + (b * d) • B := by
  rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, hAA, hAB, hBA, hBB]
  simp

omit [Finite F] in
theorem alpha_pow_eight (Z C : Matrix (Fin 3) (Fin 3) F) (hZ : Z * Z = 1) (hZ1 : Z ≠ 1)
    (hZu : (Z.map (· ^ 7))ᵀ * Z = 1) (α : F) (hα0 : α ≠ 0) (hC : C = fAlpha Z α)
    (hCu : (C.map (· ^ 7))ᵀ * C = 1) : α ^ 8 = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero'
  have hZb : (Z.map (· ^ 7))ᵀ = Z := by
    calc (Z.map (· ^ 7))ᵀ = (Z.map (· ^ 7))ᵀ * (Z * Z) := by rw [hZ, mul_one]
      _ = ((Z.map (· ^ 7))ᵀ * Z) * Z := by rw [mul_assoc]
      _ = Z := by rw [hZu, one_mul]
  set A : Matrix (Fin 3) (Fin 3) F := (2 : F)⁻¹ • (1 - Z) with hA
  set B : Matrix (Fin 3) (Fin 3) F := (2 : F)⁻¹ • (1 + Z) with hB
  have e1 : (1 - Z) * (1 - Z) = (2 : F) • (1 - Z) := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, hZ]; module
  have e2 : (1 + Z) * (1 + Z) = (2 : F) • (1 + Z) := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, hZ]; module
  have e3 : (1 - Z) * (1 + Z) = 0 := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, hZ]; module
  have e4 : (1 + Z) * (1 - Z) = 0 := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, hZ]; module
  have hinv : (2 : F)⁻¹ * (2 : F)⁻¹ * 2 = (2 : F)⁻¹ := by field_simp
  have hAA : A * A = A := by
    rw [hA, smul_mul_smul_comm, e1, smul_smul, hinv]
  have hBB : B * B = B := by
    rw [hB, smul_mul_smul_comm, e2, smul_smul, hinv]
  have hAB : A * B = 0 := by
    rw [hA, hB, smul_mul_smul_comm, e3, smul_zero]
  have hBA : B * A = 0 := by
    rw [hA, hB, smul_mul_smul_comm, e4, smul_zero]
  have hsum : A + B = 1 := by
    rw [hA, hB, ← smul_add]
    have : (1 - Z) + (1 + Z) = (2 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by module
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hA0 : A ≠ 0 := by
    intro h0
    apply hZ1
    have : (2 : F)⁻¹ • (1 - Z) = 0 := h0
    have h3 := (smul_eq_zero.mp this).resolve_left (inv_ne_zero h2)
    exact (sub_eq_zero.mp h3).symm
  have hCb := frob_transpose_fAlpha Z hZb α
  rw [hC, hCb] at hCu
  change (α ^ 7 • A + ((α ^ 2)⁻¹) ^ 7 • B) * (α • A + (α ^ 2)⁻¹ • B) = 1 at hCu
  rw [prod_proj A B hAA hBB hAB hBA] at hCu
  have hmul := congrArg (· * A) hCu
  simp only [add_mul, smul_mul_assoc, hAA, hBA, smul_zero, add_zero, one_mul] at hmul
  have h5 : (α ^ 7 * α - 1) • A = 0 := by rw [sub_smul, hmul, one_smul, sub_self]
  have h6 := (smul_eq_zero.mp h5).resolve_right hA0
  have h7 : α ^ 7 * α = 1 := sub_eq_zero.mp h6
  rwa [← pow_succ] at h7

theorem hroot_SU (X : Subgroup (GL (Fin 3) F))
    (hU : ∀ x ∈ X, ((x : Matrix (Fin 3) (Fin 3) F).map (· ^ 7))ᵀ * (x : Matrix (Fin 3) (Fin 3) F) = 1) :
    ∀ (zt : ↥X), zt ^ 2 = 1 → zt ≠ 1 → ∀ c : ↥X, ∀ α : F, α ≠ 0 →
      (((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
        fAlpha (((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) α →
      (∃ n : ℕ, α ^ (2 ^ n) = 1) → α ^ 8 = 1 := by
  intro zt hz2 hz1 c α hα0 hc _
  have hZ : ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have := congrArg (fun x : ↥X => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hz2
    simpa [pow_two] using this
  have hZ1 : ((zt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h =>
    hz1 (Subtype.ext (Units.ext h))
  exact alpha_pow_eight _ _ hZ hZ1 (hU zt zt.2) α hα0 hc (hU c c.2)

omit [CharP F 7] in
theorem charP_seven_of_card (h : Nat.card F = 7 ∨ Nat.card F = 49) : CharP F 7 := by
  have : Fintype F := Fintype.ofFinite F
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card] at h0
  have h7 : ((7 : ℕ) : F) = 0 := by
    rcases h with h | h
    · rwa [h] at h0
    · rw [h] at h0
      have : ((7 : ℕ) : F) * ((7 : ℕ) : F) = 0 := by exact_mod_cast h0
      exact mul_self_eq_zero.mp this
  exact (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 7)).mpr h7

omit [CharP F 7] [Finite F] in
theorem det_of_mem_statedSL {A : GL (Fin 3) F} (h : A ∈ StatedSL 3 F) :
    (A : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL h

omit [CharP F 7] in
theorem HX_SL (hF : Nat.card F = 7) :
    ∀ zt gt : ↥(StatedSL 3 F), zt ^ 2 = 1 → zt ≠ 1 → gt ^ 7 = 1 → gt ≠ 1 → zt * gt = gt * zt →
      Nat.card {c : ↥(StatedSL 3 F) // (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ c * zt = zt * c ∧
        c * gt = gt * c} ≤ 2 := by
  have : CharP F 7 := charP_seven_of_card (Or.inl hF)
  intro zt gt hz2 hz1 hg7 hg1 hzg
  exact T_card_le (StatedSL 3 F) (fun x hx => det_of_mem_statedSL hx) 2 (by norm_num)
    (hroot_SL hF _) zt gt hz2 hz1 hg7 hg1 hzg

omit [CharP F 7] [Finite F] in
theorem mem_statedSU_iff7 (hF : Nat.card F = 49) (A : GL (Fin 3) F) :
    A ∈ StatedSU 3 7 F ↔ (A : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) F).map (· ^ 7))ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := F) (p := 7) (f := 1)
    (by norm_num) (by rw [hF]; norm_num) (n := 3) (by norm_num)).1
  have h2 := Set.ext_iff.1 h A
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq] at h2
  exact h2

omit [CharP F 7] in
theorem HX_SU (hF : Nat.card F = 49) :
    ∀ zt gt : ↥(StatedSU 3 7 F), zt ^ 2 = 1 → zt ≠ 1 → gt ^ 7 = 1 → gt ≠ 1 → zt * gt = gt * zt →
      Nat.card {c : ↥(StatedSU 3 7 F) // (∃ n : ℕ, c ^ (2 ^ n) = 1) ∧ c * zt = zt * c ∧
        c * gt = gt * c} ≤ 8 := by
  have : CharP F 7 := charP_seven_of_card (Or.inr hF)
  intro zt gt hz2 hz1 hg7 hg1 hzg
  exact T_card_le (StatedSU 3 7 F) (fun x hx => ((mem_statedSU_iff7 hF x).mp hx).1) 8
    (by norm_num) (hroot_SU _ (fun x hx => ((mem_statedSU_iff7 hF x).mp hx).2)) zt gt hz2 hz1 hg7
    hg1 hzg

omit [CharP F 7] in
theorem card_statedSL_three' : Nat.card ↥(StatedSL 3 F) =
    Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

end TBound

end CFSG.Quasithin.Stellmacher.CD.L3YC.Row9
