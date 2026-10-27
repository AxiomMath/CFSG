module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.KGFactE623Sp4

public section

namespace CFSG.Quasithin.H13.KGE623

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Id2519
open scoped Pointwise

section Blocks

variable {F : Type} [Field F]

theorem submatrix_mul_of_rowBlock {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (f : Fin m → ι) (hf : Function.Injective f) (A B : Matrix ι ι F)
    (hA : ∀ i, ∀ w, w ∉ Set.range f → A (f i) w = 0) :
    (A * B).submatrix f f = A.submatrix f f * B.submatrix f f := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  rw [← Finset.sum_image (s := Finset.univ) (g := f)
    (fun k _ l _ hkl => hf hkl) (f := fun w => A (f i) w * B w (f j))]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro w _ hw
  have hw' : w ∉ Set.range f := by
    rintro ⟨k, rfl⟩
    exact hw (Finset.mem_image_of_mem f (Finset.mem_univ k))
  rw [hA i w hw', zero_mul]

variable [CharP F 2]

theorem eq_one_of_mul_self {c : F} (h : c * c = 1) : c = 1 := by
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

theorem eq_one_of_block₁ {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hsq : M * M = 1)
    (hz : ∀ u v, u ≠ v → (u = Sum.inl 0 ∨ u = Sum.inr 0 ∨ v = Sum.inl 0 ∨ v = Sum.inr 0) →
      M u v = 0)
    (hb : M.submatrix ![Sum.inl 1, Sum.inr 1] ![Sum.inl 1, Sum.inr 1] = 1) : M = 1 := by
  have hb' : ∀ i j : Fin 2, M (![Sum.inl 1, Sum.inr 1] i) (![Sum.inl 1, Sum.inr 1] j) =
      (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by
    rw [← hb]
    rfl
  have h11 := hb' 0 0
  have h12 := hb' 0 1
  have h21 := hb' 1 0
  have h22 := hb' 1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h11 h12 h21 h22
  have hsq00 := congrFun (congrFun hsq (Sum.inl 0)) (Sum.inl 0)
  have hsq20 := congrFun (congrFun hsq (Sum.inr 0)) (Sum.inr 0)
  simp only [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply_eq] at hsq00 hsq20
  rw [hz (Sum.inl 0) (Sum.inl 1) (by decide) (by simp), hz (Sum.inl 0) (Sum.inr 0) (by decide)
    (by simp), hz (Sum.inl 0) (Sum.inr 1) (by decide) (by simp)] at hsq00
  rw [hz (Sum.inr 0) (Sum.inl 0) (by decide) (by simp), hz (Sum.inr 0) (Sum.inl 1) (by decide)
    (by simp), hz (Sum.inr 0) (Sum.inr 1) (by decide) (by simp)] at hsq20
  simp only [zero_mul, add_zero, zero_add] at hsq00 hsq20
  have e00 := eq_one_of_mul_self hsq00
  have e20 := eq_one_of_mul_self hsq20
  ext u v
  rcases u with u | u <;> rcases v with v | v <;> fin_cases u <;> fin_cases v <;>
    first
    | simpa using e00
    | simpa using e20
    | simpa using h11
    | simpa using h12
    | simpa using h21
    | simpa using h22
    | (rw [hz _ _ (by decide) (by simp)]; simp)

theorem eq_one_of_block₀ {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hsq : M * M = 1)
    (hz : ∀ u v, u ≠ v → (u = Sum.inl 1 ∨ u = Sum.inr 1 ∨ v = Sum.inl 1 ∨ v = Sum.inr 1) →
      M u v = 0)
    (hb : M.submatrix ![Sum.inl 0, Sum.inr 0] ![Sum.inl 0, Sum.inr 0] = 1) : M = 1 := by
  have hb' : ∀ i j : Fin 2, M (![Sum.inl 0, Sum.inr 0] i) (![Sum.inl 0, Sum.inr 0] j) =
      (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by
    rw [← hb]
    rfl
  have h11 := hb' 0 0
  have h12 := hb' 0 1
  have h21 := hb' 1 0
  have h22 := hb' 1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h11 h12 h21 h22
  have hsq00 := congrFun (congrFun hsq (Sum.inl 1)) (Sum.inl 1)
  have hsq20 := congrFun (congrFun hsq (Sum.inr 1)) (Sum.inr 1)
  simp only [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply_eq] at hsq00 hsq20
  rw [hz (Sum.inl 1) (Sum.inl 0) (by decide) (by simp), hz (Sum.inl 1) (Sum.inr 0) (by decide)
    (by simp), hz (Sum.inl 1) (Sum.inr 1) (by decide) (by simp)] at hsq00
  rw [hz (Sum.inr 1) (Sum.inl 0) (by decide) (by simp), hz (Sum.inr 1) (Sum.inl 1) (by decide)
    (by simp), hz (Sum.inr 1) (Sum.inr 0) (by decide) (by simp)] at hsq20
  simp only [zero_mul, add_zero, zero_add] at hsq00 hsq20
  have e00 := eq_one_of_mul_self hsq00
  have e20 := eq_one_of_mul_self hsq20
  ext u v
  rcases u with u | u <;> rcases v with v | v <;> fin_cases u <;> fin_cases v <;>
    first
    | simpa using e00
    | simpa using e20
    | simpa using h11
    | simpa using h12
    | simpa using h21
    | simpa using h22
    | (rw [hz _ _ (by decide) (by simp)]; simp)

omit [CharP F 2] in
theorem eq_one_of_symp_inl {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hJ : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0)
    (hz : ∀ i j : Fin 2, M (Sum.inl i) (Sum.inr j) = 0 ∧ M (Sum.inr i) (Sum.inl j) = 0)
    (hb : M.submatrix ![Sum.inl 0, Sum.inl 1] ![Sum.inl 0, Sum.inl 1] = 1) : M = 1 := by
  have hform : M = fromBlocks 1 0 0 M.toBlocks₂₂ := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · have h1 := congrFun (congrFun hb u) v
      fin_cases u <;> fin_cases v <;> simpa using h1
    · simpa using (hz u v).1
    · simpa using (hz u v).2
    · rfl
  rw [hform] at hJ ⊢
  simp only [fromBlocks_transpose, fromBlocks_multiply, transpose_one, transpose_zero,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_neg] at hJ
  obtain ⟨-, h12, -, -⟩ := Matrix.fromBlocks_inj.mp hJ
  rw [h12, fromBlocks_one]

omit [CharP F 2] in
theorem eq_one_of_symp_cross {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hJ : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0)
    (hz : ∀ u v, ((u = Sum.inl 0 ∨ u = Sum.inr 1) ↔ ¬ (v = Sum.inl 0 ∨ v = Sum.inr 1)) →
      M u v = 0)
    (hb : M.submatrix ![Sum.inl 0, Sum.inr 1] ![Sum.inl 0, Sum.inr 1] = 1) : M = 1 := by
  have hb' : ∀ i j : Fin 2, M (![Sum.inl 0, Sum.inr 1] i) (![Sum.inl 0, Sum.inr 1] j) =
      (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by
    rw [← hb]
    rfl
  have a00 := hb' 0 0
  have a01 := hb' 0 1
  have a10 := hb' 1 0
  have a11 := hb' 1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at a00 a01 a10 a11
  have z1 : M (Sum.inl 0) (Sum.inl 1) = 0 := hz _ _ (by simp)
  have z2 : M (Sum.inl 0) (Sum.inr 0) = 0 := hz _ _ (by simp)
  have z3 : M (Sum.inr 1) (Sum.inl 1) = 0 := hz _ _ (by simp)
  have z4 : M (Sum.inr 1) (Sum.inr 0) = 0 := hz _ _ (by simp)
  have z5 : M (Sum.inl 1) (Sum.inl 0) = 0 := hz _ _ (by simp)
  have z6 : M (Sum.inl 1) (Sum.inr 1) = 0 := hz _ _ (by simp)
  have z7 : M (Sum.inr 0) (Sum.inl 0) = 0 := hz _ _ (by simp)
  have z8 : M (Sum.inr 0) (Sum.inr 1) = 0 := hz _ _ (by simp)
  have e1 := congrFun (congrFun hJ (Sum.inl 0)) (Sum.inr 0)
  have e2 := congrFun (congrFun hJ (Sum.inl 0)) (Sum.inl 1)
  have e3 := congrFun (congrFun hJ (Sum.inr 1)) (Sum.inl 1)
  have e4 := congrFun (congrFun hJ (Sum.inr 1)) (Sum.inr 0)
  simp only [mul_apply, transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, a00, a01, a10, a11, z1, z2, z3, z4,
    z5, z6, z7, z8, Matrix.zero_apply, Matrix.one_apply_eq, Matrix.neg_apply,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, zero_mul, add_zero, zero_add,
    one_mul, neg_zero, neg_mul] at e1 e2 e3 e4
  have e3' : M (Sum.inl 1) (Sum.inl 1) = 1 := neg_injective e3
  have e4' : M (Sum.inl 1) (Sum.inr 0) = 0 := neg_eq_zero.mp e4
  ext u v
  rcases u with u | u <;> rcases v with v | v <;> fin_cases u <;> fin_cases v <;>
    simp_all

omit [Field F] [CharP F 2] in
theorem injective_vec3 {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

end Blocks

section Count

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem card_le_four_of_block (hF : Nat.card F = 4) (f : Fin 2 → Fin 2 ⊕ Fin 2)
    (hf : Function.Injective f) (E : Subgroup (StatedSp 2 F)) (hE2 : IsPGroup 2 E)
    (hblk : ∀ g ∈ E, ∀ i w, w ∉ Set.range f → spMat g (f i) w = 0)
    (hinj : ∀ g ∈ E, (spMat g).submatrix f f = 1 → g = 1) : Nat.card E ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ0 : E →* Matrix (Fin 2) (Fin 2) F :=
    { toFun := fun g => (spMat (g : StatedSp 2 F)).submatrix f f
      map_one' := by
        show (spMat (1 : StatedSp 2 F)).submatrix f f = 1
        exact Matrix.submatrix_one f hf
      map_mul' := fun g h => by
        show (spMat ((g : StatedSp 2 F) * (h : StatedSp 2 F))).submatrix f f = _
        exact submatrix_mul_of_rowBlock f hf _ _ (hblk g g.2) }
  let ψ : E →* GL (Fin 2) F := ψ0.toHomUnits
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun g hg => ?_
    have h1 : (spMat (g : StatedSp 2 F)).submatrix f f = 1 := congrArg Units.val hg
    exact Subtype.ext (hinj g g.2 h1)
  have hdvd := Subgroup.card_dvd_of_injective ψ hψ
  have : Fintype F := Fintype.ofFinite F
  have hGL : Nat.card (GL (Fin 2) F) = 180 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  rw [hk, hGL] at hdvd
  have hk2 : k ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 180 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h8
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

end Count

theorem sp44OrderThreeCent_holds : Sp44OrderThreeCent := by
  intro F _ _ hF y hy3 hy1 E hE hEC
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hproj := UnitaryHigher.proj_bijective_of_charTwo (r := 2) (K := F)
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyp : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hoy, pow_one])
  obtain ⟨R, hR⟩ := hyp.exists_le_sylow
  have hTcard := USp4.card_torusP hF
  have hTp : IsPGroup 3 (USp4.torusP F) := IsPGroup.of_card (n := 2) (by rw [hTcard]; norm_num)
  set QT : Sylow 3 (StatedProj (StatedSp 2 F)) :=
    hTp.toSylow (USp4.not_dvd_index_of_card_nine hF hTcard) with hQT
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 F)) R QT
  have hyT : x * y * x⁻¹ ∈ USp4.torusP F := by
    have h1 : y ∈ (R : Subgroup (StatedProj (StatedSp 2 F))) := hR (Subgroup.mem_zpowers y)
    have h2 : MulAut.conj x • y ∈ MulAut.conj x • (R : Subgroup (StatedProj (StatedSp 2 F))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← Sylow.coe_subgroup_smul, hx, hQT, IsPGroup.toSylow_coe] at h2
    exact h2
  obtain ⟨s, ⟨a, rfl⟩, hsy⟩ := hyT
  set E' := E.map (MulAut.conj x).toMonoidHom with hE'
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  set Et := E'.comap (proj 2 F) with hEt
  have hEtcard : Nat.card Et = Nat.card E' := by
    rw [← Subgroup.card_map_of_injective hproj.1,
      Subgroup.map_comap_eq_self_of_surjective hproj.2]
  have hE'sq : ∀ e ∈ E', e ^ 2 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    simp [hE.2 e he]
  have hE'C : ∀ e ∈ E', e * (x * y * x⁻¹) = (x * y * x⁻¹) * e := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : e * y = y * e := Subgroup.mem_centralizer_singleton_iff.mp (hEC he)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * e * x⁻¹ * (x * y * x⁻¹) = x * (e * y) * x⁻¹ := by group
      _ = x * (y * e) * x⁻¹ := by rw [h1]
      _ = x * y * x⁻¹ * (x * e * x⁻¹) := by group
  have hEtsq : ∀ g ∈ Et, g ^ 2 = 1 := fun g hg => hproj.1 (by
    rw [map_pow, map_one]
    exact hE'sq _ hg)
  have hEtC : ∀ g ∈ Et, g * SymplecticTorusWeyl.torusHom a =
      SymplecticTorusWeyl.torusHom a * g := fun g hg => hproj.1 (by
    rw [map_mul, map_mul, hsy]
    exact hE'C _ hg)
  have hEt2 : IsPGroup 2 Et := fun g => ⟨1, Subtype.ext (by simpa using hEtsq g g.2)⟩
  rw [← hE'card, ← hEtcard]
  set d : Fin 2 ⊕ Fin 2 → F :=
    Sum.elim (fun i => (a i : F)) (fun i => (((a i)⁻¹ : Fˣ) : F)) with hd
  have hcomm : ∀ g ∈ Et, spMat g * diagonal d = diagonal d * spMat g := fun g hg => by
    have h1 := congrArg spMat (hEtC g hg)
    have hD : spMat (SymplecticTorusWeyl.torusHom a) = diagonal d :=
      SymplecticTorusWeyl.coe_torusHom a
    rw [show spMat (g * SymplecticTorusWeyl.torusHom a) = spMat g *
        spMat (SymplecticTorusWeyl.torusHom a) from rfl,
      show spMat (SymplecticTorusWeyl.torusHom a * g) = spMat (SymplecticTorusWeyl.torusHom a) *
        spMat g from rfl, hD] at h1
    exact h1
  have hzero : ∀ g ∈ Et, ∀ u v, d u ≠ d v → spMat g u v = 0 := fun g hg u v huv =>
    USp4.entry_eq_zero_of_commute_diagonal _ d (hcomm g hg) huv
  have hsqm : ∀ g ∈ Et, spMat g * spMat g = 1 := fun g hg => by
    have h1 := congrArg spMat (hEtsq g hg)
    rw [sq] at h1
    exact h1
  have hJ : ∀ g : StatedSp 2 F, (spMat g)ᵀ * fromBlocks 0 1 (-1) 0 * spMat g =
      fromBlocks 0 1 (-1) 0 := fun g => SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  have hone : ∀ g : StatedSp 2 F, spMat g = 1 → g = 1 := fun g h1 =>
    Subtype.ext (Units.ext h1)
  have : Fintype F := Fintype.ofFinite F
  have hcard3 : Fintype.card Fˣ = 3 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  have hcube : ∀ c : Fˣ, c ^ 3 = 1 := fun c => by
    rw [← hcard3]
    exact pow_card_eq_one
  have hne : ∀ c : Fˣ, c ≠ 1 → (c : F) ≠ 1 ∧ ((c⁻¹ : Fˣ) : F) ≠ 1 ∧ (c : F) ≠ ((c⁻¹ : Fˣ) : F) := by
    intro c hc
    refine ⟨fun h => hc (Units.ext h), fun h => hc (inv_eq_one.mp (Units.ext h)), fun h => ?_⟩
    have h1 : c = c⁻¹ := Units.ext h
    have h2 : c ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h1]; exact mul_inv_cancel c
    apply hc
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hcube, h2]; simp
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hy1
    have h1 : x * y * x⁻¹ = 1 := by rw [← hsy, map_one, map_one]
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have hcls : ∀ (c : Fin 3 → F), Function.Injective c → ∀ cls : Fin 2 ⊕ Fin 2 → Fin 3,
      (∀ u, d u = c (cls u)) → ∀ u v, cls u ≠ cls v → d u ≠ d v :=
    fun c hc cls hdc u v h h' => h (hc (by rw [← hdc, ← hdc, h']))
  by_cases h1 : a 1 = 1
  ·
    have h0 : a 0 ≠ 1 := fun h0 => ha1 (funext fun i => by fin_cases i <;> assumption)
    obtain ⟨n1, n2, n3⟩ := hne (a 0) h0
    have hc := injective_vec3 n1.symm n2.symm n3
    have hdc : ∀ u, d u = ![1, (a 0 : F), (((a 0)⁻¹ : Fˣ) : F)]
        (Sum.elim ![1, 0] ![2, 0] u) := by
      intro u
      rcases u with u | u <;> fin_cases u <;> simp [hd, h1]
    have hb1 : ∀ (i : Fin 2) (w : Fin 2 ⊕ Fin 2),
        (∀ k, (![Sum.inl 1, Sum.inr 1] : Fin 2 → Fin 2 ⊕ Fin 2) k ≠ w) →
        (Sum.elim ![1, 0] ![2, 0] (![Sum.inl 1, Sum.inr 1] i) : Fin 3) ≠
          Sum.elim ![1, 0] ![2, 0] w := by decide
    have hz1 : ∀ u v : Fin 2 ⊕ Fin 2, u ≠ v →
        (u = Sum.inl 0 ∨ u = Sum.inr 0 ∨ v = Sum.inl 0 ∨ v = Sum.inr 0) →
        (Sum.elim ![1, 0] ![2, 0] u : Fin 3) ≠ Sum.elim ![1, 0] ![2, 0] v := by decide
    refine card_le_four_of_block hF ![Sum.inl 1, Sum.inr 1] (by decide) Et hEt2
      (fun g hg i w hw => hzero g hg _ _ (hcls _ hc _ hdc _ _
        (hb1 i w fun k hk => hw ⟨k, hk⟩))) fun g hg hb => hone g ?_
    exact eq_one_of_block₁ (hsqm g hg)
      (fun u v huv hu => hzero g hg u v (hcls _ hc _ hdc u v (hz1 u v huv hu))) hb
  · by_cases h0 : a 0 = 1
    ·
      obtain ⟨n1, n2, n3⟩ := hne (a 1) h1
      have hc := injective_vec3 n1.symm n2.symm n3
      have hdc : ∀ u, d u = ![1, (a 1 : F), (((a 1)⁻¹ : Fˣ) : F)]
          (Sum.elim ![0, 1] ![0, 2] u) := by
        intro u
        rcases u with u | u <;> fin_cases u <;> simp [hd, h0]
      have hb1 : ∀ (i : Fin 2) (w : Fin 2 ⊕ Fin 2),
          (∀ k, (![Sum.inl 0, Sum.inr 0] : Fin 2 → Fin 2 ⊕ Fin 2) k ≠ w) →
          (Sum.elim ![0, 1] ![0, 2] (![Sum.inl 0, Sum.inr 0] i) : Fin 3) ≠
            Sum.elim ![0, 1] ![0, 2] w := by decide
      have hz1 : ∀ u v : Fin 2 ⊕ Fin 2, u ≠ v →
          (u = Sum.inl 1 ∨ u = Sum.inr 1 ∨ v = Sum.inl 1 ∨ v = Sum.inr 1) →
          (Sum.elim ![0, 1] ![0, 2] u : Fin 3) ≠ Sum.elim ![0, 1] ![0, 2] v := by decide
      refine card_le_four_of_block hF ![Sum.inl 0, Sum.inr 0] (by decide) Et hEt2
        (fun g hg i w hw => hzero g hg _ _ (hcls _ hc _ hdc _ _
          (hb1 i w fun k hk => hw ⟨k, hk⟩))) fun g hg hb => hone g ?_
      exact eq_one_of_block₀ (hsqm g hg)
        (fun u v huv hu => hzero g hg u v (hcls _ hc _ hdc u v (hz1 u v huv hu))) hb
    ·
      obtain ⟨n1, n2, n3⟩ := hne (a 0) h0
      have hc := injective_vec3 n1.symm n2.symm n3
      have hoa : orderOf (a 0) = 3 := orderOf_eq_prime (hcube _) h0
      have hmem : a 1 ∈ Subgroup.zpowers (a 0) := by
        have htop : Subgroup.zpowers (a 0) = ⊤ := by
          apply Subgroup.eq_top_of_card_eq
          rw [Nat.card_zpowers, hoa, Nat.card_eq_fintype_card, hcard3]
        rw [htop]
        exact Subgroup.mem_top _
      rw [mem_zpowers_iff_mem_range_orderOf, hoa] at hmem
      have h3 : a 1 = a 0 ∨ a 1 = (a 0)⁻¹ := by
        simp only [Finset.mem_image, Finset.mem_range] at hmem
        obtain ⟨k, hk, hk1⟩ := hmem
        interval_cases k
        · exact absurd hk1.symm (by simpa using h1)
        · left
          rw [← hk1, pow_one]
        · right
          rw [← hk1]
          calc a 0 ^ 2 = a 0 ^ 3 * (a 0)⁻¹ := by group
            _ = (a 0)⁻¹ := by rw [hcube, one_mul]
      rcases h3 with h3 | h3
      ·
        have hdc : ∀ u, d u = ![1, (a 0 : F), (((a 0)⁻¹ : Fˣ) : F)]
            (Sum.elim ![1, 1] ![2, 2] u) := by
          intro u
          rcases u with u | u <;> fin_cases u <;> simp [hd, h3]
        have hb1 : ∀ (i : Fin 2) (w : Fin 2 ⊕ Fin 2),
            (∀ k, (![Sum.inl 0, Sum.inl 1] : Fin 2 → Fin 2 ⊕ Fin 2) k ≠ w) →
            (Sum.elim ![1, 1] ![2, 2] (![Sum.inl 0, Sum.inl 1] i) : Fin 3) ≠
              Sum.elim ![1, 1] ![2, 2] w := by decide
        have hzI : ∀ i j : Fin 2,
            (Sum.elim ![1, 1] ![2, 2] (Sum.inl i) : Fin 3) ≠ Sum.elim ![1, 1] ![2, 2] (Sum.inr j) ∧
            (Sum.elim ![1, 1] ![2, 2] (Sum.inr i) : Fin 3) ≠ Sum.elim ![1, 1] ![2, 2] (Sum.inl j) :=
          by decide
        refine card_le_four_of_block hF ![Sum.inl 0, Sum.inl 1] (by decide) Et hEt2
          (fun g hg i w hw => hzero g hg _ _ (hcls _ hc _ hdc _ _
            (hb1 i w fun k hk => hw ⟨k, hk⟩))) fun g hg hb => hone g ?_
        exact eq_one_of_symp_inl (hJ g) (fun i j =>
          ⟨hzero g hg _ _ (hcls _ hc _ hdc _ _ (hzI i j).1),
            hzero g hg _ _ (hcls _ hc _ hdc _ _ (hzI i j).2)⟩) hb
      ·
        have hdc : ∀ u, d u = ![1, (a 0 : F), (((a 0)⁻¹ : Fˣ) : F)]
            (Sum.elim ![1, 2] ![2, 1] u) := by
          intro u
          rcases u with u | u <;> fin_cases u <;> simp [hd, h3]
        have hb1 : ∀ (i : Fin 2) (w : Fin 2 ⊕ Fin 2),
            (∀ k, (![Sum.inl 0, Sum.inr 1] : Fin 2 → Fin 2 ⊕ Fin 2) k ≠ w) →
            (Sum.elim ![1, 2] ![2, 1] (![Sum.inl 0, Sum.inr 1] i) : Fin 3) ≠
              Sum.elim ![1, 2] ![2, 1] w := by decide
        have hzX : ∀ u v : Fin 2 ⊕ Fin 2,
            ((u = Sum.inl 0 ∨ u = Sum.inr 1) ↔ ¬ (v = Sum.inl 0 ∨ v = Sum.inr 1)) →
            (Sum.elim ![1, 2] ![2, 1] u : Fin 3) ≠ Sum.elim ![1, 2] ![2, 1] v := by decide
        refine card_le_four_of_block hF ![Sum.inl 0, Sum.inr 1] (by decide) Et hEt2
          (fun g hg i w hw => hzero g hg _ _ (hcls _ hc _ hdc _ _
            (hb1 i w fun k hk => hw ⟨k, hk⟩))) fun g hg hb => hone g ?_
        exact eq_one_of_symp_cross (hJ g)
          (fun u v huv => hzero g hg u v (hcls _ hc _ hdc u v (hzX u v huv))) hb

end CFSG.Quasithin.H13.KGE623
