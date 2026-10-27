module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofFieldTools
public import CFSG.GH74.GLS.IVK.L2.FixedSL
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofDihedralMain

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section Field

variable {K : Type} [Field K]

theorem two_ne_zero_of_charP {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p) : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

theorem zpow_apply_eq_self {Y : Type*} [Group Y] {t : MulAut Y} {y : Y} (h : t y = y) (k : ℤ) :
    (t ^ k) y = y := by
  have hmem : t ∈ MulAction.stabilizer (MulAut Y) y := h
  exact (zpow_mem hmem k : t ^ k ∈ MulAction.stabilizer (MulAut Y) y)

theorem mul_conj_eq_of_apply {Y : Type*} [Group Y] {τ : MulAut Y} {x : Y} (h : τ x = x) :
    τ * MulAut.conj x = MulAut.conj x * τ := by
  have e := mul_conj_mul_inv' τ x
  rw [h] at e
  calc τ * MulAut.conj x = τ * MulAut.conj x * τ⁻¹ * τ := by group
    _ = MulAut.conj x * τ := by rw [e]

theorem outerCentConcl_of_field [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    {T : Subgroup (MulAut (projectiveSL 3 K))} (hX : xZero ∈ T)
    (hXc : ∀ t ∈ T, t * xZero = xZero * t)
    (hfix : ∀ t ∈ T, ProjectivePlane.linearFieldPart K (le_refl 3) t = 1 →
      ∀ A : SL(2, K), t (iota A) = iota A) :
    OuterCentConcl (innP K) T := by
  classical
  have hK2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp3
  set φ := ProjectivePlane.linearFieldPart K (le_refl 3) with hφ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf⟩ := FiniteField.card K p
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic (Fact.out : p.Prime) K
    (by rw [Nat.card_eq_fintype_card, hf.2])).2
  obtain ⟨⟨σ₁, hσ₁⟩, hgen⟩ := IsCyclic.exists_generator (α := T.map φ)
  obtain ⟨t₁, ht₁, rfl⟩ := hσ₁
  have hpow : ∀ t ∈ T, ∃ k : ℤ, φ ((t₁ ^ k)⁻¹ * t) = 1 := by
    intro t ht
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨φ t, ⟨t, ht, rfl⟩⟩)
    refine ⟨k, ?_⟩
    have h1 : φ t₁ ^ k = φ t := by simpa using congrArg Subtype.val hk
    rw [map_mul, map_inv, map_zpow, h1, inv_mul_cancel]
  obtain ⟨E, hE⟩ := exists_apply_iota hK2 (apply_x0_of_mem hXc ht₁)
  set σ := φ t₁ with hσ
  have : Finite (K ≃+* K) := CFSG.GH74.GLS.IVK.instFiniteRingEquiv K
  set h := orderOf σ with hh
  have hσh : σ ^ h = 1 := pow_orderOf_eq_one σ
  have hTh : ∀ A : SL(2, K), CatalogueBHigherLinearAction.slConjugation 2 K
      (ProjectivePlane.twistedProd σ E h) A = A := by
    intro A
    have h1 := apply_iota_pow hE h A
    rw [hσh, map_one_sl, hfix _ (T.pow_mem ht₁ h) (by rw [map_pow, ← hσ, hσh]) A] at h1
    exact (iota_injective h1).symm
  obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq hTh
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := (Matrix.isUnits_det_units (ProjectivePlane.twistedProd σ E h)).ne_zero
    rw [hc, zero_smul, Matrix.det_zero] at this
    exact this rfl
  have hTscal : ProjectivePlane.twistedProd σ E h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [hc, Matrix.smul_one_eq_diagonal]
    rfl
  obtain ⟨H, d, hHd⟩ := CFSG.StandardType.OrdPRest.exists_hilbert90 (n := 2) (by norm_num) rfl E
    hTscal
  have hEeq : E = Matrix.GeneralLinearGroup.scalar (Fin 2) d * H *
      (Matrix.GeneralLinearGroup.map (σ : K →+* K) H)⁻¹ := by
    rw [← hHd]; group
  have hact : ∀ A : SL(2, K), CatalogueBHigherLinearAction.slConjugation 2 K E
      (Matrix.SpecialLinearGroup.map (σ : K →+* K) A) =
      CatalogueBHigherLinearAction.slConjugation 2 K H (Matrix.SpecialLinearGroup.map
        (σ : K →+* K) (CatalogueBHigherLinearAction.slConjugation 2 K H⁻¹ A)) := by
    intro A
    rw [map_slConjugation, hEeq, map_mul, map_mul,
      CatalogueBHigherLinearAction.slConjugation_scalar, one_mul, map_inv, map_inv,
      MulAut.mul_apply]
    rfl
  have hfixiff : ∀ A : SL(2, K), t₁ (iota A) = iota A ↔
      Matrix.SpecialLinearGroup.map (σ : K →+* K)
        (CatalogueBHigherLinearAction.slConjugation 2 K H⁻¹ A) =
        CatalogueBHigherLinearAction.slConjugation 2 K H⁻¹ A := by
    intro A
    rw [hE, hact]
    constructor
    · intro h1
      have h2 := iota_injective h1
      apply (CatalogueBHigherLinearAction.slConjugation 2 K H).injective
      rw [h2, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    · intro h1
      rw [h1, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  set K₀ := CFSG.GH74.GLS.IVK.fixedField σ with hK₀
  have hK₀4 : 4 ≤ Nat.card K₀ := four_le_card_fixedField hp3 σ
  set f₀ : SL(2, K₀) →* SL(2, K) :=
    (CatalogueBHigherLinearAction.slConjugation 2 K H).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.map K₀.subtype) with hf₀
  have hf₀inj : Function.Injective f₀ := by
    intro a b hab
    have h1 := (CatalogueBHigherLinearAction.slConjugation 2 K H).injective hab
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => Subtype.ext ?_
    exact congrArg (fun X : SL(2, K) => (X : Matrix (Fin 2) (Fin 2) K) i j) h1
  have hrange : ∀ A : SL(2, K), t₁ (iota A) = iota A ↔ A ∈ f₀.range := by
    intro A
    rw [hfixiff]
    constructor
    · intro h1
      have hS : ∀ i j, σ ((CatalogueBHigherLinearAction.slConjugation 2 K H⁻¹ A :
          SL(2, K)) i j) =
            (CatalogueBHigherLinearAction.slConjugation 2 K H⁻¹ A : SL(2, K)) i j := by
        intro i j
        have := congrArg (fun X : SL(2, K) => (X : Matrix (Fin 2) (Fin 2) K) i j) h1
        simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
      obtain ⟨A₀, hA₀⟩ := CFSG.GH74.GLS.IVK.exists_specialLinear_map_eq σ _ hS
      refine ⟨A₀, ?_⟩
      change CatalogueBHigherLinearAction.slConjugation 2 K H
        (Matrix.SpecialLinearGroup.map K₀.subtype A₀) = A
      rw [hA₀, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    · rintro ⟨A₀, rfl⟩
      have e : CatalogueBHigherLinearAction.slConjugation 2 K H⁻¹ (f₀ A₀) =
          Matrix.SpecialLinearGroup.map K₀.subtype A₀ := by
        change CatalogueBHigherLinearAction.slConjugation 2 K H⁻¹
          (CatalogueBHigherLinearAction.slConjugation 2 K H
            (Matrix.SpecialLinearGroup.map K₀.subtype A₀)) = _
        rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [e]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      ext i j
      exact CFSG.GH74.GLS.IVK.fixedField_apply σ (A₀ i j)
  have hTfix : ∀ t ∈ T, ∀ A ∈ f₀.range, t (iota A) = iota A := by
    intro t ht A hA
    obtain ⟨k, hk⟩ := hpow t ht
    have h1 := hfix _ (T.mul_mem (T.inv_mem (T.zpow_mem ht₁ k)) ht) hk A
    have h2 : (t₁ ^ k) (iota A) = iota A := zpow_apply_eq_self ((hrange A).mpr hA) k
    have e : t = t₁ ^ k * ((t₁ ^ k)⁻¹ * t) := by group
    rw [e, MulAut.mul_apply, h1, h2]
  set F : SL(2, K₀) →* MulAut (projectiveSL 3 K) :=
    (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).comp (iota.comp f₀) with hF
  have hFinj : Function.Injective F :=
    conj_injective_three.comp (iota_injective.comp hf₀inj)
  have hFapp : ∀ A₀, F A₀ = MulAut.conj (iota (f₀ A₀)) := fun A₀ => rfl
  have hbs : ∀ Z : SL(3, K), Z * sZero = sZero * Z →
      (∀ A₀ : SL(2, K₀), MulAut.conj (proj 3 K Z) * F A₀ = F A₀ * MulAut.conj (proj 3 K Z)) →
      IsBlockScalar (Z : Matrix (Fin 3) (Fin 3) K) := by
    intro Z hZ hcomm
    have hup : ∀ A₀ : SL(2, K₀), upper (Z : Matrix (Fin 3) (Fin 3) K) *
        (f₀ A₀ : Matrix (Fin 2) (Fin 2) K) =
        (f₀ A₀ : Matrix (Fin 2) (Fin 2) K) * upper (Z : Matrix (Fin 3) (Fin 3) K) := by
      intro A₀
      have h1 : proj 3 K Z * proj 3 K (blockEmb (f₀ A₀)) =
          proj 3 K (blockEmb (f₀ A₀)) * proj 3 K Z := by
        apply conj_injective_three
        rw [map_mul, map_mul]
        exact hcomm A₀
      have h2 := commute_of_proj_commute_block hK2 hZ (blockEmb_commute_sZero _) h1
      rw [coe_blockEmb] at h2
      have h3 := congrArg upper h2
      rwa [upper_mul (isBlock_coe hK2 hZ) (isBlock_blockMat _),
        upper_mul (isBlock_blockMat _) (isBlock_coe hK2 hZ), upper_blockMat] at h3
    let u₀ : SL(2, K₀) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let l₀ : SL(2, K₀) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    have hu : (f₀ u₀ : Matrix (Fin 2) (Fin 2) K) = H.val * !![1, 1; 0, 1] * (H⁻¹).val := by
      change ((CatalogueBHigherLinearAction.slConjugation 2 K H
        (Matrix.SpecialLinearGroup.map K₀.subtype u₀) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
      rw [CatalogueBHigherLinearAction.slConjugation_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hl : (f₀ l₀ : Matrix (Fin 2) (Fin 2) K) = H.val * !![1, 0; 1, 1] * (H⁻¹).val := by
      change ((CatalogueBHigherLinearAction.slConjugation 2 K H
        (Matrix.SpecialLinearGroup.map K₀.subtype l₀) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
      rw [CatalogueBHigherLinearAction.slConjugation_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have h1 := hup u₀
    have h2 := hup l₀
    rw [hu] at h1
    rw [hl] at h2
    obtain ⟨c', hc'⟩ := exists_scalar_of_commute_conj H h1 h2
    refine ⟨isBlock_coe hK2 hZ, ?_, ?_, ?_⟩
    · have := congrFun (congrFun hc' 0) 1
      simpa [upper] using this
    · have := congrFun (congrFun hc' 1) 0
      simpa [upper] using this
    · have h0 := congrFun (congrFun hc' 0) 0
      have h1' := congrFun (congrFun hc' 1) 1
      simp [upper] at h0 h1'
      rw [h0, h1']
  refine outerCentConcl_of_sub (S := F.range) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    rintro _ ⟨A₀, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [hFapp]
    exact mul_conj_eq_of_apply (hTfix t ht _ ⟨A₀, rfl⟩)
  ·
    intro x hx
    obtain ⟨A₀, rfl⟩ := hx
    have hA : A₀ ∈ Subgroup.closure {A : SL(2, K₀) | A ^ 3 = 1} := by
      rw [closure_pow_three_eq_top hK₀4]; exact Subgroup.mem_top _
    have h1 : (Subgroup.closure {A : SL(2, K₀) | A ^ 3 = 1}).map F ≤
        Subgroup.closure {s | s ∈ F.range ∧ s ^ 3 = 1} := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨B, hB, rfl⟩
      exact ⟨⟨B, rfl⟩, by rw [← map_pow, show B ^ 3 = 1 from hB, map_one]⟩
    exact h1 ⟨A₀, hA, rfl⟩
  ·
    rintro c hc _ ⟨A₀, rfl⟩
    obtain ⟨Z, hZ, rfl⟩ := exists_block_of_mem hX hc
    have hcT := (Subgroup.mem_inf.mp hc).2
    have hZb : IsBlk ((Matrix.SpecialLinearGroup.toGL Z : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := isBlock_coe hK2 hZ
    set A' := CatalogueBHigherLinearAction.slConjugation 2 K (upperGL hZb) (f₀ A₀) with hA'
    have hcA : MulAut.conj (proj 3 K Z) (iota (f₀ A₀)) = iota A' := by
      rw [← conjAut_toGL, conjAut_iota hZb]
    have hA'fix : t₁ (iota A') = iota A' := by
      rw [← hcA]
      have h1 := Subgroup.mem_centralizer_iff.mp hcT t₁ ht₁
      rw [← MulAut.mul_apply, h1, MulAut.mul_apply, hTfix t₁ ht₁ _ ⟨A₀, rfl⟩]
    obtain ⟨A₀', hA₀'⟩ := (hrange A').mp hA'fix
    refine ⟨A₀', ?_⟩
    rw [hFapp, hFapp, hA₀', mul_conj_mul_inv', hcA]
  ·
    intro Q hQS hQ2 hQn q hq s hs
    obtain ⟨a, rfl⟩ := hQS hq
    obtain ⟨b, rfl⟩ := hs
    let Q' : Subgroup SL(2, K₀) := Q.comap F
    have hQ'n : Q'.Normal := ⟨fun x hx y => by
      change F (y * x * y⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      exact hQn (F y) ⟨y, rfl⟩ (F x) hx⟩
    have hQ'2 : ∀ x ∈ Q', ∃ e : ℕ, x ^ 2 ^ e = 1 := by
      intro x hx
      obtain ⟨e, he⟩ := hQ2 ⟨F x, hx⟩
      refine ⟨e, hFinj ?_⟩
      rw [map_pow, map_one]
      simpa using congrArg Subtype.val he
    have hcen := le_center_of_normal_two hK₀4 Q' hQ'2 (show a ∈ Q' from hq)
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen b]
  ·
    have : Group.IsPerfect SL(2, K₀) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K₀)
        (CFSG.LinearGroups.exists_finset_card_eq_four hK₀4)
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  ·
    intro c hc hcS c' hc'
    obtain ⟨Z, hZ, rfl⟩ := exists_block_of_mem hX hc
    obtain ⟨W, hW, rfl⟩ := exists_block_of_mem hX hc'
    have hZbs := hbs Z hZ fun A₀ => hcS _ ⟨A₀, rfl⟩
    have h1 := commute_of_isBlockScalar_of_isBlk hZbs (isBlock_coe hK2 hW)
    have h2 : Z * W = W * Z := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact h1)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h2]
  ·
    intro P hP hPS hP2
    have hPbs : ∀ y ∈ P, ∃ Z : SL(3, K), Z * sZero = sZero * Z ∧
        IsBlockScalar (Z : Matrix (Fin 3) (Fin 3) K) ∧ y = MulAut.conj (proj 3 K Z) := by
      intro y hy
      obtain ⟨Z, hZ, rfl⟩ := exists_block_of_mem hX (hP hy)
      exact ⟨Z, hZ, hbs Z hZ fun A₀ => hPS _ hy _ ⟨A₀, rfl⟩, rfl⟩
    have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
      intro a ha b hb
      obtain ⟨Za, hZa, hZabs, rfl⟩ := hPbs a ha
      obtain ⟨Zb, hZb, -, rfl⟩ := hPbs b hb
      have h1 := commute_of_isBlockScalar_of_isBlk hZabs (isBlock_coe hK2 hZb)
      have h2 : Za * Zb = Zb * Za := Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        exact h1)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h2]
    have hPinv : ∀ y ∈ P, y ^ 2 = 1 → y ≠ 1 → y = xZero := by
      intro y hy hy2 hy1
      obtain ⟨Z, -, hZbs, rfl⟩ := hPbs y hy
      have h2 : proj 3 K Z ^ 2 = 1 := conj_injective_three (by rw [map_pow, hy2, map_one])
      rcases eq_one_or_eq_x0_of_blockScalar hZbs h2 with h | h
      · exact absurd (by rw [h, map_one]) hy1
      · rw [h]
        rfl
    have : Finite P := Subgroup.instFiniteSubtypeMem P
    exact isCyclic_of_comm_unique hPcomm hP2 fun a ha b hb ha2 hb2 ha1 hb1 => by
      rw [hPinv a ha ha2 ha1, hPinv b hb hb2 hb1]

end Field

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
