module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithTools
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithNF

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec14.Item148Rank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (finite_mulAut_projectiveSL)

variable {K : Type} [Field K]

theorem coe_diagSL_eq (a b d : K) (h : a * b * d = 1) :
    ((diagSL a b d h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![a, b, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagSL]

theorem diagonal_mul_comm (d e : Fin 3 → K) :
    diagonal d * diagonal e = diagonal e * diagonal d := by
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem heisC_mul_diagonal (α x y z : K) :
    !![0, 0, α; 1, 0, 0; 0, 1, 0] * diagonal ![x, y, z] =
      diagonal ![z, x, y] * !![0, 0, α; 1, 0, 0; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem commute_of_intertwine {M Q Q' Δ D : Matrix (Fin 3) (Fin 3) K} (hM : M * Q = Q * Δ)
    (hQQ' : Q * Q' = 1) (hQ'Q : Q' * Q = 1) (hΔD : Δ * D = D * Δ) :
    M * (Q * D * Q') = (Q * D * Q') * M := by
  have hM' : M = Q * Δ * Q' := by
    calc M = M * (Q * Q') := by rw [hQQ', Matrix.mul_one]
      _ = Q * Δ * Q' := by rw [← Matrix.mul_assoc, hM]
  rw [hM']
  calc Q * Δ * Q' * (Q * D * Q') = Q * (Δ * (Q' * Q) * D) * Q' := by
        simp only [Matrix.mul_assoc]
    _ = Q * (D * (Q' * Q) * Δ) * Q' := by rw [hQ'Q, Matrix.mul_one, Matrix.mul_one, hΔD]
    _ = Q * D * Q' * (Q * Δ * Q') := by simp only [Matrix.mul_assoc]

theorem conjUnit_eq_of_commute {A : GL (Fin 3) K} {t : SpecialLinearGroup (Fin 3) K}
    (h : (A : Matrix (Fin 3) (Fin 3) K) * t = t * A) : conjUnit A t = t := by
  apply Subtype.ext
  rw [conjUnit_coe, h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem glAut_inv_eq {σ : K ≃+* K} {A : GL (Fin 3) K} (h : glAut σ A = A) :
    glAut σ A⁻¹ = A⁻¹ := by
  rw [map_inv, h]

theorem glAut_map_subtype {σ : K ≃+* K} {k : Subfield K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    (P : GL (Fin 3) k) : glAut σ (GeneralLinearGroup.map k.subtype P) =
      GeneralLinearGroup.map k.subtype P := by
  apply Units.ext
  ext i j
  rw [coe_glAut, Matrix.map_apply, GeneralLinearGroup.map_apply]
  exact (hk _).1 ((P : Matrix (Fin 3) (Fin 3) k) i j).2

theorem mem_of_glAut_eq {σ : K ≃+* K} {k : Subfield K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    {A : GL (Fin 3) K} (h : glAut σ A = A) (i j : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) K) i j ∈ k := by
  rw [hk]
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) i j) h
  simpa [coe_glAut] using this

theorem fixed_of_glAut_scalar {σ : K ≃+* K} {c : Kˣ}
    (h : glAut σ (GeneralLinearGroup.scalar (Fin 3) c) = GeneralLinearGroup.scalar (Fin 3) c) :
    σ (c : K) = c := by
  rw [glAut_scalar148] at h
  have := scalar_injective148 h
  exact congrArg Units.val this

theorem twisted_torus_fixed {σ : K ≃+* K} (hσσσ : ∀ x, σ (σ (σ x)) = x) {P b : GL (Fin 3) K}
    {α : K} (hPσ : glAut σ P = P) (hbσ : glAut σ b = b)
    (hb : (b : Matrix (Fin 3) (Fin 3) K) * P = P * !![0, 0, α; 1, 0, 0; 0, 1, 0]) {u : K}
    (hN : u * σ u * σ (σ u) = 1) :
    SpecialLinearGroup.map σ.toRingHom (conjUnit b (conjUnit P (diagSL u (σ u) (σ (σ u)) hN))) =
      conjUnit P (diagSL u (σ u) (σ (σ u)) hN) := by
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![u, σ u, σ (σ u)] with hD
  set D' : Matrix (Fin 3) (Fin 3) K := diagonal ![σ u, σ (σ u), u] with hD'
  set C : Matrix (Fin 3) (Fin 3) K := !![0, 0, α; 1, 0, 0; 0, 1, 0] with hC
  have hfix : ∀ A : GL (Fin 3) K, glAut σ A = A →
      (A : Matrix (Fin 3) (Fin 3) K).map σ = A := fun A hA => by
    rw [← coe_glAut, hA]
  have hP' := hfix _ (glAut_inv_eq hPσ)
  have hb' := hfix _ (glAut_inv_eq hbσ)
  have hDσ : D.map σ = D' := by
    rw [hD, hD', diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [hσσσ]
  have hCD : C * D' = D * C := by
    rw [hC, hD, hD']
    exact heisC_mul_diagonal α (σ u) (σ (σ u)) u
  have hPi : (P : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := Units.mul_inv P
  have hiP : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
      1 := Units.inv_mul P
  have hbP : (b : Matrix (Fin 3) (Fin 3) K) = P * C * ((P⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) := by
    calc (b : Matrix (Fin 3) (Fin 3) K) = b * (P * ((P⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)) := by rw [hPi, Matrix.mul_one]
      _ = P * C * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.mul_assoc, hb]
  have hcomm : (b : Matrix (Fin 3) (Fin 3) K) * (P * D' * ((P⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) = (P * D * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
      b := by
    rw [hbP]
    calc P * C * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (P * D' * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        = P * (C * (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * P) * D') *
          ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
      _ = P * (D * (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * P) * C) *
          ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hiP, Matrix.mul_one, Matrix.mul_one, hCD]
      _ = P * D * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (P * C * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          simp only [Matrix.mul_assoc]
  apply Subtype.ext
  change ((conjUnit b (conjUnit P (diagSL u (σ u) (σ (σ u)) hN)) :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ = _
  rw [conjUnit_coe, conjUnit_coe, coe_diagSL_eq, ← hD, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hfix b hbσ, hfix P hPσ, hP', hb', hDσ, hcomm,
    Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

variable [Finite K]

theorem closure_fix_eq_top_field {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hK : p ^ f % 3 = 1) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {k : Subfield K} (hk : ∀ x, x ∈ k ↔ σ x = x) (hkK : Nat.card K = Nat.card k ^ 3)
    (hk4 : 4 ≤ Nat.card k) (B : Subgroup (MulAut (projectiveSL 3 K)))
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hB27 : Nat.card B = 27) (hσB : fieldAut 3 K σ ∈ B) :
    ∃ F₀ : Subgroup (MulAut (projectiveSL 3 K)), F₀ ≤ B ∧ Nat.card F₀ = 9 ∧
      Subgroup.closure ({x | fieldAut 3 K σ x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x}) = ⊤ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (projectiveSL 3 K)) := finite_mulAut_projectiveSL 3
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by rintro rfl; rw [orderOf_one] at hσ; omega
  have hσσσ : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hσ3
    simpa [pow_succ] using this
  have hk3 : Nat.card k % 3 = 1 := by
    have h := hK
    rw [← hcard, hkK, pow_three_mod_three148] at h
    exact h
  set fσ := fieldAut 3 K σ with hfσ
  have hfσ3 : fσ ^ 3 = 1 := by rw [hfσ, ← map_pow, hσ3, map_one]
  have hfσin : ¬ IsInnerAut fσ := not_isInnerAut_fieldAut hσ1
  have hfσD : fσ ∉ linearAutGroup 3 K := fieldAut_not_mem_linearAutGroup hσ1
  set A : Subgroup (MulAut (projectiveSL 3 K)) :=
    B ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range with hA
  have hAB : A ≤ B := inf_le_left
  have hcoset : ∀ β ∈ B, ∃ j : ℕ, j < 3 ∧ β * fσ ^ j ∈ A := by
    intro β hβ
    obtain ⟨j, hj⟩ := exists_isInnerAut_mul_pow_linear148 hp hf hcard hK hfσ3 (hB3 β hβ)
      (hBab _ hσB _ hβ) hfσin
    refine ⟨j % 3, Nat.mod_lt _ (by norm_num), B.mul_mem hβ (B.pow_mem hσB _), ?_⟩
    rw [pow_mod_three_eq hfσ3]
    exact hj
  have hA9 : 9 ≤ Nat.card A := by
    have hsurj : Function.Surjective (fun x : A × Fin 3 =>
        (⟨(x.1 : MulAut (projectiveSL 3 K)) * (fσ ^ (x.2 : ℕ))⁻¹,
          B.mul_mem (hAB x.1.2) (B.inv_mem (B.pow_mem hσB _))⟩ : B)) := by
      rintro ⟨β, hβ⟩
      obtain ⟨j, hj3, hjA⟩ := hcoset β hβ
      refine ⟨(⟨_, hjA⟩, ⟨j, hj3⟩), Subtype.ext ?_⟩
      simp
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hB27, Nat.card_prod, Nat.card_fin] at this
    omega
  obtain ⟨a₁, ha₁A, ha₁1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [hbot, Subgroup.card_bot] at hA9
    omega
  have ha₁3 : a₁ ^ 3 = 1 := hB3 _ (hAB ha₁A)
  obtain ⟨a₂, ha₂A, ha₂z⟩ : ∃ a ∈ A, a ∉ Subgroup.zpowers a₁ := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers a₁ from h)
    rw [Nat.card_zpowers] at h1
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) ha₁3
    omega
  have ha₂3 : a₂ ^ 3 = 1 := hB3 _ (hAB ha₂A)
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := hBab _ (hAB ha₁A) _ (hAB ha₂A)
  have hrep : ∀ a ∈ A, ∃ g : GL (Fin 3) K, conjAut 3 K g = a ∧ glAut σ g = g := by
    intro a haA
    obtain ⟨z, hz⟩ := (Subgroup.mem_inf.1 haA).2
    obtain ⟨h, rfl⟩ := proj_surjective 3 K z
    have ha : conjAut 3 K (SpecialLinearGroup.toGL h) = a := by
      rw [← conj_proj_eq_conjAut, hz]
    have hcomm : conjAut 3 K (SpecialLinearGroup.toGL h) * fσ =
        fσ * conjAut 3 K (SpecialLinearGroup.toGL h) := by
      rw [ha]
      exact hBab _ (hAB haA) _ hσB
    obtain ⟨c, hc⟩ := exists_glAut_eq_scalar_mul148 σ _ hcomm
    have hc3 : c ^ 3 = 1 := by
      have h1 := congrArg GeneralLinearGroup.det hc
      have hdet : GeneralLinearGroup.det (SpecialLinearGroup.toGL h) = 1 := by
        apply Units.ext
        simp
      rw [det_glAut148, map_mul, det_scalar_three148, hdet, map_one, mul_one] at h1
      exact h1.symm
    obtain ⟨μ, hμ⟩ := exists_units_map_eq_mul hk hkK hk3 (c := c⁻¹)
      (by rw [inv_pow, hc3, inv_one])
    refine ⟨GeneralLinearGroup.scalar (Fin 3) μ * SpecialLinearGroup.toGL h,
      by rw [map_mul, conjAut_scalar, one_mul, ha], ?_⟩
    rw [map_mul, glAut_scalar148, hc, hμ, ← mul_assoc, ← map_mul]
    congr 2
    rw [mul_comm c⁻¹ μ, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨g₁, hg₁, hg₁σ⟩ := hrep a₁ ha₁A
  obtain ⟨g₂, hg₂, hg₂σ⟩ := hrep a₂ ha₂A
  obtain ⟨x, hx⟩ := exists_map_eq_of_mem k (mem_of_glAut_eq hk hg₁σ)
  obtain ⟨y, hy⟩ := exists_map_eq_of_mem k (mem_of_glAut_eq hk hg₂σ)
  have hlift_scalar : ∀ c : Kˣ, glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) c → ∃ c' : kˣ,
        GeneralLinearGroup.map k.subtype (GeneralLinearGroup.scalar (Fin 3) c') =
          GeneralLinearGroup.scalar (Fin 3) c := by
    intro c hc
    obtain ⟨c', hc'⟩ := exists_units_map_eq_of_mem k ((hk _).2 (fixed_of_glAut_scalar hc))
    refine ⟨c', ?_⟩
    rw [GeneralLinearGroup.map_scalar]
    congr 1
  have hinj := map_subtype_injective k
  obtain ⟨α, hα⟩ := exists_pow_three_eq_scalar (A := g₁) (by rw [hg₁]; exact ha₁3)
  obtain ⟨β, hβ⟩ := exists_pow_three_eq_scalar (A := g₂) (by rw [hg₂]; exact ha₂3)
  obtain ⟨ω, hω⟩ := exists_mul_eq_scalar_mul (A := g₁) (A' := g₂) (by rw [hg₁, hg₂]; exact ha₁₂)
  obtain ⟨α', hα'⟩ := hlift_scalar α (by rw [← hα, map_pow, hg₁σ])
  obtain ⟨β', hβ'⟩ := hlift_scalar β (by rw [← hβ, map_pow, hg₂σ])
  obtain ⟨ω', hω'⟩ := hlift_scalar ω (by
    have h1 := congrArg (glAut σ) hω
    rw [map_mul, map_mul, map_mul, hg₁σ, hg₂σ] at h1
    have h2 : glAut σ (GeneralLinearGroup.scalar (Fin 3) ω) * (g₁ * g₂) =
        GeneralLinearGroup.scalar (Fin 3) ω * (g₁ * g₂) := by rw [← h1, ← hω]
    exact mul_right_cancel h2)
  have hx3 : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) α' :=
    hinj (by rw [map_pow, hx, hα, hα'])
  have hy3 : y ^ 3 = GeneralLinearGroup.scalar (Fin 3) β' :=
    hinj (by rw [map_pow, hy, hβ, hβ'])
  have hyx : y * x = GeneralLinearGroup.scalar (Fin 3) ω' * (x * y) :=
    hinj (by rw [map_mul, map_mul, map_mul, hx, hy, hω, hω'])
  have hind : ∀ a b : ℕ, (∃ c : kˣ, x ^ a * y ^ b = GeneralLinearGroup.scalar (Fin 3) c) →
      3 ∣ a ∧ 3 ∣ b := by
    rintro a b ⟨c, hc⟩
    have h1 := congrArg (GeneralLinearGroup.map k.subtype) hc
    rw [map_mul, map_pow, map_pow, hx, hy, GeneralLinearGroup.map_scalar] at h1
    have h2 : a₁ ^ a * a₂ ^ b = 1 := by
      rw [← hg₁, ← hg₂, ← map_pow, ← map_pow, ← map_mul, h1, conjAut_scalar]
    exact three_dvd_of_pow_mul_pow_eq_one ha₁3 ha₂3 ha₁1 ha₂z h2
  set H : Subgroup (GL (Fin 3) k) :=
    (A.comap (conjAut 3 K)).comap (GeneralLinearGroup.map k.subtype) with hH
  have hHs : ∀ c : kˣ, GeneralLinearGroup.scalar (Fin 3) c ∈ H := by
    intro c
    rw [hH, Subgroup.mem_comap, Subgroup.mem_comap, GeneralLinearGroup.map_scalar,
      conjAut_scalar]
    exact A.one_mem
  have hxH : x ∈ H := by
    rw [hH, Subgroup.mem_comap, Subgroup.mem_comap, hx, hg₁]
    exact ha₁A
  have hyH : y ∈ H := by
    rw [hH, Subgroup.mem_comap, Subgroup.mem_comap, hy, hg₂]
    exact ha₂A
  have hkF3 : 3 ∣ Nat.card k - 1 := by omega
  have hζ := exists_isPrimitiveRoot_three hkF3
  have hfix_sl : ∀ g ∈ CFSG.RankThree.PartOne.CTP.slSub 3 k, fσ (proj 3 K g) = proj 3 K g :=
    fun g hg => fieldAut_proj_of_mem_slSub hk hg
  have hroot : ∀ P : GL (Fin 3) k, conjUnit (GeneralLinearGroup.map k.subtype P)
      (SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1) ∈
        CFSG.RankThree.PartOne.CTP.slSub 3 k := by
    intro P
    refine conjUnit_mem_slSub k P ?_
    exact CFSG.RankThree.PartOne.CTP.transvection_mem_slSub _ k.one_mem
  rcases toral_or_heis hkF3 hζ H hHs hxH hyH hyx hx3 hy3 hind with
    ⟨P, hP⟩ | ⟨x', hx'H, y', hy'H, P, ξ, w, α₀, hw, hPy, hPx⟩
  ·
    obtain ⟨u, hu⟩ : ∃ u : K, u ∉ k := by
      by_contra h
      push Not at h
      have h1 : Nat.card k = Nat.card K := Nat.card_congr (Equiv.subtypeUnivEquiv h)
      rw [hkK] at h1
      have h2 : Nat.card k ^ 3 = Nat.card k ^ 1 := by rw [← h1, pow_one]
      have h3 := Nat.pow_right_injective (le_trans (by norm_num) hk4) h2
      omega
    have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ k.zero_mem)
    obtain ⟨Q, hQ⟩ : ∃ Q : GL (Fin 3) k, Q = P⁻¹ := ⟨_, rfl⟩
    set QK : GL (Fin 3) K := GeneralLinearGroup.map k.subtype Q with hQK
    have hdiag : ∀ z : GL (Fin 3) k, (∀ i j : Fin 3, i ≠ j →
        ((P * z * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i j = 0) →
        ∃ d : Fin 3 → K, (GeneralLinearGroup.map k.subtype z : Matrix (Fin 3) (Fin 3) K) * QK =
          QK * diagonal d := by
      intro z hz
      set e : Fin 3 → k := fun i => ((P * z * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i
      have he : ((P * z * P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal e := by
        refine Matrix.ext fun i j => ?_
        by_cases hij : i = j
        · subst hij
          simp [e]
        · rw [diagonal_apply_ne _ hij]
          exact hz i j hij
      have hzQ : (z : Matrix (Fin 3) (Fin 3) k) * Q = Q * diagonal e := by
        rw [← he, hQ, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          ← Units.val_mul P⁻¹ P, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      refine ⟨fun i => (e i : K), ?_⟩
      have h1 := congrArg (Matrix.map · k.subtype) hzQ
      simp only [Matrix.map_mul] at h1
      have h2 : (diagonal e).map k.subtype = diagonal (fun i => (e i : K)) :=
        diagonal_map (map_zero _)
      have hmap : ∀ g : GL (Fin 3) k, (GeneralLinearGroup.map k.subtype g :
          Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) k).map k.subtype := fun g => by
        ext i j
        rw [GeneralLinearGroup.map_apply]
        rfl
      rw [hmap, hQK, hmap, ← h2]
      exact h1
    obtain ⟨d₁, hd₁⟩ := hdiag x (fun i j hij => (hP i j hij).1)
    obtain ⟨d₂, hd₂⟩ := hdiag y (fun i j hij => (hP i j hij).2)
    have huu : u * 1 * u⁻¹ = 1 := by rw [mul_one, mul_inv_cancel₀ hu0]
    set D : SpecialLinearGroup (Fin 3) K := diagSL u 1 u⁻¹ huu with hDdef
    set t : SpecialLinearGroup (Fin 3) K := conjUnit QK D with ht
    have hQQ : (QK : Matrix (Fin 3) (Fin 3) K) * ((QK⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv QK
    have hQQ' : ((QK⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (QK : Matrix (Fin 3) (Fin 3) K) = 1 := Units.inv_mul QK
    have hfixt : ∀ (z : GL (Fin 3) k) (d : Fin 3 → K),
        (GeneralLinearGroup.map k.subtype z : Matrix (Fin 3) (Fin 3) K) * QK = QK * diagonal d →
        conjAut 3 K (GeneralLinearGroup.map k.subtype z) (proj 3 K t) = proj 3 K t := by
      intro z d hzd
      rw [conjAut_proj_eq_conjUnit]
      congr 1
      apply conjUnit_eq_of_commute
      rw [ht, conjUnit_coe, hDdef, coe_diagSL_eq]
      exact commute_of_intertwine hzd hQQ hQQ' (diagonal_mul_comm _ _)
    set F₀ : Subgroup (MulAut (projectiveSL 3 K)) :=
      Subgroup.closure ({a₁, a₂} : Set (MulAut (projectiveSL 3 K))) with hF₀
    have hF₀B : F₀ ≤ B := by
      rw [hF₀, Subgroup.closure_le]
      rintro _ (rfl | h)
      · exact hAB ha₁A
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hAB ha₂A
    refine ⟨F₀, hF₀B, card_closure_eq_nine ha₁₂ ha₁3 ha₂3 ha₁1 ha₂z
      (fun z hz => hB3 z (hF₀B hz)), ?_⟩
    have htF : proj 3 K t ∈ {x | ∀ φ ∈ F₀, φ x = x} := by
      intro φ hφ
      have hle : F₀ ≤ MulAction.stabilizer (MulAut (projectiveSL 3 K)) (proj 3 K t) := by
        rw [hF₀, Subgroup.closure_le]
        rintro _ (rfl | h)
        · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def, ← hg₁, ← hx]
          exact hfixt x d₁ hd₁
        · rw [Set.mem_singleton_iff] at h
          rw [h, SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def, ← hg₂, ← hy]
          exact hfixt y d₂ hd₂
      have := hle hφ
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    set Y := Subgroup.closure ({x | fσ x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x}) with hY
    have hYsl : ∀ g ∈ CFSG.RankThree.PartOne.CTP.slSub 3 k, proj 3 K g ∈ Y :=
      fun g hg => Subgroup.subset_closure (Or.inl (hfix_sl g hg))
    have htY : proj 3 K t ∈ Y := Subgroup.subset_closure (Or.inr htF)
    refine eq_top_of_conj_root hkK hYsl Q hu ?_
    have hconj : t * conjUnit QK (SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1)
        * t⁻¹ = conjUnit QK (SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) u) := by
      rw [ht, ← map_mul, ← map_inv, ← map_mul, hDdef, diagSL_mul_xr01, mul_assoc, mul_inv_cancel,
        mul_one, div_one, mul_one]
    rw [← hconj, map_mul, map_mul, map_inv]
    exact Y.mul_mem (Y.mul_mem htY (hYsl _ (hroot Q))) (Y.inv_mem htY)
  ·
    set s : GL (Fin 3) K := GeneralLinearGroup.map k.subtype y' with hs
    set b : GL (Fin 3) K := GeneralLinearGroup.map k.subtype x' with hb
    set PK : GL (Fin 3) K := GeneralLinearGroup.map k.subtype P with hPK
    have hmap : ∀ g : GL (Fin 3) k, (GeneralLinearGroup.map k.subtype g :
        Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) k).map k.subtype := fun g => by
      ext i j
      rw [GeneralLinearGroup.map_apply]
      rfl
    have hsP : (s : Matrix (Fin 3) (Fin 3) K) * PK =
        PK * diagonal ![(ξ : K), (ξ : K) * w, (ξ : K) * w ^ 2] := by
      have h1 := congrArg (Matrix.map · k.subtype) hPy
      simp only [Matrix.map_mul] at h1
      rw [hs, hPK, hmap, hmap, h1, diagonal_map (map_zero _)]
      congr 2
      funext i
      fin_cases i <;> simp
    have hbP : (b : Matrix (Fin 3) (Fin 3) K) * PK =
        PK * !![0, 0, (α₀ : K); 1, 0, 0; 0, 1, 0] := by
      have h1 := congrArg (Matrix.map · k.subtype) hPx
      simp only [Matrix.map_mul] at h1
      rw [hb, hPK, hmap, hmap, h1]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hsA : conjAut 3 K s ∈ A := hy'H
    have hbA : conjAut 3 K b ∈ A := hx'H
    obtain ⟨u, hu0, hN, huk⟩ := exists_norm_one_not_mem hk hkK hσσσ
    set D : SpecialLinearGroup (Fin 3) K := diagSL u (σ u) (σ (σ u)) hN with hDdef
    set t : SpecialLinearGroup (Fin 3) K := conjUnit PK D with ht
    have hPP : (PK : Matrix (Fin 3) (Fin 3) K) * ((PK⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv PK
    have hPP' : ((PK⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (PK : Matrix (Fin 3) (Fin 3) K) = 1 := Units.inv_mul PK
    have hfix1 : conjAut 3 K s (proj 3 K t) = proj 3 K t := by
      rw [conjAut_proj_eq_conjUnit]
      congr 1
      apply conjUnit_eq_of_commute
      rw [ht, conjUnit_coe, hDdef, coe_diagSL_eq]
      exact commute_of_intertwine hsP hPP hPP' (diagonal_mul_comm _ _)
    have hfix2 : (fσ * conjAut 3 K b) (proj 3 K t) = proj 3 K t := by
      rw [MulAut.mul_apply, conjAut_proj_eq_conjUnit, hfσ, fieldAut_proj]
      congr 1
      exact twisted_torus_fixed hσσσ (glAut_map_subtype hk P) (glAut_map_subtype hk x') hbP hN
    set F₀ : Subgroup (MulAut (projectiveSL 3 K)) :=
      Subgroup.closure ({conjAut 3 K s, fσ * conjAut 3 K b} : Set (MulAut (projectiveSL 3 K)))
      with hF₀
    have hsB : conjAut 3 K s ∈ B := hAB hsA
    have hbB : fσ * conjAut 3 K b ∈ B := B.mul_mem hσB (hAB hbA)
    have hF₀B : F₀ ≤ B := by
      rw [hF₀, Subgroup.closure_le]
      rintro _ (rfl | h)
      · exact hsB
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hbB
    have hs1 : conjAut 3 K s ≠ 1 := by
      intro h1
      obtain ⟨e, he⟩ := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff
        le_rfl s).1 h1
      have h2 : (e : K) • (PK : Matrix (Fin 3) (Fin 3) K) =
          PK * diagonal ![(ξ : K), (ξ : K) * w, (ξ : K) * w ^ 2] := by
        rw [← hsP, he, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul]
      have h3 : diagonal ![(ξ : K), (ξ : K) * w, (ξ : K) * w ^ 2] = (e : K) • 1 := by
        calc diagonal ![(ξ : K), (ξ : K) * w, (ξ : K) * w ^ 2]
            = ((PK⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (PK * diagonal
              ![(ξ : K), (ξ : K) * w, (ξ : K) * w ^ 2]) := by
                rw [← Matrix.mul_assoc, hPP', Matrix.one_mul]
          _ = (e : K) • 1 := by rw [← h2, Matrix.mul_smul, hPP']
      have h00 := congrFun (congrFun h3 0) 0
      have h11 := congrFun (congrFun h3 1) 1
      simp at h00 h11
      have hξ0 : (ξ : K) ≠ 0 := by rw [h00]; exact e.ne_zero
      have hw1 : (w : K) = 1 := by
        have : (ξ : K) * w = (ξ : K) * 1 := by rw [mul_one, h11, h00]
        exact mul_left_cancel₀ hξ0 this
      have hw1' : w = 1 := Subtype.ext hw1
      exact hw.ne_one (by norm_num) hw1'
    have hbz : fσ * conjAut 3 K b ∉ Subgroup.zpowers (conjAut 3 K s) := by
      rintro ⟨m, hm⟩
      apply hfσD
      have h1 : fσ = conjAut 3 K s ^ m * (conjAut 3 K b)⁻¹ := by
        simp only at hm
        rw [hm, mul_inv_cancel_right]
      rw [h1, ← map_zpow, ← map_inv, ← map_mul]
      exact conjAut_mem_linearAutGroup _
    refine ⟨F₀, hF₀B, card_closure_eq_nine (hBab _ hsB _ hbB) (hB3 _ hsB) (hB3 _ hbB) hs1 hbz
      (fun z hz => hB3 z (hF₀B hz)), ?_⟩
    have htF : proj 3 K t ∈ {x | ∀ φ ∈ F₀, φ x = x} := by
      intro φ hφ
      have hle : F₀ ≤ MulAction.stabilizer (MulAut (projectiveSL 3 K)) (proj 3 K t) := by
        rw [hF₀, Subgroup.closure_le]
        rintro _ (rfl | h)
        · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
          exact hfix1
        · rw [Set.mem_singleton_iff] at h
          rw [h, SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
          exact hfix2
      have := hle hφ
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    set Y := Subgroup.closure ({x | fσ x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x}) with hY
    have hYsl : ∀ g ∈ CFSG.RankThree.PartOne.CTP.slSub 3 k, proj 3 K g ∈ Y :=
      fun g hg => Subgroup.subset_closure (Or.inl (hfix_sl g hg))
    have htY : proj 3 K t ∈ Y := Subgroup.subset_closure (Or.inr htF)
    have hσu0 : σ u ≠ 0 := by rw [map_ne_zero]; exact hu0
    refine eq_top_of_conj_root hkK hYsl P (c := u / σ u * 1) (by rwa [mul_one, div_eq_mul_inv]) ?_
    have hconj : t * conjUnit PK (SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1)
        * t⁻¹ = conjUnit PK (SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1)
          (u / σ u * 1)) := by
      rw [ht, ← map_mul, ← map_inv, ← map_mul, hDdef, diagSL_mul_xr01, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [← hconj, map_mul, map_mul, map_inv]
    exact Y.mul_mem (Y.mul_mem htY (hYsl _ (hroot P))) (Y.inv_mem htY)

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
