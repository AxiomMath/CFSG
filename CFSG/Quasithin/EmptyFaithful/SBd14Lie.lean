module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.Quasithin.EmptyFaithful.SBd9LieA

public section

namespace CFSG.Quasithin.SBd14

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter CFSG.Quasithin.SBd9

variable {K : Type} [Field K]

@[expose] def uni (s r c : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, s, c; 0, 1, r; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem uni_coe (s r c : K) : (uni s r c : Matrix (Fin 3) (Fin 3) K) = !![1, s, c; 0, 1, r; 0, 0, 1] :=
  rfl

theorem uni_mem (s r c : K) : uni s r c ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [uni_coe, Fin.lt_def]
  · fin_cases i <;> simp [uni_coe]

theorem eq_uni_of_mem {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K) :
    u = uni ((u : Matrix (Fin 3) (Fin 3) K) 0 1) ((u : Matrix (Fin 3) (Fin 3) K) 1 2)
      ((u : Matrix (Fin 3) (Fin 3) K) 0 2) := by
  obtain ⟨hlow, hdiag⟩ := hu
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni_coe, hdiag 0, hdiag 1, hdiag 2, hlow 1 0 (by decide), hlow 2 0 (by decide),
      hlow 2 1 (by decide)]

theorem corner_eq_uni (c : K) : corner c = uni 0 0 c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corner_coe, uni_coe]

theorem uni_mul (s r c s' r' c' : K) :
    uni s r c * uni s' r' c' = uni (s + s') (r + r') (c + c' + s * r') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni_coe, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uni_injective {s r c s' r' c' : K} (h : uni s r c = uni s' r' c') :
    s = s' ∧ r = r' ∧ c = c' := by
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [uni_coe] at h1
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrFun (congrFun h1 0) 1
  · simpa using congrFun (congrFun h1 1) 2
  · simpa using congrFun (congrFun h1 0) 2

@[expose] def IsUT (A : GL (Fin 3) K) : Prop :=
  (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0

theorem IsUT.diag_ne_zero {A : GL (Fin 3) K} (h : IsUT A) :
    (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
  obtain ⟨h10, h20, h21⟩ := h
  have hd : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [Matrix.det_fin_three, h10, h20, h21] at hd
  refine ⟨?_, ?_, ?_⟩ <;> intro h0 <;> apply hd <;> simp [h0]

theorem mat_conj_aux (p q m x y z s r c : K) (hq : q ≠ 0) (hm : m ≠ 0) :
    !![p, x, y; 0, q, z; 0, 0, m] * !![1, s, c; 0, 1, r; 0, 0, 1] =
      !![1, p * q⁻¹ * s, (p * c + x * r - p * q⁻¹ * s * z) * m⁻¹; 0, 1, q * m⁻¹ * r; 0, 0, 1] *
        !![p, x, y; 0, q, z; 0, 0, m] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

theorem IsUT.matrix_eq {A : GL (Fin 3) K} (h : IsUT A) :
    (A : Matrix (Fin 3) (Fin 3) K) =
      !![(A : Matrix (Fin 3) (Fin 3) K) 0 0, (A : Matrix (Fin 3) (Fin 3) K) 0 1,
        (A : Matrix (Fin 3) (Fin 3) K) 0 2; 0, (A : Matrix (Fin 3) (Fin 3) K) 1 1,
        (A : Matrix (Fin 3) (Fin 3) K) 1 2; 0, 0, (A : Matrix (Fin 3) (Fin 3) K) 2 2] := by
  obtain ⟨h10, h20, h21⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h20, h21]

theorem conj_uni {A : GL (Fin 3) K} (hA : IsUT A) (s r c : K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A (uni s r c) =
      uni ((A : Matrix (Fin 3) (Fin 3) K) 0 0 * ((A : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹ * s)
        ((A : Matrix (Fin 3) (Fin 3) K) 1 1 * ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹ * r)
        (((A : Matrix (Fin 3) (Fin 3) K) 0 0 * c + (A : Matrix (Fin 3) (Fin 3) K) 0 1 * r -
          (A : Matrix (Fin 3) (Fin 3) K) 0 0 * ((A : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹ * s *
            (A : Matrix (Fin 3) (Fin 3) K) 1 2) * ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹) := by
  obtain ⟨-, h11, h22⟩ := hA.diag_ne_zero
  have hAm := hA.matrix_eq
  have hmain := mat_conj_aux ((A : Matrix (Fin 3) (Fin 3) K) 0 0) ((A : Matrix (Fin 3) (Fin 3) K) 1 1)
    ((A : Matrix (Fin 3) (Fin 3) K) 2 2) ((A : Matrix (Fin 3) (Fin 3) K) 0 1)
    ((A : Matrix (Fin 3) (Fin 3) K) 0 2) ((A : Matrix (Fin 3) (Fin 3) K) 1 2) s r c h11 h22
  rw [← hAm] at hmain
  refine Subtype.ext ?_
  rw [coe_slConjugation]
  have hinv : (A : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [uni_coe]
  calc (A : Matrix (Fin 3) (Fin 3) K) * !![1, s, c; 0, 1, r; 0, 0, 1] *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = _ * ((A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [hmain, Matrix.mul_assoc]
    _ = _ := by rw [hinv, Matrix.mul_one]

theorem isUT_diagGL (x : Kˣ) : IsUT (diagGL x : GL (Fin 3) K) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [coe_diagGL]

theorem conjAut_mem_ubar {A : GL (Fin 3) K} (hA : IsUT A) {y : projectiveSL 3 K}
    (hy : y ∈ projUnitriangular 3 K) : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K A y ∈ projUnitriangular 3 K := by
  obtain ⟨u, hu, rfl⟩ := hy
  rw [conjAut_proj, eq_uni_of_mem hu, conj_uni hA]
  exact Subgroup.mem_map_of_mem _ (uni_mem _ _ _)

theorem conjAut_diagGL_mem_iff (x : Kˣ) (y : projectiveSL 3 K) :
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K (diagGL x) y ∈ projUnitriangular 3 K ↔ y ∈ projUnitriangular 3 K := by
  refine ⟨fun h => ?_, conjAut_mem_ubar (isUT_diagGL x)⟩
  have hinv : (diagGL x : GL (Fin 3) K)⁻¹ = diagGL x⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [diagGL_mul, mul_inv_cancel, diagGL_one]
  have := conjAut_mem_ubar (isUT_diagGL (K := K) x⁻¹) h
  rwa [← hinv, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this

theorem exists_decomp (A : GL (Fin 3) K) :
    ∃ g : SpecialLinearGroup (Fin 3) K,
      A = diagGL (GeneralLinearGroup.det A) * SpecialLinearGroup.toGL g := by
  set D : GL (Fin 3) K := diagGL (GeneralLinearGroup.det A) with hD
  have hdet : GeneralLinearGroup.det (D⁻¹ * A) = 1 := by
    rw [map_mul, map_inv, hD, det_diagGL, inv_mul_cancel]
  have hdet' : ((D⁻¹ * A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  refine ⟨⟨((D⁻¹ * A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hdet'⟩, ?_⟩
  have : SpecialLinearGroup.toGL (⟨((D⁻¹ * A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hdet'⟩ :
      SpecialLinearGroup (Fin 3) K) = D⁻¹ * A := Units.ext rfl
  rw [this, mul_inv_cancel_left]

section Outer

variable [Finite K] [CharP K 2]

theorem isUT_of_preserves {A : GL (Fin 3) K}
    (h : ∀ y : projectiveSL 3 K, y ∈ projUnitriangular 3 K ↔
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K A y ∈ projUnitriangular 3 K) : IsUT A := by
  obtain ⟨g, hg⟩ := exists_decomp A
  have hN : proj 3 K g ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := h y
    have h2 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K A y = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K (diagGL (GeneralLinearGroup.det A))
        (proj 3 K g * y * (proj 3 K g)⁻¹) := by
      conv_lhs => rw [hg]
      rw [map_mul, MulAut.mul_apply, conjAut_toGL, MulAut.conj_apply]
    rw [h2, conjAut_diagGL_mem_iff] at h1
    exact h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2] at hN
  obtain ⟨B, hB, hBg⟩ := hN
  have hsc : B⁻¹ * g ∈ scalars 3 K := proj_eq_proj_iff.mp hBg
  have hgB : g ∈ upperTriangular 3 K := by
    have : g = B * (B⁻¹ * g) := by group
    rw [this]
    exact (upperTriangular 3 K).mul_mem hB (scalars_le_upperTriangular 3 K hsc)
  have h10 := mem_upperTriangular.mp hgB 1 0 (by decide)
  have h20 := mem_upperTriangular.mp hgB 2 0 (by decide)
  have h21 := mem_upperTriangular.mp hgB 2 1 (by decide)
  rw [hg]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [coe_diagGL, Matrix.diagonal_mul, h10, h20, h21]

theorem exists_conjAut_of_pow_three (hK : Nat.card K = 4) {α : MulAut (projectiveSL 3 K)}
    (h3 : α ^ 3 = 1) : ∃ A : GL (Fin 3) K, α = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K A := by
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => by
    rw [frobeniusEquiv_apply]; rfl
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hK
  obtain ⟨⟨A, a, b⟩, hα⟩ := exists_nf hσ hK α
  have h1 : Ψ α ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  rw [hα, hΨ] at h1
  have h2 := congrArg SemidirectProduct.rightHom h1
  rw [map_pow, map_one] at h2
  have h2' : (Multiplicative.ofAdd a, Multiplicative.ofAdd b) ^ 3 = 1 := h2
  have hab : ∀ a : ZMod 2, Multiplicative.ofAdd a ^ 3 = 1 → a = 0 := by decide
  have ha : a = 0 := hab a (congrArg Prod.fst h2')
  have hb : b = 0 := hab b (congrArg Prod.snd h2')
  exact ⟨A, by rw [hα, ha, hb, nf_zero_zero]⟩

@[expose] def IsCorner (y : projectiveSL 3 K) : Prop := ∃ c : K, y = proj 3 K (corner c)

theorem weights_of_outer (hK : Nat.card K = 4) {α : MulAut (projectiveSL 3 K)} (h3 : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (hU : ∀ y, y ∈ projUnitriangular 3 K ↔ α y ∈ projUnitriangular 3 K)
    (hι : ∀ c : K, α (proj 3 K (corner c)) = proj 3 K (corner c)) :
    ∃ a b : K, a ≠ 1 ∧ b ≠ 1 ∧ ∀ s r c : K, ∃ c' : K,
      α (proj 3 K (uni s r c)) = proj 3 K (uni (a * s) (b * r) c') := by
  obtain ⟨A, rfl⟩ := exists_conjAut_of_pow_three hK h3
  have hA : IsUT A := isUT_of_preserves hU
  obtain ⟨h00, h11, h22⟩ := hA.diag_ne_zero
  have hconj : ∀ s r c : K, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K A (proj 3 K (uni s r c)) =
      proj 3 K (uni (((A : Matrix (Fin 3) (Fin 3) K) 0 0) * ((A : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹ * s)
        ((A : Matrix (Fin 3) (Fin 3) K) 1 1 * ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹ * r)
        (((A : Matrix (Fin 3) (Fin 3) K) 0 0 * c + (A : Matrix (Fin 3) (Fin 3) K) 0 1 * r -
          (A : Matrix (Fin 3) (Fin 3) K) 0 0 * ((A : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹ * s *
            (A : Matrix (Fin 3) (Fin 3) K) 1 2) * ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹)) := by
    intro s r c
    rw [conjAut_proj, conj_uni hA]
  have hpm : (A : Matrix (Fin 3) (Fin 3) K) 0 0 = (A : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    have h1 := hι 1
    rw [corner_eq_uni, hconj] at h1
    have h2 := proj_injOn_unitriangular 3 (uni_mem _ _ _) (uni_mem _ _ _) h1
    obtain ⟨-, -, h3'⟩ := uni_injective h2
    have h4 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 * ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹ = 1 := by
      simpa using h3'
    exact (mul_inv_eq_one₀ h22).mp h4
  have hdet : GeneralLinearGroup.det A ≠ 1 := fun h =>
    hout ((conjAut_mem_range_conj_iff hK A).mpr h)
  have hq : (A : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ (A : Matrix (Fin 3) (Fin 3) K) 0 0 := by
    intro hq
    apply hdet
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_three, hA.1, hA.2.1, hA.2.2, ← hq, ← hpm,
      hq]
    have := LinearFieldFour.pow_three_eq_one hK h00
    simp only [Units.val_one]
    linear_combination this
  refine ⟨(A : Matrix (Fin 3) (Fin 3) K) 0 0 * ((A : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹,
    (A : Matrix (Fin 3) (Fin 3) K) 1 1 * ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹, ?_, ?_,
    fun s r c => ⟨_, hconj s r c⟩⟩
  · intro h
    apply hq
    field_simp at h
    exact h.symm
  · intro h
    apply hq
    rw [← hpm] at h
    field_simp at h
    exact h

end Outer

theorem uni_congr {s r c s' r' c' : K} (hs : s = s') (hr : r = r') (hc : c = c') :
    uni s r c = uni s' r' c' := by
  subst hs hr hc
  rfl

section Weights

variable {a b : K} {α : MulAut (projectiveSL 3 K)}

theorem inj_mod_corner (ha : a ≠ 1) (hb : b ≠ 1)
    (hW : ∀ s r c : K, ∃ c' : K,
      α (proj 3 K (uni s r c)) = proj 3 K (uni (a * s) (b * r) c'))
    {g : projectiveSL 3 K} (hg : g ∈ projUnitriangular 3 K) (h : IsCorner (g * (α g)⁻¹)) :
    IsCorner g := by
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨s, r, c, rfl⟩ : ∃ s r c : K, u = uni s r c := ⟨_, _, _, eq_uni_of_mem hu⟩
  obtain ⟨c', hc'⟩ := hW s r c
  rw [hc'] at h
  obtain ⟨y₀, hy₀⟩ := h
  have h1 : proj 3 K (uni s r c) = proj 3 K (corner y₀) * proj 3 K (uni (a * s) (b * r) c') :=
    mul_inv_eq_iff_eq_mul.mp hy₀
  rw [← map_mul, corner_eq_uni, uni_mul] at h1
  have h2 := proj_injOn_unitriangular 3 (uni_mem _ _ _) (uni_mem _ _ _) h1
  obtain ⟨hs, hr, -⟩ := uni_injective h2
  have hs0 : s = 0 := by
    have : s * (1 - a) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm ha
  have hr0 : r = 0 := by
    have : r * (1 - b) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hb
  exact ⟨c, by rw [corner_eq_uni, hs0, hr0]⟩

theorem surj_mod_corner (ha : a ≠ 1) (hb : b ≠ 1)
    (hW : ∀ s r c : K, ∃ c' : K,
      α (proj 3 K (uni s r c)) = proj 3 K (uni (a * s) (b * r) c'))
    {v : projectiveSL 3 K} (hv : v ∈ projUnitriangular 3 K) :
    ∃ u ∈ projUnitriangular 3 K, ∃ y, IsCorner y ∧ u = v * y * α u := by
  obtain ⟨u₀, hu₀, rfl⟩ := hv
  obtain ⟨s₀, r₀, c₀, rfl⟩ : ∃ s r c : K, u₀ = uni s r c := ⟨_, _, _, eq_uni_of_mem hu₀⟩
  have ha' : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hb' : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  obtain ⟨c', hc'⟩ := hW (s₀ / (1 - a)) (r₀ / (1 - b)) 0
  refine ⟨proj 3 K (uni (s₀ / (1 - a)) (r₀ / (1 - b)) 0),
    Subgroup.mem_map_of_mem _ (uni_mem _ _ _),
    proj 3 K (corner (-(c₀ + c' + s₀ * (b * (r₀ / (1 - b)))))), ⟨_, rfl⟩, ?_⟩
  rw [hc', ← map_mul, ← map_mul, corner_eq_uni, uni_mul, uni_mul]
  congr 1
  refine uni_congr ?_ ?_ ?_
  · field_simp
    ring
  · field_simp
    ring
  · ring

end Weights

theorem exists_comm_corner (c : K) :
    ∃ x ∈ projUnitriangular 3 K, ∃ y ∈ projUnitriangular 3 K,
      x * y * x⁻¹ * y⁻¹ = proj 3 K (corner c) := by
  refine ⟨proj 3 K (uni 1 0 0), Subgroup.mem_map_of_mem _ (uni_mem _ _ _),
    proj 3 K (uni 0 c 0), Subgroup.mem_map_of_mem _ (uni_mem _ _ _), ?_⟩
  have h : uni (1 : K) 0 0 * uni 0 c 0 = corner c * (uni 0 c 0 * uni 1 0 0) := by
    rw [corner_eq_uni, uni_mul, uni_mul, uni_mul]
    exact uni_congr (by ring) (by ring) (by ring)
  have h' : proj 3 K (uni 1 0 0) * proj 3 K (uni 0 c 0) =
      proj 3 K (corner c) * (proj 3 K (uni 0 c 0) * proj 3 K (uni 1 0 0)) := by
    rw [← map_mul, ← map_mul, ← map_mul, h]
  calc proj 3 K (uni 1 0 0) * proj 3 K (uni 0 c 0) * (proj 3 K (uni 1 0 0))⁻¹ *
        (proj 3 K (uni 0 c 0))⁻¹
      = proj 3 K (corner c) * (proj 3 K (uni 0 c 0) * proj 3 K (uni 1 0 0)) *
        (proj 3 K (uni 1 0 0))⁻¹ * (proj 3 K (uni 0 c 0))⁻¹ := by rw [h']
    _ = proj 3 K (corner c) := by group

end CFSG.Quasithin.SBd14
