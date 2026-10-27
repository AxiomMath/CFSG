module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal

public noncomputable section

namespace CFSG.RankThree.PartOne.AUTSL.SpTwo

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K]

def uT (x : K) : Matrix (Fin 2) (Fin 2) K := !![1, x; 0, 1]

def sy (a b c : K) : Matrix (Fin 2) (Fin 2) K := !![a, b; b, c]

theorem uT_zero : uT (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT]

theorem uT_mul (x y : K) : uT x * uT y = uT (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uT_inv (x : K) : (uT x)⁻¹ = uT (-x) := by
  apply Matrix.inv_eq_right_inv
  rw [uT_mul, add_neg_cancel, uT_zero]

theorem isUnit_det_uT (x : K) : IsUnit (uT x).det := by
  simp [uT, Matrix.det_fin_two]

theorem isUnitriangular_two {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnitriangular A) :
    ∃ x, A = uT x := by
  refine ⟨A 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uT, hA.2 0]
  · simp [uT]
  · simp [uT]
    exact hA.1 (show (0 : Fin 2) < 1 by decide)
  · simp [uT, hA.2 1]

omit [Field K] in
theorem symm_two {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    ∃ a b c, C = sy a b c := by
  refine ⟨C 0 0, C 0 1, C 1 1, ?_⟩
  have h10 : C 1 0 = C 0 1 := by
    have := congrFun₂ hC 0 1
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sy, h10]

theorem uT_inv_conj (y a b c : K) :
    (uT y)⁻¹ * sy a b c * (uT y)⁻¹ᵀ = sy (a - 2 * y * b + y ^ 2 * c) (b - y * c) c := by
  rw [uT_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uT, sy, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem blockMat_mul_two (x y a b c a' b' c' : K) :
    blockMat (uT x) (sy a b c) * blockMat (uT y) (sy a' b' c') =
      blockMat (uT (x + y)) (sy (a' + a - 2 * y * b + y ^ 2 * c) (b' + b - y * c) (c' + c)) := by
  rw [blockMat_mul (isUnit_det_uT y), uT_mul, uT_inv_conj]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sy] <;> ring

theorem blockMat_right_cancel {A C C' : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det)
    (h : blockMat A C = blockMat A C') : C = C' := by
  rw [blockMat, blockMat, fromBlocks_inj] at h
  have := invertibleOfIsUnitDet A hA
  exact (Matrix.mul_right_injective_of_invertible A) h.2.1

abbrev mat (g : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem mat_mul (g h : StatedSp 2 K) : mat (g * h) = mat g * mat h := rfl

theorem mat_unipotent {h : StatedSp 2 K} (hh : h ∈ unipotent 2 K) :
    ∃ y a b c, mat h = blockMat (uT y) (sy a b c) := by
  obtain ⟨A, C, hA, hC, hm⟩ := hh
  obtain ⟨y, rfl⟩ := isUnitriangular_two hA
  obtain ⟨a, b, c, rfl⟩ := symm_two hC
  exact ⟨y, a, b, c, hm⟩

theorem exists_unipotent (y a b c : K) :
    ∃ h ∈ unipotent 2 K, mat h = blockMat (uT y) (sy a b c) := by
  refine exists_mem_unipotent (A := uT y) (C := sy a b c) ?_ ?_
  · refine ⟨?_, fun i => ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [uT] at hij ⊢
    · fin_cases i <;> simp [uT]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [sy]

noncomputable def tv (a : K) : StatedSp 2 K := upperUnipotentSp 2 K (C := sy a 0 0) (by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sy])

theorem mat_tv (a : K) : mat (tv a) = blockMat (uT 0) (sy a 0 0) := by
  rw [tv, mat, coe_upperUnipotentSp, blockMat, uT_zero]
  simp

theorem tv_mem_unipotent (a : K) : tv a ∈ unipotent 2 K :=
  ⟨uT 0, sy a 0 0, ⟨by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [uT] at hij ⊢, fun i => by
      fin_cases i <;> simp [uT]⟩, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sy], mat_tv a⟩

theorem tv_mul_comm (a : K) {h : StatedSp 2 K} (hh : h ∈ unipotent 2 K) :
    tv a * h = h * tv a := by
  obtain ⟨y, a', b', c', hm⟩ := mat_unipotent hh
  apply SymplecticTorusWeyl.statedSp_ext
  show mat (tv a * h) = mat (h * tv a)
  rw [mat_mul, mat_mul, mat_tv, hm, blockMat_mul_two, blockMat_mul_two]
  simp only [zero_add, add_zero, mul_zero, zero_mul, sub_zero, zero_pow two_ne_zero, mul_zero]
  rw [add_comm a a']

theorem eq_tv_of_central (h2 : (2 : K) ≠ 0) {g : StatedSp 2 K} (hg : g ∈ unipotent 2 K)
    (hc : ∀ h ∈ unipotent 2 K, g * h = h * g) : ∃ a, g = tv a := by
  obtain ⟨x, a, b, c, hm⟩ := mat_unipotent hg
  have key : ∀ y a' b' c' : K, (∃ h ∈ unipotent 2 K, mat h = blockMat (uT y) (sy a' b' c')) →
      sy (a' + a - 2 * y * b + y ^ 2 * c) (b' + b - y * c) (c' + c) =
        sy (a + a' - 2 * x * b' + x ^ 2 * c') (b + b' - x * c') (c + c') := by
    rintro y a' b' c' ⟨h, hh, hhm⟩
    have := congrArg mat (hc h hh)
    rw [mat_mul, mat_mul, hm, hhm, blockMat_mul_two, blockMat_mul_two, add_comm y x] at this
    exact blockMat_right_cancel (isUnit_det_uT _) this
  have k1 := congrFun₂ (key 0 0 0 1 (exists_unipotent 0 0 0 1)) 0 1
  have hx : x = 0 := by
    have h1 : b = b - x := by simpa [sy] using k1
    linear_combination h1
  subst hx
  have k2 := key 1 0 0 0 (exists_unipotent 1 0 0 0)
  have k2a := congrFun₂ k2 0 1
  have k2b := congrFun₂ k2 0 0
  have hc0 : c = 0 := by simpa [sy] using k2a
  subst hc0
  have hb : b = 0 := by
    simp [sy] at k2b
    exact k2b.resolve_left h2
  subst hb
  exact ⟨a, SymplecticTorusWeyl.statedSp_ext (by
    show mat g = mat (tv a)
    rw [hm, mat_tv])⟩

abbrev eOne : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1

theorem mat_one : mat (1 : StatedSp 2 K) = 1 := rfl

theorem mat_mul_inv (g : StatedSp 2 K) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem tv_mulVec (a : K) (v : Fin 2 ⊕ Fin 2 → K) :
    mat (tv a) *ᵥ v = v + (a * v (Sum.inr 0)) • (eOne : Fin 2 ⊕ Fin 2 → K) := by
  have : mat (tv a) = fromBlocks 1 (sy a 0 0) 0 1 := coe_upperUnipotentSp _
  rw [this, fromBlocks_mulVec]
  funext x
  rcases x with i | i
  · fin_cases i <;> simp [sy, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  · fin_cases i <;> simp

theorem conj_tv_mulVec (g : StatedSp 2 K) (a : K) (v : Fin 2 ⊕ Fin 2 → K) :
    mat (g * tv a * g⁻¹) *ᵥ v =
      v + (a * pairedSympForm K 2 (mat g *ᵥ eOne) v) • (mat g *ᵥ eOne) := by
  have hw : mat g *ᵥ (mat g⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, mat_mul_inv, one_mulVec]
  rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, tv_mulVec, mulVec_add, mulVec_smul, hw]
  congr 2
  have h1 := pairedSympForm_mulVec g eOne (mat g⁻¹ *ᵥ v)
  rw [hw, pairedSympForm_single_inl] at h1
  rw [h1]

theorem matrix_ext_mulVec {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col] using this

theorem conj_tv_of_mulVec_eq (g : StatedSp 2 K) (a c : K) (hg : mat g *ᵥ eOne = c • eOne) :
    g * tv a * g⁻¹ = tv (c * c * a) := by
  apply SymplecticTorusWeyl.statedSp_ext
  show mat (g * tv a * g⁻¹) = mat (tv (c * c * a))
  apply matrix_ext_mulVec
  intro v
  rw [conj_tv_mulVec, tv_mulVec, hg, map_smul, LinearMap.smul_apply, smul_smul,
    pairedSympForm_single_inl]
  congr 2
  ring

theorem mem_flag_one {v : Fin 2 ⊕ Fin 2 → K} : v ∈ flag 2 K 1 ↔ ∃ l : K, v = l • eOne := by
  rw [mem_flag_of_le (by norm_num : 1 ≤ 2), mem_isoFlag]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨v (Sum.inl 0), funext fun x => ?_⟩
    rcases x with i | i
    · fin_cases i
      · simp
      · simp [h2 1 le_rfl]
    · simp [h1 i]
  · rintro ⟨l, rfl⟩
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    fin_cases j
    · simp at hj
    · simp

theorem eOne_mem_flag : (eOne : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 :=
  mem_flag_one.2 ⟨1, by simp⟩

theorem exists_mulVec_eOne {g : StatedSp 2 K} (hg : g ∈ stabilizer 2 K (flag 2 K 1)) :
    ∃ l : K, mat g *ᵥ eOne = l • eOne := by
  have h : (flag 2 K 1).map (mulVecLin (mat g)) = flag 2 K 1 := mem_stabilizer.1 hg
  have : mat g *ᵥ eOne ∈ (flag 2 K 1).map (mulVecLin (mat g)) :=
    ⟨eOne, eOne_mem_flag, by simp⟩
  rw [h] at this
  exact mem_flag_one.1 this

theorem mem_stabilizer_flag_one {g : StatedSp 2 K}
    (h₁ : ∃ l : K, mat g *ᵥ eOne = l • eOne) (h₂ : ∃ l : K, mat g⁻¹ *ᵥ eOne = l • eOne) :
    g ∈ stabilizer 2 K (flag 2 K 1) := by
  obtain ⟨l₁, hl₁⟩ := h₁
  obtain ⟨l₂, hl₂⟩ := h₂
  refine mem_stabilizer_of_mulVec_mem (fun v hv => ?_) (fun v hv => ?_)
  · obtain ⟨l, rfl⟩ := mem_flag_one.1 hv
    exact mem_flag_one.2 ⟨l * l₁, by rw [mulVec_smul, hl₁, smul_smul]⟩
  · obtain ⟨l, rfl⟩ := mem_flag_one.1 hv
    refine mem_flag_one.2 ⟨l * l₂, ?_⟩
    change mat g⁻¹ *ᵥ (l • eOne) = _
    rw [mulVec_smul, hl₂, smul_smul]

variable (K) in
def Z0 : Subgroup (StatedProj (StatedSp 2 K)) :=
  projUnipotent 2 K ⊓ Subgroup.centralizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K)))

theorem mem_Z0_iff (h2 : (2 : K) ≠ 0) (z : StatedProj (StatedSp 2 K)) :
    z ∈ Z0 K ↔ ∃ a : K, z = proj 2 K (tv a) := by
  constructor
  · intro hz
    obtain ⟨hzU, hzc⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hzU
    have hc : ∀ h ∈ unipotent 2 K, g * h = h * g := by
      intro h hh
      have := Subgroup.mem_centralizer_iff.1 hzc (proj 2 K h) ⟨h, hh, rfl⟩
      exact (proj_injOn_unipotent (by norm_num) (mul_mem hg hh) (mul_mem hh hg)
        (by rw [map_mul, map_mul]; exact this.symm))
    obtain ⟨a, rfl⟩ := eq_tv_of_central h2 hg hc
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨tv a, tv_mem_unipotent a, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, tv_mul_comm a hh]

theorem B_single_inl_right (u : Fin 2 ⊕ Fin 2 → K) (k : Fin 2) :
    pairedSympForm K 2 u (Pi.single (Sum.inl k) 1) = -u (Sum.inr k) := by
  rw [pairedSympForm_apply]
  simp [dotProduct, Pi.single_apply]

theorem B_single_inr_right (u : Fin 2 ⊕ Fin 2 → K) (k : Fin 2) :
    pairedSympForm K 2 u (Pi.single (Sum.inr k) 1) = u (Sum.inl k) := by
  rw [pairedSympForm_apply]
  simp [dotProduct, Pi.single_apply]

theorem exists_mulVec_eOne_of_conj (g : StatedSp 2 K) (a' c : K)
    (hv : ∀ v, mat (g * tv 1 * g⁻¹) *ᵥ v = c • (mat (tv a') *ᵥ v)) :
    ∃ l : K, mat g *ᵥ eOne = l • eOne := by
  set u := mat g *ᵥ eOne with hu
  have key : ∀ v : Fin 2 ⊕ Fin 2 → K, v + (1 * pairedSympForm K 2 u v) • u =
      c • (v + (a' * v (Sum.inr 0)) • (eOne : Fin 2 ⊕ Fin 2 → K)) := fun v => by
    rw [← tv_mulVec, ← hv v, conj_tv_mulVec]
  have h1 : ∀ k : Fin 2, u (Sum.inr k) = 0 := by
    intro k
    have h := congrFun (key (Pi.single (Sum.inl k) 1)) (Sum.inr k)
    rw [B_single_inl_right] at h
    simpa using h
  have h2 : u (Sum.inl 1) = 0 := by
    have h := congrFun (key (Pi.single (Sum.inr 1) 1)) (Sum.inl 1)
    rw [B_single_inr_right] at h
    simpa using h
  refine ⟨u (Sum.inl 0), funext fun x => ?_⟩
  rcases x with i | i
  · fin_cases i
    · simp
    · simp [h2]
  · simp [h1 i]

theorem exists_mulVec_eOne_of_proj_mem_normalizer (h2 : (2 : K) ≠ 0) (g : StatedSp 2 K)
    (hg : proj 2 K g ∈ Subgroup.normalizer (Z0 K : Set (StatedProj (StatedSp 2 K)))) :
    ∃ l : K, mat g *ᵥ eOne = l • eOne := by
  have hz : proj 2 K (tv 1) ∈ Z0 K := (mem_Z0_iff h2 _).2 ⟨1, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 hg _).1 hz
  obtain ⟨a', ha'⟩ := (mem_Z0_iff h2 _).1 h1
  have h3 : proj 2 K (g * tv 1 * g⁻¹) = proj 2 K (tv a') := by
    rw [map_mul, map_mul, map_inv]
    exact ha'
  have hs : (tv a')⁻¹ * (g * tv 1 * g⁻¹) ∈ spScalars 2 K := QuotientGroup.eq.1 h3.symm
  obtain ⟨c, hc⟩ : ∃ c : Kˣ,
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c =
        (((tv a')⁻¹ * (g * tv 1 * g⁻¹) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    have := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨c, hc⟩ := (show _ ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2)).range from this)
    exact ⟨c, hc⟩
  have hM : mat (g * tv 1 * g⁻¹) = mat (tv a') * Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) := by
    have h4 : mat ((tv a')⁻¹ * (g * tv 1 * g⁻¹)) = Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) := by
      have := congrArg
        (fun x : GL (Fin 2 ⊕ Fin 2) K => (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
      exact this.symm
    have h5 : mat (tv a') * mat ((tv a')⁻¹ * (g * tv 1 * g⁻¹)) = mat (g * tv 1 * g⁻¹) := by
      rw [← mat_mul, mul_inv_cancel_left]
    rw [← h5, h4]
  refine exists_mulVec_eOne_of_conj g a' (c : K) fun v => ?_
  have hs : (Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K)) *ᵥ v = (c : K) • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [hM, ← mulVec_mulVec, hs, mulVec_smul]

theorem normalizer_Z0 (h2 : (2 : K) ≠ 0) :
    Subgroup.normalizer (Z0 K : Set (StatedProj (StatedSp 2 K))) =
      projStabilizer 2 K (flag 2 K 1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    refine ⟨g, ?_, rfl⟩
    exact mem_stabilizer_flag_one (exists_mulVec_eOne_of_proj_mem_normalizer h2 g hx)
      (exists_mulVec_eOne_of_proj_mem_normalizer h2 g⁻¹ (by
        rw [map_inv]
        exact inv_mem hx))
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨l, hl⟩ := exists_mulVec_eOne hg
    obtain ⟨l', hl'⟩ := exists_mulVec_eOne (inv_mem hg : g⁻¹ ∈ stabilizer 2 K (flag 2 K 1))
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨a, rfl⟩ := (mem_Z0_iff h2 z).1 hz
      refine (mem_Z0_iff h2 _).2 ⟨l * l * a, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, conj_tv_of_mulVec_eq g a l hl]
    · intro hz
      obtain ⟨a, ha⟩ := (mem_Z0_iff h2 _).1 hz
      refine (mem_Z0_iff h2 z).2 ⟨l' * l' * a, ?_⟩
      have h1 : z = proj 2 K g⁻¹ * (proj 2 K g * z * (proj 2 K g)⁻¹) * (proj 2 K g⁻¹)⁻¹ := by
        rw [map_inv]
        group
      rw [h1, ha, ← map_mul, ← map_inv, ← map_mul]
      have := conj_tv_of_mulVec_eq g⁻¹ a l' hl'
      rw [inv_inv] at this ⊢
      rw [this]

section Auto

variable {P : Type*} [Group P]

theorem map_centralizer_inf_le (H : Subgroup P) (β : MulAut P) (hβ : H.map β.toMonoidHom = H) :
    (H ⊓ Subgroup.centralizer (H : Set P)).map β.toMonoidHom ≤
      H ⊓ Subgroup.centralizer (H : Set P) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨hzU, hzc⟩ := Subgroup.mem_inf.1 hz
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 ?_⟩
  · rw [← hβ]
    exact ⟨z, hzU, rfl⟩
  · intro u hu
    rw [← hβ] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    show β u' * β z = β z * β u'
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hzc u' hu']

theorem map_centralizer_inf_eq (H : Subgroup P) (α : MulAut P) (hα : H.map α.toMonoidHom = H) :
    (H ⊓ Subgroup.centralizer (H : Set P)).map α.toMonoidHom =
      H ⊓ Subgroup.centralizer (H : Set P) := by
  have hα' : H.map α.symm.toMonoidHom = H := (Subgroup.map_symm_eq_iff_map_eq H).2 hα
  refine le_antisymm (map_centralizer_inf_le H α hα) fun z hz => ?_
  exact ⟨α.symm z, map_centralizer_inf_le H α.symm hα' ⟨z, hz, rfl⟩, by simp⟩

end Auto

theorem map_pointStab_of_map_unipotent (h2 : (2 : K) ≠ 0)
    (α : MulAut (StatedProj (StatedSp 2 K)))
    (hα : (projUnipotent 2 K).map α.toMonoidHom = projUnipotent 2 K) :
    (projStabilizer 2 K (flag 2 K 1)).map α.toMonoidHom = projStabilizer 2 K (flag 2 K 1) := by
  rw [← normalizer_Z0 h2, Subgroup.map_normalizer_eq_of_bijective _ α.bijective]
  have := map_centralizer_inf_eq (projUnipotent 2 K) α hα
  unfold Z0
  rw [this]

theorem exists_conj_map_unipotent [Finite K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (α : MulAut (StatedProj (StatedSp 2 K))) :
    ∃ x : StatedProj (StatedSp 2 K), (projUnipotent 2 K).map α.toMonoidHom =
      (projUnipotent 2 K).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨S₀, hS₀⟩ := exists_sylow_projUnipotent (K := K) ℓ (r := 2) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 K)) S₀
    (Sylow.mapSurjective (f := α.toMonoidHom) α.surjective S₀)
  refine ⟨x, ?_⟩
  have h1 : ((x • S₀ : Sylow ℓ (StatedProj (StatedSp 2 K))) : Subgroup _) =
      (S₀ : Subgroup _).map α.toMonoidHom := by
    rw [hx]
    rfl
  rw [← hS₀, ← h1, Sylow.coe_subgroup_smul]
  rfl

theorem flag_one_eq_span : flag 2 K 1 = Submodule.span K {(eOne : Fin 2 ⊕ Fin 2 → K)} := by
  ext v
  rw [mem_flag_one, Submodule.mem_span_singleton]
  exact ⟨fun ⟨l, h⟩ => ⟨l, h.symm⟩, fun ⟨l, h⟩ => ⟨l, h.symm⟩⟩

theorem map_projStabilizer_point (h2 : (2 : K) ≠ 0) [Finite K]
    (α : MulAut (StatedProj (StatedSp 2 K))) (L : SpPoint 2 K) :
    ∃ L' : SpPoint 2 K, (projStabilizer 2 K L.line).map α.toMonoidHom =
      projStabilizer 2 K L'.line := by
  classical
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have : Fact ℓ.Prime := ⟨CharP.char_is_prime K ℓ⟩
  let L₀ : SpPoint 2 K := SpPoint.ofVec eOne (single_ne_zero _)
  have hL₀ : L₀.line = flag 2 K 1 := by rw [line_ofVec, flag_one_eq_span]
  obtain ⟨g, hg⟩ := exists_smul_eq_point L₀ L
  have hLg : L.line = L₀.line.map (spAct g) := by rw [← hg]; rfl
  set β : MulAut (StatedProj (StatedSp 2 K)) := α * MulAut.conj (proj 2 K g) with hβ
  have h1 : (projStabilizer 2 K L.line).map α.toMonoidHom =
      (projStabilizer 2 K L₀.line).map β.toMonoidHom := by
    rw [hLg, projStabilizer_map_spAct, Subgroup.map_map]
    rfl
  obtain ⟨x, hx⟩ := exists_conj_map_unipotent ℓ β
  set β' : MulAut (StatedProj (StatedSp 2 K)) := (MulAut.conj x)⁻¹ * β with hβ'def
  have hβ' : (projUnipotent 2 K).map β'.toMonoidHom = projUnipotent 2 K := by
    have e1 : β'.toMonoidHom = ((MulAut.conj x)⁻¹).toMonoidHom.comp β.toMonoidHom := rfl
    rw [e1, ← Subgroup.map_map, hx, Subgroup.map_map]
    have : ((MulAut.conj x)⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      ext y
      simp
    rw [this, Subgroup.map_id]
  have h3 := map_pointStab_of_map_unipotent h2 β' hβ'
  obtain ⟨g', rfl⟩ := proj_surjective x
  refine ⟨g' • L₀, ?_⟩
  have e2 : β.toMonoidHom = (MulAut.conj (proj 2 K g')).toMonoidHom.comp β'.toMonoidHom := by
    refine MonoidHom.ext fun y => ?_
    simp only [hβ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply,
      MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    group
  rw [h1, e2, ← Subgroup.map_map, hL₀, h3, line_smul, hL₀, projStabilizer_map_spAct]

end CFSG.RankThree.PartOne.AUTSL.SpTwo
