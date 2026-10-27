module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestAlpha

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace SLNS

variable {F : Type} [Field F] {n e s r : ℕ}

@[expose] def nsCore (C : Matrix (Fin e) (Fin e) F) (k : Fin s → ℕ) :
    Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) F :=
  Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i) 0 0 1

@[expose] def nsMat (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (C : Matrix (Fin e) (Fin e) F)
    (k : Fin s → ℕ) : Matrix (Fin n) (Fin n) F :=
  (nsCore C k).submatrix ε ε

theorem nsCore_mul (C : Matrix (Fin e) (Fin e) F) (k k' : Fin s → ℕ) :
    nsCore (r := r) C k * nsCore C k' = nsCore C (k + k') := by
  rw [nsCore, nsCore, nsCore, fromBlocks_multiply, ← blockDiagonal_mul]
  simp [pow_add]

theorem nsMat_mul (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (C : Matrix (Fin e) (Fin e) F)
    (k k' : Fin s → ℕ) : nsMat ε C k * nsMat ε C k' = nsMat ε C (k + k') := by
  rw [nsMat, nsMat, nsMat, submatrix_mul_equiv, nsCore_mul]

theorem nsCore_zero (C : Matrix (Fin e) (Fin e) F) : nsCore (r := r) (s := s) C 0 = 1 := by
  rw [nsCore]
  simp only [Pi.zero_apply, pow_zero]
  rw [show (fun _ : Fin s => (1 : Matrix (Fin e) (Fin e) F)) = 1 from rfl, blockDiagonal_one,
    fromBlocks_one]

theorem nsMat_zero (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (C : Matrix (Fin e) (Fin e) F) :
    nsMat ε C 0 = 1 := by
  rw [nsMat, nsCore_zero, submatrix_one_equiv]

theorem det_nsMat (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F}
    (hC : C.det = 1) (k : Fin s → ℕ) : (nsMat ε C k).det = 1 := by
  rw [nsMat, det_submatrix_equiv_self, nsCore, det_fromBlocks_zero₂₁, det_blockDiagonal, det_one,
    mul_one]
  exact Finset.prod_eq_one fun i _ => by rw [det_pow, hC, one_pow]

@[expose] def nsSL (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F}
    (hC : C.det = 1) (k : Fin s → ℕ) : SpecialLinearGroup (Fin n) F :=
  ⟨nsMat ε C k, det_nsMat ε hC k⟩

variable (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1)

theorem nsSL_mul (k k' : Fin s → ℕ) : nsSL ε hC k * nsSL ε hC k' = nsSL ε hC (k + k') :=
  Subtype.ext (nsMat_mul ε C k k')

theorem nsSL_zero : nsSL ε hC 0 = 1 := Subtype.ext (nsMat_zero ε C)

theorem nsSL_comm (k k' : Fin s → ℕ) : nsSL ε hC k * nsSL ε hC k' = nsSL ε hC k' * nsSL ε hC k := by
  rw [nsSL_mul, nsSL_mul, add_comm]

theorem nsSL_pow (k : Fin s → ℕ) (j : ℕ) : nsSL ε hC k ^ j = nsSL ε hC (j • k) := by
  induction j with
  | zero => rw [pow_zero, zero_smul, nsSL_zero]
  | succ j ih => rw [pow_succ, ih, nsSL_mul, succ_nsmul]

theorem nsSL_congr {p : ℕ} (hCp : C ^ p = 1) {k k' : Fin s → ℕ} (h : ∀ i, k i % p = k' i % p) :
    nsSL ε hC k = nsSL ε hC k' := by
  have hpow : ∀ j : ℕ, C ^ j = C ^ (j % p) := fun j => by
    conv_lhs => rw [← Nat.mod_add_div j p, pow_add, pow_mul, hCp, one_pow, mul_one]
  apply Subtype.ext
  change nsMat ε C k = nsMat ε C k'
  rw [nsMat, nsMat, nsCore, nsCore]
  congr 3
  funext i
  rw [hpow (k i), hpow (k' i), h i]

theorem nsSL_pow_p {p : ℕ} (hCp : C ^ p = 1) (k : Fin s → ℕ) : nsSL ε hC k ^ p = 1 := by
  rw [nsSL_pow, ← nsSL_zero ε hC]
  exact nsSL_congr ε hC hCp fun i => by simp [Nat.mul_mod_right]

section Frame

variable {G : Type} [Group G] {p : ℕ}

theorem commute_nsSL_of_map_commute {φ : SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hnsplit : ∀ c : F, c ^ p = 1 → c = 1) (hCp : C ^ p = 1) (k : Fin s → ℕ)
    {g : SpecialLinearGroup (Fin n) F}
    (h : φ (nsSL ε hC k) * φ g = φ g * φ (nsSL ε hC k)) :
    nsSL ε hC k * g = g * nsSL ε hC k := by
  set Y := nsSL ε hC k with hY
  set z := Y * g * Y⁻¹ * g⁻¹ with hz
  have hzk : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hzc := hker hzk
  have hYg : Y * g * Y⁻¹ = z * g := by rw [hz]; group
  have hpow : ∀ j : ℕ, Y ^ j * g * (Y ^ j)⁻¹ = z ^ j * g := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hzj : z ^ j ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := pow_mem hzc j
      calc Y ^ (j + 1) * g * (Y ^ (j + 1))⁻¹ = Y * (Y ^ j * g * (Y ^ j)⁻¹) * Y⁻¹ := by group
        _ = Y * (z ^ j * g) * Y⁻¹ := by rw [ih]
        _ = z ^ j * (Y * g * Y⁻¹) := by
            rw [show Y * (z ^ j * g) * Y⁻¹ = (Y * z ^ j) * g * Y⁻¹ by group,
              Subgroup.mem_center_iff.mp hzj Y]
            group
        _ = z ^ (j + 1) * g := by rw [hYg, pow_succ]; group
  have hzp : z ^ p = 1 := by
    have := hpow p
    rw [nsSL_pow_p ε hC hCp k, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  have hz1 : z = 1 := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · exact Subsingleton.elim _ _
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzc
    have hcp : c ^ p = 1 := by
      have h1 := congrArg (fun t : SpecialLinearGroup (Fin n) F =>
        (t : Matrix (Fin n) (Fin n) F) i i) hzp
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
        one_apply_eq, ← hc] at h1
      rwa [Matrix.scalar_apply, diagonal_pow, diagonal_apply_eq] at h1
    have hc1 := hnsplit c hcp
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl
  calc Y * g = z * g * Y := by rw [← hYg]; group
    _ = g * Y := by rw [hz1, one_mul]

end Frame

section Blocks

@[expose] def kT (Tb : Finset (Fin s)) : Fin s → ℕ := fun i => if i ∈ Tb then 1 else 0

@[expose] def inT (Tb : Finset (Fin s)) : (Fin e × Fin s) ⊕ Fin r → Prop :=
  Sum.elim (fun ai => ai.2 ∈ Tb) (fun _ => False)

instance (Tb : Finset (Fin s)) (u : (Fin e × Fin s) ⊕ Fin r) : Decidable (inT Tb u) := by
  unfold inT
  cases u <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> infer_instance

@[expose] def fixS (Tb : Finset (Fin s)) : Finset (Fin n) :=
  Finset.univ.filter fun x => ¬ inT Tb (ε x)

theorem mem_fixS {Tb : Finset (Fin s)} {x : Fin n} : x ∈ fixS ε Tb ↔ ¬ inT Tb (ε x) := by
  simp [fixS]

theorem fromBlocks_zero_pow {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (X : Matrix α α F) {j : ℕ} (hj : 1 ≤ j) :
    (Matrix.fromBlocks X 0 0 (0 : Matrix β β F)) ^ j = Matrix.fromBlocks (X ^ j) 0 0 0 := by
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih => rw [pow_succ, ih, fromBlocks_multiply, pow_succ]; simp

theorem submatrix_pow_equiv {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix β β F) (σ : α ≃ β) (j : ℕ) : (M.submatrix σ σ) ^ j = (M ^ j).submatrix σ σ := by
  induction j with
  | zero => rw [pow_zero, pow_zero, submatrix_one_equiv]
  | succ j ih => rw [pow_succ, ih, submatrix_mul_equiv, pow_succ]

omit hC in
theorem nsCore_kT_sub_one (Tb : Finset (Fin s)) :
    nsCore (r := r) C (kT Tb) - 1 =
      Matrix.fromBlocks (Matrix.blockDiagonal fun i => if i ∈ Tb then C - 1 else 0) 0 0 0 := by
  ext (⟨a, i⟩ | u) (⟨b, j⟩ | v)
  · simp only [nsCore, Matrix.sub_apply, fromBlocks_apply₁₁, blockDiagonal_apply, Matrix.one_apply,
      Sum.inl.injEq, Prod.mk.injEq]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ Tb
      · simp [kT, hi, Matrix.sub_apply, Matrix.one_apply]
      · simp [kT, hi, Matrix.one_apply]
    · simp [hij]
  · simp [nsCore]
  · simp [nsCore]
  · simp [nsCore, Matrix.one_apply]

theorem nsSL_sub_one_pow (Tb : Finset (Fin s)) {j : ℕ} (hj : 1 ≤ j) :
    ((nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) - 1) ^ j =
      (Matrix.fromBlocks (Matrix.blockDiagonal fun i => if i ∈ Tb then (C - 1) ^ j else 0) 0 0
        (0 : Matrix (Fin r) (Fin r) F)).submatrix ε ε := by
  have h1 : ((nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) - 1) =
      (nsCore (r := r) C (kT Tb) - 1).submatrix ε ε := by
    ext x y
    change nsMat ε C (kT Tb) x y - (1 : Matrix (Fin n) (Fin n) F) x y = _
    rw [Matrix.submatrix_apply, Matrix.sub_apply, nsMat, Matrix.submatrix_apply]
    congr 1
    simp only [Matrix.one_apply, ε.injective.eq_iff]
  rw [h1, nsCore_kT_sub_one, submatrix_pow_equiv, fromBlocks_zero_pow _ hj, ← blockDiagonal_pow]
  congr 3
  funext i
  simp only [Pi.pow_apply]
  split_ifs
  · rfl
  · exact zero_pow (by omega)

theorem exists_pow_sub_one_eq_one [Finite F] (hunit : IsUnit (C - 1)) :
    ∃ o : ℕ, 1 ≤ o ∧ (C - 1) ^ o = 1 := by
  obtain ⟨U, hU⟩ := hunit
  refine ⟨orderOf U, orderOf_pos U, ?_⟩
  rw [← hU, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

theorem compIndicator_eq_pow (Tb : Finset (Fin s)) {o : ℕ} (ho : 1 ≤ o) (hCo : (C - 1) ^ o = 1) :
    compIndicator F (fixS ε Tb) =
      ((nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) - 1) ^ o := by
  rw [nsSL_sub_one_pow ε hC Tb ho]
  simp only [hCo]
  ext x y
  rw [compIndicator_apply, Matrix.submatrix_apply]
  simp only [mem_fixS, not_not]
  rcases hx : ε x with ⟨a, i⟩ | u <;> rcases hy : ε y with ⟨b, j⟩ | v
  · simp only [fromBlocks_apply₁₁, blockDiagonal_apply, inT, Sum.elim_inl]
    have hxy : x = y ↔ (a, i) = (b, j) := by
      constructor
      · rintro rfl
        rw [hx] at hy
        exact Sum.inl_injective hy
      · intro h
        apply ε.injective
        rw [hx, hy, h]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ Tb
      · simp [hi, hxy, Matrix.one_apply]
      · simp [hi]
    · simp [hxy, hij]
  · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]
    rw [ite_eq_right]
    rintro ⟨-, rfl⟩
    rw [hx] at hy
    exact absurd hy (by simp)
  · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]
    rw [ite_eq_right]
    rintro ⟨-, rfl⟩
    rw [hx] at hy
    exact absurd hy (by simp)
  · simp [inT]

theorem nsSL_sub_one_pow_succ (Tb : Finset (Fin s)) {o : ℕ} (hCo : (C - 1) ^ o = 1) :
    ((nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) - 1) ^ (o + 1) =
      (nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) - 1 := by
  have h1 := nsSL_sub_one_pow ε hC Tb (j := o + 1) (by omega)
  have h2 := nsSL_sub_one_pow ε hC Tb (j := 1) le_rfl
  rw [pow_one] at h2
  rw [h1, h2, pow_succ, hCo, one_mul, pow_one]

theorem compIndicator_comm_of_comm (Tb : Finset (Fin s)) {o : ℕ} (ho : 1 ≤ o)
    (hCo : (C - 1) ^ o = 1) {c : SpecialLinearGroup (Fin n) F}
    (hc : nsSL ε hC (kT Tb) * c = c * nsSL ε hC (kT Tb)) :
    compIndicator F (fixS ε Tb) * (c : Matrix (Fin n) (Fin n) F) =
      (c : Matrix (Fin n) (Fin n) F) * compIndicator F (fixS ε Tb) := by
  rw [compIndicator_eq_pow ε hC Tb ho hCo]
  have hm := congrArg (fun t : SpecialLinearGroup (Fin n) F => (t : Matrix (Fin n) (Fin n) F)) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  have hcomm : Commute ((nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) - 1)
      (c : Matrix (Fin n) (Fin n) F) := by
    change (_ - 1) * _ = _ * (_ - 1)
    rw [Matrix.sub_mul, Matrix.mul_sub, hm, Matrix.one_mul, Matrix.mul_one]
  exact (hcomm.pow_left o).eq

theorem coordBlockSL_le_centralizer (Tb : Finset (Fin s)) {o : ℕ} (ho : 1 ≤ o)
    (hCo : (C - 1) ^ o = 1) :
    coordBlockSL F (fixS ε Tb) ≤ Subgroup.centralizer {nsSL ε hC (kT Tb)} := by
  intro g hg
  obtain ⟨hg1, hg2⟩ := hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  set P := compIndicator F (fixS ε Tb) with hP
  set Y1 := (nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) - 1 with hY1
  have hPo : P = Y1 ^ o := compIndicator_eq_pow ε hC Tb ho hCo
  have hY1P : P * Y1 = Y1 := by
    rw [hPo, ← pow_succ, nsSL_sub_one_pow_succ ε hC Tb hCo]
  have hY1P' : Y1 * P = Y1 := by
    rw [hPo, ← pow_succ', nsSL_sub_one_pow_succ ε hC Tb hCo]
  have hgY : (g : Matrix (Fin n) (Fin n) F) * Y1 = Y1 * g := by
    calc (g : Matrix (Fin n) (Fin n) F) * Y1 = g * (P * Y1) := by rw [hY1P]
      _ = (g * P) * Y1 := by rw [Matrix.mul_assoc]
      _ = Y1 := by rw [hg2, hY1P]
      _ = Y1 * (P * g) := by rw [hg1, hY1P']
      _ = Y1 * g := by rw [← Matrix.mul_assoc, hY1P']
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have : (g : Matrix (Fin n) (Fin n) F) * (Y1 + 1) = (Y1 + 1) * g := by
    rw [Matrix.mul_add, Matrix.add_mul, hgY, Matrix.mul_one, Matrix.one_mul]
  rw [hY1, sub_add_cancel] at this
  exact this

end Blocks

section Ctx

variable {G : Type} [Group G] [Finite F] {p : ℕ}

structure NSCtx (p : ℕ) (B Bs G₀ : Subgroup G) (ψ : SpecialLinearGroup (Fin n) F →* G)
    (A₀ : SpecialLinearGroup (Fin n) F) : Prop where
  bstar : GGBstar p B Bs
  ker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F)
  range : ψ.range = G₀
  cent : Subgroup.centralizer (G₀ : Set G) = ⊥
  prime : p.Prime
  nsplit : ∀ c : F, c ^ p = 1 → c = 1
  cp : C ^ p = 1
  cunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)
  frame : ∀ b ∈ Bs, ∃ k : Fin s → ℕ, b = SLRep.ggFrame ψ A₀ (nsSL ε hC k)

variable {ε hC} {B Bs G₀ : Subgroup G} {ψ : SpecialLinearGroup (Fin n) F →* G}
  {A₀ : SpecialLinearGroup (Fin n) F}

omit [Finite F] in
theorem NSCtx.mem_bstar (hc : NSCtx ε hC p B Bs G₀ ψ A₀) (k : Fin s → ℕ) :
    SLRep.ggFrame ψ A₀ (nsSL ε hC k) ∈ Bs := by
  refine hc.bstar.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) ?_
  · obtain ⟨k', rfl⟩ := hc.frame b hb
    rw [← map_mul, ← map_mul, nsSL_comm]
  · rw [← map_pow, nsSL_pow_p ε hC hc.cp, map_one]

omit [Finite F] in
theorem NSCtx.ker_frame (hc : NSCtx ε hC p B Bs G₀ ψ A₀) :
    (SLRep.ggFrame ψ A₀).ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F) :=
  SLRep.ker_ggFrame_le hc.ker A₀

omit [Finite F] in
theorem NSCtx.range_frame (hc : NSCtx ε hC p B Bs G₀ ψ A₀) : (SLRep.ggFrame ψ A₀).range = G₀ :=
  (SLRep.range_ggFrame ψ A₀).trans hc.range

theorem NSCtx.isComponentOf (hc : NSCtx ε hC p B Bs G₀ ψ A₀) (Tb : Finset (Fin s))
    (hS3 : 3 ≤ (fixS ε Tb).card) {i₀ : Fin n} (hi₀ : i₀ ∉ fixS ε Tb) :
    IsComponentOf ((coordBlockSL F (fixS ε Tb)).map (SLRep.ggFrame ψ A₀))
      (G₀ ⊓ Subgroup.centralizer {SLRep.ggFrame ψ A₀ (nsSL ε hC (kT Tb))}) := by
  classical
  set φ := SLRep.ggFrame ψ A₀ with hφ
  set Y := nsSL ε hC (kT Tb) with hY
  set S := fixS ε Tb with hS
  have hp1 : ¬ p ∣ 1 := Nat.Prime.not_dvd_one hc.prime
  have hunit : IsUnit (C - 1) := by
    have := hc.cunit 1 hp1 1
    rwa [pow_one, one_smul] at this
  obtain ⟨o, ho, hCo⟩ := exists_pow_sub_one_eq_one hunit
  have hcent : G₀ ⊓ Subgroup.centralizer {φ Y} = (Subgroup.centralizer {Y}).map φ := by
    rw [← hc.range_frame]
    ext g
    simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨h, rfl⟩, hgc⟩
      exact ⟨h, (commute_nsSL_of_map_commute ε hC hc.ker_frame hc.nsplit hc.cp (kT Tb)
        hgc.symm).symm, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, rfl⟩, by rw [← map_mul, ← map_mul, hh]⟩
  rw [hcent]
  set J₀ := coordBlockSL F S with hJ₀
  have hJ₀C : J₀ ≤ Subgroup.centralizer {Y} := coordBlockSL_le_centralizer ε hC Tb ho hCo
  have hJn : ∀ c ∈ Subgroup.centralizer {Y}, ∀ j ∈ J₀, c * j * c⁻¹ ∈ J₀ := by
    intro c hc' j hj
    refine conj_mem_coordBlockSL ?_ hj
    have hcY : Y * c = c * Y := (Subgroup.mem_centralizer_singleton_iff.mp hc').symm
    exact compIndicator_comm_of_comm ε hC Tb ho hCo hcY
  have hinj : ∀ j ∈ J₀, φ j = 1 → j = 1 := fun j hj h1 => by
    have hj' : j ∈ coordBlockSL F Sᶜᶜ := by rwa [compl_compl]
    exact TypeA.coordBlockSL_compl_inf_scalars (T := Sᶜ) (by simpa using hi₀) hj'
      (SLRep.mem_scalars_of_ker_le_center hc.ker_frame h1)
  have hq : CFSG.IsQuasisimple J₀ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective (blockSLOn_injective (k := F) S)).trans
        (MulEquiv.subgroupCongr (range_blockSLOn S)))
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hS3)
  have hinj' : Function.Injective (φ.comp J₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hrange : (φ.comp J₀.subtype).range = J₀.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hJq : CFSG.IsQuasisimple (J₀.map φ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange)) hq
  have hJF : J₀.map φ ≤ (Subgroup.centralizer {Y}).map φ := Subgroup.map_mono hJ₀C
  have hJn' : ((J₀.map φ).subgroupOf ((Subgroup.centralizer {Y}).map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ f ⟨j, hj, rfl⟩ ⟨c, hc', rfl⟩
    exact ⟨c * j * c⁻¹, hJn c hc' j hj, by rw [map_mul, map_mul, map_inv]⟩
  exact ⟨hJF, IsSubnormal.step hJF hJn' (IsSubnormal.refl _),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJq⟩

omit [Finite F] in
theorem col_of_comm_single {M : Matrix (Fin n) (Fin n) F} {x y : Fin n}
    (h : M * single x y (1 : F) = single x y 1 * M) (a : Fin n) :
    M a x = if a = x then M y y else 0 := by
  have := congrFun (congrFun h a) y
  rw [mul_single_apply_same, mul_one] at this
  by_cases ha : a = x
  · subst ha
    rw [single_mul_apply_same, one_mul] at this
    rw [ite_eq_left rfl]
    exact this
  · rw [single_mul_apply_of_ne _ _ _ _ _ ha] at this
    rw [ite_eq_right ha]
    exact this

omit [Finite F] in
theorem comm_single_of_comm {k : Fin s → ℕ} {x y : Fin n} (hxy : x ≠ y)
    (h : nsSL ε hC k * Matrix.SpecialLinearGroup.transvection hxy (1 : F) =
      Matrix.SpecialLinearGroup.transvection hxy 1 * nsSL ε hC k) :
    nsMat ε C k * single x y (1 : F) = single x y 1 * nsMat ε C k := by
  have hm := congrArg (fun t : SpecialLinearGroup (Fin n) F => (t : Matrix (Fin n) (Fin n) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe] at hm
  change nsMat ε C k * (1 + single x y 1) = (1 + single x y 1) * nsMat ε C k at hm
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hm
  exact add_left_cancel hm

omit [Finite F] in
theorem nsMat_block (k : Fin s → ℕ) (j : Fin s) (a b : Fin e) :
    nsMat ε C k (ε.symm (Sum.inl (a, j))) (ε.symm (Sum.inl (b, j))) = (C ^ k j) a b := by
  rw [nsMat, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, nsCore,
    fromBlocks_apply₁₁, blockDiagonal_apply_eq]

omit [Finite F] in
theorem NSCtx.card_centralizer_le (hc : NSCtx ε hC p B Bs G₀ ψ A₀) (Tb : Finset (Fin s))
    (hS2 : 2 ≤ (fixS ε Tb).card) (he : 1 ≤ e) :
    Nat.card (Bs ⊓ Subgroup.centralizer
      (((coordBlockSL F (fixS ε Tb)).map (SLRep.ggFrame ψ A₀) : Subgroup G) : Set G) :
        Subgroup G) ≤ p ^ Tb.card := by
  classical
  set φ := SLRep.ggFrame ψ A₀ with hφ
  set S := fixS ε Tb with hS
  set X := Bs ⊓ Subgroup.centralizer (((coordBlockSL F S).map φ : Subgroup G) : Set G) with hX
  have hfr : ∀ b : X, ∃ k : Fin s → ℕ, (b : G) = φ (nsSL ε hC k) := fun b => hc.frame b b.2.1
  choose kf hkf using hfr
  have hdiv : ∀ (b : X) (j : Fin s), j ∉ Tb → p ∣ kf b j := by
    intro b j hj
    have hcomm : ∀ x y : Fin n, x ∈ S → y ∈ S → x ≠ y →
        nsMat ε C (kf b) * single x y (1 : F) = single x y 1 * nsMat ε C (kf b) := by
      intro x y hx hy hxy
      have hT : φ (Matrix.SpecialLinearGroup.transvection hxy 1) ∈
          ((coordBlockSL F S).map φ : Subgroup G) :=
        ⟨_, SLRep.transvection_mem_coordBlockSL hx hy hxy 1, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp b.2.2 _ hT
      rw [hkf b, ← map_mul, ← map_mul] at h1
      have h2 := commute_nsSL_of_map_commute ε hC hc.ker_frame hc.nsplit hc.cp (kf b)
        (g := Matrix.SpecialLinearGroup.transvection hxy 1) (by rw [← map_mul, ← map_mul, h1])
      exact comm_single_of_comm hxy h2
    obtain ⟨x₀, hx₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hdiag : ∀ y ∈ S, nsMat ε C (kf b) y y = nsMat ε C (kf b) x₀ x₀ := by
      intro y hy
      by_cases hyx : y = x₀
      · rw [hyx]
      · have := col_of_comm_single (hcomm y x₀ hy hx₀ hyx) y
        rw [ite_eq_left rfl] at this
        exact this
    have hmemS : ∀ a : Fin e, ε.symm (Sum.inl (a, j)) ∈ S := fun a => by
      rw [hS, mem_fixS, Equiv.apply_symm_apply]
      exact hj
    have hscal : C ^ kf b j = (nsMat ε C (kf b) x₀ x₀) • (1 : Matrix (Fin e) (Fin e) F) := by
      ext a a'
      rw [← nsMat_block (ε := ε) (C := C) (kf b) j a a', Matrix.smul_apply, one_apply,
        smul_eq_mul]
      obtain ⟨y, hy, hyne⟩ := Finset.exists_mem_ne (by omega : 1 < S.card)
        (ε.symm (Sum.inl (a', j)))
      have hcol := col_of_comm_single (hcomm _ y (hmemS a') hy hyne.symm) (ε.symm (Sum.inl (a, j)))
      rw [hcol, hdiag y hy]
      by_cases haa : a = a'
      · rw [haa, ite_eq_left rfl, ite_eq_left rfl, mul_one]
      · have hne : ε.symm (Sum.inl (a, j)) ≠ ε.symm (Sum.inl (a', j)) := by
          intro h
          apply haa
          have := congrArg Prod.fst (Sum.inl_injective (ε.symm.injective h))
          exact this
        rw [ite_eq_right hne, ite_eq_right haa, mul_zero]
    by_contra hpj
    have hu := hc.cunit (kf b j) hpj (nsMat ε C (kf b) x₀ x₀)
    rw [hscal, sub_self] at hu
    have : Nontrivial (Matrix (Fin e) (Fin e) F) := by
      have : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
      infer_instance
    exact not_isUnit_zero hu
  have : Fact p.Prime := ⟨hc.prime⟩
  let f : X → (Tb → ZMod p) := fun b i => (kf b i : ZMod p)
  have hf : Function.Injective f := by
    intro b₁ b₂ h12
    apply Subtype.ext
    rw [hkf b₁, hkf b₂]
    congr 1
    refine nsSL_congr ε hC hc.cp fun i => ?_
    by_cases hi : i ∈ Tb
    · have := congrFun h12 ⟨i, hi⟩
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp this
    · rw [Nat.mod_eq_zero_of_dvd (hdiv b₁ i hi), Nat.mod_eq_zero_of_dvd (hdiv b₂ i hi)]
  have hcard := Nat.card_le_card_of_injective f hf
  have hTb : Nat.card ↥Tb = Tb.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rwa [Nat.card_fun, Nat.card_zmod, hTb] at hcard

omit [Finite F] in
theorem comm_of_identity_on_blocks (Tb : Finset (Fin s)) {o : ℕ} (ho : 1 ≤ o)
    (hCo : (C - 1) ^ o = 1) {M : Matrix (Fin n) (Fin n) F}
    (hrow : ∀ x, x ∉ fixS ε Tb → ∀ c, M x c = (1 : Matrix (Fin n) (Fin n) F) x c)
    (hcol : ∀ c, c ∉ fixS ε Tb → ∀ x, M x c = (1 : Matrix (Fin n) (Fin n) F) x c) :
    (nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) * M =
      M * (nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) := by
  set P := compIndicator F (fixS ε Tb) with hP
  set Y1 := (nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) - 1 with hY1
  have hPo : P = Y1 ^ o := compIndicator_eq_pow ε hC Tb ho hCo
  have hPY : P * Y1 = Y1 := by rw [hPo, ← pow_succ, nsSL_sub_one_pow_succ ε hC Tb hCo]
  have hYP : Y1 * P = Y1 := by rw [hPo, ← pow_succ', nsSL_sub_one_pow_succ ε hC Tb hCo]
  have hMP : M * P = P := by
    ext x c
    rw [hP, mul_compIndicator_apply, compIndicator_apply]
    by_cases hc : c ∈ fixS ε Tb
    · rw [ite_eq_left hc, ite_eq_right]
      rintro ⟨hx, rfl⟩
      exact hx hc
    · rw [ite_eq_right hc, hcol c hc x, one_apply]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left ⟨hxc ▸ hc, hxc⟩]
      · rw [ite_eq_right hxc, ite_eq_right fun h => hxc h.2]
  have hPM : P * M = P := by
    ext x c
    rw [hP, compIndicator_mul_apply, compIndicator_apply]
    by_cases hx : x ∈ fixS ε Tb
    · rw [ite_eq_left hx, ite_eq_right]
      rintro ⟨h, -⟩
      exact h hx
    · rw [ite_eq_right hx, hrow x hx c, one_apply]
      by_cases hxc : x = c
      · rw [ite_eq_left hxc, ite_eq_left ⟨hx, hxc⟩]
      · rw [ite_eq_right hxc, ite_eq_right fun h => hxc h.2]
  have hMY : M * Y1 = Y1 := by rw [← hPY, ← Matrix.mul_assoc, hMP]
  have hYM : Y1 * M = Y1 := by rw [← hYP, Matrix.mul_assoc, hPM]
  have hY : (nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) = 1 + Y1 := by rw [hY1]; abel
  rw [hY, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hMY, hYM]

theorem NSCtx.ggRootFusionWitnessAlt [CharP F 2] (hc : NSCtx ε hC p B Bs G₀ ψ A₀)
    {D E M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r₀ : G} (hle : G₀ ≤ M)
    (Tb : Finset (Fin s)) {i₁ : Fin s} (hi₁ : i₁ ∈ Tb) (hTb2 : Tb.card ≤ 2) (he : 1 ≤ e)
    (hS3 : 3 ≤ (fixS ε Tb).card) {l : ℕ} (σ : Equiv.Perm (Fin n))
    (hcomm : (nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F) * (ggInvMatrix n l F).submatrix σ σ =
      (ggInvMatrix n l F).submatrix σ σ * (nsSL ε hC (kT Tb) : Matrix (Fin n) (Fin n) F)) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r₀ (ψ (ggInvSL n l F)) := by
  set φ := SLRep.ggFrame ψ A₀ with hφ
  set Y := nsSL ε hC (kT Tb) with hY
  set x₁ : Fin n := ε.symm (Sum.inl (⟨0, he⟩, i₁)) with hx₁
  have hx₁S : x₁ ∉ fixS ε Tb := by
    rw [mem_fixS, hx₁, Equiv.apply_symm_apply, not_not]
    exact hi₁
  have hbBs := hc.mem_bstar (kT Tb)
  have hb1 : φ Y ≠ 1 := by
    intro h1
    obtain ⟨c, -, hcY⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
      (hc.ker_frame (by rw [MonoidHom.mem_ker]; exact h1))
    have hCc : C = c • (1 : Matrix (Fin e) (Fin e) F) := by
      ext a a'
      have h2 := nsMat_block (ε := ε) (C := C) (kT Tb) i₁ a a'
      have h3 := congrFun (congrFun hcY (ε.symm (Sum.inl (a, i₁)))) (ε.symm (Sum.inl (a', i₁)))
      change Matrix.scalar (Fin n) c _ _ = nsMat ε C (kT Tb) _ _ at h3
      rw [h2, kT, ite_eq_left hi₁, pow_one] at h3
      rw [← h3, Matrix.smul_apply, Matrix.scalar_apply, diagonal_apply, one_apply, smul_eq_mul]
      by_cases haa : a = a'
      · subst haa
        simp
      · have hne : ε.symm (Sum.inl (a, i₁)) ≠ ε.symm (Sum.inl (a', i₁)) := fun h =>
          haa (congrArg Prod.fst (Sum.inl_injective (ε.symm.injective h)))
        rw [ite_eq_right hne, ite_eq_right haa, mul_zero]
    have hu := hc.cunit 1 (Nat.Prime.not_dvd_one hc.prime) c
    rw [pow_one, hCc, sub_self] at hu
    have : Nontrivial (Matrix (Fin e) (Fin e) F) := by
      have : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
      infer_instance
    exact not_isUnit_zero hu
  have hcomp := hc.isComponentOf Tb hS3 hx₁S
  have hbound : Nat.card (Bs ⊓ Subgroup.centralizer
      (((coordBlockSL F (fixS ε Tb)).map φ : Subgroup G) : Set G) : Subgroup G) ≤ p ^ 2 :=
    (hc.card_centralizer_le Tb (by omega) he).trans
      (Nat.pow_le_pow_right hc.prime.pos hTb2)
  have hW : GGSixFusionWitness p Bs D E G₀ t f (φ Y) :=
    ⟨hb1, Or.inr (Or.inr ⟨hbBs, _, hcomp, Or.inl hbound⟩)⟩
  set P : SpecialLinearGroup (Fin n) F := ggPermSL σ with hP
  set u := ggInvSL n l F with hu
  have hwG : ψ (A₀ * P) ∈ G₀ := hc.range ▸ (⟨A₀ * P, rfl⟩ : ψ (A₀ * P) ∈ ψ.range)
  refine SLRep.ggRootFusionWitnessAlt_of_conj_comm ψ (w := A₀ * P) ?_ (hle hwG) hW
  have hconj : ((P * u * P⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (ggInvMatrix n l F).submatrix σ σ := by
    rw [hP, coe_ggPermSL_conj, hu, coe_ggInvSL]
  have hYc : Y * (P * u * P⁻¹) = (P * u * P⁻¹) * Y := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul Y, Matrix.SpecialLinearGroup.coe_mul _ Y, hconj]
    exact hcomm
  have he' : A₀ * P * u * (A₀ * P)⁻¹ = A₀ * (P * u * P⁻¹) * A₀⁻¹ := by group
  rw [he', ← SLRep.ggFrame_apply, ← map_mul, ← map_mul, hYc]

omit [Finite F] in
theorem not_mem_fixS_single_iff {i : Fin s} {x : Fin n} :
    x ∉ fixS ε {i} ↔ ∃ a : Fin e, ε.symm (Sum.inl (a, i)) = x := by
  rw [mem_fixS, not_not]
  constructor
  · intro h
    rcases hx : ε x with ⟨a, j⟩ | u
    · rw [hx] at h
      simp only [inT, Sum.elim_inl, Finset.mem_singleton] at h
      exact ⟨a, by rw [← h, ← hx, Equiv.symm_apply_apply]⟩
    · rw [hx] at h
      exact absurd h (by simp [inT])
  · rintro ⟨a, rfl⟩
    simp [inT]

omit [Finite F] in
theorem card_compl_fixS_single (i : Fin s) : (fixS ε {i})ᶜ.card = e := by
  classical
  have hc : (fixS ε {i})ᶜ = Finset.univ.image fun a : Fin e => ε.symm (Sum.inl (a, i)) := by
    ext x
    rw [Finset.mem_compl, not_mem_fixS_single_iff, Finset.mem_image]
    simp
  rw [hc, Finset.card_image_of_injective _ fun a b h => by
    simpa using congrArg Prod.fst (Sum.inl_injective (ε.symm.injective h)), Finset.card_univ,
    Fintype.card_fin]

omit [Finite F] in
theorem card_fixS_single (i : Fin s) : (fixS ε {i}).card = n - e := by
  have h1 := Finset.card_compl (fixS ε {i})
  rw [card_compl_fixS_single, Fintype.card_fin] at h1
  have h2 := Finset.card_le_univ (fixS ε {i})
  rw [Fintype.card_fin] at h2
  omega

theorem exists_perm_comm_single [CharP F 2] (hcunit : IsUnit (C - 1)) (i : Fin s) {l : ℕ}
    (hl : 2 * l + e ≤ n) :
    ∃ σ : Equiv.Perm (Fin n),
      (nsSL ε hC (kT {i}) : Matrix (Fin n) (Fin n) F) * (ggInvMatrix n l F).submatrix σ σ =
        (ggInvMatrix n l F).submatrix σ σ * (nsSL ε hC (kT {i}) : Matrix (Fin n) (Fin n) F) := by
  classical
  obtain ⟨o, ho, hCo⟩ := exists_pow_sub_one_eq_one hcunit
  set X : Finset (Fin n) := (fixS ε {i})ᶜ with hX
  set T : Finset (Fin n) := Finset.univ.image fun a : Fin e =>
    (⟨l + a, by have := a.2; omega⟩ : Fin n) with hT
  have hXc : X.card = e := card_compl_fixS_single (ε := ε) i
  have hTc : T.card = e := by
    rw [hT, Finset.card_image_of_injective _ fun a b h => by
      have := congrArg Fin.val h
      simp only at this
      exact Fin.ext (by omega), Finset.card_univ, Fintype.card_fin]
  let eqv : {x // x ∈ X} ≃ {x // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hXc, hTc])
  set σ := eqv.extendSubtype with hσ
  have hmid : ∀ x, x ∉ fixS ε {i} → l ≤ (σ x : ℕ) ∧ (σ x : ℕ) < l + e := by
    intro x hx
    have hm := eqv.extendSubtype_mem x (by rw [hX, Finset.mem_compl]; exact hx)
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hm
    rw [← ha]
    have := a.2
    simp only
    omega
  refine ⟨σ, comm_of_identity_on_blocks (ε := ε) (hC := hC) {i} ho hCo (fun x hx c => ?_)
    (fun c hc x => ?_)⟩
  · obtain ⟨h1, h2⟩ := hmid x hx
    rw [Matrix.submatrix_apply, ggInvMatrix, Matrix.add_apply, ggInvNil_apply,
      ite_eq_right (fun h => by omega), add_zero, one_apply, one_apply]
    simp only [σ.injective.eq_iff]
  · obtain ⟨h1, h2⟩ := hmid c hc
    rw [Matrix.submatrix_apply, ggInvMatrix, Matrix.add_apply, ggInvNil_apply,
      ite_eq_right (fun h => by omega), add_zero, one_apply, one_apply]
    simp only [σ.injective.eq_iff]

omit [Finite F] in
theorem card_compl_fixS_pair {i₀ i₁ : Fin s} (h01 : i₀ ≠ i₁) : (fixS ε {i₀, i₁})ᶜ.card = 2 * e := by
  classical
  have hc : (fixS ε {i₀, i₁})ᶜ = (Finset.univ.image fun a : Fin e => ε.symm (Sum.inl (a, i₀))) ∪
      (Finset.univ.image fun a : Fin e => ε.symm (Sum.inl (a, i₁))) := by
    ext x
    rw [Finset.mem_compl, mem_fixS, not_not, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · intro h
      rcases hx : ε x with ⟨a, j⟩ | u
      · rw [hx] at h
        simp only [inT, Sum.elim_inl, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · exact Or.inl ⟨a, Finset.mem_univ _, by rw [← hx, Equiv.symm_apply_apply]⟩
        · exact Or.inr ⟨a, Finset.mem_univ _, by rw [← hx, Equiv.symm_apply_apply]⟩
      · rw [hx] at h
        exact absurd h (by simp [inT])
    · rintro (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩) <;> simp [inT]
  have hinj : ∀ j : Fin s, Function.Injective fun a : Fin e => ε.symm (Sum.inl (a, j)) :=
    fun j a b h => by simpa using congrArg Prod.fst (Sum.inl_injective (ε.symm.injective h))
  rw [hc, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (hinj i₀),
    Finset.card_image_of_injective _ (hinj i₁), Finset.card_univ, Fintype.card_fin, two_mul]
  rw [Finset.disjoint_left]
  rintro x hx0 hx1
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx0
  obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hx1
  have := congrArg Prod.snd (Sum.inl_injective (ε.symm.injective hb))
  exact h01 this.symm

omit [Finite F] in
theorem card_fixS_pair {i₀ i₁ : Fin s} (h01 : i₀ ≠ i₁) : (fixS ε {i₀, i₁}).card = n - 2 * e := by
  have h1 := Finset.card_compl (fixS ε {i₀, i₁})
  rw [card_compl_fixS_pair h01, Fintype.card_fin] at h1
  have h2 := Finset.card_le_univ (fixS ε {i₀, i₁})
  rw [Fintype.card_fin] at h2
  omega

omit [Finite F] in
theorem NSCtx.card_bstar_le (hc : NSCtx ε hC p B Bs G₀ ψ A₀) : Nat.card Bs ≤ p ^ s := by
  classical
  have : Fact p.Prime := ⟨hc.prime⟩
  have hfr : ∀ b : Bs, ∃ k : Fin s → ℕ, (b : G) = SLRep.ggFrame ψ A₀ (nsSL ε hC k) :=
    fun b => hc.frame b b.2
  choose kf hkf using hfr
  let g : Bs → (Fin s → ZMod p) := fun b i => (kf b i : ZMod p)
  have hg : Function.Injective g := by
    intro b₁ b₂ h12
    apply Subtype.ext
    rw [hkf b₁, hkf b₂]
    congr 1
    exact nsSL_congr ε hC hc.cp fun i => (ZMod.natCast_eq_natCast_iff' _ _ _).mp (congrFun h12 i)
  have := Nat.card_le_card_of_injective g hg
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at this

theorem NSCtx.ggRootFusionWitnessAlt_single [CharP F 2] (hc : NSCtx ε hC p B Bs G₀ ψ A₀)
    {D E M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r₀ : G} (hle : G₀ ≤ M)
    (hunit : IsUnit (C - 1)) (i : Fin s) (he : 1 ≤ e) (hS : 3 ≤ (fixS ε {i}).card) {l : ℕ}
    (hl : 2 * l + e ≤ n) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r₀ (ψ (ggInvSL n l F)) := by
  obtain ⟨σ, hσ⟩ := exists_perm_comm_single (ε := ε) (hC := hC) hunit i hl
  exact hc.ggRootFusionWitnessAlt hle {i} (Finset.mem_singleton_self _) (by simp) he hS σ hσ

end Ctx

theorem nsSL_eq_one_of_e_zero (h0 : e = 0) (k : Fin s → ℕ) : nsSL ε hC k = 1 := by
  subst h0
  apply Subtype.ext
  ext x y
  change nsMat ε C k x y = (1 : Matrix (Fin n) (Fin n) F) x y
  rw [nsMat, Matrix.submatrix_apply]
  rcases hx : ε x with ⟨a, i⟩ | u
  · exact a.elim0
  · rcases hy : ε y with ⟨b, j⟩ | v
    · exact b.elim0
    · rw [nsCore, fromBlocks_apply₂₂, one_apply, one_apply]
      congr 1
      apply propext
      constructor
      · rintro rfl
        exact ε.injective (hx.trans hy.symm)
      · rintro rfl
        exact Sum.inr_injective (hx.symm.trans hy)

end SLNS

section Inputs

@[expose] def GGSLNonsplitFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
      GGSixStepOne p B Bs x L D J → ¬ p ∣ 2 ^ f - 1 →
        ∃ (e s r : ℕ) (C : Matrix (Fin e) (Fin e) (GaloisField 2 f)) (hC : C.det = 1)
          (ε : Fin (m + 1) ≃ (Fin e × Fin s) ⊕ Fin r)
          (A₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
          C ^ p = 1 ∧ (∀ j : ℕ, ¬ p ∣ j → ∀ c : GaloisField 2 f, IsUnit (C ^ j - c • 1)) ∧
            ∀ b ∈ Bs, ∃ k : Fin s → ℕ, b = SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC k)

@[expose] def GGNSTwoBlockPermInput : Prop :=
  ∀ (F : Type) [Field F] [CharP F 2] (n e s r : ℕ) (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    (C : Matrix (Fin e) (Fin e) F) (hC : C.det = 1) (i₀ i₁ : Fin s), i₀ ≠ i₁ →
    ∀ l : ℕ, e ≤ l → 2 * l ≤ n →
      ∃ σ : Equiv.Perm (Fin n),
        (SLNS.nsSL ε hC (SLNS.kT {i₀, i₁}) : Matrix (Fin n) (Fin n) F) *
            (ggInvMatrix n l F).submatrix σ σ =
          (ggInvMatrix n l F).submatrix σ σ *
            (SLNS.nsSL ε hC (SLNS.kT {i₀, i₁}) : Matrix (Fin n) (Fin n) F)

theorem ggSixRootFusionSLRepNonsplitInput_of_frame (hF : GGSLNonsplitFrameInput)
    (h2 : GGNSTwoBlockPermInput) : GGSixRootFusionSLRepNonsplitInput := by
  intro G _ _ p B Bs x L D J m f ψ hctx s1 s2 E r hch hC' hodd hns l hl2 hlm
  obtain ⟨e, s, r', C, hC, ε, A₀, hCp, hcunit, hframe⟩ := hF G p B Bs x L D J m f ψ hctx s1 hns
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hnsplit : ∀ c : GaloisField 2 f, c ^ p = 1 → c = 1 := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hc
      exact zero_ne_one hc
    set u := Units.mk0 c hc0 with hu
    have hup : u ^ p = 1 := Units.ext (by simp [hu, hc])
    have h1 : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hup
    have h2' : orderOf u ∣ 2 ^ f - 1 := by
      have := orderOf_dvd_natCard u
      rwa [Nat.card_units, hcardF] at this
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · have := orderOf_eq_one_iff.mp h
      have := congrArg Units.val this
      simpa [hu] using this
    · exact absurd (h ▸ h2') hns
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hc : SLNS.NSCtx ε hC p B Bs (ggG0 p B x L D J) ψ A₀ :=
    ⟨hctx.2.1, hker, hrange, s1.1, hp, hnsplit, hCp, hcunit, hframe⟩
  have hle : ggG0 p B x L D J ≤ ggM p B x L D J := Subgroup.le_normalizer
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hs4 : 4 ≤ s :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hc.card_bstar_le)
  have hn : m + 1 = e * s + r' := by
    have := Fintype.card_congr ε
    simpa [Fintype.card_sum, Fintype.card_prod, mul_comm] using this
  have he1 : 1 ≤ e := by
    by_contra he0
    have he0' : e = 0 := by omega
    have hsub : Bs ≤ ⊥ := fun b hb => by
      obtain ⟨k, rfl⟩ := hframe b hb
      rw [SLNS.nsSL_eq_one_of_e_zero ε hC he0' k, map_one]
      exact Subgroup.one_mem _
    have h1 : Nat.card Bs ≤ 1 := by
      have := Subgroup.card_le_of_le hsub
      rwa [Subgroup.card_bot] at this
    have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) hp.one_lt
    omega
  have he2 : 2 ≤ e := by
    by_contra he
    obtain rfl : e = 1 := by omega
    have hu := hcunit 1 (Nat.Prime.not_dvd_one hp) (C 0 0)
    have h0 : C ^ 1 - C 0 0 • (1 : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) = 0 := by
      ext a b
      rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
      simp
    rw [h0] at hu
    exact not_isUnit_zero hu
  have hes : e * 4 ≤ e * s := Nat.mul_le_mul_left e hs4
  have hunit : IsUnit (C - 1) := by
    have := hcunit 1 (Nat.Prime.not_dvd_one hp) 1
    rwa [pow_one, one_smul] at this
  have hs0 : 0 < s := by omega
  have hs1 : 1 < s := by omega
  rcases le_or_gt (2 * l + e) (m + 1) with hcase | hcase
  · have hS : 3 ≤ (SLNS.fixS ε {(⟨0, hs0⟩ : Fin s)}).card := by
      rw [SLNS.card_fixS_single]
      omega
    have hT1 : ({(⟨0, hs0⟩ : Fin s)} : Finset (Fin s)).card ≤ 2 := by
      rw [Finset.card_singleton]
      omega
    exact hc.ggRootFusionWitnessAlt_single hle hunit ⟨0, hs0⟩ he1 hS hcase
  · have hel : e ≤ l := by omega
    set i₀ : Fin s := ⟨0, hs0⟩ with hi₀
    set i₁ : Fin s := ⟨1, hs1⟩ with hi₁
    have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
    obtain ⟨σ, hσ⟩ := h2 (GaloisField 2 f) (m + 1) e s r' ε C hC i₀ i₁ h01 l hel hlm
    have hS : 3 ≤ (SLNS.fixS ε {i₀, i₁}).card := by
      rw [SLNS.card_fixS_pair h01]
      omega
    have hT2 : ({i₀, i₁} : Finset (Fin s)).card ≤ 2 := Finset.card_le_two
    exact hc.ggRootFusionWitnessAlt (D := D) (E := E) (t := .PSL) (f := f) (r₀ := r) hle
      {i₀, i₁} (Finset.mem_insert_self _ _) hT2 he1 hS σ hσ

theorem ggSixRootFusionSLRepInput_of_nonsplitFrame (hF : GGSLNonsplitFrameInput)
    (h2 : GGNSTwoBlockPermInput) : GGSixRootFusionSLRepInput :=
  ggSixRootFusionSLRepInput_of_nonsplit (ggSixRootFusionSLRepNonsplitInput_of_frame hF h2)

end Inputs

end CFSG.StandardType
