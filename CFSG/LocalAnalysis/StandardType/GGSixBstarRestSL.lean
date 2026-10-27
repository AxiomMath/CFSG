module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestNonsplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace RestSL

open SLNS

variable {F : Type} [Field F] {n e s r : ℕ}

section Blocks

variable (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F} (hC : C.det = 1)

omit hC in
theorem nsCore_sub_one (k : Fin s → ℕ) :
    nsCore (r := r) C k - 1 =
      Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i - 1) 0 0 0 := by
  ext (⟨a, i⟩ | u) (⟨b, j⟩ | v)
  · simp only [nsCore, Matrix.sub_apply, fromBlocks_apply₁₁, blockDiagonal_apply, Matrix.one_apply,
      Sum.inl.injEq, Prod.mk.injEq]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  · simp [nsCore]
  · simp [nsCore]
  · simp [nsCore, Matrix.one_apply]

theorem nsSL_sub_one_pow (k : Fin s → ℕ) {j : ℕ} (hj : 1 ≤ j) :
    ((nsSL ε hC k : Matrix (Fin n) (Fin n) F) - 1) ^ j =
      (Matrix.fromBlocks (Matrix.blockDiagonal fun i => (C ^ k i - 1) ^ j) 0 0
        (0 : Matrix (Fin r) (Fin r) F)).submatrix ε ε := by
  have h1 : ((nsSL ε hC k : Matrix (Fin n) (Fin n) F) - 1) =
      (nsCore (r := r) C k - 1).submatrix ε ε := by
    ext x y
    change nsMat ε C k x y - (1 : Matrix (Fin n) (Fin n) F) x y = _
    rw [Matrix.submatrix_apply, Matrix.sub_apply, nsMat, Matrix.submatrix_apply]
    congr 1
    simp only [Matrix.one_apply, ε.injective.eq_iff]
  rw [h1, nsCore_sub_one, submatrix_pow_equiv, fromBlocks_zero_pow _ hj, ← blockDiagonal_pow]
  rfl

theorem compIndicator_eq_pow (k : Fin s → ℕ) (Tb : Finset (Fin s)) (hk0 : ∀ i, i ∉ Tb → k i = 0)
    {o : ℕ} (ho : 1 ≤ o) (hko : ∀ i ∈ Tb, (C ^ k i - 1) ^ o = 1) :
    compIndicator F (fixS ε Tb) = ((nsSL ε hC k : Matrix (Fin n) (Fin n) F) - 1) ^ o := by
  rw [nsSL_sub_one_pow ε hC k ho]
  have hfun : (fun i => (C ^ k i - 1) ^ o) =
      fun i => if i ∈ Tb then (1 : Matrix (Fin e) (Fin e) F) else 0 := by
    funext i
    by_cases hi : i ∈ Tb
    · simp only [hi, ↓reduceIte]
      exact hko i hi
    · simp only [hi, ↓reduceIte, hk0 i hi, pow_zero, sub_self]
      exact zero_pow (by omega)
  rw [hfun]
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

theorem nsSL_sub_one_pow_succ (k : Fin s → ℕ) (Tb : Finset (Fin s))
    (hk0 : ∀ i, i ∉ Tb → k i = 0) {o : ℕ} (hko : ∀ i ∈ Tb, (C ^ k i - 1) ^ o = 1) :
    ((nsSL ε hC k : Matrix (Fin n) (Fin n) F) - 1) ^ (o + 1) =
      (nsSL ε hC k : Matrix (Fin n) (Fin n) F) - 1 := by
  have h1 := nsSL_sub_one_pow ε hC k (j := o + 1) (by omega)
  have h2 := nsSL_sub_one_pow ε hC k (j := 1) le_rfl
  simp only [pow_one] at h2
  rw [h1, h2]
  congr 3
  funext i
  rw [pow_succ]
  by_cases hi : i ∈ Tb
  · rw [hko i hi, one_mul]
  · rw [hk0 i hi, pow_zero, sub_self, mul_zero]

theorem compIndicator_comm_of_comm (k : Fin s → ℕ) (Tb : Finset (Fin s))
    (hk0 : ∀ i, i ∉ Tb → k i = 0) {o : ℕ} (ho : 1 ≤ o) (hko : ∀ i ∈ Tb, (C ^ k i - 1) ^ o = 1)
    {c : SpecialLinearGroup (Fin n) F} (hc : nsSL ε hC k * c = c * nsSL ε hC k) :
    compIndicator F (fixS ε Tb) * (c : Matrix (Fin n) (Fin n) F) =
      (c : Matrix (Fin n) (Fin n) F) * compIndicator F (fixS ε Tb) := by
  rw [compIndicator_eq_pow ε hC k Tb hk0 ho hko]
  have hm := congrArg (fun t : SpecialLinearGroup (Fin n) F => (t : Matrix (Fin n) (Fin n) F)) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  have hcomm : Commute ((nsSL ε hC k : Matrix (Fin n) (Fin n) F) - 1)
      (c : Matrix (Fin n) (Fin n) F) := by
    change (_ - 1) * _ = _ * (_ - 1)
    rw [Matrix.sub_mul, Matrix.mul_sub, hm, Matrix.one_mul, Matrix.mul_one]
  exact (hcomm.pow_left o).eq

theorem coordBlockSL_le_centralizer (k : Fin s → ℕ) (Tb : Finset (Fin s))
    (hk0 : ∀ i, i ∉ Tb → k i = 0) {o : ℕ} (ho : 1 ≤ o) (hko : ∀ i ∈ Tb, (C ^ k i - 1) ^ o = 1) :
    coordBlockSL F (fixS ε Tb) ≤ Subgroup.centralizer {nsSL ε hC k} := by
  intro g hg
  obtain ⟨hg1, hg2⟩ := hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  set P := compIndicator F (fixS ε Tb) with hP
  set Y1 := (nsSL ε hC k : Matrix (Fin n) (Fin n) F) - 1 with hY1
  have hPo : P = Y1 ^ o := compIndicator_eq_pow ε hC k Tb hk0 ho hko
  have hY1P : P * Y1 = Y1 := by
    rw [hPo, ← pow_succ, nsSL_sub_one_pow_succ ε hC k Tb hk0 hko]
  have hY1P' : Y1 * P = Y1 := by
    rw [hPo, ← pow_succ', nsSL_sub_one_pow_succ ε hC k Tb hk0 hko]
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

variable {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {C : Matrix (Fin e) (Fin e) F} {hC : C.det = 1}
  {G : Type} [Group G] {p : ℕ} {B Bs G₀ : Subgroup G} {ψ : SpecialLinearGroup (Fin n) F →* G}
  {A₀ : SpecialLinearGroup (Fin n) F}

theorem NSCtx.pow_card_units (hc : NSCtx ε hC p B Bs G₀ ψ A₀) {j : ℕ} (hj : ¬ p ∣ j) :
    (C ^ j - 1) ^ Nat.card (Matrix (Fin e) (Fin e) F)ˣ = 1 := by
  obtain ⟨U, hU⟩ := hc.cunit j hj 1
  rw [one_smul] at hU
  rw [← hU, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one]

theorem NSCtx.dvd_of_frame_eq_one (hc : NSCtx ε hC p B Bs G₀ ψ A₀) (he : 1 ≤ e)
    {k : Fin s → ℕ} {j₀ : Fin s} (hj₀ : k j₀ = 0)
    (h1 : SLRep.ggFrame ψ A₀ (nsSL ε hC k) = 1) (j : Fin s) : p ∣ k j := by
  obtain ⟨c, -, hcY⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    (SLRep.ker_ggFrame_le hc.ker A₀ (by rw [MonoidHom.mem_ker]; exact h1))
  have hblock : ∀ (j' : Fin s) (a b : Fin e), (C ^ k j') a b = if a = b then c else 0 := by
    intro j' a b
    have h3 := congrFun (congrFun hcY (ε.symm (Sum.inl (a, j')))) (ε.symm (Sum.inl (b, j')))
    change Matrix.scalar (Fin n) c _ _ = nsMat ε C k _ _ at h3
    rw [nsMat_block, Matrix.scalar_apply, diagonal_apply] at h3
    rw [← h3]
    by_cases hab : a = b
    · rw [hab, ite_eq_left rfl, ite_eq_left rfl]
    · have hne : ε.symm (Sum.inl (a, j')) ≠ ε.symm (Sum.inl (b, j')) := fun h =>
        hab (congrArg Prod.fst (Sum.inl_injective (ε.symm.injective h)))
      rw [ite_eq_right hne, ite_eq_right hab]
  have hc1 : c = 1 := by
    have := hblock j₀ ⟨0, he⟩ ⟨0, he⟩
    rw [hj₀, pow_zero, one_apply_eq, ite_eq_left rfl] at this
    exact this.symm
  by_contra hpj
  have hu := hc.cunit (k j) hpj 1
  have hCk : C ^ k j - (1 : F) • (1 : Matrix (Fin e) (Fin e) F) = 0 := by
    ext a b
    rw [Matrix.sub_apply, hblock j a b, hc1, Matrix.smul_apply, one_apply, smul_eq_mul, one_mul,
      Matrix.zero_apply, sub_self]
  rw [hCk] at hu
  have : Nontrivial (Matrix (Fin e) (Fin e) F) := by
    have : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
    infer_instance
  exact not_isUnit_zero hu

variable [Finite F]

theorem NSCtx.isComponentOf_gen (hc : NSCtx ε hC p B Bs G₀ ψ A₀) (k : Fin s → ℕ)
    (Tb : Finset (Fin s)) (hk0 : ∀ i, i ∉ Tb → k i = 0) (hkp : ∀ i ∈ Tb, ¬ p ∣ k i)
    (hS3 : 3 ≤ (fixS ε Tb).card) {i₀ : Fin n} (hi₀ : i₀ ∉ fixS ε Tb) :
    IsComponentOf ((coordBlockSL F (fixS ε Tb)).map (SLRep.ggFrame ψ A₀))
      (G₀ ⊓ Subgroup.centralizer {SLRep.ggFrame ψ A₀ (nsSL ε hC k)}) := by
  classical
  set φ := SLRep.ggFrame ψ A₀ with hφ
  set Y := nsSL ε hC k with hY
  set S := fixS ε Tb with hS
  set o := Nat.card (Matrix (Fin e) (Fin e) F)ˣ with ho_def
  have ho : 1 ≤ o := Nat.card_pos
  have hko : ∀ i ∈ Tb, (C ^ k i - 1) ^ o = 1 := fun i hi =>
    RestSL.NSCtx.pow_card_units hc (hkp i hi)
  have hcent : G₀ ⊓ Subgroup.centralizer {φ Y} = (Subgroup.centralizer {Y}).map φ := by
    rw [← hc.range_frame]
    ext g
    simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨h, rfl⟩, hgc⟩
      exact ⟨h, (commute_nsSL_of_map_commute ε hC hc.ker_frame hc.nsplit hc.cp k
        hgc.symm).symm, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, rfl⟩, by rw [← map_mul, ← map_mul, hh]⟩
  rw [hcent]
  set J₀ := coordBlockSL F S with hJ₀
  have hJ₀C : J₀ ≤ Subgroup.centralizer {Y} :=
    RestSL.coordBlockSL_le_centralizer ε hC k Tb hk0 ho hko
  have hJn : ∀ c ∈ Subgroup.centralizer {Y}, ∀ j ∈ J₀, c * j * c⁻¹ ∈ J₀ := by
    intro c hc' j hj
    refine conj_mem_coordBlockSL ?_ hj
    have hcY : Y * c = c * Y := (Subgroup.mem_centralizer_singleton_iff.mp hc').symm
    exact RestSL.compIndicator_comm_of_comm ε hC k Tb hk0 ho hko hcY
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

end Ctx

end RestSL

end CFSG.StandardType
