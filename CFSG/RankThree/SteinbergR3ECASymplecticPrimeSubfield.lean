module

public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions

public section

namespace CFSG.RankThree.CASymplecticSubfield

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog SpChain
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)

section Radical

variable {G : Type*} [Group G]

theorem solvableRadical_eq_bot_of_forall
    (h : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) : CFSG.solvableRadical G = ⊥ :=
  sSup_eq_bot.mpr fun N hN => h N hN.1 hN.2

theorem solvableRadical_eq_bot_of_isSimpleGroup [IsSimpleGroup G] [Group.IsPerfect G] :
    CFSG.solvableRadical G = ⊥ := by
  refine solvableRadical_eq_bot_of_forall fun N hN hsol => ?_
  have := hN
  have := hsol
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · subst h
    have : Group.IsSolvable G :=
      Group.isSolvable_of_surjective (f := (⊤ : Subgroup G).subtype)
        fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
    exact absurd this (Group.IsPerfect.not_isSolvable G)

theorem eq_bot_of_normal_of_isSolvable_perm_six {N : Subgroup (Equiv.Perm (Fin 6))}
    (hN : N.Normal) (hsol : Group.IsSolvable N) : N = ⊥ := by
  by_contra hne
  have := hN
  have hnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
  have h5 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_fin]; norm_num
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (N := N) h5 hnt
  have hA : Group.IsSolvable (alternatingGroup (Fin 6)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top h5⟩
  have : Nontrivial (alternatingGroup (Fin 6)) :=
    (alternatingGroup.isSimpleGroup h5).toNontrivial
  exact Group.IsPerfect.not_isSolvable _ hA

theorem solvableRadical_eq_bot_of_mulEquiv_perm_six (e : G ≃* Equiv.Perm (Fin 6)) :
    CFSG.solvableRadical G = ⊥ := by
  refine solvableRadical_eq_bot_of_forall fun N hN hsol => ?_
  have hN' : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
  have := hsol
  have hsol' : Group.IsSolvable (N.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := (N.equivMapOfInjective _ e.injective).toMonoidHom)
      (MulEquiv.surjective _)
  have h := eq_bot_of_normal_of_isSolvable_perm_six hN' hsol'
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ N.map e.toMonoidHom := ⟨x, hx, rfl⟩
  rw [h, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact e.injective (hx'.trans (map_one e).symm)

theorem exists_ne_of_isPerfect [Nontrivial G] [Group.IsPerfect G] :
    ∃ x y : G, x * y ≠ y * x := by
  by_contra h
  push Not at h
  have : IsMulCommutative G := ⟨⟨h⟩⟩
  exact Group.IsPerfect.not_isMulCommutative G this

end Radical

section Inclusion

variable {r : ℕ} {K : Type} [Field K]

theorem spScalars_le_comap (k : Subfield K) :
    spScalars r k ≤ (spScalars r K).comap (subfieldSpHom r k) := by
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.map k.subtype.toMonoidHom c, Units.ext ?_⟩
  change _ = ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).map k.subtype
  rw [← hc, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
    scalar_apply, diagonal_map (map_zero _)]
  rfl

variable (r) in
@[expose] noncomputable def subfieldSpProj (k : Subfield K) :
    StatedProj (StatedSp r k) →* StatedProj (StatedSp r K) :=
  QuotientGroup.map _ _ (subfieldSpHom r k) (spScalars_le_comap k)

theorem subfieldSpProj_proj (k : Subfield K) (g : StatedSp r k) :
    subfieldSpProj r k (proj r k g) = proj r K (subfieldSpHom r k g) :=
  rfl

theorem mem_range_subfieldSpProj {k : Subfield K} {x : StatedProj (StatedSp r K)} :
    x ∈ (subfieldSpProj r k).range ↔ ∃ g : StatedSp r k, proj r K (subfieldSpHom r k g) = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective y
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨proj r k g, rfl⟩

theorem subfieldSpProj_injective (hr : 1 ≤ r) (k : Subfield K) :
    Function.Injective (subfieldSpProj r k) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [MonoidHom.mem_ker, subfieldSpProj_proj, ← MonoidHom.mem_ker, ker_proj,
    Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨c, hc⟩ := hx
  set i₀ : Fin r ⊕ Fin r := Sum.inl ⟨0, hr⟩
  have hck : (c : K) ∈ k := by
    have h1 := congrArg (fun A : GL (Fin r ⊕ Fin r) K =>
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i₀ i₀) hc
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h1
    rw [h1]
    exact (((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) i₀ i₀).2
  have hc0 : (⟨(c : K), hck⟩ : k) ≠ 0 := fun h0 =>
    c.ne_zero (congrArg Subtype.val h0)
  rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_proj, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range]
  refine ⟨Units.mk0 _ hc0, Units.ext (Matrix.ext fun a b => Subtype.ext ?_)⟩
  have h1 : (diagonal (fun _ => (c : K)) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a b =
      ((((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b : k) :
        K) := by
    have := congrArg (fun A : GL (Fin r ⊕ Fin r) K =>
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a b) hc
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply] at this
    exact this
  rw [← h1]
  change ((((GeneralLinearGroup.scalar _ (Units.mk0 _ hc0) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b : k) : K) = _
  by_cases hab : a = b
  · subst hab
    simp
  · simp [diagonal_apply_ne _ hab]

theorem subfieldSpHom_upperUnipotentSp (k : Subfield K) {B : Matrix (Fin r) (Fin r) k}
    (hB : Bᵀ = B) :
    subfieldSpHom r k (SymplecticFlag.upperUnipotentSp r k hB) =
      SymplecticFlag.upperUnipotentSp r K
        (show (B.map k.subtype)ᵀ = B.map k.subtype by rw [← transpose_map, hB]) := by
  refine Subtype.ext (Units.ext ?_)
  change ((SymplecticFlag.upperUnipotentSp r k hB : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).map k.subtype = _
  rw [SymplecticFlag.coe_upperUnipotentSp, SymplecticFlag.coe_upperUnipotentSp, fromBlocks_map,
    Matrix.map_one _ (map_zero k.subtype) (map_one k.subtype),
    Matrix.map_zero _ (map_zero k.subtype)]

theorem primeFieldSp_le_range (k : Subfield K) {g : GL (Fin r ⊕ Fin r) K}
    (hg : g ∈ UnitaryHigher.primeFieldSp r K) :
    ∃ g₀ : StatedSp r k, (subfieldSpHom r k g₀ : GL (Fin r ⊕ Fin r) K) = g := by
  obtain ⟨g₁, hg₁, rfl⟩ := hg
  have hent : ∀ (h : GL (Fin r ⊕ Fin r) (⊥ : Subfield K)) i j,
      ((GeneralLinearGroup.map (⊥ : Subfield K).subtype h : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j ∈ k := fun h i j =>
    bot_le (a := k) (((h : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (⊥ : Subfield K)) i j).2)
  have hmem := UnitaryHigher.primeFieldSp_le (r := r) (K := K)
    ⟨g₁, hg₁, rfl⟩
  obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq_of_mem k (g := ⟨_, hmem⟩) (hent g₁)
    (by
      intro i j
      have : ((⟨_, hmem⟩ : StatedSp r K)⁻¹ : StatedSp r K) =
          ⟨GeneralLinearGroup.map (⊥ : Subfield K).subtype g₁⁻¹, by
            rw [map_inv]; exact inv_mem hmem⟩ := by
        refine Subtype.ext ?_
        rw [Subgroup.coe_inv]
        exact (map_inv _ g₁).symm
      rw [this]
      exact hent g₁⁻¹ i j)
  exact ⟨g₀, congrArg Subtype.val hg₀⟩

end Inclusion

section Fixed

variable {r : ℕ} {K : Type} [Field K]

theorem sq_eq_one_of_smul_mem (hr : 1 ≤ r) {g : StatedSp r K} {c : K}
    (hg : spMat g = c • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) : c ^ 2 = 1 := by
  have h := SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  change (spMat g)ᵀ * fromBlocks 0 1 (-1) 0 * spMat g = fromBlocks 0 1 (-1) 0 at h
  rw [hg] at h
  have h1 := congrFun (congrFun h (Sum.inl ⟨0, hr⟩)) (Sum.inr ⟨0, hr⟩)
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.smul_apply, fromBlocks_apply₁₂, one_apply_eq, smul_eq_mul, mul_one] at h1
  rw [sq]
  exact h1

theorem exists_smul_of_proj_eq (hr : 1 ≤ r) {g g' : StatedSp r K}
    (h : proj r K g = proj r K g') :
    ∃ c : Kˣ, (c : K) ^ 2 = 1 ∧ spMat g' = (c : K) • spMat g := by
  have h1 : g⁻¹ * g' ∈ spScalars r K := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨c, hc⟩ := h1
  have hz : spMat (g⁻¹ * g') = (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    change (((g⁻¹ * g' : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
    rw [← hc, GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]
  refine ⟨c, sq_eq_one_of_smul_mem hr hz, ?_⟩
  have h2 : (g' : GL (Fin r ⊕ Fin r) K) = g * GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  change ((g' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
  rw [h2, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal,
    Matrix.mul_smul, Matrix.mul_one]

theorem apply_eq_self_of_sq_eq_one (τ : K ≃+* K) {c : K} (hc : c ^ 2 = 1) : τ c = c := by
  rcases (mul_self_eq_one_iff (a := c)).mp (by rw [← sq]; exact hc) with h | h
  · rw [h, map_one]
  · rw [h, map_neg, map_one]

theorem pow_apply_eq_mul {σ : K ≃+* K} {c x : K} (hc : σ c = c) (hx : σ x = c * x) (n : ℕ) :
    (σ ^ n) x = c ^ n * x := by
  have hcn : ∀ n : ℕ, (σ ^ n) c = c := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, RingAut.mul_apply, hc, ih]
  induction n with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ n ih => rw [pow_succ, RingAut.mul_apply, hx, map_mul, hcn, ih, pow_succ]; ring

theorem fieldAut_apply_eq_self_iff (hr : 1 ≤ r) {σ : K ≃+* K} (hodd : Odd (orderOf σ))
    (x : StatedProj (StatedSp r K)) :
    fieldAut r K σ x = x ↔ x ∈ (subfieldSpProj r (descentField σ)).range := by
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    rw [fieldAut_proj] at hx
    obtain ⟨c, hc2, hc⟩ := exists_smul_of_proj_eq hr hx
    have hcc : (c : K) * c = 1 := by rw [← sq]; exact hc2
    have hσg : ∀ i j, σ (spMat g i j) = c * spMat g i j := by
      intro i j
      have h1 := congrFun (congrFun hc i) j
      rw [Matrix.smul_apply, smul_eq_mul] at h1
      change spMat g i j = c * σ (spMat g i j) at h1
      calc σ (spMat g i j) = ((c : K) * c) * σ (spMat g i j) := by rw [hcc, one_mul]
        _ = c * (c * σ (spMat g i j)) := by ring
        _ = c * spMat g i j := by rw [← h1]
    have hσc : σ c = c := apply_eq_self_of_sq_eq_one σ hc2
    have hm : ∀ i j, spMat g i j = (c : K) ^ orderOf σ * spMat g i j := fun i j => by
      rw [← pow_apply_eq_mul hσc (hσg i j), pow_orderOf_eq_one]
      rfl
    have hcm : (c : K) ^ orderOf σ = 1 := by
      by_contra hne
      have h0 : spMat g = 0 := by
        ext i j
        have h1 := hm i j
        have h2 : (1 - (c : K) ^ orderOf σ) * spMat g i j = 0 := by rw [sub_mul, one_mul, ← h1,
          sub_self]
        exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
      have hdet := Matrix.GeneralLinearGroup.det_ne_zero (g : GL (Fin r ⊕ Fin r) K)
      have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, hr⟩⟩
      exact hdet (by change (spMat g).det = 0; rw [h0, det_zero])
    have hc1 : (c : K) = 1 := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at hcm
      exact hcm
    have hfix : fieldSp r K σ g = g := by
      refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
      change σ (spMat g i j) = spMat g i j
      rw [hσg, hc1, one_mul]
    obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq hfix
    exact mem_range_subfieldSpProj.mpr ⟨g₀, by rw [hg₀]⟩
  · intro hx
    obtain ⟨g₀, rfl⟩ := mem_range_subfieldSpProj.mp hx
    rw [fieldAut_proj, fieldSp_subfieldSpHom]

end Fixed

section Semilinear

variable {r : ℕ} {K : Type} [Field K]

theorem eq_one_of_smul_unipotent (hr : 1 ≤ r) {d : K} {X : Matrix (Fin r) (Fin r) K}
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hM : M = fromBlocks 1 X 0 1 ∨ M = fromBlocks 1 0 X 1)
    (h : (d • M - 1) * (d • M - 1) = 0) : d = 1 := by
  have h1 := congrFun (congrFun h (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
  rcases hM with hM | hM <;>
  · rw [hM, Matrix.mul_apply, Fintype.sum_sum_type] at h1
    simp [Matrix.one_apply] at h1
    rw [Finset.sum_eq_single (⟨0, hr⟩ : Fin r)] at h1
    · simp only [ite_true] at h1
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h1)
    · intro x _ hx
      simp [Ne.symm hx, hx]
    · intro h0
      exact absurd (Finset.mem_univ _) h0

theorem commute_of_conjAut_proj_eq (hr : 1 ≤ r) (A : gsp r K) {g : StatedSp r K}
    {X : Matrix (Fin r) (Fin r) K}
    (hg : spMat g = fromBlocks 1 X 0 1 ∨ spMat g = fromBlocks 1 0 X 1)
    (h : conjAut r K A (proj r K g) = proj r K g) :
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * spMat g =
      spMat g * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  rw [conjAut_proj] at h
  obtain ⟨c, -, hc⟩ := exists_smul_of_proj_eq hr h.symm
  set Am := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  set Ai := (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  have hAA : Am * Ai = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAA' : Ai * Am = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hconj : spMat (conjSp r K A g) = Am * spMat g * Ai := by
    change (((conjSp r K A g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
    rw [coe_conjSp, Units.val_mul, Units.val_mul]
  have hnil : (spMat g - 1) * (spMat g - 1) = 0 := by
    rcases hg with hg | hg
    · have e : spMat g - 1 = fromBlocks 0 X 0 0 := by
        rw [hg]
        ext a b
        rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply]
      rw [e, fromBlocks_multiply]
      simp
    · have e : spMat g - 1 = fromBlocks 0 0 X 0 := by
        rw [hg]
        ext a b
        rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply]
      rw [e, fromBlocks_multiply]
      simp
  have hsq : ((c : K) • spMat g - 1) * ((c : K) • spMat g - 1) = 0 := by
    have h1 : Am * spMat g * Ai - 1 = Am * (spMat g - 1) * Ai := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAA]
    rw [← hc, hconj, h1]
    calc Am * (spMat g - 1) * Ai * (Am * (spMat g - 1) * Ai) =
        Am * ((spMat g - 1) * (Ai * Am) * (spMat g - 1)) * Ai := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hAA', Matrix.mul_one, hnil, Matrix.mul_zero, Matrix.zero_mul]
  have hc1 : (c : K) = 1 := eq_one_of_smul_unipotent hr hg hsq
  rw [hc1, one_smul, hconj] at hc
  calc Am * spMat g = Am * spMat g * Ai * Am := by
        rw [Matrix.mul_assoc _ Ai, hAA', Matrix.mul_one]
    _ = spMat g * Am := by rw [hc]

end Semilinear

section Pointwise

variable {r : ℕ} {K : Type} [Field K]

theorem eq_scalar_of_fixes_primeFieldSp (hr : 1 ≤ r) (A : gsp r K)
    (h : ∀ g : StatedSp r K, (g : GL (Fin r ⊕ Fin r) K) ∈ UnitaryHigher.primeFieldSp r K →
      conjAut r K A (proj r K g) = proj r K g) :
    ∃ d : K, ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Matrix.scalar (Fin r ⊕ Fin r) d := by
  set Am := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  have hU : ∀ B : Matrix (Fin r) (Fin r) (⊥ : Subfield K), Bᵀ = B →
      Am * fromBlocks 1 (B.map (⊥ : Subfield K).subtype) 0 1 =
        fromBlocks 1 (B.map (⊥ : Subfield K).subtype) 0 1 * Am := by
    intro B hB
    obtain ⟨g, hg, hgB⟩ := UnitaryHigher.exists_upper_mem_primeFieldSp hB
    have := commute_of_conjAut_proj_eq hr A (g := ⟨g, UnitaryHigher.primeFieldSp_le hg⟩)
      (Or.inl hgB) (h _ hg)
    rw [← hgB]
    exact this
  have hL : ∀ C : Matrix (Fin r) (Fin r) (⊥ : Subfield K), Cᵀ = C →
      Am * fromBlocks 1 0 (C.map (⊥ : Subfield K).subtype) 1 =
        fromBlocks 1 0 (C.map (⊥ : Subfield K).subtype) 1 * Am := by
    intro C hC
    obtain ⟨g, hg, hgC⟩ := UnitaryHigher.exists_lower_mem_primeFieldSp hC
    have := commute_of_conjAut_proj_eq hr A (g := ⟨g, UnitaryHigher.primeFieldSp_le hg⟩)
      (Or.inr hgC) (h _ hg)
    rw [← hgC]
    exact this
  have h1 : (1 : Matrix (Fin r) (Fin r) (⊥ : Subfield K)).map (⊥ : Subfield K).subtype = 1 :=
    Matrix.map_one _ (map_zero (⊥ : Subfield K).subtype) (map_one (⊥ : Subfield K).subtype)
  have hs : ∀ i j : Fin r,
      (single i j (1 : (⊥ : Subfield K))).map (⊥ : Subfield K).subtype = single i j 1 :=
    fun i j => by rw [Matrix.map_single, map_one]
  have hsym : ∀ i : Fin r, (single i i (1 : (⊥ : Subfield K)))ᵀ = single i i 1 := fun i => by
    rw [transpose_single]
  exact UnitaryHigher.eq_scalar_of_commute_basic_unipotents Am
    (by simpa only [h1] using hU 1 transpose_one)
    (fun i => by simpa only [hs] using hU _ (hsym i))
    (fun i => by simpa only [hs] using hL _ (hsym i))
    (fun i j => by
      have hB : (single i j (1 : (⊥ : Subfield K)) + single j i 1)ᵀ =
          single i j 1 + single j i 1 := by
        rw [transpose_add, transpose_single, transpose_single, add_comm]
      simpa only [Matrix.map_add _ (map_add (⊥ : Subfield K).subtype), hs] using hU _ hB)

theorem conjAut_eq_one_of_scalar {A : gsp r K} {d : K}
    (hA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Matrix.scalar (Fin r ⊕ Fin r) d) : conjAut r K A = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  refine Subtype.ext (Units.ext ?_)
  rw [coe_conjSp, Units.val_mul, Units.val_mul]
  have hcomm : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [hA]
    exact (scalar_commute d (fun r' => Commute.all d r') _).eq
  rw [hcomm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem fieldAut_apply_of_fixes {k : Subfield K} {τ : K ≃+* K} (hτ : ∀ t ∈ k, τ t = t)
    {x : StatedProj (StatedSp r K)} (hx : x ∈ (subfieldSpProj r k).range) :
    fieldAut r K τ x = x := by
  obtain ⟨g₀, rfl⟩ := mem_range_subfieldSpProj.mp hx
  rw [fieldAut_proj]
  congr 1
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change τ ((spMat g₀ i j : k) : K) = ((spMat g₀ i j : k) : K)
  exact hτ _ (spMat g₀ i j).2

theorem fixes_of_fieldAut_apply (hr : 1 ≤ r) {k : Subfield K} {τ : K ≃+* K}
    (h : ∀ x ∈ (subfieldSpProj r k).range, fieldAut r K τ x = x) : ∀ t ∈ k, τ t = t := by
  intro t ht
  set i₀ : Fin r := ⟨0, hr⟩
  have hB : (single i₀ i₀ (⟨t, ht⟩ : k))ᵀ = single i₀ i₀ ⟨t, ht⟩ := transpose_single _ _ _
  set s := SymplecticFlag.upperUnipotentSp r k hB
  have hx := h (proj r K (subfieldSpHom r k s)) (mem_range_subfieldSpProj.mpr ⟨s, rfl⟩)
  rw [fieldAut_proj] at hx
  obtain ⟨c, -, hc⟩ := exists_smul_of_proj_eq hr hx
  have hm : ∀ a b, spMat (subfieldSpHom r k s) a b =
      ((fromBlocks 1 (single i₀ i₀ (⟨t, ht⟩ : k)) 0 1 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b : K) := by
    intro a b
    rw [spMat_subfieldSpHom]
    change ((((s : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) a b : K) = _
    rw [SymplecticFlag.coe_upperUnipotentSp]
  have hf : ∀ a b, spMat (fieldSp r K τ (subfieldSpHom r k s)) a b =
      τ (spMat (subfieldSpHom r k s) a b) := fun a b => rfl
  have h1 := congrFun (congrFun hc (Sum.inl i₀)) (Sum.inl i₀)
  have h2 := congrFun (congrFun hc (Sum.inl i₀)) (Sum.inr i₀)
  rw [Matrix.smul_apply, smul_eq_mul, hm, hf, hm] at h1 h2
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, one_apply_eq, single_apply_same,
    OneMemClass.coe_one, map_one, mul_one] at h1 h2
  rw [← h1, one_mul] at h2
  exact h2.symm

theorem eq_fieldAut_of_fixes (hr : 1 ≤ r) {k : Subfield K} (A : gsp r K) (τ : K ≃+* K)
    (h : ∀ x ∈ (subfieldSpProj r k).range, (conjAut r K A * fieldAut r K τ) x = x) :
    conjAut r K A * fieldAut r K τ = fieldAut r K τ ∧ ∀ t ∈ k, τ t = t := by
  have hprime : ∀ g : StatedSp r K, (g : GL (Fin r ⊕ Fin r) K) ∈ UnitaryHigher.primeFieldSp r K →
      conjAut r K A (proj r K g) = proj r K g := by
    intro g hg
    obtain ⟨g₀, hg₀⟩ := primeFieldSp_le_range k hg
    have hmem : proj r K g ∈ (subfieldSpProj r k).range :=
      mem_range_subfieldSpProj.mpr ⟨g₀, by rw [show subfieldSpHom r k g₀ = g from Subtype.ext hg₀]⟩
    have h1 := h _ hmem
    rw [MulAut.mul_apply, fieldAut_proj] at h1
    have hfix : fieldSp r K τ g = g := Subtype.ext (UnitaryHigher.glFieldEquiv_primeFieldSp τ hg)
    rwa [hfix] at h1
  obtain ⟨d, hd⟩ := eq_scalar_of_fixes_primeFieldSp hr A hprime
  have hA := conjAut_eq_one_of_scalar hd
  rw [hA, one_mul] at h ⊢
  exact ⟨rfl, fixes_of_fieldAut_apply hr h⟩

end Pointwise

section Exceptional

variable {K : Type} [Field K]

theorem mem_spSemilinearAutGroup_of_fixes [CharP K 2] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (β : MulAut (StatedProj (StatedSp 2 K)))
    (hβ : ∀ g : StatedSp 2 K, (g : GL (Fin 2 ⊕ Fin 2) K) ∈ UnitaryHigher.primeFieldSp 2 K →
      β (proj 2 K g) = proj 2 K g) :
    β ∈ spSemilinearAutGroup 2 K := by
  obtain ⟨Fr, hFr, -, -, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  obtain ⟨-, -, -, -, -, hγ⟩ := even_symplectic_two_exterior_square_automorphism hf hK
  obtain ⟨-, -, -, huniq, -⟩ := hγ (exceptionalAut K) exceptionalAut_proj
  obtain ⟨⟨g, j⟩, hgj, -⟩ := huniq β
  simp only at hgj
  have hsq := exceptionalAut_sq (K := K) hFr
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (j : ℕ)
  · rw [hgj, hm, pow_mul, hsq, ← map_pow]
    exact mul_mem (spInner_mem_spSemilinearAutGroup g) (fieldAut_mem_spSemilinearAutGroup _)
  · exfalso
    set t₀ := upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))
    set t₁ := upperUnipotentSp 2 K (transpose_single_swap (K := K))
    have ht₀ : (t₀ : GL (Fin 2 ⊕ Fin 2) K) ∈ UnitaryHigher.primeFieldSp 2 K := by
      have hB : (single (0 : Fin 2) (0 : Fin 2) (1 : (⊥ : Subfield K)))ᵀ = single 0 0 1 :=
        transpose_single _ _ _
      obtain ⟨g', hg', hg'B⟩ := UnitaryHigher.exists_upper_mem_primeFieldSp hB
      have heq : (t₀ : GL (Fin 2 ⊕ Fin 2) K) = g' := by
        refine Units.ext ?_
        rw [hg'B, coe_upperUnipotentSp, Matrix.map_single, map_one]
      rw [heq]
      exact hg'
    have hfix₁ : fieldSp 2 K (Fr ^ m) t₁ = t₁ := by
      refine Subtype.ext (Units.ext ?_)
      rw [coe_fieldSp, coe_upperUnipotentSp, fromBlocks_map,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
        Matrix.map_add _ (map_add _), Matrix.map_single, Matrix.map_single, map_one]
    have hβt : β (proj 2 K t₀) = proj 2 K (g * t₁ * g⁻¹) := by
      rw [hgj, hm, pow_succ, pow_mul, hsq, ← map_pow, MulAut.mul_apply, MulAut.mul_apply,
        exceptionalAut_proj, exceptionalSpAut_upperUnipotent, fieldAut_proj, hfix₁,
        spInner_eq_conj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    rw [hβ t₀ ht₀] at hβt
    have h1 : t₀ = g * t₁ * g⁻¹ := UnitaryHigher.proj_bijective_of_charTwo.1 hβt
    have h2 : g⁻¹ * fieldSp 2 K 1 t₀ * g⁻¹⁻¹ = t₁ := by
      rw [map_one, MulAut.one_apply, inv_inv, h1]
      group
    have h3 := displacementInLine_conj g⁻¹ t₀ 1 displacementInLine_upperUnipotent
    rw [h2] at h3
    exact not_displacementInLine_upperUnipotent_swap h3

end Exceptional

section SymSix

open CFSG.ComponentClassification.StandardRecognition (symplecticToSympFour
  symplecticToSympFour_bijective)
open CFSG.ComponentClassification.PresentationLocal (omegaPerm omegaPerm_injective
  omegaPerm_surjective)

theorem nonempty_statedSp_two_mulEquiv_perm {k : Type} [Field k] [Fintype k]
    (hk : Fintype.card k = 2) : Nonempty (StatedSp 2 k ≃* Equiv.Perm (Fin 6)) := by
  let e : k ≃+* ZMod 2 := (ZMod.ringEquivOfPrime k Nat.prime_two hk).symm
  let φ : TauCeti.GLSymplectic (Fin 2) k ≃* TauCeti.GLSymplectic (Fin 2) (ZMod 2) :=
    MonoidHom.toMulEquiv (TauCeti.GLSymplectic.map (Fin 2) e.toRingHom)
      (TauCeti.GLSymplectic.map (Fin 2) e.symm.toRingHom)
      (by rw [← TauCeti.GLSymplectic.map_comp, RingEquiv.symm_toRingHom_comp_toRingHom,
        TauCeti.GLSymplectic.map_id])
      (by rw [← TauCeti.GLSymplectic.map_comp, RingEquiv.toRingHom_comp_symm_toRingHom,
        TauCeti.GLSymplectic.map_id])
  exact ⟨(MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic).trans
    (φ.trans ((TauCeti.GLSymplectic.mulEquivSymplecticGroup (Fin 2) (ZMod 2)).trans
      ((MulEquiv.ofBijective symplecticToSympFour symplecticToSympFour_bijective).trans
        (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩))))⟩

end SymSix

section Transport

variable {G : Type*} [Group G]

theorem nonempty_commutator_mulEquiv_alternating {H : Subgroup G}
    (e : H ≃* Equiv.Perm (Fin 6)) :
    Nonempty (↥(⁅H, H⁆ : Subgroup G) ≃* alternatingGroup (Fin 6)) := by
  have h2 : (commutator H).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
      ← commutator_def, alternatingGroup.commutator_perm_eq (by rw [Nat.card_fin]; norm_num)]
  exact ⟨((MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator H)).symm.trans
    (Subgroup.equivMapOfInjective _ _ H.subtype_injective).symm).trans
      ((Subgroup.equivMapOfInjective _ _ e.injective).trans (MulEquiv.subgroupCongr h2))⟩

theorem mul_conj_eq (α : MulAut G) (x : G) :
    α * MulAut.conj x = MulAut.conj (α x) * α := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_injective_of_center_eq_bot (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← h, Subgroup.mem_center_iff]
  intro y
  have h1 := congrArg (fun α : MulAut G => α y) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

theorem exists_finset_card_four {α : Type*} [Finite α] (h : 4 ≤ Nat.card α) :
    ∃ s : Finset α, s.card = 4 := by
  have := Fintype.ofFinite α
  have h' : 4 ≤ (Finset.univ : Finset α).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h'
  exact ⟨s, hs⟩

end Transport

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def subfieldFixedGroup (r : ℕ) (σ : K ≃+* K) :
    Subgroup (StatedProj (StatedSp r K)) :=
  (subfieldSpProj r (descentField σ)).range

theorem symplectic_prime_subfield_fixed_group_and_full_centralizer {ℓ p f r : ℕ}
    (hℓ : ℓ.Prime) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (descentField σ) = ℓ ^ (f / p) ∧
    IsSimpleGroup (StatedProj (StatedSp r K)) ∧
    (∃ x y : StatedProj (StatedSp r K), x * y ≠ y * x) ∧
    Function.Injective (subfieldSpProj r (descentField σ)) ∧
    (∀ x : StatedProj (StatedSp r K), x ∈ subfieldFixedGroup K r σ ↔ fieldAut r K σ x = x) ∧
    CFSG.solvableRadical (subfieldFixedGroup K r σ) = ⊥ ∧
    (¬(r = 2 ∧ ℓ ^ (f / p) = 2) →
      IsSimpleGroup (subfieldFixedGroup K r σ) ∧
        ∃ x y : subfieldFixedGroup K r σ, x * y ≠ y * x) ∧
    (r = 2 ∧ ℓ ^ (f / p) = 2 →
      Nonempty (subfieldFixedGroup K r σ ≃* Equiv.Perm (Fin 6)) ∧
        Nonempty (↥(⁅subfieldFixedGroup K r σ, subfieldFixedGroup K r σ⁆ :
          Subgroup (StatedProj (StatedSp r K))) ≃* alternatingGroup (Fin 6)) ∧
        Nat.card (subfieldFixedGroup K r σ) = 720) ∧
    fixingSubgroup (MulAut (StatedProj (StatedSp r K)))
        (subfieldFixedGroup K r σ : Set (StatedProj (StatedSp r K))) =
      (fixingSubgroup (K ≃+* K) (descentField σ : Set K)).map (fieldAut r K) ∧
    (fixingSubgroup (K ≃+* K) (descentField σ : Set K)).map (fieldAut r K) =
      Subgroup.zpowers (fieldAut r K σ) ∧
    Nat.card (Subgroup.zpowers (fieldAut r K σ)) = p ∧
    Subgroup.centralizer (((subfieldFixedGroup K r σ).map MulAut.conj :
        Subgroup (MulAut (StatedProj (StatedSp r K)))) :
          Set (MulAut (StatedProj (StatedSp r K)))) =
      Subgroup.zpowers (fieldAut r K σ) ∧
    (r = 2 ∧ ℓ ^ (f / p) = 2 → (∃ x ∈ subfieldFixedGroup K r σ, orderOf x = p) →
      ℓ = 2 ∧ p = 5 ∧ f = 5 ∧ ℓ ^ f = 32) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hr1 : 1 ≤ r := by omega
  have : NeZero r := ⟨by omega⟩
  set k := descentField σ with hkdef
  set H₀ := subfieldFixedGroup K r σ with hH₀
  obtain ⟨hpf, hkcard⟩ := CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ hf hK hσ
  have hk : Nat.card k = ℓ ^ (f / p) := hkcard
  have hpf' : p ≤ f := Nat.le_of_dvd (by omega) hpf
  have hfp : 1 ≤ f / p := (Nat.one_le_div_iff hp.pos).mpr hpf'
  have hq0 : 2 ≤ ℓ ^ (f / p) := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ℓ ^ f := Nat.pow_le_pow_left hℓ.two_le f
  have hTs : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r hr1
      (Or.inl (Or.inr hK4))
  have hTp : Group.IsPerfect (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r K
      (Or.inl (exists_finset_card_four hK4))
  have hTnc : ∃ x y : StatedProj (StatedSp r K), x * y ≠ y * x := exists_ne_of_isPerfect
  have hcenter : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp r K)))
      with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hTnc
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have hconj := conj_injective_of_center_eq_bot hcenter
  have hinj := subfieldSpProj_injective hr1 k
  have hodd : Odd (orderOf σ) := hσ ▸ hp.odd_of_ne_two (by omega)
  have hfixpts : ∀ x, x ∈ H₀ ↔ fieldAut r K σ x = x := fun x =>
    (fieldAut_apply_eq_self_iff hr1 hodd x).symm
  let eH : StatedProj (StatedSp r k) ≃* H₀ := MonoidHom.ofInjective hinj
  have : Finite k := Subtype.finite
  have : Fintype k := Fintype.ofFinite k
  have hsimple : ¬(r = 2 ∧ ℓ ^ (f / p) = 2) → IsSimpleGroup H₀ ∧ Group.IsPerfect H₀ := by
    intro hne
    have hcases : 4 ≤ Nat.card k ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨ (Nat.card k = 2 ∧ 3 ≤ r) := by
      rw [hk]
      by_cases h4 : 4 ≤ ℓ ^ (f / p)
      · exact Or.inl h4
      · by_cases h3 : ℓ ^ (f / p) = 3
        · exact Or.inr (Or.inl ⟨h3, hr⟩)
        · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
          by_contra hr3
          exact hne ⟨by omega, by omega⟩
    have hs : IsSimpleGroup (StatedProj (StatedSp r k)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r hr1
        (by rcases hcases with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h)
    have hperf : Group.IsPerfect (StatedProj (StatedSp r k)) :=
      CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r k
        (by rcases hcases with h | h
            · exact Or.inl (exists_finset_card_four h)
            · exact Or.inr h)
    exact ⟨eH.symm.isSimpleGroup, Group.IsPerfect.ofSurjective (f := eH.toMonoidHom)
      eH.surjective⟩
  have hexc : r = 2 ∧ ℓ ^ (f / p) = 2 → Nonempty (H₀ ≃* Equiv.Perm (Fin 6)) := by
    rintro ⟨rfl, h2⟩
    have hk2 : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card, hk, h2]
    have : CharP k 2 := charP_of_card_eq_prime hk2
    obtain ⟨e6⟩ := nonempty_statedSp_two_mulEquiv_perm hk2
    exact ⟨eH.symm.trans ((MulEquiv.ofBijective (proj 2 k)
      UnitaryHigher.proj_bijective_of_charTwo).symm.trans e6)⟩
  have hrad : CFSG.solvableRadical H₀ = ⊥ := by
    by_cases he : r = 2 ∧ ℓ ^ (f / p) = 2
    · obtain ⟨e⟩ := hexc he
      exact solvableRadical_eq_bot_of_mulEquiv_perm_six e
    · obtain ⟨hs, hperf⟩ := hsimple he
      exact solvableRadical_eq_bot_of_isSimpleGroup
  have hprime : ∀ g : StatedSp r K, (g : GL (Fin r ⊕ Fin r) K) ∈ UnitaryHigher.primeFieldSp r K →
      proj r K g ∈ H₀ := by
    intro g hg
    obtain ⟨g₀, hg₀⟩ := primeFieldSp_le_range k hg
    exact mem_range_subfieldSpProj.mpr ⟨g₀, by rw [show subfieldSpHom r k g₀ = g from
      Subtype.ext hg₀]⟩
  have hallE : ∀ β : MulAut (StatedProj (StatedSp r K)), (∀ x ∈ H₀, β x = x) →
      β ∈ spSemilinearAutGroup r K := by
    intro β hβ
    rcases (by omega : 3 ≤ r ∨ r = 2) with h3 | rfl
    · rw [(automorphism_generation h3).1]
      exact Subgroup.mem_top β
    · by_cases hℓ2 : ℓ = 2
      · subst hℓ2
        exact mem_spSemilinearAutGroup_of_fixes hf hK β fun g hg => hβ _ (hprime g hg)
      · have hodd' : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
        obtain ⟨A, τ, hAτ⟩ :=
          (odd_symplectic_automorphism_semilinear_representation hodd' le_rfl).1 β
        exact mem_spSemilinearAutGroup_iff.mpr ⟨A, τ, hAτ⟩
  have hfixing : fixingSubgroup (MulAut (StatedProj (StatedSp r K)))
      (H₀ : Set (StatedProj (StatedSp r K))) =
        (fixingSubgroup (K ≃+* K) (k : Set K)).map (fieldAut r K) := by
    ext β
    rw [mem_fixingSubgroup_iff]
    constructor
    · intro hβ
      have hβ' : ∀ x ∈ H₀, β x = x := fun x hx => hβ x hx
      obtain ⟨A, τ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp (hallE β hβ')
      obtain ⟨heq, hτ⟩ := eq_fieldAut_of_fixes hr1 A τ hβ'
      rw [heq]
      exact ⟨τ, (mem_fixingSubgroup_iff _).mpr fun t ht => by
        rw [RingAut.smul_def]; exact hτ t ht, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩ x hx
      rw [MulAut.smul_def]
      exact fieldAut_apply_of_fixes (fun t ht => by
        have := (mem_fixingSubgroup_iff _).mp hτ t ht
        rwa [RingAut.smul_def] at this) hx
  have hfield : (fixingSubgroup (K ≃+* K) (k : Set K)).map (fieldAut r K) =
      Subgroup.zpowers (fieldAut r K σ) := by
    ext β
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      have hτσ : τ ∈ Subgroup.zpowers σ := mem_zpowers_of_fixed fun x hx => by
        have := (mem_fixingSubgroup_iff _).mp hτ x (mem_descentField.mpr hx)
        rwa [RingAut.smul_def] at this
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτσ
      exact ⟨n, (map_zpow (fieldAut r K) σ n).symm⟩
    · rintro ⟨n, rfl⟩
      refine ⟨σ ^ n, (mem_fixingSubgroup_iff _).mpr fun t ht => ?_, map_zpow _ _ _⟩
      have hσt : σ ∈ MulAction.stabilizer (K ≃+* K) t := by
        rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]
        exact mem_descentField.mp ht
      exact (MulAction.stabilizer (K ≃+* K) t).zpow_mem hσt n
  have hfinj : Function.Injective (fieldAut r K) :=
    (CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hℓ hf hr
      hK).2.1
  have hord : Nat.card (Subgroup.zpowers (fieldAut r K σ)) = p := by
    rw [Nat.card_zpowers, orderOf_injective (fieldAut r K) hfinj σ, hσ]
  have hcent : Subgroup.centralizer ((H₀.map MulAut.conj :
      Subgroup (MulAut (StatedProj (StatedSp r K)))) :
        Set (MulAut (StatedProj (StatedSp r K)))) = Subgroup.zpowers (fieldAut r K σ) := by
    rw [← hfield, ← hfixing]
    ext β
    rw [Subgroup.mem_centralizer_iff, mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      rw [MulAut.smul_def]
      have h1 := h (MulAut.conj x) ⟨x, hx, rfl⟩
      rw [mul_conj_eq] at h1
      exact (hconj (mul_right_cancel h1)).symm
    · rintro h _ ⟨x, hx, rfl⟩
      have h1 := h x hx
      rw [MulAut.smul_def] at h1
      change MulAut.conj x * β = β * MulAut.conj x
      rw [mul_conj_eq, h1]
  refine ⟨hpf, hk, hTs, hTnc, hinj, hfixpts, hrad, fun hne => ?_, fun he => ?_, hfixing, hfield,
    hord, hcent, fun he hx => ?_⟩
  · obtain ⟨hs, hperf⟩ := hsimple hne
    exact ⟨hs, exists_ne_of_isPerfect⟩
  · obtain ⟨e⟩ := hexc he
    refine ⟨⟨e⟩, nonempty_commutator_mulEquiv_alternating e, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  · obtain ⟨hr2, h2⟩ := he
    obtain ⟨x, hxH, hxp⟩ := hx
    obtain ⟨e⟩ := hexc ⟨hr2, h2⟩
    have hℓ2 : ℓ = 2 := by
      have hdvd : ℓ ∣ 2 := h2 ▸ dvd_pow_self ℓ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp hdvd
    subst hℓ2
    have hfp1 : f / p = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h2)
    have hfeq : f = p := by
      obtain ⟨c, hc⟩ := hpf
      rw [hc, Nat.mul_div_cancel_left _ hp.pos] at hfp1
      rw [hc, hfp1, mul_one]
    have h720 : Nat.card H₀ = 720 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have hdvd : p ∣ 2 ^ 4 * (3 ^ 2 * 5) := by
      rw [← hxp]
      have := Subgroup.orderOf_dvd_natCard H₀ hxH
      rw [h720] at this
      exact this
    have hp5 : p = 5 := by
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
      · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
        · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h')) (by omega)
        · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h'
    exact ⟨rfl, hp5, by omega, by rw [hfeq, hp5]; norm_num⟩

end CFSG.RankThree.CASymplecticSubfield
