module

public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartQuad
public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType.N2Chart

open Matrix Polynomial CFSG.RankThree.CALinearPrimary CFSG.RankThree.PartOne.KCPrimary

structure SuppTwo (u₁ u₂ : SL6) : Prop where
  pow₁ : u₁ ^ 5 = 1
  pow₂ : u₂ ^ 5 = 1
  dim₁ : Module.finrank F4 (suppSp u₁) = 2
  dim₂ : Module.finrank F4 (suppSp u₂) = 2
  compl₁ : IsCompl (suppSp u₁) (fixSp u₁)
  compl₂ : IsCompl (suppSp u₂) (fixSp u₂)
  le₁₂ : suppSp u₁ ≤ fixSp u₂
  le₂₁ : suppSp u₂ ≤ fixSp u₁
  comm : Commute u₁ u₂

theorem mem_fixSp_iff {g : SL6} {v : V6} :
    v ∈ fixSp g ↔ (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v := by
  rw [fixSp, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem mulVec_pow_of_mem_fixSp {g : SL6} {v : V6} (hv : v ∈ fixSp g) (k : ℕ) :
    ((g ^ k : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v := by
  rw [mem_fixSp_iff] at hv
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hv, ih]

theorem pow_mem_centralizer_self (g : SL6) (k : ℕ) :
    g ^ k ∈ Subgroup.centralizer ({g} : Set SL6) :=
  Subgroup.pow_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr rfl) k


theorem quadOm_monic (c : F4) : (quadOm c).Monic := by
  unfold quadOm
  monicity!

theorem quadOm_natDegree (c : F4) : (quadOm c).natDegree = 2 := by
  unfold quadOm
  compute_degree!

theorem quadOm_irreducible {ω : F4} (hω : ω ^ 2 + ω + 1 = 0) : Irreducible (quadOm ω) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quadOm_natDegree]
    exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  · intro ρ hρ
    have hρ' : ρ ^ 2 + ω * ρ + 1 = 0 := by simpa [quadOm, Polynomial.IsRoot] using hρ
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      simp at hρ'
    have h3 := F4_pow_three hρ0
    have hfac : (ρ - 1) * (ρ ^ 2 + ρ + 1) = 0 := by linear_combination h3
    have h10 : (1 : F4) ≠ 0 := one_ne_zero
    rcases mul_eq_zero.mp hfac with h1 | h1
    · obtain rfl : ρ = 1 := sub_eq_zero.mp h1
      exact h10 (by linear_combination hω + (1 - ω) * hρ' - two_eq_zero_F4)
    · have hω1 : (ω - 1) * ρ = 0 := by linear_combination hρ' - h1
      obtain rfl : ω = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hω1).resolve_right hρ0)
      exact h10 (by linear_combination hω - two_eq_zero_F4)


@[expose] noncomputable def sl2Block (u : SL6) (q : F4[X]) : Subgroup SL6 :=
  (linearSpecialBlock (slGL 6 F4 u) q).comap (slGL 6 F4)

theorem five_ne_zero_F4 : (5 : F4) ≠ 0 := by
  have h5 : (5 : F4) = 1 := by linear_combination (2 : F4) * two_eq_zero_F4
  rw [h5]
  exact one_ne_zero

theorem endo_commute_of_mem_centralizer {u g : SL6} (hg : g ∈ Subgroup.centralizer ({u} : Set SL6)) :
    Commute (endo g) (endo u) := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp hg
  change endo g * endo u = endo u * endo g
  rw [← endo_mul, ← endo_mul, h]

namespace SuppTwo

variable {u₁ u₂ : SL6} (h : SuppTwo u₁ u₂)
include h

theorem sup_eq_top : suppSp u₁ ⊔ suppSp u₂ ⊔ (fixSp u₁ ⊓ fixSp u₂) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha, f, hf, rfl⟩ := Submodule.mem_sup.mp (h.compl₁.sup_eq_top ▸ Submodule.mem_top :
    v ∈ suppSp u₁ ⊔ fixSp u₁)
  obtain ⟨b, hb, w, hw, rfl⟩ := Submodule.mem_sup.mp (h.compl₂.sup_eq_top ▸ Submodule.mem_top :
    f ∈ suppSp u₂ ⊔ fixSp u₂)
  have hw₁ : w ∈ fixSp u₁ := by
    have : w = (b + w) - b := by abel
    rw [this]
    exact Submodule.sub_mem _ hf (h.le₂₁ hb)
  rw [← add_assoc]
  exact Submodule.add_mem_sup (Submodule.add_mem_sup ha hb) ⟨hw₁, hw⟩

theorem disjoint_supp : Disjoint (suppSp u₁) (suppSp u₂) := by
  rw [Submodule.disjoint_def]
  intro v ha hb
  exact (Submodule.disjoint_def.mp h.compl₂.disjoint) v hb (h.le₁₂ ha)

theorem disjoint_sup : Disjoint (suppSp u₁ ⊔ suppSp u₂) (fixSp u₁ ⊓ fixSp u₂) := by
  rw [Submodule.disjoint_def]
  intro v hv hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have ha₁ : a ∈ fixSp u₁ := by
    have : a = (a + b) - b := by abel
    rw [this]
    exact Submodule.sub_mem _ hw.1 (h.le₂₁ hb)
  have ha0 : a = 0 := (Submodule.disjoint_def.mp h.compl₁.disjoint) a ha ha₁
  subst ha0
  rw [zero_add] at hw ⊢
  exact (Submodule.disjoint_def.mp h.compl₂.disjoint) b hb hw.2

theorem finrank_sup : Module.finrank F4 ↥(suppSp u₁ ⊔ suppSp u₂) = 4 := by
  have h' := Submodule.finrank_sup_add_finrank_inf_eq (suppSp u₁) (suppSp u₂)
  rw [h.disjoint_supp.eq_bot, finrank_bot, h.dim₁, h.dim₂] at h'
  omega

theorem finrank_fix : Module.finrank F4 ↥(fixSp u₁ ⊓ fixSp u₂) = 2 := by
  have h' := Submodule.finrank_sup_add_finrank_inf_eq (suppSp u₁ ⊔ suppSp u₂)
    (fixSp u₁ ⊓ fixSp u₂)
  rw [h.disjoint_sup.eq_bot, finrank_bot, h.sup_eq_top, finrank_top, h.finrank_sup] at h'
  simp only [Module.finrank_fin_fun] at h'
  omega

theorem mulVec_mul_of_mem_supp₁ (r k : ℕ) {v : V6} (hv : v ∈ suppSp u₁) :
    ((u₁ ^ r * u₂ ^ k : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v =
      ((u₁ ^ r : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    mulVec_pow_of_mem_fixSp (h.le₁₂ hv)]

theorem mulVec_mul_of_mem_supp₂ (r k : ℕ) {v : V6} (hv : v ∈ suppSp u₂) :
    ((u₁ ^ r * u₂ ^ k : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v =
      ((u₂ ^ k : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v := by
  have hv' : ((u₂ ^ k : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ suppSp u₂ :=
    mulVec_mem_suppSp (pow_mem_centralizer_self u₂ k) hv
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    mulVec_pow_of_mem_fixSp (h.le₂₁ hv')]

omit h in
theorem mulVec_mul_of_mem_fix (r k : ℕ) {v : V6} (hv : v ∈ fixSp u₁ ⊓ fixSp u₂) :
    ((u₁ ^ r * u₂ ^ k : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    mulVec_pow_of_mem_fixSp hv.2, mulVec_pow_of_mem_fixSp hv.1]

variable {ω : F4} {r k : ℕ}

theorem aeval_quadOm_mul_supp₁ {v : V6} (hv : v ∈ suppSp u₁) :
    aeval (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω) v = aeval (endo (u₁ ^ r)) (quadOm ω) v := by
  have hv' : ((u₁ ^ r : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ suppSp u₁ :=
    mulVec_mem_suppSp (pow_mem_centralizer_self u₁ r) hv
  rw [aeval_quadOm_apply, aeval_quadOm_apply, endo_apply, endo_apply, endo_apply, endo_apply,
    h.mulVec_mul_of_mem_supp₁ r k hv, h.mulVec_mul_of_mem_supp₁ r k hv']

theorem aeval_quadOm_mul_supp₂ {v : V6} (hv : v ∈ suppSp u₂) :
    aeval (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω) v = aeval (endo (u₂ ^ k)) (quadOm ω) v := by
  have hv' : ((u₂ ^ k : SL6) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ suppSp u₂ :=
    mulVec_mem_suppSp (pow_mem_centralizer_self u₂ k) hv
  rw [aeval_quadOm_apply, aeval_quadOm_apply, endo_apply, endo_apply, endo_apply, endo_apply,
    h.mulVec_mul_of_mem_supp₂ r k hv, h.mulVec_mul_of_mem_supp₂ r k hv']

theorem ker_quadOm_eq (hω : ω ^ 2 + ω + 1 = 0)
    (h₁ : ∀ v ∈ suppSp u₁, aeval (endo (u₁ ^ r)) (quadOm ω) v = 0)
    (h₂ : ∀ v ∈ suppSp u₂, aeval (endo (u₂ ^ k)) (quadOm ω) v = 0) :
    LinearMap.ker (aeval (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω)) = suppSp u₁ ⊔ suppSp u₂ := by
  have hAB : ∀ v ∈ suppSp u₁ ⊔ suppSp u₂, aeval (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω) v = 0 := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, h.aeval_quadOm_mul_supp₁ ha, h.aeval_quadOm_mul_supp₂ hb, h₁ a ha, h₂ b hb,
      add_zero]
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have hv' : v ∈ suppSp u₁ ⊔ suppSp u₂ ⊔ (fixSp u₁ ⊓ fixSp u₂) := h.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hv'
    have hww : aeval (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω) w = ω • w := by
      rw [aeval_quadOm_apply]
      simp only [endo_apply]
      rw [SuppTwo.mulVec_mul_of_mem_fix r k hw, SuppTwo.mulVec_mul_of_mem_fix r k hw, add_comm w (ω • w),
        add_assoc, ← two_smul F4 w, two_eq_zero_F4, zero_smul, add_zero]
    rw [map_add, hAB x hx, zero_add, hww] at hv
    have hw0 : w = 0 := (smul_eq_zero.mp hv).resolve_left hω0
    rw [hw0, add_zero]
    exact hx
  · intro v hv
    exact hAB v hv

theorem mem_primaryFactors_X_sub_one :
    (X - 1 : F4[X]) ∈ primaryFactors (endo (u₁ ^ r * u₂ ^ k)) ∧
      fixSp u₁ ⊓ fixSp u₂ ≤ primaryComponent (endo (u₁ ^ r * u₂ ^ k)) (X - 1) := by
  have hle : fixSp u₁ ⊓ fixSp u₂ ≤ primaryComponent (endo (u₁ ^ r * u₂ ^ k)) (X - 1) := by
    intro w hw
    rw [mem_primaryComponent, map_sub, aeval_X, map_one, LinearMap.sub_apply, endo_apply,
      SuppTwo.mulVec_mul_of_mem_fix r k hw, Module.End.one_apply, sub_self]
  refine ⟨?_, hle⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := fixSp u₁ ⊓ fixSp u₂) (by
    intro h0
    have := h.finrank_fix
    rw [h0, finrank_bot] at this
    norm_num at this)
  have hev : (endo (u₁ ^ r * u₂ ^ k)).HasEigenvalue 1 := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff, endo_apply, SuppTwo.mulVec_mul_of_mem_fix r k hw, one_smul]
  rw [mem_primaryFactors]
  refine ⟨?_, ?_, ?_⟩
  · simpa using Polynomial.irreducible_X_sub_C (1 : F4)
  · simpa using Polynomial.monic_X_sub_C (1 : F4)
  · simpa using Polynomial.dvd_iff_isRoot.mpr (Module.End.hasEigenvalue_iff_isRoot.mp hev)

theorem mem_primaryFactors_quadOm (hω : ω ^ 2 + ω + 1 = 0)
    (h₁ : ∀ v ∈ suppSp u₁, aeval (endo (u₁ ^ r)) (quadOm ω) v = 0)
    (h₂ : ∀ v ∈ suppSp u₂, aeval (endo (u₂ ^ k)) (quadOm ω) v = 0) :
    quadOm ω ∈ primaryFactors (endo (u₁ ^ r * u₂ ^ k)) ∧
      primaryComponent (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω) = suppSp u₁ ⊔ suppSp u₂ := by
  have hker := h.ker_quadOm_eq hω h₁ h₂
  refine ⟨?_, hker⟩
  set t := endo (u₁ ^ r * u₂ ^ k) with ht
  have hzero : aeval t ((X - 1) * quadOm ω) = 0 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ suppSp u₁ ⊔ suppSp u₂ ⊔ (fixSp u₁ ⊓ fixSp u₂) := h.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have hx0 : aeval t (quadOm ω) x = 0 := by
      have : x ∈ LinearMap.ker (aeval t (quadOm ω)) := by rw [ht, hker]; exact hx
      exact this
    have hw1 : aeval t (X - 1 : F4[X]) w = 0 :=
      (h.mem_primaryFactors_X_sub_one (r := r) (k := k)).2 hw
    rw [map_mul, LinearMap.zero_apply, Module.End.mul_apply, map_add, hx0, zero_add,
      ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hw1, map_zero]
  have hdvd : minpoly F4 t ∣ (X - 1) * quadOm ω := minpoly.dvd F4 t hzero
  rw [mem_primaryFactors]
  refine ⟨quadOm_irreducible hω, quadOm_monic ω, ?_⟩
  by_contra hnd
  have hcop : IsCoprime (quadOm ω) (minpoly F4 t) :=
    ((quadOm_irreducible hω).coprime_iff_not_dvd).mpr hnd
  have h1 : minpoly F4 t ∣ X - 1 := hcop.symm.dvd_of_dvd_mul_right hdvd
  have ht1 : aeval t (X - 1 : F4[X]) = 0 := minpoly.dvd_iff.mp h1
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := suppSp u₁) (by
    intro h0
    have := h.dim₁
    rw [h0, finrank_bot] at this
    norm_num at this)
  have hta : t a = a := by
    have := congrArg (fun f : Module.End F4 V6 => f a) ht1
    simpa [sub_eq_zero] using this
  have hqa : aeval t (quadOm ω) a = 0 := by
    have : a ∈ LinearMap.ker (aeval t (quadOm ω)) := by
      rw [ht, hker]
      exact Submodule.mem_sup_left ha
    exact this
  rw [aeval_quadOm_apply, hta, hta, add_comm a (ω • a), add_assoc, ← two_smul F4 a,
    two_eq_zero_F4, zero_smul, add_zero] at hqa
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  exact ha0 ((smul_eq_zero.mp hqa).resolve_left hω0)

theorem primaryMultiplicity_quadOm (hω : ω ^ 2 + ω + 1 = 0)
    (h₁ : ∀ v ∈ suppSp u₁, aeval (endo (u₁ ^ r)) (quadOm ω) v = 0)
    (h₂ : ∀ v ∈ suppSp u₂, aeval (endo (u₂ ^ k)) (quadOm ω) v = 0) :
    primaryMultiplicity (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω) = 2 ∧
      Nat.card (AdjoinRoot (quadOm ω)) = 16 := by
  have : Fact (Irreducible (quadOm ω)) := ⟨quadOm_irreducible hω⟩
  constructor
  · have hfr := finrank_primaryComponent (x := endo (u₁ ^ r * u₂ ^ k)) (a := quadOm ω)
    have h4 : Module.finrank F4 ↥(primaryComponent (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω)) = 4 := by
      rw [(h.mem_primaryFactors_quadOm hω h₁ h₂).2, h.finrank_sup]
    rw [h4, quadOm_natDegree] at hfr
    unfold primaryMultiplicity
    omega
  · rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, quadOm_natDegree,
      GaloisField.card 2 2 (by norm_num)]
    norm_num

theorem pow_mul_pow_five : (u₁ ^ r * u₂ ^ k) ^ 5 = 1 := by
  rw [(h.comm.pow_pow r k).mul_pow, ← pow_mul, ← pow_mul, mul_comm r, mul_comm k, pow_mul,
    pow_mul, h.pow₁, h.pow₂, one_pow, one_pow, mul_one]

theorem squarefree_minpoly :
    Squarefree (minpoly F4 ((slGL 6 F4 (u₁ ^ r * u₂ ^ k) : LinearMap.GeneralLinearGroup F4 V6) :
      Module.End F4 V6)) :=
  squarefree_minpoly_slGL (p := 5) five_ne_zero_F4 h.pow_mul_pow_five

variable (hω : ω ^ 2 + ω + 1 = 0)
    (h₁ : ∀ v ∈ suppSp u₁, aeval (endo (u₁ ^ r)) (quadOm ω) v = 0)
    (h₂ : ∀ v ∈ suppSp u₂, aeval (endo (u₂ ^ k)) (quadOm ω) v = 0)
include hω h₁ h₂

omit hω h₁ h₂ in
theorem sl2Block_fix {g : SL6} (hg : g ∈ sl2Block (u₁ ^ r * u₂ ^ k) (quadOm ω)) {w : V6}
    (hw : w ∈ fixSp u₁ ⊓ fixSp u₂) : (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ w = w := by
  obtain ⟨-, htriv, -⟩ := mem_linearSpecialBlock.mp (Subgroup.mem_comap.mp hg)
  have hX := h.mem_primaryFactors_X_sub_one (r := r) (k := k)
  have hne : (X - 1 : F4[X]) ≠ quadOm ω := by
    intro he
    have h1 : (X - 1 : F4[X]).natDegree = 1 := by compute_degree!
    rw [he, quadOm_natDegree] at h1
    norm_num at h1
  have := htriv (X - 1) hX.1 hne w (hX.2 hw)
  rwa [coe_slGL, Matrix.toLin'_apply] at this

theorem sl2Block_mem_sup {g : SL6} (hg : g ∈ sl2Block (u₁ ^ r * u₂ ^ k) (quadOm ω)) {v : V6}
    (hv : v ∈ suppSp u₁ ⊔ suppSp u₂) :
    (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ suppSp u₁ ⊔ suppSp u₂ := by
  have hP := (h.mem_primaryFactors_quadOm hω h₁ h₂).2
  have hc := endo_commute_of_mem_centralizer (comap_linearSpecialBlock_le_centralizer _ hg)
  rw [← hP] at hv ⊢
  rw [← endo_apply]
  exact apply_mem_primaryComponent hc hv

theorem sl2Block_mulEquiv :
    Nonempty (sl2Block (u₁ ^ r * u₂ ^ k) (quadOm ω) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  have : Fact (Irreducible (quadOm ω)) := ⟨quadOm_irreducible hω⟩
  have hq : quadOm ω ∈ primaryFactors
      ((slGL 6 F4 (u₁ ^ r * u₂ ^ k) : LinearMap.GeneralLinearGroup F4 V6) : Module.End F4 V6) :=
    (h.mem_primaryFactors_quadOm hω h₁ h₂).1
  obtain ⟨hmult, hcard⟩ := h.primaryMultiplicity_quadOm hω h₁ h₂
  obtain ⟨e1⟩ := comap_linearSpecialBlock_mulEquiv h.squarefree_minpoly hq
  let e2 := MulEquiv.ofBijective (linearSpecialBlockRestrict (slGL 6 F4 (u₁ ^ r * u₂ ^ k))
    (quadOm ω)) ⟨linearSpecialBlockRestrict_injective h.squarefree_minpoly,
      linearSpecialBlockRestrict_surjective h.squarefree_minpoly hq⟩
  let b : Module.Basis (Fin 2) (AdjoinRoot (quadOm ω))
      (primaryComponent (endo (u₁ ^ r * u₂ ^ k)) (quadOm ω)) :=
    Module.finBasisOfFinrankEq _ _ hmult
  let e3 := (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  have : Finite (AdjoinRoot (quadOm ω)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let : Fintype (AdjoinRoot (quadOm ω)) := Fintype.ofFinite _
  let : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  have hcard' : Fintype.card (AdjoinRoot (quadOm ω)) = Fintype.card (GaloisField 2 4) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
      GaloisField.card 2 4 (by norm_num)]
    norm_num
  let κ := FiniteField.ringEquivOfCardEq hcard'
  let e4 : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (quadOm ω)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4) :=
    { toFun := Matrix.SpecialLinearGroup.map κ.toRingHom
      invFun := Matrix.SpecialLinearGroup.map κ.symm.toRingHom
      left_inv := fun g => by
        ext i j
        simp
      right_inv := fun g => by
        ext i j
        simp
      map_mul' := map_mul _ }
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

theorem sl2Block_isQuasisimple :
    CFSG.IsQuasisimple ↥(sl2Block (u₁ ^ r * u₂ ^ k) (quadOm ω)) := by
  have : Fact (Irreducible (quadOm ω)) := ⟨quadOm_irreducible hω⟩
  have hq : quadOm ω ∈ primaryFactors
      ((slGL 6 F4 (u₁ ^ r * u₂ ^ k) : LinearMap.GeneralLinearGroup F4 V6) : Module.End F4 V6) :=
    (h.mem_primaryFactors_quadOm hω h₁ h₂).1
  obtain ⟨hmult, hcard⟩ := h.primaryMultiplicity_quadOm hω h₁ h₂
  obtain ⟨e1⟩ := comap_linearSpecialBlock_mulEquiv h.squarefree_minpoly hq
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm
    (isQuasisimple_linearSpecialBlock h.squarefree_minpoly hq
      (Or.inr ⟨hmult.ge, by rw [hcard]; norm_num⟩))

end SuppTwo

end CFSG.StandardType.N2Chart

end
