module

public import CFSG.RankThree.PartOne.S11d.OrthSplitAbs
public import CFSG.RankThree.PartOne.S11d.OrthGoodSingle
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Psi

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] noncomputable def SplitFourModel.psi (M : SplitFourModel (Q.comp (fixedSpace x).subtype))
    (hx : OddOrderIsometry Q p x) : SL(2, K) × SL(2, K) →* (V ≃ₗ[K] V) :=
  (supportedBlock Q x (X - 1)).subtype.comp ((fixedBlockEquiv hx).symm.toMonoidHom.comp M.act)

variable (M : SplitFourModel (Q.comp (fixedSpace x).subtype)) (hx : OddOrderIsometry Q p x)

theorem SplitFourModel.psi_mem_block (z : SL(2, K) × SL(2, K)) :
    M.psi hx z ∈ supportedBlock Q x (X - 1) :=
  ((fixedBlockEquiv hx).symm (M.act z)).2

theorem SplitFourModel.fixedBlockEquiv_psi (z : SL(2, K) × SL(2, K)) :
    fixedBlockEquiv hx ⟨M.psi hx z, M.psi_mem_block hx z⟩ = M.act z :=
  (fixedBlockEquiv hx).apply_symm_apply (M.act z)

theorem SplitFourModel.psi_apply_fixed (z : SL(2, K) × SL(2, K)) (w : fixedSpace x) :
    (M.psi hx z) (w : V) = ((M.act z).val w : V) := by
  have h := coe_fixedBlockEquiv hx ⟨M.psi hx z, M.psi_mem_block hx z⟩ w
  rw [M.fixedBlockEquiv_psi hx z] at h
  exact h.symm

theorem SplitFourModel.psi_comm_x (z : SL(2, K) × SL(2, K)) (v : V) :
    M.psi hx z (x v) = x (M.psi hx z v) :=
  (mem_isometryCentralizer.mp (mem_supportedBlock.mp (M.psi_mem_block hx z)).1).2 v

theorem SplitFourModel.psi_injective [CharP K 2] : Function.Injective (M.psi hx) := by
  intro a b h
  apply M.act_injective
  apply (fixedBlockEquiv hx).symm.injective
  exact Subtype.ext h

theorem SplitFourModel.range_psi : (M.psi hx).range = supportedFixedDerived Q x := by
  ext f
  constructor
  · rintro ⟨z, rfl⟩
    refine mem_supportedFixedDerived.mpr ⟨M.psi_mem_block hx z, ?_⟩
    have h1 : restrictFixed Q x ⟨M.psi hx z, M.psi_mem_block hx z⟩ = (M.act z).val :=
      congrArg Subtype.val (M.fixedBlockEquiv_psi hx z)
    rw [h1, orthDerived, ← Subgroup.map_subtype_commutator]
    exact ⟨M.act z, (M.mem_commutator_iff _).mpr ⟨z, rfl⟩, rfl⟩
  · intro hf
    obtain ⟨hg, hrf⟩ := mem_supportedFixedDerived.mp hf
    have hgc : fixedBlockEquiv hx ⟨f, hg⟩ ∈
        commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
      rw [orthDerived, ← Subgroup.map_subtype_commutator] at hrf
      obtain ⟨c, hc, hcv⟩ := hrf
      have : c = fixedBlockEquiv hx ⟨f, hg⟩ := Subtype.ext hcv
      rwa [← this]
    obtain ⟨z, hz⟩ := (M.mem_commutator_iff _).mp hgc
    refine ⟨z, ?_⟩
    have : (⟨M.psi hx z, M.psi_mem_block hx z⟩ : ↥(supportedBlock Q x (X - 1))) = ⟨f, hg⟩ := by
      apply (fixedBlockEquiv hx).injective
      rw [M.fixedBlockEquiv_psi hx z, hz]
    exact congrArg Subtype.val this

theorem SplitFourModel.psi_mem_orthDerived (z : SL(2, K) × SL(2, K)) :
    M.psi hx z ∈ orthDerived Q :=
  hx.supportedFixedDerived_le_orthDerived ((M.range_psi hx) ▸ ⟨z, rfl⟩)

end Psi

section Theta

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
  (M : SplitFourModel (Q.comp (fixedSpace x).subtype)) (hx : OddOrderIsometry Q p x)

@[expose] noncomputable def SplitFourModel.theta : SL(2, K) × SL(2, K) →* ProjOrthDerived Q :=
  (piOrth Q).comp ((M.psi hx).codRestrict (orthDerived Q) (M.psi_mem_orthDerived hx))

theorem SplitFourModel.theta_apply (z : SL(2, K) × SL(2, K)) :
    M.theta hx z = piOrth Q ⟨M.psi hx z, M.psi_mem_orthDerived hx z⟩ := rfl

theorem SplitFourModel.theta_injective [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [Nontrivial V] : Function.Injective (M.theta hx) := fun a b h => by
  have h1 : (⟨M.psi hx a, M.psi_mem_orthDerived hx a⟩ : orthDerived Q) =
      ⟨M.psi hx b, M.psi_mem_orthDerived hx b⟩ := piOrth_injective hQ h
  have h2 : M.psi hx a = M.psi hx b := congrArg (fun g : orthDerived Q => (g : V ≃ₗ[K] V)) h1
  exact M.psi_injective hx h2

theorem SplitFourModel.mem_supportedFactor_left {f : V ≃ₗ[K] V} :
    f ∈ supportedFactor hx (splitFourFactors M.e 0) ↔ ∃ a : SL(2, K), M.psi hx (a, 1) = f := by
  constructor
  · rintro ⟨_, ⟨j, ⟨l, ⟨a, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem SplitFourModel.mem_supportedFactor_right {f : V ≃ₗ[K] V} :
    f ∈ supportedFactor hx (splitFourFactors M.e 1) ↔ ∃ b : SL(2, K), M.psi hx (1, b) = f := by
  constructor
  · rintro ⟨_, ⟨j, ⟨l, ⟨b, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem SplitFourModel.mem_fixedFactorImage_left {t : ProjOrthDerived Q} :
    t ∈ fixedFactorImage hx (splitFourFactors M.e 0) ↔ ∃ a : SL(2, K), M.theta hx (a, 1) = t := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := (M.mem_supportedFactor_left hx).mp (Subgroup.mem_subgroupOf.mp hg)
    exact ⟨a, by rw [M.theta_apply hx]; congr 1; exact Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨M.psi hx (a, 1), M.psi_mem_orthDerived hx _⟩,
      Subgroup.mem_subgroupOf.mpr ((M.mem_supportedFactor_left hx).mpr ⟨a, rfl⟩), rfl⟩

theorem SplitFourModel.mem_fixedFactorImage_right {t : ProjOrthDerived Q} :
    t ∈ fixedFactorImage hx (splitFourFactors M.e 1) ↔ ∃ b : SL(2, K), M.theta hx (1, b) = t := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨b, hb⟩ := (M.mem_supportedFactor_right hx).mp (Subgroup.mem_subgroupOf.mp hg)
    exact ⟨b, by rw [M.theta_apply hx]; congr 1; exact Subtype.ext hb⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨M.psi hx (1, b), M.psi_mem_orthDerived hx _⟩,
      Subgroup.mem_subgroupOf.mpr ((M.mem_supportedFactor_right hx).mpr ⟨b, rfl⟩), rfl⟩

end Theta

section Outer

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
  (M : SplitFourModel (Q.comp (fixedSpace x).subtype)) (hx : OddOrderIsometry Q p x)

theorem SplitFourModel.commute_of_inner [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [Nontrivial V] {S : V ≃+ V} {α : MulAut (ProjOrthDerived Q)} (hα : ActsBySemilinear Q S α)
    (z₀ z : SL(2, K) × SL(2, K))
    (hconj : α (M.theta hx z) = M.theta hx z₀ * M.theta hx z * (M.theta hx z₀)⁻¹) (u : V) :
    (M.psi hx z₀).symm (S (M.psi hx z u)) = M.psi hx z ((M.psi hx z₀).symm (S u)) := by
  obtain ⟨ω', h1, h2⟩ := hα ⟨M.psi hx z, M.psi_mem_orthDerived hx z⟩
  have h5 : M.theta hx z₀ * M.theta hx z * (M.theta hx z₀)⁻¹ = M.theta hx (z₀ * z * z₀⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  have h6 : piOrth Q ω' = piOrth Q ⟨M.psi hx (z₀ * z * z₀⁻¹), M.psi_mem_orthDerived hx _⟩ := by
    rw [← h2]
    exact hconj.trans h5
  have h7 := piOrth_injective hQ h6
  have h8 : ∀ v, S (M.psi hx z (S.symm v)) = M.psi hx (z₀ * z * z₀⁻¹) v := fun v => by
    rw [← h1 v]
    exact congrArg (fun a : orthDerived Q => (a : V ≃ₗ[K] V) v) h7
  have h9 := h8 (S u)
  rw [AddEquiv.symm_apply_apply, map_mul, map_mul, map_inv] at h9
  rw [h9, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem SplitFourModel.symm_mem_fixed {S : V ≃+ V} (hSx : ∀ v, S (x v) = x (S v))
    (z₀ : SL(2, K) × SL(2, K)) {w : V} (hw : w ∈ fixedSpace x) :
    (M.psi hx z₀).symm (S w) ∈ fixedSpace x := by
  have h1 : x ((M.psi hx z₀).symm (S w)) = (M.psi hx z₀).symm (x (S w)) := by
    rw [LinearEquiv.eq_symm_apply, M.psi_comm_x hx, LinearEquiv.apply_symm_apply]
  rw [mem_fixedSpace, h1, ← hSx, mem_fixedSpace.mp hw]

@[expose] noncomputable def SplitFourModel.matrixMap (F : V → V)
    (hF : ∀ w ∈ fixedSpace x, F w ∈ fixedSpace x) :
    Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K :=
  fun X => M.ψ ⟨F (M.ψ.symm X : V), hF _ (M.ψ.symm X).2⟩

theorem SplitFourModel.matrixMap_mul (F : V → V) (hF : ∀ w ∈ fixedSpace x, F w ∈ fixedSpace x)
    (z : SL(2, K) × SL(2, K)) (hz : ∀ u, F (M.psi hx z u) = M.psi hx z (F u))
    (X : Matrix (Fin 2) (Fin 2) K) :
    M.matrixMap F hF (z.1.val * X * (z.2⁻¹ : SL(2, K)).val) =
      z.1.val * M.matrixMap F hF X * (z.2⁻¹ : SL(2, K)).val := by
  set Y : Matrix (Fin 2) (Fin 2) K := z.1.val * X * (z.2⁻¹ : SL(2, K)).val with hY
  have h1 : M.ψ.symm Y = (M.act z).val (M.ψ.symm X) := by
    rw [LinearEquiv.symm_apply_eq, M.psi_act, LinearEquiv.apply_symm_apply]
  have h3 : ((M.ψ.symm Y : fixedSpace x) : V) = M.psi hx z ((M.ψ.symm X : fixedSpace x) : V) := by
    rw [h1, M.psi_apply_fixed hx z]
  have h2 : (⟨F (M.ψ.symm Y : V), hF _ (M.ψ.symm Y).2⟩ : fixedSpace x) =
      (M.act z).val ⟨F (M.ψ.symm X : V), hF _ (M.ψ.symm X).2⟩ := by
    apply Subtype.ext
    show F ((M.ψ.symm Y : fixedSpace x) : V) =
      (((M.act z).val ⟨F (M.ψ.symm X : V), hF _ (M.ψ.symm X).2⟩ : fixedSpace x) : V)
    rw [h3, hz, ← M.psi_apply_fixed hx z ⟨F (M.ψ.symm X : V), hF _ (M.ψ.symm X).2⟩]
  have h4 : M.matrixMap F hF Y = M.ψ ((M.act z).val ⟨F (M.ψ.symm X : V), hF _ (M.ψ.symm X).2⟩) :=
    congrArg M.ψ h2
  rw [h4, M.psi_act]
  rfl

theorem SplitFourModel.sigma_eq_of_commute_left {σ : K ≃+* K} {S : V ≃+ V}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v) (hSx : ∀ v, S (x v) = x (S v)) (a₀ : SL(2, K))
    (hcomm : ∀ (a : SL(2, K)) u, (M.psi hx (a₀, 1)).symm (S (M.psi hx (a, 1) u)) =
      M.psi hx (a, 1) ((M.psi hx (a₀, 1)).symm (S u))) (c : K) : σ c = c := by
  have hF : ∀ w ∈ fixedSpace x, (fun u => (M.psi hx (a₀, 1)).symm (S u)) w ∈ fixedSpace x :=
    fun w hw => M.symm_mem_fixed hx hSx (a₀, 1) hw
  refine eq_of_semilinear_of_commute_left (σ := (σ : K →+* K))
    (F := M.matrixMap (fun u => (M.psi hx (a₀, 1)).symm (S u)) hF) ?_ ?_ ?_ ?_ c
  · intro X Y
    unfold SplitFourModel.matrixMap
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
  · intro X Y h
    have h1 := M.ψ.injective h
    have h2 := congrArg Subtype.val h1
    simp only at h2
    have h3 := S.injective ((M.psi hx (a₀, 1)).symm.injective h2)
    exact M.ψ.symm.injective (Subtype.ext h3)
  · intro c X
    unfold SplitFourModel.matrixMap
    have h1 : (⟨(fun u => (M.psi hx (a₀, 1)).symm (S u)) (M.ψ.symm (c • X) : V),
        hF _ (M.ψ.symm (c • X)).2⟩ : fixedSpace x) =
        (σ c) • ⟨(fun u => (M.psi hx (a₀, 1)).symm (S u)) (M.ψ.symm X : V),
          hF _ (M.ψ.symm X).2⟩ := by
      apply Subtype.ext
      simp only [map_smul, Submodule.coe_smul, hS]
    rw [h1, map_smul]
    rfl
  · intro A X
    have h := M.matrixMap_mul hx (fun u => (M.psi hx (a₀, 1)).symm (S u)) hF (A, 1) (hcomm A) X
    simpa using h

theorem SplitFourModel.sigma_eq_of_commute_right {σ : K ≃+* K} {S : V ≃+ V}
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v) (hSx : ∀ v, S (x v) = x (S v)) (b₀ : SL(2, K))
    (hcomm : ∀ (b : SL(2, K)) u, (M.psi hx (1, b₀)).symm (S (M.psi hx (1, b) u)) =
      M.psi hx (1, b) ((M.psi hx (1, b₀)).symm (S u))) (c : K) : σ c = c := by
  have hF : ∀ w ∈ fixedSpace x, (fun u => (M.psi hx (1, b₀)).symm (S u)) w ∈ fixedSpace x :=
    fun w hw => M.symm_mem_fixed hx hSx (1, b₀) hw
  refine eq_of_semilinear_of_commute_right (σ := (σ : K →+* K))
    (F := M.matrixMap (fun u => (M.psi hx (1, b₀)).symm (S u)) hF) ?_ ?_ ?_ ?_ c
  · intro X Y
    unfold SplitFourModel.matrixMap
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
  · intro X Y h
    have h1 := M.ψ.injective h
    have h2 := congrArg Subtype.val h1
    simp only at h2
    have h3 := S.injective ((M.psi hx (1, b₀)).symm.injective h2)
    exact M.ψ.symm.injective (Subtype.ext h3)
  · intro c X
    unfold SplitFourModel.matrixMap
    have h1 : (⟨(fun u => (M.psi hx (1, b₀)).symm (S u)) (M.ψ.symm (c • X) : V),
        hF _ (M.ψ.symm (c • X)).2⟩ : fixedSpace x) =
        (σ c) • ⟨(fun u => (M.psi hx (1, b₀)).symm (S u)) (M.ψ.symm X : V),
          hF _ (M.ψ.symm X).2⟩ := by
      apply Subtype.ext
      simp only [map_smul, Submodule.coe_smul, hS]
    rw [h1, map_smul]
    rfl
  · intro B X
    have h := M.matrixMap_mul hx (fun u => (M.psi hx (1, b₀)).symm (S u)) hF (1, B⁻¹)
      (hcomm B⁻¹) X
    simpa using h

end Outer

section Family

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
  (M : SplitFourModel (Q.comp (fixedSpace x).subtype)) (hx : OddOrderIsometry Q p x)

omit [CharP K 2] in
theorem exists_splitFourModel (hx : OddOrderIsometry Q p x) (hd : finrank K (fixedSpace x) = 4)
    (hsplit : ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
      ∀ u ∈ S, (Q.comp (fixedSpace x).subtype) u = 0) (hK : 4 ≤ Nat.card K) :
    Nonempty (SplitFourModel (Q.comp (fixedSpace x).subtype)) := by
  have hq2 : Nat.card K ≠ 2 := by omega
  have hq3 : Nat.card K ≠ 3 := by omega
  obtain ⟨-, -, -, hcov4, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
    (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate
    (Or.inr (Or.inr ⟨hd, hsplit⟩))
  obtain ⟨ψ, e, hψ, he, hcomm_eq, hqL, hqR, hnL, hnR, hcomm⟩ := hcov4 hd hsplit hq2 hq3
  exact ⟨⟨ψ, e, hψ, he, hcomm_eq, hqL, hqR, hnL, hnR, hcomm⟩⟩

omit [Finite K] [CharP K 2] in
theorem SplitFourModel.family :
    (⨆ i, fixedFactorImage hx (splitFourFactors M.e i)) = fixedComponentImage Q x ∧
      ∀ i, CFSG.IsQuasisimple ↥(fixedFactorImage hx (splitFourFactors M.e i)) ∧
        fixedFactorImage hx (splitFourFactors M.e i) ≤ centralizerImage Q x ∧
        ((fixedFactorImage hx (splitFourFactors M.e i)).subgroupOf
          (centralizerImage Q x)).IsSubnormal := by
  have hsup : (⨆ i, splitFourFactors M.e i) = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype)) := by
    rw [M.hcomm_eq]
    refine le_antisymm (iSup_le fun i => ?_) (sup_le ?_ ?_)
    · fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact le_iSup (splitFourFactors M.e) 0
    · exact le_iSup (splitFourFactors M.e) 1
  have hLle : ∀ i, splitFourFactors M.e i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype)) := fun i => hsup ▸ le_iSup (splitFourFactors M.e) i
  have hL : ∀ i, CFSG.IsQuasisimple ↥(splitFourFactors M.e i) ∧
      splitFourFactors M.e i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)) ∧
      ((splitFourFactors M.e i).subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)))).Normal := by
    intro i
    fin_cases i
    · exact ⟨M.hqL, hLle 0, M.hnL⟩
    · exact ⟨M.hqR, hLle 1, M.hnR⟩
  have hc : ∀ i j, i ≠ j → ∀ u ∈ splitFourFactors M.e i, ∀ v ∈ splitFourFactors M.e j,
      u * v = v * u := by
    intro i j hij u hu v hv
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact M.hcomm u hu v hv
    · exact (M.hcomm v hv u hu).symm
    · exact absurd rfl hij
  obtain ⟨hsupC, hC, -⟩ := hx.fixedFactorImage_family (splitFourFactors M.e) hsup hL hc
  exact ⟨hsupC, fun i => ⟨(hC i).2.1, (hC i).2.2.1, (hC i).2.2.2⟩⟩

end Family

section Pair

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
  (M : SplitFourModel (Q.comp (fixedSpace x).subtype)) (hx : OddOrderIsometry Q p x)

theorem SplitFourModel.range_left :
    ((M.theta hx).comp (MonoidHom.inl _ _)).range =
      fixedFactorImage hx (splitFourFactors M.e 0) := by
  ext t
  rw [MonoidHom.mem_range, M.mem_fixedFactorImage_left hx]
  rfl

theorem SplitFourModel.range_right :
    ((M.theta hx).comp (MonoidHom.inr _ _)).range =
      fixedFactorImage hx (splitFourFactors M.e 1) := by
  ext t
  rw [MonoidHom.mem_range, M.mem_fixedFactorImage_right hx]
  rfl

noncomputable def SplitFourModel.leftEquiv [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [Nontrivial V] : SL(2, K) ≃* ↥(fixedFactorImage hx (splitFourFactors M.e 0)) :=
  (MonoidHom.ofInjective (f := (M.theta hx).comp (MonoidHom.inl _ _)) (fun _ _ h =>
    (Prod.mk.inj (M.theta_injective hx hQ h)).1)).trans (MulEquiv.subgroupCongr (M.range_left hx))

noncomputable def SplitFourModel.rightEquiv [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [Nontrivial V] : SL(2, K) ≃* ↥(fixedFactorImage hx (splitFourFactors M.e 1)) :=
  (MonoidHom.ofInjective (f := (M.theta hx).comp (MonoidHom.inr _ _)) (fun _ _ h =>
    (Prod.mk.inj (M.theta_injective hx hQ h)).2)).trans (MulEquiv.subgroupCongr (M.range_right hx))

theorem SplitFourModel.not_inner_left [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [Nontrivial V] {σ : K ≃+* K} {S : V ≃+ V} (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v)) (hσ : ∃ c, σ c ≠ c) {α : MulAut (ProjOrthDerived Q)}
    (hα : ActsBySemilinear Q S α) :
    ∀ t₀ ∈ fixedFactorImage hx (splitFourFactors M.e 0),
      ¬ ∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 0), α g = t₀ * g * t₀⁻¹ := by
  intro t₀ ht₀ hcon
  obtain ⟨a₀, rfl⟩ := (M.mem_fixedFactorImage_left hx).mp ht₀
  obtain ⟨c, hc⟩ := hσ
  refine hc (M.sigma_eq_of_commute_left hx hS hSx a₀ (fun a u => ?_) c)
  exact M.commute_of_inner hx hQ hα (a₀, 1) (a, 1)
    (hcon _ ((M.mem_fixedFactorImage_left hx).mpr ⟨a, rfl⟩)) u

theorem SplitFourModel.not_inner_right [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [Nontrivial V] {σ : K ≃+* K} {S : V ≃+ V} (hS : ∀ (c : K) v, S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v)) (hσ : ∃ c, σ c ≠ c) {α : MulAut (ProjOrthDerived Q)}
    (hα : ActsBySemilinear Q S α) :
    ∀ t₀ ∈ fixedFactorImage hx (splitFourFactors M.e 1),
      ¬ ∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 1), α g = t₀ * g * t₀⁻¹ := by
  intro t₀ ht₀ hcon
  obtain ⟨b₀, rfl⟩ := (M.mem_fixedFactorImage_right hx).mp ht₀
  obtain ⟨c, hc⟩ := hσ
  refine hc (M.sigma_eq_of_commute_right hx hS hSx b₀ (fun b u => ?_) c)
  exact M.commute_of_inner hx hQ hα (1, b₀) (1, b)
    (hcon _ ((M.mem_fixedFactorImage_right hx).mpr ⟨b, rfl⟩)) u

theorem SplitFourModel.fixed_of_stable [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    [Nontrivial V] {α : MulAut (ProjOrthDerived Q)}
    (h0 : ∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 0),
      α g ∈ fixedFactorImage hx (splitFourFactors M.e 0))
    (h1 : ∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 1),
      α g ∈ fixedFactorImage hx (splitFourFactors M.e 1))
    {z : SL(2, K) × SL(2, K)} (hz : α (M.theta hx z) = M.theta hx z) :
    α (M.theta hx (z.1, 1)) = M.theta hx (z.1, 1) ∧
      α (M.theta hx (1, z.2)) = M.theta hx (1, z.2) := by
  obtain ⟨a', ha'⟩ := (M.mem_fixedFactorImage_left hx).mp
    (h0 _ ((M.mem_fixedFactorImage_left hx).mpr ⟨z.1, rfl⟩))
  obtain ⟨b', hb'⟩ := (M.mem_fixedFactorImage_right hx).mp
    (h1 _ ((M.mem_fixedFactorImage_right hx).mpr ⟨z.2, rfl⟩))
  have hzz : M.theta hx z = M.theta hx (z.1, 1) * M.theta hx (1, z.2) := by
    rw [← map_mul]
    congr 1
    ext <;> simp
  have h3 : M.theta hx (a', b') = M.theta hx z := by
    rw [← hz, hzz, map_mul, ← ha', ← hb', ← map_mul]
    congr 1
    ext <;> simp
  have h4 := M.theta_injective hx hQ h3
  have ha1 : a' = z.1 := congrArg Prod.fst h4
  have hb1 : b' = z.2 := congrArg Prod.snd h4
  subst ha1 hb1
  exact ⟨ha'.symm, hb'.symm⟩

theorem exists_pow_two_of_sq {G : Type*} [Group G] {t : G} (h : t ^ 2 = 1) :
    ∃ k : ℕ, orderOf t = 2 ^ k := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h) with h1 | h1
  · exact ⟨0, by simpa using h1⟩
  · exact ⟨1, by simpa using h1⟩

theorem SplitFourModel.pair_left [CharP K 2] (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    {α : MulAut (ProjOrthDerived Q)}
    (h0 : ∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 0),
      α g ∈ fixedFactorImage hx (splitFourFactors M.e 0))
    (h1 : ∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 1),
      α g ∈ fixedFactorImage hx (splitFourFactors M.e 1))
    {z₁ z₂ : SL(2, K) × SL(2, K)} (hf₁ : α (M.theta hx z₁) = M.theta hx z₁)
    (hf₂ : α (M.theta hx z₂) = M.theta hx z₂) (hsq₁ : z₁ ^ 2 = 1) (hsq₂ : z₂ ^ 2 = 1)
    (hne : M.theta hx z₁ * M.theta hx z₂ ≠ M.theta hx z₂ * M.theta hx z₁)
    (hsw : Commute z₁.1 z₂.1 ↔ Commute z₁.2 z₂.2) :
    ∃ t₁ ∈ fixedFactorImage hx (splitFourFactors M.e 0), α t₁ = t₁ ∧
      ∃ t₂ ∈ fixedFactorImage hx (splitFourFactors M.e 0), α t₂ = t₂ ∧
        (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  have hsq : ∀ z : SL(2, K) × SL(2, K), z ^ 2 = 1 →
      ∃ k : ℕ, orderOf (M.theta hx (z.1, 1)) = 2 ^ k :=
    fun z hz => exists_pow_two_of_sq (by
      rw [← map_pow]
      have : ((z.1, 1) : SL(2, K) × SL(2, K)) ^ 2 = 1 :=
        Prod.ext (by simpa using congrArg Prod.fst hz) (by simp)
      rw [this, map_one])
  refine ⟨M.theta hx (z₁.1, 1), (M.mem_fixedFactorImage_left hx).mpr ⟨_, rfl⟩,
    (M.fixed_of_stable hx hQ h0 h1 hf₁).1, M.theta hx (z₂.1, 1),
    (M.mem_fixedFactorImage_left hx).mpr ⟨_, rfl⟩, (M.fixed_of_stable hx hQ h0 h1 hf₂).1,
    hsq z₁ hsq₁, hsq z₂ hsq₂, ?_⟩
  intro hcomm
  rw [← map_mul, ← map_mul] at hcomm
  have h6 : Commute z₁.1 z₂.1 := congrArg Prod.fst (M.theta_injective hx hQ hcomm)
  have h7 : Commute z₁.2 z₂.2 := hsw.mp h6
  apply hne
  rw [← map_mul, ← map_mul]
  congr 1
  exact Prod.ext h6.eq h7.eq

theorem SplitFourModel.pair_right [CharP K 2] (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    {α : MulAut (ProjOrthDerived Q)}
    (h0 : ∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 0),
      α g ∈ fixedFactorImage hx (splitFourFactors M.e 0))
    (h1 : ∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 1),
      α g ∈ fixedFactorImage hx (splitFourFactors M.e 1))
    {z₁ z₂ : SL(2, K) × SL(2, K)} (hf₁ : α (M.theta hx z₁) = M.theta hx z₁)
    (hf₂ : α (M.theta hx z₂) = M.theta hx z₂) (hsq₁ : z₁ ^ 2 = 1) (hsq₂ : z₂ ^ 2 = 1)
    (hne : M.theta hx z₁ * M.theta hx z₂ ≠ M.theta hx z₂ * M.theta hx z₁)
    (hsw : Commute z₁.1 z₂.1 ↔ Commute z₁.2 z₂.2) :
    ∃ t₁ ∈ fixedFactorImage hx (splitFourFactors M.e 1), α t₁ = t₁ ∧
      ∃ t₂ ∈ fixedFactorImage hx (splitFourFactors M.e 1), α t₂ = t₂ ∧
        (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  have hsq : ∀ z : SL(2, K) × SL(2, K), z ^ 2 = 1 →
      ∃ k : ℕ, orderOf (M.theta hx (1, z.2)) = 2 ^ k :=
    fun z hz => exists_pow_two_of_sq (by
      rw [← map_pow]
      have : ((1, z.2) : SL(2, K) × SL(2, K)) ^ 2 = 1 :=
        Prod.ext (by simp) (by simpa using congrArg Prod.snd hz)
      rw [this, map_one])
  refine ⟨M.theta hx (1, z₁.2), (M.mem_fixedFactorImage_right hx).mpr ⟨_, rfl⟩,
    (M.fixed_of_stable hx hQ h0 h1 hf₁).2, M.theta hx (1, z₂.2),
    (M.mem_fixedFactorImage_right hx).mpr ⟨_, rfl⟩, (M.fixed_of_stable hx hQ h0 h1 hf₂).2,
    hsq z₁ hsq₁, hsq z₂ hsq₂, ?_⟩
  intro hcomm
  rw [← map_mul, ← map_mul] at hcomm
  have h6 : Commute z₁.2 z₂.2 := congrArg Prod.snd (M.theta_injective hx hQ hcomm)
  have h7 : Commute z₁.1 z₂.1 := hsw.mpr h6
  apply hne
  rw [← map_mul, ← map_mul]
  congr 1
  exact Prod.ext h7.eq h6.eq

theorem SplitFourModel.exists_pair_of_data [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V] {S : V ≃+ V}
    {α : MulAut (ProjOrthDerived Q)} (hα : ActsBySemilinear Q S α)
    {w : V} (hw : w ∈ fixedSpace x) (hQw : Q w ≠ 0) {t₁ t₂ : V ≃ₗ[K] V}
    (ht₁ : t₁ ∈ supportedFixedDerived Q x) (hS₁ : ∀ v, S (t₁ v) = t₁ (S v)) (hsq₁ : t₁ ^ 2 = 1)
    (hw₁ : t₁ w = w) (ht₂ : t₂ ∈ supportedFixedDerived Q x) (hS₂ : ∀ v, S (t₂ v) = t₂ (S v))
    (hsq₂ : t₂ ^ 2 = 1) (hw₂ : t₂ w = w) (hne : t₁ * t₂ ≠ t₂ * t₁) :
    ∃ z₁ z₂ : SL(2, K) × SL(2, K), α (M.theta hx z₁) = M.theta hx z₁ ∧
      α (M.theta hx z₂) = M.theta hx z₂ ∧ z₁ ^ 2 = 1 ∧ z₂ ^ 2 = 1 ∧
      M.theta hx z₁ * M.theta hx z₂ ≠ M.theta hx z₂ * M.theta hx z₁ ∧
      (Commute z₁.1 z₂.1 ↔ Commute z₁.2 z₂.2) := by
  have ht₁' : t₁ ∈ (M.psi hx).range := by rw [M.range_psi hx]; exact ht₁
  have ht₂' : t₂ ∈ (M.psi hx).range := by rw [M.range_psi hx]; exact ht₂
  obtain ⟨z₁, rfl⟩ := ht₁'
  obtain ⟨z₂, rfl⟩ := ht₂'
  have : Nontrivial (fixedSpace x) :=
    ⟨⟨⟨w, hw⟩, 0, fun h => hQw (by
      have h0 : w = 0 := congrArg Subtype.val h
      rw [h0, map_zero])⟩⟩
  have hfix : ∀ z : SL(2, K) × SL(2, K), M.psi hx z w = w →
      (M.act z).val ⟨w, hw⟩ = ⟨w, hw⟩ := fun z hz =>
    Subtype.ext ((M.psi_apply_fixed hx z ⟨w, hw⟩).symm.trans hz)
  refine ⟨z₁, z₂, hα.fixed ⟨M.psi hx z₁, M.psi_mem_orthDerived hx z₁⟩ hS₁,
    hα.fixed ⟨M.psi hx z₂, M.psi_mem_orthDerived hx z₂⟩ hS₂,
    M.psi_injective hx (by rw [map_pow, map_one]; exact hsq₁),
    M.psi_injective hx (by rw [map_pow, map_one]; exact hsq₂), ?_,
    M.commute_iff_of_fixes hx.polarBilin_fixed_nondegenerate (a := ⟨w, hw⟩) hQw (hfix z₁ hw₁)
      (hfix z₂ hw₂)⟩
  intro h
  apply hne
  rw [← map_mul, ← map_mul] at h
  have h2 := M.theta_injective hx hQ h
  rw [← map_mul, ← map_mul, h2]

end Pair

end CFSG.RankThree.PartOne
