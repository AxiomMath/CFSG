module

public import CFSG.LocalAnalysis.SteinbergBTOddClassicalScalarQuotientSL2
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup Matrix
open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonal

namespace OddOrthogonalQuotient

section Scalars

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

@[expose] def scalarIsometries (q : QuadraticForm k V) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup q) where
  carrier := {g | ∃ c : kˣ, ∀ v, (g : V ≃ₗ[k] V) v = (c : k) • v}
  one_mem' := ⟨1, fun v => by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun v => ?_⟩
    change (g : V ≃ₗ[k] V) ((h : V ≃ₗ[k] V) v) = _
    rw [hd, map_smul, hc, smul_smul, Units.val_mul, mul_comm]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, fun v => ?_⟩
    change (g : V ≃ₗ[k] V).symm v = _
    rw [LinearEquiv.symm_apply_eq, map_smul, hc, smul_smul, Units.inv_mul, one_smul]

theorem exists_apply_ne_zero (q : QuadraticForm k V) (hq : q.polarBilin.Nondegenerate)
    [Nontrivial V] : ∃ v, q v ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  apply hq.1 x
  intro y
  change QuadraticMap.polar q x y = 0
  rw [QuadraticMap.polar, h, h, h, sub_zero, sub_zero]

theorem eq_one_or_eq_neg_one_of_smul (q : QuadraticForm k V) (hq : q.polarBilin.Nondegenerate)
    [Nontrivial V] {g : TauCeti.QuadraticMap.orthogonalGroup q} {c : k}
    (hg : ∀ v, (g : V ≃ₗ[k] V) v = c • v) : c = 1 ∨ c = -1 := by
  obtain ⟨v, hv⟩ := exists_apply_ne_zero q hq
  have h1 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2 v
  rw [hg, QuadraticMap.map_smul, smul_eq_mul] at h1
  have h2 : (c * c - 1) * q v = 0 := by linear_combination h1
  have h3 : c * c - 1 = 0 := (mul_eq_zero.mp h2).resolve_right hv
  have h4 : (c - 1) * (c + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h4 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem mem_scalarIsometries_iff (q : QuadraticForm k V) (hq : q.polarBilin.Nondegenerate)
    [Nontrivial V] (g : TauCeti.QuadraticMap.orthogonalGroup q) :
    g ∈ scalarIsometries q ↔ (∀ v, (g : V ≃ₗ[k] V) v = v) ∨ ∀ v, (g : V ≃ₗ[k] V) v = -v := by
  constructor
  · rintro ⟨c, hc⟩
    rcases eq_one_or_eq_neg_one_of_smul q hq hc with h1 | h1
    · exact Or.inl fun v => by rw [hc, h1, one_smul]
    · exact Or.inr fun v => by rw [hc, h1, neg_one_smul]
  · rintro (h | h)
    · exact ⟨1, fun v => by rw [h, Units.val_one, one_smul]⟩
    · refine ⟨⟨-1, -1, by norm_num, by norm_num⟩, fun v => ?_⟩
      rw [h, Units.val_mk, neg_one_smul]
  
theorem mem_center_of_smul {q : QuadraticForm k V}
    {B : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)} {a : B} {c : k}
    (ha : ∀ v, ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = c • v) :
    a ∈ center B := by
  rw [mem_center_iff]
  intro b
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))
  change ((b : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V)
      (((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v) =
    ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V)
      (((b : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v)
  rw [ha, ha, map_smul]

theorem det_eq_one_of_mem_commutator {q : QuadraticForm k V}
    {g : TauCeti.QuadraticMap.orthogonalGroup q}
    (hg : g ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup q)) :
    LinearEquiv.det (g : V ≃ₗ[k] V) = 1 :=
  Abelianization.commutator_subset_ker
    (LinearEquiv.det.comp (TauCeti.QuadraticMap.orthogonalGroup q).subtype) hg

end Scalars

section Groups

theorem le_commutator_of_isComponent {G : Type*} [Group G] {B : Subgroup G}
    (hB : CFSG.IsComponent B) : B ≤ commutator G := by
  calc B = ⁅B, B⁆ := (Subgroup.isPerfect_iff.mp hB.1.1).symm
    _ ≤ commutator G := Subgroup.commutator_mono le_top le_top

theorem false_of_pow_four {G : Type*} [Group G] {A : Subgroup G} [A.Normal] {K : Type*}
    [Field K] (h2K : (2 : K) = 0) (φ : G ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) {x : G}
    (h4 : x ^ 4 = 1) (h2 : x ^ 2 ∉ A) : False :=
  (SteinbergBT.isEmpty_mulEquiv_SL2_of_orderOf_eq_four
    (SteinbergCD.orderOf_mk_eq_four h4 h2) K h2K).false φ

theorem cover_scalar_quotient {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (hF3 : Nat.card F ≠ 3) {G : Type*} [Group G] (f : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (hf : f.ker ≤ center _) {B : Subgroup G} (hB : f.range = B) (A : Subgroup B) [A.Normal]
    (hA : A ≤ center B) {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (φ : B ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : n = 2 ∧ Nat.card F = 5 := by
  have hF2 : Nat.card F ≠ 2 := fun h => absurd (h ▸ hF) (by decide)
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl (Or.inr hF2) (Or.inr hF3)).1
  let f' : Matrix.SpecialLinearGroup (Fin 2) F →* B := f.codRestrict B fun x => hB ▸ ⟨x, rfl⟩
  have hf'ker : f'.ker = f.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hf'surj : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    rw [← hB] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  set A' := A.comap f' with hA'
  have hA'sc : A' ≤ LinearFlag.scalars 2 F := by
    intro x hx
    rw [LinearFlag.scalars_eq_center]
    exact OddSelector.mem_center_of_map_mem_center f' (hf'ker ▸ hf) (hA hx)
  let π : Matrix.SpecialLinearGroup (Fin 2) F →* B ⧸ A := (QuotientGroup.mk' A).comp f'
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective A).comp hf'surj
  have hπker : π.ker = A' := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hA', mem_comap]
  let φ' : Matrix.SpecialLinearGroup (Fin 2) F ⧸ A' ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    ((QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)).trans φ
  obtain ⟨hn2, h5, -⟩ := SteinbergBT.linear_scalar_quotient_SL2 hF hn K hK le_rfl A' hA'sc φ'
  exact ⟨hn2, h5⟩

end Groups

section HighDimension

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs

theorem exists_sp_four_pow_four {k : Type} [Field k] (h2 : (2 : k) ≠ 0) :
    ∃ g : StatedSp 2 k, g ^ 4 = 1 ∧ g ^ 2 ∉ center (StatedSp 2 k) := by
  set M := SteinbergBT.spRot (F := k) (0 : Fin 2)
  have hM : Mᵀ * gram k 2 * M = gram k 2 := by
    rw [gram_eq_neg_J, Matrix.mul_neg, Matrix.neg_mul, SteinbergBT.spRot_symplectic]
  set g := ofSymplecticMat M hM
  have hgval : ((g : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) = M := rfl
  have hM2 := SteinbergBT.spRot_mul_self (F := k) (0 : Fin 2)
  have hsq : (((g ^ 2 : StatedSp 2 k) : GL (Fin 2 ⊕ Fin 2) k) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) = M * M := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hgval, sq]
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hsq,
      hM2, sq, SteinbergBT.spRot_sq_mul_self]
    rfl
  · intro hc
    rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf] at hc
    obtain ⟨c, hc⟩ := hc
    have h1 : ((GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c : GL (Fin 2 ⊕ Fin 2) k) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) = M * M := by
      rw [hc, hsq]
    rw [hM2, GeneralLinearGroup.coe_scalar] at h1
    have h00 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    have h11 := congrFun (congrFun h1 (Sum.inl 1)) (Sum.inl 1)
    rw [SteinbergBT.spRot_sq_apply_left] at h00
    rw [SteinbergBT.spRot_sq_apply_other (by decide)] at h11
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00 h11
    apply h2
    linear_combination h00 - h11

theorem exists_commutator_pow_four_aux {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (q : QuadraticForm k V)
    (hq : q.polarBilin.Nondegenerate) (hdim : 5 ≤ Module.finrank k V) :
    ∃ x ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup q), x ^ 4 = 1 ∧
      ¬ ∃ c : k, ∀ v, ((x ^ 2 : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = c • v := by
  have h2 := SteinbergBT.two_ne_zero_of_odd_card hk
  obtain ⟨τ, hτ⟩ := OddSelector.exists_sp_four_hom hk q hq hdim
  obtain ⟨g, hg4, hg2⟩ := exists_sp_four_pow_four h2
  have : Group.IsPerfect (StatedSp 2 k) := OddSelector.isPerfect_statedSp le_rfl hk
  refine ⟨τ g, OddSelector.map_mem_commutator_of_isPerfect τ g, by rw [← map_pow, hg4, map_one],
    ?_⟩
  rintro ⟨c, hc⟩
  apply hg2
  apply hτ
  intro y
  rw [map_pow]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  change ((τ y : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V)
      (((τ g ^ 2 : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v) =
    ((τ g ^ 2 : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V)
      (((τ y : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v)
  rw [hc, hc, map_smul]

theorem nondegenerate_comp {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (q : QuadraticForm k V) (hq : q.polarBilin.Nondegenerate)
    (ψ : W ≃ₗ[k] V) : (q.comp (ψ : W →ₗ[k] V)).polarBilin.Nondegenerate := by
  have hpol : ∀ x y, (q.comp (ψ : W →ₗ[k] V)).polarBilin x y = q.polarBilin (ψ x) (ψ y) := by
    intro x y
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.comp_apply,
      LinearEquiv.coe_coe, map_add]
  refine ⟨fun x hx => ψ.injective ?_, fun y hy => ψ.injective ?_⟩
  · rw [map_zero]
    refine hq.1 (ψ x) fun z => ?_
    have := hx (ψ.symm z)
    rwa [hpol, LinearEquiv.apply_symm_apply] at this
  · rw [map_zero]
    refine hq.2 (ψ y) fun z => ?_
    have := hy (ψ.symm z)
    rwa [hpol, LinearEquiv.apply_symm_apply] at this

theorem exists_commutator_pow_four {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (q : QuadraticForm k V)
    (hq : q.polarBilin.Nondegenerate) (hdim : 5 ≤ Module.finrank k V) :
    CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup q)) ∧
      ∃ x ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup q), x ^ 4 = 1 ∧
        ¬ ∃ c : k, ∀ v,
          ((x ^ 2 : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = c • v := by
  set ψ : V ≃ₗ[k] (Fin (Module.finrank k V) → k) := (Module.finBasis k V).equivFun
  set q' : QuadraticForm k (Fin (Module.finrank k V) → k) := q.comp (ψ.symm : _ →ₗ[k] V)
    with hq'def
  have hψ : ∀ v, q v = ((1 : kˣ) : k) * q' (ψ v) := fun v => by
    rw [Units.val_one, one_mul, hq'def, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  set e := CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q q' 1 ψ hψ with he
  have hq' : q'.polarBilin.Nondegenerate := nondegenerate_comp q hq ψ.symm
  have hdim' : 5 ≤ Module.finrank k (Fin (Module.finrank k V) → k) := by
    rwa [Module.finrank_fin_fun]
  have hQ' := OddSelector.commutator_orthogonalGroup_quasisimple hk q' hq' hdim'
  obtain ⟨x', hx', hx'4, hx'2⟩ := exists_commutator_pow_four_aux hk q' hq' hdim'
  have hcomm := commutator_eq_map_symm e
  refine ⟨?_, e.symm x', ?_, by rw [← map_pow, hx'4, map_one], ?_⟩
  · rw [hcomm]
    exact isQuasisimple_map_mulEquiv e.symm hQ'
  · rw [hcomm]
    exact ⟨x', hx', rfl⟩
  · rintro ⟨c, hc⟩
    apply hx'2
    refine ⟨c, fun w => ψ.symm.injective ?_⟩
    have h1 := hc (ψ.symm w)
    rw [← map_pow, he, CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv_symm_apply,
      LinearEquiv.apply_symm_apply] at h1
    rw [h1, map_smul]

theorem high_dimension_false {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (q : QuadraticForm k V)
    (hq : q.polarBilin.Nondegenerate) (hdim : 5 ≤ Module.finrank k V)
    {B : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)} (hB : CFSG.IsComponent B)
    (A : Subgroup B) [A.Normal]
    (hA : ∀ a ∈ A, ∃ c : k, ∀ v,
      ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = c • v)
    {n : ℕ} (hn : 1 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (φ : B ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  obtain ⟨hQ, x, hx, hx4, hx2⟩ := exists_commutator_pow_four hk q hq hdim
  have hxB : x ∈ B := (CatLeafProof.eq_commutator_of_isComponent hQ hB) ▸ hx
  refine false_of_pow_four (SteinbergBT.two_eq_zero_of_card hn hK) φ
    (x := ⟨x, hxB⟩) (Subtype.ext ?_) fun hmem => hx2 (hA _ hmem)
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact hx4

end HighDimension

section Three

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

@[expose] def traceZeroModelAction (q : QuadraticForm k V) (d : kˣ)
    (ψ : V ≃ₗ[k] traceZeroSubmodule k) (hψ : ∀ v, q v = (d : k) * traceZeroForm k (ψ v)) :
    Matrix.SpecialLinearGroup (Fin 2) k →* TauCeti.QuadraticMap.orthogonalGroup q :=
  (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q (traceZeroForm k) d ψ
    hψ).symm.toMonoidHom.comp (traceZeroOrthogonalAction.comp SpecialLinearGroup.toGL)

theorem traceZeroModelAction_apply (q : QuadraticForm k V) (d : kˣ)
    (ψ : V ≃ₗ[k] traceZeroSubmodule k) (hψ : ∀ v, q v = (d : k) * traceZeroForm k (ψ v))
    (M : Matrix.SpecialLinearGroup (Fin 2) k) (v : V) :
    ((ψ (((traceZeroModelAction q d ψ hψ M : TauCeti.QuadraticMap.orthogonalGroup q) :
      V ≃ₗ[k] V) v) : traceZeroSubmodule k) : Matrix (Fin 2) (Fin 2) k) =
      (M : Matrix (Fin 2) (Fin 2) k) * (ψ v : Matrix (Fin 2) (Fin 2) k) *
        ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  change ((ψ ((((CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q
    (traceZeroForm k) d ψ hψ).symm (traceZeroOrthogonalAction (SpecialLinearGroup.toGL M)) :
      TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v) : traceZeroSubmodule k) :
        Matrix (Fin 2) (Fin 2) k) = _
  rw [CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv_symm_apply,
    LinearEquiv.apply_symm_apply, traceZeroOrthogonalAction_val, ← map_inv]
  rfl

theorem traceZeroModelAction_ker (q : QuadraticForm k V) (d : kˣ)
    (ψ : V ≃ₗ[k] traceZeroSubmodule k) (hψ : ∀ v, q v = (d : k) * traceZeroForm k (ψ v)) :
    (traceZeroModelAction q d ψ hψ).ker = LinearFlag.scalars 2 k := by
  ext M
  rw [MonoidHom.mem_ker, LinearFlag.mem_scalars]
  change (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q (traceZeroForm k) d
    ψ hψ).symm (traceZeroOrthogonalAction (SpecialLinearGroup.toGL M)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, traceZeroOrthogonalAction_eq_one_iff]
  constructor
  · rintro ⟨c, hc⟩
    have hdet := congrArg GeneralLinearGroup.det hc
    rw [GeneralLinearGroup.det_scalar, SpecialLinearGroup.coeToGL_det, Fintype.card_fin] at hdet
    refine ⟨c, hdet, ?_⟩
    have h1 := congrArg (fun g : GL (Fin 2) k => (g : Matrix (Fin 2) (Fin 2) k)) hc
    simp only [GeneralLinearGroup.coe_scalar] at h1
    exact h1.symm
  · rintro ⟨c, -, hc⟩
    refine ⟨c, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar]
    exact hc.symm

theorem mem_traceZeroModelAction_range (q : QuadraticForm k V) (d : kˣ)
    (ψ : V ≃ₗ[k] traceZeroSubmodule k) (hψ : ∀ v, q v = (d : k) * traceZeroForm k (ψ v))
    (g : TauCeti.QuadraticMap.orthogonalGroup q) :
    g ∈ (traceZeroModelAction q d ψ hψ).range ↔
      ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
        ((ψ ((g : V ≃ₗ[k] V) v) : traceZeroSubmodule k) : Matrix (Fin 2) (Fin 2) k) =
          (M : Matrix (Fin 2) (Fin 2) k) * (ψ v : Matrix (Fin 2) (Fin 2) k) *
            ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨M, traceZeroModelAction_apply q d ψ hψ M⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, Subtype.ext (LinearEquiv.ext fun v => ψ.injective (Subtype.ext ?_))⟩
    rw [traceZeroModelAction_apply, hM]

theorem traceZeroModelAction_range [Finite k] (hk : Odd (Nat.card k)) (hk3 : Nat.card k ≠ 3)
    (q : QuadraticForm k V) (d : kˣ)
    (ψ : V ≃ₗ[k] traceZeroSubmodule k) (hψ : ∀ v, q v = (d : k) * traceZeroForm k (ψ v)) :
    (traceZeroModelAction q d ψ hψ).range =
      commutator (TauCeti.QuadraticMap.orthogonalGroup q) := by
  rw [commutator_eq_map_symm (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q
    (traceZeroForm k) d ψ hψ), traceZero_commutator_eq hk hk3, traceZeroModelAction,
    MonoidHom.range_comp]
  rfl

end Three

theorem three_case {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (q : QuadraticForm k V)
    (hq : q.polarBilin.Nondegenerate) (hdim : Module.finrank k V = 3)
    {B : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)} (hB : CFSG.IsComponent B)
    (A : Subgroup B) [A.Normal]
    (hA : ∀ a ∈ A, ∃ c : k, ∀ v,
      ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = c • v)
    {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (φ : B ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    n = 2 ∧ Nat.card k = 5 ∧ A = ⊥ ∧ Nonempty (B ≃* LinearFlag.projectiveSL 2 k) ∧
      ∀ (d : kˣ) (ψ : V ≃ₗ[k] traceZeroSubmodule k),
        (∀ v, q v = (d : k) * traceZeroForm k (ψ v)) →
        ∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ B ↔
          ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
            ((ψ ((g : V ≃ₗ[k] V) v) : traceZeroSubmodule k) : Matrix (Fin 2) (Fin 2) k) =
              (M : Matrix (Fin 2) (Fin 2) k) * (ψ v : Matrix (Fin 2) (Fin 2) k) *
                ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  have h2 := SteinbergBT.two_ne_zero_of_odd_card hk
  have hk3 : Nat.card k ≠ 3 := by
    intro h3
    have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
      hk q hq hdim).2 h3).1
    exact CatLeafProof.not_isComponent_of_isSolvable hB
  obtain ⟨-, -, -, -, -, -, hQ, -⟩ := orthogonal_three_derived hk hk3 q hq hdim
  have hBeq := CatLeafProof.eq_commutator_of_isComponent hQ hB
  obtain ⟨d₀, ψ₀, -, hψ₀, -, -⟩ :=
    CatalogueBOrthogonalThreeSimilarity.exists_trace_zero_similarity_and_orthogonal_equiv hk q hq
      hdim
  set f := traceZeroModelAction q d₀ ψ₀ hψ₀
  have hfB : f.range = B := by
    rw [hBeq]
    exact traceZeroModelAction_range hk hk3 q d₀ ψ₀ hψ₀
  have hker : f.ker = LinearFlag.scalars 2 k := traceZeroModelAction_ker q d₀ ψ₀ hψ₀
  have hAc : A ≤ center B := fun a ha => by
    obtain ⟨c, hc⟩ := hA a ha
    exact mem_center_of_smul hc
  obtain ⟨hn2, h5⟩ := cover_scalar_quotient hk hk3 f (hker ▸ LinearFlag.scalars_le_center 2 k)
    hfB A hAc hn K hK φ
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hAbot : A = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall A).mpr fun a ha => ?_
    obtain ⟨c, hc⟩ := hA a ha
    have hdet := det_eq_one_of_mem_commutator
      (show (a : TauCeti.QuadraticMap.orthogonalGroup q) ∈
        commutator (TauCeti.QuadraticMap.orthogonalGroup q) from hBeq ▸ a.2)
    have hlin : (((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) : V →ₗ[k] V) =
        c • LinearMap.id := LinearMap.ext fun v => hc v
    have hc3 : c ^ 3 = 1 := by
      have h1 := congrArg Units.val hdet
      rw [LinearEquiv.coe_det, hlin, LinearMap.det_smul, LinearMap.det_id, mul_one, hdim,
        Units.val_one] at h1
      exact h1
    rcases eq_one_or_eq_neg_one_of_smul q hq hc with h1 | h1
    · refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))
      rw [hc, h1, one_smul]
      rfl
    · exfalso
      rw [h1] at hc3
      apply h2
      linear_combination -hc3
  refine ⟨hn2, h5, hAbot, ⟨(MulEquiv.subgroupCongr hfB.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))⟩, fun d ψ hψ g => ?_⟩
  rw [hBeq, ← traceZeroModelAction_range hk hk3 q d ψ hψ, mem_traceZeroModelAction_range]

section SplitFour

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

@[expose] def determinantModelLeft (q : QuadraticForm k V) (d : kˣ)
    (ψ : V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) (hψ : ∀ v, q v = (d : k) * determinantForm k (ψ v)) :
    Matrix.SpecialLinearGroup (Fin 2) k →* TauCeti.QuadraticMap.orthogonalGroup q :=
  (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q (determinantForm k) d ψ
    hψ).symm.toMonoidHom.comp (specialRho.comp (MonoidHom.inl _ _))

@[expose] def determinantModelRight (q : QuadraticForm k V) (d : kˣ)
    (ψ : V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) (hψ : ∀ v, q v = (d : k) * determinantForm k (ψ v)) :
    Matrix.SpecialLinearGroup (Fin 2) k →* TauCeti.QuadraticMap.orthogonalGroup q :=
  (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q (determinantForm k) d ψ
    hψ).symm.toMonoidHom.comp (specialRho.comp (MonoidHom.inr _ _))

variable (q : QuadraticForm k V) (d : kˣ) (ψ : V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k)
  (hψ : ∀ v, q v = (d : k) * determinantForm k (ψ v))

theorem determinantModelLeft_apply (M : Matrix.SpecialLinearGroup (Fin 2) k) (v : V) :
    ψ (((determinantModelLeft q d ψ hψ M : TauCeti.QuadraticMap.orthogonalGroup q) :
      V ≃ₗ[k] V) v) = (M : Matrix (Fin 2) (Fin 2) k) * ψ v := by
  change ψ ((((CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q
    (determinantForm k) d ψ hψ).symm (specialRho (MonoidHom.inl _ _ M)) :
      TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v) = _
  rw [CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv_symm_apply,
    LinearEquiv.apply_symm_apply, specialRho_apply]
  simp

theorem determinantModelRight_apply (M : Matrix.SpecialLinearGroup (Fin 2) k) (v : V) :
    ψ (((determinantModelRight q d ψ hψ M : TauCeti.QuadraticMap.orthogonalGroup q) :
      V ≃ₗ[k] V) v) =
      ψ v * ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  change ψ ((((CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q
    (determinantForm k) d ψ hψ).symm (specialRho (MonoidHom.inr _ _ M)) :
      TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v) = _
  rw [CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv_symm_apply,
    LinearEquiv.apply_symm_apply, specialRho_apply]
  simp

theorem determinantModelLeft_injective : Function.Injective (determinantModelLeft q d ψ hψ) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  change (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q (determinantForm k) d ψ
    hψ).symm (specialRho (MonoidHom.inl _ _ M)) = 1 at hM
  rw [MulEquiv.map_eq_one_iff, specialRho_eq_one_iff] at hM
  obtain ⟨c, -, h1, h2⟩ := hM
  apply SpecialLinearGroup.toGL_injective
  rw [map_one]
  simp only [MonoidHom.inl_apply, map_one] at h1 h2
  rw [h1, ← h2]

theorem determinantModelRight_injective :
    Function.Injective (determinantModelRight q d ψ hψ) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  change (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q (determinantForm k) d ψ
    hψ).symm (specialRho (MonoidHom.inr _ _ M)) = 1 at hM
  rw [MulEquiv.map_eq_one_iff, specialRho_eq_one_iff] at hM
  obtain ⟨c, -, h1, h2⟩ := hM
  apply SpecialLinearGroup.toGL_injective
  rw [map_one]
  simp only [MonoidHom.inr_apply, map_one] at h1 h2
  rw [h2, ← h1]

theorem mem_determinantModelLeft_range (g : TauCeti.QuadraticMap.orthogonalGroup q) :
    g ∈ (determinantModelLeft q d ψ hψ).range ↔
      ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
        ψ ((g : V ≃ₗ[k] V) v) = (M : Matrix (Fin 2) (Fin 2) k) * ψ v := by
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨M, determinantModelLeft_apply q d ψ hψ M⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, Subtype.ext (LinearEquiv.ext fun v => ψ.injective ?_)⟩
    rw [determinantModelLeft_apply, hM]

theorem mem_determinantModelRight_range (g : TauCeti.QuadraticMap.orthogonalGroup q) :
    g ∈ (determinantModelRight q d ψ hψ).range ↔
      ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
        ψ ((g : V ≃ₗ[k] V) v) = ψ v * (M : Matrix (Fin 2) (Fin 2) k) := by
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨M⁻¹, determinantModelRight_apply q d ψ hψ M⟩
  · rintro ⟨M, hM⟩
    refine ⟨M⁻¹, Subtype.ext (LinearEquiv.ext fun v => ψ.injective ?_)⟩
    rw [determinantModelRight_apply, hM, inv_inv]

theorem determinantModelLeft_range :
    (determinantModelLeft q d ψ hψ).range =
      (determinantLeftFactor k).map (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv
        q (determinantForm k) d ψ hψ).symm.toMonoidHom := by
  rw [determinantModelLeft, MonoidHom.range_comp]
  rfl

theorem determinantModelRight_range :
    (determinantModelRight q d ψ hψ).range =
      (determinantRightFactor k).map (CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv
        q (determinantForm k) d ψ hψ).symm.toMonoidHom := by
  rw [determinantModelRight, MonoidHom.range_comp]
  rfl

theorem determinantModel_commute {x y : TauCeti.QuadraticMap.orthogonalGroup q}
    (hx : x ∈ (determinantModelLeft q d ψ hψ).range)
    (hy : y ∈ (determinantModelRight q d ψ hψ).range) : x * y = y * x := by
  rw [determinantModelLeft_range] at hx
  rw [determinantModelRight_range] at hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← map_mul, ← map_mul, determinantFactors_commute ha hb]

theorem determinantModelLeft_neg_one (v : V) :
    ((determinantModelLeft q d ψ hψ (SteinbergBT.negOneSL2 k) :
      TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = -v := by
  apply ψ.injective
  rw [determinantModelLeft_apply, map_neg]
  change (-1 : Matrix (Fin 2) (Fin 2) k) * ψ v = _
  rw [neg_one_mul]

theorem determinantModelRight_neg_one (v : V) :
    ((determinantModelRight q d ψ hψ (SteinbergBT.negOneSL2 k) :
      TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = -v := by
  apply ψ.injective
  rw [determinantModelRight_apply, map_neg]
  have h1 : ((SteinbergBT.negOneSL2 k)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) =
      SteinbergBT.negOneSL2 k := by
    apply inv_eq_of_mul_eq_one_right
    ext i j
    change ((-1 : Matrix (Fin 2) (Fin 2) k) * -1) i j = (1 : Matrix (Fin 2) (Fin 2) k) i j
    rw [neg_one_mul, neg_neg]
  rw [h1]
  change ψ v * (-1 : Matrix (Fin 2) (Fin 2) k) = _
  rw [mul_neg_one]

variable [Finite k]

theorem determinantModel_structure (hk2 : Nat.card k ≠ 2) (hk3 : Nat.card k ≠ 3) :
    commutator (TauCeti.QuadraticMap.orthogonalGroup q) =
        (determinantModelLeft q d ψ hψ).range ⊔ (determinantModelRight q d ψ hψ).range ∧
      CFSG.IsQuasisimple (determinantModelLeft q d ψ hψ).range ∧
      CFSG.IsQuasisimple (determinantModelRight q d ψ hψ).range ∧
      ((determinantModelLeft q d ψ hψ).range.subgroupOf
        (commutator (TauCeti.QuadraticMap.orthogonalGroup q))).Normal ∧
      ((determinantModelRight q d ψ hψ).range.subgroupOf
        (commutator (TauCeti.QuadraticMap.orthogonalGroup q))).Normal := by
  set e := CatalogueBOrthogonalThreeSimilarity.similarityOrthogonalEquiv q (determinantForm k) d ψ
    hψ with he
  have hcomm : commutator (TauCeti.QuadraticMap.orthogonalGroup q) =
      (specialImage k).map e.symm.toMonoidHom := by
    rw [commutator_eq_map_symm e, determinant_commutator_eq hk2 hk3]
  rw [determinantModelLeft_range, determinantModelRight_range, ← he, hcomm]
  refine ⟨by rw [← Subgroup.map_sup, determinantFactors_sup],
    isQuasisimple_map_mulEquiv e.symm (determinantLeftFactor_quasisimple hk2 hk3),
    isQuasisimple_map_mulEquiv e.symm (determinantRightFactor_quasisimple hk2 hk3),
    normal_subgroupOf_map_mulEquiv e.symm determinantLeftFactor_le determinantLeftFactor_normal,
    normal_subgroupOf_map_mulEquiv e.symm determinantRightFactor_le determinantRightFactor_normal⟩

theorem determinantModel_components [FiniteDimensional k V] (hk2 : Nat.card k ≠ 2)
    (hk3 : Nat.card k ≠ 3) :
    CFSG.IsComponent (determinantModelLeft q d ψ hψ).range ∧
      CFSG.IsComponent (determinantModelRight q d ψ hψ).range ∧
      (determinantModelLeft q d ψ hψ).range ≠ (determinantModelRight q d ψ hψ).range ∧
      ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q), CFSG.IsComponent L →
        L = (determinantModelLeft q d ψ hψ).range ∨ L = (determinantModelRight q d ψ hψ).range := by
  obtain ⟨hsup, hqL, hqR, hnL, hnR⟩ := determinantModel_structure q d ψ hψ hk2 hk3
  have hLc : (determinantModelLeft q d ψ hψ).range ≤
      commutator (TauCeti.QuadraticMap.orthogonalGroup q) := hsup ▸ le_sup_left
  have hRc : (determinantModelRight q d ψ hψ).range ≤
      commutator (TauCeti.QuadraticMap.orthogonalGroup q) := hsup ▸ le_sup_right
  refine ⟨⟨hqL, Subgroup.IsSubnormal.step _ _ hLc (Subgroup.Normal.isSubnormal inferInstance)
      hnL⟩, ⟨hqR, Subgroup.IsSubnormal.step _ _ hRc (Subgroup.Normal.isSubnormal inferInstance)
      hnR⟩, fun hLR => ?_, fun L hL => CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hqL hqR
      hnL hnR hL (le_commutator_of_isComponent hL)⟩
  obtain ⟨a, b, hab⟩ := CatLeafProof.exists_mul_ne_of_isQuasisimple hqL (MulEquiv.refl _)
  apply hab
  apply Subtype.ext
  exact determinantModel_commute q d ψ hψ a.2 (hLR ▸ b.2)

end SplitFour

theorem card_scalarIsometries_subgroupOf {k : Type*} [Field k] {V : Type*} [AddCommGroup V]
    [Module k V] (q : QuadraticForm k V) (hq : q.polarBilin.Nondegenerate) [Nontrivial V]
    (h2 : (2 : k) ≠ 0) {T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)}
    {z : TauCeti.QuadraticMap.orthogonalGroup q} (hzT : z ∈ T)
    (hz : ∀ v, (z : V ≃ₗ[k] V) v = -v) :
    Nat.card ((scalarIsometries q).subgroupOf T) = 2 := by
  have hz1 : z ≠ 1 :=
    SteinbergBT.ne_one_of_forall_neg (TauCeti.QuadraticMap.orthogonalGroup q).subtype h2 hz
  have hzs : (⟨z, hzT⟩ : T) ∈ (scalarIsometries q).subgroupOf T :=
    (mem_scalarIsometries_iff q hq z).mpr (Or.inr hz)
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨⟨z, hzT⟩, hzs⟩, fun h => hz1 ?_, ?_⟩
  · exact (congrArg (fun x : (scalarIsometries q).subgroupOf T =>
      ((x : T) : TauCeti.QuadraticMap.orthogonalGroup q)) h).symm
  · ext ⟨⟨t, htT⟩, ht⟩
    simp only [Set.mem_univ, iff_true, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (mem_scalarIsometries_iff q hq t).mp ht with h1 | h1
    · left
      exact Subtype.ext (Subtype.ext (Subtype.ext (LinearEquiv.ext h1)))
    · right
      exact Subtype.ext (Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => (h1 v).trans
        (hz v).symm)))

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit in
theorem split_four_case {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (q : QuadraticForm k V)
    (hq : q.polarBilin.Nondegenerate) (hdim : Module.finrank k V = 4)
    (hS : ∃ S : Submodule k V, Module.finrank k S = 2 ∧ ∀ x ∈ S, q x = 0)
    {B : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)} (hB : CFSG.IsComponent B)
    (A : Subgroup B) [A.Normal]
    (hA : ∀ a ∈ A, ∃ c : k, ∀ v,
      ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = c • v)
    {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (φ : B ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    n = 2 ∧ Nat.card k = 5 ∧ Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) k) ∧
      Nat.card A = 2 ∧
      (∀ a : B, a ∈ A ↔ (∀ v, ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = v) ∨
        ∀ v, ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = -v) ∧
      ∃ T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q),
        (∀ x ∈ B, ∀ y ∈ T, x * y = y * x) ∧ Group.IsPerfect T ∧
        T ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup q) ∧
        Nat.card (T ⧸ (scalarIsometries q).subgroupOf T) = 60 ∧
        ∀ (d : kˣ) (ψ : V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k), (∀ v, q v = (d : k) * (ψ v).det) →
          ((∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ B ↔
              ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                ψ ((g : V ≃ₗ[k] V) v) = (M : Matrix (Fin 2) (Fin 2) k) * ψ v) ∧
            ∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ T ↔
              ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                ψ ((g : V ≃ₗ[k] V) v) = ψ v * (M : Matrix (Fin 2) (Fin 2) k)) ∨
          ((∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ B ↔
              ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                ψ ((g : V ≃ₗ[k] V) v) = ψ v * (M : Matrix (Fin 2) (Fin 2) k)) ∧
            ∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ T ↔
              ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                ψ ((g : V ≃ₗ[k] V) v) = (M : Matrix (Fin 2) (Fin 2) k) * ψ v) := by
  have h2 := SteinbergBT.two_ne_zero_of_odd_card hk
  have hk2 : Nat.card k ≠ 2 := fun h => absurd (h ▸ hk) (by decide)
  obtain ⟨S, hSdim, hSq⟩ := hS
  have hk3 : Nat.card k ≠ 3 := by
    intro h3
    have := CatalogueBOrthogonalFourSplitComponents.orthogonal_four_split_three_solvable h3 q hq
      hdim S hSdim hSq
    exact CatLeafProof.not_isComponent_of_isSolvable hB
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hconv : ∀ (d : kˣ) (ψ : V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k),
      (∀ v, q v = (d : k) * (ψ v).det) → ∀ v, q v = (d : k) * determinantForm k (ψ v) :=
    fun d ψ h v => by rw [determinantForm_apply]; exact h v
  obtain ⟨ψ₀, -, hψ₀, -, -⟩ := split_four_determinant_form_isometry q hq hdim S hSdim hSq
  have hψ₀' := hconv 1 ψ₀ fun v => by rw [Units.val_one, one_mul]; exact hψ₀ v
  obtain ⟨hcL, hcR, hLR, hall⟩ := determinantModel_components q 1 ψ₀ hψ₀' hk2 hk3
  obtain ⟨hsup, -, -, -, -⟩ := determinantModel_structure q 1 ψ₀ hψ₀' hk2 hk3
  obtain ⟨fB, fT, hfBi, hfTi, hfB, hcT, hTB, hcomm, hTc, hnegB, hnegT⟩ :
      ∃ fB fT : Matrix.SpecialLinearGroup (Fin 2) k →* TauCeti.QuadraticMap.orthogonalGroup q,
        Function.Injective fB ∧ Function.Injective fT ∧ fB.range = B ∧
        CFSG.IsComponent fT.range ∧ fT.range ≠ B ∧ (∀ x ∈ B, ∀ y ∈ fT.range, x * y = y * x) ∧
        fT.range ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup q) ∧
        (∀ v, ((fB (SteinbergBT.negOneSL2 k) : TauCeti.QuadraticMap.orthogonalGroup q) :
          V ≃ₗ[k] V) v = -v) ∧
        ∀ v, ((fT (SteinbergBT.negOneSL2 k) : TauCeti.QuadraticMap.orthogonalGroup q) :
          V ≃ₗ[k] V) v = -v := by
    rcases hall B hB with hBL | hBR
    · exact ⟨_, _, determinantModelLeft_injective q 1 ψ₀ hψ₀',
        determinantModelRight_injective q 1 ψ₀ hψ₀', hBL.symm, hcR,
        fun h => hLR (hBL.symm.trans h.symm), fun x hx y hy =>
          determinantModel_commute q 1 ψ₀ hψ₀' (hBL ▸ hx) hy,
        hsup ▸ le_sup_right, determinantModelLeft_neg_one q 1 ψ₀ hψ₀',
        determinantModelRight_neg_one q 1 ψ₀ hψ₀'⟩
    · exact ⟨_, _, determinantModelRight_injective q 1 ψ₀ hψ₀',
        determinantModelLeft_injective q 1 ψ₀ hψ₀', hBR.symm, hcL,
        fun h => hLR (h.trans hBR), fun x hx y hy =>
          (determinantModel_commute q 1 ψ₀ hψ₀' hy (hBR ▸ hx)).symm,
        hsup ▸ le_sup_left, determinantModelRight_neg_one q 1 ψ₀ hψ₀',
        determinantModelLeft_neg_one q 1 ψ₀ hψ₀'⟩
  let eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) k :=
    (MulEquiv.subgroupCongr hfB.symm).trans (MonoidHom.ofInjective hfBi).symm
  have hAc : A ≤ center B := fun a ha => by
    obtain ⟨c, hc⟩ := hA a ha
    exact mem_center_of_smul hc
  obtain ⟨hn2, h5, hAeq, hc2⟩ := SteinbergBT.sl2_odd_scalar_quotient_core hk eB A hAc hn K hK φ
  let ι : B →* (V ≃ₗ[k] V) := (TauCeti.QuadraticMap.orthogonalGroup q).subtype.comp B.subtype
  have hι : Function.Injective ι :=
    (TauCeti.QuadraticMap.orthogonalGroup q).subtype_injective.comp B.subtype_injective
  let z : B := ⟨fB (SteinbergBT.negOneSL2 k), hfB ▸ ⟨_, rfl⟩⟩
  have hz : ∀ v, ι z v = -v := hnegB
  have hAmem := SteinbergBT.mem_iff_of_center_card_two ι hι A hAeq hc2 hz
    (SteinbergBT.ne_one_of_forall_neg ι h2 hz)
  refine ⟨hn2, h5, ⟨eB⟩, by rw [hAeq, hc2], hAmem, fT.range, hcomm, hcT.1.1, hTc, ?_, ?_⟩
  ·
    have hTcard : Nat.card fT.range = 120 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hfTi).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h5]
      norm_num
    have hScard := card_scalarIsometries_subgroupOf q hq h2 (T := fT.range) ⟨_, rfl⟩ hnegT
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((scalarIsometries q).subgroupOf fT.range)
    rw [hTcard, hScard] at h
    omega
  ·
    intro d ψ hψ
    obtain ⟨-, -, -, hall'⟩ := determinantModel_components q d ψ (hconv d ψ hψ) hk2 hk3
    rcases hall' B hB with hB1 | hB1 <;> rcases hall' _ hcT with hT1 | hT1
    · exact absurd (hT1.trans hB1.symm) hTB
    · left
      exact ⟨fun g => by rw [hB1, mem_determinantModelLeft_range],
        fun g => by rw [hT1, mem_determinantModelRight_range]⟩
    · right
      exact ⟨fun g => by rw [hB1, mem_determinantModelRight_range],
        fun g => by rw [hT1, mem_determinantModelLeft_range]⟩
    · exact absurd (hT1.trans hB1.symm) hTB

theorem nonsplit_four_false {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (q : QuadraticForm k V)
    (hq : q.polarBilin.Nondegenerate) (hdim : Module.finrank k V = 4)
    (hno : ¬ ∃ S : Submodule k V, Module.finrank k S = 2 ∧ ∀ x ∈ S, q x = 0)
    {B : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)} (hB : CFSG.IsComponent B)
    (A : Subgroup B) [A.Normal]
    (hA : ∀ a ∈ A, ∃ c : k, ∀ v,
      ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = c • v)
    {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (φ : B ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hk
  obtain ⟨δ, hns, -, -, e, -, -, hcomm, hQ, -⟩ := orthogonal_nonsplit_four_derived hk q hq hdim hno
  have : Fact (¬ IsSquare (δ : k)) := ⟨hns⟩
  have hBeq := CatLeafProof.eq_commutator_of_isComponent hQ hB
  let f := e.symm.toMonoidHom.comp (CatalogueBOrthogonalFourNonsplit.specialRho (δ : k) h2)
  have hf : f.ker ≤ center _ := fun x hx => by
    apply CatalogueBOrthogonalFourNonsplit.specialRho_kernel_le_center (δ : k) h2
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulEquiv.map_eq_one_iff e.symm).mp hx
  have hfB : f.range = B := by
    rw [hBeq, hcomm, MonoidHom.range_comp]
    rfl
  have hAc : A ≤ center B := fun a ha => by
    obtain ⟨c, hc⟩ := hA a ha
    exact mem_center_of_smul hc
  have hE := CatalogueBOrthogonalFourNonsplit.extension_card (δ : k)
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  have hEodd : Odd (Nat.card (CatalogueBOrthogonalFourNonsplit.extension (δ : k))) := by
    rw [hE]
    exact hk.pow
  have hE3 : Nat.card (CatalogueBOrthogonalFourNonsplit.extension (δ : k)) ≠ 3 := by
    rw [hE]
    intro h
    have : Nat.card k ≤ 1 := by nlinarith
    omega
  obtain ⟨-, h5⟩ := cover_scalar_quotient hEodd hE3 f hf hfB A hAc hn K hK φ
  rw [hE] at h5
  have h3 : Nat.card k ≤ 2 := by nlinarith
  have h4 : Nat.card k = 2 := by omega
  rw [h4] at h5
  norm_num at h5

end OddOrthogonalQuotient

open OddOrthogonalQuotient in
theorem odd_orthogonal_component_scalar_quotients_even_SL2_small_exceptions
    {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (q : QuadraticForm k V)
    (hq : q.polarBilin.Nondegenerate)
    {B : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q)} (hB : CFSG.IsComponent B)
    (A : Subgroup B) [A.Normal]
    (hA : ∀ a ∈ A, ∃ c : k, ∀ v,
      ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = c • v)
    {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (hBA : Nonempty (B ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    n = 2 ∧ Nat.card k = 5 ∧
      ((Module.finrank k V = 3 ∧ A = ⊥ ∧ Nonempty (B ≃* LinearFlag.projectiveSL 2 k) ∧
          ∀ (d : kˣ) (ψ : V ≃ₗ[k] traceZeroSubmodule k),
            (∀ v, q v = (d : k) * traceZeroForm k (ψ v)) →
            ∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ B ↔
              ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                ((ψ ((g : V ≃ₗ[k] V) v) : traceZeroSubmodule k) : Matrix (Fin 2) (Fin 2) k) =
                  (M : Matrix (Fin 2) (Fin 2) k) * (ψ v : Matrix (Fin 2) (Fin 2) k) *
                    ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) ∨
        (Module.finrank k V = 4 ∧
          (∃ S : Submodule k V, Module.finrank k S = 2 ∧ ∀ x ∈ S, q x = 0) ∧
          Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) k) ∧ Nat.card A = 2 ∧
          (∀ a : B, a ∈ A ↔
            (∀ v, ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = v) ∨
              ∀ v, ((a : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[k] V) v = -v) ∧
          ∃ T : Subgroup (TauCeti.QuadraticMap.orthogonalGroup q),
            (∀ x ∈ B, ∀ y ∈ T, x * y = y * x) ∧ Group.IsPerfect T ∧
            T ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup q) ∧
            Nat.card (T ⧸ (scalarIsometries q).subgroupOf T) = 60 ∧
            ∀ (d : kˣ) (ψ : V ≃ₗ[k] Matrix (Fin 2) (Fin 2) k),
              (∀ v, q v = (d : k) * (ψ v).det) →
              ((∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ B ↔
                  ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                    ψ ((g : V ≃ₗ[k] V) v) = (M : Matrix (Fin 2) (Fin 2) k) * ψ v) ∧
                ∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ T ↔
                  ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                    ψ ((g : V ≃ₗ[k] V) v) = ψ v * (M : Matrix (Fin 2) (Fin 2) k)) ∨
              ((∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ B ↔
                  ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                    ψ ((g : V ≃ₗ[k] V) v) = ψ v * (M : Matrix (Fin 2) (Fin 2) k)) ∧
                ∀ g : TauCeti.QuadraticMap.orthogonalGroup q, g ∈ T ↔
                  ∃ M : Matrix.SpecialLinearGroup (Fin 2) k, ∀ v,
                    ψ ((g : V ≃ₗ[k] V) v) = (M : Matrix (Fin 2) (Fin 2) k) * ψ v))) := by
  obtain ⟨φ⟩ := hBA
  have h2 := SteinbergBT.two_ne_zero_of_odd_card hk
  by_cases h5 : 5 ≤ Module.finrank k V
  · exact (high_dimension_false hk q hq h5 hB A hA (by omega) K hK φ).elim
  by_cases hsmall : Module.finrank k V ≤ 2
  · have := CatalogueBOrthogonal.orthogonal_small_solvable q h2 hq hsmall
    exact (CatLeafProof.not_isComponent_of_isSolvable hB).elim
  rcases (show Module.finrank k V = 3 ∨ Module.finrank k V = 4 by omega) with h3 | h4
  · obtain ⟨hn2, hk5, hAbot, hiso, hmodel⟩ := three_case hk q hq h3 hB A hA hn K hK φ
    exact ⟨hn2, hk5, Or.inl ⟨h3, hAbot, hiso, hmodel⟩⟩
  · by_cases hS : ∃ S : Submodule k V, Module.finrank k S = 2 ∧ ∀ x ∈ S, q x = 0
    · obtain ⟨hn2, hk5, hiso, hcard, hmem, T, hT⟩ :=
        split_four_case hk q hq h4 hS hB A hA hn K hK φ
      exact ⟨hn2, hk5, Or.inr ⟨h4, hS, hiso, hcard, hmem, T, hT⟩⟩
    · exact (nonsplit_four_false hk q hq h4 hS hB A hA hn K hK φ).elim

end CFSG.LocalAnalysis.SymplecticFourStandard
