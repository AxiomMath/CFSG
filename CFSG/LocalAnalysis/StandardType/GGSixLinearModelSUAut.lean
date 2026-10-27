module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSURank
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestFieldNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

namespace SUModel

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

noncomputable abbrev suEquivI (n : ℕ) : ↥(unitarySU 2 f K n) ≃* ↥(gramSU h (idGram K n)) :=
  MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)

@[expose] noncomputable def piI (n : ℕ) : ↥(unitarySU 2 f K n) →* primeFormP h (idGram K n) :=
  (QuotientGroup.mk' _).comp (suEquivI h n).toMonoidHom

theorem piI_apply (s : ↥(unitarySU 2 f K n)) :
    piI h n s = ((suEquivI h n s : ↥(gramSU h (idGram K n))) : primeFormP h (idGram K n)) :=
  rfl

theorem piI_surjective : Function.Surjective (piI h n) :=
  (QuotientGroup.mk'_surjective _).comp (suEquivI h n).surjective

theorem ker_piI (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    (piI h n).ker = Subgroup.center ↥(unitarySU 2 f K n) := by
  ext s
  rw [MonoidHom.mem_ker, piI, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    ← CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h isPrimeFormGram_idGram hn hq,
    Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hs t
    apply (suEquivI h n).injective
    rw [map_mul, map_mul]
    exact hs _
  · intro hs t
    obtain ⟨t', rfl⟩ := (suEquivI h n).surjective t
    rw [← map_mul, ← map_mul, hs t']

variable {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G}

@[expose] noncomputable def projEquivI (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    (hC : Subgroup.centralizer (φ.range : Set G) = ⊥) :
    primeFormP h (idGram K n) ≃* φ.range :=
  AutSt.modelEquiv φ (piI h n) (piI_surjective h)
    ((ker_piI h hn hq).trans (AutSt.ker_eq_center hker hC).symm)

theorem projEquivI_piI (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    (hC : Subgroup.centralizer (φ.range : Set G) = ⊥) (s : ↥(unitarySU 2 f K n)) :
    ((projEquivI h hn hq hker hC (piI h n s) : φ.range) : G) = φ s :=
  AutSt.modelEquiv_apply _ _ _ _ s

@[expose] noncomputable def autOfI (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    (hC : Subgroup.centralizer (φ.range : Set G) = ⊥) :
    Subgroup.normalizer (φ.range : Set G) →* MulAut (primeFormP h (idGram K n)) :=
  (MulAut.congr (projEquivI h hn hq hker hC)).symm.toMonoidHom.comp φ.range.normalizerMonoidHom

variable (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
  (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
  (hC : Subgroup.centralizer (φ.range : Set G) = ⊥)

include hn hq hker hC in
theorem autOfI_injective : Function.Injective (autOfI h hn hq hker hC) := by
  have hφ : Function.Injective φ.range.normalizerMonoidHom := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC, Subgroup.bot_subgroupOf]
  exact (MulAut.congr (projEquivI h hn hq hker hC)).symm.injective.comp hφ

include hn hq hker hC in
theorem autOfI_apply_piI {g : G} (hg : g ∈ Subgroup.normalizer (φ.range : Set G))
    (s s' : ↥(unitarySU 2 f K n)) (hs : g * φ s * g⁻¹ = φ s') :
    autOfI h hn hq hker hC ⟨g, hg⟩ (piI h n s) = piI h n s' := by
  change (projEquivI h hn hq hker hC).symm (φ.range.normalizerMonoidHom ⟨g, hg⟩
    (projEquivI h hn hq hker hC (piI h n s))) = piI h n s'
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [projEquivI_piI]
  change g * ((projEquivI h hn hq hker hC (piI h n s) : φ.range) : G) * g⁻¹ = φ s'
  rw [projEquivI_piI, hs]


omit hn hq hker hC

theorem semi_mem {A : GL (Fin n) K} (hA : A ∈ primeFormUnitary h (idGram K n)) (σ : K ≃+* K)
    (s : ↥(unitarySU 2 f K n)) :
    A * glAut σ (s : GL (Fin n) K) * A⁻¹ ∈ unitarySU 2 f K n := by
  have hs : (s : GL (Fin n) K) ∈ gramSU h (idGram K n) :=
    (SetLike.ext_iff.mp (unitarySU_eq_gramSU h n) _).mp s.2
  exact (SetLike.ext_iff.mp (unitarySU_eq_gramSU h n) _).mpr
    (conj_mem_gramSU h _ hA (glAut_mem_gramSU h isPrimeFormGram_idGram σ hs))

theorem glAut_mem_unitary {A : GL (Fin n) K} (hA : A ∈ primeFormUnitary h (idGram K n))
    (σ : K ≃+* K) : glAut σ A ∈ primeFormUnitary h (idGram K n) :=
  glAut_mem_primeFormUnitary h isPrimeFormGram_idGram σ hA

@[expose] def SemiActs (φ : ↥(unitarySU 2 f K n) →* G) (g : G) (A : GL (Fin n) K)
    (σ : K ≃+* K) : Prop :=
  A ∈ primeFormUnitary h (idGram K n) ∧ ∀ s s' : ↥(unitarySU 2 f K n),
    (s' : GL (Fin n) K) = A * glAut σ (s : GL (Fin n) K) * A⁻¹ → g * φ s * g⁻¹ = φ s'

variable {h}

theorem SemiActs.apply {g : G} {A : GL (Fin n) K} {σ : K ≃+* K} (hg : SemiActs h φ g A σ)
    (s : ↥(unitarySU 2 f K n)) : g * φ s * g⁻¹ = φ ⟨_, semi_mem h hg.1 σ s⟩ :=
  hg.2 s _ rfl

theorem semiActs_one (φ : ↥(unitarySU 2 f K n) →* G) : SemiActs h φ 1 1 1 := by
  refine ⟨(primeFormUnitary h _).one_mem, fun s s' hs' => ?_⟩
  have : s' = s := Subtype.ext (by rw [hs', map_one, MulAut.one_apply, one_mul, inv_one, mul_one])
  rw [this, one_mul, inv_one, mul_one]

theorem SemiActs.mul {g g' : G} {A B : GL (Fin n) K} {σ τ : K ≃+* K}
    (hg : SemiActs h φ g A σ) (hg' : SemiActs h φ g' B τ) :
    SemiActs h φ (g * g') (A * glAut σ B) (σ * τ) := by
  refine ⟨(primeFormUnitary h _).mul_mem hg.1 (glAut_mem_unitary h hg'.1 σ), fun s s' hs' => ?_⟩
  set t : ↥(unitarySU 2 f K n) := ⟨_, semi_mem h hg'.1 τ s⟩ with ht
  have e1 := hg'.2 s t rfl
  have e2 := hg.2 t s' (by
    rw [hs', ht, map_mul, MulAut.mul_apply]
    change A * glAut σ B * glAut σ (glAut τ (s : GL (Fin n) K)) * (A * glAut σ B)⁻¹ =
      A * glAut σ (B * glAut τ (s : GL (Fin n) K) * B⁻¹) * A⁻¹
    rw [map_mul, map_mul, map_inv]
    group)
  calc g * g' * φ s * (g * g')⁻¹ = g * (g' * φ s * g'⁻¹) * g⁻¹ := by group
    _ = φ s' := by rw [e1, e2]

theorem glAut_one_apply (X : GL (Fin n) K) : glAut (1 : K ≃+* K) X = X := by
  rw [map_one, MulAut.one_apply]

theorem semiActs_one_iff {g : G} {A : GL (Fin n) K} :
    SemiActs h φ g A 1 ↔ A ∈ primeFormUnitary h (idGram K n) ∧ (g, A) ∈ SUTorus.suPairs φ := by
  constructor
  · rintro ⟨hA, hg⟩
    refine ⟨hA, SUTorus.mem_normalizer_of_mem_primeFormUnitary h hA, fun u v hv => hg u v ?_⟩
    rw [hv, glAut_one_apply]
  · rintro ⟨hA, -, hg⟩
    exact ⟨hA, fun s s' hs' => hg s s' (by rw [hs', glAut_one_apply])⟩

theorem semiActs_of_frameActs {g : G} {τ : Fin n → Kˣ} (hg : SURep.GGFrameActs φ g τ) :
    SemiActs h φ g (CFSG.SectionRank.OddCover.diagHom n τ) 1 := by
  refine ⟨?_, fun s s' hs' => hg.2 s s' (by rw [hs', glAut_one_apply])⟩
  rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
  exact CFSG.RankThree.Classical2.diagHom_unitary h hg.1

theorem semi_inv_mem {A : GL (Fin n) K} (hA : A ∈ primeFormUnitary h (idGram K n)) (σ : K ≃+* K)
    (s : ↥(unitarySU 2 f K n)) :
    glAut σ⁻¹ (A⁻¹ * (s : GL (Fin n) K) * A) ∈ unitarySU 2 f K n := by
  have hB := glAut_mem_unitary h ((primeFormUnitary h (idGram K n)).inv_mem hA) σ⁻¹
  convert semi_mem h hB σ⁻¹ s using 1
  simp only [map_mul, map_inv, inv_inv]


theorem glAut_glAut_inv (σ : K ≃+* K) (X : GL (Fin n) K) : glAut σ (glAut σ⁻¹ X) = X := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem SemiActs.mem_normalizer {g : G} {A : GL (Fin n) K} {σ : K ≃+* K}
    (hg : SemiActs h φ g A σ) : g ∈ Subgroup.normalizer (φ.range : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, (hg.apply s).symm⟩
  · rintro ⟨s, hs⟩
    set t : ↥(unitarySU 2 f K n) := ⟨_, semi_inv_mem hg.1 σ s⟩ with ht
    have h1 := hg.2 t s (by
      rw [ht, glAut_glAut_inv]
      group)
    refine ⟨t, ?_⟩
    calc φ t = g⁻¹ * (g * φ t * g⁻¹) * g := by group
      _ = x := by rw [h1, hs]; group

variable (h) in
include hn hq hker hC in
theorem projEquivI_autOfI {g : G} (hg : g ∈ Subgroup.normalizer (φ.range : Set G))
    (x : primeFormP h (idGram K n)) :
    ((projEquivI h hn hq hker hC (autOfI h hn hq hker hC ⟨g, hg⟩ x) : φ.range) : G) =
      g * ((projEquivI h hn hq hker hC x : φ.range) : G) * g⁻¹ := by
  change ((projEquivI h hn hq hker hC ((projEquivI h hn hq hker hC).symm
    (φ.range.normalizerMonoidHom ⟨g, hg⟩ (projEquivI h hn hq hker hC x))) : φ.range) : G) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

variable (h) in
theorem conj_field_piI (A : primeFormUnitary h (idGram K n)) (σ : K ≃+* K)
    (s : ↥(unitarySU 2 f K n)) :
    (primeFormConjHom h _ A * primeFormFieldHom h isPrimeFormGram_idGram σ :
        MulAut (primeFormP h (idGram K n))) (piI h n s) =
      piI h n ⟨_, semi_mem h A.2 σ s⟩ := by
  rw [MulAut.mul_apply, piI_apply]
  change primeFormConjHom h _ A (primeFormFieldAut h isPrimeFormGram_idGram σ _) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

variable (h) in
include hn hq hker hC in
theorem autOfI_eq_iff {g : G} (hg : g ∈ Subgroup.normalizer (φ.range : Set G))
    (A : primeFormUnitary h (idGram K n)) (σ : K ≃+* K) :
    autOfI h hn hq hker hC ⟨g, hg⟩ =
        primeFormConjHom h _ A * primeFormFieldHom h isPrimeFormGram_idGram σ ↔
      SemiActs h φ g A σ := by
  constructor
  · intro he
    refine ⟨A.2, fun s s' hs' => ?_⟩
    have hs'' : s' = ⟨_, semi_mem h A.2 σ s⟩ := Subtype.ext hs'
    have h1 := projEquivI_autOfI h hn hq hker hC hg (piI h n s)
    rw [he, conj_field_piI, ← hs'', projEquivI_piI, projEquivI_piI] at h1
    exact h1.symm
  · intro hA
    refine MulEquiv.ext fun x => ?_
    obtain ⟨s, rfl⟩ := piI_surjective h x
    rw [conj_field_piI, autOfI_apply_piI h hn hq hker hC hg s _ (hA.apply s)]

variable (h) in
include hn hq hker hC in
theorem exists_semiActs {g : G} (hg : g ∈ Subgroup.normalizer (φ.range : Set G)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), SemiActs h φ g A σ := by
  obtain ⟨⟨A, σ⟩, hA⟩ := primeFormPsi_surjective h isPrimeFormGram_idGram hn hq
    (autOfI h hn hq hker hC ⟨g, hg⟩)
  rw [primeFormPsi_apply] at hA
  exact ⟨A, σ, (autOfI_eq_iff h hn hq hker hC hg A σ).mp hA.symm⟩

include hn hq hker hC in
theorem eq_of_semiActs {g : G} {A B : GL (Fin n) K} {σ τ : K ≃+* K}
    (hA : SemiActs h φ g A σ) (hB : SemiActs h φ g B τ) : σ = τ := by
  have hg := hA.mem_normalizer
  have e1 := (autOfI_eq_iff h hn hq hker hC hg ⟨A, hA.1⟩ σ).mpr hA
  have e2 := (autOfI_eq_iff h hn hq hker hC hg ⟨B, hB.1⟩ τ).mpr hB
  have e3 := congrArg (primeFormFieldFactor h isPrimeFormGram_idGram hn hq) (e1.symm.trans e2)
  rwa [primeFormFieldFactor_apply, primeFormFieldFactor_apply] at e3

include hn hq hker hC in
theorem eq_one_of_semiActs_of_mem_suPairs {g : G} {A B : GL (Fin n) K} {σ : K ≃+* K}
    (hA : SemiActs h φ g A σ) (hBU : B ∈ primeFormUnitary h (idGram K n))
    (hB : (g, B) ∈ SUTorus.suPairs φ) : σ = 1 :=
  eq_of_semiActs hn hq hker hC hA (semiActs_one_iff.mpr ⟨hBU, hB⟩)

theorem glAut_eq_map (σ : K ≃+* K) (X : GL (Fin n) K) :
    glAut σ X = GeneralLinearGroup.map (σ : K →+* K) X :=
  Units.ext rfl

theorem SemiActs.pow {m : ℕ} {φ : ↥(unitarySU 2 f K (m + 1)) →* G} {g : G}
    {A : GL (Fin (m + 1)) K} {σ : K ≃+* K} (hg : SemiActs h φ g A σ) :
    ∀ k : ℕ, SemiActs h φ (g ^ k) (LinModel.twistNorm A σ k) (σ ^ k)
  | 0 => by
    rw [pow_zero, pow_zero, LinModel.twistNorm_zero]
    exact semiActs_one φ
  | k + 1 => by
    rw [pow_succ', pow_succ', LinModel.twistNorm_succ, ← glAut_eq_map]
    exact hg.mul (hg.pow k)

end SUModel

end CFSG.StandardType
