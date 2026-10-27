module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHsyl
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryLagrangian

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem diagonal_mul_eq_mul_diagonal_of_agrees_one {m : ℕ} {I : Finset (Fin m)}
    {d : Fin m → K} (hd : ∀ i ∈ I, d i = 1) {M : Matrix (Fin m) (Fin m) K}
    (hM : ∀ i j, (i ∉ I ∨ j ∉ I) → M i j = (1 : Matrix (Fin m) (Fin m) K) i j) :
    diagonal d * M = M * diagonal d := by
  ext r s
  rw [diagonal_mul, mul_diagonal]
  by_cases hrs : r = s
  · subst hrs
    ring
  · by_cases hr : r ∈ I
    · by_cases hs : s ∈ I
      · rw [hd r hr, hd s hs, one_mul, mul_one]
      · rw [hM r s (Or.inr hs), one_apply_ne hrs, mul_zero, zero_mul]
    · rw [hM r s (Or.inl hr), one_apply_ne hrs, mul_zero, zero_mul]

theorem map_agrees_one {m : ℕ} {I : Finset (Fin m)} (φ : K →+* K) {M : Matrix (Fin m) (Fin m) K}
    (hM : ∀ i j, (i ∉ I ∨ j ∉ I) → M i j = (1 : Matrix (Fin m) (Fin m) K) i j) :
    ∀ i j, (i ∉ I ∨ j ∉ I) → (M.map φ) i j = (1 : Matrix (Fin m) (Fin m) K) i j := by
  intro i j hij
  rw [Matrix.map_apply, hM i j hij, one_apply]
  split_ifs <;> simp

section Perfect

variable {E H : Type*} [Group E] [Group H]

private theorem commutatorElement_mul_mem_center {z w : H} (hz : z ∈ center H) (hw : w ∈ center H)
    (a b : H) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : z * (b * w) * z⁻¹ = b * w := by
    rw [← mem_center_iff.1 hz (b * w), mul_inv_cancel_right]
  have h2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    rw [← mem_center_iff.1 hw a⁻¹, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [h1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]

private theorem eq_of_inv_mul_mem_center_of_isPerfect [Group.IsPerfect E] (f₁ f₂ : E →* H)
    (hf : ∀ x, (f₂ x)⁻¹ * f₁ x ∈ center H) : f₁ = f₂ := by
  have key : ∀ x y : E, f₁ ⁅x, y⁆ = f₂ ⁅x, y⁆ := by
    intro x y
    have hx : f₁ x = f₂ x * ((f₂ x)⁻¹ * f₁ x) := by group
    have hy : f₁ y = f₂ y * ((f₂ y)⁻¹ * f₁ y) := by group
    rw [map_commutatorElement, map_commutatorElement, hx, hy]
    exact commutatorElement_mul_mem_center (hf x) (hf y) _ _
  have hle : commutator E ≤ MonoidHom.eqLocus f₁ f₂ := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    exact key x y
  ext x
  have hx : x ∈ commutator E := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact mem_top x
  exact hle hx

end Perfect

section Aut

variable {m : ℕ}

theorem exists_eq_conj_glAut_of_mulAut (hm : 3 ≤ m) (hmq : ¬(m = 3 ∧ 2 ^ f = 2))
    (α : unitarySU 2 f K m ≃* unitarySU 2 f K m) :
    ∃ (A : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) (φ : K ≃+* K),
      ∀ g : unitarySU 2 f K m, ((α g : unitarySU 2 f K m) : GL (Fin m) K) =
        (A : GL (Fin m) K) * glAut φ (g : GL (Fin m) K) * (A : GL (Fin m) K)⁻¹ := by
  have := h.finite
  have hC1 : IsPrimeFormGram (1 : GL (Fin m) K) := isPrimeFormGram_one
  have hZ : (unitaryScalars h m).map α.toMonoidHom = unitaryScalars h m := by
    rw [← center_unitarySU_eq_unitaryScalars h m]
    exact CFSG.LieType.Universal.Unitary.map_center_mulEquiv α
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC1 hm hmq
    (MulAut.congr (CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h m).symm
      (QuotientGroup.congr _ _ α hZ))
  refine ⟨A, φ, ?_⟩
  set ψ : unitarySU 2 f K m →* GL (Fin m) K := (MulAut.conj (A : GL (Fin m) K)).toMonoidHom.comp
    ((glAut φ).toMonoidHom.comp (unitarySU 2 f K m).subtype) with hψ
  have hψapp : ∀ g : unitarySU 2 f K m, ψ g =
      (A : GL (Fin m) K) * glAut φ (g : GL (Fin m) K) * (A : GL (Fin m) K)⁻¹ := fun g => rfl
  have hmod : ∀ g : unitarySU 2 f K m,
      (ψ g)⁻¹ * ((unitarySU 2 f K m).subtype.comp α.toMonoidHom) g ∈ center (GL (Fin m) K) := by
    intro g
    have hcm : QuotientGroup.congr _ _ α hZ (unitaryProj h m g) = unitaryProj h m (α g) := rfl
    have key : MulAut.congr (CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h m).symm
        (QuotientGroup.congr _ _ α hZ)
          ((toGram h g : gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
            primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) =
        ((toGram h (α g) : gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
          primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
      rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
        primeFormOneEquiv_toGram, hcm, ← primeFormOneEquiv_toGram, MulEquiv.symm_apply_apply]
    have h2 : primeFormPsi h hC1 ⟨A, φ⟩
        ((toGram h g : gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
          primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) =
        ((toGram h (α g) : gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
          primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
      rw [hAφ]
      exact key
    rw [UnitaryLagrangian.primeFormPsi_apply_proj] at h2
    obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq (s := normOneScalars h _ m)).mp h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toGram] at hc
    change (ψ g)⁻¹ * ((α g : unitarySU 2 f K m) : GL (Fin m) K) ∈ center (GL (Fin m) K)
    rw [hψapp, hc]
    exact mem_center_iff.2 fun x => (commute_scalar c x).eq
  have : Group.IsPerfect (unitarySU 2 f K m) := (isQuasisimple_unitarySU h hm
    (fun h3 => hmq ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩)).1
  have heq := eq_of_inv_mul_mem_center_of_isPerfect _ ψ hmod
  intro g
  exact (DFunLike.congr_fun heq g).trans (hψapp g)

end Aut

section Blocks

variable {m : ℕ}

@[expose] def diagAtUnit (k : Fin m) (u : Kˣ) : GL (Fin m) K :=
  ⟨diagonal fun j => if j = k then (u : K) else 1,
    diagonal fun j => if j = k then ((u⁻¹ : Kˣ) : K) else 1, by
      simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.mul_inv, one_mul, mul_one,
        diagonal_eq_one]
      funext j; split_ifs <;> simp, by
      simp only [diagonal_mul_diagonal, mul_ite, ite_mul, Units.inv_mul, one_mul, mul_one,
        diagonal_eq_one]
      funext j; split_ifs <;> simp⟩

theorem coe_diagAtUnit (k : Fin m) (u : Kˣ) :
    ((diagAtUnit k u : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      diagonal fun j => if j = k then (u : K) else 1 :=
  rfl

theorem det_diagAtUnit (k : Fin m) (u : Kˣ) :
    Matrix.GeneralLinearGroup.det (diagAtUnit k u) = u := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagAtUnit, det_diagonal,
    Finset.prod_ite_eq' Finset.univ k]
  simp

theorem diagAtUnit_mem_primeFormUnitary (k : Fin m) {u : Kˣ} (hu : h.norm (u : K) = 1) :
    diagAtUnit k u ∈ primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, coe_diagAtUnit,
    diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  split_ifs
  · rw [← hu, UnitaryFieldData.norm, mul_comm]
  · rw [map_one, one_mul]

theorem norm_det_eq_one_of_mem_primeFormUnitary {A : GL (Fin m) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
    h.norm ((A : Matrix (Fin m) (Fin m) K).det) = 1 := by
  have h1 := congrArg Matrix.det (mem_primeFormUnitary.1 hA)
  rw [Units.val_one, Matrix.mul_one, det_mul, det_transpose, det_one] at h1
  have h2 : ((A : Matrix (Fin m) (Fin m) K).map h.bar).det =
      h.bar (A : Matrix (Fin m) (Fin m) K).det := (RingHom.map_det h.bar _).symm
  rw [h2] at h1
  rw [UnitaryFieldData.norm, mul_comm]
  exact h1

theorem exists_map_unitaryBlock_eq_conj_of_mulAut (hm : 3 ≤ m) (hmq : ¬(m = 3 ∧ 2 ^ f = 2))
    (α : unitarySU 2 f K m ≃* unitarySU 2 f K m) {J₀ : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ J₀) :
    ∃ B : unitarySU 2 f K m,
      (unitaryBlock h J₀).map α.toMonoidHom =
        (unitaryBlock h J₀).map (MulAut.conj B).toMonoidHom := by
  have := h.finite
  have hC1 : IsPrimeFormGram (1 : GL (Fin m) K) := isPrimeFormGram_one
  have hgram := CFSG.ComponentClassification.OutcomeLocal.gramSU_one_eq h m
  obtain ⟨A, φ, hα⟩ := exists_eq_conj_glAut_of_mulAut h hm hmq α
  have hδN : h.norm ((Matrix.GeneralLinearGroup.det (A : GL (Fin m) K) : Kˣ) : K) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one_of_mem_primeFormUnitary h A.2
  set D : GL (Fin m) K := diagAtUnit k (Matrix.GeneralLinearGroup.det (A : GL (Fin m) K))
    with hDdef
  have hDU : D ∈ primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    diagAtUnit_mem_primeFormUnitary h k hδN
  have hB₀ : D * (A : GL (Fin m) K)⁻¹ ∈ unitarySU 2 f K m := by
    rw [← hgram]
    refine (mem_gramSU_iff_unitary h).2 ⟨mul_mem hDU (inv_mem A.2), ?_⟩
    have hdet : Matrix.GeneralLinearGroup.det (D * (A : GL (Fin m) K)⁻¹) = 1 := by
      rw [map_mul, map_inv, hDdef, det_diagAtUnit, mul_inv_cancel]
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  set B : unitarySU 2 f K m := ⟨D * (A : GL (Fin m) K)⁻¹, hB₀⟩ with hBdef
  refine ⟨B⁻¹, ?_⟩
  have hle : (unitaryBlock h J₀).map α.toMonoidHom ≤
      (unitaryBlock h J₀).map (MulAut.conj B⁻¹).toMonoidHom := by
    rintro _ ⟨g, hg, rfl⟩
    have hg1 : (g : GL (Fin m) K) ∈
        gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
      rw [hgram]
      exact g.2
    have hφg : glAut φ (g : GL (Fin m) K) ∈ unitarySU 2 f K m := by
      have h3 := glAut_mem_gramSU h hC1 φ hg1
      rwa [hgram] at h3
    have hgJ := (mem_unitaryBlock h).1 hg
    have hg'J : ∀ i j, (i ∉ J₀ ∨ j ∉ J₀) →
        ((glAut φ (g : GL (Fin m) K) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) i j =
          (1 : Matrix (Fin m) (Fin m) K) i j := by
      rw [coe_glAut]
      exact map_agrees_one (φ : K →+* K) hgJ
    refine ⟨⟨glAut φ (g : GL (Fin m) K), hφg⟩, hg'J, ?_⟩
    have hcomm : D * glAut φ (g : GL (Fin m) K) = glAut φ (g : GL (Fin m) K) * D := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hDdef, coe_diagAtUnit]
      refine diagonal_mul_eq_mul_diagonal_of_agrees_one (fun i hi => ?_) hg'J
      have hik : i ≠ k := by rintro rfl; exact hk hi
      simp [hik]
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, hBdef, hα g]
    calc (D * (A : GL (Fin m) K)⁻¹)⁻¹ * glAut φ (g : GL (Fin m) K) * (D * (A : GL (Fin m) K)⁻¹)
        = (A : GL (Fin m) K) * (D⁻¹ * (glAut φ (g : GL (Fin m) K) * D)) *
            (A : GL (Fin m) K)⁻¹ := by group
      _ = (A : GL (Fin m) K) * glAut φ (g : GL (Fin m) K) * (A : GL (Fin m) K)⁻¹ := by
          rw [← hcomm]; group
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj B⁻¹).injective,
    Subgroup.card_map_of_injective α.injective]

end Blocks

section Coordinates

variable {n : ℕ}

theorem unitaryBlockEmbed_mem_unitaryBlock_pair_iff (I : Finset (Fin n)) (r s : Fin I.card)
    (X : unitarySU 2 f K I.card) :
    unitaryBlockEmbed h I X ∈ unitaryBlock h
        ({(I.equivFin.symm r : Fin n), (I.equivFin.symm s : Fin n)} : Finset (Fin n)) ↔
      X ∈ unitaryBlock h ({r, s} : Finset (Fin I.card)) := by
  have hmem : ∀ t : Fin I.card, ((I.equivFin.symm t : I) : Fin n) ∈
      ({(I.equivFin.symm r : Fin n), (I.equivFin.symm s : Fin n)} : Finset (Fin n)) ↔
        t ∈ ({r, s} : Finset (Fin I.card)) := by
    intro t
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (I.equivFin.symm.injective (Subtype.ext h1))
      · exact Or.inr (I.equivFin.symm.injective (Subtype.ext h1))
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hone : ∀ t u : Fin I.card, (1 : Matrix (Fin n) (Fin n) K) (I.equivFin.symm t)
      (I.equivFin.symm u) = (1 : Matrix (Fin I.card) (Fin I.card) K) t u := by
    intro t u
    rw [one_apply, one_apply]
    congr 1
    exact propext ⟨fun h1 => I.equivFin.symm.injective (Subtype.ext h1),
      fun h1 => by rw [h1]⟩
  rw [mem_unitaryBlock, mem_unitaryBlock, coe_unitaryBlockEmbed]
  constructor
  · intro H i j hij
    have h1 := H (I.equivFin.symm i) (I.equivFin.symm j)
      (hij.imp (fun hi h' => hi ((hmem i).1 h')) (fun hj h' => hj ((hmem j).1 h')))
    rw [LinearPilot.blockMatrix_apply, dite_eq_left ⟨(I.equivFin.symm i).2, (I.equivFin.symm j).2⟩,
      reindex_apply, submatrix_apply, hone] at h1
    simpa using h1
  · intro H i j hij
    rw [LinearPilot.blockMatrix_apply]
    split_ifs with hIJ
    · rw [reindex_apply, submatrix_apply]
      have hi' : I.equivFin.symm (I.equivFin ⟨i, hIJ.1⟩) = ⟨i, hIJ.1⟩ :=
        I.equivFin.symm_apply_apply _
      have hj' : I.equivFin.symm (I.equivFin ⟨j, hIJ.2⟩) = ⟨j, hIJ.2⟩ :=
        I.equivFin.symm_apply_apply _
      have hij' : I.equivFin ⟨i, hIJ.1⟩ ∉ ({r, s} : Finset (Fin I.card)) ∨
          I.equivFin ⟨j, hIJ.2⟩ ∉ ({r, s} : Finset (Fin I.card)) := by
        refine hij.imp (fun hi h' => hi ?_) (fun hj h' => hj ?_)
        · have h2 := (hmem _).2 h'
          rwa [hi'] at h2
        · have h2 := (hmem _).2 h'
          rwa [hj'] at h2
      have h3 := H _ _ hij'
      rw [Equiv.symm_symm, h3, ← hone, hi', hj']
    · rfl

theorem map_blockSUEquiv_pair {I : Finset (Fin n)} (hI : I.card < n) (r s : Fin I.card) :
    (unitaryBlock h ({r, s} : Finset (Fin I.card))).map (blockSUEquiv h hI).toMonoidHom =
      (rootSU2 h (I.equivFin.symm r) (I.equivFin.symm s)).subgroupOf (blockSU h I) := by
  ext x
  constructor
  · rintro ⟨X, hX, rfl⟩
    rw [mem_subgroupOf, MulEquiv.coe_toMonoidHom, coe_blockSUEquiv, rootSU2_eq]
    exact unitaryProj_mem_blockSU h ((unitaryBlockEmbed_mem_unitaryBlock_pair_iff h I r s X).2 hX)
  · intro hx
    rw [mem_subgroupOf, rootSU2_eq] at hx
    obtain ⟨A, hA, hAx⟩ := (mem_blockSU h).1 hx
    refine ⟨(blockSUEquiv h hI).symm x, ?_, (blockSUEquiv h hI).apply_symm_apply x⟩
    have hxX : (x : unitaryPSU h n) =
        unitaryProj h n (unitaryBlockEmbed h I ((blockSUEquiv h hI).symm x)) := by
      rw [← coe_blockSUEquiv h hI, MulEquiv.apply_symm_apply]
    have hsub : ({(I.equivFin.symm r : Fin n), (I.equivFin.symm s : Fin n)} : Finset (Fin n)) ⊆
        I := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> exact Subtype.mem _
    have hAI : A ∈ unitaryBlock h I := unitaryBlock_mono h hsub hA
    have hXI : unitaryBlockEmbed h I ((blockSUEquiv h hI).symm x) ∈ unitaryBlock h I := by
      rw [← range_unitaryBlockEmbed]
      exact ⟨_, rfl⟩
    have h1 : A⁻¹ * unitaryBlockEmbed h I ((blockSUEquiv h hI).symm x) = 1 :=
      eq_one_of_mem_unitaryBlock_of_unitaryProj_eq_one h hI (mul_mem (inv_mem hAI) hXI)
        (by rw [map_mul, map_inv, hAx, ← hxX, inv_mul_cancel])
    have heq : unitaryBlockEmbed h I ((blockSUEquiv h hI).symm x) = A :=
      (inv_mul_eq_one.1 h1).symm
    exact (unitaryBlockEmbed_mem_unitaryBlock_pair_iff h I r s _).1 (heq ▸ hA)

omit [Field K] in
theorem map_conj_subgroupOf {G : Type*} [Group G] (H S : Subgroup G) (g : S) :
    (H.subgroupOf S).map (MulAut.conj g).toMonoidHom =
      (H.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_subgroupOf]
    refine ⟨y, mem_subgroupOf.1 (SetLike.mem_coe.1 hy), ?_⟩
    simp [MulAut.conj_apply]
  · intro hx
    rw [mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      have e : ((g⁻¹ * x * g : S) : G) = y := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hyx]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hy
    · simp [MulAut.conj_apply, mul_assoc]

theorem exists_map_rootSU2_of_mulAut_blockSU {I : Finset (Fin n)} (hI3 : 3 ≤ I.card)
    (hIq : ¬(I.card = 3 ∧ 2 ^ f = 2)) (hIn : I.card < n) (ψ : blockSU h I ≃* blockSU h I)
    {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    ∃ g ∈ blockSU h I, ((rootSU2 h a b).subgroupOf (blockSU h I)).map ψ.toMonoidHom =
      ((rootSU2 h a b).map (MulAut.conj g).toMonoidHom).subgroupOf (blockSU h I) := by
  set β := blockSUEquiv h hIn with hβ
  set α : unitarySU 2 f K I.card ≃* unitarySU 2 f K I.card := β.trans (ψ.trans β.symm) with hα
  set r := I.equivFin ⟨a, ha⟩ with hr
  set s := I.equivFin ⟨b, hb⟩ with hs
  have hrs : r ≠ s := fun e => hab (congrArg Subtype.val (I.equivFin.injective e))
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({r, s} : Finset (Fin I.card))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hrs]; omega)
  obtain ⟨B, hB⟩ := exists_map_unitaryBlock_eq_conj_of_mulAut h (by omega) hIq α hk
  have hJ : (rootSU2 h a b).subgroupOf (blockSU h I) =
      (unitaryBlock h ({r, s} : Finset (Fin I.card))).map β.toMonoidHom := by
    rw [map_blockSUEquiv_pair h hIn r s, hr, hs, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  refine ⟨β B, (β B).2, ?_⟩
  rw [← map_conj_subgroupOf, hJ, Subgroup.map_map, Subgroup.map_map]
  have e1 : ψ.toMonoidHom.comp β.toMonoidHom = β.toMonoidHom.comp α.toMonoidHom := by
    ext X
    simp [hα]
  have e2 : (MulAut.conj (β B)).toMonoidHom.comp β.toMonoidHom =
      β.toMonoidHom.comp (MulAut.conj B).toMonoidHom := by
    ext X
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [e1, e2, ← Subgroup.map_map, ← Subgroup.map_map, hB]

theorem exists_map_unitaryBlock_pair_eq_conj_of_mulEquiv {m m' : ℕ} (hmm' : m = m')
    (hm : 3 ≤ m) (hmq : ¬(m = 3 ∧ 2 ^ f = 2)) (α : unitarySU 2 f K m ≃* unitarySU 2 f K m')
    {r s : Fin m} (hrs : r ≠ s) :
    ∃ B : unitarySU 2 f K m',
      (unitaryBlock h ({r, s} : Finset (Fin m))).map α.toMonoidHom =
        (unitaryBlock h ({Fin.cast hmm' r, Fin.cast hmm' s} : Finset (Fin m'))).map
          (MulAut.conj B).toMonoidHom := by
  subst hmm'
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({r, s} : Finset (Fin m))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hrs]; omega)
  simp only [Fin.cast_eq_self]
  exact exists_map_unitaryBlock_eq_conj_of_mulAut h hm hmq α hk

theorem exists_map_rootSU2_of_mulEquiv_blockSU_of_three_le {I I' : Finset (Fin n)}
    (hI3 : 3 ≤ I.card) (hIq : ¬(I.card = 3 ∧ 2 ^ f = 2)) (hIn : I.card < n)
    (hII' : I.card = I'.card) (ψ : blockSU h I ≃* blockSU h I') {a b : Fin n} (ha : a ∈ I)
    (hb : b ∈ I) (hab : a ≠ b) :
    ∃ c ∈ I', ∃ d ∈ I', c ≠ d ∧ ∃ g ∈ blockSU h I',
      ((rootSU2 h a b).subgroupOf (blockSU h I)).map ψ.toMonoidHom =
        ((rootSU2 h c d).map (MulAut.conj g).toMonoidHom).subgroupOf (blockSU h I') := by
  have hI'n : I'.card < n := hII' ▸ hIn
  set α : unitarySU 2 f K I.card ≃* unitarySU 2 f K I'.card :=
    (blockSUEquiv h hIn).trans (ψ.trans (blockSUEquiv h hI'n).symm) with hαdef
  set r : Fin I.card := I.equivFin ⟨a, ha⟩ with hr
  set s : Fin I.card := I.equivFin ⟨b, hb⟩ with hs
  have hrs : r ≠ s := fun e => hab (congrArg Subtype.val (I.equivFin.injective e))
  obtain ⟨B, hB⟩ := exists_map_unitaryBlock_pair_eq_conj_of_mulEquiv h hII' hI3 hIq α hrs
  have hcd : (I'.equivFin.symm (Fin.cast hII' r) : Fin n) ≠ I'.equivFin.symm (Fin.cast hII' s) :=
    fun e => hrs (Fin.cast_injective hII' (I'.equivFin.symm.injective (Subtype.ext e)))
  refine ⟨_, (I'.equivFin.symm (Fin.cast hII' r)).2, _, (I'.equivFin.symm (Fin.cast hII' s)).2,
    hcd, (blockSUEquiv h hI'n B : unitaryPSU h n), (blockSUEquiv h hI'n B).2, ?_⟩
  have hJ : (rootSU2 h a b).subgroupOf (blockSU h I) =
      (unitaryBlock h ({r, s} : Finset (Fin I.card))).map (blockSUEquiv h hIn).toMonoidHom := by
    rw [map_blockSUEquiv_pair h hIn r s, hr, hs, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  have e1 : ψ.toMonoidHom.comp (blockSUEquiv h hIn).toMonoidHom =
      (blockSUEquiv h hI'n).toMonoidHom.comp α.toMonoidHom := by
    ext X
    simp [hαdef]
  have e2 : (blockSUEquiv h hI'n).toMonoidHom.comp (MulAut.conj B).toMonoidHom =
      (MulAut.conj (blockSUEquiv h hI'n B)).toMonoidHom.comp
        (blockSUEquiv h hI'n).toMonoidHom := by
    ext X
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [← map_conj_subgroupOf, ← map_blockSUEquiv_pair h hI'n, hJ, Subgroup.map_map, e1,
    ← Subgroup.map_map, hB, Subgroup.map_map, e2, ← Subgroup.map_map]

theorem exists_map_rootSU2_of_mulEquiv_blockSU {I I' : Finset (Fin n)} (hI : 4 ≤ I.card)
    (hIn : I.card < n) (hII' : I.card = I'.card) (ψ : blockSU h I ≃* blockSU h I') {a b : Fin n}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    ∃ c ∈ I', ∃ d ∈ I', c ≠ d ∧ ∃ g ∈ blockSU h I',
      ((rootSU2 h a b).subgroupOf (blockSU h I)).map ψ.toMonoidHom =
        ((rootSU2 h c d).map (MulAut.conj g).toMonoidHom).subgroupOf (blockSU h I') :=
  exists_map_rootSU2_of_mulEquiv_blockSU_of_three_le h (by omega)
    (fun h3 => by have := h3.1; omega) hIn hII' ψ ha hb hab

end Coordinates

end CFSG.SeitzReduction.UnitaryPilot
