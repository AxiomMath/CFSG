module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParam
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityUnitary
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHsyl
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryLagrangian
import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {m : ℕ}

section Commute

theorem map_bar_inverseTranspose_eq {A : GL (Fin m) K}
    (hA : ((A : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) K) = 1) :
    GeneralLinearGroup.map ((barRingEquiv h : K ≃+* K) : K →+* K)
      (GeneralLinearGroup.inverseTranspose A) = A := by
  apply Units.ext
  ext i j
  have hinv : (((A⁻¹ : GL (Fin m) K)) : Matrix (Fin m) (Fin m) K) =
      ((A : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ := by
    rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv hA]
  rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_inverseTranspose, hinv,
    transpose_transpose, Matrix.map_apply]
  change h.bar (h.bar _) = _
  rw [h.bar_bar]

theorem commute_conjAut_graphFieldAut {A : GL (Fin m) K}
    (hA : ((A : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * (A : Matrix (Fin m) (Fin m) K) = 1) :
    Commute (LinearFlag.conjAut m K A) (graphFieldAut h m) := by
  have key : (LinearFlag.fieldAut m K (barRingEquiv h) * LinearFlag.dualAut m K) *
      LinearFlag.conjAut m K A = LinearFlag.conjAut m K A *
        (LinearFlag.fieldAut m K (barRingEquiv h) * LinearFlag.dualAut m K) := by
    rw [mul_assoc, LinearFlag.dualAut_mul_conjAut, ← mul_assoc, LinearFlag.fieldAut_mul_conjAut,
      map_bar_inverseTranspose_eq h hA, mul_assoc]
  exact key.symm

theorem commute_fieldAut_graphFieldAut (φ : K ≃+* K) :
    Commute (LinearFlag.fieldAut m K φ) (graphFieldAut h m) := by
  change LinearFlag.fieldAut m K φ * (LinearFlag.fieldAut m K (barRingEquiv h) *
      LinearFlag.dualAut m K) = (LinearFlag.fieldAut m K (barRingEquiv h) *
      LinearFlag.dualAut m K) * LinearFlag.fieldAut m K φ
  calc LinearFlag.fieldAut m K φ * (LinearFlag.fieldAut m K (barRingEquiv h) *
        LinearFlag.dualAut m K) =
        LinearFlag.fieldAut m K (φ * barRingEquiv h) * LinearFlag.dualAut m K := by
          rw [map_mul, mul_assoc]
    _ = LinearFlag.fieldAut m K (barRingEquiv h * φ) * LinearFlag.dualAut m K := by
          rw [(commute_barRingEquiv h φ).eq]
    _ = LinearFlag.fieldAut m K (barRingEquiv h) *
        (LinearFlag.fieldAut m K φ * LinearFlag.dualAut m K) := by rw [map_mul, mul_assoc]
    _ = (LinearFlag.fieldAut m K (barRingEquiv h) * LinearFlag.dualAut m K) *
        LinearFlag.fieldAut m K φ := by rw [← LinearFlag.dualAut_mul_fieldAut, mul_assoc]

end Commute

section Fixed

theorem exists_mem_center_graphFieldSL_eq {g : SpecialLinearGroup (Fin m) K}
    (hg : graphFieldAut h m (LinearFlag.proj m K g) = LinearFlag.proj m K g) :
    ∃ s ∈ center (SpecialLinearGroup (Fin m) K), graphFieldSL h m g = s * g := by
  rw [graphFieldAut_proj, LinearFlag.proj_eq_proj_iff] at hg
  set a := (graphFieldSL h m g)⁻¹ * g with ha
  have hs : a ∈ center (SpecialLinearGroup (Fin m) K) := LinearFlag.scalars_le_center m K hg
  have hs' : a⁻¹ ∈ center (SpecialLinearGroup (Fin m) K) := inv_mem hs
  have e1 : graphFieldSL h m g = g * a⁻¹ := by rw [ha]; group
  refine ⟨a⁻¹, hs', ?_⟩
  calc graphFieldSL h m g = g * a⁻¹ := e1
    _ = a⁻¹ * g := mem_center_iff.mp hs' g

theorem unitary_of_graphFieldSL_eq {g : SpecialLinearGroup (Fin m) K}
    (hg : graphFieldSL h m g = g) :
    ((g : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * (g : Matrix (Fin m) (Fin m) K) = 1 := by
  have h1 : ((g : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ =
      ((g⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    ext i j
    have hji := congrArg (fun x : SpecialLinearGroup (Fin m) K =>
      (x : Matrix (Fin m) (Fin m) K) j i) hg
    simp only [coe_graphFieldSL, Matrix.map_apply, transpose_apply] at hji
    rw [transpose_apply, Matrix.map_apply, ← hji, h.bar_bar]
  rw [h1]
  exact congrArg (fun x : SpecialLinearGroup (Fin m) K => (x : Matrix (Fin m) (Fin m) K))
    (inv_mul_cancel g)

theorem commutator_fixedSubgroup_graphFieldAut_le :
    ⁅fixedSubgroup (graphFieldAut h m), fixedSubgroup (graphFieldAut h m)⁆ ≤
      (toPSL h m).range := by
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective m K x
  obtain ⟨g', rfl⟩ := LinearFlag.proj_surjective m K y
  obtain ⟨s, hs, hgs⟩ := exists_mem_center_graphFieldSL_eq h (g := g) hx
  obtain ⟨s', hs', hgs'⟩ := exists_mem_center_graphFieldSL_eq h (g := g') hy
  have hc : graphFieldSL h m ⁅g, g'⁆ = ⁅g, g'⁆ := by
    rw [map_commutatorElement, hgs, hgs',
      CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hs hs']
  have hu := unitary_of_graphFieldSL_eq h hc
  obtain ⟨A, hA⟩ := (mem_range_toSL_iff h).2 hu
  refine ⟨unitaryProj h m A, ?_⟩
  rw [toPSL_unitaryProj, hA, map_commutatorElement]

theorem le_range_toPSL_of_le_fixedSubgroup {P : Subgroup (LinearFlag.projectiveSL m K)}
    (hP : ⁅P, P⁆ = P) (hPF : P ≤ fixedSubgroup (graphFieldAut h m)) :
    P ≤ (toPSL h m).range := by
  rw [← hP]
  exact (commutator_mono hPF hPF).trans (commutator_fixedSubgroup_graphFieldAut_le h)

theorem range_toPSL_le_fixedSubgroup : (toPSL h m).range ≤ fixedSubgroup (graphFieldAut h m) := by
  rintro _ ⟨x, rfl⟩
  exact graphFieldAut_toPSL h x

end Fixed

section Rigidity

theorem conjAut_eq_conj_proj_toSL (g : unitarySU p f K m) :
    LinearFlag.conjAut m K (g : GL (Fin m) K) = MulAut.conj (LinearFlag.proj m K (toSL h m g)) := by
  ext x
  obtain ⟨y, rfl⟩ := LinearFlag.proj_surjective m K x
  rw [LinearFlag.conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv (toSL h m) g]
  congr 1
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation]
  rfl

theorem mem_centralizer_of_forall_toPSL {α : MulAut (LinearFlag.projectiveSL m K)}
    (hα : ∀ x : unitaryPSU h m, α (toPSL h m x) = toPSL h m x) :
    α ∈ centralizer (((unitarySU p f K m).map (LinearFlag.conjAut m K) :
      Subgroup (MulAut (LinearFlag.projectiveSL m K))) : Set (MulAut (LinearFlag.projectiveSL m K))) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [show g = ((⟨g, hg⟩ : unitarySU p f K m) : GL (Fin m) K) from rfl,
    conjAut_eq_conj_proj_toSL h ⟨g, hg⟩]
  have hfix : α (LinearFlag.proj m K (toSL h m ⟨g, hg⟩)) = LinearFlag.proj m K (toSL h m ⟨g, hg⟩) := by
    rw [← toPSL_unitaryProj]
    exact hα _
  ext x
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, hfix]

theorem mem_zpowers_graphFieldAut_of_forall_toPSL (hm : 3 ≤ m)
    {α : MulAut (LinearFlag.projectiveSL m K)}
    (hα : ∀ x : unitaryPSU h m, α (toPSL h m x) = toPSL h m x) :
    α ∈ zpowers (graphFieldAut h m) := by
  obtain ⟨-, -, -, -, -, -, hcent⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.linear_graph_field_full_centralizer_rigidity h
      hm (barRingEquiv h) (fun _ => rfl)
  rw [graphFieldAut, ← hcent]
  exact mem_centralizer_of_forall_toPSL h hα

theorem eq_of_forall_toPSL_of_pow (hm : 3 ≤ m) {β γ : MulAut (LinearFlag.projectiveSL m K)}
    (hβθ : Commute β (graphFieldAut h m)) {r : ℕ} (hr : Odd r) (hβr : β ^ r = 1)
    (hγr : γ ^ r = 1) (hagree : ∀ x : unitaryPSU h m, γ (toPSL h m x) = β (toPSL h m x)) :
    γ = β := by
  set α := β⁻¹ * γ with hαdef
  have hα : ∀ x : unitaryPSU h m, α (toPSL h m x) = toPSL h m x := fun x => by
    rw [hαdef, MulAut.mul_apply, hagree]
    exact MulAut.inv_apply_self _ _ _
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (mem_zpowers_graphFieldAut_of_forall_toPSL h hm hα)
  have hθ2 : graphFieldAut h m ^ 2 = 1 := by rw [sq]; exact graphFieldAut_mul_self h
  have hα2 : α ^ 2 = 1 := by
    rw [← hj, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hθ2,
      _root_.one_zpow]
  have hcomm : Commute β α := hj ▸ hβθ.zpow_right j
  have hγ : γ = β * α := by rw [hαdef, mul_inv_cancel_left]
  have hαr : α ^ r = 1 := by
    have h1 := hcomm.mul_pow r
    rw [← hγ, hγr, hβr, one_mul] at h1
    exact h1.symm
  obtain ⟨s, rfl⟩ := hr
  rw [pow_succ, pow_mul, hα2, one_pow, one_mul] at hαr
  rw [hγ, hαr, mul_one]

end Rigidity

section Extension

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {m : ℕ}

theorem exists_mulAut_toPSL_comm (hm : 3 ≤ m) (hmq : ¬(m = 3 ∧ 2 ^ f = 2))
    (δ : MulAut (unitaryPSU h m)) :
    ∃ δ' : MulAut (LinearFlag.projectiveSL m K),
      (∀ x : unitaryPSU h m, δ' (toPSL h m x) = toPSL h m (δ x)) ∧
        Commute δ' (graphFieldAut h m) := by
  have := h.charP
  have := h.finite
  have hC1 : UnitaryHigher.IsPrimeFormGram (1 : GL (Fin m) K) := UnitaryHigher.isPrimeFormGram_one
  obtain ⟨⟨A, φ⟩, hAφ⟩ := UnitaryHigher.primeFormPsi_surjective h hC1 hm hmq
    (MulAut.congr (CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h m).symm δ)
  have hAu : (((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ *
      ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
    have h0 : (((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ *
        (1 : Matrix (Fin m) (Fin m) K) * ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 :=
      UnitaryHigher.mem_primeFormUnitary.1 A.2
    rwa [Matrix.mul_one] at h0
  refine ⟨LinearFlag.conjAut m K A * LinearFlag.fieldAut m K φ, fun x => ?_,
    (commute_conjAut_graphFieldAut h hAu).mul_left (commute_fieldAut_graphFieldAut h φ)⟩
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h m x
  set y : CFSG.ClassicalGroups.UnitaryFlag.gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    ⟨(A : GL (Fin m) K) * UnitaryHigher.glAut φ ((toGram h g : _) : GL (Fin m) K) *
      (A : GL (Fin m) K)⁻¹, UnitaryHigher.conj_mem_gramSU h _ A.2
        (UnitaryHigher.glAut_mem_gramSU h hC1 φ (toGram h g).2)⟩ with hy
  have hymem : (y : GL (Fin m) K) ∈ unitarySU 2 f K m := by
    rw [← CFSG.ComponentClassification.OutcomeLocal.gramSU_one_eq]
    exact y.2
  set g' : unitarySU 2 f K m := ⟨y, hymem⟩ with hg'
  have hδ : δ (unitaryProj h m g) = unitaryProj h m g' := by
    have h1 : MulAut.congr (CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h m).symm
        δ ((toGram h g : _) : UnitaryHigher.primeFormP h _) =
          (y : UnitaryHigher.primeFormP h _) := by
      rw [← hAφ, UnitaryLagrangian.primeFormPsi_apply_proj]
    rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
      primeFormOneEquiv_toGram] at h1
    have h2 := congrArg (CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h m) h1
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h2]
    exact CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv_mk h y g' rfl
  rw [hδ, toPSL_unitaryProj, toPSL_unitaryProj, MulAut.mul_apply, LinearFlag.fieldAut_proj,
    LinearFlag.conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation]
  rfl

end Extension

end CFSG.SeitzReduction.UnitaryPilot
