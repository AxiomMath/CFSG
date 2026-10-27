module

public import CFSG.LieType.SpecialLinear.SLModel.Recognition
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.EndField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.LieType.SpecialLinear
open CFSG.LieType.SpecialLinear.SLModel CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.LieType.Universal.Unitary
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.Quasithin.SmithCurtis
open scoped TensorProduct

@[expose] def HasTwistedLabel {K : Type} [Field K] [Fintype K] [CharP K 2] {f m : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] (ε : Fin f → Finset (Fin (m + 1))) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : CharP k 2)
    (_ : Algebra (Module.End (MonoidAlgebra (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule) k) (_ : Algebra K k)
    (y : k ⊗[Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
      ρ.asModule] ρ.asModule)
    (χ : Matrix.SpecialLinearGroup (Fin (m + 1)) K → k) (J : Finset (Fin m)),
    (∀ r, (0 : Fin (m + 1)) ∉ ε r) ∧
      IsCoverType (rankOne m K 2)
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ J ∧
      (∀ g ∈ (curtisDatum m K 2).H, χ g = slChiEps m (algebraMap K k) ε g) ∧
      (∀ s : Fin m, s ∈ J ↔ ∀ r, s.succ ∉ ε r) ∧
      ∃ β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2)
          (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule] ρ.asModule) ≃ₗ[k] BModel k ε,
        ∀ (g : Matrix.SpecialLinearGroup (Fin (m + 1)) K) v,
          β (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g v) =
            slModelRep (F := K) (k := k) ε g (β v)

theorem exists_hasTwistedLabel {K : Type} [Field K] [Fintype K] [CharP K 2] {f m : ℕ}
    (hK : Fintype.card K = 2 ^ f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] (hne : ∃ x, ρ x ≠ 1) :
    ∃ ε : Fin f → Finset (Fin (m + 1)), HasTwistedLabel ρ ε ∧ ∃ r, ε r ≠ ∅ := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  let k := AlgebraicClosure E
  letI : Algebra K k :=
    (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
      (K := E) (F₀ := K) (p := 2)).some.toAlgebra
  letI : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  obtain ⟨y₀, χ, J, ht, s₀, hs₀⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.top_exists_type (n := m) ρ hne
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.top_isSimpleRep (n := m) ρ
  obtain ⟨ε, hε0, hεχ, hεJ, β, hβ⟩ :=
    CFSG.LieType.SpecialLinear.SLModel.exists_iso_slModelRep (m := m) (f := f) (hF := hK)
      (ρ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) hsimp ht
  refine ⟨ε, ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, y₀, χ, J,
    hε0, ht, hεχ, hεJ, β, hβ⟩, ?_⟩
  by_contra h
  rw [not_exists] at h
  exact hs₀ ((hεJ s₀).mpr fun r => by
    rw [show ε r = ∅ from not_not.mp (h r)]
    simp)

theorem card_endField_le_of_hasTwistedLabel {K : Type} [Field K] [Fintype K] [CharP K 2]
    {f m : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {ε : Fin f → Finset (Fin (m + 1))} (hε : HasTwistedLabel ρ ε) :
    Nat.card (Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
      ρ.asModule) ≤ Nat.card K := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  obtain ⟨k, _, _, _, _, y, χ, J, _, ht, hχ, _, _, _⟩ := hε
  haveI : Finite ((CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)).Group) :=
    CFSG.LieType.RootSystem.finite_group
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    isSimpleRep_extendScalars_endFieldRep ρ k
  have hsplit : SplitOver k (curtisDatum m K 2).H := by
    have h := splitOver m K 2 k
    rwa [Subgroup.comap_id] at h
  obtain ⟨μ, hμ⟩ := ht.exists_mu (D := curtisDatum m K 2)
    (π := MonoidHom.id (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
    (C := coverId m K 2) hsimp hsplit
  have hrange :=
    CFSG.HardMathSupport.GuralnickMalle.isCurtisType_fieldRange_eq_closure
      (ρ := ρ) (D := (coverId m K 2).datum) (k := k) hμ
  have hle : (algebraMap E k).fieldRange ≤ (algebraMap K k).fieldRange := by
    rw [hrange]
    refine Subfield.closure_le.mpr ?_
    rintro x ⟨h, hh, rfl⟩
    have hh' : h ∈ (curtisDatum m K 2).H := hh
    rw [hχ h hh']
    exact RingHom.mem_fieldRange.mpr ⟨_, rfl⟩
  have hmem : ∀ x : E, algebraMap E k x ∈ (algebraMap K k).fieldRange :=
    fun x => hle (RingHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  let g : E → K := fun x => Classical.choose (RingHom.mem_fieldRange.mp (hmem x))
  have hg : ∀ x, algebraMap K k (g x) = algebraMap E k x :=
    fun x => Classical.choose_spec (RingHom.mem_fieldRange.mp (hmem x))
  refine Nat.card_le_card_of_injective g ?_
  intro x y hxy
  apply (algebraMap E k).injective
  rw [← hg x, ← hg y, hxy]

theorem le_mul_card_node_of_hasTwistedLabel {K : Type} [Field K] [Fintype K] [CharP K 2]
    {f m : ℕ} (hK : Fintype.card K = 2 ^ f) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {ε : Fin f → Finset (Fin (m + 1))} (hε : HasTwistedLabel ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule) = 2 ^ s)
    (i : Fin m) (hi : ∃ r, i.succ ∈ ε r) :
    f ≤ s * (Finset.univ.filter fun r => i.succ ∈ ε r).card := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨k, _, _, _, _, y, χ, J, _, ht, hχ, _, _, _⟩ := hε
  have hb : bDigit ε i.succ ≠ 0 := by
    rintro h
    obtain ⟨r, hr⟩ := hi
    exact ((bDigit_eq_zero_iff ε i.succ).mp h) r hr
  have hsplit : SplitOver k (curtisDatum m K 2).H := by
    have h := splitOver m K 2 k
    rwa [Subgroup.comap_id] at h
  haveI : Finite ((CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)).Group) :=
    CFSG.LieType.RootSystem.finite_group
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)
  have hD4 : ∀ h ∈ (curtisDatum m K 2).H, ∃ c : E, χ h = algebraMap E k c :=
    CFSG.HardMathSupport.GuralnickMalle.isCoverType_chi_mem_endField (ρ := ρ) k hsplit ht
  have hval : ∀ u : Kˣ,
      (algebraMap K k) (u : K) ^ bDigit ε i.succ ∈ (algebraMap E k).range := by
    intro u
    obtain ⟨c, hc⟩ := hD4 (hdiag m K i u) (hdiag_mem_H m K i u)
    refine ⟨c, ?_⟩
    rw [← hc, hχ (hdiag m K i u) (hdiag_mem_H m K i u), slChiEps_hdiag]
  have hE' : Fintype.card E = 2 ^ s := by
    rw [← Nat.card_eq_fintype_card]
    exact hE
  have hs1 : 1 ≤ s := by
    have h2 : 1 < Nat.card E := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [hE] at h2
    by_contra h
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos h
    rw [hs0] at h2
    exact lt_irrefl 1 h2
  have hF' : Nat.card K = 2 ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hK
  exact le_mul_card_of_values_mem (m := m) (F := K) (f := f) (k := k) (E := E)
    hF' hE' hs1 (algebraMap K k) ε i.succ hb hval

end CFSG.LocalAnalysis.WeakClosure81
