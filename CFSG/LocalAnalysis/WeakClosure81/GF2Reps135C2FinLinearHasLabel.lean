module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearEndField
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.LieType.SpecialLinear.SLModel.Recognition
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.GraphOdd
import CFSG.LieType.SpecialLinear.SLModel.Models
import CFSG.LieType.SpecialLinear.ExteriorModel.WeightDim

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.LieType.SpecialLinear
open CFSG.LieType.SpecialLinear.SLModel CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open Module
open scoped TensorProduct

@[expose] def HasLabel {K : Type} [Field K] [Fintype K] [CharP K 2] {m : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] (S : Finset (Fin (m + 1))) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : CharP k 2)
    (_ : Algebra (Module.End (MonoidAlgebra (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule) k) (_ : Algebra K k)
    (ε : Fin 1 → Finset (Fin (m + 1)))
    (y : k ⊗[Module.End (MonoidAlgebra (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
      ρ.asModule] ρ.asModule)
    (χ : Matrix.SpecialLinearGroup (Fin (m + 1)) K → k) (J : Finset (Fin m)),
    ε 0 = S ∧ (∀ r, (0 : Fin (m + 1)) ∉ ε r) ∧
      IsCoverType (rankOne m K 2)
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ J ∧
      (∀ s : Fin m, s ∈ J ↔ ∀ r, s.succ ∉ ε r) ∧
      ∃ β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2)
          (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule] ρ.asModule) ≃ₗ[k] BModel k ε,
        ∀ (g : Matrix.SpecialLinearGroup (Fin (m + 1)) K) v,
          β (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g v) =
            slModelRep (F := K) (k := k) ε g (β v)

theorem exists_hasLabel {K : Type} [Field K] [Fintype K] [CharP K 2] (hK : Fintype.card K = 2)
    {m : ℕ} (hm : 2 ≤ m) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] (hne : ∃ x, ρ x ≠ 1) :
    ∃ S : Finset (Fin (m + 1)), HasLabel ρ S ∧ (⟨0, by omega⟩ : Fin (m + 1)) ∉ S ∧ S ≠ ∅ := by
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
  have hsimp :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.top_isSimpleRep (n := m) ρ
  have hK' : Fintype.card K = 2 ^ 1 := by simpa using hK
  obtain ⟨ε, hε0, _hεχ, hεJ, β, hβ⟩ :=
    CFSG.LieType.SpecialLinear.SLModel.exists_iso_slModelRep (m := m) (f := 1) (hF := hK')
      (ρ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) hsimp ht
  refine ⟨ε 0, ?_, hε0 0, ?_⟩
  · exact ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, ε, y₀, χ, J,
      rfl, hε0, ht, hεJ, β, hβ⟩
  · intro hS
    exact hs₀ ((hεJ s₀).mpr fun r => by
      rw [Subsingleton.elim r 0, hS]
      simp)

private theorem w183_finrank_bModel_single {K : Type} [Field K] [Fintype K] [CharP K 2]
    {k : Type} [Field k] [CharP k 2] [Algebra K k]
    {m : ℕ} (ε : Fin 1 → Finset (Fin (m + 1))) {j : Fin (m + 1)}
    (h₀ : ε 0 = {j}) (hrest : ∀ r, r ≠ 0 → ε r = ∅) :
    finrank k (BModel k ε) = (m + 1).choose j.val := by
  obtain ⟨β', -⟩ := CFSG.LieType.SpecialLinear.SLModel.exists_equiv_single
    (F := K) (k := k) (m := m) (f := 1) ε h₀ hrest
  rw [β'.finrank_eq, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    Set.powersetCard.card]
  simp [Nat.card_fin]

theorem card_of_hasLabel {K : Type} [Field K] [Fintype K] [CharP K 2] (hK : Fintype.card K = 2)
    {m : ℕ} (hm : 2 ≤ m) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {S : Finset (Fin (m + 1))} (hS : HasLabel ρ S) (hne : S ≠ ∅) :
    2 ^ orbitSize S ≤ Nat.card W ∧
      ((S = {⟨1, by omega⟩} ∨ S = {⟨m, by omega⟩}) → Nat.card W = 2 ^ (m + 1)) := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  obtain ⟨k, hfield, hcharp, hEalg, hKalg, ε, y, χ, J, hεS, hε0, ht, hεJ, β, hβ⟩ := hS
  letI : Field k := hfield
  letI : CharP k 2 := hcharp
  letI : Algebra E k := hEalg
  letI : Algebra K k := hKalg
  have hE2 : Nat.card E = 2 :=
    card_endField_eq_two_of_card_eq_two hK (by omega : 2 ≤ m + 1) ρ inferInstance
  have hcard : Nat.card W = 2 ^ finrank k (BModel k ε) := by
    have h1 := card_eq_pow_finrank_extendScalars (ρ := ρ) k
    rw [hE2, β.finrank_eq] at h1
    exact h1
  have hrest : ∀ r : Fin 1, r ≠ 0 → ε r = ∅ := fun r hr =>
    absurd (Subsingleton.elim r 0) hr
  have hε0ne : ε 0 ≠ ∅ := by rwa [hεS]
  have hle : orbitSize (ε 0) ≤ finrank k (BModel k ε) := by
    have hsingle : ∏ r ∈ Finset.univ.filter (fun r : Fin 1 => ε r ≠ ∅), orbitSize (ε r) =
        orbitSize (ε 0) := by
      rw [Finset.prod_eq_single (0 : Fin 1)]
      · intro r _ hr
        exact absurd (Subsingleton.elim r 0) hr
      · intro h
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ 0, hε0ne⟩) h
    have h := prod_orbitSize_le_finrank (k := k) (n := m + 1) (τ := Fin 1) ε
    rwa [hsingle] at h
  refine ⟨?_, ?_⟩
  · calc 2 ^ orbitSize S = 2 ^ orbitSize (ε 0) := by rw [← hεS]
      _ ≤ 2 ^ finrank k (BModel k ε) := Nat.pow_le_pow_right (by norm_num) hle
      _ = Nat.card W := hcard.symm
  · rintro (hS1 | hSm)
    · have h₀ : ε 0 = {(⟨1, by omega⟩ : Fin (m + 1))} := by rw [hεS, hS1]
      have h := w183_finrank_bModel_single (K := K) (k := k) ε h₀ hrest
      rw [show (⟨1, by omega⟩ : Fin (m + 1)).val = 1 from rfl, Nat.choose_one_right] at h
      rw [hcard, h]
    · have h₀ : ε 0 = {(⟨m, by omega⟩ : Fin (m + 1))} := by rw [hεS, hSm]
      have h := w183_finrank_bModel_single (K := K) (k := k) ε h₀ hrest
      rw [show (⟨m, by omega⟩ : Fin (m + 1)).val = m from rfl,
        Nat.choose_succ_self_right] at h
      rw [hcard, h]

theorem movedOrbit_le_of_hasLabel {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {m : ℕ} (hm : 2 ≤ m) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {S : Finset (Fin (m + 1))} (hS : HasLabel ρ S)
    {y : Matrix.SpecialLinearGroup (Fin (m + 1)) K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    movedOrbit (by omega : 2 ≤ m + 1) S ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  obtain ⟨k, hfield, hcharp, hEalg, hKalg, ε, y', χ, J, hεS, hε0, ht, hεJ, β, hβ⟩ := hS
  letI : Field k := hfield
  letI : CharP k 2 := hcharp
  letI : Algebra E k := hEalg
  letI : Algebra K k := hKalg
  have hE2 : Nat.card E = 2 :=
    card_endField_eq_two_of_card_eq_two hK (by omega : 2 ≤ m + 1) ρ inferInstance
  have hE' : Nat.card E = 2 ^ 1 := by simpa using hE2
  have hrank := finrank_range_sub_one_eq_mul (s := 1) ρ hE' k y
  have hrankβ := finrank_range_sub_one_eq_of_equiv
    (τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ))
    (τ' := slModelRep (F := K) (k := k) (m := m) ε) β hβ y
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨π, hπ, hπ01, hrankπ⟩ :=
    exists_perm_finrank_range_slModelRep_sub_one (F := K) (k := k) (m := m') ε hy hy1
  have htop := card_moved_top_le (k := k) (n := m' + 2) ε (by omega) π hπ hπ01
  have hmovedTop : movedTop (by omega : 2 ≤ m' + 1 + 1) ε ≤
      2 * finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) := by
    have h1 : movedTop (by omega : 2 ≤ m' + 1 + 1) ε ≤
        2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
      unfold movedTop
      convert htop
    rw [hrankπ, ← hrankβ] at h1
    exact h1
  have hprod : ∏ i : {i : Fin 1 // i ≠ 0}, orbitSize (ε i) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact absurd (Subsingleton.elim i.1 0) i.2
  have hn : 2 ≤ m' + 1 + 1 := by omega
  have hlow := mul_prod_erase_le_movedTop (hn := hn) ε (0 : Fin 1)
  rw [hprod, Nat.mul_one] at hlow
  have hgoal : 2 * finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) =
      2 * finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
    rw [hrank, Nat.one_mul]
  rw [← hεS, ← hgoal]
  exact le_trans hlow hmovedTop

theorem symmetric_of_hasLabel {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {m : ℕ} (hm : 2 ≤ m) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {S : Finset (Fin (m + 1))} (hS : HasLabel ρ S)
    (hgraph : ∃ (d : W ≃ₗ[ZMod 2] W) (B : Matrix.GeneralLinearGroup (Fin (m + 1)) K)
      (τ : K ≃+* K), IsUpperGL B ∧ d * d = 1 ∧
        ∀ (x : Matrix.SpecialLinearGroup (Fin (m + 1)) K) (w : W),
          d (ρ x w) = ρ (borelStd (m + 1) K B τ 1 x) (d w)) :
    ∀ (j : Fin (m + 1)) (hj : 1 ≤ j.val),
      (j ∈ S ↔ (⟨m + 1 - j.val, by omega⟩ : Fin (m + 1)) ∈ S) := by
  classical
  obtain ⟨d, B, τ, hB, hd2, hd⟩ := hgraph
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  obtain ⟨k, hfield, hcharp, hEalg, hKalg, ε, y, χ, J, hεS, hε0, ht, hεJ, β, hβ⟩ := hS
  letI : Field k := hfield
  letI : CharP k 2 := hcharp
  letI : Algebra E k := hEalg
  letI : Algebra K k := hKalg
  have hE2 : Nat.card E = 2 :=
    card_endField_eq_two_of_card_eq_two hK (by omega : 2 ≤ m + 1) ρ inferInstance
  have htwo : ∀ c : E, c = 0 ∨ c = 1 := by
    obtain ⟨y₀, hy₀, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : E)).1 hE2
    haveI : Nontrivial E := ⟨⟨y₀, 0, hy₀⟩⟩
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have h1y : (1 : E) = y₀ := hyuniq 1 one_ne_zero
      exact (hyuniq c hc).trans h1y.symm
  let D : Subgroup (W ≃ₗ[ZMod 2] W) := Subgroup.zpowers d
  have hD2W : ∀ e ∈ D, e * e = 1 := by
    intro e he
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have h := (Commute.refl d).mul_zpow z
    rw [hd2, one_zpow] at h
    exact h.symm
  let δ : Representation (ZMod 2) ↥D ρ.asModule :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.topActor ρ D
  have hδE : ∀ (e : ↥D) (c : E) (x : ρ.asModule), δ e (c • x) = c • δ e x := by
    intro e c x
    rcases htwo c with rfl | rfl
    · rw [zero_smul, map_zero, zero_smul]
    · rw [one_smul, one_smul]
  have hD2 : ∀ e, δ e * δ e = 1 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.topActor_mul_self ρ D hD2W
  have hgraph' : ∃ e : ↥D, ∃ A : Matrix.GeneralLinearGroup (Fin (m + 1)) K,
      IsUpperGL A ∧ ∃ τ : K ≃+* K, ∀ g x, δ e (CFSG.endFieldRep ρ g x) =
        CFSG.endFieldRep ρ (borelStd (m + 1) K A τ 1 g) (δ e x) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.topActor_graph ρ D
      ⟨d, Subgroup.mem_zpowers d, B, hB, τ, hd⟩
  have hsimp := isSimpleRep_extendScalars_endFieldRep ρ k
  intro j hj
  let s : Fin m := ⟨j.val - 1, by omega⟩
  have hJ := stage_mem_iff_rev_mem (n := m) (σ := CFSG.endFieldRep ρ) hsimp ht δ hδE hD2
    hgraph' s
  have hsJ : s ∈ J ↔ s.succ ∉ S := by
    rw [hεJ s, Fin.forall_fin_one, hεS]
  have hrevJ : (Fin.rev s) ∈ J ↔ (Fin.rev s).succ ∉ S := by
    rw [hεJ (Fin.rev s), Fin.forall_fin_one, hεS]
  have hiff : s.succ ∈ S ↔ (Fin.rev s).succ ∈ S :=
    not_iff_not.mp (hsJ.symm.trans (hJ.trans hrevJ))
  have hs : s.succ = j := Fin.ext (by simp [s]; omega)
  have hfin : (⟨m + 1 - j.val, by omega⟩ : Fin (m + 1)) = (Fin.rev s).succ := by
    apply Fin.ext
    simp [s, Fin.val_rev]
    omega
  simpa [hs, hfin] using hiff

end CFSG.LocalAnalysis.WeakClosure81
