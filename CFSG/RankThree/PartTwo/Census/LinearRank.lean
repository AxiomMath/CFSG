module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.LargeEvenClassification.SemisimpleRank

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.LargeEvenClassification.Helpers

universe u v w

theorem maschke_decomposition {K : Type u} [Field K] {A : Type v} [Group A] [Finite A]
    [NeZero (Nat.card A : K)] (V : Type w) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (MonoidAlgebra K A) V]
    [IsScalarTower K (MonoidAlgebra K A) V] :
    ∃ (count : ℕ) (summands : Fin count → Submodule (MonoidAlgebra K A) V)
      (_ : V ≃ₗ[MonoidAlgebra K A] Π₀ i, summands i),
      (∀ i, IsSimpleModule (MonoidAlgebra K A) (summands i)) ∧
      Module.finrank K V = ∑ i, Module.finrank K (summands i) := by
  have : Module.Finite (MonoidAlgebra K A) V :=
    Module.Finite.of_restrictScalars_finite K (MonoidAlgebra K A) V
  obtain ⟨count, summands, equivalence, hsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (MonoidAlgebra K A) V
  refine ⟨count, summands, equivalence, hsimple, ?_⟩
  have : ∀ i, Module.Finite K (summands i) := fun i =>
    Module.Finite.of_injective (((summands i).subtype).restrictScalars K) Subtype.val_injective
  rw [(equivalence.restrictScalars K).finrank_eq,
    (DFinsupp.linearEquivFunOnFintype (R := K) (M := fun i => summands i)).finrank_eq,
    Module.finrank_pi_fintype]

theorem exists_card_eq_pow_of_exponent {A : Type v} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ a : A, a ^ p = 1) : ∃ r : ℕ, Nat.card A = p ^ r := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hexp a⟩
  exact IsPGroup.iff_card.mp hA

theorem card_le_pow_finrank_of_faithful_module {K : Type u} [Field K] {A : Type v}
    [CommGroup A] [Finite A] (V : Type w) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (MonoidAlgebra K A) V] [IsScalarTower K (MonoidAlgebra K A) V] {p : ℕ}
    (hp : p.Prime) (hpK : (p : K) ≠ 0) (hexp : ∀ a : A, a ^ p = 1)
    (hinjective : Function.Injective
      (groupAlgebraModuleAction (ScalarField := K) (Acting := A) V)) :
    Nat.card A ≤ p ^ Module.finrank K V := by
  classical
  obtain ⟨r, hr⟩ := exists_card_eq_pow_of_exponent hp hexp
  have : NeZero (Nat.card A : K) := ⟨by rw [hr, Nat.cast_pow]; exact pow_ne_zero r hpK⟩
  obtain ⟨count, summands, equivalence, hsimple, hdimension⟩ :=
    maschke_decomposition (K := K) (A := A) V
  have : ∀ i, IsSimpleModule (MonoidAlgebra K A) (summands i) := hsimple
  let actions := fun i =>
    groupAlgebraModuleAction (ScalarField := K) (Acting := A) (summands i)
  have : ∀ i, Finite (actions i).range := fun i =>
    Finite.of_surjective (actions i).rangeRestrict (actions i).rangeRestrict_surjective
  have hbound : ∀ i, Nat.card (actions i).range ≤ p ^ Module.finrank K (summands i) := by
    intro i
    have : IsCyclic (actions i).range := simple_groupAlgebra_action_cyclic (summands i)
    have hdvd := cyclic_action_card_dvd_exponent (actions i) hexp
    have hne : Nontrivial (summands i) := IsSimpleModule.nontrivial (MonoidAlgebra K A) _
    have hrank : 1 ≤ Module.finrank K (summands i) := by
      have : Nontrivial (summands i) := hne
      have : Module.Finite K (summands i) :=
        Module.Finite.of_injective (((summands i).subtype).restrictScalars K)
          Subtype.val_injective
      exact Module.finrank_pos
    calc Nat.card (actions i).range ≤ p := Nat.le_of_dvd hp.pos hdvd
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ Module.finrank K (summands i) := Nat.pow_le_pow_right hp.pos hrank
  let embedding := MonoidHom.pi (fun i => (actions i).rangeRestrict)
  have hembedding : Function.Injective embedding := by
    intro first second heq
    apply hinjective
    ext x
    change (MonoidAlgebra.of K A) first • x = (MonoidAlgebra.of K A) second • x
    apply equivalence.injective
    rw [equivalence.map_smul, equivalence.map_smul]
    apply DFinsupp.ext
    intro i
    have hcomponent : actions i first = actions i second :=
      congrArg (fun tuple => (tuple i : summands i ≃ₗ[K] summands i)) heq
    exact congrArg (fun automorphism : summands i ≃ₗ[K] summands i =>
      automorphism (equivalence x i)) hcomponent
  calc Nat.card A ≤ Nat.card (∀ i, (actions i).range) :=
        Nat.card_le_card_of_injective embedding hembedding
    _ = ∏ i, Nat.card (actions i).range := Nat.card_pi
    _ ≤ ∏ i, p ^ Module.finrank K (summands i) := Finset.prod_le_prod fun i _ => hbound i
    _ = p ^ ∑ i, Module.finrank K (summands i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = p ^ Module.finrank K V := by rw [hdimension]

theorem card_le_pow_finrank_of_faithful {K : Type u} [Field K] {A : Type v} [CommGroup A]
    [Finite A] {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {p : ℕ}
    (hp : p.Prime) (hpK : (p : K) ≠ 0) (hexp : ∀ a : A, a ^ p = 1)
    (ρ : A →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) :
    Nat.card A ≤ p ^ Module.finrank K V := by
  let representation := linearActionRepresentation ρ
  have : FiniteDimensional K representation.asModule :=
    LinearEquiv.finiteDimensional representation.asModuleEquiv.symm
  have hmoduleInjective : Function.Injective
      (groupAlgebraModuleAction (ScalarField := K) (Acting := A) representation.asModule) := by
    intro first second heq
    apply hρ
    ext x
    have hfixed := congrArg (fun automorphism : representation.asModule ≃ₗ[K]
        representation.asModule => representation.asModuleEquiv
          (automorphism (representation.asModuleEquiv.symm x))) heq
    change representation.asModuleEquiv ((MonoidAlgebra.of K A) first •
        representation.asModuleEquiv.symm x) =
      representation.asModuleEquiv ((MonoidAlgebra.of K A) second •
        representation.asModuleEquiv.symm x) at hfixed
    rw [representation.asModuleEquiv_map_smul, representation.asModuleEquiv_map_smul,
      representation.asAlgebraHom_of, representation.asAlgebraHom_of,
      representation.asModuleEquiv.apply_symm_apply] at hfixed
    exact hfixed
  have h := card_le_pow_finrank_of_faithful_module representation.asModule hp hpK hexp
    hmoduleInjective
  rwa [representation.asModuleEquiv.finrank_eq] at h

theorem pRank_le_of_injective_GL {X : Type v} [Group X] [Finite X] {K : Type u} [Field K]
    {ι : Type w} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (f : X →* GL ι K) (hf : Function.Injective f) :
    CFSG.Assembly.pRank p (⊤ : Subgroup X) ≤ Fintype.card ι := by
  apply csSup_le'
  rintro r ⟨E, -, hE, hcard⟩
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hE.1.is_comm.comm }
  let ρ : E →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (f.comp E.subtype))
  have hρ : Function.Injective ρ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).injective.comp
      (Matrix.GeneralLinearGroup.toLin.injective.comp (hf.comp E.subtype_injective))
  have hexp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hE.2 a a.2)
  have h := card_le_pow_finrank_of_faithful hp hpK hexp ρ hρ
  rw [hcard, Module.finrank_fintype_fun_eq_card] at h
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h

end CFSG.RankThree.PartTwo.Census
