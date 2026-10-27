module

public import CFSG.RankThree.PartTwo.Census.LinearRank

public section

namespace CFSG.StandardType

namespace NbrInnerNine

open CFSG.LargeEvenClassification.Helpers

theorem dvd_card_pow_finrank_sub_one {K : Type} [Field K] [Finite K] {A : Type} [CommGroup A]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (MonoidAlgebra K A) W] [IsScalarTower K (MonoidAlgebra K A) W]
    [hW : IsSimpleModule (MonoidAlgebra K A) W] {p : ℕ} (hp : p.Prime) {a : A} (hap : a ^ p = 1)
    {w : W} (hw : MonoidAlgebra.of K A a • w ≠ w) :
    p ∣ Nat.card K ^ Module.finrank K W - 1 := by
  classical
  have := Fact.mk hp
  obtain ⟨I, hI, ⟨φ⟩⟩ := isSimpleModule_iff_quot_maximal.mp hW
  let : Field (MonoidAlgebra K A ⧸ I) := Ideal.Quotient.field I
  set x : MonoidAlgebra K A ⧸ I := Ideal.Quotient.mk I (MonoidAlgebra.of K A a) with hx
  have hxp : x ^ p = 1 := by
    rw [hx, ← map_pow, ← map_pow, hap, map_one, map_one]
  have hφ : ∀ w' : W, φ (MonoidAlgebra.of K A a • w') = x * φ w' := by
    intro w'
    rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hx1 : x ≠ 1 := by
    intro h1
    apply hw
    apply φ.injective
    rw [hφ, h1, one_mul]
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hxp
    exact zero_ne_one hxp
  have : Finite W := Module.finite_of_finite K
  have : Finite (MonoidAlgebra K A ⧸ I) := Finite.of_equiv W φ.toEquiv
  set u : (MonoidAlgebra K A ⧸ I)ˣ := Units.mk0 x hx0 with hu
  have huo : orderOf u = p := by
    refine orderOf_eq_prime (Units.ext ?_) fun h => hx1 ?_
    · rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, hxp, Units.val_one]
    · have := congrArg Units.val h
      rwa [hu, Units.val_mk0, Units.val_one] at this
  have hdvd : p ∣ Nat.card (MonoidAlgebra K A ⧸ I)ˣ := huo ▸ orderOf_dvd_natCard u
  rw [Nat.card_units] at hdvd
  have hcard : Nat.card (MonoidAlgebra K A ⧸ I) = Nat.card K ^ Module.finrank K W := by
    rw [← Nat.card_congr φ.toEquiv]
    exact Module.natCard_eq_pow_finrank
  rwa [hcard] at hdvd

theorem card_pow_le_of_faithful_module {K : Type} [Field K] [Finite K] {A : Type} [CommGroup A]
    [Finite A] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (MonoidAlgebra K A) V] [IsScalarTower K (MonoidAlgebra K A) V] {p e : ℕ}
    (hp : p.Prime) (hpK : (p : K) ≠ 0) (hexp : ∀ a : A, a ^ p = 1)
    (he : ∀ j, 0 < j → j < e → ¬ p ∣ Nat.card K ^ j - 1)
    (hinjective : Function.Injective
      (groupAlgebraModuleAction (ScalarField := K) (Acting := A) V)) :
    Nat.card A ^ e ≤ p ^ Module.finrank K V := by
  classical
  obtain ⟨r, hr⟩ := CFSG.RankThree.PartTwo.Census.exists_card_eq_pow_of_exponent hp hexp
  have : NeZero (Nat.card A : K) := ⟨by rw [hr, Nat.cast_pow]; exact pow_ne_zero r hpK⟩
  obtain ⟨count, summands, equivalence, hsimple, hdimension⟩ :=
    CFSG.RankThree.PartTwo.Census.maschke_decomposition (K := K) (A := A) V
  have : ∀ i, IsSimpleModule (MonoidAlgebra K A) (summands i) := hsimple
  let actions := fun i =>
    groupAlgebraModuleAction (ScalarField := K) (Acting := A) (summands i)
  have : ∀ i, Finite (actions i).range := fun i =>
    Finite.of_surjective (actions i).rangeRestrict (actions i).rangeRestrict_surjective
  have hbound : ∀ i, Nat.card (actions i).range ^ e ≤ p ^ Module.finrank K (summands i) := by
    intro i
    have : Module.Finite K (summands i) :=
      Module.Finite.of_injective (((summands i).subtype).restrictScalars K)
        Subtype.val_injective
    have : IsCyclic (actions i).range := simple_groupAlgebra_action_cyclic (summands i)
    have hdvd := cyclic_action_card_dvd_exponent (actions i) hexp
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpc
    · rw [h1, one_pow]
      exact Nat.one_le_pow _ _ hp.pos
    · rw [hpc]
      refine Nat.pow_le_pow_right hp.pos ?_
      have hne : (actions i).range ≠ ⊥ := by
        intro hb
        rw [hb, Subgroup.card_bot] at hpc
        exact hp.one_lt.ne' hpc.symm
      obtain ⟨⟨_, a, rfl⟩, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have ha' : actions i a ≠ 1 := fun h => ha (Subtype.ext h)
      obtain ⟨w, hw⟩ : ∃ w : summands i, actions i a w ≠ w := by
        by_contra hall
        push Not at hall
        exact ha' (LinearEquiv.ext hall)
      have hd := dvd_card_pow_finrank_sub_one (K := K) (A := A) (summands i) hp (hexp a)
        (w := w) hw
      have hpos : 0 < Module.finrank K (summands i) := by
        have : Nontrivial (summands i) := IsSimpleModule.nontrivial (MonoidAlgebra K A) _
        exact Module.finrank_pos
      by_contra hlt
      exact he _ hpos (not_le.mp hlt) hd
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
  calc Nat.card A ^ e ≤ Nat.card (∀ i, (actions i).range) ^ e :=
        Nat.pow_le_pow_left (Nat.card_le_card_of_injective embedding hembedding) e
    _ = ∏ i, Nat.card (actions i).range ^ e := by rw [Nat.card_pi, Finset.prod_pow]
    _ ≤ ∏ i, p ^ Module.finrank K (summands i) := Finset.prod_le_prod fun i _ => hbound i
    _ = p ^ ∑ i, Module.finrank K (summands i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = p ^ Module.finrank K V := by rw [hdimension]

theorem card_pow_le_of_gl {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {p e : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (he : ∀ j, 0 < j → j < e → ¬ p ∣ Nat.card K ^ j - 1) (E : Subgroup (GL ι K))
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) :
    Nat.card E ^ e ≤ p ^ Fintype.card ι := by
  classical
  let _ : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have : Finite E := inferInstance
  let ρ : E →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp E.subtype)
  have hρ : Function.Injective ρ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).injective.comp
      (Matrix.GeneralLinearGroup.toLin.injective.comp E.subtype_injective)
  let representation := linearActionRepresentation ρ
  have : FiniteDimensional K representation.asModule :=
    LinearEquiv.finiteDimensional representation.asModuleEquiv.symm
  have hmoduleInjective : Function.Injective
      (groupAlgebraModuleAction (ScalarField := K) (Acting := E) representation.asModule) := by
    intro first second heq
    apply hρ
    refine LinearEquiv.ext fun x => ?_
    have hfixed := congrArg (fun automorphism : representation.asModule ≃ₗ[K]
        representation.asModule => representation.asModuleEquiv
          (automorphism (representation.asModuleEquiv.symm x))) heq
    change representation.asModuleEquiv ((MonoidAlgebra.of K E) first •
        representation.asModuleEquiv.symm x) =
      representation.asModuleEquiv ((MonoidAlgebra.of K E) second •
        representation.asModuleEquiv.symm x) at hfixed
    rw [representation.asModuleEquiv_map_smul, representation.asModuleEquiv_map_smul,
      representation.asAlgebraHom_of, representation.asAlgebraHom_of,
      representation.asModuleEquiv.apply_symm_apply] at hfixed
    exact hfixed
  have h := card_pow_le_of_faithful_module representation.asModule hp hpK
    (fun a => Subtype.ext (hexp a a.2)) he hmoduleInjective
  rwa [representation.asModuleEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card] at h

end NbrInnerNine

end CFSG.StandardType

end
