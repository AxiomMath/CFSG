module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Krull-Schmidt infrastructure for finite-dimensional modules

This file contains the finite-dimensional module decomposition and cancellation
facts needed for scalar-extension descent of representations.
-/

noncomputable section

namespace Module

/-- A nonzero module is indecomposable if every complementary pair of submodules
has a zero member. -/
public def IsIndecomposable
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧
    ∀ p q : Submodule R M, IsCompl p q → p = ⊥ ∨ q = ⊥

/-- The endomorphism ring of a finite-dimensional indecomposable module is local. -/
public theorem end_isLocalRing_of_isIndecomposable
    {F R M : Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup M] [Module F M] [Module R M] [IsScalarTower F R M]
    [FiniteDimensional F M]
    (hM : IsIndecomposable R M) : IsLocalRing (Module.End R M) := by
  letI : Nontrivial M := hM.1
  letI : IsNoetherian R M :=
    isNoetherian_of_tower F (inferInstance : IsNoetherian F M)
  letI : IsArtinian R M :=
    isArtinian_of_tower F (inferInstance : IsArtinian F M)
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  have hc := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow f
  rcases hM.2 _ _ hc with hk | hr
  · left
    rw [Module.End.isUnit_iff]
    have hker : LinearMap.ker f = ⊥ := by
      simpa using (iSup_eq_bot.mp hk 1)
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    exact ⟨hinj, IsArtinian.surjective_of_injective_endomorphism f hinj⟩
  · right
    apply IsNilpotent.isUnit_one_sub
    obtain ⟨n, hn⟩ :=
      Filter.eventually_atTop.mp f.eventually_iInf_range_pow_eq
    refine ⟨n, ?_⟩
    have hrange : LinearMap.range (f ^ n) = ⊥ := by
      rw [← hn n le_rfl]
      exact hr
    apply LinearMap.ext
    intro x
    have hx : (f ^ n) x ∈ LinearMap.range (f ^ n) :=
      LinearMap.mem_range_self _ x
    rw [hrange, Submodule.mem_bot] at hx
    exact hx


lemma isUnit_or_isUnit_of_isUnit_add
    {S : Type*} [Ring S] [IsLocalRing S] [IsDedekindFiniteMonoid S]
    {a b : S} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one, mul_add] at hu
  apply Or.imp _ _ (IsLocalRing.isUnit_or_isUnit_of_add_one hu)
  · exact isUnit_of_mul_isUnit_right
  · exact isUnit_of_mul_isUnit_right

lemma exists_isUnit_of_isUnit_sum
    {S ι : Type*} [Ring S] [IsLocalRing S] [IsDedekindFiniteMonoid S] [Fintype ι]
    (f : ι → S) (h : IsUnit (∑ i, f i)) : ∃ i, IsUnit (f i) := by
  classical
  have aux : ∀ s : Finset ι, IsUnit (∑ i ∈ s, f i) →
      ∃ i ∈ s, IsUnit (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        intro hu
        rcases isUnit_or_isUnit_of_isUnit_add hu with hfa | hsum
        · exact ⟨a, by simp, hfa⟩
        · obtain ⟨i, hi, hui⟩ := ih hsum
          exact ⟨i, by simp [hi], hui⟩
  obtain ⟨i, -, hi⟩ := aux Finset.univ (by simpa using h)
  exact ⟨i, hi⟩
lemma end_isDedekindFiniteMonoid
    {F R U : Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower F R U]
    [FiniteDimensional F U] : IsDedekindFiniteMonoid (Module.End R U) := by
  constructor
  intro a b hab
  have hab_apply (x : U) : a (b x) = x := DFunLike.congr_fun hab x
  have binj : Function.Injective (b.restrictScalars F) := by
    intro x y hxy
    calc
      x = a (b x) := (hab_apply x).symm
      _ = a (b y) := congrArg a hxy
      _ = y := hab_apply y
  have bsurj : Function.Surjective (b.restrictScalars F) :=
    LinearMap.injective_iff_surjective.mp binj
  apply LinearMap.ext
  intro x
  change b (a x) = x
  obtain ⟨y, hy⟩ := bsurj x
  rw [← hy]
  change b (a (b y)) = b y
  rw [hab_apply]
lemma linearEquiv_right_of_prod_linearEquiv_of_eq_inl
    {R U A B : Type*} [Ring R]
    [AddCommGroup U] [Module R U]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (e : (U × A) ≃ₗ[R] (U × B))
    (h : ∀ u : U, e (u, 0) = (u, 0)) : Nonempty (A ≃ₗ[R] B) := by
  let p : A →ₗ[R] B :=
    (LinearMap.snd R U B).comp
      (e.toLinearMap.comp (LinearMap.inr R U A))
  apply Nonempty.intro
  apply LinearEquiv.ofBijective p
  constructor
  · intro x y hxy
    have hp : p (x - y) = 0 := by simp [hxy]
    have hp' : (e (0, x - y)).2 = 0 := by
      exact hp
    have heq : e (0, x - y) = e ((e (0, x - y)).1, 0) := by
      rw [h]
      ext <;> simp [hp']
    have hpair := e.injective heq
    exact sub_eq_zero.mp (congrArg Prod.snd hpair)
  · intro y
    let z : U × A := e.symm (0, y)
    refine ⟨z.2, ?_⟩
    calc
      p z.2 = (e (0, z.2)).2 := rfl
      _ = (e (z.1, 0) + e (0, z.2)).2 := by simp [h]
      _ = (e z).2 := by rw [← e.map_add]; congr 2; simp
      _ = y := by simp [z]
lemma linearEquiv_cancel_of_isUnit_fst
    {R U A B : Type*} [Ring R]
    [AddCommGroup U] [Module R U]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (e : (U × A) ≃ₗ[R] (U × B))
    (ha : IsUnit ((LinearMap.fst R U B).comp
      (e.toLinearMap.comp (LinearMap.inl R U A)))) :
    Nonempty (A ≃ₗ[R] B) := by
  let a : Module.End R U :=
    (LinearMap.fst R U B).comp
      (e.toLinearMap.comp (LinearMap.inl R U A))
  let b : A →ₗ[R] U :=
    (LinearMap.fst R U B).comp
      (e.toLinearMap.comp (LinearMap.inr R U A))
  let c : U →ₗ[R] B :=
    (LinearMap.snd R U B).comp
      (e.toLinearMap.comp (LinearMap.inl R U A))
  let ae : U ≃ₗ[R] U :=
    LinearEquiv.ofBijective a ((Module.End.isUnit_iff a).mp ha)
  let r : (U × A) ≃ₗ[R] (U × A) :=
    { toFun := fun x => (x.1 - ae.symm (b x.2), x.2)
      invFun := fun x => (x.1 + ae.symm (b x.2), x.2)
      map_add' := by
        intro x y
        ext
        all_goals simp
        all_goals abel
      map_smul' := by intro s x; ext <;> simp [smul_sub]
      left_inv := by intro x; ext <;> simp
      right_inv := by intro x; ext <;> simp }
  let l : (U × B) ≃ₗ[R] (U × B) :=
    { toFun := fun x => (ae.symm x.1, x.2 - c (ae.symm x.1))
      invFun := fun x => (ae x.1, x.2 + c x.1)
      map_add' := by
        intro x y
        ext
        all_goals simp
        all_goals abel
      map_smul' := by intro s x; ext <;> simp [smul_sub]
      left_inv := by intro x; ext <;> simp
      right_inv := by intro x; ext <;> simp }
  let t : (U × A) ≃ₗ[R] (U × B) := r.trans (e.trans l)
  apply linearEquiv_right_of_prod_linearEquiv_of_eq_inl t
  intro u
  change l (e (r (u, 0))) = (u, 0)
  rw [show r (u, 0) = (u, 0) by simp [r]]
  rw [show e (u, 0) = (a u, c u) by rfl]
  dsimp [l]
  simp [ae]
lemma linearEquiv_cancel_of_isUnit_cross
    {R U A B : Type*} [Ring R]
    [AddCommGroup U] [Module R U]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (e : (U × A) ≃ₗ[R] (U × B))
    (hcross : IsUnit
      (((LinearMap.fst R U A).comp
        (e.symm.toLinearMap.comp (LinearMap.inr R U B))).comp
       ((LinearMap.snd R U B).comp
        (e.toLinearMap.comp (LinearMap.inl R U A))))) :
    Nonempty (A ≃ₗ[R] B) := by
  let a : Module.End R U :=
    (LinearMap.fst R U B).comp
      (e.toLinearMap.comp (LinearMap.inl R U A))
  let c : U →ₗ[R] B :=
    (LinearMap.snd R U B).comp
      (e.toLinearMap.comp (LinearMap.inl R U A))
  let bp : B →ₗ[R] U :=
    (LinearMap.fst R U A).comp
      (e.symm.toLinearMap.comp (LinearMap.inr R U B))
  let t : Module.End R U := bp.comp c
  let te : U ≃ₗ[R] U :=
    LinearEquiv.ofBijective t ((Module.End.isUnit_iff t).mp hcross)
  let s : B →ₗ[R] U := te.symm.toLinearMap.comp bp
  have hsc (u : U) : s (c u) = u := by
    change te.symm (t u) = u
    simp [te]
  let C : Submodule R B := LinearMap.ker s
  let bcMap : B →ₗ[R] U × C :=
    { toFun := fun y =>
        (s y, ⟨y - c (s y), by
          change s (y - c (s y)) = 0
          simp [hsc]⟩)
      map_add' := by
        intro x y
        apply Prod.ext
        · simp
        · apply Subtype.ext
          simp
          abel
      map_smul' := by
        intro r y
        apply Prod.ext
        · simp
        · apply Subtype.ext
          simp [smul_sub] }
  have hbcMap : Function.Bijective bcMap := by
    constructor
    · intro x y hxy
      have hsxy : s x = s y := congrArg Prod.fst hxy
      have hcxy : x - c (s x) = y - c (s y) := by
        exact congrArg (fun z : U × C => (z.2 : B)) hxy
      rw [hsxy] at hcxy
      exact sub_left_injective hcxy
    · rintro ⟨u, z⟩
      have hz : s (z : B) = 0 := z.property
      refine ⟨c u + z, ?_⟩
      apply Prod.ext
      · change s (c u + z) = u
        simp [hsc, hz]
      · apply Subtype.ext
        change c u + z - c (s (c u + z)) = z
        simp [hsc, hz]
  let bc : B ≃ₗ[R] U × C := LinearEquiv.ofBijective bcMap hbcMap
  have hbc_c (u : U) : bc (c u) = (u, 0) := by
    change bcMap (c u) = (u, 0)
    apply Prod.ext
    · simp [bcMap, hsc]
    · apply Subtype.ext
      simp [bcMap, hsc]
  let q : (U × (U × C)) ≃ₗ[R] (U × (U × C)) :=
    { toFun := fun x => (x.1 - a x.2.1, x.2)
      invFun := fun x => (x.1 + a x.2.1, x.2)
      map_add' := by
        intro x y
        ext
        all_goals simp
        all_goals abel
      map_smul' := by intro r x; ext <;> simp [smul_sub]
      left_inv := by intro x; ext <;> simp
      right_inv := by intro x; ext <;> simp }
  let swap : (U × (U × C)) ≃ₗ[R] (U × (U × C)) :=
    { toFun := fun x => (x.2.1, (x.1, x.2.2))
      invFun := fun x => (x.2.1, (x.1, x.2.2))
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  let e0 : (U × A) ≃ₗ[R] (U × (U × C)) :=
    (e.trans ((LinearEquiv.refl R U).prodCongr bc)).trans (q.trans swap)
  obtain ⟨ac⟩ := linearEquiv_right_of_prod_linearEquiv_of_eq_inl e0 (by
    intro u
    change swap (q (((LinearEquiv.refl R U).prodCongr bc) (e (u, 0)))) = (u, 0)
    rw [show e (u, 0) = (a u, c u) by rfl]
    rw [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, hbc_c]
    dsimp [q, swap]
    simp)
  exact ⟨ac.trans bc.symm⟩
lemma linearEquiv_cancel_of_end_isLocalRing
    {F R U A B : Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower F R U]
    [FiniteDimensional F U]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (hlocal : IsLocalRing (Module.End R U))
    (e : (U × A) ≃ₗ[R] (U × B)) : Nonempty (A ≃ₗ[R] B) := by
  letI : IsLocalRing (Module.End R U) := hlocal
  letI : IsDedekindFiniteMonoid (Module.End R U) :=
    end_isDedekindFiniteMonoid (F := F) (R := R) (U := U)
  let a : Module.End R U :=
    (LinearMap.fst R U B).comp
      (e.toLinearMap.comp (LinearMap.inl R U A))
  let ap : Module.End R U :=
    (LinearMap.fst R U A).comp
      (e.symm.toLinearMap.comp (LinearMap.inl R U B))
  let bp : B →ₗ[R] U :=
    (LinearMap.fst R U A).comp
      (e.symm.toLinearMap.comp (LinearMap.inr R U B))
  let c : U →ₗ[R] B :=
    (LinearMap.snd R U B).comp
      (e.toLinearMap.comp (LinearMap.inl R U A))
  have hsum : ap * a + bp.comp c = 1 := by
    apply LinearMap.ext
    intro u
    change (e.symm (a u, 0)).1 + (e.symm (0, c u)).1 = u
    calc
      (e.symm (a u, 0)).1 + (e.symm (0, c u)).1 =
          (e.symm (a u, 0) + e.symm (0, c u)).1 := rfl
      _ = (e.symm ((a u, 0) + (0, c u))).1 := by rw [e.symm.map_add]
      _ = (e.symm (a u, c u)).1 := by congr 3; simp
      _ = (e.symm (e (u, 0))).1 := by rfl
      _ = u := by simp
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with haa | hbc
  · exact linearEquiv_cancel_of_isUnit_fst e
      (isUnit_of_mul_isUnit_right haa)
  · exact linearEquiv_cancel_of_isUnit_cross e hbc
lemma exists_indecomposable_isCompl
    {F R M : Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup M] [Module F M] [Module R M] [IsScalarTower F R M]
    [FiniteDimensional F M] [Nontrivial M] :
    ∃ U C : Submodule R M, IsCompl U C ∧ IsIndecomposable R U := by
  classical
  let P : ℕ → Prop := fun d =>
    ∃ U C : Submodule R M,
      U ≠ ⊥ ∧ IsCompl U C ∧ finrank F U = d
  have hP : ∃ d, P d := by
    refine ⟨finrank F M, ⊤, ⊥, top_ne_bot, isCompl_top_bot, ?_⟩
    let eTop : (↥(⊤ : Submodule R M)) ≃ₗ[F] M :=
      LinearEquiv.ofBijective
        ((⊤ : Submodule R M).subtype.restrictScalars F)
        ⟨(⊤ : Submodule R M).subtype_injective, fun x =>
          ⟨⟨x, Submodule.mem_top⟩, rfl⟩⟩
    exact eTop.finrank_eq
  let d := Nat.find hP
  obtain ⟨U, C, hU0, hUC, hUd⟩ := Nat.find_spec hP
  letI : FiniteDimensional F U :=
    FiniteDimensional.of_injective (U.subtype.restrictScalars F) U.subtype_injective
  refine ⟨U, C, hUC, ?_⟩
  constructor
  · exact Submodule.nontrivial_iff_ne_bot.mpr hU0
  · intro p q hpq
    by_contra hn
    simp only [not_or] at hn
    let Pm : Submodule R M := p.map U.subtype
    let Qm : Submodule R M := q.map U.subtype
    have hsup : Pm ⊔ Qm = U := by
      change p.map U.subtype ⊔ q.map U.subtype = U
      rw [← Submodule.map_sup, hpq.sup_eq_top]
      ext x
      simp
    have hdis : Disjoint Pm Qm := by
      rw [disjoint_iff]
      apply le_antisymm
      · intro x hx
        rcases hx.1 with ⟨y, hy, rfl⟩
        rcases hx.2 with ⟨z, hz, hzy⟩
        have hyz : y = z := U.subtype_injective hzy.symm
        subst z
        have hybot : y ∈ (⊥ : Submodule R U) := by
          rw [← hpq.inf_eq_bot]
          exact ⟨hy, hz⟩
        rw [Submodule.mem_bot]
        exact congrArg Subtype.val (show y = 0 by simpa using hybot)
      · exact bot_le
    have hPC : IsCompl Pm (Qm ⊔ C) := by
      apply hdis.isCompl_sup_right_of_isCompl_sup_left
      rw [hsup]
      exact hUC
    have hPm0 : Pm ≠ ⊥ := by
      intro hbot
      apply hn.1
      rw [eq_bot_iff]
      intro y hy
      have hymap : (y : M) ∈ Pm := ⟨y, hy, rfl⟩
      rw [hbot, Submodule.mem_bot] at hymap
      rw [Submodule.mem_bot]
      exact Subtype.ext hymap
    have hPsmall : P (finrank F Pm) :=
      ⟨Pm, Qm ⊔ C, hPm0, hPC, rfl⟩
    have hdle : d ≤ finrank F Pm := Nat.find_min' hP hPsmall
    have hpeq : finrank F p = finrank F Pm :=
      ((U.equivSubtypeMap p).restrictScalars F).finrank_eq
    letI : FiniteDimensional F p :=
      FiniteDimensional.of_injective (p.subtype.restrictScalars F) p.subtype_injective
    letI : FiniteDimensional F q :=
      FiniteDimensional.of_injective (q.subtype.restrictScalars F) q.subtype_injective
    letI : Nontrivial q := Submodule.nontrivial_iff_ne_bot.mpr hn.2
    have hqpos : 0 < finrank F q := finrank_pos_iff.mpr inferInstance
    have hrank :=
      ((Submodule.prodEquivOfIsCompl p q hpq).restrictScalars F).finrank_eq
    have hplt : finrank F p < finrank F U := by
      rw [Module.finrank_prod] at hrank
      omega
    omega
/-- `U` is a direct summand of `X`, encoded by split maps. -/
def IsSplitSummand (R U X : Type*) [Ring R]
    [AddCommGroup U] [Module R U] [AddCommGroup X] [Module R X] : Prop :=
  ∃ i : U →ₗ[R] X, ∃ p : X →ₗ[R] U, p.comp i = LinearMap.id

lemma isSplitSummand_of_isCompl
    {R X : Type*} [Ring R] [AddCommGroup X] [Module R X]
    {U C : Submodule R X} (h : IsCompl U C) :
    IsSplitSummand R U X := by
  refine ⟨U.subtype, Submodule.projectionOnto U C h, ?_⟩
  ext u
  simp

lemma IsSplitSummand.exists_linearEquiv_prod
    {R U X : Type*} [Ring R]
    [AddCommGroup U] [Module R U] [AddCommGroup X] [Module R X]
    (h : IsSplitSummand R U X) :
    ∃ C : Submodule R X, Nonempty ((U × C) ≃ₗ[R] X) := by
  obtain ⟨i, p, hpi⟩ := h
  have hpi_apply (u : U) : p (i u) = u :=
    DFunLike.congr_fun hpi u
  have hi : Function.Injective i := by
    intro x y hxy
    have hxy' := congrArg p hxy
    calc
      x = p (i x) := (hpi_apply x).symm
      _ = p (i y) := hxy'
      _ = y := hpi_apply y
  have hc : IsCompl (LinearMap.range i) (LinearMap.ker p) := by
    constructor
    · rw [disjoint_iff]
      apply le_antisymm
      · intro x hx
        rcases hx.1 with ⟨u, rfl⟩
        have hpu : p (i u) = 0 := hx.2
        have : u = 0 := by
          rw [hpi_apply] at hpu
          exact hpu
        simp [this]
      · exact bot_le
    · rw [codisjoint_iff]
      apply top_unique
      intro x hx
      rw [Submodule.mem_sup]
      refine ⟨i (p x), LinearMap.mem_range_self i (p x),
        x - i (p x), ?_, by abel⟩
      change p (x - i (p x)) = 0
      simp [hpi_apply]
  refine ⟨LinearMap.ker p, ?_⟩
  let ei : U ≃ₗ[R] LinearMap.range i := LinearEquiv.ofInjective i hi
  exact ⟨(ei.prodCongr (LinearEquiv.refl R _)).trans
    (Submodule.prodEquivOfIsCompl _ _ hc)⟩
lemma IsSplitSummand.of_fin_power_linearEquiv
    {F R U M N : Type*} {n : ℕ}
    [Field F] [Ring R] [Algebra F R]
    [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower F R U]
    [FiniteDimensional F U]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (hU : IsIndecomposable R U)
    (hUM : IsSplitSummand R U M)
    (hn : n ≠ 0)
    (e : (Fin n → M) ≃ₗ[R] (Fin n → N)) :
    IsSplitSummand R U N := by
  classical
  letI : IsLocalRing (Module.End R U) :=
    end_isLocalRing_of_isIndecomposable (F := F) (R := R) (M := U) hU
  letI : IsDedekindFiniteMonoid (Module.End R U) :=
    end_isDedekindFiniteMonoid (F := F) (R := R) (U := U)
  obtain ⟨i, p, hpi⟩ := hUM
  let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let I : U →ₗ[R] (Fin n → M) :=
    (LinearMap.single R (fun _ : Fin n => M) i0).comp i
  let P : (Fin n → M) →ₗ[R] U :=
    p.comp (LinearMap.proj i0)
  have hPI : P.comp I = LinearMap.id := by
    apply LinearMap.ext
    intro u
    simpa [P, I] using DFunLike.congr_fun hpi u
  let j : U →ₗ[R] (Fin n → N) := e.toLinearMap.comp I
  let q : (Fin n → N) →ₗ[R] U := P.comp e.symm.toLinearMap
  have hqj : q.comp j = LinearMap.id := by
    apply LinearMap.ext
    intro u
    change P (e.symm (e (I u))) = u
    rw [e.symm_apply_apply]
    exact DFunLike.congr_fun hPI u
  let ji (k : Fin n) : U →ₗ[R] N :=
    (LinearMap.proj k).comp j
  let qk (k : Fin n) : N →ₗ[R] U :=
    q.comp (LinearMap.single R (fun _ : Fin n => N) k)
  have hsum : (∑ k, (qk k).comp (ji k)) = (1 : Module.End R U) := by
    apply LinearMap.ext
    intro u
    rw [LinearMap.sum_apply]
    change (∑ k, q (Pi.single k (j u k))) = u
    rw [← map_sum, LinearMap.sum_single_apply]
    exact DFunLike.congr_fun hqj u
  obtain ⟨k, hk⟩ := exists_isUnit_of_isUnit_sum
    (fun k => (qk k).comp (ji k)) (hsum ▸ isUnit_one)
  let t : Module.End R U := (qk k).comp (ji k)
  let te : U ≃ₗ[R] U :=
    LinearEquiv.ofBijective t ((Module.End.isUnit_iff t).mp hk)
  refine ⟨ji k, te.symm.toLinearMap.comp (qk k), ?_⟩
  apply LinearMap.ext
  intro u
  change te.symm (t u) = u
  simp [te]
lemma linearEquiv_cancel_fin_copies_of_end_isLocalRing
    {F R U A B : Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower F R U]
    [FiniteDimensional F U]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (hlocal : IsLocalRing (Module.End R U)) (n : ℕ)
    (e : ((Fin n → U) × A) ≃ₗ[R] ((Fin n → U) × B)) :
    Nonempty (A ≃ₗ[R] B) := by
  induction n with
  | zero =>
      let dA : ((Fin 0 → U) × A) ≃ₗ[R] A := LinearEquiv.uniqueProd (R := R)
      let dB : ((Fin 0 → U) × B) ≃ₗ[R] B := LinearEquiv.uniqueProd (R := R)
      exact ⟨dA.symm.trans (e.trans dB)⟩
  | succ n ih =>
      let s : (Fin (n + 1) → U) ≃ₗ[R] U × (Fin n → U) :=
        (LinearEquiv.piCongrLeft R (fun _ => U) (finSuccEquiv n)).trans
          (LinearEquiv.piOptionEquivProd R)
      let dA : ((Fin (n + 1) → U) × A) ≃ₗ[R]
          U × ((Fin n → U) × A) :=
        (s.prodCongr (LinearEquiv.refl R A)).trans
          (LinearEquiv.prodAssoc R U (Fin n → U) A)
      let dB : ((Fin (n + 1) → U) × B) ≃ₗ[R]
          U × ((Fin n → U) × B) :=
        (s.prodCongr (LinearEquiv.refl R B)).trans
          (LinearEquiv.prodAssoc R U (Fin n → U) B)
      let e' : (U × ((Fin n → U) × A)) ≃ₗ[R]
          (U × ((Fin n → U) × B)) := dA.symm.trans (e.trans dB)
      obtain ⟨e''⟩ := linearEquiv_cancel_of_end_isLocalRing
        (F := F) hlocal e'
      exact ih e''
/-- Distribute a finite product over a binary product. -/
def piProdLinearEquiv
    {R I A B : Type*} [Ring R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] :
    (I → A × B) ≃ₗ[R] (I → A) × (I → B) :=
  { toFun := fun f => (fun i => (f i).1, fun i => (f i).2)
    invFun := fun f i => (f.1 i, f.2 i)
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }

public lemma linearEquiv_of_fin_copies_linearEquiv
    {F R M N : Type*} [Field F] [Ring R] [Algebra F R]
    [AddCommGroup M] [Module F M] [Module R M] [IsScalarTower F R M]
    [FiniteDimensional F M]
    [AddCommGroup N] [Module F N] [Module R N] [IsScalarTower F R N]
    [FiniteDimensional F N]
    (n : ℕ) (hn : n ≠ 0)
    (e : (Fin n → M) ≃ₗ[R] (Fin n → N)) : Nonempty (M ≃ₗ[R] N) := by
  induction hdim : finrank F M using Nat.strong_induction_on generalizing M N with
  | h d ih =>
      by_cases hM : Nontrivial M
      · letI : Nontrivial M := hM
        obtain ⟨U, C, hUC, hU⟩ :=
          exists_indecomposable_isCompl (F := F) (R := R) (M := M)
        letI : FiniteDimensional F U :=
          FiniteDimensional.of_injective
            (U.subtype.restrictScalars F) U.subtype_injective
        letI : FiniteDimensional F C :=
          FiniteDimensional.of_injective
            (C.subtype.restrictScalars F) C.subtype_injective
        let eM : (U × C) ≃ₗ[R] M :=
          Submodule.prodEquivOfIsCompl U C hUC
        have hUN : IsSplitSummand R U N :=
          IsSplitSummand.of_fin_power_linearEquiv
            (F := F) hU (isSplitSummand_of_isCompl hUC) hn e
        obtain ⟨D, ⟨eN⟩⟩ := hUN.exists_linearEquiv_prod
        letI : FiniteDimensional F D :=
          FiniteDimensional.of_injective
            (D.subtype.restrictScalars F) D.subtype_injective
        let pM : (Fin n → U × C) ≃ₗ[R] (Fin n → M) :=
          LinearEquiv.piCongrRight (fun _ : Fin n => eM)
        let pN : (Fin n → U × D) ≃ₗ[R] (Fin n → N) :=
          LinearEquiv.piCongrRight (fun _ : Fin n => eN)
        let eUD : (Fin n → U × C) ≃ₗ[R] (Fin n → U × D) :=
          pM.trans (e.trans pN.symm)
        let sC : (Fin n → U × C) ≃ₗ[R] (Fin n → U) × (Fin n → C) :=
          piProdLinearEquiv
        let sD : (Fin n → U × D) ≃ₗ[R] (Fin n → U) × (Fin n → D) :=
          piProdLinearEquiv
        let eCDpow : ((Fin n → U) × (Fin n → C)) ≃ₗ[R]
            ((Fin n → U) × (Fin n → D)) :=
          sC.symm.trans (eUD.trans sD)
        let hlocal : IsLocalRing (Module.End R U) :=
          end_isLocalRing_of_isIndecomposable
            (F := F) (R := R) (M := U) hU
        obtain ⟨eCD⟩ := linearEquiv_cancel_fin_copies_of_end_isLocalRing
          (F := F) hlocal n eCDpow
        have hUpos : 0 < finrank F U := finrank_pos_iff.mpr hU.1
        have hrank := (eM.restrictScalars F).finrank_eq
        have hClt : finrank F C < d := by
          rw [Module.finrank_prod] at hrank
          omega
        obtain ⟨eCND⟩ := ih (finrank F C) hClt
          (M := C) (N := D) eCD rfl
        exact ⟨eM.symm.trans
          (((LinearEquiv.refl R U).prodCongr eCND).trans eN)⟩
      · letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
        let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
        letI : Subsingleton N := ⟨fun x y => by
          let sx := LinearMap.single R (fun _ : Fin n => N) i0 x
          let sy := LinearMap.single R (fun _ : Fin n => N) i0 y
          have hpre : e.symm sx = e.symm sy := Subsingleton.elim _ _
          have hsingle : sx = sy := by simpa using congrArg e hpre
          have hi := congrFun hsingle i0
          simpa [sx, sy] using hi⟩
        exact ⟨LinearEquiv.ofSubsingleton M N⟩

end Module
