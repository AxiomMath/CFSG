module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleSym
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE
public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep
public import CFSG.LocalAnalysis.StandardType.GGForkClassify
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflCartan
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.TripleEdge
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import CFSG.LocalAnalysis.StandardType.GGForkCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGQ2Lin.root_eq_zero_of_fix {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (xV : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV}) :
    ∀ j : {k // k ≠ D.a}, D.root j xV = 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    haveI : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact two_ne_zero_of_charP_three
  intro j
  have hxV : xV ∈ Submodule.span (ZMod p) {xV} := Submodule.mem_span_singleton_self xV
  have hmem : D.simpleRefl j ∈ D.parab {k | k ≠ D.a} :=
    Subgroup.subset_closure ⟨j.1, j.2, rfl⟩
  have hfixj : D.simpleRefl j xV = xV := (hfix xV).mpr hxV _ hmem
  have happ : D.simpleRefl j xV = xV - D.root j xV • D.coroot j :=
    Module.reflection_apply (h := D.root_coroot_self j) xV
  have hsmul : D.root j xV • D.coroot j = 0 := by
    rw [happ] at hfixj
    exact sub_eq_self.mp hfixj
  rcases smul_eq_zero.mp hsmul with h | h
  · exact h
  · exfalso
    exact h2ne (by
      calc (2 : ZMod p) = D.root j (D.coroot j) := (D.root_coroot_self j).symm
        _ = D.root j 0 := by rw [h]
        _ = 0 := map_zero (D.root j))

theorem GGQ2Lin.coroot_not_mem_span_of_fix {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p)
    (xV : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV}) (j : {k // k ≠ D.a}) :
    D.coroot j ∉ Submodule.span (ZMod p) {xV} := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    haveI : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact two_ne_zero_of_charP_three
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hKA := GGQ2Lin.root_eq_zero_of_fix hp D xV hfix j
  have h2 : (2 : ZMod p) = 0 := by
    calc (2 : ZMod p) = D.root j (D.coroot j) := (D.root_coroot_self j).symm
      _ = D.root j (c • xV) := by rw [← hc]
      _ = c * D.root j xV := by rw [map_smul, smul_eq_mul]
      _ = 0 := by rw [hKA, mul_zero]
  exact h2ne h2

theorem GGQ2Lin.mem_span_of_root_smul_coroot_mem {p : ℕ} [Fact p.Prime] (hp : p = 3)
    (D : GGQ2Lin p) (xV : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV}) (v : D.V)
    (hv : ∀ j : {k // k ≠ D.a}, D.root j v • D.coroot j ∈ Submodule.span (ZMod p) {xV}) :
    v ∈ Submodule.span (ZMod p) {xV} := by
  have hv0 : ∀ j : {k // k ≠ D.a}, D.root j v = 0 := by
    intro j
    by_contra hne
    apply GGQ2Lin.coroot_not_mem_span_of_fix hp D xV hfix j
    have h1 : D.coroot j = (D.root j v)⁻¹ • (D.root j v • D.coroot j) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ (hv j)
  have hfixW : ∀ g ∈ D.parab {k | k ≠ D.a}, g v = v := by
    intro g hg
    have hg' : g ∈ Subgroup.closure (D.simpleRefl '' {k | k ≠ D.a}) := by
      simpa only [GGQ2Lin.parab] using hg
    refine Subgroup.closure_induction (p := fun x _ => x v = v) ?_ ?_ ?_ ?_ hg'
    · rintro x ⟨k, hk, rfl⟩
      have happ : D.simpleRefl k v = v - D.root k v • D.coroot k :=
        Module.reflection_apply (h := D.root_coroot_self k) v
      rw [happ, hv0 ⟨k, hk⟩, zero_smul, sub_zero]
    · rfl
    · intro x y _ _ hx' hy'
      rw [LinearEquiv.mul_apply, hy', hx']
    · intro x _ hx'
      apply x.injective
      rw [hx']
      exact x.apply_symm_apply v
  exact (hfix v).mp hfixW

private lemma ggQ2xXLk2_zmod3_neg_one_ne_zero : ((-1 : ℤ) : ZMod 3) ≠ 0 := by
  decide +kernel

private lemma ggQ2xXLk2_zmod3_neg_two_ne_zero : ((-2 : ℤ) : ZMod 3) ≠ 0 := by
  decide +kernel

lemma ggQ2_zmod3_eq_one_or_neg_one : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by
  decide +kernel

private lemma ggQ2xXLk2_cast_ne_zero (D : GGQ2Lin 3) (hcard : 3 ≤ Fintype.card D.ι)
    {i j : D.ι} (hij : i ≠ j) (h : D.cartan i j ≠ 0) :
    (D.cartan i j : ZMod 3) ≠ 0 := by
  have hFT : TauCeti.IsFiniteType D.cartan :=
    isFiniteType_of_ggIsWeylMatrixFixed (D.isWeyl : GGIsWeylMatrixFixed D.coxeter) D.isCartan
  have hpre : (TauCeti.diagramGraph D.cartan).Preconnected :=
    (connected_diagramGraph_of_ggIsWeylMatrix (D.isWeyl : GGIsWeylMatrixFixed D.coxeter)
      D.isCartan).preconnected
  have hent : D.cartan i j = -1 ∨ D.cartan i j = -2 := by
    rcases D.isCartan.entries hij with ⟨-, h0, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact absurd h0 h
    · exact Or.inl h1
    · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h1
      · exfalso
        have hprod : D.cartan i j * D.cartan j i = 3 := by rw [h1, h2]; norm_num
        have hcard2 := hFT.card_eq_two_of_apply_mul_apply_eq_three hpre hprod
        omega
  rcases hent with h1 | h1
  · rw [h1]
    exact ggQ2xXLk2_zmod3_neg_one_ne_zero
  · rw [h1]
    exact ggQ2xXLk2_zmod3_neg_two_ne_zero

theorem GGQ2Lin.reflTransGen_compl_leaf {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) :
    ∀ i j : {k // k ≠ D.a}, Relation.ReflTransGen
      (fun i j : {k // k ≠ D.a} => i ≠ j ∧ (D.cartan i j : ZMod p) ≠ 0) i j := by
  subst hp
  intro i j
  obtain ⟨c₀, hc₀, huniq⟩ := D.a_leaf
  have hGconn : (TauCeti.diagramGraph D.cartan).Connected :=
    connected_diagramGraph_of_ggIsWeylMatrix (D.isWeyl : GGIsWeylMatrixFixed D.coxeter) D.isCartan
  have hnb : (TauCeti.diagramGraph D.cartan).neighborSet D.a = {c₀} := by
    ext c
    simp only [SimpleGraph.mem_neighborSet, TauCeti.diagramGraph_adj, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hne, hac, -⟩
      exact huniq c ⟨hne.symm, hac⟩
    · rintro rfl
      exact ⟨hc₀.1.symm, hc₀.2,
        fun h0 => hc₀.2 (D.isCartan.eq_zero_symm hc₀.1.symm h0)⟩
  have hdeg : (TauCeti.diagramGraph D.cartan).degree D.a = 1 := by
    rw [← SimpleGraph.ncard_neighborSet, hnb, Set.ncard_singleton]
  have hconn' : ((TauCeti.diagramGraph D.cartan).induce ({D.a}ᶜ : Set D.ι)).Connected :=
    hGconn.induce_compl_singleton_of_degree_eq_one hdeg
  have hrt : Relation.ReflTransGen
      (fun u v : {k // k ≠ D.a} =>
        (TauCeti.diagramGraph D.cartan).Adj u.1 v.1) i j :=
    (SimpleGraph.reachable_iff_reflTransGen i j).mp (hconn'.preconnected i j)
  refine Relation.ReflTransGen.mono ?_ i j hrt
  intro u v huv
  rw [TauCeti.diagramGraph_adj] at huv
  obtain ⟨huvne, hc, -⟩ := huv
  have hcard : 3 ≤ Fintype.card D.ι := by
    have h2 : 2 ≤ Fintype.card {k // k ≠ D.a} := by
      have h1 : 1 < Fintype.card {k // k ≠ D.a} :=
        Fintype.one_lt_card_iff.mpr ⟨u, v, fun h => huvne (congrArg Subtype.val h)⟩
      omega
    have hsub : Fintype.card {k // k ≠ D.a} = Fintype.card D.ι - 1 := Set.card_ne_eq D.a
    omega
  exact ⟨fun h => huvne (congrArg Subtype.val h),
    ggQ2xXLk2_cast_ne_zero D hcard huvne hc⟩

lemma GGQ2Lin.eq_zero_of_smul_coroot_mem_span {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p)
    (xV : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV}) (j : {k // k ≠ D.a}) (a : ZMod p)
    (h : a • D.coroot j ∈ Submodule.span (ZMod p) {xV}) : a = 0 := by
  by_contra hne
  apply GGQ2Lin.coroot_not_mem_span_of_fix hp D xV hfix j
  have h1 : D.coroot j = a⁻¹ • (a • D.coroot j) := by
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [h1]
  exact Submodule.smul_mem _ _ h

private lemma ggQ2xXLk_reflTransGen_eq {α R : Type*} (r : α → α → Prop) (g : α → R)
    (hstep : ∀ a b, r a b → g a = g b) {a b : α} (h : Relation.ReflTransGen r a b) :
    g a = g b := by
  induction h with
  | refl => rfl
  | tail hab hbc ih => exact ih.trans (hstep _ _ hbc)

theorem GGQ2Lin.exists_scalar_of_commute {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p)
    (xV : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {xV})
    (hconn : ∀ i j : {k // k ≠ D.a}, Relation.ReflTransGen
      (fun i j : {k // k ≠ D.a} => i ≠ j ∧ (D.cartan i j : ZMod p) ≠ 0) i j)
    (f : D.V →ₗ[ZMod p] D.V)
    (hcomm : ∀ g ∈ D.parab {k | k ≠ D.a}, ∀ v : D.V,
      f (g v) - g (f v) ∈ Submodule.span (ZMod p) {xV}) :
    ∃ c : ZMod p, ∀ v : D.V, f v - c • v ∈ Submodule.span (ZMod p) {xV} := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    haveI : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact two_ne_zero_of_charP_three
  let Cj : {k // k ≠ D.a} → ZMod p := fun j => D.root j (f (D.coroot j))
  have hu : ∀ j : {k // k ≠ D.a},
      (2 : ZMod p) • f (D.coroot j) - Cj j • D.coroot j ∈
        Submodule.span (ZMod p) {xV} := by
    intro j
    have hmem : D.simpleRefl j ∈ D.parab {k | k ≠ D.a} :=
      Subgroup.subset_closure ⟨j.1, j.2, rfl⟩
    have hraw := hcomm (D.simpleRefl j) hmem (D.coroot j)
    have hr : D.simpleRefl j (D.coroot j) = -D.coroot j := by
      have h : D.simpleRefl j (D.coroot j) =
          D.coroot j - D.root j (D.coroot j) • D.coroot j :=
        Module.reflection_apply (h := D.root_coroot_self j) (D.coroot j)
      rw [h, D.root_coroot_self j, two_smul]
      abel
    have hrf : D.simpleRefl j (f (D.coroot j)) =
        f (D.coroot j) - D.root j (f (D.coroot j)) • D.coroot j :=
      Module.reflection_apply (h := D.root_coroot_self j) (f (D.coroot j))
    have hvec : (2 : ZMod p) • f (D.coroot j) - Cj j • D.coroot j =
        -(f (D.simpleRefl j (D.coroot j)) - D.simpleRefl j (f (D.coroot j))) := by
      rw [hr, hrf, map_neg]
      dsimp only [Cj]
      module
    rw [hvec]
    exact Submodule.neg_mem _ hraw
  have hscalar : ∀ (j : {k // k ≠ D.a}) (v : D.V),
      (2 : ZMod p) * D.root j (f v) = Cj j * D.root j v := by
    intro j v
    have hmem : D.simpleRefl j ∈ D.parab {k | k ≠ D.a} :=
      Subgroup.subset_closure ⟨j.1, j.2, rfl⟩
    have hraw := hcomm (D.simpleRefl j) hmem v
    have hr : D.simpleRefl j v = v - D.root j v • D.coroot j :=
      Module.reflection_apply (h := D.root_coroot_self j) v
    have hrf : D.simpleRefl j (f v) = f v - D.root j (f v) • D.coroot j :=
      Module.reflection_apply (h := D.root_coroot_self j) (f v)
    have hsum := Submodule.add_mem _
      (Submodule.smul_mem _ (2 : ZMod p) hraw)
      (Submodule.smul_mem _ (D.root j v) (hu j))
    have hw : (2 * D.root j (f v) - D.root j v * Cj j) • D.coroot j ∈
        Submodule.span (ZMod p) {xV} := by
      have hvec : (2 * D.root j (f v) - D.root j v * Cj j) • D.coroot j =
          (2 : ZMod p) • (f (D.simpleRefl j v) - D.simpleRefl j (f v)) +
            D.root j v • ((2 : ZMod p) • f (D.coroot j) - Cj j • D.coroot j) := by
        rw [hr, hrf, map_sub, map_smul]
        dsimp only [Cj]
        module
      rw [hvec]
      exact hsum
    have hz := GGQ2Lin.eq_zero_of_smul_coroot_mem_span hp D xV hfix j _ hw
    exact (sub_eq_zero.mp hz).trans (mul_comm (D.root j v) (Cj j))
  have hadj : ∀ i j : {k // k ≠ D.a}, (D.cartan i j : ZMod p) ≠ 0 → Cj i = Cj j := by
    intro i j hC
    have h1 : (2 : ZMod p) * D.root i (f (D.coroot j)) =
        Cj i * (D.cartan i j : ZMod p) := by
      rw [hscalar i (D.coroot j), D.pairing]
    have h2 : (2 : ZMod p) * D.root i (f (D.coroot j)) =
        Cj j * (D.cartan i j : ZMod p) := by
      have hzero : D.root i ((2 : ZMod p) • f (D.coroot j) - Cj j • D.coroot j) = 0 := by
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hu j)
        rw [← hd, map_smul, smul_eq_mul, GGQ2Lin.root_eq_zero_of_fix hp D xV hfix i, mul_zero]
      have hexp : (2 : ZMod p) * D.root i (f (D.coroot j)) -
          Cj j * (D.cartan i j : ZMod p) = 0 := by
        have h := hzero
        rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, D.pairing] at h
        exact h
      exact sub_eq_zero.mp hexp
    exact mul_right_cancel₀ hC (h1.symm.trans h2)
  let j0 : {k // k ≠ D.a} := ⟨D.b, D.a_ne_b.symm⟩
  have hcommon : ∀ j : {k // k ≠ D.a}, Cj j = Cj j0 := by
    intro j
    refine ggQ2xXLk_reflTransGen_eq
      (fun i l : {k // k ≠ D.a} => i ≠ l ∧ (D.cartan i l : ZMod p) ≠ 0) Cj ?_
      (hconn j j0)
    intro i l hil
    exact hadj i l hil.2
  refine ⟨(2 : ZMod p)⁻¹ * Cj j0, fun v => ?_⟩
  have hw : (2 : ZMod p) • f v - Cj j0 • v ∈ Submodule.span (ZMod p) {xV} := by
    refine GGQ2Lin.mem_span_of_root_smul_coroot_mem hp D xV hfix _ (fun j => ?_)
    have hzero : D.root j ((2 : ZMod p) • f v - Cj j0 • v) = 0 := by
      rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hscalar j v, hcommon j]
      exact sub_self _
    rw [hzero, zero_smul]
    exact Submodule.zero_mem _
  have hconv : (2 : ZMod p)⁻¹ • ((2 : ZMod p) • f v - Cj j0 • v) =
      f v - ((2 : ZMod p)⁻¹ * Cj j0) • v := by
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ h2ne, one_smul]
  rw [← hconv]
  exact Submodule.smul_mem _ _ hw

@[expose] def ggQ2WeylOf {U : Type} [AddCommGroup U] [Module (ZMod 3) U] {ι : Type}
    (h : ι → U) (α : ι → Module.Dual (ZMod 3) U) : Subgroup (U ≃ₗ[ZMod 3] U) :=
  Subgroup.closure {t | ∃ j, ∀ v, t v = v - α j v • h j}

@[expose] def GGQ2WeylInner (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ {U : Type} [AddCommGroup U] [Module (ZMod 3) U] (h : Fin n → U),
    LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
    ∀ (α : Fin n → Module.Dual (ZMod 3) U), (∀ i j, α i (h j) = ((C i j : ℤ) : ZMod 3)) →
    ∀ T : U ≃ₗ[ZMod 3] U,
      T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) →
      ∃ w ∈ ggQ2WeylOf h α, ∀ g ∈ ggQ2WeylOf h α, T * g * T⁻¹ = w * g * w⁻¹

@[expose] def ggQ2xKDt_U0 (D : GGQ2Lin 3) : Submodule (ZMod 3) D.V :=
  Submodule.span (ZMod 3) (Set.range fun i : {k // k ≠ D.a} => D.coroot i)

theorem ggQ2xKDt_simpleRefl_apply (D : GGQ2Lin 3) (k : D.ι) (v : D.V) :
    D.simpleRefl k v = v - D.root k v • D.coroot k := by
  rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl]
  exact Module.reflection_apply v (D.root_coroot_self k)
end CFSG.StandardType

end
