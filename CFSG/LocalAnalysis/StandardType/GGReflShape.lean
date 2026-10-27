module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Paths

public section

namespace CFSG.StandardType

section TreeGauge

open SimpleGraph

private def wprod {ι : Type} {Γ : Type*} [CommGroup Γ] {G : SimpleGraph ι} (w : ι → ι → Γ) {a b : ι}
    (p : G.Walk a b) : Γ :=
  (p.darts.map fun d => w d.toProd.1 d.toProd.2).prod

private lemma wprod_nil {ι : Type} {Γ : Type*} [CommGroup Γ] {G : SimpleGraph ι} (w : ι → ι → Γ) {a : ι} :
    wprod w (Walk.nil : G.Walk a a) = 1 := by
  unfold wprod
  rw [Walk.darts_nil, List.map_nil, List.prod_nil]

private lemma wprod_cons {ι : Type} {Γ : Type*} [CommGroup Γ] {G : SimpleGraph ι} (w : ι → ι → Γ)
    {a b c : ι} (h : G.Adj a b) (p : G.Walk b c) :
    wprod w (Walk.cons h p) = w a b * wprod w p := by
  unfold wprod
  rw [Walk.darts_cons, List.map_cons, List.prod_cons]

private lemma wprod_append {ι : Type} {Γ : Type*} [CommGroup Γ] {G : SimpleGraph ι} (w : ι → ι → Γ)
    {a b c : ι} (p : G.Walk a b) (q : G.Walk b c) :
    wprod w (p.append q) = wprod w p * wprod w q := by
  unfold wprod
  rw [Walk.darts_append, List.map_append, List.prod_append]

private lemma wprod_concat {ι : Type} {Γ : Type*} [CommGroup Γ] {G : SimpleGraph ι} (w : ι → ι → Γ)
    {a b c : ι} (p : G.Walk a b) (h : G.Adj b c) :
    wprod w (p.concat h) = wprod w p * w b c := by
  rw [Walk.concat_eq_append, wprod_append, wprod_cons, wprod_nil, mul_one]

private lemma wprod_copy {ι : Type} {Γ : Type*} [CommGroup Γ] {G : SimpleGraph ι} (w : ι → ι → Γ)
    {a b a' b' : ι} (p : G.Walk a b) (ha : a = a') (hb : b = b') :
    wprod w (p.copy ha hb) = wprod w p := by
  unfold wprod
  rw [Walk.darts_copy]

private lemma wprod_path_edge {ι : Type} {Γ : Type*} [CommGroup Γ] {G : SimpleGraph ι}
    (hG : G.IsAcyclic) (w : ι → ι → Γ) (hw : ∀ i j, G.Adj i j → w j i = (w i j)⁻¹)
    {s i j : ι} (hij : G.Adj i j) (P : G.Path s i) (Q : G.Path s j) :
    wprod w (Q : G.Walk s j) = wprod w (P : G.Walk s i) * w i j := by
  classical
  by_cases hj : j ∈ (P : G.Walk s i).support
  ·
    have htj : ((P : G.Walk s i).takeUntil j hj).IsPath := P.isPath.takeUntil hj
    have hdj : ((P : G.Walk s i).dropUntil j hj).IsPath := P.isPath.dropUntil hj
    let T : G.Path s j := ⟨(P : G.Walk s i).takeUntil j hj, htj⟩
    let D : G.Path j i := ⟨(P : G.Walk s i).dropUntil j hj, hdj⟩
    have hsingle : (Walk.cons hij.symm (Walk.nil : G.Walk i i)).IsPath := by
      rw [Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by
        simpa [Walk.support_nil] using (G.ne_of_adj hij).symm⟩
    let E : G.Path j i := ⟨Walk.cons hij.symm Walk.nil, hsingle⟩
    have hTQ : (T : G.Walk s j) = (Q : G.Walk s j) :=
      congrArg (fun p : G.Path s j => (p : G.Walk s j)) (hG.path_unique T Q)
    have hDE : (D : G.Walk j i) = (E : G.Walk j i) :=
      congrArg (fun p : G.Path j i => (p : G.Walk j i)) (hG.path_unique D E)
    have hPD : wprod w (P : G.Walk s i)
        = wprod w (T : G.Walk s j) * wprod w (D : G.Walk j i) := by
      calc wprod w (P : G.Walk s i)
          = wprod w (((P : G.Walk s i).takeUntil j hj).append
              ((P : G.Walk s i).dropUntil j hj)) := by
            rw [Walk.take_spec]
        _ = wprod w ((P : G.Walk s i).takeUntil j hj)
              * wprod w ((P : G.Walk s i).dropUntil j hj) := wprod_append w _ _
        _ = wprod w (T : G.Walk s j) * wprod w (D : G.Walk j i) := rfl
    have hwDE : wprod w (D : G.Walk j i) = w j i := by
      rw [hDE]
      show wprod w (Walk.cons hij.symm (Walk.nil : G.Walk i i)) = w j i
      rw [wprod_cons, wprod_nil, mul_one]
    have hkey : wprod w (P : G.Walk s i) = wprod w (Q : G.Walk s j) * (w i j)⁻¹ := by
      rw [hPD, hTQ, hwDE, hw i j hij]
    have hcalc : wprod w (P : G.Walk s i) * w i j = wprod w (Q : G.Walk s j) := by
      rw [hkey, mul_assoc, inv_mul_cancel, mul_one]
    exact hcalc.symm
  ·
    have hpath : ((P : G.Walk s i).concat hij).IsPath := P.isPath.concat hj hij
    let R : G.Path s j := ⟨(P : G.Walk s i).concat hij, hpath⟩
    have hRQ : (R : G.Walk s j) = (Q : G.Walk s j) :=
      congrArg (fun p : G.Path s j => (p : G.Walk s j)) (hG.path_unique R Q)
    calc wprod w (Q : G.Walk s j)
        = wprod w (R : G.Walk s j) := by rw [← hRQ]
      _ = wprod w ((P : G.Walk s i).concat hij) := rfl
      _ = wprod w (P : G.Walk s i) * w i j := wprod_concat w (P : G.Walk s i) hij

theorem ggTreeGauge {ι : Type} {Γ : Type*} [CommGroup Γ] {G : SimpleGraph ι} (hG : G.IsAcyclic)
    (w : ι → ι → Γ) (hw : ∀ i j, G.Adj i j → w j i = (w i j)⁻¹) :
    ∃ c : ι → Γ, ∀ i j, G.Adj i j → c j = c i * w i j := by
  classical
  let r : ι → ι := fun v => Quot.out (G.connectedComponentMk v)
  have hr : ∀ v, G.Reachable (r v) v := by
    intro v
    have h : G.connectedComponentMk (r v) = G.connectedComponentMk v :=
      Quot.out_eq (G.connectedComponentMk v)
    exact SimpleGraph.ConnectedComponent.eq.mp h
  have hrij : ∀ i j, G.Adj i j → r i = r j := by
    intro i j hij
    exact congrArg Quot.out
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hij)
  let P : ∀ v, G.Path (r v) v := fun v => (Classical.choice (hr v)).toPath
  refine ⟨fun v => wprod w (P v : G.Walk (r v) v), ?_⟩
  intro i j hij
  let Q : G.Path (r i) j :=
    ⟨((P j : G.Walk (r j) j).copy (hrij i j hij).symm rfl),
      (Walk.isPath_copy (P j : G.Walk (r j) j) (hrij i j hij).symm rfl).mpr (P j).isPath⟩
  have hQ : wprod w (Q : G.Walk (r i) j) = wprod w (P j : G.Walk (r j) j) :=
    wprod_copy w (P j : G.Walk (r j) j) (hrij i j hij).symm rfl
  have h := wprod_path_edge hG w hw hij (P i) Q
  change wprod w (P j : G.Walk (r j) j) = wprod w (P i : G.Walk (r i) i) * w i j
  rw [← hQ]
  exact h

end TreeGauge

open Module Polynomial.Chebyshev CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Linear

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
  {A : Subgroup (MulAut ↥Bs)} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

private theorem cross_eq_zero_of_noTransvection' (hp2 : p ≠ 2)
    (hnt : ∀ φ ∈ A, ¬ GGIsTransvection p φ) (ι' : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ A) (hψ : ψ ∈ A) {x y : V}
    {f g : Module.Dual (ZMod p) V} (hfx : f x = 2) (hgy : g y = 2)
    (hLφ : ggLin (p := p) ι' φ = reflection hfx) (hLψ : ggLin (p := p) ι' ψ = reflection hgy)
    (hfy : f y = 0) : g x = 0 := by
  have h2 := zmod_two_ne_zero hp2
  obtain ⟨hy0, -⟩ := ne_zero_of_apply_eq_two hp2 hgy
  by_contra hgx
  refine hnt ((φ * ψ) ^ 2) (A.pow_mem (A.mul_mem hφ hψ) 2) ?_
  refine ggIsTransvection_of_apply ι' (w := y) (f := g x • f) hy0 ?_ ?_ ?_
  · intro h0
    have hx := congrArg (fun F : Module.Dual (ZMod p) V => F x) h0
    simp only [LinearMap.smul_apply, smul_eq_mul, hfx, LinearMap.zero_apply] at hx
    exact h2 ((mul_eq_zero.mp hx).resolve_left hgx)
  · rw [LinearMap.smul_apply, hfy, smul_zero]
  · intro v
    rw [map_pow, map_mul, hLφ, hLψ, reflection_mul_reflection_sq_apply_of_eq_zero hfx hgy hfy,
      LinearMap.smul_apply, smul_eq_mul]

private theorem linearIndependent_of_noTransvection' (hp2 : p ≠ 2)
    (hnt : ∀ φ ∈ A, ¬ GGIsTransvection p φ) (ι' : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ A) (hψ : ψ ∈ A) (hne : φ ≠ ψ) {x y : V}
    {f g : Module.Dual (ZMod p) V} (hfx : f x = 2) (hgy : g y = 2)
    (hLφ : ggLin (p := p) ι' φ = reflection hfx) (hLψ : ggLin (p := p) ι' ψ = reflection hgy) :
    LinearIndependent (ZMod p) ![x, y] ∧ LinearIndependent (ZMod p) ![f, g] := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero hp2⟩
  rcases linearIndependent_and_or_exists_transvection (K := ZMod p) (x := x) (y := y) (f := f)
    (g := g) hfx hgy with hind | ⟨w, θ, hθw, hT⟩
  · exact hind
  · exfalso
    have key : w = 0 ∨ θ = 0 → False := by
      intro h0
      have h1 : ggLin (p := p) ι' (φ * ψ) = 1 := by
        refine LinearEquiv.ext fun v => ?_
        rw [map_mul, hLφ, hLψ, hT]
        rcases h0 with rfl | rfl <;> simp
      have h2 : ggLin (p := p) ι' (ψ * ψ) = 1 := by
        refine LinearEquiv.ext fun v => ?_
        rw [map_mul, hLψ, LinearEquiv.mul_apply, involutive_reflection hgy v]
        rfl
      have e1 : φ * ψ = 1 := ggLin_injective (p := p) ι' (by rw [h1, map_one])
      have e2 : ψ * ψ = 1 := ggLin_injective (p := p) ι' (by rw [h2, map_one])
      exact hne (by rw [eq_inv_of_mul_eq_one_left e1, inv_eq_of_mul_eq_one_left e2])
    by_cases hw : w = 0
    · exact key (Or.inl hw)
    by_cases hθ : θ = 0
    · exact key (Or.inr hθ)
    exact hnt (φ * ψ) (A.mul_mem hφ hψ)
      (ggIsTransvection_of_apply ι' hw hθ hθw fun v => by rw [map_mul, hLφ, hLψ, hT])

private theorem reflection_pow_eq_one_of_mulAut_pow (ι' : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} {x y : V} {f g : Module.Dual (ZMod p) V} (hfx : f x = 2)
    (hgy : g y = 2) (hLφ : ggLin (p := p) ι' φ = reflection hfx)
    (hLψ : ggLin (p := p) ι' ψ = reflection hgy) {n : ℕ} (h : (φ * ψ) ^ n = 1) :
    (reflection hfx * reflection hgy) ^ n = 1 := by
  have := congrArg (ggLin (p := p) ι') h
  simpa [map_pow, map_mul, hLφ, hLψ] using this

private theorem label_two_zero_of_noTransvection (hp2 : p ≠ 2)
    (hnt : ∀ φ ∈ A, ¬ GGIsTransvection p φ) (ι' : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ A) (hψ : ψ ∈ A) {x y : V}
    {f g : Module.Dual (ZMod p) V} (hfx : f x = 2) (hgy : g y = 2)
    (hLφ : ggLin (p := p) ι' φ = reflection hfx) (hLψ : ggLin (p := p) ι' ψ = reflection hgy)
    (hind : LinearIndependent (ZMod p) ![x, y] ∧ LinearIndependent (ZMod p) ![f, g])
    (hrel : (reflection hfx * reflection hgy) ^ 2 = 1) : f y = 0 ∧ g x = 0 := by
  obtain ⟨hxy, hfg⟩ := hind
  have hfy : f y = 0 := by
    by_contra hu
    have hv : g x ≠ 0 := fun hv0 =>
      hu (cross_eq_zero_of_noTransvection' hp2 hnt ι' hψ hφ hgy hfx hLψ hLφ hv0)
    have hcontr := (reflection_mul_reflection_pow_even_eq_one_iff (K := ZMod p) (x := x) (y := y)
      (f := f) (g := g) hfx hgy hxy hfg hu hv 1).mp hrel
    rw [show ((1 : ℕ) : ℤ) - 1 = 0 by norm_num, S_zero, Polynomial.eval_one] at hcontr
    exact one_ne_zero hcontr
  refine ⟨hfy, ?_⟩
  by_contra hv
  have hu : f y ≠ 0 := fun hu0 =>
    hv (cross_eq_zero_of_noTransvection' hp2 hnt ι' hφ hψ hfx hgy hLφ hLψ hu0)
  have hcontr := (reflection_mul_reflection_pow_even_eq_one_iff (K := ZMod p) (x := x) (y := y)
    (f := f) (g := g) hfx hgy hxy hfg hu hv 1).mp hrel
  rw [show ((1 : ℕ) : ℤ) - 1 = 0 by norm_num, S_zero, Polynomial.eval_one] at hcontr
  exact one_ne_zero hcontr

private theorem label_three_self_ne_zero_of_noTransvection (hp2 : p ≠ 2)
    (hnt : ∀ φ ∈ A, ¬ GGIsTransvection p φ) (ι' : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ A) (hψ : ψ ∈ A) (hne : φ ≠ ψ) {x y : V}
    {f g : Module.Dual (ZMod p) V} (hfx : f x = 2) (hgy : g y = 2)
    (hLφ : ggLin (p := p) ι' φ = reflection hfx) (hLψ : ggLin (p := p) ι' ψ = reflection hgy)
    (hrel3 : (reflection hfx * reflection hgy) ^ 3 = 1) : f y ≠ 0 := by
  intro hfy0
  have hgx0 : g x = 0 :=
    cross_eq_zero_of_noTransvection' hp2 hnt ι' hφ hψ hfx hgy hLφ hLψ hfy0
  have hsq : (reflection hfx * reflection hgy) ^ 2 = 1 :=
    reflection_mul_reflection_pow_two hfx hgy hfy0 hgx0
  have hpow : (reflection hfx * reflection hgy) ^ 3 = reflection hfx * reflection hgy := by
    rw [pow_succ, hsq, one_mul]
  have hr1 : reflection hfx * reflection hgy = 1 := by rw [← hpow]; exact hrel3
  have e1 : φ * ψ = 1 := by
    apply ggLin_injective (p := p) ι'
    rw [map_mul, hLφ, hLψ, map_one]
    exact hr1
  have e2 : ψ * ψ = 1 := by
    apply ggLin_injective (p := p) ι'
    rw [map_mul, hLψ, map_one]
    exact LinearEquiv.ext fun v => by
      rw [LinearEquiv.mul_apply, involutive_reflection hgy v]
      rfl
  exact hne (by rw [eq_inv_of_mul_eq_one_left e1, inv_eq_of_mul_eq_one_left e2])

private lemma inv_mul_self_mul {K : Type*} [Field K] (g a : K) (hg : g ≠ 0) :
    g⁻¹ * (g * a) = a := by
  rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]

private lemma inv_mul_mul_neg_inv_mul {K : Type*} [Field K] (g₁ g₂ a : K) (hg₁ : g₁ ≠ 0)
    (ha : a ≠ 0) (h : g₂ = g₁ * (-(a⁻¹))) : g₁⁻¹ * (g₂ * a) = -1 := by
  rw [h]
  calc g₁⁻¹ * ((g₁ * (-(a⁻¹))) * a)
      = (-(a⁻¹)) * a * (g₁⁻¹ * g₁) := by ring
    _ = (-(a⁻¹)) * a := by rw [inv_mul_cancel₀ hg₁, mul_one]
    _ = -(a⁻¹ * a) := by ring
    _ = -1 := by rw [inv_mul_cancel₀ ha]

private lemma inv_mul_smul_self_smul {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (g a : K) (x : W) (hg : g ≠ 0) : (g⁻¹ * a) • (g • x) = a • x := by
  rw [smul_smul]
  congr 1
  rw [mul_assoc, mul_comm a g, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]

end Linear

theorem ggRefl_shape {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type} [Fintype ι] {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥A} (hM : GGIsWeylMatrix M) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hrefl : ∀ i : ι, GGIsReflection p ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    (hnt : ∀ φ ∈ A, ¬ GGIsTransvection p φ) {C : Matrix ι ι ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ι' : Additive ↥Bs ≃+ V) :
    ∃ (h : ι → V) (f : ι → Module.Dual (ZMod p) V),
      (∀ i j, f i (h j) = ((C i j : ℤ) : ZMod p)) ∧
      ∀ i v, ggLin (p := p) ι' ((e (M.simple i) : ↥A) : MulAut ↥Bs) v = v - f i v • h i := by
  classical
  have hSL : GGSimplyLaced M := (ggSimplyLacedConnected_of_weyl hM h3).1
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (show GGIsWeylMatrixFixed M from hM) hC
  have hinj : Function.Injective M.simple := ggSimplyLaced_simple_injective hSL
  choose x g hgx hlin using fun i => exists_of_ggIsReflection (p := p) ι' (hrefl i)
  let r : ι → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  have hrmem : ∀ i, r i ∈ A := fun i => (e (M.simple i)).2
  have hLr : ∀ i, ggLin (p := p) ι' (r i) = reflection (hgx i) :=
    fun i => ggLin_eq_reflection ι' (hgx i) (hlin i)
  have hrne : ∀ i j, i ≠ j → r i ≠ r j := by
    intro i j hij h
    have h' : ((e (M.simple i) : ↥A) : MulAut ↥Bs) = ((e (M.simple j) : ↥A) : MulAut ↥Bs) := h
    exact hij (hinj (e.injective (Subtype.ext h')))
  have hind : ∀ i j, i ≠ j →
      LinearIndependent (ZMod p) ![x i, x j] ∧ LinearIndependent (ZMod p) ![g i, g j] :=
    fun i j hij => linearIndependent_of_noTransvection' hp2 hnt ι' (hrmem i) (hrmem j)
      (hrne i j hij) (hgx i) (hgx j) (hLr i) (hLr j)
  have hrelPow : ∀ i j, (r i * r j) ^ (M.M i j) = 1 := by
    intro i j
    have h := M.toCoxeterSystem.simple_mul_simple_pow i j
    have h1 : (e (M.simple i) * e (M.simple j)) ^ (M.M i j) = 1 := by
      have he : e ((M.simple i * M.simple j) ^ (M.M i j)) = e 1 := congrArg e h
      simpa [map_pow, map_mul] using he
    have := congrArg A.subtype h1
    simpa [r, map_pow, map_mul] using this
  let u : ι → ι → ZMod p := fun i j => g i (x j)
  have hzero2 : ∀ i j, i ≠ j → M.M i j = 2 → u i j = 0 ∧ u j i = 0 := by
    intro i j hij hij2
    obtain ⟨hxy, hfg⟩ := hind i j hij
    have hrel : (reflection (hgx i) * reflection (hgx j)) ^ 2 = 1 :=
      reflection_pow_eq_one_of_mulAut_pow ι' (hgx i) (hgx j) (hLr i) (hLr j)
        (by simpa [hij2] using hrelPow i j)
    exact label_two_zero_of_noTransvection hp2 hnt ι' (hrmem i) (hrmem j) (hgx i) (hgx j)
      (hLr i) (hLr j) ⟨hxy, hfg⟩ hrel
  have hthree : ∀ i j, i ≠ j → M.M i j = 3 → u i j ≠ 0 ∧ u j i ≠ 0 ∧ u i j * u j i = 1 := by
    intro i j hij hij3
    obtain ⟨hxy, hfg⟩ := hind i j hij
    have hrel : (reflection (hgx i) * reflection (hgx j)) ^ 3 = 1 :=
      reflection_pow_eq_one_of_mulAut_pow ι' (hgx i) (hgx j) (hLr i) (hLr j)
        (by simpa [hij3] using hrelPow i j)
    have hu : u i j ≠ 0 := label_three_self_ne_zero_of_noTransvection hp2 hnt ι' (hrmem i)
      (hrmem j) (hrne i j hij) (hgx i) (hgx j) (hLr i) (hLr j) hrel
    have hrelswap : (reflection (hgx j) * reflection (hgx i)) ^ 3 = 1 := by
      have hinv : (reflection (hgx i) * reflection (hgx j))⁻¹ =
          reflection (hgx j) * reflection (hgx i) := by
        rw [mul_inv_rev, reflection_inv (hgx i), reflection_inv (hgx j)]
      have h := congrArg Inv.inv hrel
      rw [inv_one, ← inv_pow, hinv] at h
      exact h
    have hv : u j i ≠ 0 := label_three_self_ne_zero_of_noTransvection hp2 hnt ι' (hrmem j)
      (hrmem i) (hrne j i hij.symm) (hgx j) (hgx i) (hLr j) (hLr i) hrelswap
    have huv : u i j * u j i = 1 := by
      have hsum := (reflection_mul_reflection_pow_odd_eq_one_iff (K := ZMod p) (x := x i)
        (y := x j) (f := g i) (g := g j) (hgx i) (hgx j) hxy hfg hu hv 1).mp hrel
      simp only [Nat.cast_one, sub_self, S_one, S_zero, Polynomial.eval_X,
        Polynomial.eval_one] at hsum
      show g i (x j) * g j (x i) = 1
      linear_combination hsum
    exact ⟨hu, hv, huv⟩
  let Gr : SimpleGraph ι := TauCeti.diagramGraph C
  have hGadj : ∀ {i j : ι}, Gr.Adj i j ↔ i ≠ j ∧ C i j ≠ 0 ∧ C j i ≠ 0 :=
    fun {i j} => TauCeti.diagramGraph_adj
  have hGacyc : Gr.IsAcyclic := hFT.isAcyclic_diagramGraph
  have hadj3 : ∀ i j, Gr.Adj i j → M.M i j = 3 := by
    intro i j hadj
    obtain ⟨hij, hCij, -⟩ := hGadj.mp hadj
    rcases hSL i j hij with h2 | h3
    · exfalso
      rcases hC.2 i j hij with ⟨hm, hz, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · exact hCij hz
      · rw [h2] at hm; omega
      · rw [h2] at hm; omega
      · rw [h2] at hm; omega
    · exact h3
  have hadjprod : ∀ i j, Gr.Adj i j → u i j ≠ 0 ∧ u j i ≠ 0 ∧ u i j * u j i = 1 :=
    fun i j hadj => hthree i j (hGadj.mp hadj).1 (hadj3 i j hadj)
  let w : ι → ι → (ZMod p)ˣ := fun i j =>
    if h : Gr.Adj i j then
      Units.mk0 (-((u i j)⁻¹)) (neg_ne_zero.mpr (inv_ne_zero (hadjprod i j h).1))
    else 1
  have hw_val : ∀ i j (h : Gr.Adj i j), ((w i j : (ZMod p)ˣ) : ZMod p) = -((u i j)⁻¹) := by
    intro i j h
    simp only [w, dif_pos h]
    exact Units.val_mk0 _
  have hw_inv : ∀ i j, Gr.Adj i j → w j i = (w i j)⁻¹ := by
    intro i j hij
    have hji : Gr.Adj j i := by
      rw [hGadj] at hij ⊢
      exact ⟨hij.1.symm, hij.2.2, hij.2.1⟩
    have hprod : u i j * u j i = 1 := (hadjprod i j hij).2.2
    have h1 : (u i j)⁻¹ = u j i := ZMod.inv_eq_of_mul_eq_one p (u i j) (u j i) hprod
    have h2 : (u j i)⁻¹ = u i j :=
      ZMod.inv_eq_of_mul_eq_one p (u j i) (u i j) (by rw [mul_comm]; exact hprod)
    refine eq_inv_of_mul_eq_one_right ?_
    apply Units.ext
    rw [Units.val_mul, Units.val_one, hw_val i j hij, hw_val j i hji, h1, h2]
    calc (-(u j i)) * (-(u i j)) = u j i * u i j := by ring
      _ = u i j * u j i := by rw [mul_comm]
      _ = 1 := hprod
  obtain ⟨c, hc⟩ := ggTreeGauge (Γ := (ZMod p)ˣ) hGacyc w hw_inv
  let gam : ι → ZMod p := fun i => (c i : ZMod p)
  have hgam_ne : ∀ i, gam i ≠ 0 := fun i => Units.ne_zero (c i)
  have hgam_adj : ∀ i j, Gr.Adj i j → gam j = gam i * (-((u i j)⁻¹)) := by
    intro i j hadj
    have h := congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) (hc i j hadj)
    rw [Units.val_mul, hw_val i j hadj] at h
    simpa [gam] using h
  let hvec : ι → V := fun i => gam i • x i
  let fvec : ι → Module.Dual (ZMod p) V := fun i => (gam i)⁻¹ • g i
  have hfvec : ∀ i v, fvec i v = (gam i)⁻¹ * g i v := by
    intro i v
    simp only [fvec, LinearMap.smul_apply, smul_eq_mul]
  have hpair : ∀ i j, fvec i (hvec j) = ((C i j : ℤ) : ZMod p) := by
    intro i j
    have hgj : g i (hvec j) = gam j * u i j := by
      simp only [hvec, map_smul, smul_eq_mul, u]
    rw [hfvec, hgj]
    by_cases hij : i = j
    · subst hij
      rw [inv_mul_self_mul (gam i) (u i i) (hgam_ne i)]
      show g i (x i) = ((C i i : ℤ) : ZMod p)
      rw [hgx i, hC.1 i]
      norm_num
    · by_cases hadj : Gr.Adj i j
      · have hli3 : M.M i j = 3 := hadj3 i j hadj
        have hCij : C i j = -1 := by
          rcases hC.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, h1, h2⟩ | ⟨hm, -, -, -⟩ |
            ⟨hm, -, -, -⟩
          · rw [hli3] at hm; omega
          · exact h1
          · rw [hli3] at hm; omega
          · rw [hli3] at hm; omega
        rw [inv_mul_mul_neg_inv_mul (gam i) (gam j) (u i j) (hgam_ne i)
          (hadjprod i j hadj).1 (hgam_adj i j hadj), hCij]
        norm_num
      · have hli2 : M.M i j = 2 := by
          rcases hSL i j hij with h2 | h3
          · exact h2
          · exfalso
            have hC3 : C i j = -1 ∧ C j i = -1 := by
              rcases hC.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, h1, h2⟩ | ⟨hm, -, -, -⟩ |
                ⟨hm, -, -, -⟩
              · rw [h3] at hm; omega
              · exact ⟨h1, h2⟩
              · rw [h3] at hm; omega
              · rw [h3] at hm; omega
            exact hadj (hGadj.mpr ⟨hij, by rw [hC3.1]; norm_num, by rw [hC3.2]; norm_num⟩)
        have hu0 : u i j = 0 := (hzero2 i j hij hli2).1
        have hC0 : C i j = 0 := by
          rcases hC.2 i j hij with ⟨-, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
            ⟨hm, -, -, -⟩
          · exact h1
          · rw [hli2] at hm; omega
          · rw [hli2] at hm; omega
          · rw [hli2] at hm; omega
        rw [hu0, mul_zero, mul_zero, hC0]
        norm_num
  have hformula : ∀ i v, ggLin (p := p) ι' (r i) v = v - fvec i v • hvec i := by
    intro i v
    rw [hLr i, reflection_apply, hfvec i v, show hvec i = gam i • x i from rfl,
      inv_mul_smul_self_smul (gam i) (g i v) (x i) (hgam_ne i)]
  exact ⟨hvec, fvec, hpair, hformula⟩

end CFSG.StandardType
