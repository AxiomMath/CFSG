module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylReflectionOfFixedPoints
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl

public section

namespace CFSG.StandardType.SpJoinRefl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section TypeE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.Open
open CFSG.LieType.Steinberg.Adjoint

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

private lemma ra_cartan_E6 : Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6
private lemma ra_cartan_E7 : Tag.cartan .E7 = CartanMatrix.E 7 := cartanE_eq 7
private lemma ra_cartan_E8 : Tag.cartan .E8 = CartanMatrix.E 8 := cartanE_eq 8

private lemma ra_ggIntCartan_E6 : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6) := by
  rw [ra_cartan_E6]
  exact ggIntCartan_E₆

private lemma ra_ggIntCartan_E7 : GGIntCartan CoxeterMatrix.E₇ (Tag.cartan .E7) := by
  rw [ra_cartan_E7]
  exact ggIntCartan_E₇

private lemma ra_ggIntCartan_E8 : GGIntCartan CoxeterMatrix.E₈ (Tag.cartan .E8) := by
  rw [ra_cartan_E8]
  exact ggIntCartan_E₈

private lemma ra_matrix_E6 : CoxeterMatrix.E₆ = coxeterMatrix (isFiniteType_cartan .E6) :=
  (CFSG.StandardType.coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6)
    ra_ggIntCartan_E6).symm

private lemma ra_matrix_E7 : CoxeterMatrix.E₇ = coxeterMatrix (isFiniteType_cartan .E7) :=
  (CFSG.StandardType.coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E7)
    ra_ggIntCartan_E7).symm

private lemma ra_matrix_E8 : CoxeterMatrix.E₈ = coxeterMatrix (isFiniteType_cartan .E8) :=
  (CFSG.StandardType.coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E8)
    ra_ggIntCartan_E8).symm

private lemma ra_isA2Pair_of_iform_neg {τ : Tag} (hτ : ∀ i, τ.symmetrizer i i = 1)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (h : iform β γ = -1) :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair β γ :=
  ⟨hβ, hγ, CFSG.LieType.Chevalley.SimplyLacedCover.isRoot_add hτ hβ hγ h,
    by rw [CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hγ,
      CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hβ],
    by rw [h, CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hβ]; norm_num⟩

theorem weylOfType_tag_E6 {A : Subgroup (MulAut ↥Bs)} (h : GGWeylOfType p CoxeterMatrix.E₆ A) :
    GGWeylOfType p (coxeterMatrix (isFiniteType_cartan .E6)) A := by
  rw [← ra_matrix_E6]
  exact h

theorem weylOfType_tag_E7 {A : Subgroup (MulAut ↥Bs)} (h : GGWeylOfType p CoxeterMatrix.E₇ A) :
    GGWeylOfType p (coxeterMatrix (isFiniteType_cartan .E7)) A := by
  rw [← ra_matrix_E7]
  exact h

theorem weylOfType_tag_E8 {A : Subgroup (MulAut ↥Bs)} (h : GGWeylOfType p CoxeterMatrix.E₈ A) :
    GGWeylOfType p (coxeterMatrix (isFiniteType_cartan .E8)) A := by
  rw [← ra_matrix_E8]
  exact h

theorem ggIntCartan_tag_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    GGIntCartan (coxeterMatrix (isFiniteType_cartan τ)) τ.cartan := by
  rcases hτ with rfl | rfl | rfl
  · rw [← ra_matrix_E6, ra_cartan_E6]
    exact ggIntCartan_E₆
  · rw [← ra_matrix_E7, ra_cartan_E7]
    exact ggIntCartan_E₇
  · rw [← ra_matrix_E8, ra_cartan_E8]
    exact ggIntCartan_E₈

theorem exists_torus_intertwiner {τ : Tag} (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {A : Subgroup (MulAut ↥Bs)} (e : WeylGroup τ ≃* ↥A) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) (h : Fin τ.rank → V)
    (α : Fin τ.rank → Module.Dual (ZMod p) V) (hα : ∀ i, α i (h i) = 2)
    (hlin : ∀ i, ggLin (p := p) ιV ((e (simple τ i) : ↥A) : MulAut ↥Bs) =
      Module.reflection (hα i))
    (hP : ∀ i j, α i (h j) = (τ.cartan i j : ZMod p)) :
    ∃ Ψ : (Fin τ.rank → ZMod p) →ₗ[ZMod p] V, (∀ j, Ψ (Pi.single j 1) = h j) ∧
      (∀ w a, Ψ (TableBExc.torusAct τ p w a) =
        ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) (Ψ a)) ∧
      ∀ a, Ψ a = 0 → ∀ w, TableBExc.torusAct τ p w a = a := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let Ψ : (Fin τ.rank → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  have hΨ_apply : ∀ a, Ψ a = ∑ j, a j • h j := fun a => Fintype.linearCombination_apply _ _ _
  have hΨ_single : ∀ j, Ψ (Pi.single j 1) = h j := by
    intro j
    rw [hΨ_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [Pi.single_eq_of_ne hbj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hsum : ∀ (i : Fin τ.rank) (a : Fin τ.rank → ZMod p),
      (∑ j, ((τ.cartan j i : ℤ) : ZMod p) * a j) = α i (Ψ a) := by
    intro i a
    rw [hΨ_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hP i j]
    have hsymm' : ((τ.cartan j i : ℤ) : ZMod p) = ((τ.cartan i j : ℤ) : ZMod p) := by
      rw [hsymm j i]
    rw [hsymm', smul_eq_mul, mul_comm]
  have hsimple : ∀ i a, Ψ (TableBExc.torusAct τ p (simple τ i) a) =
      ggLin (p := p) ιV ((e (simple τ i) : ↥A) : MulAut ↥Bs) (Ψ a) := by
    intro i a
    have htc : TableBExc.torusAct τ p (simple τ i) a =
        a - (∑ j, ((τ.cartan j i : ℤ) : ZMod p) * a j) • Pi.single i 1 := by
      rw [← TableBExc.torusRefl_eq_torusAct hsymm]
      rfl
    rw [htc, map_sub, map_smul, hΨ_single i, hsum i a, hlin i, Module.reflection_apply]
  have hW : ∀ w a, Ψ (TableBExc.torusAct τ p w a) =
      ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) (Ψ a) := by
    intro w a
    obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective w
    induction ω with
    | nil =>
      rw [CoxeterSystem.wordProd_nil, TableBExc.torusAct_one]
      simp
    | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, TableBExc.torusAct_mul, hsimple i, ih]
      have harg : (↑(e (simple τ i)) : MulAut ↥Bs) * ↑(e ((coxeterSystem τ).wordProd ω)) =
          ↑(e (simple τ i * (coxeterSystem τ).wordProd ω)) := by
        rw [map_mul e]
        rfl
      rw [← LinearEquiv.mul_apply, ← map_mul, harg]
  refine ⟨Ψ, hΨ_single, hW, ?_⟩
  intro a ha w
  have hfix : ∀ i, TableBExc.torusAct τ p (simple τ i) a = a := by
    intro i
    have hc : (∑ j, ((τ.cartan j i : ℤ) : ZMod p) * a j) = 0 := by
      rw [hsum i a, ha, map_zero]
    rw [← TableBExc.torusRefl_eq_torusAct hsymm, TableBExc.torusRefl, hc, zero_smul]
    simp
  obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective w
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, TableBExc.torusAct_one]
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, TableBExc.torusAct_mul, ih, hfix i]

theorem ggLin_sub_mem_span_of_simple {τ : Tag} {A : Subgroup (MulAut ↥Bs)} (e : WeylGroup τ ≃* ↥A)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V)
    (h : Fin τ.rank → V) (α : Fin τ.rank → Module.Dual (ZMod p) V) (hα : ∀ i, α i (h i) = 2)
    (hlin : ∀ i, ggLin (p := p) ιV ((e (simple τ i) : ↥A) : MulAut ↥Bs) =
      Module.reflection (hα i)) (w : WeylGroup τ) (v : V) :
    ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v - v ∈ Submodule.span (ZMod p) (Set.range h) := by
  let S : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  have hS : ∀ i, h i ∈ S := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hTs : ∀ i (x : V),
      ggLin (p := p) ιV ((e (simple τ i) : ↥A) : MulAut ↥Bs) x - x ∈ S := by
    intro i x
    rw [hlin i, Module.reflection_apply]
    have : x - (α i) x • h i - x = -((α i) x • h i) := by abel
    rw [this]
    exact S.neg_mem (S.smul_mem _ (hS i))
  have hmain : ∀ w : WeylGroup τ, ∀ v : V,
      ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v - v ∈ S := by
    intro w
    refine (coxeterSystem τ).simple_induction_left (p := fun w => ∀ v : V,
      ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v - v ∈ S) w ?_ ?_
    · intro v
      simp
    · intro w i ih v
      have he : ((e (simple τ i * w) : ↥A) : MulAut ↥Bs)
          = ((e (simple τ i) : ↥A) : MulAut ↥Bs) * ((e w : ↥A) : MulAut ↥Bs) := by
        simp
      rw [he, map_mul, LinearEquiv.mul_apply]
      have h1 : ggLin (p := p) ιV ((e (simple τ i) : ↥A) : MulAut ↥Bs)
          (ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v)
          - ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v ∈ S := hTs i _
      have h2 : ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v - v ∈ S := ih v
      have hsum : ggLin (p := p) ιV ((e (simple τ i) : ↥A) : MulAut ↥Bs)
            (ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v) - v
          = (ggLin (p := p) ιV ((e (simple τ i) : ↥A) : MulAut ↥Bs)
              (ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v)
              - ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v)
            + (ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v - v) := by abel
      rw [hsum]
      exact S.add_mem h1 h2
  exact hmain w v

theorem natCard_fix_torusMulAut_of_reflection [Finite G] (hp2 : p ≠ 2) {τ : Tag}
    {A : Subgroup (MulAut ↥Bs)} (e : WeylGroup τ ≃* ↥A) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) (h : Fin τ.rank → V)
    (Ψ : (Fin τ.rank → ZMod p) →ₗ[ZMod p] V) (hΨ : ∀ j, Ψ (Pi.single j 1) = h j)
    (hΨW : ∀ w a, Ψ (TableBExc.torusAct τ p w a) =
      ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) (Ψ a))
    (hker : ∀ a, Ψ a = 0 → ∀ w, TableBExc.torusAct τ p w a = a)
    (hspan : ∀ w : WeylGroup τ, ∀ v : V,
      ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) v - v ∈ Submodule.span (ZMod p) (Set.range h))
    {w : WeylGroup τ} (hrefl : GGIsReflection p ((e w : ↥A) : MulAut ↥Bs)) :
    Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ExcWeylOuter.torusMulAut τ p w f = f} = p ^ (τ.rank - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite ↥Bs := Subtype.finite
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  obtain ⟨x, f, hfx, hT⟩ := exists_of_ggIsReflection (p := p) ιV hrefl
  obtain ⟨hx0, hf0⟩ := ne_zero_of_apply_eq_two (p := p) hp2 hfx
  have hww : w * w = 1 := by
    have hh := hrefl.1
    rw [pow_two] at hh
    apply e.injective
    apply Subtype.ext
    simpa [map_mul, pow_two] using hh
  let act : (Fin τ.rank → ZMod p) →ₗ[ZMod p] (Fin τ.rank → ZMod p) :=
    Matrix.mulVecLin ((weylLatticeMatrix τ w).map (Int.castRingHom (ZMod p)))
  have hact : ∀ a, act a = TableBExc.torusAct τ p w a := by
    intro a
    rw [Matrix.mulVecLin_apply, torusAct_eq_weylMatrix_mulVec]
  let N : (Fin τ.rank → ZMod p) →ₗ[ZMod p] (Fin τ.rank → ZMod p) :=
    { toFun := fun a => act a - a
      map_add' := by intro a b; simp only [map_add]; abel
      map_smul' := by intro c a; simp only [map_smul, smul_sub, RingHom.id_apply] }
  have hN_apply : ∀ a, N a = act a - a := fun a => rfl
  have hact2 : ∀ a, act (act a) = a := by
    intro a
    rw [hact, hact, ← TableBExc.torusAct_mul, hww, TableBExc.torusAct_one]
  have hN2 : ∀ a, N (N a) = -(2 : ZMod p) • N a := by
    intro a
    rw [hN_apply, hN_apply, map_sub, hact2]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : (a i - act a i) - (act a i - a i) = 2 * (a i - act a i) := by
      rw [two_mul]; abel
    have h2 : -(2 : ZMod p) * (act a i - a i) = 2 * (a i - act a i) := by
      rw [← neg_sub (a i) (act a i), neg_mul, mul_neg, neg_neg]
    rw [h1, h2]
  have hxmem : x ∈ Submodule.span (ZMod p) (Set.range h) := by
    have hh := hspan w x
    have hTx : ggLin (p := p) ιV ((e w : ↥A) : MulAut ↥Bs) x - x = -(f x • x) := by
      rw [hT x]
      abel
    rw [hTx, hfx] at hh
    have h2 : (2 : ZMod p) • x ∈ Submodule.span (ZMod p) (Set.range h) := by
      simpa using Submodule.neg_mem _ hh
    have h3 : (2 : ZMod p)⁻¹ • ((2 : ZMod p) • x) ∈ Submodule.span (ZMod p) (Set.range h) :=
      Submodule.smul_mem _ _ h2
    rwa [smul_smul, inv_mul_cancel₀ (zmod_two_ne_zero hp2), one_smul] at h3
  have hΨc : ∀ c : Fin τ.rank → ZMod p, Ψ c = ∑ j, c j • h j := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hs : (Pi.single j (c j) : Fin τ.rank → ZMod p) = c j • Pi.single j 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hs, map_smul, hΨ]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hxmem
  have hΨcx : Ψ c = x := by rw [hΨc c, hc]
  let a₀ : Fin τ.rank → ZMod p := (2 : ZMod p)⁻¹ • c
  have hΨa₀ : Ψ a₀ = (2 : ZMod p)⁻¹ • x := by
    change Ψ ((2 : ZMod p)⁻¹ • c) = _
    rw [map_smul, hΨcx]
  have hga₀ : f (Ψ a₀) = 1 := by
    rw [hΨa₀, map_smul, hfx, smul_eq_mul, inv_mul_cancel₀ (zmod_two_ne_zero hp2)]
  have hΨN : ∀ a, Ψ (N a) = -(f (Ψ a)) • x := by
    intro a
    rw [hN_apply, hact, map_sub, hΨW w a, hT (Ψ a)]
    have h1 : (Ψ a - f (Ψ a) • x) - Ψ a = -(f (Ψ a) • x) := by abel
    rw [h1, neg_smul]
  have hzero : ∀ a, f (Ψ a) = 0 → N a = 0 := by
    intro a hga
    have hΨNa : Ψ (N a) = 0 := by rw [hΨN a, hga, neg_zero, zero_smul]
    have hfix : act (N a) = N a := by
      have hh := hker (N a) hΨNa w
      rwa [← hact] at hh
    have hNN : N (N a) = 0 := by
      rw [hN_apply (N a), hfix, sub_self]
    rw [hN2 a] at hNN
    exact (smul_eq_zero.mp hNN).resolve_left (neg_ne_zero.mpr (zmod_two_ne_zero hp2))
  have hNa₀_ne : N a₀ ≠ 0 := by
    intro h0
    have hΨ0 : Ψ (N a₀) = 0 := by rw [h0, map_zero]
    rw [hΨN a₀, hga₀, neg_one_smul] at hΨ0
    exact hx0 (neg_eq_zero.mp hΨ0)
  have hN_eq : ∀ a, N a = f (Ψ a) • N a₀ := by
    intro a
    have hz : f (Ψ (a - f (Ψ a) • a₀)) = 0 := by
      rw [map_sub Ψ, map_smul Ψ, map_sub f, map_smul f, hga₀,
        smul_eq_mul, mul_one, sub_self]
    have h0 := hzero (a - f (Ψ a) • a₀) hz
    rw [map_sub N, map_smul N] at h0
    exact sub_eq_zero.mp h0
  have hrange : N.range = Submodule.span (ZMod p) {N a₀} := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      rw [hN_eq a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨a₀, rfl⟩
  have hcard_range : Nat.card ↥N.toAddMonoidHom.range = p := by
    let φ := LinearMap.toSpanSingleton (ZMod p) (Fin τ.rank → ZMod p) (N a₀)
    have hker1 : Nat.card ↥φ.toAddMonoidHom.ker = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun u v => Subtype.ext ?_⟩, ⟨⟨0, by simp [φ]⟩⟩⟩
      have hu : u.1 = 0 := by
        have hu0 : φ u.1 = 0 := u.2
        rw [LinearMap.toSpanSingleton_apply] at hu0
        rcases smul_eq_zero.mp hu0 with h0 | h0
        · exact h0
        · exact absurd h0 hNa₀_ne
      have hv : v.1 = 0 := by
        have hv0 : φ v.1 = 0 := v.2
        rw [LinearMap.toSpanSingleton_apply] at hv0
        rcases smul_eq_zero.mp hv0 with h0 | h0
        · exact h0
        · exact absurd h0 hNa₀_ne
      rw [hu, hv]
    have hφcard : Nat.card ↥φ.toAddMonoidHom.range = p := by
      have h2 := AddSubgroup.card_ker_mul_card_range φ.toAddMonoidHom
      rw [hker1, one_mul, Nat.card_zmod] at h2
      exact h2
    have h1 : Nat.card ↥N.toAddMonoidHom.range =
        Nat.card ↥(Submodule.span (ZMod p) {N a₀}) := by
      rw [← hrange]; rfl
    have h2 : Nat.card ↥φ.toAddMonoidHom.range =
        Nat.card ↥(Submodule.span (ZMod p) {N a₀}) := by
      rw [show (Submodule.span (ZMod p) {N a₀}) = φ.range by
        rw [LinearMap.range_toSpanSingleton]]
      rfl
    rw [h1, ← h2]
    exact hφcard
  have hrank_pos : 0 < τ.rank := by
    by_contra hlt
    have h0 : τ.rank = 0 := Nat.eq_zero_of_not_pos hlt
    haveI : Subsingleton (Fin τ.rank → ZMod p) := by
      constructor
      intro u v
      funext i
      exact absurd i.2 (by omega)
    exact hNa₀_ne (Subsingleton.elim _ _)
  have hcardU : Nat.card (Fin τ.rank → ZMod p) = p ^ τ.rank := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, Module.finrank_fin_fun]
  have hcard_ker : Nat.card ↥N.toAddMonoidHom.ker = p ^ (τ.rank - 1) := by
    have h2 := AddSubgroup.card_ker_mul_card_range N.toAddMonoidHom
    rw [hcard_range, hcardU] at h2
    apply Nat.mul_right_cancel (Fact.out : p.Prime).pos
    rw [h2, ← pow_succ, Nat.sub_add_cancel hrank_pos]
  have hcard_fix : Nat.card {a : Fin τ.rank → ZMod p // act a = a} = p ^ (τ.rank - 1) := by
    have hker_eq : Nat.card {a : Fin τ.rank → ZMod p // act a = a} = Nat.card ↥N.ker :=
      Nat.card_congr (Equiv.subtypeEquivRight fun a => by
        show act a = a ↔ act a - a = 0
        exact sub_eq_zero.symm)
    rw [hker_eq]
    exact hcard_ker
  rw [natCard_fix_torusMulAut_eq w]
  have hmat : Nat.card {f : Fin τ.rank → ZMod p //
      Matrix.mulVec ((weylLatticeMatrix τ w).map (Int.castRingHom (ZMod p))) f = f} =
      Nat.card {f : Fin τ.rank → ZMod p // act f = f} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    show (Matrix.mulVec ((weylLatticeMatrix τ w).map (Int.castRingHom (ZMod p))) f = f) ↔
      act f = f
    rw [hact f, torusAct_eq_weylMatrix_mulVec]
  rw [hmat, hcard_fix]

theorem rootReflection_mul_pow_two_or_three {τ : Tag} (hτ : ∀ i, τ.symmetrizer i i = 1)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hne : β ≠ γ)
    (hne' : β ≠ -γ) :
    (rootReflection β * rootReflection γ) ^ 2 = 1 ∨
      (rootReflection β * rootReflection γ) ^ 3 = 1 := by
  rcases CFSG.LieType.Chevalley.SimplyLacedCover.iform_mem hτ hβ hγ hne hne' with
    hneg | hzero | hpos
  · right
    have hpair := ra_isA2Pair_of_iform_neg hτ hβ hγ hneg
    have h3 := CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair.pairRefl_pow_three hpair
    change (rootReflection β * rootReflection γ) ^ 3 = 1 at h3
    exact h3
  · left
    have hc := rootReflection_commute_of_iform_eq_zero hβ hγ hzero
    rw [hc.mul_pow, pow_two (rootReflection β), pow_two (rootReflection γ),
      rootReflection_mul_self hβ, rootReflection_mul_self hγ, one_mul]
  · right
    have hif : iform β (-γ) = -1 := by rw [iform_neg_right, hpos]
    have hpair := ra_isA2Pair_of_iform_neg hτ hβ (IsRoot.neg hγ) hif
    have h3 := CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair.pairRefl_pow_three hpair
    change (rootReflection β * rootReflection (-γ)) ^ 3 = 1 at h3
    rw [rootReflection_neg hγ] at h3
    exact h3

private theorem rd_main [Finite G] (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {τ : Tag}
    (hτ1 : ∀ i, τ.symmetrizer i i = 1)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (hr : 0 < τ.rank)
    (hsl : ∀ i j, i ≠ j → τ.cartan i j = 0 ∨ τ.cartan i j = -1)
    (hC : GGIntCartan (coxeterMatrix (isFiniteType_cartan τ)) τ.cartan)
    (par : Fin τ.rank → Fin τ.rank) (root : Fin τ.rank) (depth : Fin τ.rank → ℕ)
    (hpar : ∀ i j, i ≠ j →
      (τ.cartan i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i)
    {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType p (coxeterMatrix (isFiniteType_cartan τ)) A)
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {t s : MulAut ↥Bs} (ht : t ∈ A) (hs : s ∈ A)
    (htr : GGIsReflection p t) (hsr : GGIsReflection p s) (hts : orderOf (t * s) = 4) :
    False := by
  haveI : Finite ↥Bs := Subtype.finite
  obtain ⟨V, iA, iM, ⟨ιV⟩⟩ := CFSG.StandardType.exists_ggLinData (p := p) hBs
  letI : AddCommGroup V := iA
  letI : Module (ZMod p) V := iM
  obtain ⟨e, h, α, hα, hlin, hP⟩ :=
    exists_cartan_pairing_of_weylOfType (p := p) hp2 hNT hC hsl par root depth hpar hdepth hW
      hind ιV
  obtain ⟨Ψ, hΨ1, hΨW, hker⟩ := exists_torus_intertwiner hsymm e ιV h α hα hlin hP
  have hspan := ggLin_sub_mem_span_of_simple e ιV h α hα hlin
  have hroot : ∀ (u : MulAut ↥Bs) (hu : u ∈ A), GGIsReflection p u →
      ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ e.symm ⟨u, hu⟩ = rootReflection β := by
    intro u hu hurefl
    let w : WeylGroup τ := e.symm ⟨u, hu⟩
    have hew : e w = ⟨u, hu⟩ := e.apply_symm_apply ⟨u, hu⟩
    have hcoe : ((e w : ↥A) : MulAut ↥Bs) = u := congrArg Subtype.val hew
    have hww : w * w = 1 := by
      apply e.injective
      rw [map_mul, map_one, hew]
      apply Subtype.ext
      simpa [pow_two, Subgroup.coe_mul] using hurefl.1
    have hw1 : w ≠ 1 := by
      intro h1
      have hu1 : u = 1 := by
        rw [← hcoe, h1]
        simp
      have hfix : Nat.card {b : ↥Bs // u b = b} = Nat.card ↥Bs := by
        rw [hu1]
        simp
      have h2 := hurefl.2
      rw [hfix] at h2
      have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
      have hp1 : p = 1 := Nat.mul_left_cancel hpos (by rw [h2, mul_one])
      exact (Fact.out : p.Prime).ne_one hp1
    have hfix : Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
        ExcWeylOuter.torusMulAut τ p w f = f} = p ^ (τ.rank - 1) :=
      natCard_fix_torusMulAut_of_reflection (p := p) hp2 e ιV h Ψ hΨ1 hΨW hker hspan
        (by rw [hcoe]; exact hurefl)
    obtain ⟨β, hβ, hwβ⟩ :=
      CFSG.StandardType.exists_rootReflection_of_natCard_fix_torusMulAut (p := p) hp2 hτ1 hr
        hww hw1 hfix
    exact ⟨β, hβ, hwβ⟩
  obtain ⟨β, hβ, hβeq⟩ := hroot t ht htr
  obtain ⟨γ, hγ, hγeq⟩ := hroot s hs hsr
  have ht_eq : ((e (rootReflection β) : ↥A) : MulAut ↥Bs) = t := by
    have h1 : e (rootReflection β) = ⟨t, ht⟩ := by
      rw [← hβeq]
      exact e.apply_symm_apply ⟨t, ht⟩
    exact congrArg Subtype.val h1
  have hs_eq : ((e (rootReflection γ) : ↥A) : MulAut ↥Bs) = s := by
    have h1 : e (rootReflection γ) = ⟨s, hs⟩ := by
      rw [← hγeq]
      exact e.apply_symm_apply ⟨s, hs⟩
    exact congrArg Subtype.val h1
  have hts_eq : t * s = ((e (rootReflection β * rootReflection γ) : ↥A) : MulAut ↥Bs) := by
    rw [← ht_eq, ← hs_eq, ← Subgroup.coe_mul, ← map_mul]
  have hpow : ((t * s) ^ 2 = 1 ∨ (t * s) ^ 3 = 1) := by
    by_cases hbc : β = γ
    · left
      have hX : rootReflection β * rootReflection γ = 1 := by
        rw [hbc, rootReflection_mul_self hγ]
      rw [hts_eq, hX, map_one]
      simp
    · by_cases hbn : β = -γ
      · left
        have hX : rootReflection β * rootReflection γ = 1 := by
          rw [hbn, rootReflection_neg hγ, rootReflection_mul_self hγ]
        rw [hts_eq, hX, map_one]
        simp
      · rcases rootReflection_mul_pow_two_or_three hτ1 hβ hγ hbc hbn with h2 | h3
        · left
          rw [hts_eq, ← Subgroup.coe_pow, ← map_pow, h2, map_one]
          simp
        · right
          rw [hts_eq, ← Subgroup.coe_pow, ← map_pow, h3, map_one]
          simp
  rcases hpow with h2 | h3
  · have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hts] at hd
    omega
  · have hd := orderOf_dvd_of_pow_eq_one h3
    rw [hts] at hd
    omega

theorem not_weylOfType_tag_of_order_four [Finite G] (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType p (coxeterMatrix (isFiniteType_cartan τ)) A)
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {t s : MulAut ↥Bs} (ht : t ∈ A) (hs : s ∈ A)
    (htr : GGIsReflection p t) (hsr : GGIsReflection p s) (hts : orderOf (t * s) = 4) :
    False := by
  rcases hτ with rfl | rfl | rfl
  · exact rd_main (p := p) hp2 hBs hNT (by decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> decide)
      (by decide)
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp only [Tag.cartan, Tag.cartanE, Fin.ext_iff] at hij ⊢ <;> omega)
      (ggIntCartan_tag_E (Or.inl rfl))
      excTreeParentE6 excTreeRootE6 (fun i => excTreeDepthNat i.val)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> decide)
      (by decide)
      hW hind ht hs htr hsr hts
  · exact rd_main (p := p) hp2 hBs hNT (by decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> decide)
      (by decide)
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp only [Tag.cartan, Tag.cartanE, Fin.ext_iff] at hij ⊢ <;> omega)
      (ggIntCartan_tag_E (Or.inr (Or.inl rfl)))
      excTreeParentE7 excTreeRootE7 (fun i => excTreeDepthNat i.val)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> decide)
      (by decide)
      hW hind ht hs htr hsr hts
  · exact rd_main (p := p) hp2 hBs hNT (by decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> decide)
      (by decide)
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp only [Tag.cartan, Tag.cartanE, Fin.ext_iff] at hij ⊢ <;> omega)
      (ggIntCartan_tag_E (Or.inr (Or.inr rfl)))
      excTreeParentE8 excTreeRootE8 (fun i => excTreeDepthNat i.val)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> decide)
      (by decide)
      hW hind ht hs htr hsr hts

end TypeE

end CFSG.StandardType.SpJoinRefl
