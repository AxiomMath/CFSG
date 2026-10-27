module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcWeylWords
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeAParabolicLE3

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley

@[expose] def e8LeviDel : Finset (Finset (Fin 8)) :=
  {{0}, {1}, {7}, {0, 1}, {0, 2}, {1, 7}, {0, 7}, {6, 7}}


@[expose] def e8A8Nodes : Finset (Option (Fin Tag.E8.rank)) :=
  {none, some 7, some 6, some 5, some 4, some 3, some 2, some 0}

@[expose] def ggRootAnn (p : ℕ) {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) :
    Submodule (ZMod p) (Fin τ.rank → ZMod p) where
  carrier := {t | ∀ γ ∈ Ψ, ∑ j, (γ j : ZMod p) * t j = 0}
  add_mem' := by
    intro s t hs ht γ hγ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hs γ hγ, ht γ hγ, add_zero]
  zero_mem' := by
    intro γ _
    simp
  smul_mem' := by
    intro c t ht γ hγ
    simp only [Pi.smul_apply, smul_eq_mul]
    calc ∑ j, (γ j : ZMod p) * (c * t j) = c * ∑ j, (γ j : ZMod p) * t j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [ht γ hγ, mul_zero]

section Count

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem finrank_range_add_finrank_ker_fin {K : Type} [Field K] (r m : ℕ)
    (T : (Fin r → K) →ₗ[K] (Fin m → K)) :
    Module.finrank K (LinearMap.range T) + Module.finrank K T.ker = r := by
  simpa using LinearMap.finrank_range_add_finrank_ker T

theorem le_compRank_of_finrank_ggRootAnn {τ : Tag} {p : ℕ} [Fact p.Prime]
    (Ψ : Set (Fin τ.rank → ℤ)) {d : ℕ} (h : Module.finrank (ZMod p) (ggRootAnn p Ψ) ≤ d) :
    τ.rank - d ≤ compRank Ψ := by
  classical
  let N : Submodule ℤ (Fin τ.rank → ℤ) := Submodule.span ℤ Ψ
  let V : Submodule ℚ (Fin τ.rank → ℚ) :=
    Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ)
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin τ.rank)) N
  let castQ : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℚ) :=
    { toFun := fun x i => (x i : ℚ)
      map_add' := by
        intro x y
        funext i
        simp
      map_smul' := by
        intro c x
        funext i
        simp [Int.cast_mul, zsmul_eq_mul] }
  have hLker : (castQ.comp N.subtype).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    funext j
    have hxj : ((x : Fin τ.rank → ℤ) j : ℚ) = 0 := by
      have := congrFun hx j
      simpa [castQ] using this
    exact Int.cast_eq_zero.mp hxj
  have hZ : LinearIndependent ℤ (fun i : Fin m => castQ (b i : Fin τ.rank → ℤ)) :=
    LinearIndependent.map' b.linearIndependent (castQ.comp N.subtype) hLker
  have hQ : LinearIndependent ℚ (fun i : Fin m => castQ (b i : Fin τ.rank → ℤ)) :=
    (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mp hZ
  have hcard : m ≤ Set.finrank ℚ
      (Set.range fun i : Fin m => castQ (b i : Fin τ.rank → ℤ)) := by
    have := linearIndependent_iff_card_le_finrank_span.mp hQ
    simpa only [Fintype.card_fin] using this
  have hcomap : N ≤ (V.restrictScalars ℤ).comap castQ := by
    change Submodule.span ℤ Ψ ≤ (V.restrictScalars ℤ).comap castQ
    rw [Submodule.span_le]
    intro γ hγ
    exact (Submodule.restrictScalars_mem ℤ V (castQ γ)).mpr
      (Submodule.subset_span (Set.mem_image_of_mem (fun γ (i : Fin τ.rank) => (γ i : ℚ)) hγ))
  have hmem : ∀ i : Fin m, castQ (b i : Fin τ.rank → ℤ) ∈ V := fun i =>
    (Submodule.restrictScalars_mem ℤ V _).mp (hcomap (b i).2)
  have hspan_le : Submodule.span ℚ
      (Set.range fun i : Fin m => castQ (b i : Fin τ.rank → ℤ)) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hmk : m ≤ compRank Ψ := by
    have hle : Set.finrank ℚ (Set.range fun i : Fin m => castQ (b i : Fin τ.rank → ℤ)) ≤
        Module.finrank ℚ V := by
      show Module.finrank ℚ (Submodule.span ℚ
        (Set.range fun i : Fin m => castQ (b i : Fin τ.rank → ℤ))) ≤ Module.finrank ℚ V
      exact Submodule.finrank_mono hspan_le
    exact le_trans hcard hle
  let T : (Fin τ.rank → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p) :=
    { toFun := fun t i => ∑ j, ((b i : Fin τ.rank → ℤ) j : ZMod p) * t j
      map_add' := by
        intro s t
        funext i
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c t
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        exact Finset.sum_congr rfl fun j _ => by ring }
  have hNspan : N = Submodule.span ℤ (Set.range fun i : Fin m => (b i : Fin τ.rank → ℤ)) := by
    conv_lhs =>
      rw [← Submodule.range_subtype N, ← Submodule.map_top N.subtype, ← b.span_eq]
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hker_le : T.ker ≤ ggRootAnn p Ψ := by
    intro t ht
    rw [LinearMap.mem_ker] at ht
    intro γ hγ
    let dot : (Fin τ.rank → ℤ) →ₗ[ℤ] ZMod p :=
      { toFun := fun x => ∑ j, (x j : ZMod p) * t j
        map_add' := by
          intro x y
          simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro c x
          simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul,
            Finset.mul_sum, RingHom.id_apply]
          exact Finset.sum_congr rfl fun j _ => by ring }
    have hbt : ∀ i : Fin m, dot (b i : Fin τ.rank → ℤ) = 0 := fun i =>
      congrFun ht i
    have hle : Submodule.span ℤ (Set.range fun i : Fin m => (b i : Fin τ.rank → ℤ)) ≤
        LinearMap.ker dot := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (hbt i)
    have hNle : N ≤ LinearMap.ker dot := hNspan.le.trans hle
    exact LinearMap.mem_ker.mp (hNle (Submodule.subset_span hγ))
  have hsum : Module.finrank (ZMod p) (LinearMap.range T) +
      Module.finrank (ZMod p) T.ker = τ.rank :=
    finrank_range_add_finrank_ker_fin τ.rank m T
  have hrange : Module.finrank (ZMod p) (LinearMap.range T) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range T)
    simpa using this
  have hAnn : τ.rank - m ≤ Module.finrank (ZMod p) (ggRootAnn p Ψ) :=
    le_trans (by omega) (Submodule.finrank_mono hker_le)
  omega

end Count

section Refl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem rootReflection_mem_parabolicWeylGroup
    {τ : Tag} {J : Set (Fin τ.rank)} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ parabolicRoots τ J) :
    rootReflection γ ∈ parabolicWeylGroup τ J := by
  refine (mem_parabolicWeylGroup_of_coord (A := J)
    (n := (coxeterSystem τ).length (rootReflection γ)) (rootReflection γ) rfl ?_).1
  intro v i hi
  rw [rootReflection_smul hγ.1]
  simp [hγ.2 i hi]

private theorem closure_rootReflection_parabolicRoots
    {τ : Tag} (J : Set (Fin τ.rank)) :
    Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ parabolicRoots τ J, s = rootReflection γ} =
      parabolicWeylGroup τ J := by
  refine le_antisymm (Subgroup.closure_le _ |>.2 ?_) ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    exact rootReflection_mem_parabolicWeylGroup hγ
  · rw [show parabolicWeylGroup τ J = Subgroup.closure (simple τ '' J) from rfl]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨Pi.single j 1, ⟨IsRoot.basis j, fun i hi => ?_⟩, ?_⟩
    · exact Pi.single_eq_of_ne (fun h => hi (by rw [h]; exact hj)) 1
    · rw [rootReflection_eq_conj (β := Pi.single j 1) (w := 1) (j := j) (by simp)]
      simp

theorem map_conj_parabolicWeylGroup
    {τ : Tag} (v : WeylGroup τ) (J : Set (Fin τ.rank)) :
    Subgroup.map (MulAut.conj v).toMonoidHom (parabolicWeylGroup τ J) =
      Subgroup.closure ((fun j => v * simple τ j * v⁻¹) '' J) := by
  have hfun : (fun x => (MulAut.conj v).toMonoidHom (simple τ x)) =
      fun j => v * simple τ j * v⁻¹ := by
    funext j
    exact MulAut.conj_apply v (simple τ j)
  rw [show parabolicWeylGroup τ J = Subgroup.closure (simple τ '' J) from rfl,
    MonoidHom.map_closure, Set.image_image, hfun]

theorem closure_rootReflection_smul_parabolicRoots
    {τ : Tag} (v : WeylGroup τ) (Jset : Set (Fin τ.rank)) :
    Subgroup.closure {s : WeylGroup τ |
        ∃ γ ∈ (fun α => v • α) '' parabolicRoots τ Jset, s = rootReflection γ} =
      Subgroup.closure ((fun j => v * simple τ j * v⁻¹) '' Jset) := by
  have hset : (MulAut.conj v) '' {s : WeylGroup τ |
        ∃ γ ∈ parabolicRoots τ Jset, s = rootReflection γ} =
      {s : WeylGroup τ |
        ∃ γ ∈ (fun α => v • α) '' parabolicRoots τ Jset, s = rootReflection γ} := by
    ext s
    constructor
    · rintro ⟨t, ⟨γ, hγ, ht⟩, hts⟩
      subst ht
      refine ⟨v • γ, ⟨γ, hγ, rfl⟩, ?_⟩
      rw [← hts, MulAut.conj_apply, rootReflection_smul_root v hγ.1]
    · rintro ⟨γ, ⟨α, hα, hγα⟩, hγs⟩
      subst hγα
      refine ⟨rootReflection α, ⟨α, hα, rfl⟩, ?_⟩
      rw [hγs, MulAut.conj_apply, rootReflection_smul_root v hα.1]
  calc Subgroup.closure {s : WeylGroup τ |
          ∃ γ ∈ (fun α => v • α) '' parabolicRoots τ Jset, s = rootReflection γ}
      = Subgroup.closure ((MulAut.conj v) '' {s : WeylGroup τ |
          ∃ γ ∈ parabolicRoots τ Jset, s = rootReflection γ}) := by rw [hset]
    _ = Subgroup.map (MulAut.conj v).toMonoidHom (Subgroup.closure {s : WeylGroup τ |
          ∃ γ ∈ parabolicRoots τ Jset, s = rootReflection γ}) := by
        rw [MonoidHom.map_closure]
        rfl
    _ = Subgroup.map (MulAut.conj v).toMonoidHom (parabolicWeylGroup τ Jset) := by
        rw [closure_rootReflection_parabolicRoots (τ := τ) Jset]
    _ = Subgroup.closure ((fun j => v * simple τ j * v⁻¹) '' Jset) :=
        map_conj_parabolicWeylGroup v Jset

end Refl

section Kac

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.AlgebraicGroups (rootCharHom)
open CFSG.RankThree.Lattice CFSG.HardMathSupport.Curtis.UnitaryLevi
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootChar_nsmul_single)

section

private def e8Theta : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

private theorem e8Theta_eq :
    kacE8.θ = e8Theta := rfl

open scoped CFSG.Decide.Bounded in
private theorem e8_conn_cases : ∀ c ∈ e8Conn, 6 ≤ c.length → c.length ≤ 8 →
    c = [0, 2, 4, 5, 6, 7, 8] ∨ c = [0, 2, 3, 4, 5, 6, 7, 8] ∨ c = [0, 1, 3, 4, 5, 6, 7, 8] ∨
    c = [0, 4, 5, 6, 7, 8] ∨ c = [0, 3, 4, 5, 6, 7, 8] ∨ c = [1, 2, 3, 4, 5, 6] ∨
    c = [1, 3, 4, 5, 6, 7] ∨ c = [2, 3, 4, 5, 6, 7] ∨ c = [2, 4, 5, 6, 7, 8] ∨
    c = [3, 4, 5, 6, 7, 8] ∨ c = [1, 2, 3, 4, 5, 6, 7] ∨ c = [1, 3, 4, 5, 6, 7, 8] ∨
    c = [2, 3, 4, 5, 6, 7, 8] ∨ c = [1, 2, 3, 4, 5, 6, 7, 8] := by
  decide +kernel

private def e8LeviDel' : Finset (Finset (Fin Tag.E8.rank)) :=
  {{0}, {1}, {7}, {0, 1}, {0, 2}, {1, 7}, {0, 7}, {6, 7}}

open scoped CFSG.Decide.Bounded in
private theorem e8_levi_del_cases : ∀ c ∈ e8Conn, 6 ≤ c.length → c.length ≤ 7 → 0 ∉ c →
    ∃ S ∈ e8LeviDel', ∀ j : Fin Tag.E8.rank,
      some j ∈ ((c.map (idxNode (r := Tag.E8.rank))).toFinset :
        Finset (Option (Fin Tag.E8.rank))) ↔ j ∉ S := by
  decide +kernel

private def wordAct :
    List (Fin Tag.E8.rank) → (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ)
  | [], v => v
  | i :: l, v => reflect .E8 i (wordAct l v)

private def e8Word6 : List (Fin Tag.E8.rank) :=
  [2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4,
    5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2]

private def e8Word7 : List (Fin Tag.E8.rank) :=
  [1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3, 0, 2, 1, 3,
    4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]

private def e8Nodes6 : Finset (Option (Fin Tag.E8.rank)) :=
  {none, some 3, some 4, some 5, some 6, some 7}

private def e8Nodes7 : Finset (Option (Fin Tag.E8.rank)) :=
  {none, some 2, some 3, some 4, some 5, some 6, some 7}

private def e8Del6 : Finset (Fin Tag.E8.rank) := {0, 2}

private def e8Del7 : Finset (Fin Tag.E8.rank) := {1}

private theorem e8Del6_mem : e8Del6 ∈ e8LeviDel' := by decide +kernel

private theorem e8Del7_mem : e8Del7 ∈ e8LeviDel' := by decide +kernel

private theorem wordW_smul_wordAct
    (l : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    wordW .E8 l • v = wordAct l v := by
  induction l with
  | nil => simp [wordW, wordAct]
  | cons i l ih =>
    have h1 : wordW .E8 (i :: l) = simple .E8 i * wordW .E8 l := rfl
    rw [h1, mul_smul, ih, simple_smul]
    rfl

private theorem wordW_reverse
    (l : List (Fin Tag.E8.rank)) :
    wordW .E8 l.reverse = (wordW .E8 l)⁻¹ := by
  induction l with
  | nil => simp [wordW]
  | cons i l ih =>
    have h1 : wordW .E8 (i :: l) = simple .E8 i * wordW .E8 l := rfl
    have h2 : wordW .E8 [i] = simple .E8 i := rfl
    rw [List.reverse_cons, wordW_append, ih, h1, h2, mul_inv_rev, simple_inv]

open scoped CFSG.Decide.Bounded in
private theorem e8Check6M : ∀ l ∈ Tag.E8.artifactRoots,
    (kacTest e8Theta e8Nodes6 (toVec Tag.E8.rank l) ↔
      ∀ j ∈ e8Del6, (wordAct e8Word6 (toVec Tag.E8.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e8Check6N : ∀ l ∈ Tag.E8.artifactRoots,
    (kacTest e8Theta e8Nodes6 (wordAct e8Word6.reverse (toVec Tag.E8.rank l)) ↔
      ∀ j ∈ e8Del6, (toVec Tag.E8.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e8Check7M : ∀ l ∈ Tag.E8.artifactRoots,
    (kacTest e8Theta e8Nodes7 (toVec Tag.E8.rank l) ↔
      ∀ j ∈ e8Del7, (wordAct e8Word7 (toVec Tag.E8.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e8Check7N : ∀ l ∈ Tag.E8.artifactRoots,
    (kacTest e8Theta e8Nodes7 (wordAct e8Word7.reverse (toVec Tag.E8.rank l)) ↔
      ∀ j ∈ e8Del7, (toVec Tag.E8.rank l) j = 0) := by
  decide +kernel

private theorem toVec_ofFn {n : ℕ} (f : Fin n → ℤ) : toVec n (List.ofFn f) = f := toVec_vofFn f

private theorem checkM_of_list
    {C : Finset (Option (Fin Tag.E8.rank))}
    {S : Finset (Fin Tag.E8.rank)} {l : List (Fin Tag.E8.rank)}
    (h : ∀ l' ∈ Tag.E8.artifactRoots,
      (kacTest e8Theta C (toVec Tag.E8.rank l') ↔
        ∀ j ∈ S, (wordAct l (toVec Tag.E8.rank l')) j = 0)) :
    ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ →
      (kacTest kacE8.θ C γ ↔ ∀ j ∈ S, (wordAct l γ) j = 0) := by
  intro γ hγ
  have hmem : List.ofFn γ ∈ Tag.E8.artifactRoots := (isRoot_iff_mem_artifactRoots (τ := .E8)).1 hγ
  have h' := h (List.ofFn γ) hmem
  rw [toVec_ofFn] at h'
  rwa [e8Theta_eq]

private theorem checkN_of_list
    {C : Finset (Option (Fin Tag.E8.rank))}
    {S : Finset (Fin Tag.E8.rank)} {l : List (Fin Tag.E8.rank)}
    (h : ∀ l' ∈ Tag.E8.artifactRoots,
      (kacTest e8Theta C (wordAct l.reverse (toVec Tag.E8.rank l')) ↔
        ∀ j ∈ S, (toVec Tag.E8.rank l') j = 0)) :
    ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ →
      (kacTest kacE8.θ C (wordAct l.reverse γ) ↔ ∀ j ∈ S, γ j = 0) := by
  intro γ hγ
  have hmem : List.ofFn γ ∈ Tag.E8.artifactRoots := (isRoot_iff_mem_artifactRoots (τ := .E8)).1 hγ
  have h' := h (List.ofFn γ) hmem
  rw [toVec_ofFn] at h'
  rwa [e8Theta_eq]

private theorem rootsOf_eq_image_parabolic
    (l : List (Fin Tag.E8.rank))
    (C : Finset (Option (Fin Tag.E8.rank))) (S : Finset (Fin Tag.E8.rank))
    (hC : ∃ y, y ∉ C)
    (hcheckM : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ →
      (kacTest kacE8.θ C γ ↔ ∀ j ∈ S, (wordAct l γ) j = 0))
    (hcheckN : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ →
      (kacTest kacE8.θ C (wordAct l.reverse γ) ↔ ∀ j ∈ S, γ j = 0)) :
    kacE8.rootsOf (C : Set (Option (Fin Tag.E8.rank))) =
      (fun α => wordW .E8 l.reverse • α) '' parabolicRoots .E8 {j : Fin Tag.E8.rank | j ∉ S} := by
  ext γ
  rw [mem_rootsOf_iff kacE8 facts_E8 hC]
  constructor
  · rintro ⟨hγ, htest⟩
    have hvan : ∀ j ∈ S, (wordAct l γ) j = 0 := (hcheckM γ hγ).1 htest
    refine ⟨wordAct l γ, ⟨?_, fun j hj => hvan j (by by_contra h; exact hj h)⟩, ?_⟩
    · rw [← wordW_smul_wordAct]
      exact IsRoot.smul hγ _
    · rw [wordW_reverse, ← wordW_smul_wordAct]
      exact inv_smul_smul (wordW .E8 l) γ
  · rintro ⟨δ, ⟨hδroot, hδvan⟩, rfl⟩
    have hvanS : ∀ j ∈ S, δ j = 0 := fun j hj => hδvan j (fun h => h hj)
    change IsRoot .E8 (wordW .E8 l.reverse • δ) ∧
      kacTest kacE8.θ C (wordW .E8 l.reverse • δ)
    refine ⟨IsRoot.smul hδroot _, ?_⟩
    rw [wordW_smul_wordAct]
    exact (hcheckN δ hδroot).2 hvanS

private theorem p_eq_sum_off
    {p : ℕ} {μ : Fin Tag.E8.rank → ℤ}
    {x : Option (Fin Tag.E8.rank)} {c : List ℕ}
    (hcomp : kacE8.comp p μ x = {y | nodeIdx y ∈ c}) (h0 : 0 ∈ c) :
    (p : ℤ) = ∑ j ∈ Finset.univ.filter (fun j : Fin Tag.E8.rank => (j : ℕ) + 1 ∉ c),
      kacE8.θ j * μ j := by
  have hθ : kacE8.θ ⬝ᵥ μ = (p : ℤ) := by
    have hmem : none ∈ kacE8.comp p μ x := by
      rw [hcomp]
      exact h0
    exact hmem.1
  rw [← hθ, dotProduct]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_).symm
  have hj' : (j : ℕ) + 1 ∈ c := by
    by_contra h
    exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, h⟩)
  have hzj : μ j = 0 := by
    have hmem : some j ∈ kacE8.comp p μ x := by
      rw [hcomp]
      exact hj'
    exact hmem.1
  rw [hzj, mul_zero]

private theorem rootsOf_eq_parabolic_of_forall
    {C : Finset (Option (Fin Tag.E8.rank))}
    (hnone : none ∉ C) {S : Finset (Fin Tag.E8.rank)}
    (hJ : ∀ j : Fin Tag.E8.rank, some j ∈ C ↔ j ∉ S) :
    kacE8.rootsOf (C : Set (Option (Fin Tag.E8.rank))) =
      parabolicRoots .E8 {j : Fin Tag.E8.rank | j ∉ S} := by
  rw [KacData.rootsOf_eq_parabolicRoots kacE8 hnone]
  congr 1
  ext j
  exact hJ j

private theorem false_of_two_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : 2 ∣ p) : False := by
  obtain h1 | h1 := Nat.Prime.eq_one_or_self_of_dvd (p := p) hp 2 h
  · norm_num at h1
  · exact hp2 h1.symm

end

theorem e8_class_levi_or_a8
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot (ζ : L) p) (a : Fin Tag.E8.rank → Lˣ) (ha : ∀ i, a i ^ p = 1)
    (ha1 : ∃ j, a j ≠ 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i)) :
    (∃ (v : WeylGroup .E8) (S : Finset (Fin 8)), S ∈ e8LeviDel ∧
        componentRoots (rootCharHom a) i =
          (fun α => v • α) '' parabolicRoots .E8 {j | j ∉ S}) ∨
      (p = 3 ∧ ∃ v : WeylGroup .E8, componentRoots (rootCharHom a) i =
          (fun α => v • α) '' kacE8.rootsOf (e8A8Nodes : Set (Option (Fin Tag.E8.rank)))) := by
  classical
  obtain ⟨v, μ, hμ, hi⟩ :=
    KacData.exists_smul_rootsOf (τ := Tag.E8) kacE8 facts_E8 hp.pos hζ a ha
  obtain ⟨x, hx, hcl⟩ := hi i
  obtain ⟨c, hc, hcomp⟩ :=
    kacE8.exists_comp_eq_of_check e8_tree e8_adj (adm := fun _ => true) e8_check rfl hx
  set C : Finset (Option (Fin Tag.E8.rank)) := (c.map (idxNode (r := Tag.E8.rank))).toFinset
    with hCdef
  have hCset : kacE8.comp p μ x = (C : Set (Option (Fin Tag.E8.rank))) := by
    rw [hcomp, hCdef]
    ext y
    simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (e8_lt c hc w hw)]
      exact hw
  have hproper : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacE8 hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hcl' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacE8.rootsOf (C : Set (Option (Fin Tag.E8.rank))) := by
    rw [hcl, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hcl', compRank_image, compRank_rootsOf kacE8 facts_E8 hproper, hCdef, e8_card c hc]
  have hlen6 : 6 ≤ c.length := by
    have h := h6
    rwa [hrank] at h
  have hlen8 : c.length ≤ 8 := by
    obtain ⟨y, hy⟩ := hproper
    have h1 := Finset.card_lt_univ_of_notMem hy
    rw [hCdef, e8_card c hc, Fintype.card_option, Fintype.card_fin] at h1
    have h8 : Tag.E8.rank = 8 := rfl
    rw [h8] at h1
    omega
  rcases e8_conn_cases c hc hlen6 hlen8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  ·
    exfalso
    have hp_eq := p_eq_sum_off (c := [0, 2, 4, 5, 6, 7, 8]) hcomp (by decide +kernel)
    have hfilt : (Finset.univ.filter
        (fun j : Fin Tag.E8.rank => (j : ℕ) + 1 ∉ [0, 2, 4, 5, 6, 7, 8])) =
        ({0, 2} : Finset (Fin Tag.E8.rank)) := by decide +kernel
    rw [hfilt, Finset.sum_pair (by decide : (0 : Fin Tag.E8.rank) ≠ 2)] at hp_eq
    have h0 : kacE8.θ 0 = 2 := by rw [e8Theta_eq]; decide +kernel
    have h2 : kacE8.θ 2 = 4 := by rw [e8Theta_eq]; decide +kernel
    rw [h0, h2] at hp_eq
    have hdvd : (2 : ℤ) ∣ (p : ℤ) := ⟨μ 0 + 2 * μ 2, by rw [hp_eq]; ring⟩
    exact false_of_two_dvd hp hp2 (by exact_mod_cast hdvd)
  ·
    exfalso
    have hp_eq := p_eq_sum_off (c := [0, 2, 3, 4, 5, 6, 7, 8]) hcomp (by decide +kernel)
    have hfilt : (Finset.univ.filter
        (fun j : Fin Tag.E8.rank => (j : ℕ) + 1 ∉ [0, 2, 3, 4, 5, 6, 7, 8])) =
        ({0} : Finset (Fin Tag.E8.rank)) := by decide +kernel
    rw [hfilt, Finset.sum_singleton] at hp_eq
    have h0 : kacE8.θ 0 = 2 := by rw [e8Theta_eq]; decide +kernel
    rw [h0] at hp_eq
    have hdvd : (2 : ℤ) ∣ (p : ℤ) := ⟨μ 0, by rw [hp_eq]⟩
    exact false_of_two_dvd hp hp2 (by exact_mod_cast hdvd)
  ·
    have hp_eq := p_eq_sum_off (c := [0, 1, 3, 4, 5, 6, 7, 8]) hcomp (by decide +kernel)
    have hfilt : (Finset.univ.filter
        (fun j : Fin Tag.E8.rank => (j : ℕ) + 1 ∉ [0, 1, 3, 4, 5, 6, 7, 8])) =
        ({1} : Finset (Fin Tag.E8.rank)) := by decide +kernel
    rw [hfilt, Finset.sum_singleton] at hp_eq
    have h1 : kacE8.θ 1 = 3 := by rw [e8Theta_eq]; decide +kernel
    rw [h1] at hp_eq
    have hm : (((μ 1).toNat : ℤ)) = μ 1 := Int.toNat_of_nonneg (hμ.1 1)
    rw [← hm] at hp_eq
    have hp3 : p = 3 * (μ 1).toNat := by exact_mod_cast hp_eq
    have hdvd : 3 ∣ p := ⟨(μ 1).toNat, by rw [hp3]⟩
    obtain h31 | h3p := Nat.Prime.eq_one_or_self_of_dvd (p := p) hp 3 hdvd
    · norm_num at h31
    · have hCeq : C = e8A8Nodes := by rw [hCdef]; decide +kernel
      refine Or.inr ⟨h3p.symm, v, ?_⟩
      rw [hcl', hCeq]
  ·
    have hCeq : C = e8Nodes6 := by rw [hCdef]; decide +kernel
    have hword : kacE8.rootsOf (e8Nodes6 : Set (Option (Fin Tag.E8.rank))) =
        (fun α => wordW .E8 e8Word6.reverse • α) ''
          parabolicRoots .E8 {j : Fin Tag.E8.rank | j ∉ e8Del6} :=
      rootsOf_eq_image_parabolic e8Word6 e8Nodes6 e8Del6 (by decide +kernel)
        (checkM_of_list e8Check6M) (checkN_of_list e8Check6N)
    refine Or.inl ⟨v * wordW .E8 e8Word6.reverse, e8Del6, e8Del6_mem, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e8Nodes7 := by rw [hCdef]; decide +kernel
    have hword : kacE8.rootsOf (e8Nodes7 : Set (Option (Fin Tag.E8.rank))) =
        (fun α => wordW .E8 e8Word7.reverse • α) ''
          parabolicRoots .E8 {j : Fin Tag.E8.rank | j ∉ e8Del7} :=
      rootsOf_eq_image_parabolic e8Word7 e8Nodes7 e8Del7 (by decide +kernel)
        (checkM_of_list e8Check7M) (checkN_of_list e8Check7N)
    refine Or.inl ⟨v * wordW .E8 e8Word7.reverse, e8Del7, e8Del7_mem, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e8_levi_del_cases [1, 2, 3, 4, 5, 6] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine Or.inl ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e8_levi_del_cases [1, 3, 4, 5, 6, 7] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine Or.inl ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e8_levi_del_cases [2, 3, 4, 5, 6, 7] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine Or.inl ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e8_levi_del_cases [2, 4, 5, 6, 7, 8] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine Or.inl ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e8_levi_del_cases [3, 4, 5, 6, 7, 8] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine Or.inl ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e8_levi_del_cases [1, 2, 3, 4, 5, 6, 7] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine Or.inl ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e8_levi_del_cases [1, 3, 4, 5, 6, 7, 8] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine Or.inl ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e8_levi_del_cases [2, 3, 4, 5, 6, 7, 8] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine Or.inl ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    exfalso
    have hnone : none ∉ (([1, 2, 3, 4, 5, 6, 7, 8].map (idxNode (r := Tag.E8.rank))).toFinset :
        Finset (Option (Fin Tag.E8.rank))) := by decide +kernel
    have hpar : kacE8.rootsOf (C : Set (Option (Fin Tag.E8.rank))) =
        parabolicRoots .E8 Set.univ := by
      rw [hCdef, KacData.rootsOf_eq_parabolicRoots kacE8 hnone]
      congr 1
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      fin_cases j <;> decide +kernel
    have hall : ∀ j : Fin Tag.E8.rank, a j = 1 := by
      intro j
      have hmem : (Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈
          componentRoots (rootCharHom a) i := by
        rw [hcl', hpar]
        refine ⟨v⁻¹ • (Pi.single j 1),
          ⟨IsRoot.smul (isRoot_single .E8 j) v⁻¹, ?_⟩, ?_⟩
        · exact fun k hk => absurd (Set.mem_univ k) hk
        · change v • (v⁻¹ • (Pi.single j 1)) = Pi.single j 1
          exact smul_inv_smul v _
      obtain ⟨hkr, -⟩ := hmem
      have hroot : rootChar a (Pi.single j 1) = 1 := hkr.2
      have hev : rootChar a (Pi.single j 1) = a j := by
        simpa using rootChar_nsmul_single a j 1
      rwa [hev] at hroot
    obtain ⟨j, hj⟩ := ha1
    exact hj (hall j)

end Kac

section Datum

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

private def e8Reach (S : Finset (Fin 8)) (s : Finset {i : Fin 8 // i ∉ S}) :
    Finset {i : Fin 8 // i ∉ S} :=
  s ∪ s.biUnion fun a => Finset.univ.filter fun b =>
    b ≠ a ∧ CoxeterMatrix.E₈.M b a ≠ 2

private def e8ReachN (S : Finset (Fin 8)) : ℕ → Finset {i : Fin 8 // i ∉ S} →
    Finset {i : Fin 8 // i ∉ S}
  | 0, s => s
  | k + 1, s => e8Reach S (e8ReachN S k s)

private theorem e8ReachN_mem_rtg {S : Finset (Fin 8)} {a : {i : Fin 8 // i ∉ S}} (k : ℕ) :
    ∀ {b : {i : Fin 8 // i ∉ S}}, b ∈ e8ReachN S k {a} →
      Relation.ReflTransGen
        (fun u v : {i : Fin 8 // i ∉ S} => u ≠ v ∧ CoxeterMatrix.E₈.M u v ≠ 2) a b := by
  induction k with
  | zero =>
    intro b hb
    simp only [e8ReachN, Finset.mem_singleton] at hb
    subst hb
    exact .refl
  | succ k ih =>
    intro b hb
    simp only [e8ReachN, e8Reach, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb
    rcases hb with hb | ⟨a', ha', hb'⟩
    · exact ih hb
    · exact (ih ha').trans (.single ⟨hb'.1.symm, by
        rw [← CoxeterMatrix.E₈.isSymm.apply a' b]; exact hb'.2⟩)

private theorem e8DeletedConnectedS {S : Finset (Fin 8)}
    (h : ∀ i j : {i : Fin 8 // i ∉ S}, j ∈ e8ReachN S 8 {i}) :
    GGDeletedConnectedS CoxeterMatrix.E₈ S := by
  intro i j
  exact e8ReachN_mem_rtg 8 (a := i) (h i j)

private theorem e8Parabolic_weyl {S : Finset (Fin 8)} (hne : Nonempty {i : Fin 8 // i ∉ S})
    (hdel : GGDeletedConnectedS CoxeterMatrix.E₈ S) :
    GGIsWeylMatrix (parMatrix CoxeterMatrix.E₈ {i | i ∉ S}) :=
  l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S CoxeterMatrix.E₈ CartanMatrix.E₈
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 8), by ext i j; rfl⟩))))
    ggIntCartan_E₈ hdel hne

private theorem ggIsWeylMatrixFixed_of_weyl {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) : GGIsWeylMatrixFixed M := by
  rcases hM with ⟨n, e, hn, h | h | h⟩ | h | h | h | h | h
  · exact Or.inl ⟨n, e, hn, Or.inl h⟩
  · exact Or.inl ⟨n, e, hn, Or.inr (Or.inl h)⟩
  · obtain ⟨hn4, h⟩ := h
    exact Or.inl ⟨n, e, hn, Or.inr (Or.inr ⟨hn4, h⟩)⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

private theorem ggIntCartan_parMatrix {ι : Type} (M : CoxeterMatrix ι) (C : Matrix ι ι ℤ)
    (T : Set ι) (h : GGIntCartan M C) :
    GGIntCartan (parMatrix M T) (C.submatrix Subtype.val Subtype.val) := by
  constructor
  · intro i
    exact h.1 i.val
  · intro i j hij
    exact h.2 i.val j.val (fun hh => hij (Subtype.ext hh))

private theorem ggIsReflection_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {φ : MulAut ↥Bs} (h : GGIsReflection p φ) (ψ : MulAut ↥Bs) :
    GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

private theorem ggLin_conj {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) (u φ : MulAut E)
    {g : Module.Dual (ZMod p) V} {z : V}
    (hφ : ∀ v, ggLin (p := p) ι φ v = v - g v • z) (v : V) :
    ggLin (p := p) ι (u * φ * u⁻¹) v =
      v - g ((ggLin (p := p) ι u).symm v) • ggLin (p := p) ι u z := by
  rw [map_mul, map_mul, map_inv]
  show ggLin (p := p) ι u (ggLin (p := p) ι φ ((ggLin (p := p) ι u).symm v)) = _
  rw [hφ, map_sub, map_smul, LinearEquiv.apply_symm_apply]

private theorem subgroup_map_conj {E : Type*} [Group E] (S : Subgroup E) (u : E) (hu : u ∈ S) :
    Subgroup.map (MulAut.conj u).toMonoidHom S = S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hy) (Subgroup.inv_mem _ hu)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨u⁻¹ * x * u, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hx) hu
    · show u * (u⁻¹ * x * u) * u⁻¹ = x
      group

private theorem range_subtype_eq {β : Type*} (f : Fin 8 → β) {S : Finset (Fin 8)} {b : Fin 8}
    (hSb : S = {b}) :
    Set.range (fun j : {j : Fin 8 // j ≠ b} => f j) =
      Set.range (fun j : {j : Fin 8 // j ∉ S} => f j) := by
  subst hSb
  let e : {j : Fin 8 // j ≠ b} ≃ {j : Fin 8 // j ∉ ({b} : Finset (Fin 8))} :=
    Equiv.subtypeEquivRight (fun j => by simp)
  have h : (fun j : {j : Fin 8 // j ≠ b} => f j) =
      (fun j : {j : Fin 8 // j ∉ ({b} : Finset (Fin 8))} => f j) ∘ e := rfl
  rw [h, Set.range_comp, e.surjective.range_eq, Set.image_univ]

private theorem e8Side_weyl {b : Fin 8}
    (h : GGIsWeylMatrix (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ∉ ({b} : Finset (Fin 8))})) :
    GGIsWeylMatrix (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ≠ b}) := by
  have hmat : parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ≠ b} =
      (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ∉ ({b} : Finset (Fin 8))}).reindex
        (Equiv.subtypeEquivRight (fun j => by simp)) := by
    ext i j
    rfl
  rw [hmat]
  exact l05nBL_weyl_reindex h _

private theorem e8SideDatum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {M : CoxeterMatrix (Fin 8)} (hWM : GGIsWeylMatrix M)
    {C : Matrix (Fin 8) (Fin 8) ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {ψ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (b : Fin 8) (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 8 // j ≠ b} => ψ j))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Fin 8 | j ≠ b}))
    (h3 : 3 ≤ Fintype.card {j : Fin 8 // j ≠ b}) :
    GGResSideDatum p Bs X J := by
  have hWMJ' : GGIsWeylMatrixFixed (parMatrix M {j : Fin 8 | j ≠ b}) :=
    ggIsWeylMatrixFixed_of_weyl hWMJ
  have hCJ : GGIntCartan (parMatrix M {j : Fin 8 | j ≠ b})
      (C.submatrix Subtype.val Subtype.val) := ggIntCartan_parMatrix M C _ hMC
  have hpairJ : ∀ i j : {j : Fin 8 // j ≠ b}, α (i : Fin 8) (h (j : Fin 8)) =
      ((C.submatrix Subtype.val Subtype.val) i j : ZMod p) := fun i j => hpair i.val j.val
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin 8 // j ≠ b} => ψ j) :=
    ggReflConjSimple_of_weylMatrix hp hWMJ' h3 hCJ ι
      (fun j : {j : Fin 8 // j ≠ b} => ψ j) (fun j : {j : Fin 8 // j ≠ b} => h j)
      (fun j : {j : Fin 8 // j ≠ b} => α j) hpairJ (fun i w => hlin i w) hJ
  let fJ : (parMatrix M {j : Fin 8 | j ≠ b}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Fin 8 | j ≠ b} ψ f hf hJ
  have hfJ : ∀ j, (fJ ((parMatrix M {j : Fin 8 | j ≠ b}).simple j) : MulAut ↥Bs) = ψ j :=
    fun i => ggParabolic_equiv_of_generator_equiv_simple M f ψ hf _ hJ i
  exact ⟨Fin 8, inferInstance, inferInstance, b, M, C, parMatrix M {j : Fin 8 | j ≠ b}, V,
    inferInstance, inferInstance, ι, ψ, h, α, hWM, hMC, hWMJ, fun _ _ => rfl, hlin, hrefl, hpair,
    ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hJ, hconjJ⟩

private theorem e8LeviSideDatum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {M : CoxeterMatrix (Fin 8)} (hWM : GGIsWeylMatrix M)
    {C : Matrix (Fin 8) (Fin 8) ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {ψ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (S : Finset (Fin 8)) (hS1 : 2 ≤ S.card) (hS2 : S.card ≤ 3)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 8 // j ∉ S} => ψ j))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Fin 8 | j ∉ S}))
    (h3 : 3 ≤ Fintype.card {j : Fin 8 // j ∉ S}) :
    GGResLeviSideDatumLE3 p Bs X J := by
  have hWMJ' : GGIsWeylMatrixFixed (parMatrix M {j : Fin 8 | j ∉ S}) :=
    ggIsWeylMatrixFixed_of_weyl hWMJ
  have hCJ : GGIntCartan (parMatrix M {j : Fin 8 | j ∉ S})
      (C.submatrix Subtype.val Subtype.val) := ggIntCartan_parMatrix M C _ hMC
  have hpairJ : ∀ i j : {j : Fin 8 // j ∉ S}, α (i : Fin 8) (h (j : Fin 8)) =
      ((C.submatrix Subtype.val Subtype.val) i j : ZMod p) := fun i j => hpair i.val j.val
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin 8 // j ∉ S} => ψ j) :=
    ggReflConjSimple_of_weylMatrix hp hWMJ' h3 hCJ ι
      (fun j : {j : Fin 8 // j ∉ S} => ψ j) (fun j : {j : Fin 8 // j ∉ S} => h j)
      (fun j : {j : Fin 8 // j ∉ S} => α j) hpairJ (fun i w => hlin i w) hJ
  let fJ : (parMatrix M {j : Fin 8 | j ∉ S}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Fin 8 | j ∉ S} ψ f hf hJ
  have hfJ : ∀ j, (fJ ((parMatrix M {j : Fin 8 | j ∉ S}).simple j) : MulAut ↥Bs) = ψ j :=
    fun i => ggParabolic_equiv_of_generator_equiv_simple M f ψ hf _ hJ i
  exact ⟨Fin 8, inferInstance, inferInstance, S, M, C, parMatrix M {j : Fin 8 | j ∉ S}, V,
    inferInstance, inferInstance, ι, ψ, h, α, hS1, hS2, hWM, hMC, hWMJ, fun _ _ => rfl, hlin,
    hrefl, hpair, ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hJ, hconjJ⟩

theorem ggE8LeviDatum_of_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {Bs X J : Subgroup G} {M : CoxeterMatrix (Fin 8)} (hM : M = CoxeterMatrix.E₈)
    {C : Matrix (Fin 8) (Fin 8) ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Fin 8 → MulAut ↥Bs} {h : Fin 8 → V} {α : Fin 8 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (u : M.Group) {S : Finset (Fin 8)} (hS : S ∈ e8LeviDel)
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Fin 8 // j ∉ S} =>
      (f u : MulAut ↥Bs) * φ j * (f u : MulAut ↥Bs)⁻¹)) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  obtain rfl : M = CoxeterMatrix.E₈ := hM
  have hWM : GGIsWeylMatrix (CoxeterMatrix.E₈ : CoxeterMatrix (Fin 8)) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 8), by ext i j; rfl⟩)))
  let g : MulAut ↥Bs := (f u : MulAut ↥Bs)
  let W : V ≃ₗ[ZMod p] V := ggLin (p := p) ι g
  let ψ : Fin 8 → MulAut ↥Bs := fun i => (f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹
  let h' : Fin 8 → V := fun i => W (h i)
  let α' : Fin 8 → Module.Dual (ZMod p) V :=
    fun i => (α i).comp (W.symm : V ≃ₗ[ZMod p] V).toLinearMap
  have hlin' : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α' i w • h' i := by
    intro i v
    have h := ggLin_conj (p := p) ι g (φ i) (hlin i) v
    simpa only [ψ, α', h', W, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h
  have hrefl' : ∀ i, GGIsReflection p (ψ i) := fun i => ggIsReflection_conj (hrefl i) g
  have hpair' : ∀ i j, α' i (h' j) = (C i j : ZMod p) := by
    intro i j
    simpa only [α', h', W, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] using hpair i j
  let f' : (CoxeterMatrix.E₈).Group ≃* ↥(ggAutomizer X Bs) := (MulAut.conj u).trans f
  have hf' : ∀ i, (f' ((CoxeterMatrix.E₈).simple i) : MulAut ↥Bs) = ψ i := by
    intro i
    show ((f (u * (CoxeterMatrix.E₈).simple i * u⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = _
    rw [map_mul, map_mul, map_inv]
    simp only [ψ, Subgroup.coe_mul, Subgroup.coe_inv, hf i]
  have hgA : g ∈ ggAutomizer X Bs := (f u).2
  have hclos' : ggAutomizer X Bs = Subgroup.closure (Set.range ψ) := by
    have hrange : Set.range ψ = (MulAut.conj g).toMonoidHom '' Set.range φ := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨φ i, ⟨i, rfl⟩, (MulAut.conj_apply g (φ i)).symm⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, MulAut.conj_apply g (φ i)⟩
    rw [hclos, hrange, ← MonoidHom.map_closure]
    exact (subgroup_map_conj _ g (hclos ▸ hgA)).symm
  have hS' : S = {0} ∨ S = {1} ∨ S = {7} ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 7} ∨
      S = {0, 7} ∨ S = {6, 7} := by
    simpa [e8LeviDel] using hS
  rcases hS' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 8 // j ≠ 0} => ψ j) := by
      rw [hJ, ← range_subtype_eq ψ (S := ({0} : Finset (Fin 8))) rfl]
    have hWMJ : GGIsWeylMatrix (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ≠ 0}) :=
      e8Side_weyl (e8Parabolic_weyl (S := {0}) ⟨⟨1, by decide⟩⟩
        (e8DeletedConnectedS (by decide +kernel)))
    exact Or.inl (e8SideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos' 0 hJ' hWMJ
      (by decide +kernel))
  ·
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 8 // j ≠ 1} => ψ j) := by
      rw [hJ, ← range_subtype_eq ψ (S := ({1} : Finset (Fin 8))) rfl]
    have hWMJ : GGIsWeylMatrix (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ≠ 1}) :=
      e8Side_weyl (e8Parabolic_weyl (S := {1}) ⟨⟨0, by decide⟩⟩
        (e8DeletedConnectedS (by decide +kernel)))
    exact Or.inl (e8SideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos' 1 hJ' hWMJ
      (by decide +kernel))
  ·
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 8 // j ≠ 7} => ψ j) := by
      rw [hJ, ← range_subtype_eq ψ (S := ({7} : Finset (Fin 8))) rfl]
    have hWMJ : GGIsWeylMatrix (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ≠ 7}) :=
      e8Side_weyl (e8Parabolic_weyl (S := {7}) ⟨⟨0, by decide⟩⟩
        (e8DeletedConnectedS (by decide +kernel)))
    exact Or.inl (e8SideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos' 7 hJ' hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ∉ ({0, 1} : Finset (Fin 8))}) :=
      e8Parabolic_weyl (S := {0, 1}) ⟨⟨2, by decide⟩⟩ (e8DeletedConnectedS (by decide +kernel))
    exact Or.inr (e8LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 1} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ∉ ({0, 2} : Finset (Fin 8))}) :=
      e8Parabolic_weyl (S := {0, 2}) ⟨⟨1, by decide⟩⟩ (e8DeletedConnectedS (by decide +kernel))
    exact Or.inr (e8LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 2} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ∉ ({1, 7} : Finset (Fin 8))}) :=
      e8Parabolic_weyl (S := {1, 7}) ⟨⟨0, by decide⟩⟩ (e8DeletedConnectedS (by decide +kernel))
    exact Or.inr (e8LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({1, 7} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ∉ ({0, 7} : Finset (Fin 8))}) :=
      e8Parabolic_weyl (S := {0, 7}) ⟨⟨1, by decide⟩⟩ (e8DeletedConnectedS (by decide +kernel))
    exact Or.inr (e8LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 7} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₈ {j : Fin 8 | j ∉ ({6, 7} : Finset (Fin 8))}) :=
      e8Parabolic_weyl (S := {6, 7}) ⟨⟨0, by decide⟩⟩ (e8DeletedConnectedS (by decide +kernel))
    exact Or.inr (e8LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({6, 7} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))

end Datum

end CFSG.StandardType

end
