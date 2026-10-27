module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockCyc
public import CFSG.RankThree.PartOne.KC.UnitaryPrimarySelfDual
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import Mathlib

public section

namespace CFSG.StandardType

namespace SUTB

open Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.OddIso
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

section General

variable {K : Type} [Field K] {σ : K →+* K} {V : Type} [AddCommGroup V] [Module K V]
  {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem apply_pow_left_eq {X : Module.End K V} (hXB : ∀ v w, B (X v) (X w) = B v w) {p : ℕ}
    (hp : 1 ≤ p) (hXp : X ^ p = 1) (k : ℕ) (v w : V) :
    B ((X ^ k) v) w = B v ((X ^ (k * (p - 1))) w) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, apply_left_eq hXB hp hXp, ih, ← Module.End.mul_apply,
      ← pow_add]
    congr 3
    ring

theorem apply_pow_pow_eq {X : Module.End K V} (hXB : ∀ v w, B (X v) (X w) = B v w) {p : ℕ}
    (hp : 1 ≤ p) (hXp : X ^ p = 1) (k l : ℕ) (v w : V) :
    B ((X ^ k) v) ((X ^ l) w) = B v ((X ^ (l + k * (p - 1))) w) := by
  rw [apply_pow_left_eq hXB hp hXp, ← Module.End.mul_apply, ← pow_add, add_comm]

theorem exists_isometry_of_families {ι : Type} [Fintype ι] {F₁ F₂ : ι → V}
    (hG : ∀ i j, B (F₁ i) (F₁ j) = B (F₂ i) (F₂ j)) {U₁ U₂ : Submodule K V}
    (hs₁ : Submodule.span K (Set.range F₁) = U₁) (hs₂ : Submodule.span K (Set.range F₂) = U₂)
    (hnd₂ : NondegOn B U₂) {X : Module.End K V} {τ : ι → ι}
    (hτ₁ : ∀ i, X (F₁ i) = F₁ (τ i)) (hτ₂ : ∀ i, X (F₂ i) = F₂ (τ i)) :
    ∃ θ : V →ₗ[K] V, (∀ u ∈ U₁, θ u ∈ U₂) ∧ (∀ u ∈ U₁, ∀ v ∈ U₁, B (θ u) (θ v) = B u v) ∧
      (∀ u ∈ U₁, θ (X u) = X (θ u)) ∧ ∀ w ∈ U₂, ∃ u ∈ U₁, θ u = w := by
  subst hs₁ hs₂
  obtain ⟨θ, hθ⟩ := exists_linearMap_of_gram hG hnd₂
  refine ⟨θ, fun u hu => gram_map_mem hθ hu, fun u hu v hv => gram_map_eq hG hθ hu hv,
    fun u hu => gram_map_comm hθ hτ₁ hτ₂ hu, fun w hw => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw
  refine ⟨∑ i, c i • F₁ i, Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  simp only [map_sum, map_smul, hθ]

end General

section Primary

variable {K : Type} [Field K] [Finite K] {f : ℕ} (hK : UnitaryFieldData 2 f K)
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

omit [Finite K] [FiniteDimensional K V] in
theorem coe_root_pow_smul {g : K[X]} (v : primaryComponent (x : Module.End K V) g) (k : ℕ) :
    ((AdjoinRoot.root g ^ k • v : primaryComponent (x : Module.End K V) g) : V) =
      ((x : Module.End K V) ^ k) (v : V) := by
  rw [← AdjoinRoot.mk_X, ← map_pow, coe_mk_smul_primaryComponent, map_pow, aeval_X]

omit [Finite K] [FiniteDimensional K V] in
theorem eq_zero_of_forall_left (H : UnitaryPrimaryData hK.bar B x) {U : Submodule K V}
    (hU : NondegOn B U) {v : V} (hv : v ∈ U) (h : ∀ u ∈ U, B v u = 0) : v = 0 :=
  hU v hv fun u hu => by rw [← H.symm.eq v u, h u hu, map_zero]

omit [Finite K] in
theorem nondegOn_inf_selfDual (H : UnitaryPrimaryData hK.bar B x) {g : K[X]}
    (hg : g ∈ primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar g = g)
    {U : Submodule K V} (hU : NondegOn B U) (hUx : ∀ u ∈ U, (x : Module.End K V) u ∈ U) :
    NondegOn B (primaryComponent (x : Module.End K V) g ⊓ U) := by
  classical
  intro m hm hn
  refine hU m hm.2 fun u hu => ?_
  rw [eq_sum_primaryProjection H.squarefree u, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hbU : primaryProjection (x : Module.End K V) b u ∈ U := aeval_mem_of_inv hUx _ hu
  by_cases hbg : b = g
  · subst hbg
    exact hn _ ⟨primaryProjection_mem H.squarefree hb u, hbU⟩
  · refine orthogonal_of_ne_dualPoly H hb hg (fun hgb => hbg ?_)
      (primaryProjection_mem H.squarefree hb u) hm.1
    rw [← dualPoly_dualPoly_of_mem H hb, ← hgb, hself]

theorem exists_trace_ne_zero {g : K[X]} [Fact (Irreducible g)] :
    ∃ c : AdjoinRoot g, Algebra.trace K (AdjoinRoot g) c ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : (1 : AdjoinRoot g) = 0 := eq_of_trace_eq fun b => by rw [hcon, zero_mul, hcon]
  exact one_ne_zero h1

variable (H : UnitaryPrimaryData hK.bar B x) {g : K[X]}
  (hg : g ∈ primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar g = g)
  [Fact (Irreducible g)]

include H hg hself in
theorem apply_smul_smul (u : primaryComponent (x : Module.End K V) g) (e e' : AdjoinRoot g) :
    B ((e • u : primaryComponent (x : Module.End K V) g) : V)
      ((e' • u : primaryComponent (x : Module.End K V) g) : V) =
      Algebra.trace K (AdjoinRoot g) ((unitaryFieldData_adjoinRoot hK (a := g)).bar e *
        (e' * selfDualVal B (x : Module.End K V) g u u)) := by
  rw [apply_eq_trace_selfDualForm hK H hg hself, selfDualForm_apply,
    selfDualVal_smul_left hK H hg hself, selfDualVal_smul_right]

include H hg hself in
theorem nondegOn_cyc_of_selfDualVal (u : primaryComponent (x : Module.End K V) g)
    (hu : selfDualVal B (x : Module.End K V) g u u ≠ 0) :
    NondegOn B (cyc (x : Module.End K V) (u : V)) := by
  intro m hm hn
  obtain ⟨t, rfl⟩ := (mem_cyc_iff _ _ _).mp hm
  have hmu : aeval (x : Module.End K V) t (u : V) =
      ((AdjoinRoot.mk g t • u : primaryComponent (x : Module.End K V) g) : V) :=
    (coe_mk_smul_primaryComponent _ _ t u).symm
  by_cases hβ : AdjoinRoot.mk g t = 0
  · rw [hmu, hβ, zero_smul, Submodule.coe_zero]
  exfalso
  obtain ⟨c₀, hc₀⟩ := exists_trace_ne_zero (K := K) (g := g)
  obtain ⟨t', ht'⟩ := AdjoinRoot.mk_surjective ((unitaryFieldData_adjoinRoot hK (a := g)).bar
    ((AdjoinRoot.mk g t * selfDualVal B (x : Module.End K V) g u u)⁻¹ * c₀))
  have hn' := hn (aeval (x : Module.End K V) t' (u : V)) ((mem_cyc_iff _ _ _).mpr ⟨t', rfl⟩)
  rw [hmu, ← coe_mk_smul_primaryComponent, apply_smul_smul hK H hg hself, ht',
    UnitaryFieldData.bar_bar] at hn'
  have hc : (AdjoinRoot.mk g t * selfDualVal B (x : Module.End K V) g u u)⁻¹ * c₀ *
      (AdjoinRoot.mk g t * selfDualVal B (x : Module.End K V) g u u) = c₀ := by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hβ hu), one_mul]
  rw [hc] at hn'
  exact hc₀ hn'

include H hg hself in
theorem exists_selfDualVal_ne_zero {U : Submodule K V} (hnd : NondegOn B U)
    (hinv : ∀ u ∈ U, (x : Module.End K V) u ∈ U)
    (hgU : ∃ w ∈ U, w ≠ 0 ∧ aeval (x : Module.End K V) g w = 0) :
    ∃ u : primaryComponent (x : Module.End K V) g, (u : V) ∈ U ∧
      selfDualVal B (x : Module.End K V) g u u ≠ 0 := by
  have : CharP K 2 := hK.charP
  obtain ⟨w, hwU, hw0, hwg⟩ := hgU
  have hW := nondegOn_inf_selfDual hK H hg hself hnd hinv
  have hwW : w ∈ primaryComponent (x : Module.End K V) g ⊓ U :=
    ⟨mem_primaryComponent.mpr hwg, hwU⟩
  have hex : ∃ v ∈ primaryComponent (x : Module.End K V) g ⊓ U, B v v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall := form_eq_zero_of_isotropic hK.exists_bar_ne (fun a b => (H.symm.eq a b).symm)
      hcon
    exact hw0 (hW w hwW fun n hn => hall n hn w hwW)
  obtain ⟨v, ⟨hvg, hvU⟩, hvv⟩ := hex
  refine ⟨⟨v, hvg⟩, hvU, fun h0 => hvv ?_⟩
  have h1 := apply_eq_trace_selfDualForm hK H hg hself
    (⟨v, hvg⟩ : primaryComponent (x : Module.End K V) g) ⟨v, hvg⟩
  rw [selfDualForm_apply, h0, map_zero] at h1
  exact h1

include H hg hself in
theorem exists_smul_selfDualVal_eq (u₁ u₂ : primaryComponent (x : Module.End K V) g)
    (h₂ : selfDualVal B (x : Module.End K V) g u₂ u₂ ≠ 0) :
    ∃ β : AdjoinRoot g, selfDualVal B (x : Module.End K V) g (β • u₂) (β • u₂) =
      selfDualVal B (x : Module.End K V) g u₁ u₁ := by
  set hE := unitaryFieldData_adjoinRoot hK (a := g) with hhE
  have hfix : ∀ u : primaryComponent (x : Module.End K V) g,
      hE.bar (selfDualVal B (x : Module.End K V) g u u) = selfDualVal B (x : Module.End K V) g u u :=
    fun u => selfDualVal_symm hK H hg hself u u
  set r := selfDualVal B (x : Module.End K V) g u₁ u₁ / selfDualVal B (x : Module.End K V) g u₂ u₂
    with hr
  have hrf : r ∈ hE.fixedField := by
    rw [hE.mem_fixedField, hr, map_div₀, hfix, hfix]
  obtain ⟨β, hβ⟩ := hE.normHom_surjective ⟨r, hrf⟩
  have hβ' : β * hE.bar β = r := congrArg Subtype.val hβ
  refine ⟨β, ?_⟩
  rw [selfDualVal_smul_left hK H hg hself, selfDualVal_smul_right, ← mul_assoc, mul_comm (hE.bar β),
    hβ', hr, div_mul_cancel₀ _ h₂]

include H hg hself in
theorem apply_pow_selfDual (u : primaryComponent (x : Module.End K V) g) (k l : ℕ) :
    B (((x : Module.End K V) ^ k) (u : V)) (((x : Module.End K V) ^ l) (u : V)) =
      Algebra.trace K (AdjoinRoot g) ((unitaryFieldData_adjoinRoot hK (a := g)).bar
        (AdjoinRoot.root g ^ k) * (AdjoinRoot.root g ^ l * selfDualVal B (x : Module.End K V) g u u)) := by
  rw [← coe_root_pow_smul, ← coe_root_pow_smul, apply_smul_smul hK H hg hself]

end Primary

section Paired

variable {K : Type} [Field K] [Finite K] {f : ℕ} (hK : UnitaryFieldData 2 f K)
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData hK.bar B x) {g : K[X]} (hg : g ∈ primaryFactors (x : Module.End K V))

omit [Finite K] in
include H hg in
theorem exists_pair_vec {U : Submodule K V} (hnd : NondegOn B U)
    (hinv : ∀ u ∈ U, (x : Module.End K V) u ∈ U) {w : V} (hwU : w ∈ U) (hw0 : w ≠ 0)
    (hwg : aeval (x : Module.End K V) g w = 0) :
    ∃ w' : primaryComponent (x : Module.End K V) (dualPoly hK.bar g), (w' : V) ∈ U ∧
      B w w' ≠ 0 := by
  classical
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, B w u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (eq_zero_of_forall_left hK H hnd hwU hcon)
  have hg' := dualPoly_mem_primaryFactors H hg
  refine ⟨⟨primaryProjection (x : Module.End K V) (dualPoly hK.bar g) u,
    primaryProjection_mem H.squarefree hg' u⟩, aeval_mem_of_inv hinv _ huU, fun h0 => hu ?_⟩
  rw [eq_sum_primaryProjection H.squarefree u, map_sum,
    Finset.sum_eq_single (dualPoly hK.bar g)]
  · exact h0
  · intro b hb hbne
    exact orthogonal_of_ne_dualPoly H hg hb hbne (mem_primaryComponent.mpr hwg)
      (primaryProjection_mem H.squarefree hb u)
  · intro hn
    exact absurd hg' hn

omit [Finite K] [FiniteDimensional K V] in
@[expose] noncomputable def pairFunctional (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (X : Module.End K V)
    (g' : K[X]) (w : V) (w' : primaryComponent X g') : Module.Dual K (AdjoinRoot g') where
  toFun c := B w ((c • w' : primaryComponent X g') : V)
  map_add' c c' := by rw [add_smul, Submodule.coe_add, map_add]
  map_smul' r c := by
    rw [smul_assoc, Submodule.coe_smul, map_smul]
    rfl

omit [FiniteDimensional K V] in
theorem exists_smul_pair_eq {g' : K[X]} [Fact (Irreducible g')] (w₁ w₂ : V)
    (w₁' w₂' : primaryComponent (x : Module.End K V) g') (h₂ : B w₂ w₂' ≠ 0) :
    ∃ α : AdjoinRoot g', ∀ c : AdjoinRoot g',
      B w₂ ((c • α • w₂' : primaryComponent (x : Module.End K V) g') : V) =
        B w₁ ((c • w₁' : primaryComponent (x : Module.End K V) g') : V) := by
  obtain ⟨z₁, hz₁⟩ := exists_trace_dual (pairFunctional hK B (x : Module.End K V) g' w₁ w₁')
  obtain ⟨z₂, hz₂⟩ := exists_trace_dual (pairFunctional hK B (x : Module.End K V) g' w₂ w₂')
  have hz₂0 : z₂ ≠ 0 := by
    intro h0
    apply h₂
    have := hz₂ 1
    rw [h0, zero_mul, map_zero] at this
    change 0 = B w₂ ((1 • w₂' : primaryComponent (x : Module.End K V) g') : V) at this
    rw [one_smul] at this
    exact this.symm
  refine ⟨z₁ * z₂⁻¹, fun c => ?_⟩
  have e₁ := hz₁ c
  have e₂ := hz₂ (c * (z₁ * z₂⁻¹))
  change _ = B w₂ (((c * (z₁ * z₂⁻¹)) • w₂' : primaryComponent (x : Module.End K V) g') : V)
    at e₂
  change _ = B w₁ ((c • w₁' : primaryComponent (x : Module.End K V) g') : V) at e₁
  rw [mul_smul] at e₂
  rw [← e₂, ← e₁]
  congr 1
  field_simp

end Paired

section Main

variable {K : Type} [Field K] [Finite K] {f : ℕ} (hK : UnitaryFieldData 2 f K)
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem exists_isometry_of_pieces (H : UnitaryPrimaryData hK.bar B x) {p : ℕ} (hp : 0 < p)
    (hxp : (x : Module.End K V) ^ p = 1) {U₁ U₂ : Submodule K V}
    (hnd₁ : NondegOn B U₁) (hnd₂ : NondegOn B U₂)
    (hinv₁ : ∀ u ∈ U₁, (x : Module.End K V) u ∈ U₁)
    (hinv₂ : ∀ u ∈ U₂, (x : Module.End K V) u ∈ U₂)
    (hmin₁ : ∀ W : Submodule K V, W ≤ U₁ → W ≠ ⊥ → NondegOn B W →
      (∀ w ∈ W, (x : Module.End K V) w ∈ W) → W = U₁)
    (hmin₂ : ∀ W : Submodule K V, W ≤ U₂ → W ≠ ⊥ → NondegOn B W →
      (∀ w ∈ W, (x : Module.End K V) w ∈ W) → W = U₂)
    {g : K[X]} (hg : g ∈ primaryFactors (x : Module.End K V))
    (hg₁ : ∃ w ∈ U₁, w ≠ 0 ∧ aeval (x : Module.End K V) g w = 0)
    (hg₂ : ∃ w ∈ U₂, w ≠ 0 ∧ aeval (x : Module.End K V) g w = 0) :
    ∃ θ : V →ₗ[K] V, (∀ u ∈ U₁, θ u ∈ U₂) ∧ (∀ u ∈ U₁, ∀ v ∈ U₁, B (θ u) (θ v) = B u v) ∧
      (∀ u ∈ U₁, θ ((x : Module.End K V) u) = (x : Module.End K V) (θ u)) ∧
      ∀ w ∈ U₂, ∃ u ∈ U₁, θ u = w := by
  classical
  have : Fact (Irreducible g) := ⟨irreducible_of_mem_primaryFactors hg⟩
  set X := (x : Module.End K V) with hXdef
  have hXB : ∀ v w, B (X v) (X w) = B v w := H.isom
  set τ : Fin p → Fin p := fun k => ⟨((k : ℕ) + 1) % p, Nat.mod_lt _ hp⟩ with hτ
  have hshift : ∀ (w : V) (k : Fin p), X ((X ^ (k : ℕ)) w) = (X ^ ((τ k : Fin p) : ℕ)) w :=
    fun w k => pow_succ_mod_apply hxp w k
  have hVg : ∀ (a : K[X]) (v : V), v ∈ primaryComponent X a → X v ∈ primaryComponent X a :=
    fun a v hv => apply_mem_primaryComponent (Commute.refl X) hv
  by_cases hself : dualPoly hK.bar g = g
  ·
    obtain ⟨u₁, hu₁U, hu₁⟩ := exists_selfDualVal_ne_zero hK H hg hself hnd₁ hinv₁ hg₁
    obtain ⟨u₂, hu₂U, hu₂⟩ := exists_selfDualVal_ne_zero hK H hg hself hnd₂ hinv₂ hg₂
    obtain ⟨β, hβ⟩ := exists_smul_selfDualVal_eq hK H hg hself u₁ u₂ hu₂
    have hu₂'U : ((β • u₂ : primaryComponent X g) : V) ∈ U₂ := by
      obtain ⟨t, rfl⟩ := AdjoinRoot.mk_surjective β
      rw [coe_mk_smul_primaryComponent]
      exact aeval_mem_of_inv hinv₂ t hu₂U
    have hcyc : ∀ {U : Submodule K V}, (∀ u ∈ U, X u ∈ U) →
        (∀ W : Submodule K V, W ≤ U → W ≠ ⊥ → NondegOn B W → (∀ w ∈ W, X w ∈ W) → W = U) →
        ∀ u : primaryComponent X g, (u : V) ∈ U → selfDualVal B X g u u ≠ 0 →
          cyc X (u : V) = U := by
      intro U hinv hmin u huU hu
      refine hmin _ (cyc_le hinv huU) ?_ (nondegOn_cyc_of_selfDualVal hK H hg hself u hu)
        (cyc_invariant X _)
      intro hbot
      have h1 : (u : V) ∈ cyc X (u : V) := by simpa using pow_mem_cyc X (u : V) 0
      rw [hbot, Submodule.mem_bot] at h1
      have h2 : u = 0 := Subtype.ext h1
      apply hu
      rw [h2]
      have := selfDualVal_smul_right (B := B) (0 : AdjoinRoot g) (0 : primaryComponent X g)
        (0 : primaryComponent X g)
      rwa [zero_smul, zero_mul] at this
    refine exists_isometry_of_families
      (F₁ := fun k : Fin p => (X ^ (k : ℕ)) (u₁ : V))
      (F₂ := fun k : Fin p => (X ^ (k : ℕ)) ((β • u₂ : primaryComponent X g) : V)) ?_
      ((span_pow_eq_cyc hp hxp _).trans (hcyc hinv₁ hmin₁ u₁ hu₁U hu₁))
      ((span_pow_eq_cyc hp hxp _).trans (hcyc hinv₂ hmin₂ _ hu₂'U (hβ.symm ▸ hu₁)))
      hnd₂ (τ := τ) (fun k => hshift _ k) (fun k => hshift _ k)
    intro k l
    rw [apply_pow_selfDual hK H hg hself, apply_pow_selfDual hK H hg hself, hβ]
  ·
    set g' := dualPoly hK.bar g with hg'def
    have hg' : g' ∈ primaryFactors X := dualPoly_mem_primaryFactors H hg
    have : Fact (Irreducible g') := ⟨irreducible_of_mem_primaryFactors hg'⟩
    have hgg : dualPoly hK.bar g' = g := dualPoly_dualPoly_of_mem H hg
    have hne : g ≠ dualPoly hK.bar g := fun h => hself h.symm
    have hne' : g' ≠ dualPoly hK.bar g' := by rw [hgg]; exact hself
    have hiso : ∀ {a : K[X]}, a ∈ primaryFactors X → a ≠ dualPoly hK.bar a → ∀ {w : V},
        w ∈ primaryComponent X a → ∀ v ∈ cyc X w, ∀ v' ∈ cyc X w, B v v' = 0 := by
      intro a ha hane w hw v hv v' hv'
      exact isotropic_primaryComponent H ha hane (cyc_le (hVg a) hw hv) (cyc_le (hVg a) hw hv')
    obtain ⟨w₁, hw₁U, hw₁0, hw₁g⟩ := hg₁
    obtain ⟨w₂, hw₂U, hw₂0, hw₂g⟩ := hg₂
    obtain ⟨w₁', hw₁'U, hw₁'⟩ := exists_pair_vec hK H hg hnd₁ hinv₁ hw₁U hw₁0 hw₁g
    obtain ⟨w₂', hw₂'U, hw₂'⟩ := exists_pair_vec hK H hg hnd₂ hinv₂ hw₂U hw₂0 hw₂g
    obtain ⟨α, hα⟩ := exists_smul_pair_eq hK w₁ w₂ w₁' w₂' hw₂'
    set w₂'' : primaryComponent X g' := α • w₂' with hw₂''
    have hw₂''U : (w₂'' : V) ∈ U₂ := by
      obtain ⟨t, ht⟩ := AdjoinRoot.mk_surjective α
      rw [hw₂'', ← ht, coe_mk_smul_primaryComponent]
      exact aeval_mem_of_inv hinv₂ t hw₂'U
    have hαc : ∀ c : AdjoinRoot g', B w₂ ((c • w₂'' : primaryComponent X g') : V) =
        B w₁ ((c • w₁' : primaryComponent X g') : V) := hα
    have hw₂''0 : B w₂ (w₂'' : V) ≠ 0 := by
      have := hαc 1
      rw [one_smul, one_smul] at this
      rw [this]
      exact hw₁'
    have hsup : ∀ {U : Submodule K V}, (∀ u ∈ U, X u ∈ U) →
        (∀ W : Submodule K V, W ≤ U → W ≠ ⊥ → NondegOn B W → (∀ w ∈ W, X w ∈ W) → W = U) →
        ∀ {w : V} (w' : primaryComponent X g'), w ∈ U → (w' : V) ∈ U → w ≠ 0 →
          aeval X g w = 0 → B w w' ≠ 0 → cyc X w ⊔ cyc X (w' : V) = U := by
      intro U hinv hmin w w' hwU hw'U hw0 hwg hww'
      refine hmin _ (sup_le (cyc_le hinv hwU) (cyc_le hinv hw'U)) ?_
        (nondegOn_cyc_sup H.symm hXB hp hxp (irreducible_of_mem_primaryFactors hg)
          (irreducible_of_mem_primaryFactors hg') hwg (mem_primaryComponent.mp w'.2) hww'
          (hiso hg hne (mem_primaryComponent.mpr hwg)) (hiso hg' hne' w'.2))
        fun v hv => ?_
      · intro hbot
        have h1 : w ∈ cyc X w ⊔ cyc X (w' : V) :=
          Submodule.mem_sup_left (by simpa using pow_mem_cyc X w 0)
        rw [hbot, Submodule.mem_bot] at h1
        exact hw0 h1
      · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add]
        exact Submodule.add_mem_sup (cyc_invariant X w a ha) (cyc_invariant X _ b hb)
    have hspan : ∀ (w w' : V), Submodule.span K (Set.range (Sum.elim
        (fun k : Fin p => (X ^ (k : ℕ)) w) (fun k : Fin p => (X ^ (k : ℕ)) w'))) =
        cyc X w ⊔ cyc X w' := by
      intro w w'
      rw [Set.Sum.elim_range, Submodule.span_union, span_pow_eq_cyc hp hxp,
        span_pow_eq_cyc hp hxp]
    have hcross : ∀ (k l : ℕ), B ((X ^ k) w₂) ((X ^ l) (w₂'' : V)) =
        B ((X ^ k) w₁) ((X ^ l) (w₁' : V)) := by
      intro k l
      rw [apply_pow_pow_eq hXB hp hxp, apply_pow_pow_eq hXB hp hxp, ← coe_root_pow_smul,
        ← coe_root_pow_smul, hαc]
    have hpow_mem : ∀ {a : K[X]} {w : V}, w ∈ primaryComponent X a → ∀ k : ℕ,
        (X ^ k) w ∈ primaryComponent X a := fun hw k =>
      invariant_pow (hVg _) k _ hw
    refine exists_isometry_of_families
      (F₁ := Sum.elim (fun k : Fin p => (X ^ (k : ℕ)) w₁) (fun k : Fin p => (X ^ (k : ℕ)) (w₁' : V)))
      (F₂ := Sum.elim (fun k : Fin p => (X ^ (k : ℕ)) w₂) (fun k : Fin p => (X ^ (k : ℕ)) (w₂'' : V)))
      ?_ ((hspan _ _).trans (hsup hinv₁ hmin₁ w₁' hw₁U hw₁'U hw₁0 hw₁g hw₁'))
      ((hspan _ _).trans (hsup hinv₂ hmin₂ w₂'' hw₂U hw₂''U hw₂0 hw₂g hw₂''0))
      hnd₂ (τ := Sum.map τ τ) ?_ ?_
    · rintro (k | k) (l | l)
      · simp only [Sum.elim_inl]
        rw [isotropic_primaryComponent H hg hne (hpow_mem (mem_primaryComponent.mpr hw₁g) _)
            (hpow_mem (mem_primaryComponent.mpr hw₁g) _),
          isotropic_primaryComponent H hg hne (hpow_mem (mem_primaryComponent.mpr hw₂g) _)
            (hpow_mem (mem_primaryComponent.mpr hw₂g) _)]
      · simp only [Sum.elim_inl, Sum.elim_inr]
        exact (hcross k l).symm
      · simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← H.symm.eq, ← H.symm.eq ((X ^ (l : ℕ)) w₂), hcross]
      · simp only [Sum.elim_inr]
        rw [isotropic_primaryComponent H hg' hne' (hpow_mem w₁'.2 _) (hpow_mem w₁'.2 _),
          isotropic_primaryComponent H hg' hne' (hpow_mem w₂''.2 _) (hpow_mem w₂''.2 _)]
    · rintro (k | k)
      · exact hshift _ k
      · exact hshift _ k
    · rintro (k | k)
      · exact hshift _ k
      · exact hshift _ k

end Main

end SUTB

end CFSG.StandardType
