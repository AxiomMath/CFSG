module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nK2_blocks_disjoint {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {k : ℕ} {W : Fin k → Submodule (ZMod p) V}
    (hWint : DirectSum.IsInternal W) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (W i) (W j) :=
  hWint.submodule_iSupIndep.pairwiseDisjoint hij

private theorem l05nK2_ker_finrank {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {t : V ≃ₗ[ZMod p] V}
    (ht : GGLinRefl t) :
    Module.finrank (ZMod p) (LinearMap.ker ((t : V →ₗ[ZMod p] V) - LinearMap.id)) =
      Module.finrank (ZMod p) V - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((t : V →ₗ[ZMod p] V) - LinearMap.id)
  have hr : Module.finrank (ZMod p) (LinearMap.range ((t : V →ₗ[ZMod p] V) - LinearMap.id)) = 1 :=
    ht.2
  rw [hr] at h
  omega

private theorem l05nK2_block_finrank_le_one {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {k : ℕ} {W : Fin k → Submodule (ZMod p) V}
    (hWint : DirectSum.IsInternal W) {i j : Fin k} (hij : j ≠ i) {t : V ≃ₗ[ZMod p] V}
    (ht : GGLinRefl t) (htW : (W i).map (t : V →ₗ[ZMod p] V) = W j) :
    Module.finrank (ZMod p) (W i) ≤ 1 := by
  have hdisj : Disjoint (W i) (LinearMap.ker ((t : V →ₗ[ZMod p] V) - LinearMap.id)) := by
    rw [Submodule.disjoint_def]
    intro x hx hxker
    have htx : (t : V →ₗ[ZMod p] V) x = x := by
      have h0 : (t : V →ₗ[ZMod p] V) x - x = 0 := by simpa using hxker
      exact sub_eq_zero.mp h0
    have hxWj : x ∈ W j := by
      have hmem : (t : V →ₗ[ZMod p] V) x ∈ (W i).map (t : V →ₗ[ZMod p] V) :=
        Submodule.mem_map_of_mem hx
      rw [htW] at hmem
      rwa [htx] at hmem
    exact Submodule.disjoint_def.mp (l05nK2_blocks_disjoint hWint (Ne.symm hij)) x hx hxWj
  have hVpos : 1 ≤ Module.finrank (ZMod p) V := by
    have h := LinearMap.finrank_range_add_finrank_ker ((t : V →ₗ[ZMod p] V) - LinearMap.id)
    have hr : Module.finrank (ZMod p)
        (LinearMap.range ((t : V →ₗ[ZMod p] V) - LinearMap.id)) = 1 := ht.2
    rw [hr] at h
    omega
  have hsum := Submodule.finrank_add_finrank_le_of_disjoint hdisj
  rw [l05nK2_ker_finrank ht] at hsum
  omega

private theorem l05nK2_map_injective {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (a : V ≃ₗ[ZMod p] V) :
    Function.Injective (fun U : Submodule (ZMod p) V => U.map (a : V →ₗ[ZMod p] V)) := by
  intro U1 U2 h
  have hcomp : (a.symm : V →ₗ[ZMod p] V).comp (a : V →ₗ[ZMod p] V) = LinearMap.id := by
    have h2 := congrArg (fun e : V ≃ₗ[ZMod p] V => (e : V →ₗ[ZMod p] V)) (inv_mul_cancel a)
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_one] at h2
    rwa [Module.End.mul_eq_comp] at h2
  have hh := congrArg (fun X : Submodule (ZMod p) V => X.map (a.symm : V →ₗ[ZMod p] V)) h
  rw [← Submodule.map_comp (a : V →ₗ[ZMod p] V) (a.symm : V →ₗ[ZMod p] V) U1,
      ← Submodule.map_comp (a : V →ₗ[ZMod p] V) (a.symm : V →ₗ[ZMod p] V) U2,
      hcomp, Submodule.map_id, Submodule.map_id] at hh
  exact hh

private theorem l05nK2_exists_reflection_moving_block {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {k : ℕ} (hk2 : 2 ≤ k)
    {W : Fin k → Submodule (ZMod p) V} (hWint : DirectSum.IsInternal W)
    (hWne : ∀ i, W i ≠ ⊥) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hWmap : ∀ a ∈ A, ∀ i, ∃ j, (W i).map (a : V →ₗ[ZMod p] V) = W j)
    (hirr : ZS.AbsIrred p A) (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (i : Fin k) :
    ∃ (t : V ≃ₗ[ZMod p] V) (j : Fin k), t ∈ A ∧ GGLinRefl t ∧ j ≠ i ∧
      (W i).map (t : V →ₗ[ZMod p] V) = W j := by
  classical
  by_contra hcon
  have hstab : ∀ t ∈ A, GGLinRefl t → (W i).map (t : V →ₗ[ZMod p] V) = W i := by
    intro t ht hrefl
    obtain ⟨j, hj⟩ := hWmap t ht i
    by_contra hne
    have hji : j ≠ i := by
      intro hji
      exact hne (hj.trans (congrArg W hji))
    exact hcon ⟨t, j, ht, hrefl, hji, hj⟩
  let S : Subgroup (V ≃ₗ[ZMod p] V) :=
    { carrier := {a | (W i).map (a : V →ₗ[ZMod p] V) = W i}
      one_mem' := by
        show (W i).map ((1 : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W i
        rw [LinearEquiv.coe_toLinearMap_one, Submodule.map_id]
      mul_mem' := by
        intro a b ha hb
        show (W i).map ((a * b : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W i
        rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
          Submodule.map_comp (b : V →ₗ[ZMod p] V) (a : V →ₗ[ZMod p] V) (W i), hb, ha]
      inv_mem' := by
        intro a ha
        show (W i).map ((a.symm : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = W i
        have hcomp : (a.symm : V →ₗ[ZMod p] V).comp (a : V →ₗ[ZMod p] V) = LinearMap.id := by
          have h2 := congrArg (fun e : V ≃ₗ[ZMod p] V => (e : V →ₗ[ZMod p] V)) (inv_mul_cancel a)
          rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_one] at h2
          rwa [Module.End.mul_eq_comp] at h2
        have h := congrArg (fun X : Submodule (ZMod p) V => X.map (a.symm : V →ₗ[ZMod p] V)) ha
        rw [← Submodule.map_comp (a : V →ₗ[ZMod p] V) (a.symm : V →ₗ[ZMod p] V) (W i),
          hcomp, Submodule.map_id] at h
        exact h.symm }
  have hS : A ≤ S := by
    rw [hgen]
    rw [Subgroup.closure_le]
    intro r hr
    exact hstab r hr.1 hr.2
  have hinv : ∀ a ∈ A, (W i).map (a : V →ₗ[ZMod p] V) = W i := fun a ha => hS ha
  have hW : W i = ⊥ ∨ W i = ⊤ := hirr.1 (W i) fun a ha w hw => by
    rw [← hinv a ha]
    exact Submodule.mem_map_of_mem hw
  rcases hW with hbot | htop
  · exact absurd hbot (hWne i)
  · obtain ⟨j, hji⟩ :=
      Fintype.exists_ne_of_one_lt_card (α := Fin k) (by rw [Fintype.card_fin]; omega) i
    have hdisj : Disjoint (W i) (W j) := l05nK2_blocks_disjoint hWint (Ne.symm hji)
    have hle : W j ≤ W i := by rw [htop]; exact le_top
    have hbotj : W j = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact Submodule.disjoint_def.mp hdisj x (hle hx) hx
    exact absurd hbotj (hWne j)

private theorem l05nK2_finrank_eq_sum {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {k : ℕ}
    {W : Fin k → Submodule (ZMod p) V} (hWint : DirectSum.IsInternal W) :
    Module.finrank (ZMod p) V = ∑ i : Fin k, Module.finrank (ZMod p) (W i) := by
  let he := LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hWint
  rw [← he.finrank_eq]
  rw [Module.finrank_directSum]

theorem ggRC_monomial_of_imprimitive {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {n : ℕ}
    (hn : Module.finrank (ZMod p) V = n) (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (himp : CFSG.Quasithin.SimsG4.IsImprimitiveOnV A) :
    ∃ b : Module.Basis (Fin n) (ZMod p) V, ∀ a ∈ A,
      ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i) := by
  classical
  obtain ⟨k, W, hk2, hWne, hindep, hsup, hWmap⟩ := himp
  have hWint : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).2 ⟨hindep, hsup⟩
  have hIndep : iSupIndep W := hWint.submodule_iSupIndep
  have hWinj : Function.Injective W := hIndep.injective hWne
  have hmoved : ∀ i : Fin k, ∃ (t : V ≃ₗ[ZMod p] V) (j : Fin k),
      t ∈ A ∧ GGLinRefl t ∧ j ≠ i ∧ (W i).map (t : V →ₗ[ZMod p] V) = W j :=
    fun i => l05nK2_exists_reflection_moving_block hk2 hWint hWne A hWmap hirr hgen i
  have hle1 : ∀ i : Fin k, Module.finrank (ZMod p) (W i) ≤ 1 := by
    intro i
    obtain ⟨t, j, _htA, htRefl, hji, htW⟩ := hmoved i
    exact l05nK2_block_finrank_le_one hWint hji htRefl htW
  have heq1 : ∀ i : Fin k, Module.finrank (ZMod p) (W i) = 1 := by
    intro i
    have hpos : 1 ≤ Module.finrank (ZMod p) (W i) := by
      obtain ⟨x, hx, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hWne i)
      have hle : Submodule.span (ZMod p) {x} ≤ W i :=
        (Submodule.span_singleton_le_iff_mem x (W i)).mpr hx
      have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {x}) = 1 :=
        finrank_span_singleton hxne
      calc 1 = Module.finrank (ZMod p) (Submodule.span (ZMod p) {x}) := h1.symm
        _ ≤ Module.finrank (ZMod p) (W i) := Submodule.finrank_mono hle
    exact le_antisymm (hle1 i) hpos
  have hfin : Module.finrank (ZMod p) V = k := by
    rw [l05nK2_finrank_eq_sum hWint]
    simp [heq1]
  have hnk : n = k := by omega
  have hv : ∀ i : Fin k, ∃ x : V, x ∈ W i ∧ x ≠ 0 := fun i =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hWne i)
  let v : Fin k → V := fun i => (hv i).choose
  have hv_mem : ∀ i, v i ∈ W i := fun i => (hv i).choose_spec.1
  have hv_ne : ∀ i, v i ≠ 0 := fun i => (hv i).choose_spec.2
  have hlin : LinearIndependent (ZMod p) v := hIndep.linearIndependent W hv_mem hv_ne
  let e : Fin n ≃ Fin k := finCongr hnk
  let b : Module.Basis (Fin n) (ZMod p) V :=
    basisOfLinearIndependentOfCardEqFinrank' (v ∘ e) (hlin.comp e e.injective) (by
      rw [Fintype.card_fin, hn])
  have hb : ∀ i : Fin n, b i = v (e i) := fun i => by
    simp [b]
  refine ⟨b, ?_⟩
  intro a ha
  let f : Fin k → Fin k := fun i => Classical.choose (hWmap a ha i)
  have hf_spec : ∀ i : Fin k, (W i).map (a : V →ₗ[ZMod p] V) = W (f i) := fun i =>
    Classical.choose_spec (hWmap a ha i)
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hmap : (W i).map (a : V →ₗ[ZMod p] V) = (W j).map (a : V →ₗ[ZMod p] V) := by
      rw [hf_spec i, hf_spec j, hij]
    exact hWinj (l05nK2_map_injective a hmap)
  let fEquiv : Equiv.Perm (Fin k) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  let σ : Equiv.Perm (Fin n) := (e.trans fEquiv).trans e.symm
  have hσ : ∀ i : Fin n, σ i = e.symm (f (e i)) := fun i => by simp [σ, fEquiv]
  have hspan : ∀ i : Fin n, W (f (e i)) = Submodule.span (ZMod p) {v (f (e i))} := by
    intro i
    have h1 : Module.finrank (ZMod p) (W (f (e i))) = 1 := heq1 _
    have hmem : v (f (e i)) ∈ W (f (e i)) := hv_mem _
    have hne : v (f (e i)) ≠ 0 := hv_ne _
    have hle : Submodule.span (ZMod p) {v (f (e i))} ≤ W (f (e i)) :=
      (Submodule.span_singleton_le_iff_mem (v (f (e i))) (W (f (e i)))).mpr hmem
    have hfr : Module.finrank (ZMod p) (Submodule.span (ZMod p) {v (f (e i))}) = 1 :=
      finrank_span_singleton hne
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, h1])).symm
  have hcoeff : ∀ i : Fin n, ∃ c : ZMod p, c ≠ 0 ∧ a (b i) = c • b (σ i) := by
    intro i
    have hmem : a (b i) ∈ W (f (e i)) := by
      have hbi : b i ∈ W (e i) := by rw [hb i]; exact hv_mem (e i)
      have hmap := Submodule.mem_map_of_mem (f := (a : V →ₗ[ZMod p] V)) hbi
      rwa [hf_spec (e i)] at hmap
    rw [hspan i] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hbσ : b (σ i) = v (f (e i)) := by
      rw [hσ i, hb, Equiv.apply_symm_apply]
    refine ⟨c, ?_, ?_⟩
    · intro hc0
      have hzero : a (b i) = 0 := by rw [← hc, hc0, zero_smul]
      have hbi0 : b i = 0 := a.injective (by rw [hzero, map_zero])
      exact b.ne_zero i hbi0
    · rw [hbσ]; exact hc.symm
  choose c hc using hcoeff
  exact ⟨σ, c, fun i => (hc i).1, fun i => (hc i).2⟩

end CFSG.StandardType
