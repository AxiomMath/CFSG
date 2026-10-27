module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.StandardType.OrthF3

private lemma ct_f1_exists_fixed {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hdim : Module.finrank (ZMod 3) V = 5)
    (r : Fin 4 → (V ≃ₗ[ZMod 3] V))
    (hr : ∀ i, Module.finrank (ZMod 3) (LinearMap.range ((r i).toLinearMap - LinearMap.id)) = 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, r i v = v := by
  classical
  have : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  let f : Fin 4 → V →ₗ[ZMod 3] V := fun i => (r i).toLinearMap - LinearMap.id
  have hw : ∀ i, ∃ w : V, w ≠ 0 ∧ LinearMap.range (f i) = Submodule.span (ZMod 3) {w} := by
    intro i
    have hne : LinearMap.range (f i) ≠ ⊥ := by
      intro h
      have hr' := hr i
      rw [h, finrank_bot] at hr'
      exact zero_ne_one hr'
    obtain ⟨w, hwmem, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨w, hwne, ?_⟩
    have hle : Submodule.span (ZMod 3) {w} ≤ LinearMap.range (f i) :=
      Submodule.span_le.mpr (by rintro _ rfl; exact hwmem)
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hwne, hr i])).symm
  choose w hwne hwspan using hw
  let g : Fin 4 → (Fin 4 → V) := fun i => Pi.single i (w i)
  have hcoord : ∀ i (v : V), ∃ c : ZMod 3, c • w i = f i v := by
    intro i v
    have hmem : f i v ∈ Submodule.span (ZMod 3) {w i} := by
      rw [← hwspan i]
      exact ⟨v, rfl⟩
    exact Submodule.mem_span_singleton.mp hmem
  have hTle : LinearMap.range (LinearMap.pi f) ≤ Submodule.span (ZMod 3) (Set.range g) := by
    rintro _ ⟨v, rfl⟩
    choose c hc using fun i => hcoord i v
    have hTv : (LinearMap.pi f) v = ∑ i : Fin 4, c i • g i := by
      funext j
      simp only [LinearMap.pi_apply, Finset.sum_apply, Pi.smul_apply, g]
      rw [Finset.sum_eq_single j]
      · simp [hc j]
      · intro b _ hbj
        simp [hbj]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hTv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfin : Module.finrank (ZMod 3) (LinearMap.range (LinearMap.pi f)) ≤ 4 := by
    calc Module.finrank (ZMod 3) (LinearMap.range (LinearMap.pi f))
        ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range g)) :=
          Submodule.finrank_mono hTle
      _ = (Set.range g).finrank (ZMod 3) := rfl
      _ ≤ Fintype.card (Fin 4) := finrank_range_le_card g
      _ = 4 := by simp
  have hkerdim : 1 ≤ Module.finrank (ZMod 3) (LinearMap.ker (LinearMap.pi f)) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi f)
    rw [hdim] at hrn
    omega
  have hnebot : LinearMap.ker (LinearMap.pi f) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hkerdim
    omega
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnebot
  refine ⟨v, hvne, ?_⟩
  intro i
  have h0 : (LinearMap.pi f) v = 0 := by simpa using hvmem
  have hi : f i v = 0 := by
    have := congrFun h0 i
    simpa [f] using this
  have : (r i) v - v = 0 := by simpa [f] using hi
  exact sub_eq_zero.mp this

private lemma ct_f1_fixed_closure {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (r : Fin 4 → (V ≃ₗ[ZMod 3] V)) {v : V} (hv : ∀ i, r i v = v) :
    ∀ g ∈ Subgroup.closure (Set.range r), g v = v := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact hv i
  | one => simp
  | mul x y _ _ ihx ihy =>
      rw [LinearEquiv.mul_apply, ihy, ihx]
  | inv x _ ih =>
      change x.symm v = v
      rw [LinearEquiv.symm_apply_eq]
      exact ih.symm

theorem ggOrth_rankFour_false {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hdim : Module.finrank (ZMod 3) V = 5)
    (r : Fin 4 → (V ≃ₗ[ZMod 3] V))
    (hr : ∀ i, Module.finrank (ZMod 3) (LinearMap.range ((r i).toLinearMap - LinearMap.id)) = 1)
    {AK AL : Subgroup (V ≃ₗ[ZMod 3] V)} (hKW : AK ≤ Subgroup.closure (Set.range r))
    (hLW : AL ≤ Subgroup.closure (Set.range r))
    {x y : V} (hxy : x ∉ Submodule.span (ZMod 3) {y})
    (hFixL : ∀ v : V, (∀ a ∈ AL, a v = v) → v ∈ Submodule.span (ZMod 3) {x})
    (hFixK : ∀ v : V, (∀ a ∈ AK, a v = v) → v ∈ Submodule.span (ZMod 3) {y}) :
    False := by
  obtain ⟨v, hvne, hvfix⟩ := ct_f1_exists_fixed hdim r hr
  have hAL : ∀ a ∈ AL, a v = v := fun a ha => ct_f1_fixed_closure r hvfix a (hLW ha)
  have hAK : ∀ a ∈ AK, a v = v := fun a ha => ct_f1_fixed_closure r hvfix a (hKW ha)
  have hvL : v ∈ Submodule.span (ZMod 3) {x} := hFixL v hAL
  have hvK : v ∈ Submodule.span (ZMod 3) {y} := hFixK v hAK
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvL
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    exact hvne hc.symm
  have hx : x = c⁻¹ • v := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  exact hxy (by rw [hx]; exact Submodule.smul_mem _ _ hvK)

end CFSG.StandardType.OrthF3

end
