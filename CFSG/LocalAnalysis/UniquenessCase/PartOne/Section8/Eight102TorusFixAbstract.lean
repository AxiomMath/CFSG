module

public import CFSG.GroupTheory.SylowAutConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

@[expose] def TorusFixConcl (X : Type*) [Group X] (n : ℕ) : Prop :=
  ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
    ∀ Θ : Subgroup (MulAut X), IsPGroup 3 Θ → (∀ α ∈ Θ, ∀ s ∈ S, α s ∈ S) →
      ∃ q : ℕ, q.Prime ∧ q ∣ 2 ^ n + 1 ∧ ∃ x : X, orderOf x = q ∧
        (∀ s ∈ S, x * s = s * x) ∧ ∀ α ∈ Θ, α x = x

theorem TorusFixConcl.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : TorusFixConcl Y n) : TorusFixConcl X n := by
  intro S hS hSi Θ hΘ hΘS
  let S' : Subgroup Y := S.map e.toMonoidHom
  have hS' : IsPGroup 3 S' := hS.map e.toMonoidHom
  have hS'i : ¬ 3 ∣ S'.index := by
    change ¬ 3 ∣ (S.map e.toMonoidHom).index
    rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective S]
    exact hSi
  let Θ' : Subgroup (MulAut Y) := Θ.map (MulAut.congr e).toMonoidHom
  have hΘ' : IsPGroup 3 Θ' := hΘ.map (MulAut.congr e).toMonoidHom
  have hΘ'S' : ∀ α ∈ Θ', ∀ s ∈ S', α s ∈ S' := by
    intro α hα s hs
    obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hα
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    change (MulAut.congr e β) (e.toMonoidHom t) ∈ S'
    have hcongr : (MulAut.congr e β) (e.toMonoidHom t) = e.toMonoidHom (β t) := by
      simp [MulAut.congr_apply]
    rw [hcongr]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hΘS β hβ t ht)
  obtain ⟨q, hq, hqn, y, hyq, hyc, hyfix⟩ := h S' hS' hS'i Θ' hΘ' hΘ'S'
  refine ⟨q, hq, hqn, e.symm y, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hyq]
  · intro s hs
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      hyc (e s) (Subgroup.mem_map_of_mem e.toMonoidHom hs)
  · intro α hα
    apply e.injective
    have h := hyfix (MulAut.congr e α) (Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hα)
    simpa [MulAut.congr_apply] using h

theorem torusFixConcl_of_torus {X : Type*} [Group X] [Finite X] {n q : ℕ} {S₀ : Subgroup X}
    (hS₀ : IsPGroup 3 S₀) (hS₀i : ¬ 3 ∣ S₀.index) {φ : MulAut X} (hφ : ∃ k : ℕ, φ ^ (3 ^ k) = 1)
    (hφS : ∀ s ∈ S₀, φ s ∈ S₀)
    (hφi : ¬ 3 ∣ ((MulAut.conj : X →* MulAut X).range ⊔ zpowers φ).index) (hq : q.Prime)
    (hqn : q ∣ 2 ^ n + 1) {x₀ : X} (hx₀q : orderOf x₀ = q) (hx₀ : ∀ s ∈ S₀, x₀ * s = s * x₀)
    (hφx₀ : φ x₀ = x₀) : TorusFixConcl X n := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S hS hSi Θ hΘ hΘS
  obtain ⟨x, hxord, hxc, hxfix⟩ :=
    CFSG.exists_orderOf_eq_forall_commute_forall_apply_eq hS₀ hS₀i hφ hφS hφi hx₀ hφx₀
      hS hSi hΘ hΘS
  exact ⟨q, hq, hqn, x, hxord.trans hx₀q, hxc, hxfix⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
