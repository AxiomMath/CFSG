module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bWitt
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Quasithin

theorem eq_of_ne_one_of_card_two {H : Type*} [Group H] (h : Nat.card H = 2) {a b : H}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨x, y, hxy, hall⟩ := Nat.card_eq_two_iff.1 h
  have hm : ∀ g : H, g = x ∨ g = y := fun g => by
    have : g ∈ ({x, y} : Set H) := by
      rw [hall]
      exact Set.mem_univ _
    simpa using this
  rcases hm 1 with h1 | h1 <;> rcases hm a with h2 | h2 <;> rcases hm b with h3 | h3 <;>
    simp_all

section Omega

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem mem_stabS_span_iff {v : W} (hv : v ≠ 0) (g : W ≃ₗ[ZMod 2] W) :
    g ∈ stabS (Submodule.span (ZMod 2) {v}) ↔ g v = v := by
  constructor
  · intro hg
    have hgv := (hg v).1 (Submodule.mem_span_singleton_self v)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hgv
    rcases zmod2_cases c with rfl | rfl
    · exfalso
      rw [zero_smul] at hc
      exact hv (g.map_eq_zero_iff.1 hc.symm)
    · rw [one_smul] at hc
      exact hc.symm
  · intro hgv x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
      rw [← hc, map_smul, hgv]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · intro hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
      have hgsymm : g.symm v = v := by
        rw [LinearEquiv.symm_apply_eq]
        exact hgv.symm
      have hxc : x = c • v := by
        have h1 : x = g.symm (g x) := (g.symm_apply_apply x).symm
        rw [h1, ← hc, map_smul, hgsymm]
      rw [hxc]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem orbit_eq_sing {H : Subgroup (W ≃ₗ[ZMod 2] W)} (q : W → ZMod 2)
    (hH : H ≤ orthogonalSubgroupOf q) {v : W} (hv : v ≠ 0) (hqv : q v = 0)
    (htrans : ∀ w : W, w ≠ 0 → q w = 0 → ∃ γ ∈ H, γ v = w) :
    MulAction.orbit H v = {x : W | x ≠ 0 ∧ q x = 0} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hg : (g : W ≃ₗ[ZMod 2] W) ∈ orthogonalSubgroupOf q := hH g.2
    refine ⟨?_, ?_⟩
    · intro h0
      apply hv
      exact (g : W ≃ₗ[ZMod 2] W).map_eq_zero_iff.1 h0
    · show q ((g : W ≃ₗ[ZMod 2] W) v) = 0
      rw [hg v, hqv]
  · rintro ⟨hx0, hxq⟩
    obtain ⟨γ, hγ, hγv⟩ := htrans x hx0 hxq
    exact ⟨⟨γ, hγ⟩, hγv⟩

theorem omega_sing_transitive (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0)
    (hcount : Nat.card {v : W // v ≠ 0 ∧ q v = 0} = 35)
    (Ω : Subgroup (W ≃ₗ[ZMod 2] W)) (hΩ : Ω ≤ orthogonalSubgroupOf q)
    (hrel : Ω.relIndex (orthogonalSubgroupOf q) = 2) :
    ∀ v w : W, v ≠ 0 → w ≠ 0 → q v = 0 → q w = 0 → ∃ γ ∈ Ω, γ v = w := by
  intro v w hv hw hqv hqw
  obtain ⟨γ0, hγ0G, hγ0v⟩ := singular_transitive q B hq hB hv hw hqv hqw
  by_cases hγ0Ω : γ0 ∈ Ω
  · exact ⟨γ0, hγ0Ω, hγ0v⟩
  have hcount' : Set.ncard {x : W | x ≠ 0 ∧ q x = 0} = 35 := by
    rw [← Nat.card_coe_set_eq]
    exact hcount
  have htransG : ∀ x : W, x ≠ 0 → q x = 0 → ∃ γ ∈ orthogonalSubgroupOf q, γ v = x :=
    fun x hx hqx => singular_transitive q B hq hB hv hx hqv hqx
  have hindex : (MulAction.stabilizer (orthogonalSubgroupOf q) v).index = 35 := by
    rw [MulAction.index_stabilizer, orbit_eq_sing q le_rfl hv hqv htransG, hcount']
  have hA : ∃ g ∈ orthogonalSubgroupOf q, g v = v ∧ g ∉ Ω := by
    by_contra hcon
    push Not at hcon
    have hle : MulAction.stabilizer (orthogonalSubgroupOf q) v ≤ Ω.subgroupOf (orthogonalSubgroupOf q) := by
      intro g hg
      rw [Subgroup.mem_subgroupOf]
      exact hcon g.1 g.2 (MulAction.mem_stabilizer_iff.1 hg)
    have h1 := Subgroup.relIndex_mul_index hle
    have hΩ2 : (Ω.subgroupOf (orthogonalSubgroupOf q)).index = 2 := hrel
    rw [hindex, hΩ2] at h1
    omega
  obtain ⟨g, hgG, hgv, hgΩ⟩ := hA
  set Ω' : Subgroup (orthogonalSubgroupOf q) := Ω.subgroupOf (orthogonalSubgroupOf q) with hΩ'
  have hΩ'2 : Ω'.index = 2 := hrel
  haveI : Ω'.Normal := Subgroup.normal_of_index_eq_two hΩ'2
  let γ' : orthogonalSubgroupOf q := ⟨γ0, hγ0G⟩
  let g' : orthogonalSubgroupOf q := ⟨g, hgG⟩
  have hγ'ne : γ' ∉ Ω' := fun h => hγ0Ω ((Subgroup.mem_subgroupOf).1 h)
  have hg'ne : g' ∉ Ω' := fun h => hgΩ ((Subgroup.mem_subgroupOf).1 h)
  have hpair : (γ' : orthogonalSubgroupOf q ⧸ Ω') = (g' : orthogonalSubgroupOf q ⧸ Ω') := by
    apply eq_of_ne_one_of_card_two (H := orthogonalSubgroupOf q ⧸ Ω') hΩ'2
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact hγ'ne
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact hg'ne
  have hx : γ'⁻¹ * g' ∈ Ω' := QuotientGroup.eq.1 hpair
  have hconj : g' * (γ'⁻¹ * g') * g'⁻¹ ∈ Ω' := Subgroup.Normal.conj_mem inferInstance _ hx g'
  have hω : γ' * g'⁻¹ ∈ Ω' := by
    have heq : γ' * g'⁻¹ = (g' * (γ'⁻¹ * g') * g'⁻¹)⁻¹ := by group
    rw [heq]
    exact Ω'.inv_mem hconj
  have hginv : (g⁻¹ : W ≃ₗ[ZMod 2] W) v = v := by
    show g.symm v = v
    rw [LinearEquiv.symm_apply_eq]
    exact hgv.symm
  refine ⟨((γ' * g'⁻¹ : orthogonalSubgroupOf q) : W ≃ₗ[ZMod 2] W), (Subgroup.mem_subgroupOf).1 hω, ?_⟩
  show γ0 ((g⁻¹ : W ≃ₗ[ZMod 2] W) v) = w
  rw [hginv, hγ0v]

theorem relIndex_stabS_span (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0)
    (hcount : Nat.card {v : W // v ≠ 0 ∧ q v = 0} = 35)
    (Ω : Subgroup (W ≃ₗ[ZMod 2] W)) (hΩ : Ω ≤ orthogonalSubgroupOf q)
    (hrel : Ω.relIndex (orthogonalSubgroupOf q) = 2) {v : W} (hv : v ≠ 0) (hqv : q v = 0) :
    (stabS (Submodule.span (ZMod 2) {v})).relIndex Ω = 35 := by
  have htransΩ := omega_sing_transitive q B hq hB hcount Ω hΩ hrel
  have hK : (stabS (Submodule.span (ZMod 2) {v})).subgroupOf Ω = MulAction.stabilizer Ω v := by
    ext ω
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    exact mem_stabS_span_iff hv ω
  have hcount' : Set.ncard {x : W | x ≠ 0 ∧ q x = 0} = 35 := by
    rw [← Nat.card_coe_set_eq]
    exact hcount
  have horb : MulAction.orbit Ω v = {x : W | x ≠ 0 ∧ q x = 0} :=
    orbit_eq_sing q hΩ hv hqv (fun x hx hqx => htransΩ v x hv hx hqv hqx)
  rw [Subgroup.relIndex, hK, MulAction.index_stabilizer, horb, hcount']

end Omega

end CFSG.Quasithin.H13.C1294
