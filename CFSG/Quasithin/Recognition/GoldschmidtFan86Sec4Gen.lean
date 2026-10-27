module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.Fan86

variable {G : Type*} [Group G]

theorem mem_normalizer_of_characteristic {R K : Subgroup G} (hKR : K ≤ R)
    (hchar : (K.subgroupOf R).Characteristic) {n : G} (hn : n ∈ Subgroup.normalizer (R : Set G)) :
    n ∈ Subgroup.normalizer (K : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (R : Set G), ∀ x ∈ K, n * x * n⁻¹ ∈ K := by
    intro n hn x hx
    let φ : R ≃* R := R.normalizerMonoidHom ⟨n, hn⟩
    have hfix := Subgroup.characteristic_iff_map_eq.mp hchar φ
    have hy : (⟨x, hKR hx⟩ : R) ∈ K.subgroupOf R := hx
    have hyK : φ ⟨x, hKR hx⟩ ∈ K.subgroupOf R := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hy
    have := R.normalizerMonoidHom_apply_apply_coe ⟨n, hn⟩ ⟨x, hKR hx⟩
    exact this ▸ hyK
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_of_normal_subgroupOf {K M : Subgroup G} (hKM : K ≤ M)
    (hN : (K.subgroupOf M).Normal) {g : G} (hg : g ∈ M) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have key : ∀ g ∈ M, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    intro g hg x hx
    have hx' : (⟨x, hKM hx⟩ : M) ∈ K.subgroupOf M := hx
    have := hN.conj_mem _ hx' ⟨g, hg⟩
    exact this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {B R : Subgroup G} [Finite B]
    (hB : IsPGroup p B) (hRB : R ≤ B) (hne : ∃ x ∈ B, x ∉ R) :
    ∃ n ∈ B, n ∉ R ∧ n ∈ Subgroup.normalizer (R : Set G) := by
  have : Group.IsNilpotent ↥B := hB.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥B)
  obtain ⟨x, hxB, hxR⟩ := hne
  have hlt : R.subgroupOf B < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hxR ?_
    have : (⟨x, hxB⟩ : B) ∈ R.subgroupOf B := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨n', hn', hn'R⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  refine ⟨n'.1, n'.2, hn'R, ?_⟩
  have key : ∀ m : B, m ∈ Subgroup.normalizer ((R.subgroupOf B : Subgroup B) : Set B) →
      ∀ x ∈ R, (m : G) * x * (m : G)⁻¹ ∈ R := by
    intro m hm x hx
    have hx' : (⟨x, hRB hx⟩ : B) ∈ R.subgroupOf B := hx
    have := (Subgroup.mem_normalizer_iff.1 hm ⟨x, hRB hx⟩).1 hx'
    exact this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n' hn' x, fun hx => ?_⟩
  have := key n'⁻¹ (inv_mem hn') _ hx
  simpa [mul_assoc] using this

theorem characteristic_map_subtype {H R : Subgroup G} (hRH : R ≤ H) {K0 : Subgroup H}
    (hchar : (K0.subgroupOf (R.subgroupOf H)).Characteristic) :
    ((K0.map H.subtype).subgroupOf R).Characteristic := by
  refine ⟨fun ψ => ?_⟩
  let e : ↥(R.subgroupOf H) ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRH
  let ψ' : ↥(R.subgroupOf H) ≃* ↥(R.subgroupOf H) := e.trans (ψ.trans e.symm)
  have hfix := hchar.fixed ψ'
  have mem : ∀ z : ↥R, z ∈ (K0.map H.subtype).subgroupOf R ↔
      e.symm z ∈ K0.subgroupOf (R.subgroupOf H) := by
    intro z
    constructor
    · rintro ⟨y, hy, hyz⟩
      have : y = ((e.symm z : ↥(R.subgroupOf H)) : ↥H) := Subtype.ext hyz
      rw [Subgroup.mem_subgroupOf, ← this]
      exact hy
    · intro hz
      exact ⟨((e.symm z : ↥(R.subgroupOf H)) : ↥H), hz, rfl⟩
  ext z
  have hfix_mem : ψ' (e.symm z) ∈ K0.subgroupOf (R.subgroupOf H) ↔
      e.symm z ∈ K0.subgroupOf (R.subgroupOf H) := Subgroup.ext_iff.1 hfix (e.symm z)
  have h1 : ψ z ∈ (K0.map H.subtype).subgroupOf R ↔
      ψ' (e.symm z) ∈ K0.subgroupOf (R.subgroupOf H) := by
    rw [mem]
    simp [ψ']
  show ψ z ∈ (K0.map H.subtype).subgroupOf R ↔ z ∈ (K0.map H.subtype).subgroupOf R
  rw [h1, hfix_mem, mem]

end CFSG.Quasithin.Fan86
