module

public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc5

section Generic

variable {X : Type} [Group X]

theorem oPrimeResidualOf_conj_mem (p : ℕ) {K : Subgroup X} {k : X} (hk : k ∈ K) {y : X}
    (hy : y ∈ oPrimeResidualOf p K) : k * y * k⁻¹ ∈ oPrimeResidualOf p K := by
  unfold oPrimeResidualOf at hy ⊢
  refine Subgroup.closure_induction (p := fun y _ => k * y * k⁻¹ ∈ Subgroup.closure
    {x : X | x ∈ K ∧ ∃ j : ℕ, orderOf x = p ^ j}) ?_ ?_ ?_ ?_ hy
  · rintro x ⟨hxK, j, hj⟩
    refine Subgroup.subset_closure ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), j, ?_⟩
    have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective x
    simpa [MulAut.conj_apply] using this.trans hj
  · simp
  · intro x y _ _ hx hy
    have : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem isSylowTwoOf_subgroupOf_top {P L : Subgroup X} (h : IsSylowTwoOf P L) :
    IsSylowTwoOf (P.subgroupOf L) (⊤ : Subgroup ↥L) := by
  obtain ⟨hPL, hP2, hidx⟩ := h
  refine ⟨le_top, ?_, ?_⟩
  · have := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
    exact this
  · rw [show ((P.subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index = (P.subgroupOf L).index from
      Subgroup.relIndex_top_right _]
    exact hidx

theorem mem_normalizer_subgroupOf_iff {P L : Subgroup X} (hPL : P ≤ L) {x : ↥L} :
    x ∈ Subgroup.normalizer ((P.subgroupOf L : Subgroup ↥L) : Set ↥L) ↔
      (x : X) ∈ Subgroup.normalizer (P : Set X) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    by_cases hy : y ∈ L
    · have := h ⟨y, hy⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hyP
        exact absurd (hPL hyP) hy
      · intro hxy
        exfalso
        apply hy
        have h1 : (x : X) * y * (x : X)⁻¹ ∈ L := hPL hxy
        have h2 : (x : X)⁻¹ * ((x : X) * y * (x : X)⁻¹) * (x : X) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem x.2) h1) x.2
        simpa [mul_assoc] using h2
  · intro h y
    simpa [Subgroup.mem_subgroupOf] using h (y : X)

end Generic

section Hom

variable {A B : Type} [Group A] [Group B]

theorem isSylowTwoOf_map_surjective (α : A →* B) (hα : Function.Surjective α) {P : Subgroup A}
    (hP : IsSylowTwoOf P ⊤) : IsSylowTwoOf (P.map α) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact hP.2.1.of_surjective (α.subgroupMap P) (MonoidHom.subgroupMap_surjective α P)
  · have h1 : (P.map α).index ∣ P.index := Subgroup.index_map_dvd P hα
    have h2 : ¬ 2 ∣ P.index := by
      have := hP.2.2
      rwa [show (P.subgroupOf (⊤ : Subgroup A)).index = P.index from
        Subgroup.relIndex_top_right P] at this
    rw [show ((P.map α).subgroupOf (⊤ : Subgroup B)).index = (P.map α).index from
      Subgroup.relIndex_top_right _]
    exact fun h => h2 (h.trans h1)

theorem map_normalizer_eq_of_ker_le (α : A →* B) (hα : Function.Surjective α) {P : Subgroup A}
    (hker : α.ker ≤ P) :
    (Subgroup.normalizer (P : Set A)).map α = Subgroup.normalizer ((P.map α : Subgroup B) : Set B) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨x * a * x⁻¹, (hx a).1 ha, by simp⟩
    · rintro ⟨a, ha, hab⟩
      refine ⟨x⁻¹ * a * x, (hx (x⁻¹ * a * x)).2 (by simpa [mul_assoc] using ha), ?_⟩
      have h1 : α a = α x * b * (α x)⁻¹ := hab
      simp only [map_mul, map_inv, h1]
      group
  · intro hy
    obtain ⟨x, rfl⟩ := hα y
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro a
    constructor
    · intro ha
      have h1 : α x * α a * (α x)⁻¹ ∈ P.map α := (hy (α a)).1 (Subgroup.mem_map_of_mem α ha)
      obtain ⟨p, hp, hpe⟩ := h1
      have h2 : p⁻¹ * (x * a * x⁻¹) ∈ α.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hpe]
        group
      have h3 := hker h2
      have : x * a * x⁻¹ = p * (p⁻¹ * (x * a * x⁻¹)) := by group
      rw [this]
      exact P.mul_mem hp h3
    · intro ha
      have h1 : α x * α a * (α x)⁻¹ ∈ P.map α := by
        have : α x * α a * (α x)⁻¹ = α (x * a * x⁻¹) := by simp
        rw [this]
        exact Subgroup.mem_map_of_mem α ha
      obtain ⟨p, hp, hpe⟩ := (hy (α a)).2 h1
      have h2 : p⁻¹ * a ∈ α.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hpe]
        group
      have h3 := hker h2
      have : a = p * (p⁻¹ * a) := by group
      rw [this]
      exact P.mul_mem hp h3

end Hom

end SBc5

end CFSG.Quasithin
