module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38Syl

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts

section Transport

variable {M N : Type*} [Group M] [Group N]

theorem congr_apply_e (e : M ≃* N) (φ : MulAut M) (x : M) :
    MulAut.congr e φ (e x) = e (φ x) := by
  simp [MulAut.congr_apply]

theorem mem_u38Fix_congr (e : M ≃* N) (φ : MulAut M) (x : M) :
    e x ∈ u38Fix (MulAut.congr e φ) ↔ x ∈ u38Fix φ := by
  rw [mem_u38Fix, mem_u38Fix, congr_apply_e]
  exact e.injective.eq_iff

theorem u38Fix_congr (e : M ≃* N) (φ : MulAut M) :
    u38Fix (MulAut.congr e φ) = (u38Fix φ).map e.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [mem_u38Fix_congr, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', hxx⟩
    have : x' = x := e.injective hxx
    rw [← this]
    exact hx'

theorem card_u38Fix_congr (e : M ≃* N) (φ : MulAut M) :
    Nat.card (u38Fix (MulAut.congr e φ)) = Nat.card (u38Fix φ) := by
  rw [u38Fix_congr]
  exact Subgroup.card_map_of_injective e.injective

theorem u38Two_congr (e : M ≃* N) (φ : MulAut M) :
    u38Two (MulAut.congr e φ) = (u38Two φ).map e.toMonoidHom := by
  rw [u38Two, u38Two, MonoidHom.map_closure]
  congr 1
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, k, hk⟩
    refine ⟨x, ⟨(mem_u38Fix_congr e φ x).mp hx, k, ?_⟩, rfl⟩
    apply e.injective
    rw [map_pow, map_one]
    exact hk
  · rintro ⟨x', ⟨hx', k, hk⟩, hxx⟩
    have : x' = x := e.injective hxx
    subst this
    refine ⟨(mem_u38Fix_congr e φ x').mpr hx', k, ?_⟩
    rw [← map_pow, hk, map_one]

@[expose] def U38Hyps (Ū : Type*) [Group Ū] (α β : MulAut Ū) : Prop :=
  α ^ 3 = 1 ∧ β ^ 3 = 1 ∧ α * β = β * α ∧ ¬ KFacts.IsInnerAut α ∧
    (∃ u ∈ u38Fix α, u ^ 4 = 1 ∧ u ^ 2 ≠ 1) ∧ β ≠ 1 ∧ 7 ∣ Nat.card (u38Fix β)

theorem U38Hyps.congr (e : M ≃* N) {α β : MulAut M} (h : U38Hyps M α β) :
    U38Hyps N (MulAut.congr e α) (MulAut.congr e β) := by
  obtain ⟨hα3, hβ3, hαβ, hαout, ⟨u, hu, hu4, hu2⟩, hβ1, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ⟨e u, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← map_pow, hα3, map_one]
  · rw [← map_pow, hβ3, map_one]
  · rw [← map_mul, ← map_mul, hαβ]
  · rwa [isInnerAut_congr]
  · exact (mem_u38Fix_congr e α u).mpr hu
  · rw [← map_pow, hu4, map_one]
  · intro h1
    apply hu2
    apply e.injective
    rw [map_pow, h1, map_one]
  · intro h1
    apply hβ1
    exact (map_eq_one_iff _ (MulAut.congr e).injective).mp h1
  · rwa [card_u38Fix_congr]

theorem syl_conclusion_congr (e : M ≃* N) {α β : MulAut M}
    (h : ∃ T : Subgroup N, T ≤ u38Fix (MulAut.congr e α) ∧ Nat.card T = 8 ∧
      (∀ x ∈ T, MulAut.congr e β x ∈ T) ∧ T ≤ u38Comm T (MulAut.congr e β)) :
    ∃ T : Subgroup M, T ≤ u38Fix α ∧ Nat.card T = 8 ∧ (∀ x ∈ T, β x ∈ T) ∧
      T ≤ u38Comm T β := by
  obtain ⟨T, hTf, hT8, hTβ, hTc⟩ := h
  refine ⟨T.comap e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have := hTf hx
    exact (mem_u38Fix_congr e α x).mp this
  · rw [← hT8]
    have h1 : T.comap e.toMonoidHom = T.map e.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm e T
    rw [h1]
    exact Subgroup.card_map_of_injective e.symm.injective
  · intro x hx
    have := hTβ (e x) hx
    rw [congr_apply_e] at this
    exact this
  · intro x hx
    have hx' : e x ∈ T := hx
    have h1 := hTc hx'
    have h2 : u38Comm T (MulAut.congr e β) ≤
        (u38Comm (T.comap e.toMonoidHom) β).map e.toMonoidHom := by
      rw [u38Comm]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨w, hw, rfl⟩
      obtain ⟨w₀, rfl⟩ := e.surjective w
      refine ⟨w₀ * (β w₀)⁻¹, Subgroup.subset_closure ⟨w₀, hw, rfl⟩, ?_⟩
      simp [congr_apply_e]
    obtain ⟨y, hy, hyx⟩ := h2 h1
    have : y = x := e.injective hyx
    rw [← this]
    exact hy

theorem mem_perfectResidual_congr [Finite M] [Finite N] (e : M ≃* N) (φ : MulAut M) (x : M) :
    e x ∈ (perfectResidual (u38Fix (MulAut.congr e φ))).map
        (u38Fix (MulAut.congr e φ)).subtype ↔
      x ∈ (perfectResidual (u38Fix φ)).map (u38Fix φ).subtype := by
  have h1 := map_inSubgroup_perfectResidual_hom e.toMonoidHom (u38Fix φ)
  rw [← u38Fix_congr] at h1
  change e x ∈ inSubgroup perfectResidual (u38Fix (MulAut.congr e φ)) ↔
    x ∈ inSubgroup perfectResidual (u38Fix φ)
  rw [← h1]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := e.injective hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem p3_conclusion_congr (e : M ≃* N) {α : MulAut M} {x : M}
    (h : e x ∈ u38Two (MulAut.congr e α) ∧ ∀ z ∈ u38Two (MulAut.congr e α),
      (∃ j : ℕ, z ^ 3 ^ j = 1) →
        z ∈ Subgroup.closure {y | ∃ g ∈ u38Two (MulAut.congr e α), y = g * e x * g⁻¹}) :
    x ∈ u38Two α ∧ ∀ z ∈ u38Two α, (∃ j : ℕ, z ^ 3 ^ j = 1) →
      z ∈ Subgroup.closure {y | ∃ g ∈ u38Two α, y = g * x * g⁻¹} := by
  obtain ⟨hx, hz⟩ := h
  rw [u38Two_congr] at hx hz
  refine ⟨?_, fun z hzI ⟨j, hj⟩ => ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := e.injective hyx
    rwa [← this]
  · have hez : e z ∈ (u38Two α).map e.toMonoidHom := ⟨z, hzI, rfl⟩
    have hej : (e z) ^ 3 ^ j = 1 := by rw [← map_pow, hj, map_one]
    have h1 := hz (e z) hez ⟨j, hej⟩
    have h2 : Subgroup.closure {y | ∃ g ∈ (u38Two α).map e.toMonoidHom, y = g * e x * g⁻¹} ≤
        (Subgroup.closure {y | ∃ g ∈ u38Two α, y = g * x * g⁻¹}).map e.toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨g, ⟨g₀, hg₀, rfl⟩, rfl⟩
      exact ⟨g₀ * x * g₀⁻¹, Subgroup.subset_closure ⟨g₀, hg₀, rfl⟩, by simp⟩
    obtain ⟨y, hy, hyz⟩ := h2 h1
    have : y = z := e.injective hyz
    rwa [← this]

end Transport

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
