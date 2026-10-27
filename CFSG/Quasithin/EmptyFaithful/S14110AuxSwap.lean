module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxCases

public section

namespace CFSG.Quasithin.S14110

open CFSG.Open CFSG.LieType.BorelTits Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cj_cj (g h : G) (X : Subgroup G) : cj g (cj h X) = cj (g * h) X := (cj_mul g h X).symm

omit [Finite G] in
theorem cj_inv_cj (g : G) (X : Subgroup G) : cj g⁻¹ (cj g X) = X := by
  rw [cj_cj, inv_mul_cancel, cj_one]

omit [Finite G] in
theorem cj_injective (g : G) {X Y : Subgroup G} (h : cj g X = cj g Y) : X = Y := by
  have := congrArg (cj g⁻¹) h
  rwa [cj_inv_cj, cj_inv_cj] at this

omit [Finite G] in
theorem cj_le {M X : Subgroup G} (hXM : X ≤ M) {m : G} (hm : m ∈ M) : cj m X ≤ M := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_cj_iff.1 hy
  exact M.mul_mem (M.mul_mem hm (hXM hx)) (M.inv_mem hm)

omit [Finite G] in
theorem cj_comm {g : G} {A B : Subgroup G} (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ cj g A, ∀ y ∈ cj g B, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := mem_cj_iff.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_cj_iff.1 hy
  have := h a ha b hb
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [this]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem two_conj {M X W : Subgroup G} {c : G} (hX : A4Data X W c) (hXM : X ≤ M)
    (hDC : ∀ m ∈ M, cj m X = X ∨ ∀ x ∈ X, ∀ y ∈ cj m X, x * y = y * x)
    (hrank : CFSG.Open.pRank 3 M ≤ 2) {m₀ : G} (hm₀ : m₀ ∈ M) (hne : cj m₀ X ≠ X) :
    ∀ m ∈ M, cj m X = X ∨ cj m X = cj m₀ X := by
  intro m hm
  by_contra hcon
  have hcon1 : cj m X ≠ X := fun e => hcon (Or.inl e)
  have hcon2 : cj m X ≠ cj m₀ X := fun e => hcon (Or.inr e)
  have h12 : ∀ x ∈ X, ∀ y ∈ cj m₀ X, x * y = y * x := (hDC m₀ hm₀).resolve_left hne
  have h13 : ∀ x ∈ X, ∀ y ∈ cj m X, x * y = y * x := (hDC m hm).resolve_left hcon1
  have hmm : m₀⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hm₀) hm
  have hne' : cj (m₀⁻¹ * m) X ≠ X := by
    intro e
    apply hcon2
    have : cj m X = cj m₀ (cj (m₀⁻¹ * m) X) := by
      rw [cj_cj, mul_inv_cancel_left]
    rw [this, e]
  have h23' := (hDC _ hmm).resolve_left hne'
  have h23 : ∀ x ∈ cj m₀ X, ∀ y ∈ cj m X, x * y = y * x := by
    have := cj_comm (g := m₀) h23'
    intro x hx y hy
    apply this x hx
    rw [cj_cj, mul_inv_cancel_left]
    exact hy
  have hY : A4Data (cj m₀ X) (cj m₀ W) (m₀ * c * m₀⁻¹) := hX.map (MulAut.conj m₀)
  have hZ : A4Data (cj m X) (cj m W) (m * c * m⁻¹) := hX.map (MulAut.conj m)
  exact false_of_three_commuting hrank hX hY hZ hXM (cj_le hXM hm₀) (cj_le hXM hm) h12 h13 h23

section Swap

variable {M X Y : Subgroup G}

omit [Finite G] in
theorem cj_sup (g : G) (A B : Subgroup G) : cj g (A ⊔ B) = cj g A ⊔ cj g B :=
  Subgroup.map_sup _ _ _

structure TwoConj (M X Y : Subgroup G) : Prop where
  ne : Y ≠ X
  exists_conj : ∃ m₀ ∈ M, Y = cj m₀ X
  two : ∀ m ∈ M, cj m X = X ∨ cj m X = Y

namespace TwoConj

omit [Finite G] in
theorem cj_Y (h : TwoConj M X Y) {m : G} (hm : m ∈ M) :
    (cj m X = X → cj m Y = Y) ∧ (cj m X = Y → cj m Y = X) := by
  obtain ⟨m₀, hm₀, hY⟩ := h.exists_conj
  have hcm : cj m Y = cj (m * m₀) X := by rw [hY, cj_cj]
  have h1 : cj m Y = X ∨ cj m Y = Y := by
    rw [hcm]; exact h.two _ (M.mul_mem hm hm₀)
  constructor
  · intro hX
    rcases h1 with h2 | h2
    · exact absurd (cj_injective m (h2.trans hX.symm)) h.ne
    · exact h2
  · intro hX
    rcases h1 with h2 | h2
    · exact h2
    · exact absurd (cj_injective m (h2.trans hX.symm)) h.ne

omit [Finite G] in
theorem mem_normalizer_Y_iff (h : TwoConj M X Y) {m : G} (hm : m ∈ M) :
    m ∈ normalizer (Y : Set G) ↔ m ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff_cj, mem_normalizer_iff_cj]
  constructor
  · intro hY
    rcases h.two m hm with h1 | h1
    · exact h1
    · exact absurd ((h.cj_Y hm).2 h1 |>.symm.trans hY) h.ne.symm
  · intro hX
    exact (h.cj_Y hm).1 hX

omit [Finite G] in
theorem swap (h : TwoConj M X Y) {m : G} (hm : m ∈ M) (hmX : m ∉ normalizer (X : Set G)) :
    cj m X = Y ∧ cj m Y = X := by
  rw [mem_normalizer_iff_cj] at hmX
  have h1 : cj m X = Y := (h.two m hm).resolve_left hmX
  exact ⟨h1, (h.cj_Y hm).2 h1⟩

omit [Finite G] in
theorem index_two (h : TwoConj M X Y) :
    ((normalizer (X : Set G)).subgroupOf M).index = 2 := by
  obtain ⟨m₀, hm₀, hY⟩ := h.exists_conj
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨m₀, hm₀⟩, fun b => ?_⟩
  have hb := b.2
  have hbm : (b : G) * m₀ ∈ M := M.mul_mem hb hm₀
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
    mem_normalizer_iff_cj, mem_normalizer_iff_cj]
  have hcm : cj (b : G) Y = cj ((b : G) * m₀) X := by rw [hY, cj_cj]
  rcases h.two b hb with h1 | h1
  · have h2 := (h.cj_Y hb).1 h1
    right
    refine ⟨h1, fun h3 => ?_⟩
    rw [← hcm, h2] at h3
    exact h.ne h3
  · have h2 := (h.cj_Y hb).2 h1
    left
    refine ⟨?_, fun h3 => h.ne (h1.symm.trans h3)⟩
    rw [← hcm, h2]

omit [Finite G] in
theorem exists_mem_not_mem_normalizer (h : TwoConj M X Y) {T : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTM : T ≤ M) : ∃ t ∈ T, t ∉ normalizer (X : Set G) := by
  by_contra hcon
  have hTN : T ≤ normalizer (X : Set G) := fun t ht => by_contra fun hn => hcon ⟨t, ht, hn⟩
  have h1 : T.subgroupOf M ≤ (normalizer (X : Set G)).subgroupOf M := fun t ht => hTN ht
  have h2 := Subgroup.index_dvd_of_le h1
  rw [h.index_two] at h2
  exact not_two_dvd_index_subgroupOf hT hTM h2

end TwoConj

end Swap


end CFSG.Quasithin.S14110
