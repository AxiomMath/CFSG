module

public import CFSG.Quasithin.EmptyFaithful.ModCAbs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.ModC

open CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem coset_decomp {I₂ T₀ : Subgroup G} (hidx : T₀.relIndex I₂ ∣ 3) (hT₀2 : IsPGroup 2 ↥T₀)
    {g : G} (hg : g ∈ I₂) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∀ x ∈ I₂, x ∈ T₀ ∨ g⁻¹ * x ∈ T₀ ∨ g * x ∈ T₀ := by
  classical
  have hgT : g ∉ T₀ := by
    intro h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT₀2) ⟨g, h⟩
    have h1 : orderOf (⟨g, h⟩ : ↥T₀) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hg3))
    rw [hk] at h1
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
      have := h2.trans h1
      omega
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact hg1 (congrArg Subtype.val hk)
  have hginv2 : (g ^ 2)⁻¹ = g := inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hg3)
  have hg2T : g ^ 2 ∉ T₀ := by
    intro h
    apply hgT
    have := T₀.inv_mem h
    rwa [hginv2] at this
  let T' : Subgroup ↥I₂ := T₀.subgroupOf I₂
  let g' : ↥I₂ := ⟨g, hg⟩
  let _ : Fintype (↥I₂ ⧸ T') := Fintype.ofFinite _
  have hcard : Fintype.card (↥I₂ ⧸ T') ∣ 3 := by
    have : Nat.card (↥I₂ ⧸ T') = T₀.relIndex I₂ := rfl
    rw [← Nat.card_eq_fintype_card, this]
    exact hidx
  have hmemT' : ∀ y : ↥I₂, y ∈ T' ↔ (y : G) ∈ T₀ := fun y => Iff.rfl
  have h12 : ((1 : ↥I₂) : ↥I₂ ⧸ T') ≠ (g' : ↥I₂ ⧸ T') := by
    intro h
    have := QuotientGroup.eq.mp h
    apply hgT
    have h' := (hmemT' _).mp this
    simpa [g'] using h'
  have h13 : ((1 : ↥I₂) : ↥I₂ ⧸ T') ≠ ((g' ^ 2 : ↥I₂) : ↥I₂ ⧸ T') := by
    intro h
    have := QuotientGroup.eq.mp h
    apply hg2T
    have h' := (hmemT' _).mp this
    simpa [g'] using h'
  have h23 : (g' : ↥I₂ ⧸ T') ≠ ((g' ^ 2 : ↥I₂) : ↥I₂ ⧸ T') := by
    intro h
    have := QuotientGroup.eq.mp h
    apply hgT
    have h' := (hmemT' _).mp this
    have e : (g' : ↥I₂)⁻¹ * g' ^ 2 = g' := by group
    rw [e] at h'
    exact h'
  let S : Finset (↥I₂ ⧸ T') := {((1 : ↥I₂) : ↥I₂ ⧸ T'), (g' : ↥I₂ ⧸ T'), ((g' ^ 2 : ↥I₂) : ↥I₂ ⧸ T')}
  have hS : S.card = 3 := Finset.card_eq_three.mpr ⟨_, _, _, h12, h13, h23, rfl⟩
  have hle : Fintype.card (↥I₂ ⧸ T') ≤ 3 := Nat.le_of_dvd (by norm_num) hcard
  have hSuniv : S = Finset.univ := by
    apply Finset.eq_univ_of_card
    have := Finset.card_le_univ S
    omega
  intro x hx
  have hx' : ((⟨x, hx⟩ : ↥I₂) : ↥I₂ ⧸ T') ∈ S := by rw [hSuniv]; exact Finset.mem_univ _
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with h | h | h
  · left
    have := (hmemT' _).mp (QuotientGroup.eq.mp h)
    simpa using this
  · right; left
    have h1 := (hmemT' _).mp (QuotientGroup.eq.mp h)
    have h2 := T₀.inv_mem h1
    have e : (((⟨x, hx⟩ : ↥I₂)⁻¹ * g' : ↥I₂) : G)⁻¹ = g⁻¹ * x := by simp [g']
    rw [e] at h2
    exact h2
  · right; right
    have h1 := (hmemT' _).mp (QuotientGroup.eq.mp h)
    have h2 := T₀.inv_mem h1
    have e : (((⟨x, hx⟩ : ↥I₂)⁻¹ * g' ^ 2 : ↥I₂) : G)⁻¹ = g * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, g', mul_inv_rev, inv_inv]
      rw [hginv2]
    rw [e] at h2
    exact h2

omit [Finite G] in
theorem mem_normalizer_of_conj_le {V : Subgroup G} {g : G} (hg3 : g ^ 3 = 1)
    (h : ∀ a ∈ V, g * a * g⁻¹ ∈ V) : g ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨h a, fun ha => ?_⟩
  have h1 := h _ (h _ ha)
  have e : g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ = a := by
    have : g * g * g = 1 := by simpa [pow_succ] using hg3
    calc g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * a * (g * g * g)⁻¹ := by group
      _ = a := by rw [this]; group
  rw [e] at h1
  exact h1

variable {V W I I₂ T₀ : Subgroup G}

omit [Finite G] in
theorem conjClosure_eq_join3 [IsMulCommutative ↥W] (hVW : V ≤ W)
    (hI₂ : I₂ ≤ I) (hT₀V : ∀ t ∈ T₀, ∀ a ∈ V, t * a * t⁻¹ ∈ V) {g : G} (hg : g ∈ I₂) (hg3 : g ^ 3 = 1)
    (hcos : ∀ x ∈ I₂, x ∈ T₀ ∨ g⁻¹ * x ∈ T₀ ∨ g * x ∈ T₀)
    (β : ↥I →* MulAut ↥W) (hβ : ∀ (h : ↥I) (w : ↥W), ((β h w : ↥W) : G) = (h : G) * w * (h : G)⁻¹) :
    conjClosure V I₂ = (join3 (V.subgroupOf W) (β ⟨g, hI₂ hg⟩)).map W.subtype := by
  classical
  have hginv2 : g⁻¹ = g * g := by
    have : g * (g * g) = 1 := by rw [← mul_assoc]; simpa [pow_succ] using hg3
    exact inv_eq_of_mul_eq_one_right this
  apply le_antisymm
  · refine conjClosure_le fun h hh a ha => ?_
    have hVW' : ∀ b ∈ V, b ∈ W := fun b hb => hVW hb
    rcases hcos h hh with hT | hT | hT
    · have hmem : h * a * h⁻¹ ∈ V := hT₀V h hT a ha
      refine Subgroup.mem_map.mpr ⟨⟨h * a * h⁻¹, hVW' _ hmem⟩, mem_join3.mpr ⟨⟨h * a * h⁻¹, hVW' _ hmem⟩, hmem, 1,
        Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩, rfl⟩
    · have hmem : (g⁻¹ * h) * a * (g⁻¹ * h)⁻¹ ∈ V := hT₀V _ hT a ha
      refine Subgroup.mem_map.mpr ⟨(β ⟨g, hI₂ hg⟩) ⟨(g⁻¹ * h) * a * (g⁻¹ * h)⁻¹, hVW' _ hmem⟩,
        mem_join3.mpr ⟨1, Subgroup.one_mem _, ⟨(g⁻¹ * h) * a * (g⁻¹ * h)⁻¹, hVW' _ hmem⟩, hmem, 1,
          Subgroup.one_mem _, by simp⟩, ?_⟩
      show (((β ⟨g, hI₂ hg⟩) ⟨(g⁻¹ * h) * a * (g⁻¹ * h)⁻¹, hVW' _ hmem⟩ : ↥W) : G) = h * a * h⁻¹
      rw [hβ]
      simp only [mul_inv_rev, inv_inv]
      group
    · have hmem : (g * h) * a * (g * h)⁻¹ ∈ V := hT₀V _ hT a ha
      refine Subgroup.mem_map.mpr ⟨((β ⟨g, hI₂ hg⟩) ^ 2) ⟨(g * h) * a * (g * h)⁻¹, hVW' _ hmem⟩,
        mem_join3.mpr ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, ⟨(g * h) * a * (g * h)⁻¹, hVW' _ hmem⟩, hmem,
          by simp⟩, ?_⟩
      show ((((β ⟨g, hI₂ hg⟩) ^ 2) ⟨(g * h) * a * (g * h)⁻¹, hVW' _ hmem⟩ : ↥W) : G) = h * a * h⁻¹
      rw [pow_two, MulAut.mul_apply, hβ, hβ]
      have e : h = g⁻¹ * (g * h) := by group
      have e2 : (g * (g * ((g * h) * a * (g * h)⁻¹) * g⁻¹) * g⁻¹) = (g * g) * ((g * h) * a * (g * h)⁻¹) * (g * g)⁻¹ := by
        group
      show g * (g * ((g * h) * a * (g * h)⁻¹) * g⁻¹) * g⁻¹ = h * a * h⁻¹
      rw [e2, ← hginv2]
      group
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_join3.mp hw
    have ha' : (a : G) ∈ V := ha
    have hb' : (b : G) ∈ V := hb
    have hc' : (c : G) ∈ V := hc
    show ((a * (β ⟨g, hI₂ hg⟩) b * ((β ⟨g, hI₂ hg⟩) ^ 2) c : ↥W) : G) ∈ conjClosure V I₂
    rw [Subgroup.coe_mul, Subgroup.coe_mul, pow_two, MulAut.mul_apply, hβ, hβ, hβ]
    have e : (g * (g * (c : G) * g⁻¹) * g⁻¹) = (g * g) * c * (g * g)⁻¹ := by group
    show (a : G) * (g * (b : G) * g⁻¹) * (g * (g * (c : G) * g⁻¹) * g⁻¹) ∈ conjClosure V I₂
    rw [e]
    exact (conjClosure V I₂).mul_mem
      ((conjClosure V I₂).mul_mem (le_conjClosure V I₂ ha') (mem_conjClosure hg hb'))
      (mem_conjClosure (I₂.mul_mem hg hg) hc')

end CFSG.Quasithin.ModC
