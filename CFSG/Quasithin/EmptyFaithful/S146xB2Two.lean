module

public import CFSG.Quasithin.EmptyFaithful.S146xB2Dih

public section

namespace CFSG.Quasithin

open CFSG.Open

section Conj

variable {X : Type} [Group X]

theorem mem_map_conj_toMonoidHom_iff {K : Subgroup X} {t y : X} :
    y ∈ K.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * y * t ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem mem_centralizer_map_conj_toMonoidHom_iff {K₁ K₂ : Subgroup X} {t : X}
    (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom) {y : X} :
    y ∈ Subgroup.centralizer (K₂ : Set X) ↔ t⁻¹ * y * t ∈ Subgroup.centralizer (K₁ : Set X) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have hk2 : t * k * t⁻¹ ∈ K₂ := by
      rw [hK₂, mem_map_conj_toMonoidHom_iff]
      simpa [mul_assoc] using hk
    have := Subgroup.mem_centralizer_iff.mp h _ hk2
    calc k * (t⁻¹ * y * t) = t⁻¹ * ((t * k * t⁻¹) * y) * t := by group
      _ = t⁻¹ * (y * (t * k * t⁻¹)) * t := by rw [this]
      _ = t⁻¹ * y * t * k := by group
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have hk1 : t⁻¹ * k * t ∈ K₁ := by
      have hk' : k ∈ K₂ := hk
      rw [hK₂, mem_map_conj_toMonoidHom_iff] at hk'
      exact hk'
    have := Subgroup.mem_centralizer_iff.mp h _ hk1
    calc k * y = t * ((t⁻¹ * k * t) * (t⁻¹ * y * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * y * t) * (t⁻¹ * k * t)) * t⁻¹ := by rw [this]
      _ = y * k := by group

end Conj

theorem card_le_eight_of_two_psl2_factors {X : Type} [Group X] [Finite X] {K₁ K₂ T B : Subgroup X} {t : X}
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (e₁ : K₁ ≃* CFSG.GorensteinWalter.PSL2 F) (e₂ : K₂ ≃* CFSG.GorensteinWalter.PSL2 F)
    (hT : IsPGroup 2 T) (ht : t ∈ T) (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom)
    (hT₀N : T ⊓ Subgroup.normalizer (K₁ : Set X) ≤ Subgroup.normalizer (K₂ : Set X))
    (hidx : (T ⊓ Subgroup.normalizer (K₁ : Set X)).relIndex T ≤ 2)
    (hC : ∀ x ∈ T, x ∈ Subgroup.centralizer (K₁ : Set X) →
      x ∈ Subgroup.centralizer (K₂ : Set X) → x = 1)
    (h16 : 16 ≤ ((T ⊓ Subgroup.normalizer (K₁ : Set X)) ⊓
      Subgroup.centralizer (K₁ : Set X)).relIndex (T ⊓ Subgroup.normalizer (K₁ : Set X)))
    (hBT : B ≤ T) (hBn : ∀ s ∈ T, ∀ b ∈ B, s * b * s⁻¹ ∈ B) (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    Nat.card B ≤ 8 := by
  classical
  set T₀ : Subgroup X := T ⊓ Subgroup.normalizer (K₁ : Set X) with hT₀def
  have hT₀T : T₀ ≤ T := inf_le_left
  have hT₀2 : IsPGroup 2 T₀ := hT.to_le hT₀T
  have hT₀J₁ : T₀ ≤ Subgroup.normalizer (K₁ : Set X) := inf_le_right
  have hnorm : ∀ s ∈ T, ∀ x ∈ T₀, s * x * s⁻¹ ∈ T₀ := by
    have hne : (T₀.subgroupOf T).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : (T₀.subgroupOf T).index ≤ 2 := hidx
    have hcases : (T₀.subgroupOf T).index = 1 ∨ (T₀.subgroupOf T).index = 2 := by omega
    rcases hcases with h1 | h2
    · have htop : T₀.subgroupOf T = ⊤ := Subgroup.index_eq_one.mp h1
      intro s hs x hx
      have hxT : x ∈ T := hT₀T hx
      have : s * x * s⁻¹ ∈ T := T.mul_mem (T.mul_mem hs hxT) (T.inv_mem hs)
      have h3 : (⟨s * x * s⁻¹, this⟩ : ↥T) ∈ T₀.subgroupOf T := by
        rw [htop]; exact Subgroup.mem_top _
      exact h3
    · have hn : (T₀.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
      intro s hs x hx
      exact hn.conj_mem ⟨x, hT₀T hx⟩ (by exact hx) ⟨s, hs⟩
  have hT₀J₂ : T₀ ≤ Subgroup.normalizer (K₂ : Set X) := hT₀N
  have hmap_T₀ : T₀.map (MulAut.conj t).toMonoidHom = T₀ := by
    ext y
    rw [mem_map_conj_toMonoidHom_iff]
    constructor
    · intro hy
      have := hnorm t ht _ hy
      simpa [mul_assoc] using this
    · intro hy
      have := hnorm t⁻¹ (T.inv_mem ht) _ hy
      simpa [mul_assoc] using this
  have h16₂ : 16 ≤ (T₀ ⊓ Subgroup.centralizer (K₂ : Set X)).relIndex T₀ := by
    have hyT₀ : ∀ y, t⁻¹ * y * t ∈ T₀ ↔ y ∈ T₀ := by
      intro y
      constructor
      · intro hy
        have := hnorm t ht _ hy
        simpa [mul_assoc] using this
      · intro hy
        have := hnorm t⁻¹ (T.inv_mem ht) _ hy
        simpa [mul_assoc] using this
    have hmap : (T₀ ⊓ Subgroup.centralizer (K₁ : Set X)).map (MulAut.conj t).toMonoidHom =
        T₀ ⊓ Subgroup.centralizer (K₂ : Set X) := by
      ext y
      rw [mem_map_conj_toMonoidHom_iff]
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨(hyT₀ y).mp hy1, (mem_centralizer_map_conj_toMonoidHom_iff hK₂).mpr hy2⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨(hyT₀ y).mpr hy1, (mem_centralizer_map_conj_toMonoidHom_iff hK₂).mp hy2⟩
    have h := Subgroup.relIndex_map_map_of_injective (T₀ ⊓ Subgroup.centralizer (K₁ : Set X)) T₀
      (MulAut.conj t).injective (f := (MulAut.conj t).toMonoidHom)
    rw [hmap, hmap_T₀] at h
    rw [h]
    exact h16
  set W₀ : Subgroup X := B ⊓ T₀ with hW₀def
  have hW₀T₀ : W₀ ≤ T₀ := inf_le_right
  have hW₀n : ∀ s ∈ T₀, ∀ w ∈ W₀, s * w * s⁻¹ ∈ W₀ := fun s hs w hw =>
    ⟨hBn s (hT₀T hs) w hw.1, T₀.mul_mem (T₀.mul_mem hs hw.2) (T₀.inv_mem hs)⟩
  have hstep1 : (W₀ ⊓ Subgroup.centralizer (K₁ : Set X)).relIndex W₀ ≤ 2 :=
    relIndex_inf_centralizer_le_two hp7 hF e₁ hT₀2 hT₀J₁ hW₀T₀ hW₀n (fun w hw => hB2 w hw.1) h16
  set W₂ : Subgroup X := W₀ ⊓ Subgroup.centralizer (K₁ : Set X) with hW₂def
  have hW₂W₀ : W₂ ≤ W₀ := inf_le_left
  have hW₂T₀ : W₂ ≤ T₀ := hW₂W₀.trans hW₀T₀
  have hW₂n : ∀ s ∈ T₀, ∀ w ∈ W₂, s * w * s⁻¹ ∈ W₂ := by
    intro s hs w hw
    refine ⟨hW₀n s hs w hw.1, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hk' : s⁻¹ * k * s ∈ K₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hT₀J₁ (T₀.inv_mem hs)) k).mp hk
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hw.2 _ hk'
    calc k * (s * w * s⁻¹) = s * ((s⁻¹ * k * s) * w) * s⁻¹ := by group
      _ = s * (w * (s⁻¹ * k * s)) * s⁻¹ := by rw [this]
      _ = s * w * s⁻¹ * k := by group
  have hstep2 : (W₂ ⊓ Subgroup.centralizer (K₂ : Set X)).relIndex W₂ ≤ 2 :=
    relIndex_inf_centralizer_le_two hp7 hF e₂ hT₀2 hT₀J₂ hW₂T₀ hW₂n
      (fun w hw => hB2 w hw.1.1) h16₂
  have hW₃ : W₂ ⊓ Subgroup.centralizer (K₂ : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hC x (hT₀T (hW₂T₀ hx.1)) hx.1.2 hx.2
  have hc2 : Nat.card W₂ ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (W₂ ⊓ Subgroup.centralizer (K₂ : Set X)) W₂
    rw [hW₃] at h hstep2
    have h1 : Nat.card ↥((⊥ : Subgroup X) ⊓ W₂) = 1 := by simp
    rw [h1, mul_one] at h
    omega
  have hc0 : Nat.card W₀ ≤ 4 := by
    have h := Subgroup.relIndex_mul_card W₂ W₀
    rw [inf_eq_left.mpr hW₂W₀] at h
    nlinarith
  have hB : (B ⊓ T₀).relIndex B ≤ 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right hBT
      (by unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite)).trans hidx
  have h := Subgroup.relIndex_mul_card W₀ B
  rw [inf_eq_left.mpr (inf_le_left : W₀ ≤ B)] at h
  nlinarith

end CFSG.Quasithin
