module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Lift

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E217R4

variable {G : Type} [Group G] [Finite G]

theorem false_of_quotient {H T M V : Subgroup G} (h : E2.Hyp28 H T M V) (hchar : CharTwo H)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI h.elem H)) (hV16 : Nat.card V = 2 ^ 4)
    {D : Subgroup ↥H} [D.Normal] (hD : D = (pCoreOf 2 H).subgroupOf H)
    {Ā T₀b : Subgroup (↥H ⧸ D)} (hA9 : Nat.card Ā = 9)
    (hT₀bT : T₀b ≤ (T.subgroupOf H).map (QuotientGroup.mk' D))
    (hT₀bA : T₀b ≤ Subgroup.normalizer (Ā : Set (↥H ⧸ D)))
    (hirr : ∀ C : Subgroup (↥H ⧸ D), C ≤ Ā → T₀b ≤ Subgroup.normalizer (C : Set (↥H ⧸ D)) →
      C = ⊥ ∨ C = Ā)
    {v : G} (hv : v ∈ V) (hVT₀b : (V.subgroupOf H).map (QuotientGroup.mk' D) ≤ T₀b)
    (hinv : ∀ a ∈ Ā, QuotientGroup.mk' D ⟨v, h.le_H hv⟩ * a *
      (QuotientGroup.mk' D ⟨v, h.le_H hv⟩)⁻¹ * a = 1) : False := by
  subst hD
  set Q := pCoreOf 2 H with hQ
  set π : ↥H →* ↥H ⧸ Q.subgroupOf H := QuotientGroup.mk' (Q.subgroupOf H) with hπ
  have hQH : Q ≤ H := pCoreOf_le 2 H
  have hQT : Q ≤ T := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    h.minParabolic.isSylow
  have hker : ∀ x : ↥H, π x = 1 ↔ (x : G) ∈ Q := fun x =>
    (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set B : Subgroup G := (Ā.comap π).map H.subtype with hB
  set T₀ : Subgroup G := (T₀b.comap π).map H.subtype with hT₀
  have hmemB : ∀ x : ↥H, (x : G) ∈ B ↔ π x ∈ Ā := fun x => by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hmemT : ∀ x : ↥H, (x : G) ∈ T₀ ↔ π x ∈ T₀b := fun x => by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hBH : B ≤ H := Subgroup.map_subtype_le _
  have hQB : Q ≤ B := fun x hx => by
    have hxH : x ∈ H := hQH hx
    have : π ⟨x, hxH⟩ = 1 := (hker ⟨x, hxH⟩).2 hx
    exact (hmemB ⟨x, hxH⟩).2 (by rw [this]; exact Ā.one_mem)
  have hQT₀ : Q ≤ T₀ := fun x hx => by
    have hxH : x ∈ H := hQH hx
    have : π ⟨x, hxH⟩ = 1 := (hker ⟨x, hxH⟩).2 hx
    exact (hmemT ⟨x, hxH⟩).2 (by rw [this]; exact T₀b.one_mem)
  have hT₀T : T₀ ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hyT, hyx⟩ := hT₀bT (show π x ∈ T₀b from hx)
    have h1 : π (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have h2 : ((y⁻¹ * x : ↥H) : G) ∈ Q := (hker _).1 h1
    have h3 : (x : G) = (y : G) * ((y⁻¹ * x : ↥H) : G) := by simp
    show (x : G) ∈ T
    rw [h3]
    exact T.mul_mem hyT (hQT h2)
  have hB9 : ∀ b ∈ B, b ^ 9 ∈ Q := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : π x ∈ Ā := hx
    have h9 : (π x) ^ 9 = 1 := by
      have := pow_card_eq_one' (x := (⟨π x, hx'⟩ : ↥Ā))
      rw [hA9] at this
      exact congrArg Subtype.val this
    have : π (x ^ 9) = 1 := by rw [map_pow, h9]
    simpa using (hker (x ^ 9)).1 this
  have hT₀B : T₀ ≤ Subgroup.normalizer (B : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    have htA := Subgroup.mem_normalizer_iff.1 (hT₀bA (show π t ∈ T₀b from ht))
    rw [Subgroup.mem_normalizer_iff]
    intro b
    show b ∈ B ↔ (t : G) * b * (t : G)⁻¹ ∈ B
    by_cases hbH : b ∈ H
    · have h1 := htA (π ⟨b, hbH⟩)
      have e : π (t * ⟨b, hbH⟩ * t⁻¹) = π t * π ⟨b, hbH⟩ * (π t)⁻¹ := by
        simp [map_mul, map_inv]
      rw [show (t : G) * b * (t : G)⁻¹ = ((t * ⟨b, hbH⟩ * t⁻¹ : ↥H) : G) by simp]
      rw [hmemB ⟨b, hbH⟩, hmemB (t * ⟨b, hbH⟩ * t⁻¹), e]
      exact h1
    · have h1 : b ∉ B := fun hb => hbH (hBH hb)
      have h2 : (t : G) * b * (t : G)⁻¹ ∉ B := fun hb => by
        have h3 := hBH hb
        apply hbH
        have h4 : (t : G)⁻¹ * ((t : G) * b * (t : G)⁻¹) * (t : G) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem t.2) h3) t.2
        simpa [mul_assoc] using h4
      exact ⟨fun hb => absurd hb h1, fun hb => absurd hb h2⟩
  have hirr' : ∀ C : Subgroup G, Q ≤ C → C ≤ B → T₀ ≤ Subgroup.normalizer (C : Set G) →
      C = Q ∨ C = B := by
    intro C hQC hCB hT₀C
    set C' : Subgroup (↥H ⧸ Q.subgroupOf H) := (C.subgroupOf H).map π with hC'
    have hmemC : ∀ x : ↥H, π x ∈ C' ↔ (x : G) ∈ C := by
      intro x
      constructor
      · rintro ⟨c, hc, hcx⟩
        have h1 : π (c⁻¹ * x) = 1 := by rw [map_mul, map_inv, hcx, inv_mul_cancel]
        have h2 : ((c⁻¹ * x : ↥H) : G) ∈ Q := (hker _).1 h1
        have h3 : (x : G) = (c : G) * ((c⁻¹ * x : ↥H) : G) := by simp
        rw [h3]
        exact C.mul_mem hc (hQC h2)
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hC'A : C' ≤ Ā := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hmemB x).1 (hCB hx)
    have hC'N : T₀b ≤ Subgroup.normalizer (C' : Set (↥H ⧸ Q.subgroupOf H)) := by
      intro tb htb
      obtain ⟨t, rfl⟩ := hsurj tb
      have hN := Subgroup.mem_normalizer_iff.1 (hT₀C ((hmemT t).2 htb))
      rw [Subgroup.mem_normalizer_iff]
      intro cb
      obtain ⟨c, rfl⟩ := hsurj cb
      have e : π t * π c * (π t)⁻¹ = π (t * c * t⁻¹) := by simp
      rw [e, hmemC, hmemC]
      have := hN (c : G)
      simpa using this
    rcases hirr C' hC'A hC'N with h0 | h0
    · left
      refine le_antisymm (fun x hx => ?_) hQC
      have hxH : x ∈ H := hBH (hCB hx)
      have : π ⟨x, hxH⟩ ∈ C' := (hmemC ⟨x, hxH⟩).2 hx
      rw [h0, Subgroup.mem_bot] at this
      exact (hker _).1 this
    · right
      refine le_antisymm hCB (fun x hx => ?_)
      have hxH : x ∈ H := hBH hx
      have : π ⟨x, hxH⟩ ∈ C' := by
        rw [h0]
        exact (hmemB ⟨x, hxH⟩).1 hx
      exact (hmemC ⟨x, hxH⟩).1 this
  have hidx : Q.relIndex B = 9 := by
    have hBsub : B.subgroupOf H = Ā.comap π := by
      ext x
      exact hmemB x
    rw [← Subgroup.relIndex_subgroupOf hBH, hBsub]
    have hcard : Nat.card ((Ā.comap π).map π) = (Q.subgroupOf H).relIndex (Ā.comap π) := by
      have hk : (π.domRestrict (Ā.comap π)).ker = (Q.subgroupOf H).subgroupOf (Ā.comap π) := by
        rw [MonoidHom.ker_domRestrict, hπ, QuotientGroup.ker_mk']
      have h1 := Subgroup.index_ker (π.domRestrict (Ā.comap π))
      rw [hk, MonoidHom.domRestrict_range] at h1
      exact h1.symm
    rw [← hcard, Subgroup.map_comap_eq_self_of_surjective hsurj]
    exact hA9
  have hVT₀ : V ≤ T₀ := fun x hx => by
    have hxH : x ∈ H := h.le_H hx
    exact (hmemT ⟨x, hxH⟩).2 (hVT₀b ⟨⟨x, hxH⟩, hx, rfl⟩)
  have hinv' : ∀ b ∈ B, v * b * v⁻¹ * b ∈ Q := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hinv (π y) hy
    have h2 : π (⟨v, h.le_H hv⟩ * y * ⟨v, h.le_H hv⟩⁻¹ * y) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv]
      exact h1
    simpa using (hker _).1 h2
  exact false_of_lifted h hchar hq hV16 hQB hBH hidx hB9 hQT₀ hT₀T hT₀B hirr' hVT₀ hv hinv'

end E217R4

end CFSG.Quasithin
