module

public import CFSG.Quasithin.Vol2.Asc94.TS40e

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

structure Frame5 (G : Type) [Group G] (z : G) extends Frame4 G z where
  z_mem_closure_Δ3 : z ∈ Subgroup.closure (Δ 3)
  card_A_Q : Nat.card ↥(A ⊓ Q) = 16

@[expose] def Frame2.Ω (F : Frame2 G z) : Set G := ((F.A : Set G) \ {1}) \ F.Sz

theorem Frame3.Δ2_sub_Sz (F : Frame3 G z) (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) :
    F.Δ 2 ⊆ F.Sz := by
  intro a ha
  obtain ⟨haU, ha1, haz⟩ := F.Δ2_sub a ha
  have hA : a ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨2, ha⟩
  rw [F.Δ_union] at hA
  exact ⟨hA.1, ha1, hU2 a haU ha1⟩

theorem Frame3.exists_x (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) (h45 : F.Sz.ncard = 45)
    (hex : F.Δ 4 ⊆ F.Sz ∨ F.Δ 5 ⊆ F.Sz) :
    ∃ x : Fin 7, (x = 4 ∨ x = 5) ∧ ¬ F.Δ x ⊆ F.Sz ∧
      ∀ i : Fin 7, i ≠ 3 → i ≠ x → F.Δ i ⊆ F.Sz := by
  classical
  have hsum := F.sum_Sz' hU1 hU2
  have h0 := F.Δ0_sub_Sz
  have h1 := F.Δ1_sub_Sz hU1
  have h2 := F.Δ2_sub_Sz hU2
  have hfin7 : ∀ i : Fin 7, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by decide
  by_cases h4 : F.Δ 4 ⊆ F.Sz <;> by_cases h5 : F.Δ 5 ⊆ F.Sz <;>
    by_cases h6 : F.Δ 6 ⊆ F.Sz <;> simp [h4, h5, h6] at hsum
  all_goals first
    | (exfalso; omega)
    | (exfalso; rcases hex with h | h <;> contradiction)
    | skip
  · refine ⟨5, Or.inr rfl, h5, fun i hi3 hi5 => ?_⟩
    rcases hfin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact absurd rfl hi3
    · exact h4
    · exact absurd rfl hi5
    · exact h6
  · refine ⟨4, Or.inl rfl, h4, fun i hi3 hi4 => ?_⟩
    rcases hfin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact absurd rfl hi3
    · exact absurd rfl hi4
    · exact h5
    · exact h6


theorem Frame2.card_Ω (F : Frame2 G z) (h45 : F.Sz.ncard = 45) : F.Ω.ncard = 18 := by
  have hSz : F.Sz ⊆ (F.A : Set G) \ {1} := fun a ha => ⟨ha.1, ha.2.1⟩
  have h1 : ((F.A : Set G) \ {1}).ncard = 63 := by
    rw [Set.ncard_diff_singleton_of_mem F.A.one_mem, ← Nat.card_coe_set_eq]
    show Nat.card F.A - 1 = 63
    rw [F.card_A]
  show (((F.A : Set G) \ {1}) \ F.Sz).ncard = 18
  rw [Set.ncard_diff hSz, h1, h45]

theorem s40_2_T (F : Frame5 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) (h45 : F.Sz.ncard = 45) :
    F.Ω.ncard = 18 ∧
      (∀ a ∈ F.Ω, ∀ b ∈ F.Ω, ∃ n ∈ Subgroup.normalizer (F.A : Set G), b = n⁻¹ * a * n) ∧
      (∀ a ∈ F.Ω, ∃ t ∈ F.TQ, ∃ g : G, a = g⁻¹ * t * g) ∧
      (∀ a ∈ F.A, a ≠ 1 → (∃ t ∈ F.TQ, ∃ g : G, a = g⁻¹ * t * g) → a ∈ F.Ω) := by
  classical
  have hΩc := F.toFrame2.card_Ω h45
  obtain ⟨j, hj4, hjS, hj12⟩ := F.exists_Δ12 hU1 hU2
  have hex : F.Δ 4 ⊆ F.Sz ∨ F.Δ 5 ⊆ F.Sz := by
    have hfin : ∀ j : Fin 7, 4 ≤ j.val → (F.Δ j).ncard = 12 → j = 4 ∨ j = 5 := by
      intro j hj hc
      rw [F.Δ_card j] at hc
      revert hj hc
      fin_cases j <;> simp
    rcases hfin j hj4 hj12 with rfl | rfl
    · exact Or.inl hjS
    · exact Or.inr hjS
  obtain ⟨x, hx45, hxS, hrest⟩ := F.toFrame3.exists_x hU1 hU2 h45 hex
  have hx3 : x ≠ 3 := by
    rcases hx45 with rfl | rfl <;> decide
  have hdich := F.toFrame3.dich
  have hΩ : F.Ω = F.Δ 3 ∪ F.Δ x := by
    ext a
    constructor
    · rintro ⟨⟨haA, ha1⟩, haS⟩
      have haU : a ∈ ⋃ i, F.Δ i := by
        rw [F.Δ_union]
        exact ⟨haA, ha1⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 haU
      by_cases hi3 : i = 3
      · subst hi3
        exact Or.inl hi
      · by_cases hix : i = x
        · subst hix
          exact Or.inr hi
        · exact absurd (hrest i hi3 hix hi) haS
    · intro ha
      rcases ha with ha | ha
      · have haU : a ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨3, ha⟩
        rw [F.Δ_union] at haU
        refine ⟨haU, fun haS => ?_⟩
        exact Set.disjoint_left.1 ((hdich 3).resolve_left F.toFrame3.not_Δ3_sub_Sz) ha haS
      · have haU : a ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨x, ha⟩
        rw [F.Δ_union] at haU
        refine ⟨haU, fun haS => ?_⟩
        exact Set.disjoint_left.1 ((hdich x).resolve_left hxS) ha haS
  obtain ⟨a₀, ha₀⟩ := F.Δ_nonempty 3
  have ha₀T : a₀ ∈ F.TQ := F.Δ3_sub a₀ ha₀
  have ha₀A : a₀ ∈ F.A := by
    have : a₀ ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨3, ha₀⟩
    rw [F.Δ_union] at this
    exact this.1
  have ha₀1 : a₀ ≠ 1 := by
    have : a₀ ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨3, ha₀⟩
    rw [F.Δ_union] at this
    exact this.2
  set L : Subgroup G := Subgroup.normalizer (F.A : Set G) with hL
  have hNL : F.NA ≤ L := inf_le_right
  have hO₀Ω : ∀ l ∈ L, l⁻¹ * a₀ * l ∈ F.Ω := by
    intro l hl
    refine ⟨⟨F.conj_mem_A ha₀A hl, fun h => ha₀1 ?_⟩, fun hS => ?_⟩
    · have : a₀ = l * (l⁻¹ * a₀ * l) * l⁻¹ := by group
      rw [this, h]
      group
    · obtain ⟨-, -, g, hg⟩ := hS
      refine s39_4 F.toFrame1 a₀ ha₀T (g * l⁻¹) ?_
      calc (g * l⁻¹)⁻¹ * z * (g * l⁻¹) = l * (g⁻¹ * z * g) * l⁻¹ := by group
        _ = l * (l⁻¹ * a₀ * l) * l⁻¹ := by rw [hg]
        _ = a₀ := by group
  have hΔ3O : ∀ a ∈ F.Δ 3, ∃ l ∈ L, a = l⁻¹ * a₀ * l := by
    intro a ha
    obtain ⟨n, hn, hna⟩ := F.Δ_trans 3 a₀ ha₀ a ha
    exact ⟨n, hNL hn, hna⟩
  have hOinv : ∀ l ∈ L, ∀ n ∈ F.NA, n⁻¹ * (l⁻¹ * a₀ * l) * n = (l * n)⁻¹ * a₀ * (l * n) := by
    intro l hl n hn
    group
  have hΩall : ∀ a ∈ F.Ω, ∃ l ∈ L, a = l⁻¹ * a₀ * l := by
    by_cases hcase : ∃ b ∈ F.Δ x, ∃ l ∈ L, b = l⁻¹ * a₀ * l
    · obtain ⟨b, hb, l, hl, hbl⟩ := hcase
      intro a ha
      rw [hΩ] at ha
      rcases ha with ha | ha
      · exact hΔ3O a ha
      · obtain ⟨n, hn, hna⟩ := F.Δ_trans x b hb a ha
        refine ⟨l * n, L.mul_mem hl (hNL hn), ?_⟩
        rw [hna, hbl]
        group
    · exfalso
      push Not at hcase
      have hinv : ∀ l ∈ L, ∀ a ∈ F.Δ 3, l⁻¹ * a * l ∈ F.Δ 3 := by
        intro l hl a ha
        obtain ⟨n, hn, hna⟩ := hΔ3O a ha
        have hmem : l⁻¹ * a * l ∈ F.Ω := by
          have := hO₀Ω (n * l) (L.mul_mem hn hl)
          rw [hna]
          convert this using 1
          group
        rw [hΩ] at hmem
        rcases hmem with h | h
        · exact h
        · exfalso
          exact hcase _ h (n * l) (L.mul_mem hn hl) (by rw [hna]; group)
      set C : Subgroup G := Subgroup.closure (F.Δ 3) with hC
      have hCinv : ∀ l ∈ L, ∀ c ∈ C, l⁻¹ * c * l ∈ C := by
        intro l hl c hc
        have hmap : C.map (MulAut.conj l⁻¹).toMonoidHom ≤ C := by
          rw [hC, MonoidHom.map_closure]
          apply Subgroup.closure_mono
          rintro _ ⟨a, ha, rfl⟩
          have := hinv l hl a ha
          simpa [MulAut.conj_apply] using this
        have := hmap ⟨c, hc, rfl⟩
        simpa [MulAut.conj_apply] using this
      have hCAQ : C ≤ F.A ⊓ F.Q := by
        refine (Subgroup.closure_le _).2 fun a ha => ⟨?_, F.Δ_Q 3 (by decide) a ha⟩
        have : a ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨3, ha⟩
        rw [F.Δ_union] at this
        exact this.1
      have hSzC : F.Sz ⊆ (C : Set G) := by
        rintro a ⟨haA, ha1, g, hg⟩
        obtain ⟨n, hn, hna⟩ := s39_6_3 F.toFrame2 F.z_mem_A haA hg.symm
        rw [← hna]
        exact hCinv n hn z F.z_mem_closure_Δ3
      have h1 := Set.ncard_le_ncard hSzC
      rw [h45, ← Nat.card_coe_set_eq] at h1
      have h1' : 45 ≤ Nat.card ↥C := h1
      have h2 := Subgroup.card_le_of_le hCAQ
      rw [F.card_A_Q] at h2
      omega
  refine ⟨hΩc, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨l₁, hl₁, rfl⟩ := hΩall a ha
    obtain ⟨l₂, hl₂, rfl⟩ := hΩall b hb
    refine ⟨l₁⁻¹ * l₂, L.mul_mem (L.inv_mem hl₁) hl₂, ?_⟩
    group
  · intro a ha
    obtain ⟨l, hl, rfl⟩ := hΩall a ha
    exact ⟨a₀, ha₀T, l, rfl⟩
  · intro a haA ha1 ⟨t, ht, g, hg⟩
    refine ⟨⟨haA, ha1⟩, fun hS => ?_⟩
    obtain ⟨-, -, g', hg'⟩ := hS
    refine s39_4 F.toFrame1 t ht (g' * g⁻¹) ?_
    calc (g' * g⁻¹)⁻¹ * z * (g' * g⁻¹) = g * (g'⁻¹ * z * g') * g⁻¹ := by group
      _ = g * a * g⁻¹ := by rw [← hg']
      _ = t := by rw [hg]; group

end CFSG.Quasithin.A94
