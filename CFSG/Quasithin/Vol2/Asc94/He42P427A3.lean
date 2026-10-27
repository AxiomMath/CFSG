module

public import CFSG.Quasithin.Vol2.Asc94.He42P427A2

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

@[expose] def KB (T : HeSetup G) : Subgroup G :=
  centralizer ({T.a} : Set G) ⊓ normalizer (T.B : Set G)

theorem p427_exists_b (T : HeSetup G) :
    ∃ b ∈ T.B, b ≠ 1 ∧ b ≠ T.a ∧ T.m b = T.g.val := by
  obtain ⟨b, hbB, hbm⟩ := T.hD.exists_b T.hxN T.hxa T.hx3
  have hg1 : T.g ≠ 1 := T.hD.g_ne_one T.hxN T.hxa T.hx3
  have hbm' : T.m b = T.g.val := hbm
  refine ⟨b, hbB, ?_, ?_, hbm'⟩
  · rintro rfl
    apply Units.ne_zero T.g
    rw [← hbm', T.hD.hT.m_one]
  · rintro rfl
    apply hg1
    apply Units.ext
    rw [Units.val_one, ← hbm', T.hD.ham]

theorem p427_comm_all_B (T : HeSetup G) {b : G} (hbB : b ∈ T.B) (hb1 : b ≠ 1) (hba : b ≠ T.a)
    {x : G} (hxa : x * T.a = T.a * x) (hxb : x * b = b * x) : ∀ y ∈ T.B, x * y = y * x := by
  intro y hy
  rcases T.hD.B_elems T.hxN T.hxa T.hx3 hbB hb1 hba y hy with rfl | rfl | rfl | rfl
  · simp
  · exact hxa
  · exact hxb
  · rw [← mul_assoc, hxa, mul_assoc, hxb, ← mul_assoc]

theorem p427_L_le_KB (T : HeSetup G) (hB : T.BaseFacts) : T.L ≤ KB T := by
  intro c hc
  have hcB := p427_L_le_centB T hB hc
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hcB T.a (T.hD.a_mem_B T.hxN T.hxa T.hx3)).symm
  · apply Subgroup.mem_normalizer_fintype
    intro n hn
    have hcn := mem_centralizer_iff.1 hcB n hn
    have e : c * n * c⁻¹ = n := by
      calc c * n * c⁻¹ = n * c * c⁻¹ := by rw [hcn]
        _ = n := by group
    rw [e]
    exact hn

theorem p427_KB_coset (T : HeSetup G) (hB : T.BaseFacts)
    (hL : ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c ∈ T.L)
    {b : G} (hbB : b ∈ T.B) (hb1 : b ≠ 1) (hba : b ≠ T.a)
    {s₀ : G} (hs₀ : s₀ ∈ KB T) (hs₀L : s₀ ∉ T.L) {k : G} (hk : k ∈ KB T) :
    k ∈ T.L ∨ s₀⁻¹ * k ∈ T.L := by
  have hdich : ∀ g ∈ KB T, g * b * g⁻¹ = b ∨ g * b * g⁻¹ = T.a * b := by
    intro g hg
    have hga : g * T.a = T.a * g := mem_centralizer_singleton_iff.1 hg.1
    have hmem : g * b * g⁻¹ ∈ T.B := (Subgroup.mem_normalizer_iff.1 hg.2 b).1 hbB
    rcases T.hD.B_elems T.hxN T.hxa T.hx3 hbB hb1 hba _ hmem with h | h | h | h
    · exfalso
      apply hb1
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hba
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = g⁻¹ * T.a * g := by rw [h]
        _ = T.a := by rw [mul_assoc, ← hga, inv_mul_cancel_left]
    · exact Or.inl h
    · exact Or.inr h
  rcases hdich k hk with hkb | hkab
  · left
    have hkb' : k * b = b * k := by
      calc k * b = (k * b * k⁻¹) * k := by group
        _ = b * k := by rw [hkb]
    exact hL k (p427_comm_all_B T hbB hb1 hba (mem_centralizer_singleton_iff.1 hk.1) hkb')
  · right
    have hs₀a : s₀ * T.a = T.a * s₀ := mem_centralizer_singleton_iff.1 hs₀.1
    have hs₀b : s₀ * b * s₀⁻¹ = T.a * b := by
      rcases hdich s₀ hs₀ with h | h
      · exfalso
        apply hs₀L
        apply hL s₀ (p427_comm_all_B T hbB hb1 hba hs₀a ?_)
        calc s₀ * b = (s₀ * b * s₀⁻¹) * s₀ := by group
          _ = b * s₀ := by rw [h]
      · exact h
    have hconj : s₀⁻¹ * (T.a * b) * s₀ = b := by
      calc s₀⁻¹ * (T.a * b) * s₀ = s₀⁻¹ * (s₀ * b * s₀⁻¹) * s₀ := by rw [hs₀b]
        _ = b := by group
    have heb : (s₀⁻¹ * k) * b * (s₀⁻¹ * k)⁻¹ = b := by
      calc (s₀⁻¹ * k) * b * (s₀⁻¹ * k)⁻¹ = s₀⁻¹ * (k * b * k⁻¹) * s₀ := by group
        _ = s₀⁻¹ * (T.a * b) * s₀ := by rw [hkab]
        _ = b := hconj
    have heb' : (s₀⁻¹ * k) * b = b * (s₀⁻¹ * k) := by
      calc (s₀⁻¹ * k) * b = ((s₀⁻¹ * k) * b * (s₀⁻¹ * k)⁻¹) * (s₀⁻¹ * k) := by group
        _ = b * (s₀⁻¹ * k) := by rw [heb]
    have hs₀inv : s₀⁻¹ * T.a = T.a * s₀⁻¹ := by
      calc s₀⁻¹ * T.a = s₀⁻¹ * (T.a * s₀) * s₀⁻¹ := by group
        _ = s₀⁻¹ * (s₀ * T.a) * s₀⁻¹ := by rw [← hs₀a]
        _ = T.a * s₀⁻¹ := by group
    have hea : (s₀⁻¹ * k) * T.a = T.a * (s₀⁻¹ * k) := by
      rw [mul_assoc, mem_centralizer_singleton_iff.1 hk.1, ← mul_assoc, hs₀inv, mul_assoc]
    exact hL _ (p427_comm_all_B T hbB hb1 hba hea heb')

theorem p427_KB_card_le (T : HeSetup G) (hB : T.BaseFacts)
    (hL : ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c ∈ T.L)
    {b : G} (hbB : b ∈ T.B) (hb1 : b ≠ 1) (hba : b ≠ T.a)
    {s₀ : G} (hs₀ : s₀ ∈ KB T) (hs₀L : s₀ ∉ T.L) :
    Nat.card ↥(KB T) ≤ 2 * Nat.card ↥T.L := by
  have hLK : T.L ≤ KB T := p427_L_le_KB T hB
  let L' : Subgroup ↥(KB T) := T.L.subgroupOf (KB T)
  let f : Fin 2 → ↥(KB T) ⧸ L' := ![QuotientGroup.mk 1, QuotientGroup.mk ⟨s₀, hs₀⟩]
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    by_cases hg : (g : G) ∈ T.L
    · refine ⟨0, ?_⟩
      show (QuotientGroup.mk (1 : ↥(KB T)) : ↥(KB T) ⧸ L') = QuotientGroup.mk g
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hg
    · rcases p427_KB_coset T hB hL hbB hb1 hba hs₀ hs₀L g.2 with h | h
      · exact absurd h hg
      · refine ⟨1, ?_⟩
        show QuotientGroup.mk (⟨s₀, hs₀⟩ : ↥(KB T)) = QuotientGroup.mk g
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using h
  have hcard : Nat.card (↥(KB T) ⧸ L') ≤ 2 := by
    have h := Nat.card_le_card_of_surjective f hsurj
    simpa using h
  have hidx : L'.index = Nat.card (↥(KB T) ⧸ L') := rfl
  have hmul := Subgroup.index_mul_card (H := L')
  have hL'card : Nat.card ↥L' = Nat.card ↥T.L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv
  rw [hL'card, hidx] at hmul
  rw [← hmul]
  exact Nat.mul_le_mul_right _ hcard

theorem p427_S_le_KB (T : HeSetup G) {z : G} (hz : z ∈ T.Z) (ha : T.a ∈ T.Z)
    (hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512)
    (haB : T.a ∈ T.B) (ha1 : T.a ≠ 1) (hB : T.BaseFacts) :
    centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) ≤ KB T := by
  intro s hs
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hs).2,
    p427_S_le_normalizer_B T hB hz ha hS haB ha1 hs⟩

theorem p427_KB_card (T : HeSetup G) (hB : T.BaseFacts)
    (hL : ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c ∈ T.L)
    (hLcard : Nat.card T.L = 80640) {z : G} (hz : z ∈ T.Z) (ha : T.a ∈ T.Z)
    (hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512) :
    Nat.card ↥(KB T) = 161280 := by
  have haB : T.a ∈ T.B := T.hD.a_mem_B T.hxN T.hxa T.hx3
  have ha1 : T.a ≠ 1 := by
    intro h
    have := T.hD.ham
    rw [h, T.hD.hT.m_one] at this
    exact absurd this (by decide)
  have hSK := p427_S_le_KB T hz ha hS haB ha1 hB
  have hLK := p427_L_le_KB T hB
  obtain ⟨b, hbB, hb1, hba, -⟩ := p427_exists_b T
  obtain ⟨s₀, hs₀, hs₀L⟩ : ∃ s₀ ∈ KB T, s₀ ∉ T.L := by
    by_contra hcon
    push_neg at hcon
    have hEq : KB T ≤ T.L := hcon
    have hK : KB T = T.L := le_antisymm hEq hLK
    have h1 := Subgroup.card_dvd_of_le hSK
    rw [hS, hK, hLcard] at h1
    norm_num at h1
  have hle := p427_KB_card_le T hB hL hbB hb1 hba hs₀ hs₀L
  have hd1 : Nat.card ↥T.L ∣ Nat.card ↥(KB T) := Subgroup.card_dvd_of_le hLK
  have hd2 : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) ∣
      Nat.card ↥(KB T) := Subgroup.card_dvd_of_le hSK
  rw [hS] at hd2
  rw [hLcard] at hd1 hle
  have hlcm : 161280 ∣ Nat.card ↥(KB T) := by
    have h := Nat.lcm_dvd hd1 hd2
    norm_num at h
    exact h
  obtain ⟨q, hq⟩ := hlcm
  have hpos : 0 < Nat.card ↥(KB T) := Nat.card_pos
  omega

theorem p427_conj_KB (T : HeSetup G) (hB : T.BaseFacts) {z : G}
    (hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512)
    (hSK : centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) ≤ KB T)
    (hKB : Nat.card ↥(KB T) = 161280) {c : G} (hc : c ∈ KB T) (hc2 : c * c = 1) :
    ∃ k ∈ KB T, k⁻¹ * c * k ∈ centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) := by
  set S := centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) with hSdef
  have hP : IsPGroup 2 (S.subgroupOf (KB T)) := by
    apply IsPGroup.of_card (n := 9)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hS]
    norm_num
  have hodd : Odd (S.subgroupOf (KB T)).index := by
    have h := Subgroup.relIndex_mul_card S (KB T)
    rw [inf_eq_left.2 hSK, hS, hKB] at h
    have h315 : S.relIndex (KB T) = 315 := by omega
    have : (S.subgroupOf (KB T)).index = S.relIndex (KB T) := rfl
    rw [this, h315]
    decide
  have hQ : IsPGroup 2 (Subgroup.zpowers (⟨c, hc⟩ : ↥(KB T))) :=
    p427_isPGroup_zpowers (x := (⟨c, hc⟩ : ↥(KB T))) (Subtype.ext (by simpa using hc2))
  obtain ⟨g, hg⟩ := p427_conj_into hP hQ hodd
  refine ⟨(g : G), g.2, ?_⟩
  have h1 := hg ⟨c, hc⟩ (Subgroup.mem_zpowers _)
  have h2 := Subgroup.mem_subgroupOf.1 h1
  simpa using h2

end CFSG.Quasithin.A94.He42
