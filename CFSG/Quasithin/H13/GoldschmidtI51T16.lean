module

public import CFSG.Quasithin.H13.GoldschmidtI51ConjD
public import CFSG.Quasithin.H13.GoldschmidtI51GQLoc
public import CFSG.Quasithin.H13.GoldschmidtI51Geom2

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

theorem Q01_not_normal (hD : IsDSystem D Gs) :
    ¬ ∀ a ∈ Gs 0, ∀ n ∈ QQ Gs 0 ⊓ QQ Gs 1, a * n * a⁻¹ ∈ QQ Gs 0 ⊓ QQ Gs 1 := by
  intro hG0
  have hNQ2 : QQ Gs 0 ⊓ QQ Gs 1 ≤ QQ Gs 2 := fun n hn =>
    loc2_core hD n (TT_le 2 (QQ_le_TT hD 0 hn.1)) (core_of_conj_mem_Q1 hD (fun a ha => by
      have := (hG0 a⁻¹ ((Gs 0).inv_mem ha.1) n hn).2
      simpa using this))
  have hQ0Q2 : QQ Gs 0 ≤ QQ Gs 2 := loc2_noNormal_20 hD (Q0_le_P02 hD)
    (fun a ha m hm => normalizes_pCoreOf (Gs 0) ha.1 hm) (fun m₁ h₁ m₂ h₂ => by
      rcases Q0_cases hD m₁ h₁ m₂ h₂ with h | h | h
      · exact Or.inl (hNQ2 ⟨h₁, h⟩)
      · exact Or.inr (Or.inl (hNQ2 ⟨h₂, h⟩))
      · exact Or.inr (Or.inr (hNQ2 ⟨(QQ Gs 0).mul_mem h₁ ((QQ Gs 0).inv_mem h₂), h⟩)))
  exact not_Q0_le_Q1 hD (fun n hn => loc1_core hD n (TT_le 1 (QQ_le_TT hD 0 hn))
    (Q2_core10 hD n (hQ0Q2 hn)) (Q0_core12 hD n hn))

theorem Q01_conj_ne (hD : IsDSystem D Gs) {g : G} (hg : g ∈ Gs 0) (hg1 : g ∉ Gs 1) :
    ∃ n ∈ QQ Gs 0 ⊓ QQ Gs 1, g * n * g⁻¹ ∉ QQ Gs 0 ⊓ QQ Gs 1 := by
  by_contra hcon
  push Not at hcon
  set K : Subgroup G := QQ Gs 0 ⊓ QQ Gs 1 with hK
  have hle : K ≤ cj g⁻¹ K := fun n hn => by
    rw [mem_cj]; simpa using hcon n hn
  have heq : cj g⁻¹ K = K :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])).symm
  have hback : ∀ n, g * n * g⁻¹ ∈ K → n ∈ K := fun n hn => by
    have : n ∈ cj g⁻¹ K := by rw [mem_cj]; simpa using hn
    rwa [heq] at this
  have hP : ∀ a ∈ Gs 0 ⊓ Gs 1, ∀ n ∈ K, a * n * a⁻¹ ∈ K :=
    fun a ha n hn => ⟨normalizes_pCoreOf (Gs 0) ha.1 hn.1, normalizes_pCoreOf (Gs 1) ha.2 hn.2⟩
  obtain ⟨-, -, hmax0⟩ :
      Gs 0 ⊓ Gs 1 ⊓ Gs 2 ≤ Gs 0 ⊓ Gs 1 ∧ A6.IsMaxSubgroupIn (Gs 0 ⊓ Gs 1) (Gs 0) :=
    ((hD.d3max 0 1 2 (by decide) (by decide) (by decide)).2 (Gs 0 ⊓ Gs 1)).2 (Or.inl rfl)
  have hnorm : ∀ a ∈ Gs 0, ∀ n ∈ K, a * n * a⁻¹ ∈ K := by
    have hP' : Gs 0 ⊓ Gs 1 ≤ Subgroup.normalizer (K : Set G) ⊓ Gs 0 :=
      le_inf (le_normalizer_of_conj hP) inf_le_left
    rcases hmax0 _ hP' inf_le_right with hW | hW
    · exfalso
      have hgW : g ∈ Subgroup.normalizer (K : Set G) ⊓ Gs 0 :=
        ⟨Subgroup.mem_normalizer_iff.2 (fun n => ⟨fun hn => hcon n hn, hback n⟩), hg⟩
      rw [hW] at hgW
      exact hg1 hgW.2
    · intro a ha n hn
      have : a ∈ Subgroup.normalizer (K : Set G) ⊓ Gs 0 := by rw [hW]; exact ha
      exact (Subgroup.mem_normalizer_iff.1 this.1 n).1 hn
  exact Q01_not_normal hD hnorm

theorem forall_of_three {X : Type*} [Finite X] (hX : Nat.card X = 3) {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (w : X) : w = a ∨ w = b ∨ w = c := by
  classical
  have := Fintype.ofFinite X
  by_contra hw
  push Not at hw
  obtain ⟨hw1, hw2, hw3⟩ := hw
  have h4 : ({a, b, c, w} : Finset X).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, Ne.symm hw1]),
      Finset.card_insert_of_notMem (by simp [hbc, Ne.symm hw2]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hw3]), Finset.card_singleton]
  have h5 := Finset.card_le_univ ({a, b, c, w} : Finset X)
  rw [Nat.card_eq_fintype_card] at hX
  omega

theorem line_pts (hD : IsDSystem D Gs) {s q t : G} (hs : s ∈ Gs 1) (hs0 : s ∉ Gs 0)
    (hq : q ∈ QQ Gs 0) (hq1 : q ∉ QQ Gs 1) (ht : t ∈ Gs 1) :
    t ∈ Gs 0 ∨ s⁻¹ * t ∈ Gs 0 ∨ (q * s)⁻¹ * t ∈ Gs 0 := by
  have hq0 : q ∈ Gs 0 := TT_le 0 (QQ_le_TT hD 0 hq)
  have hqG1 : q ∈ Gs 1 := TT_le 1 (QQ_le_TT hD 0 hq)
  have hcard : Nat.card (↥(Gs 1) ⧸ (Gs 0 ⊓ Gs 1).subgroupOf (Gs 1)) = 3 := by
    rw [← Subgroup.index_eq_card]; exact loc1_index_10 hD
  have hqs : q * s ∈ Gs 1 := (Gs 1).mul_mem hqG1 hs
  have key := forall_of_three hcard
    (a := (((1 : ↥(Gs 1))) : ↥(Gs 1) ⧸ (Gs 0 ⊓ Gs 1).subgroupOf (Gs 1)))
    (b := ((⟨s, hs⟩ : ↥(Gs 1)) : ↥(Gs 1) ⧸ (Gs 0 ⊓ Gs 1).subgroupOf (Gs 1)))
    (c := ((⟨q * s, hqs⟩ : ↥(Gs 1)) : ↥(Gs 1) ⧸ (Gs 0 ⊓ Gs 1).subgroupOf (Gs 1)))
    (by
      intro h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      exact hs0 (by simpa using h.1))
    (by
      intro h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      have : q * s ∈ Gs 0 := by simpa using h.1
      exact hs0 (by simpa using (Gs 0).mul_mem ((Gs 0).inv_mem hq0) this))
    (by
      intro h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      have h' : s⁻¹ * (q * s) ∈ Gs 0 := by simpa using h.1
      exact hq1 ((fix_iff hD hs hs0 hq).1 (by simpa [mul_assoc] using h')))
    ((⟨t, ht⟩ : ↥(Gs 1)) : ↥(Gs 1) ⧸ (Gs 0 ⊓ Gs 1).subgroupOf (Gs 1))
  rcases key with h | h | h
  · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    exact Or.inl (by simpa using h.1)
  · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    have h1 : t⁻¹ * s ∈ Gs 0 := by simpa using h.1
    have := (Gs 0).inv_mem h1
    rw [mul_inv_rev, inv_inv] at this
    exact Or.inr (Or.inl this)
  · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    have h1 : t⁻¹ * (q * s) ∈ Gs 0 := by simpa using h.1
    have := (Gs 0).inv_mem h1
    rw [mul_inv_rev, inv_inv] at this
    exact Or.inr (Or.inr this)

theorem P_dec (hD : IsDSystem D Gs) {s0 q0 p : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hq0 : q0 ∈ QQ Gs 0) (hq01 : q0 ∉ QQ Gs 1) (hp : p ∈ Gs 0 ⊓ Gs 1) :
    ∃ h1 ∈ Gs 0 ⊓ Gs 1, ∃ r ∈ QQ Gs 0, s0⁻¹ * h1 * s0 ∈ Gs 0 ∧ p = h1 * r := by
  rcases line_pts hD hs0 hs00 hq0 hq01 ((Gs 1).mul_mem hp.2 hs0) with h | h | h
  · exact absurd (by simpa using (Gs 0).mul_mem ((Gs 0).inv_mem hp.1) h) hs00
  · exact ⟨p, hp, 1, (QQ Gs 0).one_mem, by simpa [mul_assoc] using h, by group⟩
  · have hq0P : q0 ∈ Gs 0 ⊓ Gs 1 := Q0_le_P01 hD hq0
    refine ⟨q0⁻¹ * p, (Gs 0 ⊓ Gs 1).mul_mem ((Gs 0 ⊓ Gs 1).inv_mem hq0P) hp,
      p⁻¹ * q0 * p, ?_, by simpa [mul_assoc] using h, by group⟩
    simpa using normalizes_pCoreOf (Gs 0) ((Gs 0).inv_mem hp.1) hq0

omit [Finite G] in
theorem not_mem_G1_of_far {f : G} (hf : f ∈ Gs 0) (hnf : ¬ Nr Gs f) :
    f ∉ Gs 1 := fun h =>
  hnf ⟨f, ⟨hf, h⟩, 1, (Gs 0 ⊓ Gs 2).one_mem, 1, (Gs 0 ⊓ Gs 1).one_mem, by group⟩

theorem T16 (hD : IsDSystem .C3 Gs) {s0 f t f' t' : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hf : f ∈ Gs 0) (hnf : ¬ Nr Gs f) (ht : t ∈ Gs 1) (ht0 : t ∉ Gs 0)
    (hf' : f' ∈ Gs 0) (hnf' : ¬ Nr Gs f') (ht' : t' ∈ Gs 1) (ht'0 : t' ∉ Gs 0) :
    ∃ g ∈ Gs 0, s0⁻¹ * g * s0 ∈ Gs 0 ∧ (f' * t')⁻¹ * (g * f * t) ∈ Gs 0 := by
  obtain ⟨q0, hq0, hq01⟩ : ∃ q ∈ QQ Gs 0, q ∉ QQ Gs 1 := by
    by_contra h; push Not at h; exact not_Q0_le_Q1 hD h
  have hGQ := gqLoc hD
  obtain ⟨p, hp, p', hp', hfp⟩ := hGQ.farT f hf hnf f' hf' hnf'
  obtain ⟨h1, hh1, r, hr, hh1s, hpr⟩ := P_dec hD hs0 hs00 hq0 hq01 hp
  have hr'Q : f⁻¹ * r * f ∈ QQ Gs 0 := by
    simpa using normalizes_pCoreOf (Gs 0) ((Gs 0).inv_mem hf) hr
  have hw : (f⁻¹ * r * f) * p' ∈ Gs 0 ⊓ Gs 1 :=
    (Gs 0 ⊓ Gs 1).mul_mem (Q0_le_P01 hD hr'Q) hp'
  have hf'eq : f' = h1 * f * ((f⁻¹ * r * f) * p') := by
    rw [hfp, hpr]; group
  have ht''G1 : ((f⁻¹ * r * f) * p')⁻¹ * t ∈ Gs 1 :=
    (Gs 1).mul_mem ((Gs 1).inv_mem hw.2) ht
  have ht''0 : ((f⁻¹ * r * f) * p')⁻¹ * t ∉ Gs 0 := fun h => ht0 (by
    have := (Gs 0).mul_mem hw.1 h
    rwa [mul_inv_cancel_left] at this)
  have hgft : h1 * f * t = f' * (((f⁻¹ * r * f) * p')⁻¹ * t) := by
    rw [hf'eq]; group
  generalize ((f⁻¹ * r * f) * p')⁻¹ * t = t'' at ht''G1 ht''0 hgft
  rcases line_pts hD ht''G1 ht''0 hq0 hq01 ht' with h | h | h
  · exact absurd h ht'0
  · refine ⟨h1, hh1.1, hh1s, ?_⟩
    rw [hgft]
    have : (f' * t')⁻¹ * (f' * t'') = (t''⁻¹ * t')⁻¹ := by group
    rw [this]; exact (Gs 0).inv_mem h
  · have hf'1 : f'⁻¹ ∉ Gs 1 := fun h => not_mem_G1_of_far hf' hnf' (by simpa using (Gs 1).inv_mem h)
    obtain ⟨n, hn, hnc⟩ := Q01_conj_ne hD ((Gs 0).inv_mem hf') hf'1
    rw [inv_inv] at hnc
    have huQ : f'⁻¹ * n * f' ∈ QQ Gs 0 := by
      simpa using normalizes_pCoreOf (Gs 0) ((Gs 0).inv_mem hf') hn.1
    have hu1 : f'⁻¹ * n * f' ∉ QQ Gs 1 := fun h => hnc ⟨huQ, h⟩
    have hnG0 : n ∈ Gs 0 := TT_le 0 (QQ_le_TT hD 0 hn.1)
    have huG1 : f'⁻¹ * n * f' ∈ Gs 1 := TT_le 1 (QQ_le_TT hD 0 huQ)
    have hs0n : s0⁻¹ * n * s0 ∈ Gs 0 := by
      have := normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem hs0) hn.2
      simpa using TT_le 0 (QQ_le_TT hD 1 this)
    have hut : f'⁻¹ * n * f' * t'' ∈ Gs 1 := (Gs 1).mul_mem huG1 ht''G1
    have hu' : (q0 * t'')⁻¹ * (f'⁻¹ * n * f' * t'') ∈ Gs 0 := by
      rcases line_pts hD ht''G1 ht''0 hq0 hq01 hut with h2 | h2 | h2
      · refine absurd ?_ ht''0
        have := (Gs 0).mul_mem ((Gs 0).inv_mem (TT_le 0 (QQ_le_TT hD 0 huQ))) h2
        rwa [inv_mul_cancel_left] at this
      · exact absurd ((fix_iff hD ht''G1 ht''0 huQ).1 (by simpa [mul_assoc] using h2)) hu1
      · exact h2
    refine ⟨n * h1, (Gs 0).mul_mem hnG0 hh1.1, ?_, ?_⟩
    · have : s0⁻¹ * (n * h1) * s0 = (s0⁻¹ * n * s0) * (s0⁻¹ * h1 * s0) := by group
      rw [this]; exact (Gs 0).mul_mem hs0n hh1s
    · have e : (f' * t')⁻¹ * (n * h1 * f * t) = ((f'⁻¹ * n * f' * t'')⁻¹ * t')⁻¹ := by
        have : n * h1 * f * t = n * (h1 * f * t) := by group
        rw [this, hgft]; group
      rw [e]
      refine (Gs 0).inv_mem ?_
      have e2 : (f'⁻¹ * n * f' * t'')⁻¹ * t' =
          ((q0 * t'')⁻¹ * (f'⁻¹ * n * f' * t''))⁻¹ * ((q0 * t'')⁻¹ * t') := by group
      rw [e2]
      exact (Gs 0).mul_mem ((Gs 0).inv_mem hu') h

end CFSG.Quasithin.H13.I51
