module

public import CFSG.RankThree.GF2n.Tim79a34TwoGame

public section

namespace CFSG.RankThree.GF2n.Tim79a.TwoGame

section Part1

open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

theorem dec_conj_one {G : Type} [Group G] {V : Subgroup G} : conjSubgroup (1 : G) V = V := by
  ext t
  rw [mem_conjSubgroup]
  simp

theorem dec_mem_conj {G : Type} [Group G] {V : Subgroup G} (y : G) {v : G} (hv : v ∈ V) :
    y * v * y⁻¹ ∈ conjSubgroup y V := by
  rw [mem_conjSubgroup]
  have e : y⁻¹ * (y * v * y⁻¹) * y = v := by group
  rw [e]
  exact hv

theorem dec_inf_bot {G : Type} [Group G] {V M : Subgroup G} {a v₀ : G}
    (L : LocalFacts V M a v₀) {x u : G} (hu : u = x * a * x⁻¹) (huV : u ∉ V) :
    V ⊓ conjSubgroup x V = ⊥ := by
  have hne : conjSubgroup x V ≠ conjSubgroup (1 : G) V := by
    rw [dec_conj_one]
    exact L.conj_eq x (by rw [← hu]; exact huV)
  have hbot := L.inf_eq_bot x 1 hne
  rw [dec_conj_one, inf_comm] at hbot
  exact hbot

theorem dec_enum {G : Type} [Group G] {V M : Subgroup G} {a v₀ : G}
    (L : LocalFacts V M a v₀) {x u s t : G} (hu : u = x * a * x⁻¹) (hs : s = x * v₀ * x⁻¹)
    (ht : t ∈ conjSubgroup x V) : t = 1 ∨ t = u ∨ t = s ∨ t = u * s := by
  have hus : x * (a * v₀) * x⁻¹ = u * s := by
    rw [hu, hs]
    group
  rcases L.enum x t ht with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl (h1.trans hu.symm))
  · exact Or.inr (Or.inr (Or.inl (h1.trans hs.symm)))
  · exact Or.inr (Or.inr (Or.inr (h1.trans hus)))

theorem dec_conj_inter_Q {G : Type} [Group G] {V M Q : Subgroup G} {a v₀ : G}
    (L : LocalFacts V M a v₀) {x u s t : G} (hu : u = x * a * x⁻¹) (hs : s = x * v₀ * x⁻¹)
    (huQ : u ∈ Q) (hsQ : s ∉ Q) (ht : t ∈ conjSubgroup x V) (htQ : t ∈ Q) :
    t = 1 ∨ t = u := by
  rcases dec_enum L hu hs ht with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · rw [h1] at htQ
    exact (hsQ htQ).elim
  · rw [h1] at htQ
    have h2 := Q.mul_mem (Q.inv_mem huQ) htQ
    rw [inv_mul_cancel_left] at h2
    exact (hsQ h2).elim

theorem dec_mul_ne_one {G : Type} [Group G] {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {x₀ y₀ : G}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) (hx1 : x₀ ≠ 1) : x₀ * y₀ ≠ 1 := by
  intro e
  have hx' : x₀ = y₀⁻¹ := eq_inv_of_mul_eq_one_left e
  have hxB : x₀ ∈ B := by
    rw [hx']
    exact B.inv_mem hy
  have hxAB : x₀ ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨hx, hxB⟩
  rw [hAB] at hxAB
  exact hx1 (Subgroup.mem_bot.mp hxAB)

theorem dec_conj_commute {G : Type} [Group G] (ρ b t : G) (hbt : b * t = t * b) :
    (ρ * b * ρ⁻¹) * (ρ * t * ρ⁻¹) = (ρ * t * ρ⁻¹) * (ρ * b * ρ⁻¹) := by
  calc (ρ * b * ρ⁻¹) * (ρ * t * ρ⁻¹) = ρ * (b * t) * ρ⁻¹ := by group
    _ = ρ * (t * b) * ρ⁻¹ := by rw [hbt]
    _ = (ρ * t * ρ⁻¹) * (ρ * b * ρ⁻¹) := by group

theorem dec_comm_conj_V {G : Type} [Group G] {V Q P M : Subgroup G} {a v₀ b : G}
    (h : TIData V Q P M a v₀ b) (L : LocalFacts V M a v₀) {x u z t : G}
    (hu : u = x * a * x⁻¹) (huP : u ∈ P) (hbot : V ⊓ conjSubgroup x V = ⊥)
    (hz : z ∈ V) (ht : t ∈ conjSubgroup x V) (htM : t ∈ M) : z * t = t * z := by
  have hzu : z * (x * a * x⁻¹) = (x * a * x⁻¹) * z := by
    rw [← hu]
    exact (h.P_cent u huP z hz).symm
  have hzN := Subgroup.mem_set_normalizer_iff.mp (L.normalizes x z hzu)
  have htN := (h.M_norm t).mp htM
  have h1 : t * z⁻¹ * t⁻¹ ∈ V :=
    (Subgroup.mem_set_normalizer_iff.mp htN z⁻¹).mp (V.inv_mem hz)
  have h2 : z * t * z⁻¹ ∈ conjSubgroup x V := (hzN t).mp ht
  have hmem : z * t * z⁻¹ * t⁻¹ ∈ V ⊓ conjSubgroup x V := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : z * t * z⁻¹ * t⁻¹ = z * (t * z⁻¹ * t⁻¹) := by group
      rw [e]
      exact V.mul_mem hz h1
    · exact (conjSubgroup x V).mul_mem h2 ((conjSubgroup x V).inv_mem ht)
  rw [hbot] at hmem
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem))

theorem dec_s_comm_conj {G : Type} [Group G] {V Q P M : Subgroup G} {a v₀ b : G}
    (h : TIData V Q P M a v₀ b) (L : LocalFacts V M a v₀) {x u s ρ₁ : G}
    (hu : u = x * a * x⁻¹) (huP : u ∈ P) (hbot : V ⊓ conjSubgroup x V = ⊥)
    (hsV : s ∈ conjSubgroup x V) (hsu : s * u = u * s) (hρ₁M : ρ₁ ∈ M)
    (hq : s * ρ₁ * s⁻¹ * ρ₁⁻¹ ∈ Q) (he : u * (ρ₁ * u * ρ₁⁻¹) = (ρ₁ * u * ρ₁⁻¹) * u) :
    s * (ρ₁ * u * ρ₁⁻¹) = (ρ₁ * u * ρ₁⁻¹) * s := by
  have hwP : ρ₁ * u * ρ₁⁻¹ ∈ P := h.P_norm ρ₁ hρ₁M u huP
  have hwu : (ρ₁ * u * ρ₁⁻¹) * (x * a * x⁻¹) = (x * a * x⁻¹) * (ρ₁ * u * ρ₁⁻¹) := by
    rw [← hu]
    exact he.symm
  have hwN := Subgroup.mem_set_normalizer_iff.mp (L.normalizes x (ρ₁ * u * ρ₁⁻¹) hwu)
  have hk1 : s * (ρ₁ * u * ρ₁⁻¹) * s⁻¹ * (ρ₁ * u * ρ₁⁻¹)⁻¹ ∈ conjSubgroup x V := by
    have h1 : (ρ₁ * u * ρ₁⁻¹) * s⁻¹ * (ρ₁ * u * ρ₁⁻¹)⁻¹ ∈ conjSubgroup x V :=
      (hwN s⁻¹).mp ((conjSubgroup x V).inv_mem hsV)
    have e : s * (ρ₁ * u * ρ₁⁻¹) * s⁻¹ * (ρ₁ * u * ρ₁⁻¹)⁻¹
        = s * ((ρ₁ * u * ρ₁⁻¹) * s⁻¹ * (ρ₁ * u * ρ₁⁻¹)⁻¹) := by
      group
    rw [e]
    exact (conjSubgroup x V).mul_mem hsV h1
  have hsinv_u : s⁻¹ * u * s = u := by
    calc s⁻¹ * u * s = s⁻¹ * (u * s) := by group
      _ = s⁻¹ * (s * u) := by rw [hsu]
      _ = u := by group
  have hq' : (s * ρ₁ * s⁻¹ * ρ₁⁻¹) * (ρ₁ * u * ρ₁⁻¹) * (s * ρ₁ * s⁻¹ * ρ₁⁻¹)⁻¹
      = s * (ρ₁ * u * ρ₁⁻¹) * s⁻¹ := by
    calc (s * ρ₁ * s⁻¹ * ρ₁⁻¹) * (ρ₁ * u * ρ₁⁻¹) * (s * ρ₁ * s⁻¹ * ρ₁⁻¹)⁻¹
        = s * ρ₁ * (s⁻¹ * u * s) * ρ₁⁻¹ * s⁻¹ := by group
      _ = s * ρ₁ * u * ρ₁⁻¹ * s⁻¹ := by rw [hsinv_u]
      _ = s * (ρ₁ * u * ρ₁⁻¹) * s⁻¹ := by group
  have hk2 : s * (ρ₁ * u * ρ₁⁻¹) * s⁻¹ * (ρ₁ * u * ρ₁⁻¹)⁻¹ ∈ V := by
    have hc : ⁅s * ρ₁ * s⁻¹ * ρ₁⁻¹, ρ₁ * u * ρ₁⁻¹ ⁆ ∈ V := h.QP _ hq _ hwP
    rw [commutatorElement_def] at hc
    have e : s * (ρ₁ * u * ρ₁⁻¹) * s⁻¹ * (ρ₁ * u * ρ₁⁻¹)⁻¹
        = (s * ρ₁ * s⁻¹ * ρ₁⁻¹) * (ρ₁ * u * ρ₁⁻¹) * (s * ρ₁ * s⁻¹ * ρ₁⁻¹)⁻¹
          * (ρ₁ * u * ρ₁⁻¹)⁻¹ := by
      rw [hq']
    rw [e]
    exact hc
  have hmem : s * (ρ₁ * u * ρ₁⁻¹) * s⁻¹ * (ρ₁ * u * ρ₁⁻¹)⁻¹ ∈ V ⊓ conjSubgroup x V :=
    Subgroup.mem_inf.mpr ⟨hk2, hk1⟩
  rw [hbot] at hmem
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem))

theorem two_game_dec {G : Type} [Group G] {V Q P M : Subgroup G} {a v₀ b : G}
    (h : TIData V Q P M a v₀ b) (L : LocalFacts V M a v₀) (x ρ u s u' : G)
    (hu : u = x * a * x⁻¹) (hs : s = x * v₀ * x⁻¹) (hu' : u' = ρ * u * ρ⁻¹)
    (huP : u ∈ P) (huV : u ∉ V) (hsM : s ∈ M) (hsQ : s ∉ Q)
    (hρM : ρ ∈ M) (hρV : ∀ z ∈ V, ρ * z = z * ρ)
    (hsρ : s * ρ * s⁻¹ * ρ⁻¹ ∈ Q)
    (hbu : b * u = u * b) (hbs : b * s = s * b)
    (he1 : u * u' = u' * u)
    (hperp : ∀ k ∈ P, k * u = u * k → k * u' = u' * k →
      ∃ z ∈ V, k = z ∨ k = z * u ∨ k = z * u' ∨ k = z * u * u')
    (hind : ∀ z ∈ V, z ≠ u ∧ z ≠ u' ∧ z ≠ u * u') :
    ∃ x₀ y₀ : G, x₀ * x₀ = 1 ∧ x₀ ∈ M ∧ b * x₀ = x₀ * b ∧
      (y₀ = ρ * x * v₀ * (ρ * x)⁻¹ ∨ y₀ = ρ * x * (a * v₀) * (ρ * x)⁻¹) ∧ y₀ ∈ M ∧
      (ρ * b * ρ⁻¹) * y₀ = y₀ * (ρ * b * ρ⁻¹) ∧ x₀ * y₀ ∈ V ∧ x₀ * y₀ ≠ 1 := by
  have huu : u * u = 1 := by
    calc u * u = x * (a * a) * x⁻¹ := by rw [hu]; group
      _ = 1 := by rw [h.a_sq]; group
  have hss : s * s = 1 := by
    calc s * s = x * (v₀ * v₀) * x⁻¹ := by rw [hs]; group
      _ = 1 := by rw [h.v_sq]; group
  have hsu : s * u = u * s := by
    rw [hs, hu]
    calc x * v₀ * x⁻¹ * (x * a * x⁻¹) = x * (v₀ * a) * x⁻¹ := by group
      _ = x * (a * v₀) * x⁻¹ := by rw [h.av_comm]
      _ = x * a * x⁻¹ * (x * v₀ * x⁻¹) := by group
  have huQ : u ∈ Q := h.P_le huP
  have huM : u ∈ M := h.Q_le huQ
  have hsuM : s * u ∈ M := M.mul_mem hsM huM
  have hsuQ : s * u ∉ Q := by
    intro hm
    apply hsQ
    have h2 := Q.mul_mem hm (Q.inv_mem huQ)
    rw [mul_inv_cancel_right] at h2
    exact h2
  have hsQ1 : s ≠ 1 := by
    intro e
    apply hsQ
    rw [e]
    exact Q.one_mem
  have hsuQ1 : s * u ≠ 1 := by
    intro e
    apply hsuQ
    rw [e]
    exact Q.one_mem
  have hsuu : s * u * (s * u) = 1 := by
    calc s * u * (s * u) = s * (u * s) * u := by group
      _ = s * (s * u) * u := by rw [← hsu]
      _ = (s * s) * (u * u) := by group
      _ = 1 := by rw [hss, huu, mul_one]
  have hsV : s ∈ conjSubgroup x V := by
    rw [hs]
    exact dec_mem_conj x h.v_mem
  have huVc : u ∈ conjSubgroup x V := by
    rw [hu]
    exact dec_mem_conj x h.a_mem
  have hsuV : s * u ∈ conjSubgroup x V := (conjSubgroup x V).mul_mem hsV huVc
  have hbot : V ⊓ conjSubgroup x V = ⊥ := dec_inf_bot L hu huV
  have hbsu : b * (s * u) = s * u * b := by
    calc b * (s * u) = (b * s) * u := by group
      _ = (s * b) * u := by rw [hbs]
      _ = s * (b * u) := by group
      _ = s * (u * b) := by rw [hbu]
      _ = s * u * b := by group
  obtain ⟨s', hs'⟩ : ∃ s' : G, s' = ρ * s * ρ⁻¹ := ⟨_, rfl⟩
  have hρinvM : ρ⁻¹ ∈ M := M.inv_mem hρM
  have hs'M : s' ∈ M := by
    rw [hs']
    exact M.mul_mem (M.mul_mem hρM hsM) hρinvM
  have hu'P : u' ∈ P := by
    rw [hu']
    exact h.P_norm ρ hρM u huP
  have hu'Q : u' ∈ Q := h.P_le hu'P
  have hu'M : u' ∈ M := h.Q_le hu'Q
  have hu'u' : u' * u' = 1 := by
    calc u' * u' = ρ * (u * u) * ρ⁻¹ := by rw [hu']; group
      _ = 1 := by rw [huu]; group
  have hu'1 : u' ≠ 1 := fun e => (hind 1 V.one_mem).2.1 e.symm
  have hu'u : u' ≠ u := by
    intro e
    apply (hind 1 V.one_mem).2.2
    rw [e, huu]
  have he_ρ : u * (ρ * u * ρ⁻¹) = (ρ * u * ρ⁻¹) * u := by
    rw [← hu']
    exact he1
  have hsu_u' : s * u' = u' * s := by
    rw [hu']
    exact dec_s_comm_conj h L hu huP hbot hsV hsu hρM hsρ he_ρ
  have hq2 : s * ρ⁻¹ * s⁻¹ * ρ⁻¹⁻¹ ∈ Q := by
    have e : s * ρ⁻¹ * s⁻¹ * ρ⁻¹⁻¹ = ρ⁻¹ * (s * ρ * s⁻¹ * ρ⁻¹)⁻¹ * ρ⁻¹⁻¹ := by
      group
    rw [e]
    exact h.Q_norm ρ⁻¹ hρinvM _ (Q.inv_mem hsρ)
  have he_ρinv : u * (ρ⁻¹ * u * ρ⁻¹⁻¹) = (ρ⁻¹ * u * ρ⁻¹⁻¹) * u := by
    rw [inv_inv]
    have e : ρ⁻¹ * (u * (ρ * u * ρ⁻¹)) * ρ = ρ⁻¹ * ((ρ * u * ρ⁻¹) * u) * ρ := by
      rw [he_ρ]
    calc u * (ρ⁻¹ * u * ρ) = ρ⁻¹ * ((ρ * u * ρ⁻¹) * u) * ρ := by group
      _ = ρ⁻¹ * (u * (ρ * u * ρ⁻¹)) * ρ := e.symm
      _ = ρ⁻¹ * u * ρ * u := by group
  have hs'_u : s' * u = u * s' := by
    have hc := dec_s_comm_conj h L hu huP hbot hsV hsu (M.inv_mem hρM) hq2 he_ρinv
    rw [hs']
    calc ρ * s * ρ⁻¹ * u = ρ * (s * (ρ⁻¹ * u * ρ⁻¹⁻¹)) * ρ⁻¹ := by group
      _ = ρ * ((ρ⁻¹ * u * ρ⁻¹⁻¹) * s) * ρ⁻¹ := by rw [hc]
      _ = u * (ρ * s * ρ⁻¹) := by group
  have hs'_u' : s' * u' = u' * s' := by
    rw [hs', hu']
    calc ρ * s * ρ⁻¹ * (ρ * u * ρ⁻¹) = ρ * (s * u) * ρ⁻¹ := by group
      _ = ρ * (u * s) * ρ⁻¹ := by rw [hsu]
      _ = ρ * u * ρ⁻¹ * (ρ * s * ρ⁻¹) := by group
  have hC1 : ρ * x * v₀ * (ρ * x)⁻¹ = s' := by
    rw [hs', hs]
    group
  have hsV' : s' ∈ conjSubgroup (ρ * x) V := by
    rw [← hC1]
    exact dec_mem_conj (ρ * x) h.v_mem
  have hE : ρ * x * (a * v₀) * (ρ * x)⁻¹ = u' * s' := by
    rw [hu', hs', hu, hs]
    group
  have hD1 : ρ * x * (a * v₀) * (ρ * x)⁻¹ = s' * u' := hE.trans hs'_u'.symm
  have hu'sV' : u' * s' ∈ conjSubgroup (ρ * x) V := by
    rw [← hE]
    exact dec_mem_conj (ρ * x) (V.mul_mem h.a_mem h.v_mem)
  have hD4 : s' * u' ∈ conjSubgroup (ρ * x) V := by
    rw [hs'_u']
    exact hu'sV'
  have hVu'x : conjSubgroup (ρ * x) V ≠ conjSubgroup x V := by
    intro heq
    have hmem : u' ∈ conjSubgroup x V := by
      rw [← heq]
      have e : ρ * x * a * (ρ * x)⁻¹ = u' := by
        rw [hu', hu]
        group
      rw [← e]
      exact dec_mem_conj (ρ * x) h.a_mem
    rcases dec_conj_inter_Q L hu hs huQ hsQ hmem hu'Q with h1 | h1
    · exact hu'1 h1
    · exact hu'u h1
  have hbot' : conjSubgroup x V ⊓ conjSubgroup (ρ * x) V = ⊥ :=
    L.inf_eq_bot x (ρ * x) (Ne.symm hVu'x)
  have hkQ : s * s' ∈ Q := by
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have e : s * ρ * s⁻¹ * ρ⁻¹ = s * s' := by
      rw [hsinv, hs']
      group
    rw [← e]
    exact hsρ
  have hkcent : ∀ z ∈ V, (s * s') * z = z * (s * s') := by
    intro z hz
    have h1 : z * s = s * z := dec_comm_conj_V h L hu huP hbot hz hsV hsM
    have hρz : ρ * z = z * ρ := hρV z hz
    have hρinvz : ρ⁻¹ * z = z * ρ⁻¹ := by
      calc ρ⁻¹ * z = ρ⁻¹ * (z * ρ) * ρ⁻¹ := by group
        _ = ρ⁻¹ * (ρ * z) * ρ⁻¹ := by rw [hρz]
        _ = z * ρ⁻¹ := by group
    have h2 : s' * z = z * s' := by
      rw [hs']
      calc ρ * s * ρ⁻¹ * z = ρ * s * (ρ⁻¹ * z) := by group
        _ = ρ * s * (z * ρ⁻¹) := by rw [hρinvz]
        _ = ρ * (s * z) * ρ⁻¹ := by group
        _ = ρ * (z * s) * ρ⁻¹ := by rw [h1]
        _ = (ρ * z) * s * ρ⁻¹ := by group
        _ = (z * ρ) * s * ρ⁻¹ := by rw [hρz]
        _ = z * (ρ * s * ρ⁻¹) := by group
    calc (s * s') * z = s * (s' * z) := by group
      _ = s * (z * s') := by rw [h2]
      _ = (s * z) * s' := by group
      _ = (z * s) * s' := by rw [h1]
      _ = z * (s * s') := by group
  have hkP : s * s' ∈ P := h.QV (s * s') hkQ hkcent
  have hkP_u : (s * s') * u = u * (s * s') := by
    calc (s * s') * u = s * (s' * u) := by group
      _ = s * (u * s') := by rw [hs'_u]
      _ = (s * u) * s' := by group
      _ = (u * s) * s' := by rw [hsu]
      _ = u * (s * s') := by group
  have hkP_u' : (s * s') * u' = u' * (s * s') := by
    calc (s * s') * u' = s * (s' * u') := by group
      _ = s * (u' * s') := by rw [hs'_u']
      _ = (s * u') * s' := by group
      _ = (u' * s) * s' := by rw [hsu_u']
      _ = u' * (s * s') := by group
  obtain ⟨z, hzV, hk⟩ := hperp (s * s') hkP hkP_u hkP_u'
  have huu'2 : u * u' * (u * u') = 1 := by
    calc u * u' * (u * u') = u * (u' * u) * u' := by group
      _ = u * (u * u') * u' := by rw [← he1]
      _ = (u * u) * (u' * u') := by group
      _ = 1 := by rw [huu, hu'u', mul_one]
  have hC3 : (ρ * b * ρ⁻¹) * s' = s' * (ρ * b * ρ⁻¹) := by
    rw [hs']
    exact dec_conj_commute ρ b s hbs
  have hD3 : (ρ * b * ρ⁻¹) * (s' * u') = (s' * u') * (ρ * b * ρ⁻¹) := by
    have e : s' * u' = ρ * (s * u) * ρ⁻¹ := by
      rw [hs', hu']
      group
    rw [e]
    exact dec_conj_commute ρ b (s * u) hbsu
  have hD2 : s' * u' ∈ M := M.mul_mem hs'M hu'M
  rcases hk with hk | hk | hk | hk
  · refine ⟨s, s', hss, hsM, hbs, Or.inl hC1.symm, hs'M, hC3, ?_, ?_⟩
    · rw [hk]
      exact hzV
    · exact dec_mul_ne_one hbot' hsV hsV' hsQ1
  · have e : s * u * s' = z := by
      calc s * u * s' = s * (u * s') := by group
        _ = s * (s' * u) := by rw [← hs'_u]
        _ = (s * s') * u := by group
        _ = (z * u) * u := by rw [hk]
        _ = z := by rw [mul_assoc, huu, mul_one]
    refine ⟨s * u, s', hsuu, hsuM, hbsu, Or.inl hC1.symm, hs'M, hC3, ?_, ?_⟩
    · rw [e]
      exact hzV
    · exact dec_mul_ne_one hbot' hsuV hsV' hsuQ1
  · have e : s * (s' * u') = z := by
      calc s * (s' * u') = (s * s') * u' := by group
        _ = (z * u') * u' := by rw [hk]
        _ = z := by rw [mul_assoc, hu'u', mul_one]
    refine ⟨s, s' * u', hss, hsM, hbs, Or.inr hD1.symm, hD2, hD3, ?_, ?_⟩
    · rw [e]
      exact hzV
    · exact dec_mul_ne_one hbot' hsV hD4 hsQ1
  · have e : s * u * (s' * u') = z := by
      calc s * u * (s' * u') = s * (u * s') * u' := by group
        _ = s * (s' * u) * u' := by rw [← hs'_u]
        _ = (s * s') * (u * u') := by group
        _ = (z * u * u') * (u * u') := by rw [hk]
        _ = z * (u * u' * (u * u')) := by group
        _ = z := by rw [huu'2, mul_one]
    refine ⟨s * u, s' * u', hsuu, hsuM, hbsu, Or.inr hD1.symm, hD2, hD3, ?_, ?_⟩
    · rw [e]
      exact hzV
    · exact dec_mul_ne_one hbot' hsuV hD4 hsuQ1

end Part1

section Part2

theorem two_game_fin {G : Type} [Group G] {V Q P M : Subgroup G} {a v₀ b : G}
    (h : TIData V Q P M a v₀ b) (L : LocalFacts V M a v₀) (x ρ u u' x₀ y₀ : G)
    (hu : u = x * a * x⁻¹) (hu' : u' = ρ * u * ρ⁻¹)
    (hm3 : ¬ (b * u' = u' * b))
    (hm4 : ¬ ((ρ * b * ρ⁻¹) * (b * u' * b⁻¹) = (b * u' * b⁻¹) * (ρ * b * ρ⁻¹)))
    (hρM : ρ ∈ M)
    (hx₀ : x₀ * x₀ = 1) (hx₀M : x₀ ∈ M) (hbx₀ : b * x₀ = x₀ * b)
    (hy₀ : y₀ = ρ * x * v₀ * (ρ * x)⁻¹ ∨ y₀ = ρ * x * (a * v₀) * (ρ * x)⁻¹) (hy₀M : y₀ ∈ M)
    (hb'y₀ : (ρ * b * ρ⁻¹) * y₀ = y₀ * (ρ * b * ρ⁻¹))
    (hz : x₀ * y₀ ∈ V) (hz1 : x₀ * y₀ ≠ 1) : False := by
  have hbM : b * a = a * b := (h.M_cent b).mp h.b_mem
  have hx₀a : x₀ * a = a * x₀ := (h.M_cent x₀).mp hx₀M
  have hu'eq : u' = ρ * x * a * (ρ * x)⁻¹ := by
    rw [hu', hu]
    simp only [mul_inv_rev, mul_assoc]
  have hb'M : ρ * b * ρ⁻¹ ∈ M := M.mul_mem (M.mul_mem hρM h.b_mem) (M.inv_mem hρM)
  have hb'a : (ρ * b * ρ⁻¹) * a = a * (ρ * b * ρ⁻¹) := (h.M_cent (ρ * b * ρ⁻¹)).mp hb'M
  have hza : x₀ * y₀ = a → False := by
    intro h1
    have hy : y₀ = x₀ * a := by
      calc y₀ = x₀ * (x₀ * y₀) := by rw [← mul_assoc, hx₀, one_mul]
        _ = x₀ * a := by rw [h1]
    have hby : b * y₀ = y₀ * b := by
      rw [hy]
      calc b * (x₀ * a) = (b * x₀) * a := (mul_assoc b x₀ a).symm
        _ = (x₀ * b) * a := by rw [hbx₀]
        _ = x₀ * (b * a) := mul_assoc x₀ b a
        _ = x₀ * (a * b) := by rw [hbM]
        _ = (x₀ * a) * b := (mul_assoc x₀ a b).symm
    have hyp : b * (ρ * x * v₀ * (ρ * x)⁻¹) = ρ * x * v₀ * (ρ * x)⁻¹ * b ∨
        b * (ρ * x * (a * v₀) * (ρ * x)⁻¹) = ρ * x * (a * v₀) * (ρ * x)⁻¹ * b := by
      rcases hy₀ with hy' | hy'
      · left
        rw [← hy']
        exact hby
      · right
        rw [← hy']
        exact hby
    have hc := L.cent_le (ρ * x) b hyp
    exact hm3 (by rw [hu'eq]; exact hc)
  have hzv : x₀ * y₀ = v₀ ∨ x₀ * y₀ = a * v₀ → False := by
    intro h1
    have hbz : b * (x₀ * y₀) * b⁻¹ = a * (x₀ * y₀) := by
      rcases h1 with h2 | h2
      · rw [h2]
        exact h.b_swap
      · rw [h2]
        calc b * (a * v₀) * b⁻¹ = (b * a) * v₀ * b⁻¹ := by simp only [mul_assoc]
          _ = (a * b) * v₀ * b⁻¹ := by rw [hbM]
          _ = a * (b * v₀ * b⁻¹) := by simp only [mul_assoc]
          _ = a * (a * v₀) := by rw [h.b_swap]
    have hy1 : b * y₀ * b⁻¹ = a * y₀ := by
      have key : x₀ * (b * y₀ * b⁻¹) = x₀ * (a * y₀) := by
        calc x₀ * (b * y₀ * b⁻¹) = (x₀ * b) * y₀ * b⁻¹ := by simp only [mul_assoc]
          _ = (b * x₀) * y₀ * b⁻¹ := by rw [hbx₀]
          _ = b * (x₀ * y₀) * b⁻¹ := by simp only [mul_assoc]
          _ = a * (x₀ * y₀) := hbz
          _ = (a * x₀) * y₀ := by simp only [mul_assoc]
          _ = (x₀ * a) * y₀ := by rw [hx₀a]
          _ = x₀ * (a * y₀) := by simp only [mul_assoc]
      exact mul_left_cancel key
    have hb'y2 : (ρ * b * ρ⁻¹) * (b * y₀ * b⁻¹) = (b * y₀ * b⁻¹) * (ρ * b * ρ⁻¹) := by
      rw [hy1]
      calc (ρ * b * ρ⁻¹) * (a * y₀) = ((ρ * b * ρ⁻¹) * a) * y₀ := by simp only [mul_assoc]
        _ = (a * (ρ * b * ρ⁻¹)) * y₀ := by rw [hb'a]
        _ = a * ((ρ * b * ρ⁻¹) * y₀) := by simp only [mul_assoc]
        _ = a * (y₀ * (ρ * b * ρ⁻¹)) := by rw [hb'y₀]
        _ = (a * y₀) * (ρ * b * ρ⁻¹) := by simp only [mul_assoc]
    have hyp' : b * y₀ * b⁻¹ = (b * (ρ * x)) * v₀ * (b * (ρ * x))⁻¹ ∨
        b * y₀ * b⁻¹ = (b * (ρ * x)) * (a * v₀) * (b * (ρ * x))⁻¹ := by
      rcases hy₀ with hy' | hy'
      · left
        rw [hy']
        simp only [mul_assoc, mul_inv_rev]
      · right
        rw [hy']
        simp only [mul_assoc, mul_inv_rev]
    have hyp : (ρ * b * ρ⁻¹) * ((b * (ρ * x)) * v₀ * (b * (ρ * x))⁻¹) =
        ((b * (ρ * x)) * v₀ * (b * (ρ * x))⁻¹) * (ρ * b * ρ⁻¹) ∨
        (ρ * b * ρ⁻¹) * ((b * (ρ * x)) * (a * v₀) * (b * (ρ * x))⁻¹) =
        ((b * (ρ * x)) * (a * v₀) * (b * (ρ * x))⁻¹) * (ρ * b * ρ⁻¹) := by
      rcases hyp' with h2 | h2
      · left
        rw [← h2]
        exact hb'y2
      · right
        rw [← h2]
        exact hb'y2
    have hc := L.cent_le (b * (ρ * x)) (ρ * b * ρ⁻¹) hyp
    have hkey : b * u' * b⁻¹ = (b * (ρ * x)) * a * (b * (ρ * x))⁻¹ := by
      rw [hu'eq]
      simp only [mul_assoc, mul_inv_rev]
    exact hm4 (by rw [hkey]; exact hc)
  rcases h.V_enum (x₀ * y₀) hz with h1 | h1 | h1 | h1
  · exact hz1 h1
  · exact hza h1
  · exact hzv (Or.inl h1)
  · exact hzv (Or.inr h1)

end Part2

end CFSG.RankThree.GF2n.Tim79a.TwoGame
