module

public import CFSG.Quasithin.EmptyFaithful.S143LB

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model CFSG.Quasithin.B3 Equiv

abbrev s0123 : Perm (Fin 6) := swap 0 1 * swap 2 3

abbrev s0145 : Perm (Fin 6) := swap 0 1 * swap 4 5

abbrev s2345 : Perm (Fin 6) := swap 2 3 * swap 4 5

abbrev c0123 : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3

abbrev nfix (σ : Perm (Fin 6)) : ℕ := (Finset.univ.filter (fun a : N6 => n6Act σ a = a)).card

theorem swap_of_eight_le_nfix : ∀ σ : Perm (Fin 6), σ * σ = 1 → σ ≠ 1 → 8 ≤ nfix σ →
    ∃ i j : Fin 6, i ≠ j ∧ σ = swap i j := by
  decide +kernel

theorem fix_swap_not_le : ∀ i j k l : Fin 6, i ≠ j → k ≠ l → swap i j ≠ swap k l →
    ∃ a : N6, n6Act (swap i j) a = a ∧ n6Act (swap k l) a ≠ a := by
  decide +kernel

theorem typeII_of_card : ∀ τ : Perm (Fin 6), Perm.sign τ = 1 → τ * τ = 1 → τ ≠ 1 →
    τ ≠ s0123 → τ * s0123 = s0123 * τ →
    4 ≤ (Finset.univ.filter (fun a : N6 => n6Act s0123 a = a ∧ n6Act τ a = a)).card →
    τ = s0145 ∨ τ = s2345 := by
  decide +kernel

theorem even_of_rawD : ∀ w : Fin 6 → ZMod 2, rawD w s0123 = 0 →
    (rawD w s0145 = 0 ∨ rawD w s2345 = 0) → ∑ i, w i = 0 := by
  decide +kernel

theorem fixed_gens : ∀ a : N6, n6Act (swap 0 1 * swap 1 2) a = a →
    n6Act (swap 1 2 * swap 2 3) a = a → n6Act (swap 2 3 * swap 3 4) a = a →
    n6Act (swap 3 4 * swap 4 5) a = a → a.1 = 1 := by
  decide +kernel

theorem center_gens : ∀ σ : Perm (Fin 6), σ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * σ →
    σ * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * σ →
    σ * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * σ →
    σ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * σ → σ = 1 := by
  decide +kernel

theorem gens_mem : swap (0 : Fin 6) 1 * swap 1 2 ∈ alternatingGroup (Fin 6) ∧
    swap (1 : Fin 6) 2 * swap 2 3 ∈ alternatingGroup (Fin 6) ∧
    swap (2 : Fin 6) 3 * swap 3 4 ∈ alternatingGroup (Fin 6) ∧
    swap (3 : Fin 6) 4 * swap 4 5 ∈ alternatingGroup (Fin 6) := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem c0123_sq_ne : c0123 ^ 2 ≠ 1 := by decide

theorem c0123_pow_four : c0123 ^ 4 = 1 := by decide

theorem fixed_alt6 (a : N6) (h : ∀ σ ∈ alternatingGroup (Fin 6), n6Act σ a = a) : a = 1 :=
  Subtype.ext (fixed_gens a (h _ gens_mem.1) (h _ gens_mem.2.1) (h _ gens_mem.2.2.1)
    (h _ gens_mem.2.2.2))

theorem center_alt6 (σ : Perm (Fin 6))
    (h : ∀ τ ∈ alternatingGroup (Fin 6), σ * τ = τ * σ) : σ = 1 :=
  center_gens σ (h _ gens_mem.1) (h _ gens_mem.2.1) (h _ gens_mem.2.2.1) (h _ gens_mem.2.2.2)

theorem card_perm_six : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem isPGroup_of_sq {B : Subgroup (Perm (Fin 6))} (hB : ∀ b ∈ B, b * b = 1) :
    IsPGroup 2 ↥B := by
  intro b
  refine ⟨1, Subtype.ext ?_⟩
  simpa [pow_one, sq] using hB b b.2

theorem card_dvd_sixteen {B : Subgroup (Perm (Fin 6))} (hB : IsPGroup 2 ↥B) :
    Nat.card B ∣ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hB.exists_card_eq
  have h := Subgroup.card_subgroup_dvd_card B
  rw [card_perm_six, hk] at h
  rw [hk]
  have hk4 : k ≤ 4 := by
    by_contra hlt
    have h32 : 2 ^ 5 ∣ 720 := (pow_dvd_pow 2 (by omega : 5 ≤ k)).trans h
    norm_num at h32
  exact pow_dvd_pow 2 hk4 |>.trans (by norm_num)

theorem card_le_eight {B : Subgroup (Perm (Fin 6))} (hB : ∀ b ∈ B, b * b = 1) :
    Nat.card B ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 := isPGroup_of_sq hB
  have h16 := card_dvd_sixteen hB2
  by_contra hgt
  have hB16 : Nat.card B = 16 := by
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) h16
    rcases (Nat.dvd_prime_pow (Nat.prime_two)).1 (show Nat.card B ∣ 2 ^ 4 by simpa using h16) with
      ⟨m, hm, hm'⟩
    interval_cases m <;> simp_all
  obtain ⟨Q, hBQ⟩ := hB2.exists_le_sylow
  have hQ16 : Nat.card Q = 16 := by
    refine le_antisymm (Nat.le_of_dvd (by norm_num) (card_dvd_sixteen Q.isPGroup')) ?_
    rw [← hB16]
    exact Subgroup.card_le_of_le hBQ
  have hBQ' : B = Q := Subgroup.eq_of_le_of_card_ge hBQ (by rw [hB16, hQ16])
  have hg : IsPGroup 2 ↥(Subgroup.zpowers c0123) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime_pow (by simpa using c0123_sq_ne) (by simpa using c0123_pow_four)
  obtain ⟨Q', hgQ'⟩ := hg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) Q Q'
  have hmem : c0123 ∈ ((h • Q : Sylow 2 (Perm (Fin 6))) : Subgroup (Perm (Fin 6))) := by
    rw [hh]
    exact hgQ' (Subgroup.mem_zpowers c0123)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  have hmemB : (MulAut.conj h)⁻¹ • c0123 ∈ B := by rw [hBQ']; exact hmem
  have hsq := hB _ hmemB
  apply c0123_sq_ne
  have : (MulAut.conj h)⁻¹ • c0123 = h⁻¹ * c0123 * h := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  rw [this] at hsq
  calc c0123 ^ 2 = c0123 * c0123 := sq _
    _ = h * ((h⁻¹ * c0123 * h) * (h⁻¹ * c0123 * h)) * h⁻¹ := by group
    _ = 1 := by rw [hsq]; group

@[expose] def fixN6 (B : Subgroup (Perm (Fin 6))) : Subgroup N6 where
  carrier := {a | ∀ b ∈ B, n6Act b a = a}
  mul_mem' := fun ha hb b hbB => by rw [map_mul, ha b hbB, hb b hbB]
  one_mem' := fun b _ => map_one _
  inv_mem' := fun ha b hbB => by rw [map_inv, ha b hbB]

theorem mem_fixN6 {B : Subgroup (Perm (Fin 6))} {a : N6} :
    a ∈ fixN6 B ↔ ∀ b ∈ B, n6Act b a = a :=
  Iff.rfl

@[expose] def stabN6 (a : N6) : Subgroup (Perm (Fin 6)) :=
  (MulAction.stabilizer (MulAut N6) a).comap n6Act

theorem mem_stabN6 {a : N6} {σ : Perm (Fin 6)} : σ ∈ stabN6 a ↔ n6Act σ a = a :=
  Iff.rfl

theorem mem_fixN6_zpowers {σ : Perm (Fin 6)} {a : N6} :
    a ∈ fixN6 (Subgroup.zpowers σ) ↔ n6Act σ a = a := by
  constructor
  · intro h
    exact h σ (Subgroup.mem_zpowers σ)
  · intro h b hb
    have hle : Subgroup.zpowers σ ≤ stabN6 a := (Subgroup.zpowers_le).2 (mem_stabN6.2 h)
    exact mem_stabN6.1 (hle hb)

theorem fixN6_mono {B B' : Subgroup (Perm (Fin 6))} (h : B ≤ B') : fixN6 B' ≤ fixN6 B :=
  fun _ ha b hb => ha b (h hb)

theorem card_fixN6_zpowers (σ : Perm (Fin 6)) :
    Nat.card ↥(fixN6 (Subgroup.zpowers σ)) = nfix σ := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_fixN6_zpowers

theorem card_dvd_sixteen_N6 (H : Subgroup N6) : Nat.card H ∣ 16 := by
  rw [← n6_card]
  exact Subgroup.card_subgroup_dvd_card H

theorem card_le_eight_of_ne_top {H : Subgroup N6} (hH : H ≠ ⊤) : Nat.card H ≤ 8 := by
  have h := card_dvd_sixteen_N6 H
  have hne : Nat.card H ≠ 16 := by
    intro h16
    apply hH
    apply Subgroup.eq_top_of_card_eq
    rw [h16, n6_card]
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card H ∣ 2 ^ 4 by simpa using h) with
    ⟨m, hm, hm'⟩
  interval_cases m <;> simp_all

theorem nfix_le_eight {σ : Perm (Fin 6)} (hσ : σ ≠ 1) : nfix σ ≤ 8 := by
  rw [← card_fixN6_zpowers]
  refine card_le_eight_of_ne_top fun h => hσ (n6_faithful_perm σ fun a => ?_)
  have : a ∈ fixN6 (Subgroup.zpowers σ) := by rw [h]; trivial
  exact mem_fixN6_zpowers.1 this

theorem card_fix_inf_le_four {σ τ : Perm (Fin 6)} (hσ2 : σ * σ = 1) (hτ2 : τ * τ = 1)
    (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hστ : σ ≠ τ) :
    Nat.card ↥(fixN6 (Subgroup.zpowers σ) ⊓ fixN6 (Subgroup.zpowers τ)) ≤ 4 := by
  set H := fixN6 (Subgroup.zpowers σ) ⊓ fixN6 (Subgroup.zpowers τ) with hH
  by_contra hgt
  have h8 : 8 ≤ Nat.card H := by
    have h := card_dvd_sixteen_N6 H
    rcases (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card H ∣ 2 ^ 4 by simpa using h) with
      ⟨m, hm, hm'⟩
    interval_cases m <;> simp_all
  have hσle : H ≤ fixN6 (Subgroup.zpowers σ) := inf_le_left
  have hτle : H ≤ fixN6 (Subgroup.zpowers τ) := inf_le_right
  have hσ8 : 8 ≤ nfix σ := by
    rw [← card_fixN6_zpowers]
    exact h8.trans (Subgroup.card_le_of_le hσle)
  have hτ8 : 8 ≤ nfix τ := by
    rw [← card_fixN6_zpowers]
    exact h8.trans (Subgroup.card_le_of_le hτle)
  have hσeq : H = fixN6 (Subgroup.zpowers σ) := by
    refine Subgroup.eq_of_le_of_card_ge hσle ?_
    rw [card_fixN6_zpowers]
    exact (nfix_le_eight hσ1).trans h8
  obtain ⟨i, j, hij, rfl⟩ := swap_of_eight_le_nfix σ hσ2 hσ1 hσ8
  obtain ⟨k, l, hkl, rfl⟩ := swap_of_eight_le_nfix τ hτ2 hτ1 hτ8
  obtain ⟨a, ha, hna⟩ := fix_swap_not_le i j k l hij hkl hστ
  apply hna
  have haH : a ∈ H := by rw [hσeq]; exact mem_fixN6_zpowers.2 ha
  exact mem_fixN6_zpowers.1 (hτle haH)


theorem card_fixN6_inf (α β : Perm (Fin 6)) :
    Nat.card ↥(fixN6 (Subgroup.zpowers α) ⊓ fixN6 (Subgroup.zpowers β)) =
      (Finset.univ.filter (fun a : N6 => n6Act α a = a ∧ n6Act β a = a)).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf]
  rw [mem_fixN6_zpowers, mem_fixN6_zpowers]

theorem card_mul_fixN6_le {B : Subgroup (Perm (Fin 6))} (hB : ∀ b ∈ B, b * b = 1) :
    Nat.card B * Nat.card ↥(fixN6 B) ≤ 32 ∧
      (Nat.card B * Nat.card ↥(fixN6 B) = 32 → Nat.card B = 8 ∧ Nat.card ↥(fixN6 B) = 4) := by
  have h8 := card_le_eight hB
  have h16 := card_dvd_sixteen (isPGroup_of_sq hB)
  have hfix16 : Nat.card ↥(fixN6 B) ≤ 16 := by
    rw [← n6_card]
    exact Subgroup.card_le_card_group _
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card B ∣ 2 ^ 4 by simpa using h16) with
    ⟨m, hm, hBm⟩
  interval_cases m
  ·
    rw [hBm]
    constructor
    · simp only [pow_zero, one_mul]; omega
    · intro h; simp only [pow_zero, one_mul] at h; omega
  ·
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra h
      push Not at h
      have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 h
      rw [this, Subgroup.card_bot] at hBm
      norm_num at hBm
    have hle : fixN6 B ≤ fixN6 (Subgroup.zpowers b) :=
      fixN6_mono ((Subgroup.zpowers_le).2 hbB)
    have hfix8 : Nat.card ↥(fixN6 B) ≤ 8 :=
      (Subgroup.card_le_of_le hle).trans ((card_fixN6_zpowers b).le.trans (nfix_le_eight hb1))
    rw [hBm]
    constructor
    · simp only [pow_one]; omega
    · intro h; simp only [pow_one] at h; omega
  all_goals
    try (exfalso; rw [hBm] at h8; norm_num at h8; done)
  all_goals
    obtain ⟨σ, hσB, hσ1⟩ : ∃ σ ∈ B, σ ≠ 1 := by
      by_contra h
      push Not at h
      have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 h
      rw [this, Subgroup.card_bot] at hBm
      norm_num at hBm
    have hzle : Nat.card ↥(Subgroup.zpowers σ) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact hB σ hσB)
    obtain ⟨τ, hτB, hτσ⟩ : ∃ τ ∈ B, τ ∉ Subgroup.zpowers σ := by
      by_contra h
      push Not at h
      have hle : B ≤ Subgroup.zpowers σ := h
      have := (Subgroup.card_le_of_le hle).trans hzle
      rw [hBm] at this
      norm_num at this
    have hτ1 : τ ≠ 1 := fun h => hτσ (h ▸ Subgroup.one_mem _)
    have hστ : σ ≠ τ := fun h => hτσ (h ▸ Subgroup.mem_zpowers σ)
    have hle : fixN6 B ≤ fixN6 (Subgroup.zpowers σ) ⊓ fixN6 (Subgroup.zpowers τ) :=
      le_inf (fixN6_mono ((Subgroup.zpowers_le).2 hσB)) (fixN6_mono ((Subgroup.zpowers_le).2 hτB))
    have hfix4 : Nat.card ↥(fixN6 B) ≤ 4 := (Subgroup.card_le_of_le hle).trans
      (card_fix_inf_le_four (hB σ hσB) (hB τ hτB) hσ1 hτ1 hστ)
    rw [hBm]
    constructor
    · norm_num; omega
    · intro h; norm_num at h ⊢; omega

theorem isDer_conj {Γ W : Type*} [Group Γ] [CommGroup W] {ρ : Γ →* MulAut W} {d : Γ → W}
    (hd : IsDer ρ d) (g : Γ) : IsDer ρ (fun x => ρ g⁻¹ (d (g * x * g⁻¹))) := by
  intro x y
  have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  simp only
  rw [e, hd, map_mul]
  congr 1
  rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
  congr 2
  group

theorem isPrin_of_vanish {d : LG 6 → N6} (hd : IsDer n6ActL d) {σ τ : LG 6}
    (hσ2 : σ * σ = 1) (hτ2 : τ * τ = 1) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hστ : σ ≠ τ)
    (hcomm : σ * τ = τ * σ)
    (h4 : 4 ≤ Nat.card ↥(fixN6 (Subgroup.zpowers (σ : Perm (Fin 6))) ⊓
      fixN6 (Subgroup.zpowers (τ : Perm (Fin 6)))))
    (hdσ : d σ = 1) (hdτ : d τ = 1) : ∃ a : N6, ∀ x : LG 6, d x = n6ActL x a * a⁻¹ := by
  have hs0 : s0123 ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup]; decide
  have hσ1' : (σ : Perm (Fin 6)) ≠ 1 := fun h => hσ1 (Subtype.ext h)
  have hσ2' : (σ : Perm (Fin 6)) * σ = 1 := congrArg Subtype.val hσ2
  obtain ⟨ρ, hρ, hρσ⟩ := alt6_invol_conj s0123 σ hs0 σ.2 (by decide) hσ1' (by decide) hσ2'
  set g : LG 6 := ⟨ρ, hρ⟩ with hg
  set d' : LG 6 → N6 := fun x => n6ActL g⁻¹ (d (g * x * g⁻¹)) with hd'
  have hd'D : IsDer n6ActL d' := isDer_conj hd g
  set τ' : LG 6 := g⁻¹ * τ * g with hτ'
  have hgσ : g * ⟨s0123, hs0⟩ * g⁻¹ = σ := Subtype.ext hρσ
  have hτ'v : (τ' : Perm (Fin 6)) = ρ⁻¹ * τ * ρ := rfl
  have hτ'cases : (τ' : Perm (Fin 6)) = s0145 ∨ (τ' : Perm (Fin 6)) = s2345 := by
    refine typeII_of_card _ (Perm.mem_alternatingGroup.1 τ'.2) ?_ ?_ ?_ ?_ ?_
    · rw [hτ'v]
      have hτ2' : (τ : Perm (Fin 6)) * τ = 1 := congrArg Subtype.val hτ2
      calc ρ⁻¹ * τ * ρ * (ρ⁻¹ * τ * ρ) = ρ⁻¹ * ((τ : Perm (Fin 6)) * τ) * ρ := by group
        _ = 1 := by rw [hτ2']; group
    · intro h
      apply hτ1
      apply Subtype.ext
      rw [hτ'v] at h
      calc (τ : Perm (Fin 6)) = ρ * (ρ⁻¹ * τ * ρ) * ρ⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      apply hστ
      apply Subtype.ext
      rw [hτ'v] at h
      calc (σ : Perm (Fin 6)) = ρ * s0123 * ρ⁻¹ := hρσ.symm
        _ = ρ * (ρ⁻¹ * τ * ρ) * ρ⁻¹ := by rw [← h]
        _ = τ := by group
    · rw [hτ'v]
      have hc : (σ : Perm (Fin 6)) * τ = τ * σ := congrArg Subtype.val hcomm
      rw [← hρσ] at hc
      calc ρ⁻¹ * τ * ρ * s0123 = ρ⁻¹ * ((τ : Perm (Fin 6)) * (ρ * s0123 * ρ⁻¹)) * ρ := by group
        _ = ρ⁻¹ * ((ρ * s0123 * ρ⁻¹) * τ) * ρ := by rw [hc]
        _ = s0123 * (ρ⁻¹ * τ * ρ) := by group
    · rw [← card_fixN6_inf]
      have hmap : (fixN6 (Subgroup.zpowers (σ : Perm (Fin 6))) ⊓
          fixN6 (Subgroup.zpowers (τ : Perm (Fin 6)))).map (n6Act ρ⁻¹).toMonoidHom ≤
          fixN6 (Subgroup.zpowers s0123) ⊓ fixN6 (Subgroup.zpowers (τ' : Perm (Fin 6))) := by
        rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩
        have ha1' : n6Act (σ : Perm (Fin 6)) a = a := mem_fixN6_zpowers.1 ha1
        have ha2' : n6Act (τ : Perm (Fin 6)) a = a := mem_fixN6_zpowers.1 ha2
        refine ⟨mem_fixN6_zpowers.2 ?_, mem_fixN6_zpowers.2 ?_⟩
        · show n6Act s0123 (n6Act ρ⁻¹ a) = n6Act ρ⁻¹ a
          rw [← MulAut.mul_apply, ← map_mul]
          have : s0123 * ρ⁻¹ = ρ⁻¹ * σ := by rw [← hρσ]; group
          rw [this, map_mul, MulAut.mul_apply, ha1']
        · show n6Act (τ' : Perm (Fin 6)) (n6Act ρ⁻¹ a) = n6Act ρ⁻¹ a
          rw [hτ'v, ← MulAut.mul_apply, ← map_mul]
          have : ρ⁻¹ * τ * ρ * ρ⁻¹ = ρ⁻¹ * τ := by group
          rw [this, map_mul, MulAut.mul_apply, ha2']
      refine h4.trans ?_
      rw [← Subgroup.card_map_of_injective (f := (n6Act ρ⁻¹).toMonoidHom)
        (by exact (n6Act ρ⁻¹).injective)]
      exact Subgroup.card_le_of_le hmap
  have hd's : d' ⟨s0123, hs0⟩ = 1 := by
    simp only [hd', hgσ, hdσ, map_one]
  have hd'τ : d' τ' = 1 := by
    have : g * τ' * g⁻¹ = τ := by rw [hτ']; group
    simp only [hd', this, hdτ, map_one]
  obtain ⟨w, hw⟩ := z1_N6 d' hd'D
  have hr0 : rawD w s0123 = 0 := by
    rw [← dW_eq_one_iff, ← hw ⟨s0123, hs0⟩]
    exact hd's
  have hrτ : rawD w (τ' : Perm (Fin 6)) = 0 := by
    rw [← dW_eq_one_iff, ← hw τ']
    exact hd'τ
  have heven : ∑ i, w i = 0 := by
    refine even_of_rawD w hr0 ?_
    rcases hτ'cases with h | h
    · left; rw [← h]; exact hrτ
    · right; rw [← h]; exact hrτ
  obtain ⟨a', ha'⟩ := dW_principal_of_even heven
  refine ⟨n6ActL g a', fun x => ?_⟩
  have h1 : d x = n6ActL g (d' (g⁻¹ * x * g)) := by
    simp only [hd']
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [h1, hw, ha', map_mul, map_inv]
  congr 1
  show n6Act (g : Perm (Fin 6)) (n6Act ((g⁻¹ * x * g : LG 6) : Perm (Fin 6)) a') =
    n6Act (x : Perm (Fin 6)) (n6Act (g : Perm (Fin 6)) a')
  rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
  congr 2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

end SmithB57E

end CFSG.Quasithin
