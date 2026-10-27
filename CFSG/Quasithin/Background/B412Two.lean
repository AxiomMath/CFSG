module

public import CFSG.Quasithin.Background.B412Orb
public import CFSG.Quasithin.Recognition.HSTypeModels
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.B412

open Matrix CFSG.Quasithin

theorem eq_of_zero_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · exact absurd (h.mp rfl) (by decide)
  · exact absurd (h.mpr rfl) (by decide)
  · rfl

theorem exists_fix_L4 {H : Type*} [Group H] [Finite H]
    (ρ : H →* SpecialLinearGroup (Fin 4) (ZMod 2)) (hρ : Function.Injective ρ)
    (h7 : 7 ∣ Nat.card H) (R : Subgroup H) [R.Normal] (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ∃ p : Fin 4 → ZMod 2, p ≠ 0 ∧
      ((∀ h, (ρ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p = p) ∨
        ∀ h, ((invTr (ρ h) : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ p = p) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨h₇, hh₇⟩ := exists_prime_orderOf_dvd_card' 7 h7
  set M₇ := (ρ h₇ : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hM₇def
  have hM₇ : M₇ ^ 7 = 1 := by
    have h1 : ρ h₇ ^ 7 = 1 := by rw [← map_pow, ← hh₇, pow_orderOf_eq_one, map_one]
    have h2 := congrArg (fun g : SpecialLinearGroup (Fin 4) (ZMod 2) =>
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) h1
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using h2
  have hM₇1 : M₇ ≠ 1 := by
    intro h
    have h1 : ρ h₇ = ρ 1 := by
      rw [map_one]
      exact Subtype.ext h
    rw [hρ h1, orderOf_one] at hh₇
    omega
  let C : AddSubgroup (Fin 4 → ZMod 2) :=
    ⨅ r : R, fixSub (ρ r : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hmemC : ∀ x, x ∈ C ↔ ∀ r : R, (ρ r : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x :=
    fun x => AddSubgroup.mem_iInf
  have hCinv : ∀ (h : H) (x : Fin 4 → ZMod 2), x ∈ C →
      (ρ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x ∈ C := by
    intro h x hx
    rw [hmemC] at hx ⊢
    intro r
    have hr : h⁻¹ * (r : H) * h ∈ R := by
      have := (inferInstance : R.Normal).conj_mem r r.2 h⁻¹
      rwa [inv_inv] at this
    have e : ρ (r : H) * ρ h = ρ h * ρ (h⁻¹ * r * h) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, e, Matrix.SpecialLinearGroup.coe_mul,
      ← mulVec_mulVec, hx ⟨_, hr⟩]
  have hCiff : ∀ (h : H) (x : Fin 4 → ZMod 2),
      (ρ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x ∈ C ↔ x ∈ C := by
    intro h x
    refine ⟨fun hx => ?_, hCinv h x⟩
    have := hCinv h⁻¹ _ hx
    rwa [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, one_mulVec] at this
  have hN : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have heven : Even (Nat.card C) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hmemC)]
    exact even_card_fix hR (ρ.comp R.subtype) (by norm_num)
  have hdvd : Nat.card C ∣ 16 := hN ▸ AddSubgroup.card_addSubgroup_dvd_card C
  have hlt : Nat.card C < 16 := by
    obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
    obtain ⟨x, hx⟩ : ∃ x, (ρ r : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x ≠ x := by
      by_contra hc
      push Not at hc
      apply hr1
      have h1 : ρ (r : H) = ρ 1 := by
        rw [map_one]
        exact Subtype.ext (eq_one_of_mulVec_eq hc)
      exact Subtype.ext (hρ h1)
    have hxC : x ∉ C := fun h => hx ((hmemC x).mp h r)
    rw [← hN, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_lt hxC
  have h4 : Nat.card C ≠ 4 := by
    intro h4
    have hfix := fix_of_invariant M₇ hM₇ (S := (C : Set (Fin 4 → ZMod 2)))
      (fun x hx => hCinv h₇ x hx) (by
        show Nat.card C < 7
        rw [h4]
        norm_num)
    have hle : Nat.card C ≤ Nat.card {x : Fin 4 → ZMod 2 // M₇ *ᵥ x = x} :=
      Nat.card_le_card_of_injective (fun x => ⟨x.1, hfix x.1 x.2⟩) fun x y hxy => by
        have h' := Subtype.ext_iff.mp hxy
        exact Subtype.ext h'
    rw [card_fix_eq_two M₇ hM₇ hM₇1, h4] at hle
    omega
  obtain ⟨k, hk, hCk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card C ∣ 2 ^ 4 from hdvd)
  have hk' : k = 1 ∨ k = 3 := by
    rw [hCk] at heven hlt h4
    interval_cases k
    · simp at heven
    · exact Or.inl rfl
    · simp at h4
    · exact Or.inr rfl
    · simp at hlt
  rcases hk' with rfl | rfl
  ·
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : C)).mp hCk
    refine ⟨y.1, fun h => hy (Subtype.ext h), Or.inl fun h => ?_⟩
    have hne : (ρ h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y.1 ≠ 0 :=
      mulVec_ne_zero _ fun h0 => hy (Subtype.ext h0)
    have := huniq ⟨_, hCinv h y.1 y.2⟩ fun h0 => hne (congrArg Subtype.val h0)
    exact congrArg Subtype.val this
  ·
    obtain ⟨p, hp, hpC⟩ := exists_dual C hCk
    refine ⟨p, hp, Or.inr fun h => invTr_mulVec fun x => eq_of_zero_iff ?_⟩
    rw [← hpC, ← hpC]
    exact hCiff h x

theorem arith_L4 {a k : ℕ} (h : a * (168 * 2 ^ k) = 20160) (ha : Odd a) : a = 15 ∧ k = 3 := by
  have hk : k < 7 := by
    by_contra hc
    push Not at hc
    have h1 : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    obtain ⟨m, rfl⟩ := ha
    have h2 : (2 * m + 1) * (168 * 2 ^ k) ≥ 1 * (168 * 2 ^ 7) := by
      apply Nat.mul_le_mul <;> omega
    omega
  obtain ⟨m, rfl⟩ := ha
  interval_cases k <;> omega

theorem arith_A7 {a k : ℕ} (h : a * (168 * 2 ^ k) = 2520) (ha : Odd a) : a = 15 ∧ k = 0 := by
  have hk : k < 4 := by
    by_contra hc
    push Not at hc
    have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    obtain ⟨m, rfl⟩ := ha
    have h2 : (2 * m + 1) * (168 * 2 ^ k) ≥ 1 * (168 * 2 ^ 4) := by
      apply Nat.mul_le_mul <;> omega
    omega
  obtain ⟨m, rfl⟩ := ha
  interval_cases k <;> omega

variable {V : Type*} [CommGroup V] [Finite V]

theorem card_eq_of_orbit {G : Subgroup (MulAut V)} {v : V}
    (hall : ∀ x : V, x ≠ 1 → x ∈ orbitOf G v) (hΩ : Nat.card (orbitOf G v) = 15) :
    Nat.card V = 2 ^ 4 := by
  classical
  have h1 : (1 : V) ∉ orbitOf G v := one_not_mem_orbitOf (ne_one_of_card hΩ)
  have heq : orbitOf G v = {x | x ≠ 1} := by
    ext x
    exact ⟨fun hx h => h1 (h ▸ hx), hall x⟩
  rw [heq] at hΩ
  have := Fintype.ofFinite V
  have h2 : Nat.card {x : V // x ≠ 1} = Nat.card V - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  have h3 : Nat.card {x : V // x ≠ 1} = 15 := hΩ
  have h4 : 0 < Nat.card V := Nat.card_pos
  omega

theorem b412_two (hV : ∀ v : V, v ^ 2 = 1) (G : Subgroup (MulAut V)) (v : V)
    (hgen : Subgroup.closure (orbitOf G v) = ⊤)
    (hU : ∃ U : Subgroup V, (∃ x ∈ U, ∃ y ∈ U, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y) ∧
      ∀ u ∈ U, u ≠ 1 → u ∈ orbitOf G v)
    (hiso : Nonempty (↥G ≃* SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥G ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (orbitOf G v)))
    (hH : Nonempty (↥(G ⊓ MulAction.stabilizer (MulAut V) v) ⧸
        CFSG.pCore 2 ↥(G ⊓ MulAction.stabilizer (MulAut V) v) ≃*
      SpecialLinearGroup (Fin 3) (ZMod 2))) :
    Nat.card V = 2 ^ 4 ∧ ∀ x : V, x ≠ 1 → x ∈ orbitOf G v := by
  classical
  obtain ⟨U, ⟨x₀, hx₀U, y₀, hy₀U, hx₀1, hy₀1, hxy⟩, hUorb⟩ := hU
  have hx₀ := hUorb x₀ hx₀U hx₀1
  have hy₀ := hUorb y₀ hy₀U hy₀1
  have hxy₀ : x₀ * y₀ ∈ orbitOf G v := by
    refine hUorb _ (U.mul_mem hx₀U hy₀U) fun h => hxy ?_
    rw [eq_inv_of_mul_eq_one_left h]
    have := hV y₀
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  have finish : (∀ a ∈ orbitOf G v, ∀ b ∈ orbitOf G v, a ≠ b → a * b ∈ orbitOf G v) →
      Nat.card (orbitOf G v) = 15 →
      Nat.card V = 2 ^ 4 ∧ ∀ x : V, x ≠ 1 → x ∈ orbitOf G v := fun hprod hΩ =>
    ⟨card_eq_of_orbit (orbit_eq_of_mul_mem hV G v hgen hprod) hΩ,
      orbit_eq_of_mul_mem hV G v hgen hprod⟩
  set H := G ⊓ MulAction.stabilizer (MulAut V) v with hHdef
  set S := MulAction.stabilizer ↥G v with hSdef
  let eS : ↥S ≃* ↥H :=
    { toFun := fun s => ⟨s.1.1, s.1.2, s.2⟩
      invFun := fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hGcard : Nat.card (orbitOf G v) * Nat.card H = Nat.card G := by
    rw [← Nat.card_congr eS.toEquiv, mul_comm]
    have := Subgroup.card_mul_index S
    rwa [MulAction.index_stabilizer, orbit_eq_orbitOf, ← Nat.card_coe_set_eq] at this
  obtain ⟨eH⟩ := hH
  have hR : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hHcard : Nat.card H = 168 * 2 ^ k := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H),
      Nat.card_congr eH.toEquiv, CFSG.Quasithin.HSType.card_SL_three_two, hk]
  rcases hiso with hφ | hφ
  ·
    obtain ⟨φ⟩ := hφ
    have hG : Nat.card G = 20160 := by
      rw [Nat.card_congr φ.toEquiv, Matrix.card_SL_field]
      simp [Fin.prod_univ_four]
    rw [hHcard, hG] at hGcard
    obtain ⟨hΩ, rfl⟩ := arith_L4 hGcard hodd
    have hR1 : CFSG.pCore 2 ↥H ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hk
      norm_num at hk
    let ρH : ↥H →* SpecialLinearGroup (Fin 4) (ZMod 2) :=
      φ.toMonoidHom.comp (Subgroup.inclusion inf_le_left)
    have hρH : Function.Injective ρH := φ.injective.comp (Subgroup.inclusion_injective _)
    obtain ⟨p, hp, hfix⟩ := exists_fix_L4 ρH hρH (by rw [hHcard]; norm_num)
      (CFSG.pCore 2 ↥H) hR hR1
    rcases hfix with hfix | hfix
    · exact finish (mul_mem_of_fix φ.toMonoidHom φ.surjective hp
        (fun g hg => hfix ⟨(g : MulAut V), g.2, hg⟩) hΩ hx₀ hy₀ hxy hxy₀) hΩ
    · exact finish (mul_mem_of_fix (invTr.comp φ.toMonoidHom)
        (invTr_surjective.comp φ.surjective) hp
        (fun g hg => hfix ⟨(g : MulAut V), g.2, hg⟩) hΩ hx₀ hy₀ hxy hxy₀) hΩ
  ·
    obtain ⟨φ⟩ := hφ
    have hG : Nat.card G = 2520 := by
      rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    rw [hHcard, hG] at hGcard
    obtain ⟨hΩ, rfl⟩ := arith_A7 hGcard hodd
    have hRbot : CFSG.pCore 2 ↥H = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hk]; rfl)
    let eH' : ↥H ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
      ((QuotientGroup.quotientMulEquivOfEq hRbot).trans QuotientGroup.quotientBot).symm.trans eH
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      CFSG.Quasithin.HSType.isSimpleGroup_SL_three_two
    have hGs : IsSimpleGroup ↥G := φ.isSimpleGroup
    have hSs : IsSimpleGroup ↥S := (eS.trans eH').isSimpleGroup
    refine finish (mul_mem_of_simple hV hGs hSs hΩ ?_ ?_ ?_ hx₀ hy₀ hxy hxy₀) hΩ
    · rw [Nat.card_congr eS.toEquiv, hHcard]
      norm_num
    · rw [hG]
      norm_num
    · rw [hG]
      norm_num

end CFSG.Quasithin.B412

end
