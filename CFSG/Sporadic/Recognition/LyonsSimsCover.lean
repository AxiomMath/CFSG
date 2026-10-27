module

public import CFSG.GH74.GLS.Stage12.McLEndgame
public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup Equiv Equiv.Perm CFSG.GH74.GLS CFSG.GH74.GLS.Stage12.McLRec
  CFSG.RankThree.PerfectCover

theorem card_alternatingGroup_eleven : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

section Cover

variable {K : Type} [Group K]

theorem card_eq_two_mul_of_doubleCover {n : ℕ} (h : IsDoubleCoverOfAlt K n) :
    Nat.card K = 2 * Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rw [Nat.card_congr e.toEquiv, hc] at h1
  omega

theorem card_eq_of_doubleCover_eleven (h : IsDoubleCoverOfAlt K 11) : Nat.card K = 39916800 := by
  rw [card_eq_two_mul_of_doubleCover h, card_alternatingGroup_eleven]

theorem card_le_two_of_normal_of_doubleCover_eleven (h : IsDoubleCoverOfAlt K 11) (T : Subgroup K)
    [T.Normal] (hT : IsPGroup 2 T) : Nat.card T ≤ 2 := by
  have hfin : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [card_eq_of_doubleCover_eleven h]; norm_num)
  obtain ⟨hq, hc, ⟨e⟩⟩ := h
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
  set Q := K ⧸ Subgroup.center K
  have hQ : Nat.card Q = 19958400 := by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_eleven]
  set T' : Subgroup Q := T.map (QuotientGroup.mk' (Subgroup.center K)) with hT'
  have : T'.Normal := Subgroup.Normal.map (inferInstance) (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _)
  have hT'2 : IsPGroup 2 T' := by
    have := hT.map (QuotientGroup.mk' (Subgroup.center K))
    simpa [hT'] using this
  rcases hs.eq_bot_or_eq_top_of_normal T' with h | h
  · have hle : T ≤ Subgroup.center K := by
      intro t ht
      have : QuotientGroup.mk' (Subgroup.center K) t ∈ T' := Subgroup.mem_map_of_mem _ ht
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff t).mp this
    calc Nat.card T ≤ Nat.card (Subgroup.center K) := Subgroup.card_le_of_le hle
      _ = 2 := hc
  · exfalso
    have hQ2 : IsPGroup 2 Q := by
      have := hT'2
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ2
    rw [hQ] at hk
    have h3 : (3 : ℕ) ∣ 2 ^ k := by rw [← hk]; norm_num
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega

end Cover

theorem exists_noncentral_involution_of_map_gen {K P : Type*} [Group K] [Group P] (ρ : K →* P)
    (a b c : P) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hc1 : c ≠ 1) (hab1 : a * b ≠ 1) (hac1 : a * c ≠ 1) (hbc1 : b * c ≠ 1)
    (habc1 : a * b * c ≠ 1) (hab2 : (a * b) * (a * b) = 1) (hac2 : (a * c) * (a * c) = 1)
    (hbc2 : (b * c) * (b * c) = 1) (habc2 : (a * b * c) * (a * b * c) = 1)
    (hρa : ∃ x, ρ x = a) (hρb : ∃ x, ρ x = b) (hρc : ∃ x, ρ x = c)
    (hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center K) (hc : Nat.card (Subgroup.center K) = 2) :
    ∃ u : K, u ^ 2 = 1 ∧ u ∉ Subgroup.center K := by
  by_contra H
  push Not at H
  obtain ⟨⟨z0, hz0⟩, hz01, hz0uniq'⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center K)).mp hc
  have hz01' : z0 ≠ 1 := fun h => hz01 (Subtype.ext h)
  have hz0uniq : ∀ c ∈ Subgroup.center K, c = 1 ∨ c = z0 := by
    intro c hc'
    by_cases h1 : c = 1
    · exact Or.inl h1
    · right
      have e1 : (⟨c, hc'⟩ : Subgroup.center K) = ⟨z0, hz0⟩ :=
        (hz0uniq' ⟨c, hc'⟩ (fun h => h1 (congrArg Subtype.val h))).trans
          (hz0uniq' ⟨z0, hz0⟩ hz01).symm
      exact congrArg Subtype.val e1
  have hsqc : ∀ c ∈ Subgroup.center K, c * c = 1 := by
    intro c hc'
    rcases hz0uniq c hc' with h | h
    · rw [h, mul_one]
    · have := pow_card_eq_one' (G := Subgroup.center K) (x := ⟨c, hc'⟩)
      rw [hc] at this
      have h2 := congrArg Subtype.val this
      simpa [pow_two] using h2
  have hsq : ∀ v : K, ρ v ≠ 1 → ρ v * ρ v = 1 → v * v = z0 := by
    intro v hv1 hv2
    have hvc : v * v ∈ Subgroup.center K := (hker (v * v)).mp (by rw [map_mul]; exact hv2)
    rcases hz0uniq _ hvc with h | h
    · exfalso
      have : v ^ 2 = 1 := by rw [pow_two]; exact h
      exact hv1 ((hker v).mpr (H v this))
    · exact h
  obtain ⟨x, hx⟩ := hρa
  obtain ⟨y, hy⟩ := hρb
  obtain ⟨w, hw⟩ := hρc
  have cen : ∀ u v : K, ρ u * ρ v = ρ v * ρ u → v⁻¹ * u⁻¹ * v * u ∈ Subgroup.center K := by
    intro u v huv
    rw [← hker]
    simp only [map_mul, map_inv]
    calc (ρ v)⁻¹ * (ρ u)⁻¹ * ρ v * ρ u = (ρ v)⁻¹ * (ρ u)⁻¹ * (ρ v * ρ u) := by group
      _ = (ρ v)⁻¹ * (ρ u)⁻¹ * (ρ u * ρ v) := by rw [huv]
      _ = 1 := by group
  have hcxy := cen x y (by rw [hx, hy]; exact hab)
  have hcxw := cen x w (by rw [hx, hw]; exact hac)
  have hcyw := cen y w (by rw [hy, hw]; exact hbc)
  have sqid : ∀ u v : K, v⁻¹ * u⁻¹ * v * u ∈ Subgroup.center K →
      (u * v) * (u * v) = (u * u) * (v * v) * (v⁻¹ * u⁻¹ * v * u) := by
    intro u v hk
    have hkc := Subgroup.mem_center_iff.mp hk
    have e : (u * v) * (u * v) = (u * u) * (v * v) * (v⁻¹ * (v⁻¹ * u⁻¹ * v * u) * v) := by group
    have hk' : v⁻¹ * (v⁻¹ * u⁻¹ * v * u) * v = v⁻¹ * u⁻¹ * v * u := by
      rw [hkc v⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, hk']
  have sxx : x * x = z0 := hsq x (by rw [hx]; exact ha1) (by rw [hx]; exact ha2)
  have syy : y * y = z0 := hsq y (by rw [hy]; exact hb1) (by rw [hy]; exact hb2)
  have sww : w * w = z0 := hsq w (by rw [hw]; exact hc1) (by rw [hw]; exact hc2)
  have sxy : (x * y) * (x * y) = z0 :=
    hsq (x * y) (by rw [map_mul, hx, hy]; exact hab1) (by rw [map_mul, hx, hy]; exact hab2)
  have sxw : (x * w) * (x * w) = z0 :=
    hsq (x * w) (by rw [map_mul, hx, hw]; exact hac1) (by rw [map_mul, hx, hw]; exact hac2)
  have syw : (y * w) * (y * w) = z0 :=
    hsq (y * w) (by rw [map_mul, hy, hw]; exact hbc1) (by rw [map_mul, hy, hw]; exact hbc2)
  have hz2 : z0 * z0 = 1 := hsqc z0 hz0
  have kxw : w⁻¹ * x⁻¹ * w * x = z0 := by
    have := sqid x w hcxw
    rw [sxw, sxx, sww, hz2, one_mul] at this
    exact this.symm
  have kyw : w⁻¹ * y⁻¹ * w * y = z0 := by
    have := sqid y w hcyw
    rw [syw, syy, sww, hz2, one_mul] at this
    exact this.symm
  have kxyw : w⁻¹ * (x * y)⁻¹ * w * (x * y) = 1 := by
    have e : w⁻¹ * (x * y)⁻¹ * w * (x * y) =
        (w⁻¹ * y⁻¹ * w * y) * (y⁻¹ * (w⁻¹ * x⁻¹ * w * x) * y) := by group
    have hkc := Subgroup.mem_center_iff.mp hz0
    have hcc : y⁻¹ * z0 * y = z0 := by rw [hkc y⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, kyw, kxw, hcc, hz2]
  have hcen : w⁻¹ * (x * y)⁻¹ * w * (x * y) ∈ Subgroup.center K := by
    rw [kxyw]; exact Subgroup.one_mem _
  have sall : (x * y * w) * (x * y * w) = 1 := by
    have := sqid (x * y) w hcen
    rw [sxy, sww, kxyw, hz2, mul_one] at this
    exact this
  have := hsq (x * y * w) (by rw [map_mul, map_mul, hx, hy, hw]; exact habc1)
    (by rw [map_mul, map_mul, hx, hy, hw]; exact habc2)
  rw [sall] at this
  exact hz01' this.symm

@[expose] def permA11 : Perm (Fin 11) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
@[expose] def permB11 : Perm (Fin 11) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7
@[expose] def permC11 : Perm (Fin 11) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

theorem sign_permA11 : sign permA11 = 1 := by simp [permA11, Perm.sign_mul]
theorem sign_permB11 : sign permB11 = 1 := by simp [permB11, Perm.sign_mul]
theorem sign_permC11 : sign permC11 = 1 := by simp [permC11, Perm.sign_mul]

theorem permABC11_facts :
    (permA11 * permB11 = permB11 * permA11) ∧ (permA11 * permC11 = permC11 * permA11) ∧
    (permB11 * permC11 = permC11 * permB11) ∧
    permA11 * permA11 = 1 ∧ permB11 * permB11 = 1 ∧ permC11 * permC11 = 1 ∧
    permA11 ≠ 1 ∧ permB11 ≠ 1 ∧ permC11 ≠ 1 ∧
    permA11 * permB11 ≠ 1 ∧ permA11 * permC11 ≠ 1 ∧ permB11 * permC11 ≠ 1 ∧
    permA11 * permB11 * permC11 ≠ 1 ∧ (permA11 * permB11) * (permA11 * permB11) = 1 ∧
    (permA11 * permC11) * (permA11 * permC11) = 1 ∧
    (permB11 * permC11) * (permB11 * permC11) = 1 ∧
    (permA11 * permB11 * permC11) * (permA11 * permB11 * permC11) = 1 := by
  unfold permA11 permB11 permC11
  decide

section Cover

variable {K : Type} [Group K]

theorem exists_noncentral_involution_of_doubleCover_eleven (h : IsDoubleCoverOfAlt K 11) :
    ∃ u : K, u ^ 2 = 1 ∧ u ∉ Subgroup.center K := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  let ρ : K →* Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  have hlift : ∀ p : Perm (Fin 11), sign p = 1 → ∃ x, ρ x = p := by
    intro p hp
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center K)
      (e.symm ⟨p, Perm.mem_alternatingGroup.mpr hp⟩)
    refine ⟨x, ?_⟩
    have := congrArg e hx
    simp only [MulEquiv.apply_symm_apply] at this
    simpa [ρ] using congrArg Subtype.val this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    permABC11_facts
  refine exists_noncentral_involution_of_map_gen ρ permA11 permB11 permC11 h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10 h11 h12 h13 h14 h15 h16 h17 (hlift _ sign_permA11) (hlift _ sign_permB11)
    (hlift _ sign_permC11) ?_ hc
  intro x
  simp only [ρ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    have : e (QuotientGroup.mk' (center K) x) = 1 := Subtype.ext hx
    rw [MulEquiv.map_eq_one_iff] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · intro hx
    have : QuotientGroup.mk' (center K) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [this, map_one]
    rfl

end Cover

theorem coverFacts_eleven : CoverFacts 11 39916800 where
  four_dvd := by norm_num
  card_eq := fun K _ h => card_eq_of_doubleCover_eleven h
  card_le_two := fun K _ h T hT hTp => card_le_two_of_normal_of_doubleCover_eleven h T hTp
  exists_noncentral := fun K _ h => exists_noncentral_involution_of_doubleCover_eleven h

section Unique

variable {n : ℕ}

theorem exists_centralExtension_of_doubleCover {K : Type} [Group K] (h : IsDoubleCoverOfAlt K n) :
    ∃ p : K →* alternatingGroup (Fin n), Function.Surjective p ∧ p.ker = Subgroup.center K := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center K)), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem nonempty_mulEquiv_hopfCover_of_doubleCover (hn : 8 ≤ n) {E : Type} [Group E]
    (hE : IsDoubleCoverOfAlt E n) :
    Nonempty (HopfCover (alternatingGroup (Fin n)) ≃* E) := by
  have hperfS : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
  obtain ⟨p, hps, hpk⟩ := exists_centralExtension_of_doubleCover hE
  have hEperf : Group.IsPerfect E := hE.1.1
  have hker : p.ker ≤ Subgroup.center E := hpk.le
  have hsurj := hopfLift_surjective p hps hker
  have hcardE : Nat.card E = 2 * Nat.card (alternatingGroup (Fin n)) :=
    card_eq_two_mul_of_doubleCover hE
  have hcardU : Nat.card (HopfCover (alternatingGroup (Fin n))) =
      2 * Nat.card (alternatingGroup (Fin n)) := by
    rw [CFSG.Alternating.Multipliers.card_hopfCover,
      CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup hn, mul_comm]
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by
    rw [hcardE]
    exact (Nat.mul_pos (by norm_num) Nat.card_pos).ne')
  have hUfin : Finite (HopfCover (alternatingGroup (Fin n))) := Nat.finite_of_card_ne_zero (by
    rw [hcardU]
    exact (Nat.mul_pos (by norm_num) Nat.card_pos).ne')
  have hbij : Function.Bijective (hopfLift p hps hker) :=
    Function.Surjective.bijective_of_nat_card_le hsurj (by rw [hcardU, hcardE])
  exact ⟨MulEquiv.ofBijective _ hbij⟩

theorem nonempty_mulEquiv_of_doubleCover_alt (hn : 8 ≤ n) {E E' : Type} [Group E] [Group E']
    (hE : IsDoubleCoverOfAlt E n) (hE' : IsDoubleCoverOfAlt E' n) : Nonempty (E ≃* E') := by
  obtain ⟨e⟩ := nonempty_mulEquiv_hopfCover_of_doubleCover hn hE
  obtain ⟨e'⟩ := nonempty_mulEquiv_hopfCover_of_doubleCover hn hE'
  exact ⟨e.symm.trans e'⟩

end Unique

end CFSG.Sporadic.Recognition.LyonsSims
