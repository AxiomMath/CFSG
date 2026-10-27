module

public import CFSG.Quasithin.Background.F6CatRecogInputs2
public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace F6

namespace L28Res

abbrev T8 := GF8 × GF8 × GF8 × GF8

@[expose] def tmul (x y : T8) : T8 :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
    x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)

@[expose] def tdet (x : T8) : GF8 := x.1 * x.2.2.2 + x.2.1 * x.2.2.1

@[expose] def tinv (x : T8) : T8 := (x.2.2.2, x.2.1, x.2.2.1, x.1)

theorem gf8_two_eq_zero : (2 : GF8) = 0 := by decide

theorem gf8_sub_eq_add (a b : GF8) : a - b = a + b := by
  revert a b
  decide

theorem tdet_tmul (x y : T8) : tdet (tmul x y) = tdet x * tdet y := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨e, f, g, h⟩ := y
  simp only [tdet, tmul]
  linear_combination (a * c * e * f + b * d * g * h) * gf8_two_eq_zero

abbrev G8 := {x : T8 // tdet x = 1}

instance : Group G8 where
  mul x y := ⟨tmul x.1 y.1, by rw [tdet_tmul, x.2, y.2, mul_one]⟩
  one := ⟨(1, 0, 0, 1), by decide⟩
  inv x := ⟨tinv x.1, by
    obtain ⟨⟨a, b, c, d⟩, hx⟩ := x
    simp only [tdet, tinv] at hx ⊢
    rw [← hx]
    ring⟩
  mul_assoc x y z := by
    apply Subtype.ext
    obtain ⟨⟨a, b, c, d⟩, -⟩ := x
    obtain ⟨⟨e, f, g, h⟩, -⟩ := y
    obtain ⟨⟨i, j, k, l⟩, -⟩ := z
    show tmul (tmul (a, b, c, d) (e, f, g, h)) (i, j, k, l) =
      tmul (a, b, c, d) (tmul (e, f, g, h) (i, j, k, l))
    simp only [tmul, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring, by ring⟩
  one_mul x := by
    apply Subtype.ext
    obtain ⟨⟨a, b, c, d⟩, -⟩ := x
    show tmul (1, 0, 0, 1) (a, b, c, d) = (a, b, c, d)
    simp [tmul]
  mul_one x := by
    apply Subtype.ext
    obtain ⟨⟨a, b, c, d⟩, -⟩ := x
    show tmul (a, b, c, d) (1, 0, 0, 1) = (a, b, c, d)
    simp [tmul]
  inv_mul_cancel x := by
    apply Subtype.ext
    obtain ⟨⟨a, b, c, d⟩, hx⟩ := x
    simp only [tdet] at hx
    show tmul (tinv (a, b, c, d)) (a, b, c, d) = (1, 0, 0, 1)
    simp only [tmul, tinv, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hx]
      ring
    · linear_combination (b * d) * gf8_two_eq_zero
    · linear_combination (a * c) * gf8_two_eq_zero
    · rw [← hx]
      ring

theorem val_mul (x y : G8) : ((x * y : G8) : T8) = tmul x y := rfl

theorem card_G8 : Nat.card G8 = 504 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def ga : G8 := ⟨(GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1), by decide⟩

@[expose] def gb : G8 := ⟨(GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 6, GF8.ofNat' 1), by decide⟩

@[expose] def g9 : G8 := ga * gb * ga * gb⁻¹

@[expose] def g7 : G8 := gb * ga * gb * ga * gb * ga * gb⁻¹

theorem gen_facts_ab : ga ≠ 1 ∧ ga * ga = 1 ∧ gb ≠ 1 ∧ gb ^ 3 = 1 := by
  decide +kernel

theorem gen_facts_prod : ga * gb ≠ 1 ∧ (ga * gb) ^ 7 = 1 ∧ ¬ g9 ^ 3 = 1 ∧ g9 ^ 9 = 1 := by
  decide +kernel

@[expose] def uHom : Multiplicative GF8 →* G8 where
  toFun t := ⟨(1, t.toAdd, 0, 1), by simp [tdet]⟩
  map_one' := rfl
  map_mul' s t := Subtype.ext (by
    show ((1 : GF8), s.toAdd + t.toAdd, (0 : GF8), (1 : GF8)) =
      tmul (1, s.toAdd, 0, 1) (1, t.toAdd, 0, 1)
    simp [tmul, add_comm])

theorem uHom_injective : Function.Injective uHom := fun s t h => by
  have := congrArg (fun x : G8 => x.1.2.1) h
  exact this

theorem u_words : ∀ t : GF8, t = 0 ∨
    ∃ k : Fin 7, ((g7 ^ (k : ℕ) * ga * g7 ^ (7 - (k : ℕ)) : G8) : T8) = (1, t, 0, 1) := by
  decide +kernel

theorem closure_eq_top : Subgroup.closure ({ga, gb} : Set G8) = ⊤ := by
  obtain ⟨hab1, hab7, h93, h99⟩ := gen_facts_prod
  set H := Subgroup.closure ({ga, gb} : Set G8)
  have ha : ga ∈ H := Subgroup.subset_closure (by simp)
  have hb : gb ∈ H := Subgroup.subset_closure (by simp)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h7 : 7 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H (H.mul_mem ha hb)
    rwa [orderOf_eq_prime hab7 hab1] at this
  have h9 : 9 ∣ Nat.card H := by
    have h9H : g9 ∈ H := H.mul_mem (H.mul_mem (H.mul_mem ha hb) ha) (H.inv_mem hb)
    have := Subgroup.orderOf_dvd_natCard H h9H
    rwa [orderOf_eq_prime_pow (n := 1) (p := 3) (by simpa using h93) (by simpa using h99)]
      at this
  have h8 : 8 ∣ Nat.card H := by
    have h7H : g7 ∈ H := H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem hb ha) hb) ha) hb) ha) (H.inv_mem hb)
    have hU : uHom.range ≤ H := by
      rintro _ ⟨t, rfl⟩
      rcases u_words t.toAdd with ht | ⟨k, hk⟩
      · have : t = 1 := ht
        rw [this, map_one]
        exact H.one_mem
      · have : uHom t = g7 ^ (k : ℕ) * ga * g7 ^ (7 - (k : ℕ)) := Subtype.ext hk.symm
        rw [this]
        exact H.mul_mem (H.mul_mem (H.pow_mem h7H _) ha) (H.pow_mem h7H _)
    have := Subgroup.card_dvd_of_le hU
    rwa [MonoidHom.range_eq_map, Subgroup.card_map_of_injective uHom_injective,
      Subgroup.card_top, Nat.card_eq_fintype_card] at this
  have h504 : 504 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 72 7)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 9) h8 h9) h7
  apply Subgroup.eq_top_of_card_eq
  have hle := Subgroup.card_le_card_group H
  rw [card_G8] at hle ⊢
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos h504)

theorem finite_mulAut : Finite (MulAut G8) :=
  Finite.of_injective (fun α : MulAut G8 => (α : G8 → G8)) DFunLike.coe_injective

theorem card_involutions : Fintype.card {x : G8 // x ≠ 1 ∧ x * x = 1} = 63 := by
  decide +kernel

theorem card_partners :
    Fintype.card {y : G8 // y ≠ 1 ∧ y ^ 3 = 1 ∧ ga * y ≠ 1 ∧ (ga * y) ^ 7 = 1} = 24 := by
  decide +kernel

theorem card_mulAut_le : Nat.card (MulAut G8) ≤ 1512 := by
  have : Finite (MulAut G8) := finite_mulAut
  obtain ⟨ha1, ha2, hb1, hb3⟩ := gen_facts_ab
  obtain ⟨hab1, hab7, -, -⟩ := gen_facts_prod
  have hos := Subgroup.card_mul_index (MulAction.stabilizer (MulAut G8) ga)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at hos
  have horb : Nat.card (MulAction.orbit (MulAut G8) ga) ≤ 63 := by
    calc _ ≤ Nat.card ({x : G8 | x ≠ 1 ∧ x * x = 1} : Set G8) :=
          Nat.card_mono (Set.toFinite _) (by
            rintro _ ⟨α, rfl⟩
            refine ⟨?_, ?_⟩
            · simp only [MulAut.smul_def]
              exact fun h => ha1 (α.injective (h.trans (map_one α).symm))
            · simp only [MulAut.smul_def]
              rw [← map_mul, ha2, map_one])
      _ = 63 := by
        rw [← card_involutions, ← Nat.card_eq_fintype_card]
        rfl
  have hstab : Nat.card (MulAction.stabilizer (MulAut G8) ga) ≤ 24 := by
    let f : MulAction.stabilizer (MulAut G8) ga →
        {y : G8 // y ≠ 1 ∧ y ^ 3 = 1 ∧ ga * y ≠ 1 ∧ (ga * y) ^ 7 = 1} := fun α => by
      have hα : (α : MulAut G8) ga = ga := MulAction.mem_stabilizer_iff.mp α.2
      have hαab : ga * (α : MulAut G8) gb = (α : MulAut G8) (ga * gb) := by
        rw [map_mul, hα]
      refine ⟨(α : MulAut G8) gb, ?_, ?_, ?_, ?_⟩
      · exact fun h => hb1 ((α : MulAut G8).injective (h.trans (map_one _).symm))
      · rw [← map_pow, hb3, map_one]
      · rw [hαab]
        exact fun h => hab1 ((α : MulAut G8).injective (h.trans (map_one _).symm))
      · rw [hαab, ← map_pow, hab7, map_one]
    have hf : Function.Injective f := by
      intro α β hαβ
      have hb : (α : MulAut G8) gb = (β : MulAut G8) gb := congrArg Subtype.val hαβ
      have ha : (α : MulAut G8) ga = (β : MulAut G8) ga :=
        (MulAction.mem_stabilizer_iff.mp α.2).trans (MulAction.mem_stabilizer_iff.mp β.2).symm
      have heq : Set.EqOn ((α : MulAut G8).toMonoidHom) ((β : MulAut G8).toMonoidHom)
          ({ga, gb} : Set G8) := by
        intro z hz
        rcases hz with rfl | rfl
        · exact ha
        · exact hb
      have hcl := MonoidHom.eqOn_closure heq
      rw [closure_eq_top] at hcl
      exact Subtype.ext (MulEquiv.ext fun z => hcl (Set.mem_univ z))
    calc _ ≤ Nat.card {y : G8 // y ≠ 1 ∧ y ^ 3 = 1 ∧ ga * y ≠ 1 ∧ (ga * y) ^ 7 = 1} :=
          Nat.card_le_card_of_injective f hf
      _ = 24 := by rw [Nat.card_eq_fintype_card, card_partners]
  rw [← hos]
  calc _ ≤ 24 * 63 := Nat.mul_le_mul hstab horb
    _ = 1512 := by norm_num

@[expose] def frobT (x : T8) : T8 :=
  (x.1 * x.1, x.2.1 * x.2.1, x.2.2.1 * x.2.2.1, x.2.2.2 * x.2.2.2)

theorem frobT_tmul (x y : T8) : frobT (tmul x y) = tmul (frobT x) (frobT y) := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨e, f, g, h⟩ := y
  simp only [frobT, tmul, Prod.mk.injEq]
  exact ⟨by linear_combination (a * e * b * g) * gf8_two_eq_zero,
    by linear_combination (a * f * b * h) * gf8_two_eq_zero,
    by linear_combination (c * e * d * g) * gf8_two_eq_zero,
    by linear_combination (c * f * d * h) * gf8_two_eq_zero⟩

theorem tdet_frobT (x : T8) : tdet (frobT x) = tdet x * tdet x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [frobT, tdet]
  linear_combination (-(a * d * b * c)) * gf8_two_eq_zero

theorem frob_cube (t : GF8) : t * t * (t * t) * (t * t * (t * t)) = t := by
  revert t
  decide

@[expose] def frobF (x : G8) : G8 := ⟨frobT x.1, by rw [tdet_frobT, x.2, mul_one]⟩

theorem frobF_frobF_frobF (x : G8) : frobF (frobF (frobF x)) = x := by
  obtain ⟨⟨a, b, c, d⟩, hx⟩ := x
  apply Subtype.ext
  simp only [frobF, frobT, frob_cube]

@[expose] def frob : MulAut G8 where
  toFun := frobF
  invFun x := frobF (frobF x)
  left_inv := frobF_frobF_frobF
  right_inv := frobF_frobF_frobF
  map_mul' x y := Subtype.ext (frobT_tmul x.1 y.1)

theorem frob_not_inner : ∀ g : G8,
    ¬ (g * ga * g⁻¹ = frobF ga ∧ g * gb * g⁻¹ = frobF gb) ∧
      ¬ (g * ga * g⁻¹ = frobF (frobF ga) ∧ g * gb * g⁻¹ = frobF (frobF gb)) := by
  decide +kernel

theorem eq_one_of_commute : ∀ g : G8, g * ga = ga * g → g * gb = gb * g → g = 1 := by
  decide +kernel

theorem le_card_mulAut : 1512 ≤ Nat.card (MulAut G8) := by
  have : Finite (MulAut G8) := finite_mulAut
  have hinj : Function.Injective (MulAut.conj : G8 →* MulAut G8) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hc : ∀ h : G8, g * h * g⁻¹ = h := fun h => by
      have := congrArg (fun α : MulAut G8 => α h) (MonoidHom.mem_ker.mp hg)
      simpa using this
    have hc' : ∀ h : G8, g * h = h * g := fun h => by
      calc g * h = g * h * g⁻¹ * g := by group
        _ = h * g := by rw [hc h]
    exact Subgroup.mem_bot.mpr (eq_one_of_commute g (hc' ga) (hc' gb))
  have hInn : Nat.card (MulAut.conj : G8 →* MulAut G8).range = 504 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, card_G8]
  have hnot : ∀ g : G8, MulAut.conj g ≠ frob ∧ MulAut.conj g ≠ frob ^ 2 := by
    intro g
    obtain ⟨h1, h2⟩ := frob_not_inner g
    refine ⟨fun h => h1 ⟨?_, ?_⟩, fun h => h2 ⟨?_, ?_⟩⟩
    · rw [← MulAut.conj_apply, h]
      rfl
    · rw [← MulAut.conj_apply, h]
      rfl
    · rw [← MulAut.conj_apply, h]
      rfl
    · rw [← MulAut.conj_apply, h]
      rfl
  have hidx : 3 ≤ (MulAut.conj : G8 →* MulAut G8).range.index := by
    have h0 : (MulAut.conj : G8 →* MulAut G8).range.index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have h1 : (MulAut.conj : G8 →* MulAut G8).range.index ≠ 1 := by
      intro h
      obtain ⟨g, hg⟩ := (Subgroup.index_eq_one.mp h).symm ▸ Subgroup.mem_top frob
      exact (hnot g).1 hg
    have h2 : (MulAut.conj : G8 →* MulAut G8).range.index ≠ 2 := by
      intro h
      obtain ⟨g, hg⟩ := Subgroup.sq_mem_of_index_two h frob
      exact (hnot g).2 hg
    omega
  have := (MulAut.conj : G8 →* MulAut G8).range.card_mul_index
  rw [hInn] at this
  omega

theorem card_mulAut : Nat.card (MulAut G8) = 1512 :=
  le_antisymm card_mulAut_le le_card_mulAut

@[expose] def slEquiv : Matrix.SpecialLinearGroup (Fin 2) GF8 ≃* G8 where
  toFun A := ⟨((A : Matrix (Fin 2) (Fin 2) GF8) 0 0, (A : Matrix (Fin 2) (Fin 2) GF8) 0 1,
      (A : Matrix (Fin 2) (Fin 2) GF8) 1 0, (A : Matrix (Fin 2) (Fin 2) GF8) 1 1), by
    have h := A.2
    rw [Matrix.det_fin_two, gf8_sub_eq_add] at h
    exact h⟩
  invFun x := ⟨!![x.1.1, x.1.2.1; x.1.2.2.1, x.1.2.2.2], by
    rw [Matrix.det_fin_two_of, gf8_sub_eq_add]
    exact x.2⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv x := rfl
  map_mul' A B := by
    apply Subtype.ext
    simp only [val_mul, tmul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sl_center_eq_bot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) GF8) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr1 : r = 1 := by
    have hsq : ∀ s : GF8, s ^ 2 = 1 → s = 1 := by decide
    exact hsq r (by simpa using hr)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp [Matrix.one_apply]

theorem nonempty_equiv (K : Type) [Field K] [Finite K] (hK : Nat.card K = 8) :
    Nonempty (StatedProj (StatedSL 2 K) ≃* G8) := by
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card GF8 := by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl
  exact ⟨(projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcard)).trans
    (((QuotientGroup.quotientMulEquivOfEq sl_center_eq_bot).trans
      QuotientGroup.quotientBot).trans slEquiv))⟩

end L28Res

theorem l28AutFact_holds : L28AutFact := by
  intro K _ _ hK
  obtain ⟨e⟩ := L28Res.nonempty_equiv K hK
  rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv, L28Res.card_mulAut,
    L28Res.card_G8]

end F6

end CFSG.Quasithin
