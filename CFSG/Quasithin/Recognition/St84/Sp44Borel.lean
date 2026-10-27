module

public import CFSG.Quasithin.Background.F7TwoInvSp4OddTorus
public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4B
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Frob
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin.F112R.St84.Sp44

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2 uElt_inj uElt_mul_self uElt_zero_eq_one
  card_radicals radA1_inf_radA2 mem_antiUnipotentCenter_iff_central radA1_le_antiUnipotent
  radA2_le_antiUnipotent)
open CFSG.RankThree.PartOne.KCRootAxis
open CFSG.QuasithinUnique.Fin257.Sp4
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def B0 (F : Type) [Field F] [CharP F 2] : Subgroup (antiSp F) :=
  Subgroup.normalizer (antiUnipotent F : Set (antiSp F))

abbrev dTor (F : Type) [Field F] [CharP F 2] : Subgroup (antiSp F) :=
  CFSG.Quasithin.F7Two.antiTorus F

@[expose] def rootXa (F : Type) [Field F] [CharP F 2] : Subgroup (antiSp F) where
  carrier := {g | ∃ a : F, g = uElt a 0 0 0}
  one_mem' := ⟨0, uElt_zero_eq_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    rw [uElt_mul]
    congr 1 <;> ring
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [uElt_inv]
    congr 1 <;> ring

@[expose] def rootXb (F : Type) [Field F] [CharP F 2] : Subgroup (antiSp F) where
  carrier := {g | ∃ d : F, g = uElt 0 0 0 d}
  one_mem' := ⟨0, uElt_zero_eq_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    rw [uElt_mul]
    congr 1 <;> ring
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [uElt_inv]
    congr 1 <;> ring

theorem mem_dTor {x : antiSp F} : x ∈ dTor F ↔ ∃ s t : Fˣ, x = dSp s t := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.2, hp.symm⟩
  · rintro ⟨s, t, rfl⟩
    exact CFSG.Quasithin.F7Two.torElt_mem_antiTorus s t

theorem dSp_mem_dTor (s t : Fˣ) : dSp s t ∈ dTor F :=
  CFSG.Quasithin.F7Two.torElt_mem_antiTorus s t

theorem dSp_inj {s t s' t' : Fˣ} (h : dSp s t = (dSp s' t' : antiSp F)) : s = s' ∧ t = t' := by
  have h' := congrArg (fun x : antiSp F => glMat (x : GL (Fin 4) F)) h
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp [glMat_dSp, dSpMat] at h0 h1
  exact ⟨Units.ext h0, Units.ext h1⟩

theorem dTor_comm {a b : antiSp F} (ha : a ∈ dTor F) (hb : b ∈ dTor F) : a * b = b * a := by
  obtain ⟨s, t, rfl⟩ := mem_dTor.mp ha
  obtain ⟨s', t', rfl⟩ := mem_dTor.mp hb
  rw [dSp_mul, dSp_mul]
  congr 1 <;> exact mul_comm _ _

theorem dTor_le : dTor F ≤ B0 F := by
  intro x hx
  obtain ⟨s, t, rfl⟩ := mem_dTor.mp hx
  exact dSp_mem_normalizer s t

theorem card_dTor (hF : Nat.card F = 2 ^ 2) : Nat.card (dTor F) = 9 := by
  have hcard : Nat.card (Fˣ × Fˣ) = Nat.card (dTor F) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun p : Fˣ × Fˣ => (⟨dSp p.1 p.2, dSp_mem_dTor p.1 p.2⟩ : dTor F)) ⟨?_, ?_⟩)
    · intro p q h
      have h' : dSp p.1 p.2 = (dSp q.1 q.2 : antiSp F) := by
        simpa using congrArg (fun x : dTor F => (x : antiSp F)) h
      obtain ⟨h1, h2⟩ := dSp_inj h'
      exact Prod.ext h1 h2
    · rintro ⟨x, hx⟩
      obtain ⟨s, t, rfl⟩ := mem_dTor.mp hx
      exact ⟨(s, t), rfl⟩
  rw [← hcard, Nat.card_prod, Nat.card_units, hF]
  norm_num

theorem card_antiUnipotent (hF : Nat.card F = 2 ^ 2) : Nat.card (antiUnipotent F) = 2 ^ 8 := by
  have h := (card_radicals (K := F)).1
  rw [h, hF]
  norm_num

theorem card_radA1 (hF : Nat.card F = 2 ^ 2) : Nat.card (radA1 F) = 2 ^ 6 := by
  have h := (card_radicals (K := F)).2.1
  rw [h, hF]
  norm_num

theorem card_radA2 (hF : Nat.card F = 2 ^ 2) : Nat.card (radA2 F) = 2 ^ 6 := by
  have h := (card_radicals (K := F)).2.2.1
  rw [h, hF]
  norm_num

theorem card_antiUnipotentCenter (hF : Nat.card F = 2 ^ 2) :
    Nat.card (antiUnipotentCenter F) = 2 ^ 4 := by
  have h := (card_radicals (K := F)).2.2.2
  rw [h, hF]
  norm_num

theorem antiUnipotent_inf_dTor : antiUnipotent F ⊓ dTor F = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro x ⟨hxU, hxT⟩
  obtain ⟨s, t, rfl⟩ := mem_dTor.mp hxT
  have hd := ((mem_antiUnipotent_iff_upper (dSp s t)).mp hxU).2
  have h0 : (s : F) = 1 := by simpa [glMat_dSp, dSpMat] using hd 0
  have h1 : (t : F) = 1 := by simpa [glMat_dSp, dSpMat] using hd 1
  rw [show s = 1 from Units.ext h0, show t = 1 from Units.ext h1, dSp_one]
  exact Subgroup.mem_bot.mpr rfl

theorem card_B0 (hF : Nat.card F = 2 ^ 2) : Nat.card (B0 F) = 2 ^ 8 * 3 ^ 2 := by
  have hB : B0 F = antiUnipotent F ⊔ dTor F := by
    refine le_antisymm ?_ ?_
    · intro g hg
      obtain ⟨u, s, t, hu, rfl, -⟩ :=
        CFSG.Quasithin.SzN27.Sp4.exists_unip_dSp_of_mem_normalizer hg
      exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (dSp_mem_dTor s t))
    · refine sup_le ?_ dTor_le
      exact Subgroup.le_normalizer
  rw [hB]
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := antiUnipotent F) (B := dTor F) dTor_le
  rw [antiUnipotent_inf_dTor, card_antiUnipotent hF, card_dTor hF] at h
  have hbot : Nat.card (⊥ : Subgroup (antiSp F)) = 1 := by simp
  rw [hbot, mul_one] at h
  rw [h]
  norm_num

theorem rootU₁_le_antiUnipotentCenter : rootU₁ F ≤ antiUnipotentCenter F := by
  rintro _ ⟨b, rfl⟩
  exact ⟨b, 0, rfl⟩

theorem rootU₂_le_antiUnipotentCenter : rootU₂ F ≤ antiUnipotentCenter F := by
  rintro _ ⟨c, rfl⟩
  exact ⟨0, c, rfl⟩

theorem centralizer_dSp_diag (hF : Nat.card F = 2 ^ 2) {s : Fˣ} (hs : s ≠ 1) {x : antiSp F}
    (hx : x ∈ antiUnipotent F) (hc : dSp s s * x = x * dSp s s) : x ∈ rootXa F := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  have hconj : dSp s s * uElt a b c d * (dSp s s)⁻¹ = uElt a b c d := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [dSp_conj_uElt] at hconj
  obtain ⟨-, hb, hc', hd⟩ := uElt_inj hconj
  have hsq : (s : F) ^ 2 ≠ 1 := by
    intro h
    apply hs
    apply Units.ext
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact h1
    · rwa [CharTwo.neg_eq] at h1
  have hne : (s : F) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hsq
  have hb0 : b = 0 := by
    have h : ((s : F) ^ 2 - 1) * b = 0 := by linear_combination hb
    exact (mul_eq_zero.mp h).resolve_left hne
  have hc0 : c = 0 := by
    have h : ((s : F) ^ 2 - 1) * c = 0 := by linear_combination hc'
    exact (mul_eq_zero.mp h).resolve_left hne
  have hd0 : d = 0 := by
    have h : ((s : F) ^ 2 - 1) * d = 0 := by linear_combination hd
    exact (mul_eq_zero.mp h).resolve_left hne
  rw [hb0, hc0, hd0]
  exact ⟨a, rfl⟩

theorem centralizer_dSp_left (hF : Nat.card F = 2 ^ 2) {s : Fˣ} (hs : s ≠ 1) {x : antiSp F}
    (hx : x ∈ antiUnipotent F) (hc : dSp s 1 * x = x * dSp s 1) : x ∈ rootXb F := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  have hconj : dSp s 1 * uElt a b c d * (dSp s 1)⁻¹ = uElt a b c d := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [dSp_conj_uElt] at hconj
  simp only [Units.val_one, inv_one, mul_one, one_mul] at hconj
  obtain ⟨ha, hb, hc', -⟩ := uElt_inj hconj
  have hs1 : (s : F) - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hs (Units.ext h))
  have hsq1 : (s : F) ^ 2 ≠ 1 := by
    intro h
    apply hs
    apply Units.ext
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact h1
    · rwa [CharTwo.neg_eq] at h1
  have hs2 : (s : F) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hsq1
  have ha0 : a = 0 := by
    have h : ((s : F) - 1) * a = 0 := by linear_combination ha
    exact (mul_eq_zero.mp h).resolve_left hs1
  have hb0 : b = 0 := by
    have h : ((s : F) - 1) * b = 0 := by linear_combination hb
    exact (mul_eq_zero.mp h).resolve_left hs1
  have hc0 : c = 0 := by
    have h : ((s : F) ^ 2 - 1) * c = 0 := by linear_combination hc'
    exact (mul_eq_zero.mp h).resolve_left hs2
  rw [ha0, hb0, hc0]
  exact ⟨d, rfl⟩

theorem dSp_mem_Kb_iff (hF : Nat.card F = 2 ^ 2) (s t : Fˣ) :
    (∀ x ∈ radA1 F, dSp s t * x * (dSp s t)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F) ↔ t = 1 := by
  constructor
  · intro H
    have h1 : (uElt (0 : F) 0 0 1 : antiSp F) ∈ radA1 F := ⟨0, 0, 1, rfl⟩
    have hmem := H _ h1
    have hxinv : (uElt (0 : F) 0 0 1 : antiSp F)⁻¹ = uElt 0 0 0 1 := by
      rw [uElt_inv]
      congr 1 <;> ring
    have hcomm : dSp s t * uElt 0 0 0 1 * (dSp s t)⁻¹ * (uElt 0 0 0 1)⁻¹ =
        uElt 0 0 0 ((t : F) ^ 2 + 1) := by
      rw [dSp_conj_uElt, hxinv, uElt_mul]
      congr 1 <;> ring1
    rw [hcomm] at hmem
    obtain ⟨B, C, hBC⟩ := hmem
    have hd : (t : F) ^ 2 + 1 = 0 := (uElt_inj hBC).2.2.2
    have ht2 : (t : F) ^ 2 = 1 := CharTwo.add_eq_zero.mp hd
    apply Units.ext
    rcases sq_eq_one_iff.mp ht2 with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  · intro ht
    subst ht
    intro x hx
    obtain ⟨b, c, d, rfl⟩ := hx
    have hxinv : (uElt (0 : F) b c d : antiSp F)⁻¹ = uElt 0 b c d := by
      rw [uElt_inv]
      congr 1 <;> ring
    have hcomm : dSp s 1 * uElt 0 b c d * (dSp s 1)⁻¹ * (uElt 0 b c d)⁻¹ =
        uElt 0 ((1 + (s : F)) * b) ((1 + (s : F) ^ 2) * c) 0 := by
      rw [dSp_conj_uElt, hxinv, uElt_mul]
      simp only [Units.val_one, Units.val_inv_eq_inv_val, inv_one, mul_one, one_mul, pow_one]
      congr 1 <;> (ring_nf; try simp [CharTwo.two_eq_zero])
    rw [hcomm]
    exact ⟨(1 + (s : F)) * b, (1 + (s : F) ^ 2) * c, rfl⟩

theorem dSp_mem_Ka_iff (hF : Nat.card F = 2 ^ 2) (s t : Fˣ) :
    (∀ x ∈ radA2 F, dSp s t * x * (dSp s t)⁻¹ * x⁻¹ ∈ antiUnipotentCenter F) ↔ s = t := by
  constructor
  · intro H
    have h1 : (uElt (1 : F) 0 0 0 : antiSp F) ∈ radA2 F := ⟨1, 0, 0, rfl⟩
    have hmem := H _ h1
    have hxinv : (uElt (1 : F) 0 0 0 : antiSp F)⁻¹ = uElt 1 0 0 0 := by
      rw [uElt_inv]
      congr 1 <;> ring
    have hcomm : dSp s t * uElt 1 0 0 0 * (dSp s t)⁻¹ * (uElt 1 0 0 0)⁻¹ =
        uElt ((s : F) * ((t⁻¹ : Fˣ) : F) + 1) 0 0 0 := by
      rw [dSp_conj_uElt, hxinv, uElt_mul]
      simp
    rw [hcomm] at hmem
    obtain ⟨B, C, hBC⟩ := hmem
    have ha : (s : F) * ((t⁻¹ : Fˣ) : F) + 1 = 0 := (uElt_inj hBC).1
    have hst : (s : F) * ((t⁻¹ : Fˣ) : F) = 1 := CharTwo.add_eq_zero.mp ha
    have hu : s * t⁻¹ = 1 := Units.ext (by simpa using hst)
    exact mul_inv_eq_one.mp hu
  · intro hst
    subst hst
    intro x hx
    obtain ⟨a, b, c, rfl⟩ := hx
    have hxinv : (uElt a b c (0 : F) : antiSp F)⁻¹ = uElt a b c 0 := by
      rw [uElt_inv]
      congr 1 <;> ring
    have hcomm : dSp s s * uElt a b c 0 * (dSp s s)⁻¹ * (uElt a b c 0)⁻¹ =
        uElt 0 ((1 + (s : F) ^ 2) * b) ((1 + (s : F) ^ 2) * (c + a * b)) 0 := by
      rw [dSp_conj_uElt, hxinv, uElt_mul]
      simp only [Units.val_one, Units.val_inv_eq_inv_val, inv_one, mul_one, one_mul, pow_one]
      rw [mul_inv_cancel₀ (Units.ne_zero s), one_mul]
      congr 1 <;> (ring_nf; try simp [CharTwo.two_eq_zero])
    rw [hcomm]
    exact ⟨_, _, rfl⟩

theorem dSp_mem_K2ab_iff (hF : Nat.card F = 2 ^ 2) (s t : Fˣ) :
    (∀ x ∈ rootU₂ F, dSp s t * x * (dSp s t)⁻¹ = x) ↔ s = 1 := by
  constructor
  · intro H
    have h1 : (uElt (0 : F) 0 1 0 : antiSp F) ∈ rootU₂ F := ⟨1, rfl⟩
    have hmem := H _ h1
    rw [dSp_conj_uElt] at hmem
    have hc : (s : F) ^ 2 = 1 := by
      have := (uElt_inj hmem).2.2.1
      simpa using this
    apply Units.ext
    rcases sq_eq_one_iff.mp hc with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  · intro hs
    subst hs
    intro x hx
    obtain ⟨c, rfl⟩ := hx
    rw [dSp_conj_uElt]
    norm_num

theorem card_rootU₁ (hF : Nat.card F = 2 ^ 2) : Nat.card (rootU₁ F) = 4 := by
  have h : Nat.card F = Nat.card (rootU₁ F) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun b : F => (⟨uElt 0 b 0 0, ⟨b, rfl⟩⟩ : rootU₁ F)) ⟨?_, ?_⟩)
    · intro a b h
      exact (uElt_inj (congrArg Subtype.val h)).2.1
    · rintro ⟨x, b, rfl⟩
      exact ⟨b, rfl⟩
  rw [← h, hF]
  norm_num

theorem card_rootU₂ (hF : Nat.card F = 2 ^ 2) : Nat.card (rootU₂ F) = 4 := by
  have h : Nat.card F = Nat.card (rootU₂ F) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun c : F => (⟨uElt 0 0 c 0, ⟨c, rfl⟩⟩ : rootU₂ F)) ⟨?_, ?_⟩)
    · intro a b h
      exact (uElt_inj (congrArg Subtype.val h)).2.2.1
    · rintro ⟨x, c, rfl⟩
      exact ⟨c, rfl⟩
  rw [← h, hF]
  norm_num

theorem eq_rootU_of_dTor_normal (hF : Nat.card F = 2 ^ 2) {W : Subgroup (antiSp F)}
    (hWZ : W ≤ antiUnipotentCenter F) (hWc : Nat.card W = 4)
    (hWn : dTor F ≤ Subgroup.normalizer (W : Set (antiSp F))) :
    W = rootU₁ F ∨ W = rootU₂ F := by
  classical
  have hq : Nat.card F = 4 := by rw [hF]; norm_num
  have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hq]
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : ∀ u : F, u ^ 2 = 1 ↔ u = 1 := by
    intro u
    rw [sq_eq_one_iff]
    constructor
    · rintro (h | h)
      · exact h
      · rwa [CharTwo.neg_eq] at h
    · intro h
      exact Or.inl h
  have hsqU : ∀ u : Fˣ, u ^ 2 = 1 ↔ u = 1 := by
    intro u
    constructor
    · intro h
      apply Units.ext
      apply (hsq (u : F)).mp
      simpa using congrArg (fun x : Fˣ => (x : F)) h
    · intro h
      rw [h, one_pow]
  haveI : Fintype F := Fintype.ofFinite F
  have hone_lt : 1 < Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, hcu]
    norm_num
  obtain ⟨t0, ht0⟩ := Fintype.exists_ne_of_one_lt_card hone_lt (1 : Fˣ)
  obtain ⟨s0, hs0⟩ := Fintype.exists_ne_of_one_lt_card hone_lt (1 : Fˣ)
  have hadd : ∀ u : Fˣ, u ≠ 1 → (1 : F) + (u : F) ≠ 0 := by
    intro u hu h
    apply hu
    apply Units.ext
    exact (CharTwo.add_eq_zero.mp h).symm
  have hsurj : Function.Surjective (fun u : Fˣ => u ^ 2) := by
    rw [← Finite.injective_iff_surjective]
    intro a b hab
    have hab' : a ^ 2 = b ^ 2 := hab
    have h : (a * b⁻¹) ^ 2 = 1 := by
      rw [mul_pow, hab', inv_pow]
      exact mul_inv_cancel _
    have h' := (hsqU (a * b⁻¹)).mp h
    calc a = a * b⁻¹ * b := by group
      _ = 1 * b := by rw [h']
      _ = b := one_mul b
  have hscale_b : ∀ (l : Fˣ) (B : F),
      dSp l 1 * uElt 0 B 0 0 * (dSp l 1)⁻¹ = uElt 0 ((l : F) * B) 0 0 := by
    intro l B
    rw [dSp_conj_uElt]
    simp
  have hscale_c : ∀ (l : Fˣ) (C : F),
      dSp l 1 * uElt 0 0 C 0 * (dSp l 1)⁻¹ = uElt 0 0 ((l : F) ^ 2 * C) 0 := by
    intro l C
    rw [dSp_conj_uElt]
    simp
  have hsplit : ∀ w : antiSp F, w ∈ W → ∃ b c : F,
      w = uElt 0 b 0 0 * uElt 0 0 c 0 ∧ uElt 0 b 0 0 ∈ W ∧ uElt 0 0 c 0 ∈ W := by
    intro w hw
    obtain ⟨b, c, rfl⟩ := hWZ hw
    have hbW : uElt 0 b 0 0 ∈ W := by
      have hconj : dSp 1 t0 * uElt 0 b c 0 * (dSp 1 t0)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWn (dSp_mem_dTor 1 t0)) _).mp hw
      have hconj_eq : dSp 1 t0 * uElt 0 b c 0 * (dSp 1 t0)⁻¹ =
          uElt 0 ((t0 : F) * b) c 0 := by
        rw [dSp_conj_uElt]
        simp
      have hprod : uElt 0 b c 0 * uElt 0 ((t0 : F) * b) c 0 ∈ W :=
        W.mul_mem hw (hconj_eq ▸ hconj)
      have hprod_eq : uElt 0 b c 0 * uElt 0 ((t0 : F) * b) c 0 =
          uElt 0 ((1 + (t0 : F)) * b) 0 0 := by
        rw [uElt_mul]
        congr 1 <;> (ring_nf; try simp [htwo])
      have hne : (1 : F) + (t0 : F) ≠ 0 := hadd t0 ht0
      let l : Fˣ := (Units.mk0 ((1 : F) + (t0 : F)) hne)⁻¹
      have hl : (l : F) * ((1 : F) + (t0 : F)) = 1 := by
        change (((1 : F) + (t0 : F))⁻¹) * ((1 : F) + (t0 : F)) = 1
        exact inv_mul_cancel₀ hne
      have hmem : dSp l 1 * uElt 0 ((1 + (t0 : F)) * b) 0 0 * (dSp l 1)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWn (dSp_mem_dTor l 1)) _).mp
          (hprod_eq ▸ hprod)
      have heq : dSp l 1 * uElt 0 ((1 + (t0 : F)) * b) 0 0 * (dSp l 1)⁻¹ =
          uElt 0 b 0 0 := by
        rw [hscale_b]
        congr 1
        calc (l : F) * ((1 + (t0 : F)) * b)
            = ((l : F) * ((1 : F) + (t0 : F))) * b := by ring
          _ = 1 * b := by rw [hl]
          _ = b := one_mul b
      exact heq ▸ hmem
    have hcW : uElt 0 0 c 0 ∈ W := by
      have hconj : dSp s0 s0⁻¹ * uElt 0 b c 0 * (dSp s0 s0⁻¹)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWn (dSp_mem_dTor s0 s0⁻¹)) _).mp hw
      have hconj_eq : dSp s0 s0⁻¹ * uElt 0 b c 0 * (dSp s0 s0⁻¹)⁻¹ =
          uElt 0 b ((s0 : F) ^ 2 * c) 0 := by
        rw [dSp_conj_uElt]
        simp only [Units.val_inv_eq_inv_val]
        rw [mul_inv_cancel₀ (Units.ne_zero s0), one_mul, inv_inv]
        simp
      have hprod : uElt 0 b c 0 * uElt 0 b ((s0 : F) ^ 2 * c) 0 ∈ W :=
        W.mul_mem hw (hconj_eq ▸ hconj)
      have hprod_eq : uElt 0 b c 0 * uElt 0 b ((s0 : F) ^ 2 * c) 0 =
          uElt 0 0 ((1 + (s0 : F) ^ 2) * c) 0 := by
        rw [uElt_mul]
        congr 1 <;> (ring_nf; try simp [htwo])
      have hne : (1 : F) + (s0 : F) ^ 2 ≠ 0 := by
        intro h
        have h1 : (s0 : F) ^ 2 = 1 := (CharTwo.add_eq_zero.mp h).symm
        exact hs0 ((hsqU s0).mp (Units.ext h1))
      let mu : Fˣ := (Units.mk0 ((1 : F) + (s0 : F) ^ 2) hne)⁻¹
      obtain ⟨l, hl2⟩ := hsurj mu
      have hl : (l : F) ^ 2 * ((1 : F) + (s0 : F) ^ 2) = 1 := by
        have hl2' : l ^ 2 = mu := hl2
        have h1 : (l : F) ^ 2 = (mu : F) := by
          rw [← Units.val_pow_eq_pow_val, hl2']
        rw [h1, Units.val_inv_eq_inv_val]
        change ((1 : F) + (s0 : F) ^ 2)⁻¹ * ((1 : F) + (s0 : F) ^ 2) = 1
        exact inv_mul_cancel₀ hne
      have hmem : dSp l 1 * uElt 0 0 ((1 + (s0 : F) ^ 2) * c) 0 * (dSp l 1)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWn (dSp_mem_dTor l 1)) _).mp
          (hprod_eq ▸ hprod)
      have heq : dSp l 1 * uElt 0 0 ((1 + (s0 : F) ^ 2) * c) 0 * (dSp l 1)⁻¹ =
          uElt 0 0 c 0 := by
        rw [hscale_c]
        congr 1
        calc (l : F) ^ 2 * ((1 + (s0 : F) ^ 2) * c)
            = ((l : F) ^ 2 * ((1 : F) + (s0 : F) ^ 2)) * c := by ring
          _ = 1 * c := by rw [hl]
          _ = c := one_mul c
      exact heq ▸ hmem
    have hdecomp : uElt 0 b c 0 = uElt 0 b 0 0 * uElt 0 0 c 0 := by
      rw [uElt_mul]
      congr 1 <;> ring
    exact ⟨b, c, hdecomp, hbW, hcW⟩
  have hV1 : W ⊓ rootU₁ F = ⊥ ∨ W ⊓ rootU₁ F = rootU₁ F := by
    by_cases hbot : W ⊓ rootU₁ F = ⊥
    · exact Or.inl hbot
    · right
      have hne : ∃ x ∈ W ⊓ rootU₁ F, x ≠ 1 := by
        by_contra h
        apply hbot
        rw [eq_bot_iff]
        intro x hx
        by_contra hx1
        exact h ⟨x, hx, hx1⟩
      obtain ⟨x, hx, hx1⟩ := hne
      obtain ⟨hxW, hxU⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨b, rfl⟩ := hxU
      have hb : b ≠ 0 := by
        intro hb
        exact hx1 (by rw [hb]; exact uElt_zero_eq_one)
      have hle : rootU₁ F ≤ W := by
        rintro _ ⟨y, rfl⟩
        rcases eq_or_ne y 0 with hy | hy
        · rw [hy, uElt_zero_eq_one]
          exact W.one_mem
        · let l : Fˣ := Units.mk0 (y / b) (div_ne_zero hy hb)
          have hl : (l : F) * b = y := by
            change (y / b) * b = y
            exact div_mul_cancel₀ y hb
          have hmem : dSp l 1 * uElt 0 b 0 0 * (dSp l 1)⁻¹ ∈ W :=
            (Subgroup.mem_normalizer_iff.mp (hWn (dSp_mem_dTor l 1)) _).mp hxW
          rw [hscale_b l b, hl] at hmem
          exact hmem
      exact le_antisymm inf_le_right (le_inf hle le_rfl)
  rcases hV1 with h1 | h1
  · right
    have hWsub : W ≤ rootU₂ F := by
      intro w hw
      obtain ⟨b, c, hwc, hbW, hcW⟩ := hsplit w hw
      have hb1 : uElt 0 b 0 0 = 1 := by
        have hmem : uElt 0 b 0 0 ∈ W ⊓ rootU₁ F := ⟨hbW, ⟨b, rfl⟩⟩
        rw [h1] at hmem
        exact Subgroup.mem_bot.mp hmem
      rw [hwc, hb1, one_mul]
      exact ⟨c, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hWsub (by rw [card_rootU₂ hF, hWc])
  · left
    have hle : rootU₁ F ≤ W := by
      intro x hx
      have : x ∈ W ⊓ rootU₁ F := by rw [h1]; exact hx
      exact this.1
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hWc, card_rootU₁ hF])).symm

theorem conj_mem_antiUnipotentCenter {u z : antiSp F} (hu : u ∈ antiUnipotent F)
    (hz : z ∈ antiUnipotentCenter F) : u * z * u⁻¹ ∈ antiUnipotentCenter F := by
  have hcomm : u * z = z * u := (antiUnipotentCenter_comm hz hu).symm
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact hz

theorem conj_mem_rootU₁ {u y : antiSp F} (hu : u ∈ antiUnipotent F) (hy : y ∈ rootU₁ F) :
    u * y * u⁻¹ = y := by
  have hz : y ∈ antiUnipotentCenter F := rootU₁_le_antiUnipotentCenter hy
  have hcomm : u * y = y * u := (antiUnipotentCenter_comm hz hu).symm
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_mem_rootU₂ {u y : antiSp F} (hu : u ∈ antiUnipotent F) (hy : y ∈ rootU₂ F) :
    u * y * u⁻¹ = y := by
  have hz : y ∈ antiUnipotentCenter F := rootU₂_le_antiUnipotentCenter hy
  have hcomm : u * y = y * u := (antiUnipotentCenter_comm hz hu).symm
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem dTor_conj_mem_rootU₁ {h x : antiSp F} (hh : h ∈ dTor F) (hx : x ∈ rootU₁ F) :
    h * x * h⁻¹ ∈ rootU₁ F := by
  obtain ⟨s, t, rfl⟩ := mem_dTor.mp hh
  obtain ⟨b, rfl⟩ := hx
  rw [dSp_conj_uElt]
  refine ⟨(s : F) * (t : F) * b, ?_⟩
  congr 1 <;> ring

theorem dTor_conj_mem_rootU₂ {h x : antiSp F} (hh : h ∈ dTor F) (hx : x ∈ rootU₂ F) :
    h * x * h⁻¹ ∈ rootU₂ F := by
  obtain ⟨s, t, rfl⟩ := mem_dTor.mp hh
  obtain ⟨c, rfl⟩ := hx
  rw [dSp_conj_uElt]
  refine ⟨(s : F) ^ 2 * c, ?_⟩
  congr 1 <;> ring

theorem B0_conj_mem_antiUnipotentCenter {g z : antiSp F} (hg : g ∈ B0 F)
    (hz : z ∈ antiUnipotentCenter F) : g * z * g⁻¹ ∈ antiUnipotentCenter F := by
  obtain ⟨u, s, t, hu, rfl, -, -⟩ :=
    CFSG.Quasithin.SzN27.Sp4.exists_unip_dSp_of_mem_normalizer hg
  obtain ⟨b, c, rfl⟩ := hz
  have h2 : dSp s t * uElt 0 b c 0 * (dSp s t)⁻¹ ∈ antiUnipotentCenter F := by
    rw [dSp_conj_uElt]
    refine ⟨(s : F) * (t : F) * b, (s : F) ^ 2 * c, ?_⟩
    congr 1 <;> ring
  have he : (u * dSp s t) * uElt 0 b c 0 * (u * dSp s t)⁻¹ =
      u * (dSp s t * uElt 0 b c 0 * (dSp s t)⁻¹) * u⁻¹ := by group
  rw [he]
  exact conj_mem_antiUnipotentCenter hu h2

theorem B0_conj_mem_rootU₁ {g x : antiSp F} (hg : g ∈ B0 F) (hx : x ∈ rootU₁ F) :
    g * x * g⁻¹ ∈ rootU₁ F := by
  obtain ⟨u, s, t, hu, rfl, -, -⟩ :=
    CFSG.Quasithin.SzN27.Sp4.exists_unip_dSp_of_mem_normalizer hg
  have h2 : dSp s t * x * (dSp s t)⁻¹ ∈ rootU₁ F :=
    dTor_conj_mem_rootU₁ (dSp_mem_dTor s t) hx
  have h3 : u * (dSp s t * x * (dSp s t)⁻¹) * u⁻¹ = dSp s t * x * (dSp s t)⁻¹ :=
    conj_mem_rootU₁ hu h2
  have he : (u * dSp s t) * x * (u * dSp s t)⁻¹ =
      u * (dSp s t * x * (dSp s t)⁻¹) * u⁻¹ := by group
  rw [he, h3]
  exact h2

theorem B0_conj_mem_rootU₂ {g x : antiSp F} (hg : g ∈ B0 F) (hx : x ∈ rootU₂ F) :
    g * x * g⁻¹ ∈ rootU₂ F := by
  obtain ⟨u, s, t, hu, rfl, -, -⟩ :=
    CFSG.Quasithin.SzN27.Sp4.exists_unip_dSp_of_mem_normalizer hg
  have h2 : dSp s t * x * (dSp s t)⁻¹ ∈ rootU₂ F :=
    dTor_conj_mem_rootU₂ (dSp_mem_dTor s t) hx
  have h3 : u * (dSp s t * x * (dSp s t)⁻¹) * u⁻¹ = dSp s t * x * (dSp s t)⁻¹ :=
    conj_mem_rootU₂ hu h2
  have he : (u * dSp s t) * x * (u * dSp s t)⁻¹ =
      u * (dSp s t * x * (dSp s t)⁻¹) * u⁻¹ := by group
  rw [he, h3]
  exact h2

theorem B0_le_normalizer_antiUnipotentCenter :
    B0 F ≤ Subgroup.normalizer (antiUnipotentCenter F : Set (antiSp F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact B0_conj_mem_antiUnipotentCenter hg
  · intro hz
    have h := B0_conj_mem_antiUnipotentCenter ((B0 F).inv_mem hg) hz
    have he : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
    rwa [he] at h

theorem B0_le_normalizer_rootU₁ :
    B0 F ≤ Subgroup.normalizer (rootU₁ F : Set (antiSp F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact B0_conj_mem_rootU₁ hg
  · intro hz
    have h := B0_conj_mem_rootU₁ ((B0 F).inv_mem hg) hz
    have he : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
    rwa [he] at h

theorem B0_le_normalizer_rootU₂ :
    B0 F ≤ Subgroup.normalizer (rootU₂ F : Set (antiSp F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact B0_conj_mem_rootU₂ hg
  · intro hz
    have h := B0_conj_mem_rootU₂ ((B0 F).inv_mem hg) hz
    have he : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
    rwa [he] at h

theorem B0_le_normalizer_radA1 :
    B0 F ≤ Subgroup.normalizer (radA1 F : Set (antiSp F)) :=
  normalizer_U_le_normalizer_radA1

theorem B0_le_normalizer_radA2 :
    B0 F ≤ Subgroup.normalizer (radA2 F : Set (antiSp F)) :=
  normalizer_U_le_normalizer_radA2

theorem antiUnipotentCenter_normal :
    ((antiUnipotentCenter F).subgroupOf (B0 F)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (antiUnipotentCenter_le.trans Subgroup.le_normalizer)).mpr
    B0_le_normalizer_antiUnipotentCenter

theorem rootU₁_normal : ((rootU₁ F).subgroupOf (B0 F)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (rootU₁_le_antiUnipotentCenter.trans (antiUnipotentCenter_le.trans Subgroup.le_normalizer))).mpr
    B0_le_normalizer_rootU₁

theorem rootU₂_normal : ((rootU₂ F).subgroupOf (B0 F)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (rootU₂_le_antiUnipotentCenter.trans (antiUnipotentCenter_le.trans Subgroup.le_normalizer))).mpr
    B0_le_normalizer_rootU₂

theorem radA1_normal : ((radA1 F).subgroupOf (B0 F)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((radA1_le_antiUnipotent (K := F)).trans Subgroup.le_normalizer)).mpr B0_le_normalizer_radA1

theorem radA2_normal : ((radA2 F).subgroupOf (B0 F)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((radA2_le_antiUnipotent (K := F)).trans Subgroup.le_normalizer)).mpr B0_le_normalizer_radA2

theorem B0_le_closure (hF : Nat.card F = 2 ^ 2) :
    B0 F ≤ Subgroup.closure ((rootXa F : Set (antiSp F)) ∪ rootXb F ∪ dTor F) := by
  classical
  have hq : Nat.card F = 4 := by rw [hF]; norm_num
  have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hq]
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  haveI : Fintype F := Fintype.ofFinite F
  have h1lt : 1 < Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, hcu]
    norm_num
  obtain ⟨ω, hω1⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : Fˣ)
  have hω3 : ω ^ 3 = 1 := by
    have := pow_card_eq_one' (x := ω)
    rwa [hcu] at this
  have hωrel : (ω : F) ^ 2 + (ω : F) + 1 = 0 := by
    have h : ((ω : F) - 1) * ((ω : F) ^ 2 + (ω : F) + 1) = 0 := by
      have h3 : (ω : F) ^ 3 = 1 := by
        simpa using congrArg (fun x : Fˣ => (x : F)) hω3
      have hring : ((ω : F) - 1) * ((ω : F) ^ 2 + (ω : F) + 1) = (ω : F) ^ 3 - 1 := by
        ring
      rw [hring, h3, sub_self]
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (Units.ext (sub_eq_zero.mp h)) hω1
    · exact h
  have hωsum : (ω : F) ^ 2 + (ω : F) = 1 := CharTwo.add_eq_zero.mp hωrel
  let V := Subgroup.closure ((rootXa F : Set (antiSp F)) ∪ rootXb F ∪ dTor F)
  have hxa : ∀ a : F, uElt a 0 0 0 ∈ V := fun a =>
    Subgroup.subset_closure (Or.inl (Or.inl ⟨a, rfl⟩))
  have hxb : ∀ d : F, uElt 0 0 0 d ∈ V := fun d =>
    Subgroup.subset_closure (Or.inl (Or.inr ⟨d, rfl⟩))
  have hT : ∀ s t : Fˣ, dSp s t ∈ V := fun s t =>
    Subgroup.subset_closure (Or.inr (dSp_mem_dTor s t))
  have hcomm_mem : ∀ α δ : F, uElt 0 (α * δ) (α ^ 2 * δ) 0 ∈ V := by
    intro α δ
    have hx := hxa α
    have hy := hxb δ
    have hxinv : (uElt α 0 0 0 : antiSp F)⁻¹ ∈ V := V.inv_mem hx
    have hyinv : (uElt 0 0 0 δ : antiSp F)⁻¹ ∈ V := V.inv_mem hy
    have heq : uElt α 0 0 0 * uElt 0 0 0 δ * (uElt α 0 0 0)⁻¹ * (uElt 0 0 0 δ)⁻¹ =
        uElt 0 (α * δ) (α ^ 2 * δ) 0 := by
      have hxinv' : (uElt α 0 0 0 : antiSp F)⁻¹ = uElt α 0 0 0 := by
        rw [uElt_inv]
        congr 1 <;> ring
      have hyinv' : (uElt 0 0 0 δ : antiSp F)⁻¹ = uElt 0 0 0 δ := by
        rw [uElt_inv]
        congr 1 <;> ring
      rw [hxinv', hyinv']
      have hxy : uElt α 0 0 0 * uElt 0 0 0 δ = uElt α (α * δ) 0 δ := by
        rw [uElt_mul]
        congr 1 <;> ring
      calc uElt α 0 0 0 * uElt 0 0 0 δ * uElt α 0 0 0 * uElt 0 0 0 δ
          = (uElt α 0 0 0 * uElt 0 0 0 δ) * (uElt α 0 0 0 * uElt 0 0 0 δ) := by group
        _ = (uElt α (α * δ) 0 δ) * (uElt α (α * δ) 0 δ) := by rw [hxy]
        _ = uElt 0 (α * δ) (α ^ 2 * δ) 0 := by
          rw [uElt_mul_self]
    rw [← heq]
    exact V.mul_mem (V.mul_mem (V.mul_mem hx hy) hxinv) hyinv
  have hU1 : ∀ b : F, uElt 0 b 0 0 ∈ V := by
    intro b
    have h1 : uElt 0 ((ω : F) ^ 2 * b) ((ω : F) ^ 2 * b) 0 ∈ V := by
      simpa using hcomm_mem 1 (ω ^ 2 * b)
    have h2 : uElt 0 ((ω : F) * b) ((ω : F) ^ 2 * b) 0 ∈ V := by
      simpa using hcomm_mem ω b
    have hprod : uElt 0 ((ω : F) ^ 2 * b) ((ω : F) ^ 2 * b) 0 *
        uElt 0 ((ω : F) * b) ((ω : F) ^ 2 * b) 0 = uElt 0 b 0 0 := by
      rw [uElt_mul]
      simp only [zero_mul, mul_zero, add_zero]
      rw [show (ω : F) ^ 2 * b + (ω : F) * b = b by
        calc (ω : F) ^ 2 * b + (ω : F) * b = ((ω : F) ^ 2 + (ω : F)) * b := by ring
          _ = 1 * b := by rw [hωsum]
          _ = b := one_mul b]
      rw [show (ω : F) ^ 2 * b + (ω : F) ^ 2 * b = 0 by
        linear_combination ((ω : F) ^ 2 * b) * htwo]
    rw [← hprod]
    exact V.mul_mem h1 h2
  have hU2 : ∀ c : F, uElt 0 0 c 0 ∈ V := by
    intro c
    have h1 : uElt 0 ((ω : F) * c) ((ω : F) * c) 0 ∈ V := by
      simpa using hcomm_mem 1 (ω * c)
    have h2 : uElt 0 ((ω : F) * c) ((ω : F) ^ 2 * c) 0 ∈ V := by
      simpa using hcomm_mem ω c
    have hprod : uElt 0 ((ω : F) * c) ((ω : F) * c) 0 *
        uElt 0 ((ω : F) * c) ((ω : F) ^ 2 * c) 0 = uElt 0 0 c 0 := by
      rw [uElt_mul]
      simp only [zero_mul, mul_zero, add_zero]
      rw [show (ω : F) * c + (ω : F) * c = 0 by
        linear_combination ((ω : F) * c) * htwo]
      rw [show (ω : F) * c + (ω : F) ^ 2 * c = c by
        calc (ω : F) * c + (ω : F) ^ 2 * c = ((ω : F) + (ω : F) ^ 2) * c := by ring
          _ = 1 * c := by rw [add_comm, hωsum]
          _ = c := one_mul c]
    rw [← hprod]
    exact V.mul_mem h1 h2
  have hZ : antiUnipotentCenter F ≤ V := by
    rintro _ ⟨b, c, rfl⟩
    have hb := hU1 b
    have hc := hU2 c
    have hprod : uElt 0 b 0 0 * uElt 0 0 c 0 = uElt 0 b c 0 := by
      rw [uElt_mul]
      congr 1 <;> ring
    rw [← hprod]
    exact V.mul_mem hb hc
  intro g hg
  obtain ⟨u, s, t, hu, rfl, -, -⟩ :=
    CFSG.Quasithin.SzN27.Sp4.exists_unip_dSp_of_mem_normalizer hg
  obtain ⟨a, b, c, d, rfl⟩ := hu
  have hfac : uElt a b c d =
      uElt a 0 0 0 * uElt 0 0 0 d * uElt 0 (b + a * d) (c + a * (b + a * d)) 0 := by
    have h1 : uElt a 0 0 0 * uElt 0 0 0 d = uElt a (a * d) 0 d := by
      rw [uElt_mul]
      congr 1 <;> ring
    have h2 : uElt a (a * d) 0 d * uElt 0 (b + a * d) (c + a * (b + a * d)) 0 =
        uElt a b c d := by
      rw [uElt_mul]
      congr 1 <;> (ring_nf; try simp [htwo])
    calc uElt a b c d
        = uElt a (a * d) 0 d * uElt 0 (b + a * d) (c + a * (b + a * d)) 0 := h2.symm
      _ = (uElt a 0 0 0 * uElt 0 0 0 d) *
            uElt 0 (b + a * d) (c + a * (b + a * d)) 0 := by rw [← h1]
      _ = uElt a 0 0 0 * uElt 0 0 0 d *
            uElt 0 (b + a * d) (c + a * (b + a * d)) 0 := rfl
  rw [hfac]
  exact V.mul_mem (V.mul_mem (V.mul_mem (hxa a) (hxb d)) (hZ ⟨_, _, rfl⟩)) (hT s t)

theorem rootXa_le_antiUnipotent : rootXa F ≤ antiUnipotent F := by
  rintro _ ⟨a, rfl⟩
  exact ⟨a, 0, 0, 0, rfl⟩

theorem rootXb_le_antiUnipotent : rootXb F ≤ antiUnipotent F := by
  rintro _ ⟨d, rfl⟩
  exact ⟨0, 0, 0, d, rfl⟩

theorem rootXa_comm_dSp (s : Fˣ) {x : antiSp F} (hx : x ∈ rootXa F) :
    dSp s s * x = x * dSp s s := by
  obtain ⟨a, rfl⟩ := hx
  have h : dSp s s * uElt a 0 0 0 * (dSp s s)⁻¹ = uElt a 0 0 0 := by
    rw [dSp_conj_uElt]
    simp
  calc dSp s s * uElt a 0 0 0
      = (dSp s s * uElt a 0 0 0 * (dSp s s)⁻¹) * dSp s s := by group
    _ = uElt a 0 0 0 * dSp s s := by rw [h]

theorem rootXb_comm_dSp_left (s : Fˣ) {x : antiSp F} (hx : x ∈ rootXb F) :
    dSp s 1 * x = x * dSp s 1 := by
  obtain ⟨d, rfl⟩ := hx
  have h : dSp s 1 * uElt 0 0 0 d * (dSp s 1)⁻¹ = uElt 0 0 0 d := by
    rw [dSp_conj_uElt]
    simp
  calc dSp s 1 * uElt 0 0 0 d
      = (dSp s 1 * uElt 0 0 0 d * (dSp s 1)⁻¹) * dSp s 1 := by group
    _ = uElt 0 0 0 d * dSp s 1 := by rw [h]

theorem frobAut_pow_dSp (j : ℕ) (s t : Fˣ) :
    (frobAut F ^ j) (dSp s t) = dSp (s ^ 2 ^ j) (t ^ 2 ^ j) := by
  apply mat_ext
  rw [CFSG.Quasithin.H13.F431.SpOut2.mat_frobAut_pow]
  show (dSpMat s t).map (fun x => x ^ 2 ^ j) = dSpMat (s ^ 2 ^ j) (t ^ 2 ^ j)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [dSpMat, Matrix.diagonal_apply, Units.val_pow_eq_pow_val, inv_pow]

theorem frobAut_dSp (hF : Nat.card F = 2 ^ 2) (s t : Fˣ) :
    frobAut F (dSp s t) = dSp s⁻¹ t⁻¹ := by
  have hsq : ∀ u : Fˣ, u ^ 2 = u⁻¹ := by
    intro u
    have hcu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
    have h3 : u ^ 3 = 1 := by
      simpa [hcu] using pow_card_eq_one' (x := u)
    have hm : u * u ^ 2 = 1 := by
      rw [← pow_succ', show 1 + 2 = 3 by norm_num, h3]
    exact eq_inv_of_mul_eq_one_right hm
  have h := frobAut_pow_dSp (F := F) 1 s t
  simpa [hsq s, hsq t] using h

theorem frobAut_sq (hF : Nat.card F = 2 ^ 2) : frobAut F ^ 2 = 1 :=
  CFSG.Quasithin.H13.F431.SpOut2.frobAut_pow_card hF

theorem frobAut_mem_B0_iff (x : antiSp F) : frobAut F x ∈ B0 F ↔ x ∈ B0 F := by
  have hiff : ∀ y : antiSp F, frobAut F y ∈ antiUnipotent F ↔ y ∈ antiUnipotent F :=
    CFSG.Quasithin.H13.F431.SpOut2.frobAut_pow_mem_antiUnipotent_iff 1
  have hmap : (antiUnipotent F).map (frobAut F).toMonoidHom = antiUnipotent F := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hiff z).mpr hz
    · intro hy
      refine ⟨(frobAut F)⁻¹ y, ?_, by simp⟩
      exact (hiff ((frobAut F)⁻¹ y)).mp (by simpa using hy)
  have h := mem_normalizer_map (frobAut F) (antiUnipotent F) (frobAut F x)
  rw [hmap, MulEquiv.symm_apply_apply] at h
  simpa only [B0] using h

theorem isSylowTwoOf_antiUnipotent_B0 (hF : Nat.card F = 2 ^ 2) :
    CFSG.QuasithinUnique.IsSylowTwoOf (antiUnipotent F) (B0 F) := by
  have hle : antiUnipotent F ≤ B0 F := Subgroup.le_normalizer
  have hcardU : Nat.card (↥((antiUnipotent F).subgroupOf (B0 F))) = Nat.card (antiUnipotent F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hcard := Subgroup.card_mul_index ((antiUnipotent F).subgroupOf (B0 F))
  rw [hcardU, card_antiUnipotent hF, card_B0 hF] at hcard
  have hidx : ((antiUnipotent F).subgroupOf (B0 F)).index = 9 := by
    norm_num at hcard ⊢
    omega
  refine ⟨hle, IsPGroup.of_card (n := 8) (card_antiUnipotent hF), ?_⟩
  rw [hidx]
  norm_num

theorem rootU₁_le_B0 : rootU₁ F ≤ B0 F :=
  rootU₁_le_antiUnipotentCenter.trans (antiUnipotentCenter_le.trans Subgroup.le_normalizer)

theorem rootU₂_le_B0 : rootU₂ F ≤ B0 F :=
  rootU₂_le_antiUnipotentCenter.trans (antiUnipotentCenter_le.trans Subgroup.le_normalizer)

theorem card_dTor_subgroupOf (hF : Nat.card F = 2 ^ 2) :
    Nat.card ((dTor F).subgroupOf (B0 F)) = 9 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe dTor_le).toEquiv).trans (card_dTor hF)

theorem card_rootU₁_subgroupOf (hF : Nat.card F = 2 ^ 2) :
    Nat.card ((rootU₁ F).subgroupOf (B0 F)) = 4 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe rootU₁_le_B0).toEquiv).trans (card_rootU₁ hF)

theorem card_rootU₂_subgroupOf (hF : Nat.card F = 2 ^ 2) :
    Nat.card ((rootU₂ F).subgroupOf (B0 F)) = 4 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe rootU₂_le_B0).toEquiv).trans (card_rootU₂ hF)

theorem card_radA1_subgroupOf (hF : Nat.card F = 2 ^ 2) :
    Nat.card ((radA1 F).subgroupOf (B0 F)) = 2 ^ 6 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    ((radA1_le_antiUnipotent (K := F)).trans Subgroup.le_normalizer)).toEquiv).trans
    (card_radA1 hF)

theorem card_radA2_subgroupOf (hF : Nat.card F = 2 ^ 2) :
    Nat.card ((radA2 F).subgroupOf (B0 F)) = 2 ^ 6 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    ((radA2_le_antiUnipotent (K := F)).trans Subgroup.le_normalizer)).toEquiv).trans
    (card_radA2 hF)

@[expose] noncomputable def frobAutB0 : MulAut (↥(B0 F)) :=
  subgroupEquiv (frobAut F) fun g => (frobAut_mem_B0_iff g).symm

theorem frobAutB0_apply (g : ↥(B0 F)) :
    ((frobAutB0 g : ↥(B0 F)) : antiSp F) = frobAut F g :=
  rfl

end CFSG.Quasithin.F112R.St84.Sp44
