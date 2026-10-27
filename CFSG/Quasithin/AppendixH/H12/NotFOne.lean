module

public import CFSG.Quasithin.Background.HM22RowMain

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.M22Row

variable {V : Type} [CommGroup V] [Finite V]

theorem not_isFOneModule_of_mhat22
    {L M : Subgroup (MulAut V)} {z : MulAut V} (hV : ∀ v : V, v ^ 2 = 1) (hc : Nat.card V = 4096)
    (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) (hz3 : ∀ v, z (z (z v)) = v)
    (hzf : ∀ v, z v = v → v = 1) (hz1 : z ≠ z⁻¹) (hzc : ∀ g ∈ L, g * z = z * g)
    (hdi : ∀ x ∈ Subgroup.normalizer (L : Set (MulAut V)), x ∈ L ∨ x * z * x⁻¹ = z⁻¹)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hinv : ∀ b ∈ L, b * b = 1 → b ≠ 1 → Nat.card (fixV (Subgroup.zpowers b)) ≤ 256)
    (hne : ∀ b ∈ L, ∀ b' ∈ L, b * b = 1 → b' * b' = 1 → b ≠ 1 → b' ≠ 1 → b * b' = b' * b →
      b ≠ b' → ∃ v : V, b v = v ∧ b' v ≠ v) :
    ¬ IsFOneModule M := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  rintro ⟨A, ⟨hAM, hA1, hAc, hAs⟩, hoff⟩
  have hAs' : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← pow_two]; exact hAs a ha
  have hfixle : ∀ b ∈ A, fixV A ≤ fixV (Subgroup.zpowers b) := fun b hb v hv =>
    mem_fixV_zpowers_iff.mpr (hv b hb)
  have hrk5 := rk_le_of_card_le hAs (card_le_of_le_normalizer hL hz1 hdi (hAM.trans hMN) hAc hAs')
  obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  by_cases hAL : A ≤ L
  ·
    have hrk4 := rk_le_of_card_le hAs (card_le_of_le_L hL hAL hAc hAs')
    have hb := hinv b (hAL hbA) (hAs' b hbA) hb1'
    by_cases hA2 : Nat.card A ≤ 2
    · have hrk1 := rk_le_of_card_le hAs (k := 1) (by simpa using hA2)
      have h1 := le_rkIdx_of_card_le hV hc (j := 8)
        ((Subgroup.card_le_of_le (hfixle b hbA)).trans (by simpa using hb))
      omega
    · obtain ⟨b', hb'A, hb'1, hb'b⟩ := exists_ne_of_two_lt_card (A := A) (by omega) b
      obtain ⟨v, hv, hv'⟩ := hne b (hAL hbA) b' (hAL hb'A) (hAs' b hbA) (hAs' b' hb'A) hb1' hb'1
        (hAc b hbA b' hb'A) (Ne.symm hb'b)
      have hlt : fixV A < fixV (Subgroup.zpowers b) := by
        refine lt_of_le_of_ne (hfixle b hbA) fun heq => hv' ?_
        have h1 : v ∈ fixV A := heq ▸ mem_fixV_zpowers_iff.mpr hv
        exact h1 b' hb'A
      have hcard := Subgroup.card_lt_of_lt hlt
      obtain ⟨j, hj⟩ := exists_card_eq_four_pow hV hz3 hzf (fixV A) fun x hx a ha => by
        rw [← MulAut.mul_apply, hzc a (hAL ha), MulAut.mul_apply, hx a ha]
      have hj3 : j ≤ 3 := by
        have h4 : 4 ^ j < 4 ^ 4 := by
          rw [← hj]
          calc Nat.card ↥(fixV A) < Nat.card ↥(fixV (Subgroup.zpowers b)) := hcard
            _ ≤ 256 := hb
            _ = 4 ^ 4 := by norm_num
        have h5 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h4
        omega
      have h6 : Nat.card ↥(fixV A) ≤ 2 ^ 6 := by
        rw [hj]
        calc 4 ^ j ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
          _ = 2 ^ 6 := by norm_num
      have h7 := le_rkIdx_of_card_le hV hc h6
      omega
  ·
    obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
    have haz : a * z * a⁻¹ = z⁻¹ := (hdi a (hMN (hAM haA))).resolve_left haL
    have ha2 : ∀ v, a (a v) = v := fun v => by
      have h2 := congrArg (fun f : MulAut V => f v) (hAs' a haA)
      simpa only [MulAut.mul_apply, MulAut.one_apply] using h2
    have hazv : ∀ v, a (z v) = z (z (a v)) := fun v => by
      have h1 : a * z = z⁻¹ * a := by
        calc a * z = (a * z * a⁻¹) * a := by group
          _ = z⁻¹ * a := by rw [haz]
      have h2 := congrArg (fun f : MulAut V => f v) h1
      simp only [MulAut.mul_apply] at h2
      rw [h2, inv_apply_eq hz3]
    by_cases hA0 : A ⊓ L = ⊥
    ·
      have hA2 : Nat.card A ≤ 2 := by
        have h1 := card_le_two_mul hz1 hdi (hAM.trans hMN) (H := A)
        rw [hA0, Subgroup.card_bot] at h1
        exact h1
      have hrk1 := rk_le_of_card_le hAs (k := 1) (by simpa using hA2)
      have hsq := card_eq_sq_fix hV hz3 hzf ha2 hazv ⊤ (fun _ _ => trivial) fun _ _ => trivial
      rw [Subgroup.card_top, hc, top_inf_eq] at hsq
      have h64 : Nat.card ↥(fixV (Subgroup.zpowers a)) ≤ 2 ^ 6 := by
        have h1 : Nat.card ↥(fixV (Subgroup.zpowers a)) ^ 2 ≤ (2 ^ 6) ^ 2 := by
          rw [← hsq]
          norm_num
        exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
      have h1 := le_rkIdx_of_card_le hV hc ((Subgroup.card_le_of_le (hfixle a haA)).trans h64)
      omega
    ·
      obtain ⟨⟨b0, hb0⟩, hb01⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA0
      have hb0A := (Subgroup.mem_inf.mp hb0).1
      have hb0L := (Subgroup.mem_inf.mp hb0).2
      have hb0c := hinv b0 hb0L (hAs' b0 hb0A) fun h1 => hb01 (Subtype.ext h1)
      have hXz : ∀ x ∈ fixV (A ⊓ L), z x ∈ fixV (A ⊓ L) := fun x hx c hc => by
        rw [← MulAut.mul_apply, hzc c (Subgroup.mem_inf.mp hc).2, MulAut.mul_apply, hx c hc]
      have hXa : ∀ x ∈ fixV (A ⊓ L), a x ∈ fixV (A ⊓ L) := fun x hx c hc => by
        rw [← MulAut.mul_apply, hAc c (Subgroup.mem_inf.mp hc).1 a haA, MulAut.mul_apply,
          hx c hc]
      have hsq := card_eq_sq_fix hV hz3 hzf ha2 hazv (fixV (A ⊓ L)) hXz hXa
      have hle : fixV A ≤ fixV (A ⊓ L) ⊓ fixV (Subgroup.zpowers a) := fun v hv =>
        ⟨fun c hc => hv c (Subgroup.mem_inf.mp hc).1, hfixle a haA hv⟩
      have hXb : fixV (A ⊓ L) ≤ fixV (Subgroup.zpowers b0) := fun v hv =>
        mem_fixV_zpowers_iff.mpr (hv b0 hb0)
      have h16 : Nat.card ↥(fixV A) ≤ 2 ^ 4 := by
        have h1 : Nat.card ↥(fixV A) ^ 2 ≤ (2 ^ 4) ^ 2 := by
          calc Nat.card ↥(fixV A) ^ 2
              ≤ Nat.card ↥(fixV (A ⊓ L) ⊓ fixV (Subgroup.zpowers a)) ^ 2 :=
                Nat.pow_le_pow_left (Subgroup.card_le_of_le hle) 2
            _ = Nat.card ↥(fixV (A ⊓ L)) := hsq.symm
            _ ≤ Nat.card ↥(fixV (Subgroup.zpowers b0)) := Subgroup.card_le_of_le hXb
            _ ≤ (2 ^ 4) ^ 2 := by simpa using hb0c
        exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
      have h1 := le_rkIdx_of_card_le hV hc h16
      omega

theorem not_isFOneModule_row
    (hV : ∀ v : V, v ^ 2 = 1) {L M : Subgroup (MulAut V)}
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) (h : Mhat22Twelve L ⊤ ⊥) :
    ¬ IsFOneModule M := by
  have hL := H12Pf.isHat_of_mhat22Twelve h
  have hc := H12Pf.card_eq_of_mhat22Twelve h
  obtain ⟨z, -, hz3, hzf, hz1, hzc, hdi⟩ := exists_center_gen hV h
  obtain ⟨hinv, hne, hodd⟩ := model_facts hV h
  exact not_isFOneModule_of_mhat22 hV hc hL hz3 hzf hz1 hzc hdi hMN hinv hne

end CFSG.Quasithin.AppendixH.H12
