module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Core

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.Shult CFSG.Quasithin.Loc442 MulAction

theorem divCases60 : ∀ d ∈ Nat.divisors 60, d % 8 = 1 → d = 1 := by decide +kernel

theorem divCases62400 : ∀ d ∈ Nat.divisors 62400, d % 8 = 1 → d = 1 ∨ d = 25 ∨ d = 65 := by
  decide +kernel

theorem numericsCop (N b a m : ℕ) (h8 : 8 ∣ N) (hb : Nat.Coprime b 65) (hodd : Odd a)
    (hab : a ∣ b) (hm : m = 60 ∨ m = 62400) (hn : (N + 1) * b = a * m) : False := by
  obtain ⟨c, rfl⟩ := hab
  have hapos : 0 < a := hodd.pos
  have hc : (N + 1) * c = m := by
    refine Nat.eq_of_mul_eq_mul_left hapos ?_
    rw [← hn]
    ring
  have hc65 : Nat.Coprime c 65 := Nat.Coprime.coprime_dvd_left (Dvd.intro_left a rfl) hb
  have h5 : ¬ 5 ∣ c :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).1
      (Nat.Coprime.coprime_dvd_right (by norm_num : 5 ∣ 65) hc65).symm
  have h13 : ¬ 13 ∣ c :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).1
      (Nat.Coprime.coprime_dvd_right (by norm_num : 13 ∣ 65) hc65).symm
  obtain ⟨k, rfl⟩ := h8
  have hdvd : 8 * k + 1 ∣ m := Dvd.intro c hc
  have hmod : (8 * k + 1) % 8 = 1 := by omega
  rcases hm with rfl | rfl
  · have hmem : 8 * k + 1 ∈ Nat.divisors 60 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    rw [divCases60 _ hmem hmod] at hc
    omega
  · have hmem : 8 * k + 1 ∈ Nat.divisors 62400 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    rcases divCases62400 _ hmem hmod with h | h | h <;> rw [h] at hc <;> omega

section Core


theorem acoreCop {K : Type} [Group K] [Finite K] {X V : Subgroup K} (hX : X ≠ ⊤) (hVX : V ≤ X)
    (hVn : (V.subgroupOf X).Normal) (hV4 : Nat.card V = 4)
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    (hfix : ShultFixedPoint X V) {q : K} (hqX : q ∈ X) (hqV : ∀ v ∈ V, q * v = v * q)
    (hq2 : q ^ 2 ∈ V) (hq2' : q ^ 2 ≠ 1) (hXc : Nat.Coprime (Nat.card X) 65) : False := by
  have hVbot : V ≠ ⊥ := by
    intro h
    rw [h] at hV4
    simp at hV4
  have hElem : IsElemAbelian 2 V := ⟨⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩, hV2⟩
  have hyp : ShultI85Hyp X V := ⟨hX, hVbot, hVX, hVn, hElem, hfix⟩
  rcases shultI85Part1 K X V hyp with ⟨h2, -⟩ | ⟨f, hf, hBQ, -, hXL, hSE⟩
  · omega
  · have hf2 : f = 2 := by
      have : (2 : ℕ) ^ f = 2 ^ 2 := by rw [← hf, hV4]; norm_num
      exact Nat.pow_right_injective le_rfl this
    subst hf2
    set L := Subgroup.normalClosure (V : Set K) with hL
    have : L.Normal := Subgroup.normalClosure_normal
    have hVL : V ≤ L := Subgroup.le_normalClosure
    have h8 := eight_dvd hSE hVL hVX hV4 hV2 hqX hqV hq2 hq2'
    have hcount := card_deltaSet_succ (X := X) (L := L)
    have hZodd : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
      rw [hBQ.2.1]
      exact odd_card_fusionOddCore ↥L
    have hLZ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    have hm : Nat.card (↥L ⧸ Subgroup.center ↥L) = 60 ∨
        Nat.card (↥L ⧸ Subgroup.center ↥L) = 62400 := by
      rcases hBQ.2.2 with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨a, ha, hfa, -⟩
      · left
        rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card (by norm_num)]
        norm_num
      · right
        rw [Nat.card_congr e.toEquiv,
          CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3 (by norm_num)]
        norm_num
      · omega
    have hZle : (Subgroup.center ↥L).map L.subtype ≤ X ⊓ L := by
      rintro _ ⟨z, hz, rfl⟩
      have hc : ∀ w ∈ L, (z : K) * w * (z : K)⁻¹ = w := by
        intro w hw
        have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨w, hw⟩)
        simp only [Subgroup.coe_mul] at this
        rw [← this]
        group
      have hzN : (z : K) ∈ Subgroup.normalizer (V : Set K) := by
        rw [Subgroup.mem_normalizer_iff]
        intro v
        constructor
        · intro hv
          rw [hc v (hVL hv)]
          exact hv
        · intro hv
          have hvL : v ∈ L := by
            have h1 : (z : K)⁻¹ * ((z : K) * v * (z : K)⁻¹) * (z : K) ∈ L :=
              L.mul_mem (L.mul_mem (L.inv_mem z.2) (hVL hv)) z.2
            simpa [mul_assoc] using h1
          rwa [hc v hvL] at hv
      have : (z : K) ∈ X ⊓ L := by
        rw [hXL]
        exact ⟨hzN, z.2⟩
      exact this
    have hab : Nat.card ↥(Subgroup.center ↥L) ∣ Nat.card ↥(X ⊓ L) := by
      have := Subgroup.card_dvd_of_le hZle
      rwa [Subgroup.card_map_of_injective L.subtype_injective] at this
    have hb : Nat.Coprime (Nat.card ↥(X ⊓ L)) 65 :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hXc
    refine numericsCop (Nat.card ↥(deltaSet X L)) (Nat.card ↥(X ⊓ L)) _ _ h8 hb hZodd hab hm ?_
    rw [hcount, hLZ, mul_comm]

end Core

end CFSG.Quasithin
