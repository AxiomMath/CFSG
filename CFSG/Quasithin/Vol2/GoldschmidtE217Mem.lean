module

public import CFSG.Quasithin.Vol2.GoldschmidtE217Quot
public import CFSG.Quasithin.Vol2.Ch3nE2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F B6 E2

namespace E217R1

section Numerics

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem not_le_pCoreOf (h : E2.Pair X T M V g) (hXV : X ≠ V) : ¬ V ≤ pCoreOf 2 X := by
  set Q := pCoreOf 2 X with hQ
  intro hVQ
  have hWQ : conjSub g V ≤ Q := by
    have h1 := (conjSub g).monotone hVQ
    rwa [hQ, h.conjSub_pCoreOf] at h1
  have hXQ : X ≤ Q := by
    rw [h.gen]
    exact sup_le hVQ hWQ
  have hX2 : IsPGroup 2 X := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hXQ
  have hTX : T = X := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hX2
    have hdvd : T.relIndex X ∣ 2 ^ n := by
      rw [← hn]
      have h1 := Subgroup.relIndex_mul_card T X
      rw [inf_eq_left.2 h.sylow.1] at h1
      exact Dvd.intro _ h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hi0 : i = 0 := by
      by_contra hi0
      apply h.sylow.2.2
      show 2 ∣ T.relIndex X
      rw [hi]
      exact dvd_pow_self 2 hi0
    rw [hi0, pow_zero] at hi
    exact le_antisymm h.sylow.1 (Subgroup.relIndex_eq_one.1 hi)
  have hgV : conjSub g V = V := conjSub_eq_self (h.normal_T (hTX ▸ h.mem))
  apply hXV
  rw [h.gen, hgV, sup_idem]

theorem cube_le_sq_of_cubic {H A : Subgroup G} (hV : IsElemAbelian 2 V) (hAH : A ≤ H)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hAel : IsElemAbelian 2 A)
    (hcub : ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥) (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G))
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hV H)) :
    ((A ⊓ Subgroup.centralizer (V : Set G)).relIndex A) ^ 3 ≤
      ((V ⊓ Subgroup.centralizer (A : Set G)).relIndex V) ^ 2 := by
  have h := le_kq_iff.1 hq (autI hV A) ⟨autI_mono hV hAH,
    (autI_eq_bot_iff hV hAN).not.2 hAV, isElemAbelian2_autI hV hAel hAN⟩
    (commSeries_autI_eq_bot_of_cubic hcub)
  rw [rAV_autI hAN] at h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hV)
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hAel)
  have hdx := hk ▸ relIndex_dvd_card (V ⊓ Subgroup.centralizer (A : Set G)) V inf_le_left
  have hdy := hl ▸ relIndex_dvd_card (A ⊓ Subgroup.centralizer (V : Set G)) A inf_le_left
  obtain ⟨β, -, hβ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdx
  obtain ⟨α, -, hα⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdy
  have hα0 : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hα
      exact hAV ((Subgroup.relIndex_eq_one.1 hα).trans inf_le_right)
    · exact h0
  rw [hβ, hα, padicValNat.prime_pow, padicValNat.prime_pow,
    le_div_iff₀ (by exact_mod_cast hα0)] at h
  rw [hβ, hα, ← pow_mul, ← pow_mul]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have h3 : ((α * 3 : ℕ) : ℚ) ≤ ((β * 2 : ℕ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h3


theorem relIndex_eq_two_of_member {H : Subgroup G} (hel : IsElemAbelian 2 V)
    (h : E2.Pair X T M V g) (hchar : CharTwo X) (hne : X ≠ V) (hXH : X ≤ H)
    (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hel H))
    (hstar : (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V)) :
    (kerIn M X ⊓ V).relIndex V = 2 := by
  set B := kerIn M X ⊓ V with hB
  set A := conjSub g B with hA
  set Z := V ⊓ conjSub g V with hZ
  obtain ⟨hAT, -, hAel, hcub, hAnc, hAC⟩ := Ch3n.exists_cubic_of_pair h hchar hne
  have hAX : A ≤ X := h.A_le_pCoreOf.trans (pCoreOf_le 2 X)
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans h.normal_T
  have hcube := cube_le_sq_of_cubic hel (hAX.trans hXH) hAN hAel hcub hAnc hq
  rw [hAC] at hcube
  have hZB : Z ≤ B := h.inf_conj_le_kerIn_inf
  have hBV : B ≤ V := inf_le_right
  have hZg : conjSub g Z = Z := conjSub_eq_self (h.le_normalizer_Z h.mem)
  have hZA : Z.relIndex A = Z.relIndex B := by
    have := Ch3n.relIndex_conjSub g Z B
    rwa [hZg] at this
  rw [hZA] at hcube
  have hb0 : Z.relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hZC : Z ≤ Subgroup.centralizer (V : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.2 fun v hv => h.comm hv hz.1
  have hb1 : Z.relIndex B ≠ 1 := by
    intro h1
    apply hAnc
    rw [← hZA] at h1
    exact (Subgroup.relIndex_eq_one.1 h1).trans hZC
  have hb2 : 2 ≤ Z.relIndex B := by omega
  have hZCA : Z ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    intro z hz
    refine ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact (h.mem_center hz (hAX ha)).symm
  have hcV : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ∣ Z.relIndex B * B.relIndex V := by
    rw [Subgroup.relIndex_mul_relIndex Z B V hZB hBV]
    exact Subgroup.relIndex_dvd_of_le_left V hZCA
  have hcVle : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ Z.relIndex B * B.relIndex V :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hb0)
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)) hcV
  have hv0 : B.relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hv1 : B.relIndex V ≠ 1 := by
    intro h1
    have hVB : V ≤ B := Subgroup.relIndex_eq_one.1 h1
    exact not_le_pCoreOf h hne
      (h.le_pCoreOf_of_le_kerIn (B6.isPGroup_of_isElemAbelian hel) (hVB.trans inf_le_left))
  have hv2 : 2 ≤ B.relIndex V := by omega
  have hcardV : B.relIndex V * (Z.relIndex B * Nat.card Z) = 2 ^ 4 := by
    have e1 := Subgroup.relIndex_mul_card B V
    rw [inf_eq_left.2 hBV] at e1
    have e2 := Subgroup.relIndex_mul_card Z B
    rw [inf_eq_left.2 hZB] at e2
    rw [e2, e1, hV16]
  by_cases hz1 : Nat.card Z = 1
  · exfalso
    have hZbot : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z hz1
    have hBC : B ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
      intro b hb
      refine ⟨hb.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 := h.commutator_B_A hb ha
      have h2 : b * a * b⁻¹ * a⁻¹ = 1 := by
        have : b * a * b⁻¹ * a⁻¹ ∈ Z := h1
        rw [hZbot, Subgroup.mem_bot] at this
        exact this
      calc a * b = (b * a * b⁻¹ * a⁻¹)⁻¹ * (b * a) := by group
        _ = b * a := by rw [h2]; group
    have hcV2 : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ B.relIndex V :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) (Subgroup.relIndex_dvd_of_le_left V hBC)
    have h1 : Z.relIndex B ^ 3 ≤ B.relIndex V ^ 2 :=
      hcube.trans (Nat.pow_le_pow_left hcV2 2)
    have h2 : B.relIndex V ^ 2 ≤ Z.relIndex B ^ 2 := Nat.pow_le_pow_left hstar 2
    nlinarith
  · have hz2 : 2 ≤ Nat.card Z := by
      have := Nat.card_pos (α := Z)
      omega
    nlinarith


theorem false_of_member {H : Subgroup G} (hel : IsElemAbelian 2 V) (h : E2.Pair X T M V g)
    (hchar : CharTwo X) (hne : X ≠ V) (hXH : X ≤ H) (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hel H))
    (hstar : (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V))
    (h4 : 4 ∣ (kerIn M X).relIndex X) : False :=
  not_four_dvd_relIndex_of_relIndex_eq_two h
    (relIndex_eq_two_of_member hel h hchar hne hXH hV16 hq hstar) h4

end Numerics

end E217R1

end CFSG.Quasithin
