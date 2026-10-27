module

public import CFSG.Quasithin.AppendixH.H12.Setting
public import CFSG.Quasithin.AppendixH.H12.NotFOne
public import CFSG.Quasithin.Background.HMathieuFactsBase
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin.H.Mathieu.H12Cert CFSG.Quasithin.H13.MatNCert CFSG.Monster.Code Matrix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {V : Type} [CommGroup V]
  {ρ : G →* MulAut V}

private theorem bvec_eq_vecN (n m : ℕ) : bvec n m = vecN n m := by
  funext i
  simp only [bvec, vecN, CFSG.Quasithin.H13.Mat8Cert.b2z]

private theorem mem_fixV_of_model {c : List ℕ} (hc : ValidN 12 c)
    (θ : V ≃* Wn 12) (t : MulAut V)
    (hθ : ∀ w : V, Multiplicative.toAdd (θ (t w)) =
      (decN 12 c) *ᵥ Multiplicative.toAdd (θ w)) :
    ∀ m < 2 ^ 12,
      (MaskCoords.ofEquiv θ).vm m ∈ fixV (Subgroup.zpowers t) ↔ (mvN c m == m) = true := by
  intro m hm
  let w : V := θ.symm (toW 12 m)
  have hwadd : Multiplicative.toAdd (θ w) = vecN 12 m := by
    dsimp only [w]
    rw [MulEquiv.apply_symm_apply, toAdd_toW, bvec_eq_vecN]
  have key : θ (t w) = θ w ↔ mvN c m = m := by
    constructor
    · intro h
      have h2 := congrArg Multiplicative.toAdd h
      rw [hθ w, hwadd, decN_mulVec hc.1] at h2
      exact vecN_inj (mvN_lt hc.2 m) (by simpa using hm) h2
    · intro h
      apply Multiplicative.toAdd.injective
      rw [hθ w, hwadd, decN_mulVec hc.1, h]
  rw [CFSG.Quasithin.H.mem_fixV_zpowers_iff, MaskCoords.ofEquiv_vm]
  exact ((θ.injective.eq_iff).symm).trans (key.trans beq_iff_eq.symm)

private def w3 : List ℕ := [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0]

private theorem orderOf_gU_zero : orderOf (H12Cert.gU 0) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
    decide +kernel
  · intro h
    have h1 : (H12Cert.gU 0 : Matrix (Fin 12) (Fin 12) (ZMod 2)) = 1 := by rw [h]; rfl
    rw [H12Cert.gU_val, ← decN_oneN] at h1
    exact (by decide +kernel : H12Cert.gG.getD 0 H12Cert.one12 ≠ H12Cert.one12)
      (decN_injOn (validN_getD H12Cert.validN_gG 0) validN_oneN h1)

private theorem orderOf_tU_w3 : orderOf (H12Cert.tU w3) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    decide +kernel
  · intro h
    have h1 : (H12Cert.tU w3 : Matrix (Fin 12) (Fin 12) (ZMod 2)) = 1 := by rw [h]; rfl
    rw [H12Cert.tU_val, ← decN_oneN] at h1
    exact (by decide +kernel : H12Cert.tW w3 ≠ H12Cert.one12)
      (decN_injOn (validN_evalW H12Cert.gG H12Cert.validN_gG w3) validN_oneN h1)

theorem mParam_eq_four
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    (hρ : IsFaithIrr12 (ρ.comp L.subtype)) : E3.mParam ρ.range = 4 := by
  haveI : Finite V := finite_of_faithIrr12 hρ
  have hV : ∀ v : V, v ^ 2 = 1 := hρ.1
  have hc : Nat.card V = 4096 := by rw [hρ.2.1]; norm_num
  have hM : Mhat22Twelve (L.map ρ) ⊤ ⊥ := mhat22Twelve_map hL hρ
  have hMN : ρ.range ≤
      Subgroup.normalizer ((L.map ρ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    range_le_normalizer hF
  have hLM : L.map ρ ≤ ρ.range := Subgroup.map_le_range ρ L
  have hOver : IsOver (L.map ρ) ρ.range := ⟨hLM, hMN⟩
  obtain ⟨ψ, θ, hψθ⟩ := H12Pf.exists_model_of_mhat22Twelve hV hM
  obtain ⟨z, hzL, hz3, hzf, hz1, hzc, hdi⟩ := M22Row.exists_center_gen hV hM
  obtain ⟨hinv, hne, hodd⟩ := M22Row.model_facts hV hM
  let g0 : ↥H12Cert.G := ⟨H12Cert.gU 0, H12Cert.gU_mem 0⟩
  let t0 : MulAut V := ((ψ g0 : ↥(L.map ρ)) : MulAut V)
  have hθ0 : ∀ w : V, Multiplicative.toAdd (θ (t0 w)) =
      (decN 12 (H12Cert.gG.getD 0 H12Cert.one12)) *ᵥ Multiplicative.toAdd (θ w) := by
    intro w
    simpa only [g0, t0, H12Cert.gU_val] using hψθ g0 w
  have hc0 : ValidN 12 (H12Cert.gG.getD 0 H12Cert.one12) := validN_getD H12Cert.validN_gG 0
  have hX0 := mem_fixV_of_model hc0 θ t0 hθ0
  have hlen0 : ((List.range (2 ^ 12)).filter
      (fun m => mvN (H12Cert.gG.getD 0 H12Cert.one12) m == m)).length = 256 := by
    decide +kernel
  have ht0_ord : orderOf t0 = 2 := by
    have h1 : orderOf t0 = orderOf g0 := by
      change orderOf (((ψ g0 : ↥(L.map ρ)) : MulAut V)) = orderOf g0
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    have hg0 : orderOf g0 = 2 := (Subgroup.orderOf_coe g0).symm.trans orderOf_gU_zero
    exact h1.trans hg0
  have ht0_rk : rkIdx (fixV (Subgroup.zpowers t0)) = 4 := by
    have h1 := rkIdx_of_arr (e := θ)
      (P := fun m => mvN (H12Cert.gG.getD 0 H12Cert.one12) m == m) hX0
    rw [h1, hlen0]
    decide +kernel
  have ht0L : t0 ∈ L.map ρ := (ψ g0).2
  have hall : ∀ s ∈ ρ.range, orderOf s = 2 → 4 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
    intro s hsM hs2
    have hs_sq : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rwa [hs2, pow_two] at h
    have hs_ne1 : s ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
    by_cases hsL : s ∈ L.map ρ
    · have hcard := hinv s hsL hs_sq hs_ne1
      have := M22Row.le_rkIdx_of_card_le hV hc (j := 8) (by simpa using hcard)
      omega
    · have haz : s * z * s⁻¹ = z⁻¹ := (hdi s (hMN hsM)).resolve_left hsL
      have ha2 : ∀ v, s (s v) = v := by
        intro v
        have h := congrArg (fun f : MulAut V => f v) hs_sq
        simpa only [MulAut.mul_apply, MulAut.one_apply] using h
      have hazv : ∀ v, s (z v) = z (z (s v)) := by
        have h1 : s * z = z⁻¹ * s := by
          calc s * z = (s * z * s⁻¹) * s := by group
            _ = z⁻¹ * s := by rw [haz]
        intro v
        have h2 := congrArg (fun f : MulAut V => f v) h1
        simp only [MulAut.mul_apply] at h2
        rw [h2, M22Row.inv_apply_eq hz3]
      have hsq := M22Row.card_eq_sq_fix hV hz3 hzf ha2 hazv ⊤
        (fun _ _ => trivial) (fun _ _ => trivial)
      rw [Subgroup.card_top, hc, top_inf_eq] at hsq
      have h64 : Nat.card (fixV (Subgroup.zpowers s)) ≤ 2 ^ 6 := by
        have h1 : Nat.card (fixV (Subgroup.zpowers s)) ^ 2 ≤ (2 ^ 6) ^ 2 := by
          rw [← hsq]; norm_num
        exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
      have := M22Row.le_rkIdx_of_card_le hV hc (j := 8) (h64.trans (by norm_num))
      omega
  exact mParam_eq_of hOver ht0L ht0_ord ht0_rk hall

theorem betaH_eq_eight
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    (hρ : IsFaithIrr12 (ρ.comp L.subtype)) : H.betaH ρ.range = 8 := by
  haveI : Finite V := finite_of_faithIrr12 hρ
  have hV : ∀ v : V, v ^ 2 = 1 := hρ.1
  have hc : Nat.card V = 4096 := by rw [hρ.2.1]; norm_num
  have hM : Mhat22Twelve (L.map ρ) ⊤ ⊥ := mhat22Twelve_map hL hρ
  have hMN : ρ.range ≤
      Subgroup.normalizer ((L.map ρ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    range_le_normalizer hF
  obtain ⟨z, hzL, hz3, hzf, hz1, hzc, hdi⟩ := M22Row.exists_center_gen hV hM
  obtain ⟨hinv, hne, hodd⟩ := M22Row.model_facts hV hM
  obtain ⟨ψ, θ, hψθ⟩ := H12Pf.exists_model_of_mhat22Twelve hV hM
  have hLc : Nat.card (L.map ρ) = 1330560 := by
    rw [← Nat.card_congr ψ.toEquiv, H12Cert.card_G]
  have hlow : (8 : ℕ∞) ≤ H.betaH ρ.range :=
    M22Row.eight_le_betaH hV hc hz1 hdi hMN hLc hodd
  let gy : ↥H12Cert.G := ⟨H12Cert.tU w3, H12Cert.tU_mem w3⟩
  let a : MulAut V := ((ψ gy : ↥(L.map ρ)) : MulAut V)
  let U : Subgroup V := fixV (Subgroup.zpowers a)
  have hθ3 : ∀ w : V, Multiplicative.toAdd (θ (a w)) =
      (decN 12 (H12Cert.tW w3)) *ᵥ Multiplicative.toAdd (θ w) := by
    intro w
    simpa only [gy, a, H12Cert.tU_val] using hψθ gy w
  have hc3 : ValidN 12 (H12Cert.tW w3) := validN_evalW H12Cert.gG H12Cert.validN_gG w3
  have hX3 := mem_fixV_of_model hc3 θ a hθ3
  have hlen3 : ((List.range (2 ^ 12)).filter
      (fun m => mvN (H12Cert.tW w3) m == m)).length = 16 := by
    decide +kernel
  have hcardU : Nat.card U = 16 := by
    rw [(MaskCoords.ofEquiv θ).card_eq U (fun m => mvN (H12Cert.tW w3) m == m) hX3, hlen3]
  have hUtop : U ≠ ⊤ := by
    intro h
    have h2 : Nat.card U = 4096 := by rw [h, Subgroup.card_top, hc]
    omega
  have ha3 : orderOf a = 3 := by
    have h1 : orderOf a = orderOf gy := by
      change orderOf (((ψ gy : ↥(L.map ρ)) : MulAut V)) = orderOf gy
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    have hgy : orderOf gy = 3 := (Subgroup.orderOf_coe gy).symm.trans orderOf_tU_w3
    exact h1.trans hgy
  have haM : a ∈ ρ.range := Subgroup.map_le_range ρ L (ψ gy).2
  have haU : a ∈ centSub U := by
    intro u hu
    exact (CFSG.Quasithin.H.mem_fixV_zpowers_iff (x := a)).mp hu
  have hres : twoResidual (ρ.range ⊓ centSub U) ≠ ⊥ := by
    intro hbot
    have hpg : IsPGroup 2 ↥(ρ.range ⊓ centSub U) := twoResidual_eq_bot_iff.mp hbot
    obtain ⟨k, hk⟩ := hpg ⟨a, haM, haU⟩
    have hk' : a ^ (2 ^ k) = 1 := by
      have h := congrArg (fun x : ↥(ρ.range ⊓ centSub U) => (x : MulAut V)) hk
      simpa [Subgroup.coe_pow] using h
    have hdvd : 3 ∣ 2 ^ k := by
      rw [← ha3]
      exact orderOf_dvd_iff_pow_eq_one.mpr hk'
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)
  have hrkU : rkIdx U = 8 := by
    have h1 := rkIdx_of_arr (e := θ) (P := fun m => mvN (H12Cert.tW w3) m == m) hX3
    rw [h1, hlen3]
    decide +kernel
  have hUle : H.betaH ρ.range ≤ (rkIdx U : ℕ∞) := by
    unfold H.betaH
    exact (iInf_le _ U).trans ((iInf_le _ hUtop).trans (iInf_le _ hres))
  have hle : H.betaH ρ.range ≤ 8 := by
    calc H.betaH ρ.range ≤ (rkIdx U : ℕ∞) := hUle
      _ = 8 := by rw [hrkU]; norm_num
  exact le_antisymm hle hlow

theorem pRank_le_five_of_setting
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    (hρ : IsFaithIrr12 (ρ.comp L.subtype)) : CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 5 := by
  have hinj : Function.Injective ρ := injective_of_fitting hF hρ.2.2.1
  haveI : Finite V := finite_of_faithIrr12 hρ
  haveI : Finite (MulAut V) := MulEquiv.finite_left
  have hV : ∀ v : V, v ^ 2 = 1 := hρ.1
  have hM : Mhat22Twelve (L.map ρ) ⊤ ⊥ := mhat22Twelve_map hL hρ
  have hMN : ρ.range ≤
      Subgroup.normalizer ((L.map ρ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    range_le_normalizer hF
  have hrow := M22Row.row721M22Hat hV hMN hM
  have htop := pRank_two_map_of_injective ρ hinj (⊤ : Subgroup G)
  rw [← htop, ← MonoidHom.range_eq_map]
  exact hrow.1

theorem params_clause
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    (hρ : IsFaithIrr12 (ρ.comp L.subtype)) :
    E3.mParam ρ.range = 4 ∧ H.betaH ρ.range = 8 ∧ ¬ H.IsFOneModule ρ.range ∧
      CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 5 := by
  haveI : Finite V := finite_of_faithIrr12 hρ
  have hV : ∀ v : V, v ^ 2 = 1 := hρ.1
  have hM : Mhat22Twelve (L.map ρ) ⊤ ⊥ := mhat22Twelve_map hL hρ
  have hMN : ρ.range ≤
      Subgroup.normalizer ((L.map ρ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    range_le_normalizer hF
  exact ⟨mParam_eq_four hL hF hρ, betaH_eq_eight hL hF hρ,
    not_isFOneModule_row hV hMN hM, pRank_le_five_of_setting hL hF hρ⟩

end CFSG.Quasithin.AppendixH.H12
