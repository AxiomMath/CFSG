module

public import CFSG.Quasithin.H13.NQCatT3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.Quasithin.H13.NQCat.T3

open CFSG.Quasithin.H13.NQCat.T513 CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.Blueprint CFSG.Sporadic.Schreier

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem three_m22
    (h : Star513 Q R S B D)
    (hQ : IsSporadic .M22 ↥Q ∨ IsHat ↥Q (NativeSporadic.Carrier .M22))
    (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc22 : Subgroup.center ↥NativeSporadic.M22 = ⊥ := m22_center_eq_bot'
  have : IsSimpleGroup ↥NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have : Finite ↥NativeSporadic.M22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  obtain ⟨⟨ψ⟩, hperf⟩ : Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* ↥NativeSporadic.M22) ∧
      Group.IsPerfect ↥Q := by
    rcases hQ with hS | ⟨hqs, -, ⟨e⟩⟩
    · obtain ⟨e⟩ : Nonempty (↥Q ≃* ↥NativeSporadic.M22) := hS
      have hM : Group.IsPerfect ↥NativeSporadic.M22 := isPerfect_of_center_eq_bot hc22
      have hZ : Subgroup.center ↥Q = ⊥ := by
        have h1 := Subgroup.map_center_eq e
        rw [hc22] at h1
        exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
      exact ⟨⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩,
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩
    · exact ⟨⟨e⟩, hqs.1⟩
  have hcen : Subgroup.center (↥Q ⧸ Subgroup.center ↥Q) = ⊥ :=
    @Group.IsPerfect.center_quotient_center_eq_bot ↥Q _ hperf
  have hinn := oddInner_of_mulEquiv ψ (oddInner_of_card_le hc22 m22_mulAut_card)
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q ⧸ Subgroup.center ↥Q := MulEquiv.refl _
  obtain ⟨b, hb, hb3⟩ := exists_b_three e h
  obtain ⟨hE3, hE9⟩ := exists_three_group e hcen hinn h hD3 hnot hb hb3
  have hcard := card_sup_three e hcen hinn h hD3 hb hb3
  set E := iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) with hEdef
  set T := pImg Q e (S ⊓ Q) with hTdef
  have hP : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 443520 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
  have hE : Nat.card E = 9 := by
    obtain ⟨m, hm⟩ := hE3.exists_card_eq
    have hdvd : 3 ^ m ∣ 443520 := hm ▸ hP ▸ Subgroup.card_subgroup_dvd_card E
    rw [hm] at hE9 ⊢
    have hm2 : m ≤ 2 := by
      by_contra hm3
      have : 3 ^ 3 ∣ 443520 := (pow_dvd_pow 3 (by omega)).trans hdvd
      revert this
      decide
    interval_cases m
    · norm_num at hE9
    · norm_num at hE9
    · norm_num
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hT : Nat.card T = 128 := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have h1 := Subgroup.card_mul_index T
    rw [hn, hP] at h1
    have hn7 : n = 7 := by
      have hdvd : 2 ^ n ∣ 2 ^ 7 * 3465 := ⟨T.index, by rw [h1]; norm_num⟩
      have hle : n ≤ 7 := by
        by_contra hlt
        have : 2 ^ 8 ∣ 2 ^ 7 * 3465 := (pow_dvd_pow 2 (by omega)).trans hdvd
        revert this
        decide
      by_contra hne
      apply hTi
      have h2 : 2 ^ n * (T.index) = 2 ^ n * (2 ^ (7 - n) * 3465) := by
        rw [h1, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
        norm_num
      rw [Nat.eq_of_mul_eq_mul_left (by positivity) h2]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    rw [hn, hn7]
    norm_num
  have hET : Nat.card ↥(E ⊔ T) = 1152 := by rw [hcard, hE, hT]
  let ψ₀ : (↥Q ⧸ Subgroup.center ↥Q) ≃* ↥Mgrp :=
    ψ.trans (MulEquiv.subgroupCongr mGens_closure).symm
  have hck := cert_check
  have hU : IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  let US : Sylow 2 ↥Mgrp := hU.2.1.toSylow (by
    have := hU.2.2
    have e : (Ugrp.subgroupOf ⊤).index = Ugrp.index := Subgroup.relIndex_top_right _
    rwa [e] at this)
  let TS : Sylow 2 ↥Mgrp :=
    (hT2.toSylow hTi).mapSurjective (f := ψ₀.toMonoidHom) ψ₀.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Mgrp TS US
  let Y : Subgroup ↥Mgrp := ((E ⊔ T).map ψ₀.toMonoidHom).map (MulAut.conj g).toMonoidHom
  have hUY : Ugrp ≤ Y := by
    have h1 : (US : Subgroup ↥Mgrp) = Ugrp := rfl
    rw [← h1, ← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.map_mono (Subgroup.map_mono le_sup_right)
  have hY : Nat.card Y = 1152 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective ψ₀.injective, hET]
  obtain ⟨j, hj, hLM, hYL, hcj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) hck Y hUY
  rw [hYL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcj] at hY
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  have hsz : cert.sizes = [128, 384, 1920, 5760, 443520, 384] := rfl
  rw [hlen] at hj
  rw [hsz] at hY
  interval_cases j <;> simp at hY

end CFSG.Quasithin.H13.NQCat.T3
