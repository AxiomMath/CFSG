module

public import CFSG.Quasithin.Recognition.Stroth.Str83Rq413Arc
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Vol2.Ch11SecA02Arith

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem exists_cartan_factor {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) :
    ∃ Dv : Subgroup G, Dv ≤ t.K ∧ Dv ≤ t.Lv v ∧
      Nat.card Dv = (if Even v then 2 ^ (2 * a + 1) else 2 ^ f) - 1 := by
  classical
  let Dv : Subgroup G := (if Even v then t.D1 else t.D2).map
    (MulAut.conj (t.edgeElt v)).toMonoidHom
  have hK : t.K.map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.edgeElt_mem_normalizer v)
  have hDvK : Dv ≤ t.K := by
    dsimp [Dv]
    refine (Subgroup.map_mono ?_).trans_eq hK
    split_ifs
    · exact le_sup_left
    · exact le_sup_right
  have hDvLv : Dv ≤ t.Lv v := by
    dsimp [Dv]
    split_ifs with hv
    · have hL : (t.Lv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Lv v := by
        have h := t.map_Lv_edgeElt hfr v 0
        rw [if_pos hv] at h
        rwa [show v + 0 = v by omega] at h
      have hD : t.D1 ≤ t.Lv 0 := by
        rw [t.Lv_zero]
        exact (t.hD1hall.1.trans (F1.borelOf_le L1 S)).trans le_sup_left
      exact (Subgroup.map_mono hD).trans_eq hL
    · have hL : (t.Lv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Lv v := by
        have h := t.map_Lv_edgeElt hfr v 1
        rw [if_neg hv] at h
        rwa [show v + 1 - 1 = v by omega] at h
      have hD : t.D2 ≤ t.Lv 1 := by
        rw [t.Lv_one]
        exact (t.hD2hall.1.trans (F1.borelOf_le L2 S)).trans le_sup_left
      exact (Subgroup.map_mono hD).trans_eq hL
  refine ⟨Dv, hDvK, hDvLv, ?_⟩
  by_cases hv : Even v
  · have hcard : Nat.card Dv = Nat.card t.D1 := by
      dsimp [Dv]
      rw [if_pos hv]
      exact Subgroup.card_map_of_injective
        (f := (MulAut.conj (t.edgeElt v)).toMonoidHom)
        (MulAut.conj (t.edgeElt v)).injective
    rw [hcard, t.card_D1 hfr, if_pos hv]
  · have hcard : Nat.card Dv = Nat.card t.D2 := by
      dsimp [Dv]
      rw [if_neg hv]
      exact Subgroup.card_map_of_injective
        (f := (MulAut.conj (t.edgeElt v)).toMonoidHom)
        (MulAut.conj (t.edgeElt v)).injective
    rw [hcard, t.card_D2 hfr, if_neg hv]

theorem sub_one_dvd_of_Lv_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε h : ℤ} (hh : Even (h - ε)) {X : Subgroup G}
    (hX : X ≤ pCoreOf 2 (t.Gw ε (ε + 1))) (hXK : t.K ≤ normalizer (X : Set G))
    (hXQ : ¬ X ≤ t.Qv ε) (hC : t.Lv h ≤ centralizer (X : Set G)) :
    (if Even ε then 2 ^ (2 * a + 1) else 2 ^ f) - 1 ∣
      (if Even ε then 2 ^ f else 2 ^ (2 * a + 1)) - 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := hfr.hf
  obtain ⟨Dε, hDεK, hDεL, hDεcard⟩ := t.exists_cartan_factor hfr ε
  obtain ⟨Dh, hDhK, hDhL, hDhcard⟩ := t.exists_cartan_factor hfr h
  have hpar : Even h ↔ Even ε := Int.even_sub.mp hh
  have hDεCX : Dε ⊓ centralizer (X : Set G) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro k hk
    obtain ⟨hkD, hkC⟩ := Subgroup.mem_inf.mp hk
    have hkK : k ∈ t.K := hDεK hkD
    have hkL : k ∈ t.Lv ε := hDεL hkD
    have hcomm := t.commutator_mem_Qv_of_mem_centralizer hfr ε hX hXK hXQ hkK hkC
    have hkQ : k ∈ t.Qv ε := t.mem_Qv_of_forall_commutator_mem hfr ε hkL hcomm
    have hKQ : t.K ⊓ t.Qv ε = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime ?_
      obtain ⟨n, hn⟩ := (t.isPGroup_Qv ε).exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr t.hHall.2.1)
    have hkbot : k ∈ (⊥ : Subgroup G) := by
      rw [← hKQ]
      exact Subgroup.mem_inf.mpr ⟨hkK, hkQ⟩
    simpa using hkbot
  have hDhC : Dh ≤ centralizer (X : Set G) := hDhL.trans hC
  have hinf : Dε ⊓ Dh = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left Dε hDhC).trans (le_of_eq hDεCX))
  have hDεC : Dε ≤ centralizer (Dh : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (t.K_comm hfr x (hDεK hx) y (hDhK hy)).symm
  have hDεN : Dε ≤ normalizer (Dh : Set G) :=
    hDεC.trans (Subgroup.centralizer_le_normalizer (Dh : Set G))
  have hprod : Nat.card ↥(Dε ⊔ Dh) = Nat.card Dε * Nat.card Dh := by
    have h := C5.card_sup_mul_card_inf_of_le_normalizer (A := Dε) (B := Dh) hDεN
    rw [hinf] at h
    simpa using h
  have hdvdK : Nat.card ↥(Dε ⊔ Dh) ∣ Nat.card t.K :=
    Subgroup.card_dvd_of_le (sup_le hDεK hDhK)
  have hD1N : t.D1 ≤ normalizer (t.D2 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have h : x * y * x⁻¹ = y := by
      rw [t.hcomm x hx y hy]
      group
    rwa [h]
  have hKdvd : Nat.card t.K ∣ Nat.card t.D1 * Nat.card t.D2 := by
    refine ⟨Nat.card ↥(t.D1 ⊓ t.D2), ?_⟩
    exact (C5.card_sup_mul_card_inf_of_le_normalizer (A := t.D1) (B := t.D2) hD1N).symm
  have hdvd : Nat.card Dε * Nat.card Dh ∣ Nat.card t.D1 * Nat.card t.D2 := by
    rw [← hprod]
    exact dvd_trans hdvdK hKdvd
  let q : ℕ := 2 ^ (2 * a + 1)
  let r : ℕ := 2 ^ f
  have hqpos : 0 < q - 1 := by
    have hq2 : 2 ≤ q := by
      dsimp [q]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrpos : 0 < r - 1 := by
    have hr2 : 2 ≤ r := by
      dsimp [r]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvdqr : ((if Even ε then q else r) - 1) * ((if Even h then q else r) - 1) ∣
      (q - 1) * (r - 1) := by
    simpa [q, r, hDεcard, hDhcard, t.card_D1 hfr, t.card_D2 hfr] using hdvd
  by_cases hε : Even ε
  · rw [if_pos hε, if_pos hε]
    have hhε : Even h := hpar.mpr hε
    have hdvdq : (q - 1) * (q - 1) ∣ (q - 1) * (r - 1) := by
      simpa [hε, hhε] using hdvdqr
    exact Nat.dvd_of_mul_dvd_mul_left hqpos hdvdq
  · rw [if_neg hε, if_neg hε]
    have hhε : ¬ Even h := fun hh' => hε (hpar.mp hh')
    have hdvdr : (r - 1) * (r - 1) ∣ (r - 1) * (q - 1) := by
      have h := hdvdqr
      simp only [if_neg hε, if_neg hhε] at h
      rwa [Nat.mul_comm (q - 1) (r - 1)] at h
    exact Nat.dvd_of_mul_dvd_mul_left hrpos hdvdr

theorem IsMaxArc.even_and_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1) {ε : ℤ} {b₁ : ℕ}
    (h : t.IsMaxArc ε (2 * (b₁ + 1))) (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₁ : Odd b₁)
    (hC : t.Lv ε ≤ centralizer (t.Zv ε : Set G)) (hZ : t.Zv ε ≤ t.Zv (ε + 1))
    (hZQ : t.Zv (ε + 1 + b₁) = omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + 2 * (b₁ + 1))))) :
    Even ε ∧ f = 2 * (2 * a + 1) ∧ Nat.card (t.Zv (ε + 1)) = (2 ^ f) ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := hfr.hf
  have hnotC : ¬ t.Lv (ε + 1) ≤ centralizer (t.Zv (ε + 1) : Set G) := by
    intro hC'
    exact t.false_of_Zv_le_of_le_centralizer hfr (u := ε) (v := ε + 1) (Or.inr rfl) hZ hC'
  have hlow := t.le_card_Zv_of_not_le_centralizer hfr (ε + 1) hnotC
  have hup := IsMaxArc.card_Zv_add_one_le t hfr h h₁ hb₁
  let w : ℤ := ε + 1 + b₁
  have hwsub : w - ε = (b₁ : ℤ) + 1 := by
    dsimp [w]
    ring
  have hεsub : ε - w = -((b₁ : ℤ) + 1) := by
    dsimp [w]
    ring
  have hb1_int : Odd (b₁ : ℤ) := (Int.odd_coe_nat b₁).mpr hb₁
  have hb1_even : Even ((b₁ : ℤ) + 1) :=
    Int.even_add_one.mpr (Int.not_even_iff_odd.mpr hb1_int)
  have hw_even : Even (w - ε) := by
    rw [hwsub]
    exact hb1_even
  have hε_even : Even (ε - w) := by
    rw [hεsub]
    exact Even.neg hb1_even
  have hZQw : t.Zv w = omegaOneCenterOf
      (pCoreOf 2 (t.Gw ε (ε + 2 * (b₁ + 1)))) := by
    simpa [w] using hZQ
  have hindex : ε + ↑(2 * (b₁ + 1)) = ε + 2 * (b₁ + 1) := by
    push_cast
    ring
  have hXle : t.Zv w ≤ pCoreOf 2 (t.Gw ε (ε + 2 * (b₁ + 1))) := by
    rw [hZQw]
    exact A4.omegaOneCenterOf_le _
  have hX : t.Zv w ≤ pCoreOf 2 (t.Gw ε (ε + 1)) :=
    t.le_pCoreOf_Gw hfr (show ε < ε + 1 by omega) (t.isPGroup_Zv w)
      (hXle.trans ((pCoreOf_le 2 _).trans (win_mono le_rfl (by omega))))
  have hXK : t.K ≤ normalizer (t.Zv w : Set G) := t.K_le_normalizer_Zv w
  have hXQ : ¬ t.Zv w ≤ t.Qv ε := by
    intro hle
    have harc : pCoreOf 2 (t.Gw ε (ε + 2 * (b₁ + 1))) ⊓ t.Qv ε = ⊥ := by
      rw [← hindex]
      exact (h.inf_Qv_eq_bot t hfr).1
    have hbot : t.Zv w ≤ (⊥ : Subgroup G) := by
      rw [← harc]
      exact le_inf hXle hle
    exact t.Zv_ne_bot hfr.hF w (le_bot_iff.mp hbot)
  have hCw : t.Lv w ≤ centralizer (t.Zv w : Set G) :=
    t.Lv_le_centralizer_of_even_sub hfr hε_even hC
  have hdvd := t.sub_one_dvd_of_Lv_le_centralizer hfr hw_even hX hXK hXQ hCw
  let q : ℕ := 2 ^ (2 * a + 1)
  let r : ℕ := 2 ^ f
  by_cases hε : Even ε
  · have hε1 : ¬ Even (ε + 1) := fun he => (Int.even_add_one.mp he) hε
    have hlow' : r ^ 2 ≤ Nat.card (t.Zv (ε + 1)) := by
      have h := hlow
      rw [if_neg hε1] at h
      simpa [r] using h
    have hup' : Nat.card (t.Zv (ε + 1)) ≤ q ^ 2 * r := by
      have h := hup
      rw [if_pos hε] at h
      simpa [q, r] using h
    have hr2 : 2 ≤ r := by
      dsimp [r]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hrle : r ≤ q ^ 2 := by
      have h1 : r * r ≤ q ^ 2 * r := by
        calc r * r = r ^ 2 := by ring
          _ ≤ Nat.card (t.Zv (ε + 1)) := hlow'
          _ ≤ q ^ 2 * r := hup'
      exact Nat.le_of_mul_le_mul_right h1 (by omega)
    have hfle : f ≤ 2 * (2 * a + 1) := by
      have hpow : 2 ^ f ≤ 2 ^ (2 * (2 * a + 1)) := by
        calc 2 ^ f = r := by dsimp [r]
          _ ≤ q ^ 2 := hrle
          _ = 2 ^ (2 * (2 * a + 1)) := by
            dsimp [q]
            rw [← pow_mul]
            congr 1
            ring
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
    have hdvd_qr : q - 1 ∣ r - 1 := by
      simpa [q, r, if_pos hε] using hdvd
    have hqf : 2 * a + 1 ∣ f := by
      apply CFSG.Quasithin.Vol2.Ch11.SecA.dvd_of_two_pow_sub_one_dvd
      simpa [q, r] using hdvd_qr
    obtain ⟨k, hk⟩ := hqf
    have hk0 : k ≠ 0 := by
      intro hk0
      rw [hk0, mul_zero] at hk
      omega
    have hk1 : k ≠ 1 := by
      intro hk1
      apply hrq
      rw [hk, hk1, mul_one]
    have hk2 : 2 ≤ k := by omega
    have hfge : 2 * (2 * a + 1) ≤ f := by
      rw [hk]
      calc 2 * (2 * a + 1) = (2 * a + 1) * 2 := by ring
        _ ≤ (2 * a + 1) * k := Nat.mul_le_mul_left (2 * a + 1) hk2
    have hfeq : f = 2 * (2 * a + 1) := le_antisymm hfle hfge
    have hreq : r = q ^ 2 := by
      calc r = 2 ^ f := by dsimp [r]
        _ = 2 ^ (2 * (2 * a + 1)) := by rw [hfeq]
        _ = q ^ 2 := by
          dsimp [q]
          rw [← pow_mul]
          congr 1
          ring
    have hcard : Nat.card (t.Zv (ε + 1)) = r ^ 2 := by
      apply le_antisymm
      · calc Nat.card (t.Zv (ε + 1)) ≤ q ^ 2 * r := hup'
          _ = r ^ 2 := by rw [← hreq]; ring
      · exact hlow'
    exact ⟨hε, hfeq, by simpa [r] using hcard⟩
  · exfalso
    have hε1 : Even (ε + 1) := Int.even_add_one.mpr hε
    have hq2 : 2 ≤ q := by
      dsimp [q]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hr2 : 2 ≤ r := by
      dsimp [r]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdvd_rq : r - 1 ∣ q - 1 := by
      simpa [q, r, if_neg hε] using hdvd
    have hfr_dvd : f ∣ 2 * a + 1 := by
      apply CFSG.Quasithin.Vol2.Ch11.SecA.dvd_of_two_pow_sub_one_dvd
      simpa [q, r] using hdvd_rq
    have hfle : f ≤ 2 * a + 1 := Nat.le_of_dvd (by omega) hfr_dvd
    have hflt : f < 2 * a + 1 := lt_of_le_of_ne hfle hrq
    have hrq_lt : r < q := by
      dsimp [r, q]
      exact Nat.pow_lt_pow_right (by norm_num) hflt
    have hlow' : q ^ 4 ≤ Nat.card (t.Zv (ε + 1)) := by
      have h := hlow
      rw [if_pos hε1] at h
      simpa [q] using h
    have hup' : Nat.card (t.Zv (ε + 1)) ≤ r ^ 2 * q := by
      have h := hup
      rw [if_neg hε] at h
      simpa [q, r] using h
    have hr2q2 : r ^ 2 < q ^ 2 :=
      Nat.pow_lt_pow_left hrq_lt (by norm_num : (2 : ℕ) ≠ 0)
    have hlt1 : r ^ 2 * q < q ^ 2 * q :=
      (Nat.mul_lt_mul_right (by omega : 0 < q)).mpr hr2q2
    have hq3 : q ^ 2 * q = q ^ 3 := by ring
    have hq34 : q ^ 3 < q ^ 4 := by
      calc q ^ 3 = q ^ 3 * 1 := by ring
        _ < q ^ 3 * q :=
          Nat.mul_lt_mul_of_pos_left (by omega : 1 < q) (pow_pos (by omega : 0 < q) 3)
        _ = q ^ 4 := by ring
    have hlt2 : r ^ 2 * q < q ^ 4 := by
      rw [hq3] at hlt1
      exact lt_trans hlt1 hq34
    exact (not_le.mpr (lt_of_le_of_lt hup' hlt2)) hlow'

end Track

end CFSG.Quasithin.Stroth.Rq
