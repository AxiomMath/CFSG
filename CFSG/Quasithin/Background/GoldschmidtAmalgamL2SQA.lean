module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SKer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2S

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem sq_mem_of_relIndex_two {H K : Subgroup D} (h2 : H.relIndex K = 2) {b : D} (hb : b ∈ K) :
    b * b ∈ H := by
  by_cases hbH : b ∈ H
  · exact H.mul_mem hbH hbH
  · obtain ⟨a, -, -, hall⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp h2
    have hba : b * a ∈ H := (hall b hb).resolve_right hbH
    by_contra hbb
    have hbba : b * b * a ∈ H := (hall (b * b) (K.mul_mem hb hb)).resolve_right hbb
    apply hbH
    have := H.mul_mem hbba (H.inv_mem hba)
    have e : b * b * a * (b * a)⁻¹ = b := by group
    rwa [e] at this


section QA

variable [Finite D] (h : Hyp2 A B z V)

include h

theorem Hyp2.inf_normalizer_zpowers_le :
    A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D) ≤ A ⊓ B := by
  have hTM : A ⊓ B ≤ A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D) := by
    refine le_inf inf_le_left (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hc : t * z = z * t := (Subgroup.mem_centralizer_iff.mp h.natural.z_mem.2 t ht)
    exact ((Commute.zpow_right (show Commute t z from hc) k).symm).eq
  have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hTM
    (inf_le_left : A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D) ≤ A)
  rw [h.gold.relIndex_left] at h1
  have hb : (A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D)).relIndex A ∣ 3 :=
    ⟨(A ⊓ B).relIndex (A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D)), by
      rw [← h1]; ring⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hb with hb1 | hb3
  · exfalso
    apply h.natural.not_normalizes
    intro a ha
    exact ((Subgroup.relIndex_eq_one.mp hb1) ha).2
  · rw [hb3] at h1
    exact Subgroup.relIndex_eq_one.mp (by omega)

theorem Hyp2.mem_T_of_comm {y : D} (hy : y ∈ A) (hyz : y * z = z * y) : y ∈ A ⊓ B := by
  have hcen : y ∈ Subgroup.centralizer (Subgroup.zpowers z : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((Commute.zpow_right (show Commute y z from hyz) k).symm).eq
  exact h.inf_normalizer_zpowers_le ⟨hy, Subgroup.centralizer_le_normalizer _ hcen⟩


theorem Hyp2.mem_V_of_center_QA {e : D} (he : e ∈ centerOf (pCoreOf 2 A)) (he2 : e * e = 1) :
    e ∈ V := by
  have hrel := h.gold.relIndex_pCoreOf_T_left
  obtain ⟨t, htT, htQ, hall⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hrel
  have hQT : pCoreOf 2 A ≤ A ⊓ B := h.QA_le_T
  have hsq : t * t ∈ pCoreOf 2 A := sq_mem_of_relIndex_two hrel htT
  have hnorm : t ∈ Subgroup.normalizer (pCoreOf 2 A : Set D) := le_normalizer_pCoreOf 2 A htT.1
  have he' : t * e * t⁻¹ ∈ centerOf (pCoreOf 2 A) := conj_mem_centerOf' hnorm he
  have hcQ : ∀ {q w : D}, q ∈ pCoreOf 2 A → w ∈ centerOf (pCoreOf 2 A) → q * w = w * q :=
    fun {q w} hq hw => Subgroup.mem_centralizer_iff.mp hw.2 q hq
  have hZT : ∀ {w : D}, w ∈ centerOf (pCoreOf 2 A) → t * w = w * t →
      w ∈ centerOf (A ⊓ B) := by
    intro w hw htw
    refine ⟨hQT hw.1, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    by_cases hsQ : s ∈ pCoreOf 2 A
    · exact hcQ hsQ hw
    · have hst : s * t ∈ pCoreOf 2 A := (hall s hs).resolve_right hsQ
      have hwt' : t⁻¹ * w = w * t⁻¹ := by
        calc t⁻¹ * w = t⁻¹ * (w * t) * t⁻¹ := by group
          _ = t⁻¹ * (t * w) * t⁻¹ := by rw [htw]
          _ = w * t⁻¹ := by group
      calc s * w = (s * t) * (t⁻¹ * w) := by group
        _ = (s * t) * (w * t⁻¹) := by rw [hwt']
        _ = ((s * t) * w) * t⁻¹ := by group
        _ = (w * (s * t)) * t⁻¹ := by rw [hcQ hst hw]
        _ = w * s := by group
  have he'2 : (t * e * t⁻¹) * (t * e * t⁻¹) = 1 := by
    calc (t * e * t⁻¹) * (t * e * t⁻¹) = t * (e * e) * t⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have hee' : e * (t * e * t⁻¹) = (t * e * t⁻¹) * e := hcQ he.1 he'
  have hee2 : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hn : e * (t * e * t⁻¹) ∈ centerOf (pCoreOf 2 A) := Subgroup.mul_mem _ he he'
  have htn : t * (e * (t * e * t⁻¹)) = (e * (t * e * t⁻¹)) * t := by
    have h1 : t * (t * e * t⁻¹) * t⁻¹ = e := by
      have : (t * t) * e * (t * t)⁻¹ = e := by
        rw [hcQ hsq he]; group
      calc t * (t * e * t⁻¹) * t⁻¹ = (t * t) * e * (t * t)⁻¹ := by group
        _ = e := this
    calc t * (e * (t * e * t⁻¹)) = ((t * e * t⁻¹) * (t * (t * e * t⁻¹) * t⁻¹)) * t := by group
      _ = ((t * e * t⁻¹) * e) * t := by rw [h1]
      _ = (e * (t * e * t⁻¹)) * t := by rw [hee']
  have hnZ := hZT hn htn
  have hn2 : (e * (t * e * t⁻¹)) * (e * (t * e * t⁻¹)) = 1 := by
    calc (e * (t * e * t⁻¹)) * (e * (t * e * t⁻¹))
        = e * ((t * e * t⁻¹) * e) * (t * e * t⁻¹) := by group
      _ = e * (e * (t * e * t⁻¹)) * (t * e * t⁻¹) := by rw [← hee']
      _ = (e * e) * ((t * e * t⁻¹) * (t * e * t⁻¹)) := by group
      _ = 1 := by rw [he2, he'2, one_mul]
  rcases h.omega _ hnZ (by rw [pow_two]; exact hn2) with h1 | h1
  ·
    have hte : t * e * t⁻¹ = e := by
      have := eq_inv_of_mul_eq_one_right h1
      rw [this, hee2]
    have htw : t * e = e * t := by
      calc t * e = (t * e * t⁻¹) * t := by group
        _ = e * t := by rw [hte]
    rcases h.omega e (hZT he htw) (by rw [pow_two]; exact he2) with h2 | h2
    · rw [h2]; exact V.one_mem
    · rw [h2]; exact h.natural.z_mem_V
  ·
    obtain ⟨a₀, ha1, haz, hVset⟩ := h.natural.basis
    have ha0V : a₀ ∈ V := by
      have : a₀ ∈ (V : Set D) := by rw [hVset]; simp
      exact this
    have ha0Z : a₀ ∈ centerOf (pCoreOf 2 A) := h.natural.le_center ha0V
    have hconj : t * a₀ * t⁻¹ = a₀ * z := h.natural.conj_eq_mul inf_le_left htT htQ ha0V ha1 haz
    have hze : e * z = z * e := Subgroup.mem_centralizer_iff.mp h.natural.z_mem.2 e (hQT he.1)
    have hza : z * a₀ = a₀ * z := h.natural.comm_of_mem h.natural.z_mem_V ha0V
    have he'z : t * e * t⁻¹ = e * z := by
      calc t * e * t⁻¹ = e⁻¹ * (e * (t * e * t⁻¹)) := by group
        _ = e⁻¹ * z := by rw [h1]
        _ = e * z := by rw [hee2]
    have hf : e * a₀ ∈ centerOf (pCoreOf 2 A) := Subgroup.mul_mem _ he ha0Z
    have hea : e * a₀ = a₀ * e := hcQ he.1 ha0Z
    have htf : t * (e * a₀) = (e * a₀) * t := by
      have h2 : t * (e * a₀) * t⁻¹ = e * a₀ := by
        calc t * (e * a₀) * t⁻¹ = (t * e * t⁻¹) * (t * a₀ * t⁻¹) := by group
          _ = (e * z) * (a₀ * z) := by rw [he'z, hconj]
          _ = e * (z * a₀) * z := by group
          _ = e * (a₀ * z) * z := by rw [hza]
          _ = e * a₀ * (z * z) := by group
          _ = e * a₀ := by rw [h.z_mul_z, mul_one]
      calc t * (e * a₀) = (t * (e * a₀) * t⁻¹) * t := by group
        _ = (e * a₀) * t := by rw [h2]
    have hf2 : (e * a₀) * (e * a₀) = 1 := by
      calc (e * a₀) * (e * a₀) = e * (a₀ * e) * a₀ := by group
        _ = e * (e * a₀) * a₀ := by rw [← hea]
        _ = (e * e) * (a₀ * a₀) := by group
        _ = 1 := by rw [he2, h.V_sq ha0V, one_mul]
    have ha0inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right (h.V_sq ha0V)
    have hefa : e = (e * a₀) * a₀ := by
      calc e = (e * a₀) * a₀⁻¹ := by group
        _ = (e * a₀) * a₀ := by rw [ha0inv]
    rcases h.omega _ (hZT hf htf) (by rw [pow_two]; exact hf2) with h2 | h2
    · rw [hefa, h2, one_mul]; exact ha0V
    · rw [hefa, h2]; exact V.mul_mem h.natural.z_mem_V ha0V


theorem Hyp2.exists_mem_V_of_normal {N : Subgroup D} (hNQ : N ≤ pCoreOf 2 A) (hN1 : N ≠ ⊥)
    (hn : pCoreOf 2 A ≤ Subgroup.normalizer (N : Set D)) : ∃ e ∈ N, e ≠ 1 ∧ e ∈ V := by
  have hP : IsPGroup 2 ↥(pCoreOf 2 A) := pCoreOf_isPGroup 2 A
  have hbot : pCoreOf 2 A ≤ Subgroup.normalizer ((⊥ : Subgroup D) : Set D) := by
    intro t _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp [Subgroup.mem_bot]
  obtain ⟨x, hxN, hx1, hxT⟩ :=
    D14.exists_fixed_of_lt hP hNQ (bot_lt_iff_ne_bot.mpr hN1) hn hbot
  have hxc : x ∈ Subgroup.centralizer ((pCoreOf 2 A : Subgroup D) : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h' := Subgroup.mem_bot.mp (hxT t ht)
    calc t * x = (t * x * t⁻¹ * x⁻¹) * (x * t) := by group
      _ = x * t := by rw [h', one_mul]
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup D, C = N ⊓ centerOf (pCoreOf 2 A) := ⟨_, rfl⟩
  have hxC : x ∈ C := by rw [hCdef]; exact ⟨hxN, hNQ hxN, hxc⟩
  have hCT : IsPGroup 2 ↥C := hP.to_le (by rw [hCdef]; exact inf_le_left.trans hNQ)
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ω', hω'⟩ : ∃ ω : ↥C, orderOf ω = 2 := by
    refine exists_prime_orderOf_dvd_card' 2 ?_
    obtain ⟨k, hk⟩ := hCT.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hC1 : C = ⊥ := Subgroup.eq_bot_of_card_eq C (by simpa using hk)
      exact hx1 (by rw [hC1] at hxC; exact hxC)
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hωo : orderOf (ω' : D) = 2 := by rw [Subgroup.orderOf_coe, hω']
  have hω2 : (ω' : D) ^ 2 = 1 := by rw [← hωo]; exact pow_orderOf_eq_one _
  have hω1 : (ω' : D) ≠ 1 := fun e => by rw [e, orderOf_one] at hωo; omega
  have hωC : (ω' : D) ∈ N ⊓ centerOf (pCoreOf 2 A) := by rw [← hCdef]; exact ω'.2
  exact ⟨ω', hωC.1, hω1, h.mem_V_of_center_QA hωC.2 (by rw [← pow_two]; exact hω2)⟩

theorem Hyp2.QA_le_normalizer_K : pCoreOf 2 A ≤ Subgroup.normalizer
    ((pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) : Subgroup D) : Set D) :=
  (h.QA_le_T.trans inf_le_right).trans h.B_le_normalizer_K

theorem Hyp2.K_le_QA : pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) ≤
    pCoreOf 2 A := h.K_le_R.trans inf_le_left

theorem Hyp2.conjSub_K_le_QA {y : D} (hyA : y ∈ A) :
    conjSub y (pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) ≤ pCoreOf 2 A := by
  intro w hw
  have hw' := mem_conjSub.mp hw
  have hyN : y ∈ Subgroup.normalizer (pCoreOf 2 A : Set D) := le_normalizer_pCoreOf 2 A hyA
  have := (Subgroup.mem_normalizer_iff.mp hyN _).mp (h.K_le_QA hw')
  have e : y * (y⁻¹ * w * y) * y⁻¹ = w := by group
  rwa [e] at this

theorem Hyp2.QA_le_normalizer_conjSub_K {y : D} (hyA : y ∈ A) : pCoreOf 2 A ≤
    Subgroup.normalizer
      (conjSub y (pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) : Set D) := by
  have hconjQ : ∀ q ∈ pCoreOf 2 A, y⁻¹ * q * y ∈ pCoreOf 2 A := by
    intro q hq
    have hyN : y⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 A : Set D) :=
      le_normalizer_pCoreOf 2 A (A.inv_mem hyA)
    have := (Subgroup.mem_normalizer_iff.mp hyN q).mp hq
    simpa using this
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [mem_conjSub, mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp (h.QA_le_normalizer_K (hconjQ q hq)) (y⁻¹ * w * y)
  have e : y⁻¹ * (q * w * q⁻¹) * y = (y⁻¹ * q * y) * (y⁻¹ * w * y) * (y⁻¹ * q * y)⁻¹ := by
    group
  rw [e]; exact this

theorem Hyp2.K_inf_conj_eq_bot {y : D} (hyA : y ∈ A) (hyT : y ∉ A ⊓ B) :
    (pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) ⊓
      conjSub y (pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) = ⊥ := by
  obtain ⟨K, hK⟩ : ∃ K : Subgroup D,
      K = pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := ⟨_, rfl⟩
  rw [← hK]
  by_contra hne
  have hQK : pCoreOf 2 A ≤ Subgroup.normalizer (K : Set D) := by
    rw [hK]; exact h.QA_le_normalizer_K
  have hQKy : pCoreOf 2 A ≤ Subgroup.normalizer (conjSub y K : Set D) := by
    rw [hK]; exact h.QA_le_normalizer_conjSub_K hyA
  have hKQ : K ≤ pCoreOf 2 A := by rw [hK]; exact h.K_le_QA
  have hQN₀ : pCoreOf 2 A ≤ Subgroup.normalizer ((K ⊓ conjSub y K : Subgroup D) : Set D) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (hQK hq) w)
      (Subgroup.mem_normalizer_iff.mp (hQKy hq) w)
  obtain ⟨e, heN, he1, heV⟩ :=
    h.exists_mem_V_of_normal (inf_le_left.trans hKQ) hne hQN₀
  have hKV : K ⊓ V = Subgroup.zpowers z := by rw [hK]; exact h.K_inf_V
  have hez : e = z := by
    have : e ∈ Subgroup.zpowers z := by rw [← hKV]; exact ⟨heN.1, heV⟩
    exact (h.mem_zpowers this).resolve_left he1
  have hye : y⁻¹ * e * y ∈ K := mem_conjSub.mp heN.2
  have hyeV : y⁻¹ * e * y ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 (A.inv_mem hyA)) e).mp heV
    simpa using this
  have hyz : y⁻¹ * z * y ∈ Subgroup.zpowers z := by
    rw [← hKV]; rw [hez] at hye hyeV; exact ⟨hye, hyeV⟩
  rcases h.mem_zpowers hyz with h1 | h1
  · apply h.natural.z_ne
    calc z = y * (y⁻¹ * z * y) * y⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · apply hyT
    refine h.mem_T_of_comm hyA ?_
    calc y * z = y * (y⁻¹ * z * y) := by rw [h1]
      _ = z * y := by group

end QA

end GoldAmL2S

end F6

end CFSG.Quasithin
