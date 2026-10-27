module

public import CFSG.GH74.Generic.BProg.B1.PilotS5Facts

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.Open (walterJ1)
open CFSG.GH74.Generic.BProg.B1.PilotS5 (walterJ1_split mem_sup_zpowers_of_two mem_zpowers_of_two)

def kleinAt189 (i : Fin 5) : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {g | g.1 i = i ∧ g * g = 1}
  mul_mem' := by
    have key : ∀ (i : Fin 5) (a b : alternatingGroup (Fin 5)), (a.1 i = i ∧ a * a = 1) →
        (b.1 i = i ∧ b * b = 1) → ((a * b).1 i = i ∧ (a * b) * (a * b) = 1) := by
      decide +kernel
    intro a b ha hb
    exact key i a b ha hb
  one_mem' := by
    refine ⟨rfl, one_mul 1⟩
  inv_mem' := by
    intro a ha
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.2
    rw [this]
    exact ha

theorem a5_exists_normalized_klein (σ : alternatingGroup (Fin 5)) (hσ : orderOf σ = 3) :
    ∃ V : Subgroup (alternatingGroup (Fin 5)), Nat.card V = 4 ∧
      σ ∈ Subgroup.normalizer (V : Set (alternatingGroup (Fin 5))) := by
  have hσ' : σ ^ 3 = 1 ∧ σ ≠ 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime_iff.mp hσ
  have hfix : ∀ σ : alternatingGroup (Fin 5), σ ^ 3 = 1 → σ ≠ 1 → ∃ i : Fin 5, σ.1 i = i := by
    decide +kernel
  obtain ⟨i, hi⟩ := hfix σ hσ'.1 hσ'.2
  refine ⟨kleinAt189 i, ?_, ?_⟩
  · have key : ∀ i : Fin 5, (Finset.univ.filter
        (fun g : alternatingGroup (Fin 5) => g.1 i = i ∧ g * g = 1)).card = 4 := by
      decide +kernel
    rw [← key i, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => Iff.rfl)
  · have key : ∀ (i : Fin 5) (σ h : alternatingGroup (Fin 5)), σ.1 i = i →
        ((h.1 i = i ∧ h * h = 1) ↔
          ((σ * h * σ⁻¹).1 i = i ∧ (σ * h * σ⁻¹) * (σ * h * σ⁻¹) = 1)) := by
      decide +kernel
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact key i σ h hi

theorem J1_mem_zpowers_of_commute {x g : walterJ1} (hx3 : orderOf x = 3) (hg3 : g ^ 3 = 1)
    (hc : g * x = x * g) : g ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hog : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 1)).mp (by simpa using hog)
  have hg3' : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hx3' : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3, pow_one])
  have hnorm : Subgroup.zpowers g ≤ Subgroup.normalizer (Subgroup.zpowers x : Set walterJ1) := by
    rw [Subgroup.zpowers_le]
    have hgc : g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set walterJ1) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_right (show Commute g x from hc) k).symm).eq
    exact Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set walterJ1) hgc
  have hsup : IsPGroup 3 (Subgroup.zpowers g ⊔ Subgroup.zpowers x : Subgroup walterJ1) :=
    hg3'.to_sup_of_normal_right' hx3' hnorm
  obtain ⟨k, hk⟩ := hsup.exists_card_eq
  have hdvd : 3 ^ k ∣ Nat.card walterJ1 := hk ▸ Subgroup.card_subgroup_dvd_card _
  rw [CFSG.Walter.J1Props.J1_card] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h9.trans hdvd
    norm_num at this
  have heq : Subgroup.zpowers x = Subgroup.zpowers g ⊔ Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by
      rw [hk, Nat.card_zpowers, hx3]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := pow_one 3)
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g)

theorem J1_mem_of_commute_odd {t x : walterJ1} (ht2 : orderOf t = 2) {L : Subgroup walterJ1}
    (hL : L ≤ Subgroup.centralizer ({t} : Set walterJ1))
    (hC : Subgroup.centralizer ({t} : Set walterJ1) = Subgroup.zpowers t ⊔ L)
    (e : L ≃* alternatingGroup (Fin 5)) (hxodd : Odd (orderOf x)) (hx1 : x ≠ 1)
    (hc : x * t = t * x) : x ∈ L := by
  have hxC : x ∈ Subgroup.centralizer ({t} : Set walterJ1) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc
  rw [hC] at hxC
  rcases mem_sup_zpowers_of_two ht2 hL hxC with ⟨l, hl, rfl⟩ | ⟨l, hl, hxl⟩
  · exact hl
  · exfalso
    have ht2' : t * t = 1 := by
      rw [← pow_two, ← ht2]
      exact pow_orderOf_eq_one t
    have hlx : l = t * x := by
      rw [hxl, ← mul_assoc, ht2', one_mul]
    have hord : orderOf l = 2 * orderOf x := by
      rw [hlx]
      refine (Commute.orderOf_mul_eq_mul_orderOf_of_coprime hc.symm ?_).trans (by rw [ht2])
      rw [ht2]
      exact (Nat.coprime_two_left.mpr hxodd)
    have hxpos : 0 < orderOf x := orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)
    have hx1' : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    rcases CFSG.Walter.J1.A5Sub.pow_eq_one e hl with h2 | h3 | h5
    · have := orderOf_dvd_of_pow_eq_one h2
      rw [hord] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have := orderOf_dvd_of_pow_eq_one h3
      rw [hord] at this
      have := Nat.le_of_dvd (by norm_num) this
      obtain ⟨m, hm⟩ := hxodd
      omega
    · have := orderOf_dvd_of_pow_eq_one h5
      rw [hord] at this
      have := Nat.le_of_dvd (by norm_num) this
      obtain ⟨m, hm⟩ := hxodd
      omega

theorem J1_invariant_sylow_of_involution {x t : walterJ1}
    (hx3 : orderOf x = 3) (ht2 : orderOf t = 2) (hc : x * t = t * x) :
    ∃ S : Subgroup walterJ1, Subgroup.zpowers t ≤ S ∧ IsPGroup 2 S ∧
      x ∈ Subgroup.normalizer (S : Set walterJ1) ∧ Nat.card S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, hLC, htL, hC, ⟨e⟩⟩ := walterJ1_split t ht2
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx3
    omega
  have hxL : x ∈ L := J1_mem_of_commute_odd ht2 hLC hC e (by rw [hx3]; decide) hx1 hc
  have hea : orderOf (e ⟨x, hxL⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx3]
  obtain ⟨V, hV4, hVN⟩ := a5_exists_normalized_klein _ hea
  set V' : Subgroup walterJ1 := V.map (CFSG.Walter.J1.A5Sub.ι e) with hV'
  have hV'card : Nat.card V' = 4 := by
    rw [hV', Subgroup.card_map_of_injective (CFSG.Walter.J1.A5Sub.ι_injective e), hV4]
  have hV'L : V' ≤ L := by
    rintro _ ⟨b, -, rfl⟩
    exact CFSG.Walter.J1.A5Sub.ι_mem e b
  have hxV' : x ∈ Subgroup.normalizer (V' : Set walterJ1) := by
    have := Subgroup.le_normalizer_map (CFSG.Walter.J1.A5Sub.ι e) (Subgroup.mem_map_of_mem _ hVN)
    rwa [CFSG.Walter.J1.A5Sub.ι_apply e hxL] at this
  have htcomm : ∀ v ∈ V', v * t = t * v := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLC (hV'L hv))
  have htV' : t ∈ Subgroup.normalizer (V' : Set walterJ1) :=
    Subgroup.centralizer_le_normalizer (V' : Set walterJ1) (Subgroup.mem_centralizer_iff.mpr htcomm)
  have hdisj : Disjoint V' (Subgroup.zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro g hgV hgt
    rcases mem_zpowers_of_two ht2 hgt with rfl | rfl
    · rfl
    · exact absurd (hV'L hgV) htL
  have hcardS : Nat.card (V' ⊔ Subgroup.zpowers t : Subgroup walterJ1) = 8 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V' (Subgroup.zpowers t)
      (Subgroup.zpowers_le.mpr htV') hdisj, hV'card, Nat.card_zpowers, ht2]
  refine ⟨V' ⊔ Subgroup.zpowers t, le_sup_right,
    IsPGroup.of_card (n := 3) (by rw [hcardS]; norm_num), ?_, hcardS⟩
  have hxt : x ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup walterJ1) : Set walterJ1) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    have h1 : (MulAut.conj x) t = t := by
      rw [MulAut.conj_apply, hc]
      group
    exact h1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hxV' hxt ⊢
  rw [Subgroup.map_sup, hxV', hxt]

theorem mem_normalizer_centralizer189 {G : Type*} [Group G] {T : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    x ∈ Subgroup.normalizer ((Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) := by
  have hfwd : ∀ x ∈ Subgroup.normalizer (T : Set G), ∀ y ∈ Subgroup.centralizer (T : Set G),
      x * y * x⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
    intro x hx y hy
    rw [Subgroup.mem_centralizer_iff]
    intro τ hτ
    have hτ' : x⁻¹ * τ * x ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hx _).mpr (by simpa [mul_assoc] using hτ)
    have h1 := Subgroup.mem_centralizer_iff.mp hy _ hτ'
    calc τ * (x * y * x⁻¹) = x * ((x⁻¹ * τ * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * τ * x)) * x⁻¹ := by rw [h1]
      _ = (x * y * x⁻¹) * τ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hfwd x hx y, fun hy => ?_⟩
  have := hfwd x⁻¹ ((Subgroup.normalizer (T : Set G)).inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem J1_centralizer_eq_sylow {T : Subgroup walterJ1}
    (hT4 : Nat.card T = 4) (P : Sylow 2 walterJ1) (hTP : T ≤ P) :
    Subgroup.centralizer (T : Set walterJ1) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP8, hPsq, hPcomm, -⟩ := CFSG.Walter.J1Props.jankoHyp.sylow_structure P
  have hPC : (P : Subgroup walterJ1) ≤ Subgroup.centralizer (T : Set walterJ1) := fun p hp =>
    Subgroup.mem_centralizer_iff.mpr fun t ht => hPcomm t (hTP ht) p hp
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : T = ⊥ := (Subgroup.eq_bot_iff_forall T).mpr hcon
    rw [this, Subgroup.card_bot] at hT4
    omega
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime_iff.mpr ⟨by rw [pow_two]; exact hPsq t (hTP htT), ht1⟩
  obtain ⟨v, hvT, hvt⟩ : ∃ v ∈ T, v ∉ Subgroup.zpowers t := by
    by_contra hcon
    push Not at hcon
    have hle : T ≤ Subgroup.zpowers t := hcon
    have := Subgroup.card_le_of_le hle
    rw [hT4, Nat.card_zpowers, ht2] at this
    omega
  have hv1 : v ≠ 1 := fun h => hvt (h ▸ Subgroup.one_mem _)
  have hvne : v ≠ t := fun h => hvt (h ▸ Subgroup.mem_zpowers t)
  have ht2' : t * t = 1 := hPsq t (hTP htT)
  have hv2' : v * v = 1 := hPsq v (hTP hvT)
  have hvtc : v * t = t * v := hPcomm v (hTP hvT) t (hTP htT)
  obtain ⟨L, hLC, htL, hC, ⟨e⟩⟩ := walterJ1_split t ht2
  have hCp : IsPGroup 2 (Subgroup.centralizer (T : Set walterJ1)) := by
    have hpos : Nat.card (Subgroup.centralizer (T : Set walterJ1)) ≠ 0 := Nat.card_pos.ne'
    refine IsPGroup.of_card
      (n := (Nat.card (Subgroup.centralizer (T : Set walterJ1))).primeFactorsList.length)
      (Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun {d} hd hdvd => ?_))
    by_contra hd2
    haveI := Fact.mk hd
    obtain ⟨z, hz⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (T : Set walterJ1)) d hdvd
    have hzo : orderOf (z : walterJ1) = d := by rw [Subgroup.orderOf_coe, hz]
    have hzodd : Odd (orderOf (z : walterJ1)) := by
      rw [hzo]
      exact (hd.eq_two_or_odd'.resolve_left hd2)
    have hz1 : (z : walterJ1) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzo
      exact hd.one_lt.ne hzo
    have hzt : (z : walterJ1) * t = t * z := (Subgroup.mem_centralizer_iff.mp z.2 t htT).symm
    have hzv : (z : walterJ1) * v = v * z := (Subgroup.mem_centralizer_iff.mp z.2 v hvT).symm
    have hzL : (z : walterJ1) ∈ L := J1_mem_of_commute_odd ht2 hLC hC e hzodd hz1 hzt
    have hvC : v ∈ Subgroup.centralizer ({t} : Set walterJ1) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hvtc
    rw [hC] at hvC
    have key : ∃ w ∈ L, w * w = 1 ∧ w ≠ 1 ∧ w * z = z * w := by
      rcases mem_sup_zpowers_of_two ht2 hLC hvC with ⟨l, hl, rfl⟩ | ⟨l, hl, hvl⟩
      · exact ⟨v, hl, hv2', hv1, hzv.symm⟩
      · have hlv : l = t * v := by rw [hvl, ← mul_assoc, ht2', one_mul]
        refine ⟨l, hl, ?_, ?_, ?_⟩
        · rw [hlv]
          calc t * v * (t * v) = t * (v * t) * v := by group
            _ = t * (t * v) * v := by rw [hvtc]
            _ = (t * t) * (v * v) := by group
            _ = 1 := by rw [ht2', hv2', one_mul]
        · intro h
          rw [hlv] at h
          have h1 : v = t⁻¹ := eq_inv_of_mul_eq_one_right h
          rw [inv_eq_of_mul_eq_one_right ht2'] at h1
          exact hvne h1
        · rw [hlv]
          calc t * v * z = t * (v * z) := by group
            _ = t * (z * v) := by rw [← hzv]
            _ = (t * z) * v := by group
            _ = (z * t) * v := by rw [hzt]
            _ = z * (t * v) := by group
    obtain ⟨w, hwL, hw2, hw1, hwz⟩ := key
    have hz2 := CFSG.Walter.J1.A5Sub.sq_eq_one_of_commute e hwL hzL
      (by rw [pow_two]; exact hw2) hw1 hwz
    have hdvd2 : d ∣ 2 := hzo ▸ orderOf_dvd_of_pow_eq_one hz2
    exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp hdvd2)
  obtain ⟨P', hCP'⟩ := hCp.exists_le_sylow
  have hP' : Nat.card (P' : Subgroup walterJ1) = 8 :=
    (CFSG.Walter.J1Props.jankoHyp.sylow_structure P').1
  have hPP' : (P : Subgroup walterJ1) = P' :=
    Subgroup.eq_of_le_of_card_ge (hPC.trans hCP') (by rw [hP', hP8])
  exact le_antisymm (hCP'.trans hPP'.symm.le) hPC

theorem J1_invariant_sylow_of_card_four {x : walterJ1}
    {T : Subgroup walterJ1} (hT : IsPGroup 2 T) (hT4 : Nat.card T = 4)
    (hxT : x ∈ Subgroup.normalizer (T : Set walterJ1)) :
    ∃ S : Subgroup walterJ1, T ≤ S ∧ IsPGroup 2 S ∧
      x ∈ Subgroup.normalizer (S : Set walterJ1) ∧ Nat.card S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  have hC := J1_centralizer_eq_sylow hT4 P hTP
  refine ⟨P, hTP, P.isPGroup', ?_, (CFSG.Walter.J1Props.jankoHyp.sylow_structure P).1⟩
  rw [← hC]
  exact mem_normalizer_centralizer189 hxT

theorem J1_exists_invariant_sylow {x : walterJ1}
    (hx3 : orderOf x = 3) {T : Subgroup walterJ1} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hxT : x ∈ Subgroup.normalizer (T : Set walterJ1)) :
    ∃ S : Subgroup walterJ1, T ≤ S ∧ IsPGroup 2 S ∧
      x ∈ Subgroup.normalizer (S : Set walterJ1) ∧ Nat.card S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 ^ 3 * 3 * 5 * 7 * 11 * 19 := by
    rw [← CFSG.Walter.J1Props.J1_card, ← hk]
    exact Subgroup.card_subgroup_dvd_card T
  have hk3 : k ≤ 3 := by
    by_contra hk4
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd
    norm_num at this
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hk, pow_zero])) hT1
    · exact hpos
  interval_cases k
  · obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hT1 ((Subgroup.eq_bot_iff_forall T).mpr hcon)
    have ht2 : orderOf t = 2 := by
      have h1 : orderOf t ∣ 2 := by
        have := Subgroup.orderOf_dvd_natCard T htT
        rwa [hk, pow_one] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ht1
      · exact h
    have hTt : T = Subgroup.zpowers t :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htT)
        (by rw [Nat.card_zpowers, ht2, hk, pow_one])).symm
    have hc : x * t = t * x := by
      have h1 : x * t * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hxT t).mp htT
      rw [hTt] at h1
      rcases mem_zpowers_of_two ht2 h1 with h | h
      · exfalso
        apply ht1
        have : x * t = x := by
          rw [mul_inv_eq_one] at h
          exact h
        exact mul_eq_left.mp this
      · exact mul_inv_eq_iff_eq_mul.mp h
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := J1_invariant_sylow_of_involution hx3 ht2 hc
    exact ⟨S, hTt ▸ hS1, hS2, hS3, hS4⟩
  · exact J1_invariant_sylow_of_card_four hT (by rw [hk]; norm_num) hxT
  · exact ⟨T, le_rfl, hT, hxT, by rw [hk]; norm_num⟩

end CFSG.RankThree.PartTwo.Sec18
