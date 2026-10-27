module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinB3Subgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCardThreeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUniformInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinS4Normalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUCardThreePreB3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.HhatQuotientS4
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalTwoSubgroupSymmetricFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem even_card_of_mem_involution_j3
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {s : G} (hsM : s ∈ M) (hs : IsInvolution s) :
    Even (Nat.card M) := by
  have hdiv : orderOf s ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hsM
  have horder : orderOf s = 2 := orderOf_eq_prime hs.2 hs.1
  rw [horder] at hdiv
  exact even_iff_two_dvd.mpr hdiv

private theorem eq_of_mem_card_two_j3
    {H : Type u} [Group H] [Finite H]
    (A : Subgroup H) (hA : Nat.card A = 2) {a b : H}
    (ha : a ∈ A) (hb : b ∈ A) (hane : a ≠ 1) (hbne : b ≠ 1) : a = b := by
  rcases (Nat.card_eq_two_iff' (1 : A)).mp hA with ⟨z, hzne, hzuniq⟩
  have ha' : (⟨a, ha⟩ : A) ≠ 1 := by
    intro h
    exact hane (congrArg Subtype.val h)
  have hb' : (⟨b, hb⟩ : A) ≠ 1 := by
    intro h
    exact hbne (congrArg Subtype.val h)
  exact congrArg Subtype.val ((hzuniq ⟨a, ha⟩ ha').trans
    (hzuniq ⟨b, hb⟩ hb').symm)

public theorem firstCase_klein_J3_normalizer_even
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hyJ : y ∈ firstCaseJ c 3)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXcard : Nat.card X = 3)
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hXinf : X ⊓ (twoCoreOf c.Hhat ⊔ c.U) = ⊥) :
    Even (Nat.card (Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)) := by
  classical
  have hU3 : Nat.card c.U = 3 :=
    firstCase_klein_U_card_three_pre_b3 hmin c hfirst hklein
  have hXcentU : X ≤ Subgroup.centralizer (c.U : Set G) :=
    firstCase_klein_card_three_subgroup_centralizes_U hmin c hXcard hXle hU3
  let H : Subgroup G := c.Hhat
  let O : Subgroup H := pPrimeCore 2 H
  let q : H →* (H ⧸ O) := QuotientGroup.mk' O
  have hOnormal : O.Normal := by
    dsimp [O, H]
    infer_instance
  obtain ⟨t0, ht0ne0⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hXne)
  have ht0ne : (t0 : G) ≠ 1 := by
    intro ht
    apply ht0ne0
    exact Subtype.ext ht
  let t : G := t0
  have htord : orderOf t = 3 := by
    have hd : orderOf (t0 : G) ∣ Nat.card X :=
      Subgroup.orderOf_dvd_natCard X t0.2
    rw [hXcard] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact False.elim (ht0ne (orderOf_eq_one_iff.mp h1))
    · exact h3
  have hXeq : X = Subgroup.zpowers t := by
    have heq := Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr t0.2) (by
      rw [Nat.card_zpowers, htord, hXcard])
    exact heq.symm
  have hOmap : O.map H.subtype = c.U := by
    dsimp [O, H]
    rw [show c.U = oddCoreOf c.Hhat by exact (theorem_2_6 hmin c).1]
    rfl
  let tH : H := ⟨t, hXle t0.2⟩
  have hqtne : q tH ≠ 1 := by
    intro hq1
    have htO : tH ∈ O := (QuotientGroup.eq_one_iff (N := O) tH).mp hq1
    have htU : t ∈ c.U := by
      have : t ∈ O.map H.subtype := Subgroup.mem_map.mpr ⟨tH, htO, rfl⟩
      simpa [hOmap] using this
    have htVU : t ∈ twoCoreOf c.Hhat ⊔ c.U :=
      (le_sup_right : c.U ≤ twoCoreOf c.Hhat ⊔ c.U) htU
    have htbot : t ∈ X ⊓ (twoCoreOf c.Hhat ⊔ c.U) := ⟨t0.2, htVU⟩
    rw [hXinf] at htbot
    exact ht0ne (Subgroup.mem_bot.mp htbot)
  have hqt3 : (q tH) ^ 3 = 1 := by
    rw [← map_pow]
    have ht3 : t ^ 3 = 1 := by
      rw [← htord]
      exact pow_orderOf_eq_one t
    exact congrArg q (Subtype.ext ht3)
  have hqtord : orderOf (q tH) = 3 := by
    have hd := orderOf_dvd_of_pow_eq_one hqt3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact False.elim (hqtne (orderOf_eq_one_iff.mp h1))
    · exact h3
  let e : (H ⧸ O) ≃* Equiv.Perm (Fin 4) :=
    (firstCase_hhat_quotient_U_s4_of_U_card_three hmin c hfirst hklein hU3).some
  let T4 : Subgroup (Equiv.Perm (Fin 4)) :=
    Subgroup.zpowers (e (q tH))
  have hT4card : Nat.card T4 = 3 := by
    rw [Nat.card_zpowers]
    have heorder : orderOf (e (q tH)) = 3 := by
      exact (MulEquiv.orderOf_eq e (q tH)).trans hqtord
    exact heorder
  obtain ⟨s4, hs4I, hs4N, hs4sign, hs4x⟩ :=
    firstCase_s4_generator_normalizer_odd_involution (e (q tH))
      ((MulEquiv.orderOf_eq e (q tH)).trans hqtord)
  let sQ : H ⧸ O := e.symm s4
  have hsQI : IsInvolution sQ := by
    refine ⟨?_, ?_⟩
    · intro hs1
      apply hs4I.1
      simpa [sQ] using congrArg e hs1
    · apply e.injective
      change e (sQ ^ 2) = e 1
      rw [map_pow, map_one]
      simpa [sQ] using hs4I.2
  have hsQx : sQ * q tH * sQ⁻¹ = (q tH)⁻¹ := by
    apply e.injective
    change e (sQ * q tH * sQ⁻¹) = e ((q tH)⁻¹)
    rw [map_mul, map_mul, map_inv, map_inv]
    simpa [sQ] using hs4x
  have hsQT : sQ ∈ Subgroup.normalizer
      (Subgroup.zpowers (q tH) : Set (H ⧸ O)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      rw [← hn, ← conj_zpow, hsQx]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by simp⟩
    · intro hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      have hback : sQ * (sQ * z * sQ⁻¹) * sQ⁻¹ ∈
          Subgroup.zpowers (q tH) := by
        rw [← hn, ← conj_zpow, hsQx]
        exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by simp⟩
      have hss : sQ * sQ = 1 := by simpa [pow_two] using hsQI.2
      have hsinv : sQ⁻¹ = sQ := inv_eq_of_mul_eq_one_right hss
      have hEq : sQ * (sQ * z * sQ⁻¹) * sQ⁻¹ = z := by
        rw [hsinv]
        calc
          sQ * (sQ * z * sQ) * sQ = (sQ * sQ) * z * (sQ * sQ) := by group
          _ = z := by rw [hss]; simp
      rw [hEq] at hback
      exact hback
  have hsQne : sQ ≠ 1 := by
    intro hs1
    apply hs4I.1
    simpa [sQ] using hs1
  have hsQord : orderOf sQ = 2 := orderOf_eq_prime hsQI.2 hsQne
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective O sQ
  have haQ : q a = sQ := by simpa [q] using ha
  have h2ordera : 2 ∣ orderOf a := by
    rw [← hsQord, ← haQ]
    exact orderOf_map_dvd q a
  let A : Subgroup H := Subgroup.zpowers a
  have h2A : 2 ∣ Nat.card A := by
    simpa [A, Nat.card_zpowers] using h2ordera
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a2, ha2ord⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 h2A
  let hH : H := a2
  have hhord : orderOf hH = 2 := by
    simpa [hH] using (Subgroup.orderOf_coe a2).trans ha2ord
  let hG : G := hH
  have hhordG : orderOf hG = 2 := by
    simpa [hG] using (Subgroup.orderOf_coe hH).trans hhord
  have hhI : IsInvolution hG := by
    refine ⟨?_, ?_⟩
    · intro hh1
      have : orderOf hG = 1 := by simpa [hh1]
      omega
    · rw [← hhordG]
      exact pow_orderOf_eq_one hG
  have hqhmem : q hH ∈ Subgroup.zpowers sQ := by
    rcases Subgroup.mem_zpowers_iff.mp a2.2 with ⟨n, hn⟩
    change q (a2 : H) ∈ Subgroup.zpowers sQ
    rw [← hn, map_zpow, haQ]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers sQ) n
  have hqhne : q hH ≠ 1 := by
    intro hq1
    have hhO : hH ∈ O := (QuotientGroup.eq_one_iff (N := O) hH).mp hq1
    have hdO : orderOf hH ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hhO
    have hOcop : Nat.Coprime 2 (Nat.card O) :=
      pPrimeCore_coprime_card (p := 2) (G := H)
    have hone : 2 = 1 := Nat.eq_one_of_dvd_coprimes hOcop (dvd_refl 2) (by
      rw [hhord] at hdO
      exact hdO)
    norm_num at hone
  have hqheq : q hH = sQ := by
    apply eq_of_mem_card_two_j3 (Subgroup.zpowers sQ)
      (by rw [Nat.card_zpowers, hsQord]) hqhmem
      (Subgroup.mem_zpowers sQ) hqhne hsQne
  have hVnot : hG ∉ twoCoreOf c.Hhat := by
    intro hhV
    let Vh : Subgroup H := pCore 2 H
    have hVmap : Vh.map H.subtype = twoCoreOf c.Hhat := by
      rfl
    have hhV' : hG ∈ Vh.map H.subtype := by simpa [hVmap] using hhV
    rcases Subgroup.mem_map.mp hhV' with ⟨v, hv, hv_eq⟩
    have hvh : v = hH := by
      apply Subtype.ext
      exact hv_eq
    have hqhV : q hH ∈ (Vh.map q) := by
      rw [← hvh]
      exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    have hVhnormal : Vh.Normal := by
      dsimp [Vh]
      infer_instance
    have hVbarNormal : (Vh.map q).Normal :=
      Subgroup.Normal.map hVhnormal q (QuotientGroup.mk'_surjective O)
    have hVhp : IsPGroup 2 Vh := by
      dsimp [Vh]
      exact pCore_isPGroup (G := H) (p := 2)
    have hVbarp : IsPGroup 2 (Vh.map q) := IsPGroup.map hVhp q
    let V4 : Subgroup (Equiv.Perm (Fin 4)) := (Vh.map q).map e.toMonoidHom
    have hV4normal : V4.Normal :=
      Subgroup.Normal.map hVbarNormal e.toMonoidHom e.surjective
    have hV4p : IsPGroup 2 V4 := IsPGroup.map hVbarp e.toMonoidHom
    have hV4A : V4 ≤ alternatingGroup (Fin 4) :=
      normal_two_subgroup_le_alternating_of_perm_four V4 hV4normal hV4p
    have hs4A : s4 ∈ alternatingGroup (Fin 4) := by
      have hs4mem : e (q hH) ∈ V4 :=
        Subgroup.mem_map.mpr ⟨q hH, hqhV, rfl⟩
      have hs4eq : s4 = e (q hH) := by
        calc
          s4 = e sQ := by simp [sQ]
          _ = e (q hH) := by rw [hqheq]
      rw [hs4eq]
      exact hV4A hs4mem
    exact hs4sign (Equiv.Perm.mem_alternatingGroup.mp hs4A)
  obtain ⟨r, hr, hrV⟩ :=
    firstCase_klein_exists_reflection_not_mem_twoCore hmin c hfirst hklein
  obtain ⟨K, _hKr, hKHall, hKne, hKall⟩ :=
    firstCase_klein_uniform_involution_inverted hmin c hfirst hklein r hr hrV
  have hKcard : Nat.card K = 3 :=
    firstCase_klein_K_card_eq_three_of_U_card_three c hKHall hKne hU3
  have hKeq : K = c.U := by
    have hKleU : K ≤ c.U := hKHall.1.trans (fittingSubgroupOf_le c.U)
    have heq := Subgroup.eq_of_le_of_card_ge hKleU (by rw [hKcard, hU3])
    exact heq
  have hhInvU : ∀ u : G, u ∈ c.U → hG * u * hG⁻¹ = u⁻¹ := by
    intro u hu
    have huK : u ∈ K := by rw [hKeq]; exact hu
    have hInvSet := hKall hG hH.2 hhI hVnot
    have huInv : u ∈ invertedElements c.U hG := by
      rw [← hInvSet]
      exact huK
    exact huInv.2
  have hqconj : q (hH * tH * hH⁻¹) = (q tH)⁻¹ := by
    calc
      q (hH * tH * hH⁻¹) = q hH * q tH * (q hH)⁻¹ := by
        simp [map_mul, map_inv]
      _ = sQ * q tH * sQ⁻¹ := by rw [hqheq]
      _ = (q tH)⁻¹ := hsQx
  let uH : H := hH * tH * hH⁻¹ * tH
  have huHO : uH ∈ O := by
    apply (QuotientGroup.eq_one_iff (N := O) uH).mp
    change q (hH * tH * hH⁻¹ * tH) = 1
    rw [map_mul, hqconj]
    simp
  let uG : G := uH
  have huU : uG ∈ c.U := by
    have huMap : uG ∈ O.map H.subtype :=
      Subgroup.mem_map.mpr ⟨uH, huHO, rfl⟩
    simpa [hOmap, uG] using huMap
  have hth : hG * t * hG⁻¹ = uG * t⁻¹ := by
    change (hH : G) * (tH : G) * (hH : G)⁻¹ =
      (uH : G) * (tH : G)⁻¹
    dsimp [uH, uG, tH, t]
    group
  have hconjU : hG * uG * hG = uG⁻¹ := by
    calc
      hG * uG * hG = hG * uG * hG⁻¹ := by rw [show hG⁻¹ = hG by
        exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hhI.2)]
      _ = uG⁻¹ := hhInvU uG huU
  have hTU : t * uG = uG * t := by
    simpa [t] using (Subgroup.mem_centralizer_iff.mp (hXcentU t0.2)) uG huU |>.symm
  have hginv : hG⁻¹ = hG :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hhI.2)
  have hconj_tinv : hG * t⁻¹ * hG = (uG * t⁻¹)⁻¹ := by
    calc
      hG * t⁻¹ * hG = hG * t⁻¹ * hG⁻¹ := by rw [hginv]
      _ = (hG * t * hG⁻¹)⁻¹ := by group
      _ = (uG * t⁻¹)⁻¹ := by rw [hth]
  have hcalc : t = uG⁻¹ * (t * uG⁻¹) := by
    calc
      t = (hG * hG) * t * (hG * hG) := by
        have hss : hG * hG = 1 := by simpa [pow_two] using hhI.2
        simpa [hss]
      _ = hG * (hG * t * hG⁻¹) * hG⁻¹ := by rw [hginv]; group
      _ = hG * (uG * t⁻¹) * hG⁻¹ := by rw [hth]
      _ = hG * (uG * t⁻¹) * hG := by rw [hginv]
      _ = (hG * uG * hG) * (hG * t⁻¹ * hG) := by
        have hss : hG * hG = 1 := by simpa [pow_two] using hhI.2
        have hmid : hG * (uG * t⁻¹) * hG =
            hG * uG * (hG * hG) * t⁻¹ * hG := by
          rw [hss]
          group
        calc
          hG * (uG * t⁻¹) * hG =
              hG * uG * (hG * hG) * t⁻¹ * hG := hmid
          _ = (hG * uG * hG) * (hG * t⁻¹ * hG) := by group
      _ = uG⁻¹ * (t * uG⁻¹) := by
        rw [hconjU, hconj_tinv]
        simp [mul_inv_rev]
  have htuinv : t * uG⁻¹ = uG⁻¹ * t := by
    exact (Commute.eq ((commute_iff_eq _ _).2 hTU).inv_right)
  have hEq : t = t * (uG⁻¹ * uG⁻¹) := by
    calc
      t = uG⁻¹ * (t * uG⁻¹) := hcalc
      _ = (uG⁻¹ * uG⁻¹) * t := by rw [htuinv]; group
      _ = t * (uG⁻¹ * uG⁻¹) := by
        have hc := ((commute_iff_eq _ _).2 hTU).inv_right.pow_right 2
        simpa only [pow_two] using hc.eq.symm
  have huinv2 : uG⁻¹ * uG⁻¹ = 1 := by
    have hh := congrArg (fun z : G => t⁻¹ * z) hEq
    have hh' : 1 = uG⁻¹ * uG⁻¹ := by simpa [mul_assoc] using hh
    exact hh'.symm
  have hu2 : uG ^ 2 = 1 := by
    calc
      uG ^ 2 = (uG⁻¹ * uG⁻¹)⁻¹ := by group
      _ = 1 := by rw [huinv2]; simp
  have huord2 : orderOf uG ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have huordU : orderOf uG ∣ Nat.card c.U :=
    Subgroup.orderOf_dvd_natCard c.U huU
  have huord1 : orderOf uG = 1 := by
    apply Nat.dvd_one.mp
    have hd := Nat.dvd_gcd huord2 huordU
    rw [hU3] at hd
    simpa using hd
  have huone : uG = 1 := orderOf_eq_one_iff.mp huord1
  have hconj_t : hG * t * hG⁻¹ = t⁻¹ := by
    rw [hth, huone]
    simp
  have hhNormX : hG ∈ Subgroup.normalizer (X : Set G) := by
    rw [hXeq, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      rw [← hn, ← conj_zpow, hconj_t]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by simp⟩
    · intro hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      have hback : hG * (hG * z * hG⁻¹) * hG⁻¹ ∈
          Subgroup.zpowers t := by
        rw [← hn, ← conj_zpow, hconj_t]
        exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by simp⟩
      have hEq' : hG * (hG * z * hG⁻¹) * hG⁻¹ = z := by
        rw [hginv]
        calc
          hG * (hG * z * hG) * hG = (hG * hG) * z * (hG * hG) := by group
          _ = z := by
            have hss : hG * hG = 1 := by simpa [pow_two] using hhI.2
            rw [hss]
            simp
      rw [hEq'] at hback
      exact hback
  let N : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ c.Hhat
  have hNmem : hG ∈ N := ⟨hhNormX, hH.2⟩
  exact even_card_of_mem_involution_j3 N hNmem hhI

end CFSG.GorensteinWalter
