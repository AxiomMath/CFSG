module

public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofChoose
import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofSAlt
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1117ResProof

section Group

variable {G : Type} [Group G] [Finite G]

theorem three_mul_card_le_of_lt {P T : Subgroup G} (hTP : T ≤ P) (hP3 : IsPGroup 3 P) {y : G}
    (hyP : y ∈ P) (hyT : y ∉ T) : 3 * Nat.card T ≤ Nat.card P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrel : Nat.card T * T.relIndex P = Nat.card P := by
    have h1 := Subgroup.relIndex_mul_card T P
    rw [inf_of_le_left hTP] at h1
    rw [mul_comm]
    exact h1
  have hrel1 : T.relIndex P ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hyT (h1 hyP)
  have hrel3 : 3 ≤ T.relIndex P := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP3
    have hdvd : T.relIndex P ∣ 3 ^ m := by
      rw [← hm, ← hrel]
      exact Dvd.intro_left _ rfl
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hj] at hrel1 ⊢
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd (pow_zero 3) hrel1
    · calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj0
  calc 3 * Nat.card T ≤ T.relIndex P * Nat.card T := Nat.mul_le_mul_right _ hrel3
    _ = Nat.card P := by rw [mul_comm]; exact hrel

omit [Finite G] in
theorem card_sup_eq_of_inf_eq_bot {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hinf : X ⊓ N = ⊥) :
    Nat.card (X ⊔ N : Subgroup G) = Nat.card X * Nat.card N := by
  have h1 := Sec6.card_sup_mul_card_inf hXN
  rwa [hinf, Subgroup.card_bot, mul_one] at h1

omit [Finite G] in
theorem zpowers_inf_eq_bot {N : Subgroup G} {y : G} (hy3 : y ^ 3 = 1) (hyN : y ∉ N) :
    Subgroup.zpowers y ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, hzN⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [Subgroup.mem_bot]
  by_contra hk
  have h3 : ¬ (3 : ℤ) ∣ k := fun h3 => hk (ActOnA.zpow_eq_one_of_dvd hy3 h3)
  exact hyN (ActOnA.mem_of_zpow_mem hy3 hzN h3)

end Group

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem card_R_le (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    Nat.card R ≤ 9 * orderOf x := by
  have hRle : R ≤ A ⊔ Subgroup.zpowers x := by
    intro y hy
    obtain ⟨m, u, hu, rfl⟩ := Item1117Proof.exists_eq_zpow_mul h hsc hrs hy
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers x m))
      (Subgroup.mem_sup_left hu)
  have hAx : A ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro u hu
    obtain ⟨z, hz, hzu⟩ := Item1117Proof.exists_conj_x_of_mem_A h hu
    refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [hzu]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x)
      (Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_zpowers_x h) hz)
  have hcard := Sec6.card_sup_mul_card_inf hAx
  rw [h.card_eq, Nat.card_zpowers] at hcard
  have h3 : 3 ≤ Nat.card (A ⊓ Subgroup.zpowers x : Subgroup G) := by
    have hle : Subgroup.zpowers d ≤ A ⊓ Subgroup.zpowers x :=
      Subgroup.zpowers_le.mpr ⟨Item1117Proof.d_mem_A h, Item1117Proof.d_mem_zpowers_x h⟩
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, Item1117Proof.orderOf_d h] at this
  have hsup : Nat.card (A ⊔ Subgroup.zpowers x : Subgroup G) ≤ 9 * orderOf x := by
    by_contra hlt
    push Not at hlt
    have h1 : (9 * orderOf x + 1) * 3 ≤ Nat.card (A ⊔ Subgroup.zpowers x : Subgroup G) *
        Nat.card (A ⊓ Subgroup.zpowers x : Subgroup G) := Nat.mul_le_mul hlt h3
    rw [hcard] at h1
    omega
  exact (Subgroup.card_le_of_le hRle).trans hsup

theorem g_pow_three_mem_R (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) : g ^ 3 ∈ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgP := Item1119Proof.g_mem_P R g
  set u := g * c * g⁻¹ * c⁻¹ with hu
  have huD : u ∈ Subgroup.zpowers d := Item1119Proof.conj_c_mul_inv_mem h113 h117 h hgP
  have hgu : g * u = u * g := Item1119Proof.commute_of_mem_zpowers_d h113 h117 h huD hgP
  have hgc : g * c * g⁻¹ = u * c := by rw [hu]; group
  have hu3 : u ^ (3 : ℤ) = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huD
    rw [← hk, ← zpow_mul, mul_comm, zpow_mul, zpow_ofNat,
      (Item1115Proof.d_mem h).2.2, one_zpow]
  have h3 := Item1119Proof.zpow_conj_eq_zpow_mul hgu hgc 3
  rw [hu3, one_mul, zpow_ofNat] at h3
  have hg3H : g ^ 3 ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [h3]
    exact Subgroup.mem_zpowers c
  have hp : IsPGroup 3 (R ⊔ Subgroup.zpowers (g ^ 3) : Subgroup G) :=
    h.isPGroup_sec11P.to_le
      (sup_le le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hgP 3)))
  have hRH : R ⊔ Subgroup.zpowers (g ^ 3) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    sup_le h.isSylowOf.le (Subgroup.zpowers_le.mpr hg3H)
  have heq := h.isSylowOf.eq_of_le le_sup_left hRH hp
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem card_sec11P_le (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) : Nat.card (sec11P R g) ≤ 3 * Nat.card R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgR : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr h.g_mem_normalizer
  have hcard := Sec6.card_sup_mul_card_inf hgR
  have hP : sec11P R g = Subgroup.zpowers g ⊔ R := sup_comm _ _
  have hg3 : g ^ 3 ∈ R := g_pow_three_mem_R h113 h117 h
  have hle : Subgroup.zpowers (g ^ 3) ≤ Subgroup.zpowers g ⊓ R :=
    Subgroup.zpowers_le.mpr ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 3, hg3⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have hg1 : g ≠ 1 := fun h1 => h.g_not_mem (h1 ▸ Subgroup.one_mem _)
  obtain ⟨k, hk⟩ := Item1119Proof.exists_orderOf_eq_three_pow' h.pow_eq_one
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hg1 hk
  have h3g : 3 ∣ orderOf g := by rw [hk]; exact dvd_pow_self 3 hk0
  have hord : orderOf g = 3 * orderOf (g ^ 3) := by
    rw [orderOf_pow_of_dvd (by norm_num) h3g, Nat.mul_div_cancel' h3g]
  rw [Nat.card_zpowers, hord] at hcard
  have hpos : 0 < Nat.card (Subgroup.zpowers g ⊓ R : Subgroup G) := Nat.card_pos
  rw [hP]
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card (Subgroup.zpowers g ⊔ R : Subgroup G) * Nat.card (Subgroup.zpowers g ⊓ R :
        Subgroup G) = 3 * orderOf (g ^ 3) * Nat.card R := hcard
    _ ≤ 3 * Nat.card (Subgroup.zpowers g ⊓ R : Subgroup G) * Nat.card R := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ = 3 * Nat.card R * Nat.card (Subgroup.zpowers g ⊓ R : Subgroup G) := by ring

theorem card_inf_centralizer_le (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {e : G} (he : e ∈ A)
    (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) :
    Nat.card (sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) ≤ 9 * orderOf x := by
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  have hxT : x ∉ sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) := fun hx =>
    Item1117StepsProof.not_commute_x_e h45 h he hecd
      (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
  have h1 := three_mul_card_le_of_lt inf_le_left h.isPGroup_sec11P hxP hxT
  have h2 := card_sec11P_le h113 h117 h
  have h3 := card_R_le h hsc hrs
  omega

theorem x_cube_mem_sec11K (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) {e : G}
    (he : e ∈ A) (hecd : e ∉ Subgroup.closure ({c, d} : Set G)) : x ^ 3 ∈ sec11K L e := by
  obtain ⟨heN, he3, -, hQ, -⟩ :=
    basic_facts_of_conj h45 h.toSec11Std h.inf_eq h.closure_eq he hecd
  have hxL : x ∈ L := by
    have : x ∈ R ⊓ L := by
      rw [h.inf_L_eq]
      exact Subgroup.mem_zpowers x
    exact this.2
  set z := x * e * x⁻¹ * e⁻¹ with hz
  have hzd : z ∈ Subgroup.zpowers d := Item1117StepsProof.conj_x_e_mem h he
  have hxz : x * z = z * x := (Item1117Proof.commute_x_of_mem_zpowers_d h hzd).eq
  have hxe : x * e * x⁻¹ = z * e := by rw [hz]; group
  have hz3 : z ^ (3 : ℤ) = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzd
    rw [← hk, ← zpow_mul, mul_comm, zpow_mul, zpow_ofNat, (Item1115Proof.d_mem h).2.2,
      one_zpow]
  have h3 := Item1119Proof.zpow_conj_eq_zpow_mul hxz hxe 3
  rw [hz3, one_mul, zpow_ofNat] at h3
  have hx3e : x ^ 3 ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 3 * e = (x ^ 3 * e * (x ^ 3)⁻¹) * x ^ 3 := by group
      _ = e * x ^ 3 := by rw [h3]
  obtain ⟨k, hk⟩ := Item1117Proof.x_pow_eq_one h
  exact mem_sec11K_of_pow_eq_one heN he3 hQ.1 ⟨L.pow_mem hxL 3, hx3e⟩ (k := k)
    (by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow])

end Data

end Item1117ResProof

section Main

open Item1117ResProof in
theorem gap1117SwapOut_of (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h113 : Item113)
    (h117 : Item117) : Gap1117SwapOut := by
  intro G _ _ A c L a R Y d x s r g h hsc hrs heA hecd _ Ye R' Y'' hYe hKYe hstd _ _ hQ hbig
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e := g * x * g⁻¹ * x⁻¹ with he
  set T := sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) with hT
  set M := innerPreimage Ye with hM
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hdA := Item1117Proof.d_mem_A h
  obtain ⟨x', s', r', hx', -, hdata⟩ :=
    Item1117StepsProof.exists_sec11Data_swap h45 h97 h113 h117 h hsc hrs heA hecd hYe hKYe hstd hQ
  have hx'card : Nat.card (T ⊓ Ye : Subgroup G) = orderOf x' := by
    rw [hx', Nat.card_zpowers]
  have hcde : c ∉ Subgroup.closure ({e, d} : Set G) := by
    intro hc
    obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair
      (hcomm e heA d hdA) hc
    by_cases h3 : (3 : ℤ) ∣ i
    · apply c_not_mem_closure_a_d h.toSec11Std h.closure_eq hdA
      rw [hij, ActOnA.zpow_eq_one_of_dvd (hexp e heA) h3, one_mul]
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _
    · apply hecd
      refine ActOnA.mem_of_zpow_mem (hexp e heA) ?_ h3
      have e1 : e ^ i = c * (d ^ j)⁻¹ := by rw [hij]; group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _))
  have hx3Ye : x ^ 3 ∈ Ye := hKYe (x_cube_mem_sec11K h45 h heA hecd)
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp
    (Item1117Proof.R_le_centralizer_c h (Item1116Proof.mem_R h).2.1)
  have hx3c : x ^ 3 ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Commute.pow_left hxc 3).eq
  have hx'3 : ∃ k : ℕ, x' ^ 3 ^ k = 1 := by
    have hx'T : x' ∈ T := (hx' ▸ Subgroup.mem_zpowers x' : x' ∈ T ⊓ Ye).1
    exact Item1119Proof.exists_pow_eq_one_of_mem_P h hx'T.1
  obtain ⟨n', hn'⟩ := Item1119Proof.exists_orderOf_eq_three_pow' hx'3
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    rw [hx'card] at hbig
    rw [hn'] at hbig
    norm_num at hbig
  obtain ⟨n, rfl⟩ : ∃ n, n' = n + 1 := ⟨n' - 1, by omega⟩
  obtain ⟨k₀, hk₀⟩ := Item1117Proof.x_pow_eq_one h
  have hx3k : ∃ k : ℕ, (x ^ 3) ^ 3 ^ k = 1 :=
    ⟨k₀, by rw [← pow_mul, mul_comm, pow_mul, hk₀, one_pow]⟩
  have hpow := Item1117StepsProof.pow_eq_one_of_mem_inf_centralizer h45 hdata h.mem_A hcde
    h.mem_thetaComponentsAt (Item1117StepsProof.sec11K_swap_le_L h45 h heA hecd hYe hKYe hstd)
    hn' ⟨hx3Ye, hx3c⟩ hx3k
  have hxx' : orderOf x ≤ orderOf x' := by
    obtain ⟨m, hm⟩ := Item1119Proof.exists_orderOf_eq_three_pow' (Item1117Proof.x_pow_eq_one h)
    have h9 := Item1117Proof.nine_dvd_orderOf_x h
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [hm, pow_zero] at h9
      norm_num at h9
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h3x : 3 ∣ orderOf x := by rw [hm]; exact dvd_pow_self 3 (by omega)
    have hox3 : orderOf (x ^ 3) = 3 ^ m := by
      rw [orderOf_pow_of_dvd (by norm_num) h3x, hm, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [hox3] at hdvd
    have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    rw [hm, hn']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTle : Nat.card T ≤ 9 * orderOf x := card_inf_centralizer_le h45 h113 h117 h hsc hrs heA hecd
  have he1 : e ≠ 1 := fun h1 => hecd (h1 ▸ Subgroup.one_mem _)
  have heYe : e ∉ Ye := by
    intro heY
    have hmem : e ∈ A ⊓ Ye := ⟨heA, heY⟩
    rw [hdata.inf_eq] at hmem
    exact hecd (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hmem)
  have hYeC := Sec6.le_centralizer_of_mem_thetaComponentsAt hYe
  have hAP : A ≤ sec11P R g :=
    (le_R_of_hyp91 h.toHyp91).trans (Item1119Proof.R_le_P R g)
  have hAT : ∀ u ∈ A, u ∈ T := fun u hu =>
    ⟨hAP hu, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm u hu e heA)⟩
  have heM : e ∈ M := Item1118StepsProof.mem_innerPreimage_of_commute fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hYeC hy)).symm
  set N := T ⊓ M with hN
  have heN : Subgroup.zpowers e ≤ Subgroup.normalizer ((T ⊓ Ye : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hAT e heA), ?_⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hYeC hy), mul_inv_cancel_right]
    exact hy
  have heinf : Subgroup.zpowers e ⊓ (T ⊓ Ye) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have := (zpowers_inf_eq_bot (hexp e heA) heYe).le ⟨hz.1, hz.2.2⟩
    exact this
  have hE := card_sup_eq_of_inf_eq_bot heN heinf
  rw [Nat.card_zpowers, orderOf_eq_prime (hexp e heA) he1, hx'card] at hE
  have hEN : Subgroup.zpowers e ⊔ (T ⊓ Ye) ≤ N := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨hAT e heA, heM⟩) ?_
    exact le_inf inf_le_left (inf_le_right.trans (Item1118StepsProof.le_innerPreimage_self Ye))
  have hNcard : 3 * orderOf x' ≤ Nat.card N := hE ▸ Subgroup.card_le_of_le hEN
  have hcM : c ∉ M := hstd.a_not_mem_innerPreimage
  have hcT := hAT c h.mem_A
  have hAYe : A ≤ Subgroup.normalizer (Ye : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe heA he1 Ye hYe
  have hcN : c ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hcT,
      normalizer_le_normalizer_innerPreimage Ye (hAYe h.mem_A)⟩
  have hcinf : Subgroup.zpowers c ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (zpowers_inf_eq_bot (hexp c h.mem_A) hcM).le ⟨hz.1, hz.2.2⟩
  have hS := card_sup_eq_of_inf_eq_bot (Subgroup.zpowers_le.mpr hcN) hcinf
  rw [Nat.card_zpowers, orderOf_eq_prime (hexp c h.mem_A) h.ne_one] at hS
  have hSle : Subgroup.zpowers c ⊔ N ≤ T := sup_le (Subgroup.zpowers_le.mpr hcT) inf_le_left
  have hSeq : Subgroup.zpowers c ⊔ N = T := by
    refine Subgroup.eq_of_le_of_card_ge hSle ?_
    rw [hS]
    omega
  intro y hy
  rw [← hSeq] at hy
  obtain ⟨i, ν, hν, hyi⟩ := Item1119Proof.exists_zpow_mul_of_mem_sup hcN hy
  refine ⟨((-i) % 3).toNat, ?_⟩
  have hc3 : c ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hexp c h.mem_A
  have hci : c ^ ((-i) % 3).toNat = c ^ (-i) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num)),
      ← zpow_eq_zpow_emod _ hc3]
  rw [hci, hyi, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
  exact hν.2

end Main

end CFSG.RankThree.PartTwo.Sec11
