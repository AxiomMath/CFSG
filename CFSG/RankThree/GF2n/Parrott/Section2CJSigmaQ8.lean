module

public import CFSG.RankThree.GF2n.Parrott.Section2Q8Final2
public import CFSG.RankThree.GF2n.Parrott.FixDimIII
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem eq_of_le_of_card_eq_four_mul {N S T : Subgroup G} (hNS : N ≤ S) (hST : S ≤ T)
    (hcard : Nat.card T = 4 * Nat.card N) {a b : G} (ha : a ∈ S) (hb : b ∈ S) (haN : a ∉ N)
    (hbN : b ∉ N) (habN : a⁻¹ * b ∉ N) : S = T := by
  classical
  let N' : Subgroup S := N.subgroupOf S
  have hN' : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv
  have hS := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  have e : ∀ s t : S, (QuotientGroup.mk s : S ⧸ N') = QuotientGroup.mk t ↔
      (s : G)⁻¹ * (t : G) ∈ N := fun s t => by
    rw [QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf
  have hne01 : (QuotientGroup.mk 1 : S ⧸ N') ≠ QuotientGroup.mk ⟨a, ha⟩ := by
    rw [Ne, e]
    simpa using haN
  have hne02 : (QuotientGroup.mk 1 : S ⧸ N') ≠ QuotientGroup.mk ⟨b, hb⟩ := by
    rw [Ne, e]
    simpa using hbN
  have hne12 : (QuotientGroup.mk ⟨a, ha⟩ : S ⧸ N') ≠ QuotientGroup.mk ⟨b, hb⟩ := by
    rw [Ne, e]
    exact habN
  have h3 : 3 ≤ Nat.card (S ⧸ N') := by
    have : Fintype (S ⧸ N') := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    have hc3 : ({QuotientGroup.mk 1, QuotientGroup.mk ⟨a, ha⟩, QuotientGroup.mk ⟨b, hb⟩} :
        Finset (S ⧸ N')).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne01, hne02]), Finset.card_pair hne12]
    calc 3 = _ := hc3.symm
      _ ≤ Fintype.card (S ⧸ N') := Finset.card_le_univ _
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hdvd : Nat.card S ∣ Nat.card T := Subgroup.card_dvd_of_le hST
  rw [hcard] at hdvd
  have hge : 3 * Nat.card N ≤ Nat.card S := by
    rw [hS, hN']
    exact Nat.mul_le_mul_right _ h3
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : m = 1 := by
    by_contra hm1
    rcases Nat.lt_or_gt_of_ne hm1 with hlt | hgt
    · have hm0 : m = 0 := by omega
      rw [hm0, mul_zero] at hm
      omega
    · have h2 : Nat.card S * 2 ≤ Nat.card S * m := Nat.mul_le_mul_left _ hgt
      omega
  rw [hm1, mul_one] at hm
  exact Subgroup.eq_of_le_of_card_ge hST (by rw [hcard, hm])

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem mem_centerIn_J_of_commute_CJ (h : Tim79a.ParrottHyp z) {x : ↥(H z)} (hx3 : x ^ 3 = 1)
    (hZx : conjZ z x = 1) {y : G} (hy : y ∈ CJ z (x : G))
    (hcomm : ∀ c ∈ CJ z (x : G), c * y = y * c) : y ∈ centerIn (J z) := by
  obtain ⟨hyx, hyJ⟩ := mem_CJ.mp hy
  refine ⟨hyJ, (pi_mem_radical_iff h ⟨y, hyJ⟩).mp fun w => ?_⟩
  have hv : conjV h x (QuotientV.pi z ⟨y, hyJ⟩) = QuotientV.pi z ⟨y, hyJ⟩ := by
    rw [conjV_mk]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hxy : (x : G) * y = y * (x : G) := (Subgroup.mem_centralizer_singleton_iff.mp hyx).symm
    calc (x : G) * y * (x : G)⁻¹ = y * (x : G) * (x : G)⁻¹ := by rw [hxy]
      _ = y := by group
  have hcommV : ∀ u v : QuotientV.V z, u * v = v * u :=
    (QuotientV.isMulCommutative_V h).is_comm.comm
  have hx3w : conjV h x (conjV h x (conjV h x w)) = w := by
    have hh := congrArg (fun τ : MulAut (QuotientV.V z) => τ w)
      (show conjV h x ^ 3 = 1 by rw [← map_pow, hx3, map_one])
    simpa [pow_succ, MulAut.mul_apply] using hh
  have htr : conjV h x (w * conjV h x w * conjV h x (conjV h x w)) =
      w * conjV h x w * conjV h x (conjV h x w) := by
    rw [map_mul, map_mul, hx3w]
    calc conjV h x w * conjV h x (conjV h x w) * w
        = w * (conjV h x w * conjV h x (conjV h x w)) := hcommV _ _
      _ = w * conjV h x w * conjV h x (conjV h x w) := by rw [mul_assoc]
  have hbw : polarVZMod h (QuotientV.pi z ⟨y, hyJ⟩) (conjV h x w) =
      polarVZMod h (QuotientV.pi z ⟨y, hyJ⟩) w :=
    polarVZMod_conj_eq_of_fixed h hv w
  have hbw2 : polarVZMod h (QuotientV.pi z ⟨y, hyJ⟩) (conjV h x (conjV h x w)) =
      polarVZMod h (QuotientV.pi z ⟨y, hyJ⟩) w := by
    rw [polarVZMod_conj_eq_of_fixed h hv (conjV h x w), hbw]
  have htrb : polarVZMod h (QuotientV.pi z ⟨y, hyJ⟩)
      (w * conjV h x w * conjV h x (conjV h x w)) = polarVZMod h (QuotientV.pi z ⟨y, hyJ⟩) w := by
    rw [polarVZMod_add_right, polarVZMod_add_right, hbw, hbw2]
    exact (by decide : ∀ a : ZMod 2, a + a + a = a) _
  obtain ⟨j', hj'⟩ := QuotientV.pi_surjective z (w * conjV h x w * conjV h x (conjV h x w))
  have hj'cent : j' ∈ centralizerJ x :=
    mem_centralizerJ_of_conjV_pi_eq h hx3 hZx (by rw [hj']; exact htr)
  have hj'CJ : (j' : G) ∈ CJ z (x : G) :=
    mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hj'cent),
      j'.2⟩
  rw [← htrb, ← hj']
  exact (polarVZMod_pi_eq_zero_iff h ⟨y, hyJ⟩ j').mpr (hcomm _ hj'CJ).symm

private theorem CJ_sigma1Nine_le_CJ_mul_inv {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    CJ z (sigma1Nine (z := z) D : G) ≤ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
  intro y hy
  obtain ⟨hy1, hyJ⟩ := mem_CJ.mp hy
  have h1 : Commute y ((sigma1Nine (z := z) D : ↥(H z)) : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hy1
  have h2' : (⟨y, hyJ⟩ : ↥(J z)) ∈ centralizerJ σ₂ := by
    rw [← hEq]
    exact mem_centralizerJ_iff.mpr h1
  have h2 : Commute y (σ₂ : G) := mem_centralizerJ_iff.mp h2'
  refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hyJ⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (h1.mul_right h2.inv_right).eq

theorem commute_of_mem_CJ_sigma1Nine_of_mem_commutator (h : Tim79a.ParrottHyp z)
    {a b : G} (ha : a ∈ CJ z (sigma1Nine (z := z) D : G))
    (hb : b ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    a * b = b * a := by
  have hb1 : b ∈ J1sub (z := z) (D := D) h := by
    rw [J1sub]
    exact Subgroup.mem_sup_left hb
  rw [← centralizer_centralizerJ_eq_J1sub (z := z) (D := D) h] at hb1
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb1
  obtain ⟨ha1, haJ⟩ := mem_CJ.mp ha
  have haC : (⟨a, haJ⟩ : ↥(J z)) ∈ centralizerJ (sigma1Nine (z := z) D) :=
    mem_centralizerJ_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp ha1)
  have := Subgroup.mem_centralizer_iff.mp hb' _ haC
  exact congrArg Subtype.val this

theorem exists_mul_eq_of_mem_CJ_mul_inv (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {c : G}
    (hc : c ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) :
    ∃ q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆,
      ∃ a ∈ CJ z (sigma1Nine (z := z) D : G), q * a = c := by
  let P : Subgroup G := ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆
  let A : Subgroup G := CJ z (sigma1Nine (z := z) D : G)
  have hAN : A ≤ Subgroup.normalizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      rw [commute_of_mem_CJ_sigma1Nine_of_mem_commutator (z := z) D h ha hp,
        mul_inv_cancel_right]
      exact hp
    · intro hp
      have hc := commute_of_mem_CJ_sigma1Nine_of_mem_commutator (z := z) D h ha hp
      have hp' : p = a * p * a⁻¹ := by
        calc p = a⁻¹ * (a * p * a⁻¹) * a := by group
          _ = a⁻¹ * (a * (a * p * a⁻¹)) := by rw [mul_assoc, ← hc]
          _ = a * p * a⁻¹ := by group
      rw [hp']
      exact hp
  have hcJ : c ∈ J z := (mem_CJ.mp hc).2
  have hJ := J_eq_centralizer_commutator_sigma1Nine (z := z) h D
  have hcPA : c ∈ P ⊔ A := by
    have : c ∈ (J z ⊓ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G)) ⊔ P := by
      rw [← hJ]
      exact hcJ
    rwa [sup_comm, inf_comm] at this
  obtain ⟨p, hpP, a, haA, hpa⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := P) (K := A) hAN).mp hcPA
  have haσ : a ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) :=
    CJ_sigma1Nine_le_CJ_mul_inv (z := z) D hEq haA
  have hpσ : p ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
    have hp_eq : p = c * a⁻¹ := by rw [hpa]; group
    rw [hp_eq]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ haσ)
  exact ⟨p, ⟨hpσ, hpP⟩, a, haA, hpa.symm⟩

theorem card_CJ_mul_inv_inf_commutator (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Nat.card ↥(CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) = 8 := by
  have h8 := card_CJcomm_sigma1sigma2inv_eq_eight_final (z := z) (D := D) h hEq hσ₂ hq₂
    hcomm.eq.symm
  rw [← h8]
  let C : Subgroup G := CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆
  have hCJ : C ≤ J z := inf_le_left.trans inf_le_right
  have heq : CJcomm (z := z) (D := D) (sigma1Nine (z := z) D * σ₂⁻¹) = C.subgroupOf (J z) := by
    ext j
    simp only [CJcomm, centralizerJ, Subgroup.mem_inf, Subgroup.mem_subgroupOf, C, CJ]
  rw [heq]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCJ).toEquiv).symm

theorem mem_zpowers_of_conj_mul_inv_mem_zpowers (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) {q : G}
    (hqσ : q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hqP : q ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆)
    (hω : ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * q *
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹ * q⁻¹ ∈ Subgroup.zpowers z) :
    q ∈ Subgroup.zpowers z := by
  set a : G := ((sigma1Nine (z := z) D : ↥(H z)) : G) with ha_def
  set b : G := (σ₂ : G) with hb_def
  have hab : a * b = b * a := congrArg Subtype.val hcomm.eq
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one (sigma1Nine (z := z) D)
    rw [sigma1Nine_order] at this
    simpa [ha_def] using congrArg Subtype.val this
  obtain ⟨hqs, hqJ⟩ := mem_CJ.mp hqσ
  have hqs' : q * (a * b⁻¹) = (a * b⁻¹) * q := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hqs
    simpa [ha_def, hb_def] using this
  set c : G := (a * b) * q * (a * b)⁻¹ * q⁻¹ with hc_def
  have hω' : c ∈ Subgroup.zpowers z := hω
  have hcH : ∀ g ∈ H z, g * c = c * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hω')) g hg
  have hcc : c * c = 1 := sq_eq_one_of_mem_zpowers h hω'
  have haH : a ∈ H z := (sigma1Nine (z := z) D).2
  have hca : a * c = c * a := hcH a haH
  have h2 : a * a * q * (a * a)⁻¹ = c * q := by
    have e1 : a * a = (a * b) * (a * b⁻¹) := by
      calc a * a = a * (b * b⁻¹) * a := by group
        _ = a * b * (b⁻¹ * a) := by group
        _ = a * b * (a * b⁻¹) := by
          rw [show b⁻¹ * a = a * b⁻¹ by
            calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
              _ = b⁻¹ * (b * a) * b⁻¹ := by rw [hab]
              _ = a * b⁻¹ := by group]
    rw [e1]
    calc (a * b) * (a * b⁻¹) * q * ((a * b) * (a * b⁻¹))⁻¹
        = (a * b) * ((a * b⁻¹) * q * (a * b⁻¹)⁻¹) * (a * b)⁻¹ := by group
      _ = (a * b) * q * (a * b)⁻¹ := by rw [← hqs']; group
      _ = c * q := by rw [hc_def]; group
  have h1 : a * q * a⁻¹ = q := by
    have e4 : a = a * a * (a * a) := by
      calc a = a ^ 3 * a := by rw [ha3, one_mul]
        _ = a * a * (a * a) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    calc a * q * a⁻¹ = (a * a) * ((a * a) * q * (a * a)⁻¹) * (a * a)⁻¹ := by
          conv_lhs => rw [e4]
          group
      _ = (a * a) * (c * q) * (a * a)⁻¹ := by rw [h2]
      _ = c * ((a * a) * q * (a * a)⁻¹) := by
          have hcaa : (a * a) * c = c * (a * a) := hcH (a * a) ((H z).mul_mem haH haH)
          calc (a * a) * (c * q) * (a * a)⁻¹ = ((a * a) * c) * q * (a * a)⁻¹ := by group
            _ = (c * (a * a)) * q * (a * a)⁻¹ := by rw [hcaa]
            _ = c * ((a * a) * q * (a * a)⁻¹) := by group
      _ = c * (c * q) := by rw [h2]
      _ = q := by rw [← mul_assoc, hcc, one_mul]
  have hqA : q ∈ (J z ⊓ Subgroup.centralizer ({a} : Set G)) ⊓
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
    refine ⟨⟨hqJ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hqP⟩
    calc q * a = a * q * a⁻¹ * a := by rw [h1]
      _ = a * q := by group
  rw [centralizer_inf_commutator_eq_sigma1Nine (z := z) h D] at hqA
  exact hqA

theorem exists_not_commute_of_mem_CJ_mul_inv_inf_commutator (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    ∃ r₁ ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆,
      ∃ r₂ ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆,
      r₁ * r₂ ≠ r₂ * r₁ := by
  by_contra hab
  push Not at hab
  set Q : Subgroup G := CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ with hQ
  have hσ3 : (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1 := by
    have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]; exact pow_orderOf_eq_one _
    have h2 : σ₂ ^ 3 = 1 := by rw [← hσ₂]; exact pow_orderOf_eq_one _
    rw [(hcomm.inv_right).mul_pow, h1, inv_pow, h2, inv_one, one_mul]
  have hZσ : conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
    rw [map_mul, map_inv, conjZ_sigma1Nine h D, conjZ_eq_one_of_qH_eq_sigma2 D h hq₂, inv_one,
      mul_one]
  have hle : Q ≤ Subgroup.zpowers z := by
    intro q hq
    have hqZ : q ∈ centerIn (J z) := by
      refine mem_centerIn_J_of_commute_CJ h hσ3 hZσ hq.1 fun c hc => ?_
      obtain ⟨q', hq', a, ha, rfl⟩ := exists_mul_eq_of_mem_CJ_mul_inv (z := z) D h hEq hc
      have haq : a * q = q * a :=
        commute_of_mem_CJ_sigma1Nine_of_mem_commutator (z := z) D h ha hq.2
      calc q' * a * q = q' * (a * q) := by group
        _ = q' * (q * a) := by rw [haq]
        _ = (q' * q) * a := by group
        _ = (q * q') * a := by rw [hab q' hq' q hq]
        _ = q * (q' * a) := by group
    have hqA : q ∈ (J z ⊓ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G)) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ :=
      ⟨⟨hqZ.1, centerIn_le_centralizer_of_conjZ_eq_one (z := z) (conjZ_sigma1Nine h D) hqZ⟩,
        hq.2⟩
    rwa [centralizer_inf_commutator_eq_sigma1Nine (z := z) h D] at hqA
  have h8 := card_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq
  have h2 : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, h.1]
  have := Subgroup.card_le_of_le hle
  rw [← hQ] at h8
  omega

theorem mul_self_eq_of_mem_CJ_mul_inv_inf_commutator (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {q : G}
    (hq : q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆)
    (hqz : q ∉ Subgroup.zpowers z) : q * q = z := by
  classical
  set Q : Subgroup G := CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ with hQ
  set ω : ↥(H z) := sigma1Nine (z := z) D * σ₂ with hω_def
  set σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hσ_def
  have hz2 : orderOf z = 2 := h.1
  have hz1 : z ≠ 1 := by
    intro hz
    rw [hz, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzJ : z ∈ J z := z_mem_J h
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  have hsq : ∀ r ∈ J z, r * r ∈ Subgroup.zpowers z := fun r hr => sq_mem_zpowers_z h hr
  have hcomJ : ∀ r₁ ∈ J z, ∀ r₂ ∈ J z, r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ Subgroup.zpowers z := by
    intro r₁ hr₁ r₂ hr₂
    rw [← h.2.2.1]
    have := Subgroup.commutator_mem_commutator hr₁ hr₂
    rwa [commutatorElement_def] at this
  have hQJ : ∀ r ∈ Q, r ∈ J z := fun r hr => (mem_CJ.mp hr.1).2
  have hQH : ∀ r ∈ Q, r ∈ H z := fun r hr => J_le_H (hQJ r hr)
  have hzQ : z ∈ Q := by
    have hzA : z ∈ (J z ⊓ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G)) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      rw [centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
      exact Subgroup.mem_zpowers z
    refine ⟨mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hzJ⟩, hzA.2⟩
    exact (hcent z (Subgroup.mem_zpowers z) _ σ.2).symm
  have hzpQ : Subgroup.zpowers z ≤ Q := Subgroup.zpowers_le_of_mem hzQ
  have hQcard : Nat.card Q = 4 * Nat.card (Subgroup.zpowers z) := by
    rw [hQ, card_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq, Nat.card_zpowers, hz2]
  have hωσ : (ω : G) * (σ : G) = (σ : G) * (ω : G) := by
    have hc : Commute ω σ := by
      rw [hω_def, hσ_def]
      exact Commute.mul_left ((Commute.refl _).mul_right hcomm.inv_right)
        (hcomm.symm.mul_right (Commute.refl _).inv_right)
    exact congrArg Subtype.val hc.eq
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hωQ : ∀ r ∈ Q, (ω : G) * r * (ω : G)⁻¹ ∈ Q := by
    intro r hr
    obtain ⟨hrσ, hrJ⟩ := mem_CJ.mp hr.1
    refine ⟨mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      (Subgroup.mem_normalizer_iff.mp (hHN ω.2) r).mp hrJ⟩,
      commutator_sigma1Nine_conj_mem (z := z) (D := D) h hEq hσ₂ hq₂ hcomm.eq.symm ω r hr.2⟩
    have hrσ' : r * (σ : G) = (σ : G) * r := Subgroup.mem_centralizer_singleton_iff.mp hrσ
    calc (ω : G) * r * (ω : G)⁻¹ * (σ : G) = (ω : G) * r * ((ω : G)⁻¹ * (σ : G)) := by group
      _ = (ω : G) * r * ((σ : G) * (ω : G)⁻¹) := by
          rw [show (ω : G)⁻¹ * (σ : G) = (σ : G) * (ω : G)⁻¹ by
            calc (ω : G)⁻¹ * (σ : G) = (ω : G)⁻¹ * ((σ : G) * (ω : G)) * (ω : G)⁻¹ := by group
              _ = (ω : G)⁻¹ * ((ω : G) * (σ : G)) * (ω : G)⁻¹ := by rw [hωσ]
              _ = (σ : G) * (ω : G)⁻¹ := by group]
      _ = (ω : G) * (r * (σ : G)) * (ω : G)⁻¹ := by group
      _ = (ω : G) * ((σ : G) * r) * (ω : G)⁻¹ := by rw [hrσ']
      _ = ((ω : G) * (σ : G)) * r * (ω : G)⁻¹ := by group
      _ = (σ : G) * ((ω : G) * r * (ω : G)⁻¹) := by rw [hωσ]; group
  have hω3 : (ω : G) ^ 3 = 1 := by
    have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]; exact pow_orderOf_eq_one _
    have h2 : σ₂ ^ 3 = 1 := by rw [← hσ₂]; exact pow_orderOf_eq_one _
    have : ω ^ 3 = 1 := by rw [hω_def, hcomm.mul_pow, h1, h2, one_mul]
    simpa using congrArg Subtype.val this
  have hfpf : ∀ r ∈ Q, (ω : G) * r * (ω : G)⁻¹ * r⁻¹ ∈ Subgroup.zpowers z →
      r ∈ Subgroup.zpowers z := fun r hr hωr =>
    mem_zpowers_of_conj_mul_inv_mem_zpowers (z := z) D h hcomm hr.1 hr.2 hωr
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp (hsq q (hQJ q hq)) with hq1 | hqq
  swap
  · exact hqq
  exfalso
  set q₂ : G := (ω : G) * q * (ω : G)⁻¹ with hq₂_def
  set q₃ : G := (ω : G) * q₂ * (ω : G)⁻¹ with hq₃_def
  have hq₂Q : q₂ ∈ Q := hωQ q hq
  have hq₃Q : q₃ ∈ Q := hωQ q₂ hq₂Q
  have hq₂1 : q₂ * q₂ = 1 := by
    calc q₂ * q₂ = (ω : G) * (q * q) * (ω : G)⁻¹ := by rw [hq₂_def]; group
      _ = 1 := by rw [hq1]; group
  have hq₃1 : q₃ * q₃ = 1 := by
    calc q₃ * q₃ = (ω : G) * (q₂ * q₂) * (ω : G)⁻¹ := by rw [hq₃_def]; group
      _ = 1 := by rw [hq₂1]; group
  have hq₂z : q₂ ∉ Subgroup.zpowers z := by
    intro hq₂z
    apply hqz
    have : q = (ω : G)⁻¹ * q₂ * (ω : G) := by rw [hq₂_def]; group
    rw [this, hcent q₂ hq₂z _ (inv_mem ω.2), mul_assoc, inv_mul_cancel, mul_one]
    exact hq₂z
  have hqq₂ : q⁻¹ * q₂ ∉ Subgroup.zpowers z := by
    intro hm
    apply hqz
    apply hfpf q hq
    have e : (ω : G) * q * (ω : G)⁻¹ * q⁻¹ = q * (q⁻¹ * q₂) * q⁻¹ := by rw [hq₂_def]; group
    rw [e, hcent _ hm q (hQH q hq), mul_assoc, mul_inv_cancel, mul_one]
    exact hm
  by_cases hc : q * q₂ = q₂ * q
  ·
    obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ :=
      exists_not_commute_of_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq
    rw [← hQ] at hr₁ hr₂
    let C1 : Subgroup G := Q ⊓ Subgroup.centralizer ({q} : Set G)
    let C2 : Subgroup G := Q ⊓ Subgroup.centralizer ({q₂} : Set G)
    have hzC : ∀ x : G, Subgroup.zpowers z ≤ Q ⊓ Subgroup.centralizer ({x} : Set G) ∨
        x ∉ H z := by
      intro x
      by_cases hx : x ∈ H z
      · left
        intro w hw
        exact ⟨hzpQ hw, Subgroup.mem_centralizer_singleton_iff.mpr (hcent w hw x hx).symm⟩
      · right; exact hx
    have hC1 : C1 = Q := by
      have hle : Subgroup.zpowers z ≤ C1 := by
        rcases hzC q with h' | h'
        · exact h'
        · exact absurd (hQH q hq) h'
      refine eq_of_le_of_card_eq_four_mul hle inf_le_left hQcard
        (a := q) (b := q₂) ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
        ⟨hq₂Q, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩ hqz hq₂z hqq₂
    have hC2 : C2 = Q := by
      have hle : Subgroup.zpowers z ≤ C2 := by
        rcases hzC q₂ with h' | h'
        · exact h'
        · exact absurd (hQH q₂ hq₂Q) h'
      refine eq_of_le_of_card_eq_four_mul hle inf_le_left hQcard
        (a := q) (b := q₂) ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
        ⟨hq₂Q, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ hqz hq₂z hqq₂
    let C3 : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
    have hC3 : C3 = Q := by
      have hle : Subgroup.zpowers z ≤ C3 := by
        intro w hw
        refine ⟨hzpQ hw, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
        exact hcent w hw r (hQH r hr)
      have hqC3 : q ∈ C3 := by
        refine ⟨hq, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
        have : r ∈ C1 := by rw [hC1]; exact hr
        exact Subgroup.mem_centralizer_singleton_iff.mp this.2
      have hq₂C3 : q₂ ∈ C3 := by
        refine ⟨hq₂Q, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
        have : r ∈ C2 := by rw [hC2]; exact hr
        exact Subgroup.mem_centralizer_singleton_iff.mp this.2
      exact eq_of_le_of_card_eq_four_mul hle inf_le_left hQcard hqC3 hq₂C3 hqz hq₂z hqq₂
    have : r₂ ∈ C3 := by rw [hC3]; exact hr₂
    exact hne (Subgroup.mem_centralizer_iff.mp this.2 r₁ hr₁)
  ·
    have hk : q * q₂ * q⁻¹ * q₂⁻¹ = z := by
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp
          (hcomJ q (hQJ q hq) q₂ (hQJ q₂ hq₂Q)) with hk | hk
      · exfalso
        apply hc
        calc q * q₂ = q * q₂ * q⁻¹ * q₂⁻¹ * (q₂ * q) := by group
          _ = q₂ * q := by rw [hk, one_mul]
      · exact hk
    have hzz : z * z = 1 := sq_eq_one_of_mem_zpowers h (Subgroup.mem_zpowers z)
    have hzq : ∀ r ∈ J z, z * r = r * z := fun r hr => (hcent z (Subgroup.mem_zpowers z) r
      (J_le_H hr)).symm
    have hqq2 : (q * q₂) * (q * q₂) = z := by
      have e1 : q * q₂ = z * (q₂ * q) := by rw [← hk]; group
      calc (q * q₂) * (q * q₂) = q * q₂ * (z * (q₂ * q)) := by rw [← e1]
        _ = z * (q * (q₂ * q₂) * q) := by
            rw [show q * q₂ * (z * (q₂ * q)) = q * q₂ * z * q₂ * q by group,
              show q * q₂ * z = z * (q * q₂) by
                rw [← hzq _ (mul_mem (hQJ q hq) (hQJ q₂ hq₂Q))]]
            group
        _ = z := by rw [hq₂1, mul_one, hq1, mul_one]
    have hω3' : (ω : G) * (ω : G) * (ω : G) = 1 := by rw [← pow_three']; exact hω3
    have hq₄ : (ω : G) * q₃ * (ω : G)⁻¹ = q := by
      rw [hq₃_def, hq₂_def]
      calc (ω : G) * ((ω : G) * ((ω : G) * q * (ω : G)⁻¹) * (ω : G)⁻¹) * (ω : G)⁻¹
          = ((ω : G) * (ω : G) * (ω : G)) * q * ((ω : G) * (ω : G) * (ω : G))⁻¹ := by group
        _ = q := by rw [hω3']; group
    have hrQ : q * q₂ * q₃ ∈ Q := mul_mem (mul_mem hq hq₂Q) hq₃Q
    have hr : q * q₂ * q₃ ∈ Subgroup.zpowers z := by
      apply hfpf _ hrQ
      have e : (ω : G) * (q * q₂ * q₃) * (ω : G)⁻¹ = q₂ * q₃ * q := by
        calc (ω : G) * (q * q₂ * q₃) * (ω : G)⁻¹
            = ((ω : G) * q * (ω : G)⁻¹) * ((ω : G) * q₂ * (ω : G)⁻¹) *
                ((ω : G) * q₃ * (ω : G)⁻¹) := by group
          _ = q₂ * q₃ * q := by rw [← hq₂_def, ← hq₃_def, hq₄]
      rw [e]
      have := hcomJ (q₂ * q₃) (mul_mem (hQJ q₂ hq₂Q) (hQJ q₃ hq₃Q)) q (hQJ q hq)
      have e2 : q₂ * q₃ * q * (q * q₂ * q₃)⁻¹ = q₂ * q₃ * q * (q₂ * q₃)⁻¹ * q⁻¹ := by group
      rw [e2]
      exact this
    have hrc : ∀ g ∈ H z, g * (q * q₂ * q₃) = (q * q₂ * q₃) * g := fun g hg => hcent _ hr g hg
    have hrr : (q * q₂ * q₃) * (q * q₂ * q₃) = 1 := sq_eq_one_of_mem_zpowers h hr
    have hq₃e : q₃ = (q * q₂)⁻¹ * (q * q₂ * q₃) := by group
    have : q₃ * q₃ = z := by
      have hqH : (q * q₂)⁻¹ ∈ H z := inv_mem (mul_mem (hQH q hq) (hQH q₂ hq₂Q))
      calc q₃ * q₃ = (q * q₂)⁻¹ * (q * q₂ * q₃) * ((q * q₂)⁻¹ * (q * q₂ * q₃)) := by
            rw [← hq₃e]
        _ = (q * q₂)⁻¹ * ((q * q₂ * q₃) * (q * q₂)⁻¹) * (q * q₂ * q₃) := by group
        _ = (q * q₂)⁻¹ * ((q * q₂)⁻¹ * (q * q₂ * q₃)) * (q * q₂ * q₃) := by
            rw [hrc _ hqH]
        _ = ((q * q₂) * (q * q₂))⁻¹ * ((q * q₂ * q₃) * (q * q₂ * q₃)) := by group
        _ = z := by rw [hqq2, hrr, mul_one, inv_eq_of_mul_eq_one_right hzz]
    rw [hq₃1] at this
    exact hz1 this.symm

end CFSG.RankThree.GF2n.Parrott
