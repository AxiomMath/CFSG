module

public import CFSG.RankThree.GF2n.Parrott.Section5Lemma53
public import CFSG.RankThree.GF2n.Parrott.Section2CJ
public import CFSG.RankThree.GF2n.Parrott.QA45SigmaCentralizers
public import CFSG.RankThree.GF2n.Parrott.CentralizerOrders
public import CFSG.RankThree.GF2n.Parrott.FixDimIII
public import CFSG.GroupTheory.ConjOrderThree
public import CFSG.RankThree.PartTwo.Sec10.Item103
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem factorization_two_of_eq_two_pow_mul_odd {k m : ℕ} (hm0 : m ≠ 0)
    (hm : ¬ 2 ∣ m) : Nat.factorization (2 ^ k * m) 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero k (by norm_num)) hm0]
  change (Nat.factorization (2 ^ k) + Nat.factorization m) 2 = k
  rw [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

private theorem inf_centralizer_eq_map_centralizer (y : H z) :
    H z ⊓ Subgroup.centralizer ({(y : G)} : Set G) =
      (Subgroup.centralizer ({y} : Set ↥(H z))).map (H z).subtype := by
  ext g
  constructor
  · rintro ⟨hgH, hgC⟩
    refine Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    simpa using Subgroup.mem_centralizer_singleton_iff.mp hgC
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hh))⟩

private theorem center_subgroupOf_le_centralizerJ_of_conjZ_eq_one {x : H z}
    (hx : conjZ z x = 1) : Subgroup.center (J z) ≤ centralizerJ x := by
  intro j hj
  rw [mem_centralizerJ_iff]
  have hjZ : (j : G) ∈ centerIn (J z) := by
    have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
      rwa [QuotientV.centerIn_subgroupOf_eq_center]
    exact Subgroup.mem_subgroupOf.mp hj'
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := x) hx hjZ)

private theorem card_centralizerJ_inf_center_eq_four_of_conjZ_eq_one (h : Tim79a.ParrottHyp z)
    {x : H z} (hx : conjZ z x = 1) :
    Nat.card ↥(centralizerJ x ⊓ Subgroup.center (J z)) = 4 := by
  rw [inf_eq_right.mpr (center_subgroupOf_le_centralizerJ_of_conjZ_eq_one (z := z) hx)]
  exact card_center_subgroupOf_J (z := z) h

private theorem card_centralizerJ_eq_four_mul_two_pow_fixDim_of_conjZ
    (h : Tim79a.ParrottHyp z) {x : H z} (hx3 : orderOf x = 3) (hxZ : conjZ z x = 1) :
    Nat.card (centralizerJ x) = 4 * 2 ^ fixDimV h x := by
  rw [card_centralizerJ_eq_card_inf_mul_card_pow_fixDim_of_orderOf_eq_three
    (z := z) (h := h) (x := x) hx3,
    card_centralizerJ_inf_center_eq_four_of_conjZ_eq_one (z := z) h hxZ]

private theorem card_centralizer_eq_card_centralizerJ_mul_card_centralizer_QA45
    {x : H z} (hx3 : orderOf x = 3) {q : QA45.originalSubgroup} (hq : qH D x = q) :
    Nat.card (Subgroup.centralizer ({x} : Set ↥(H z))) =
      Nat.card (centralizerJ x) *
        Nat.card (Subgroup.centralizer ({q} : Set QA45.originalSubgroup)) := by
  have hx3P : IsPGroup 3 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx3]
    norm_num
  have hmain := CFSG.card_centralizer_eq_card_inf_mul_card_quotient
    (G := ↥(H z)) (p := 3) (N := (J z).subgroupOf (H z)) (x := x) hx3P
    (coprime_three_card_J_subgroupOf (z := z))
  rw [hmain, card_centralizer_quotient_eq (D := D) x, hq,
    card_centralizer_inf_J_subgroupOf (z := z) (x := x)]

private theorem qH_mul_sigma2_inv_eq {σ₂ : H z}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    qH D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : QA45.originalSubgroup) := by
  rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  rfl

private theorem qH_mul_sigma2_eq {σ₂ : H z}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    qH D (sigma1Nine (z := z) D * σ₂) =
      (⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩ : QA45.originalSubgroup) := by
  rw [map_mul, qH_sigma1Nine, hq₂]
  rfl

private theorem conjZ_sigma2_of_qH (h : Tim79a.ParrottHyp z) {σ₂ : H z}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z σ₂ = 1 :=
  conjZ_eq_one_of_mem_Q (z := z) D h σ₂
    (Subgroup.mem_subgroupOf.mpr (by rw [hq₂]; exact sigma2_mem_Q))

private theorem conjZ_mul_sigma2_inv_eq_one (h : Tim79a.ParrottHyp z) {σ₂ : H z}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
  rw [map_mul, map_inv, conjZ_sigma1Nine h D, conjZ_sigma2_of_qH (z := z) D h hq₂,
    inv_one, mul_one]

private theorem conjZ_mul_sigma2_eq_one (h : Tim79a.ParrottHyp z) {σ₂ : H z}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z (sigma1Nine (z := z) D * σ₂) = 1 := by
  rw [map_mul, conjZ_sigma1Nine h D, conjZ_sigma2_of_qH (z := z) D h hq₂, mul_one]

theorem orderOf_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    orderOf ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) = 3 := by
  rw [Subgroup.orderOf_coe]
  have hcomm : Commute (sigma1Nine (z := z) D) σ₂ := hc₂.symm
  have hcomm' : Commute (sigma1Nine (z := z) D) σ₂⁻¹ := hcomm.inv_right
  have hcube : (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1 := by
    have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]
      exact pow_orderOf_eq_one _
    have h2 : (σ₂⁻¹) ^ 3 = 1 := by
      have hp : σ₂ ^ 3 = 1 := by
        rw [← hσ₂]
        exact pow_orderOf_eq_one σ₂
      rw [inv_pow, hp, inv_one]
    calc (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3
        = (sigma1Nine (z := z) D) ^ 3 * (σ₂⁻¹) ^ 3 := hcomm'.mul_pow 3
      _ = 1 := by rw [h1, h2, mul_one]
  refine orderOf_eq_prime hcube ?_
  intro h1
  apply sigma1_mul_sigma2_inv_ne_one
  rw [← qH_mul_sigma2_inv_eq (z := z) D hq₂, h1, map_one]

theorem orderOf_sigma1Nine_mul (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    orderOf ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) = 3 := by
  rw [Subgroup.orderOf_coe]
  have hcomm : Commute (sigma1Nine (z := z) D) σ₂ := hc₂.symm
  have hcube : (sigma1Nine (z := z) D * σ₂) ^ 3 = 1 := by
    have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]
      exact pow_orderOf_eq_one _
    have h2 : σ₂ ^ 3 = 1 := by
      rw [← hσ₂]
      exact pow_orderOf_eq_one σ₂
    calc (sigma1Nine (z := z) D * σ₂) ^ 3
        = (sigma1Nine (z := z) D) ^ 3 * σ₂ ^ 3 := hcomm.mul_pow 3
      _ = 1 := by rw [h1, h2, mul_one]
  refine orderOf_eq_prime hcube ?_
  intro h1
  apply sigma1_mul_sigma2_ne_one
  rw [← qH_mul_sigma2_eq (z := z) D hq₂, h1, map_one]

private theorem map_mk_eq_of_map_qH_eq {P Q : Subgroup (H z)}
    (h : P.map (qH D) = Q.map (qH D)) :
    P.map (QuotientGroup.mk' ((J z).subgroupOf (H z))) =
      Q.map (QuotientGroup.mk' ((J z).subgroupOf (H z))) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : qH D p ∈ Q.map (qH D) := h ▸ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp hp'
    exact Subgroup.mem_map.mpr ⟨q, hq, (mk_eq_mk_iff D q p).mpr hqp⟩
  · rintro ⟨q, hq, rfl⟩
    have hq' : qH D q ∈ P.map (qH D) := h ▸ ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := Subgroup.mem_map.mp hq'
    exact Subgroup.mem_map.mpr ⟨p, hp, (mk_eq_mk_iff D p q).mpr hpq⟩

private theorem exists_conj_of_model_conj (h : Tim79a.ParrottHyp z) {r : G}
    (hrH : r ∈ H z) (hr3 : orderOf r = 3) {x : QA45.originalSubgroup} {y : H z}
    (hy3 : orderOf y = 3) (hqy : qH D y = x) {g : QA45.originalSubgroup}
    (hg : (Subgroup.zpowers (qH D ⟨r, hrH⟩)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers x) :
    ∃ g' ∈ H z, CFSG.conjugate (Subgroup.zpowers r) g' = Subgroup.zpowers ((y : H z) : G) := by
  let rH : H z := ⟨r, hrH⟩
  have hrH3 : orderOf rH = 3 := by simpa [rH] using hr3
  let m : H z := lift D g
  have hqm : qH D m = g := qH_lift D g
  have hqmr : qH D (m * rH * m⁻¹) = g * qH D rH * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hqm]
  have hPcard : Nat.card (Subgroup.zpowers (m * rH * m⁻¹)) = 3 := by
    rw [Nat.card_zpowers]
    have hord : orderOf (m * rH * m⁻¹) = 3 := by
      rw [show m * rH * m⁻¹ = MulAut.conj m rH by rw [MulAut.conj_apply]]
      exact (MulEquiv.orderOf_eq (MulAut.conj m) rH).trans hrH3
    exact hord
  have hQcard : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, hy3]
  have hqimg : (Subgroup.zpowers (m * rH * m⁻¹)).map (qH D) =
      (Subgroup.zpowers y).map (qH D) := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, hqmr, hqy]
    rw [← hg, MonoidHom.map_zpowers]
    rfl
  have hN3 : ¬ 3 ∣ Nat.card ((J z).subgroupOf (H z)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_three_card_J_subgroupOf (z := z))
  obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Sec10.exists_conj_eq_of_map_eq
    (X := H z) (N := (J z).subgroupOf (H z)) hN3 hPcard hQcard
    (map_mk_eq_of_map_qH_eq (z := z) D hqimg)
  let w : H z := k * m
  have hw : Subgroup.zpowers y = Subgroup.zpowers (w * rH * w⁻¹) := by
    rw [hk, MonoidHom.map_zpowers]
    congr 1
    change k * (m * rH * m⁻¹) * k⁻¹ = (k * m) * rH * (k * m)⁻¹
    group
  have hsubG : Subgroup.zpowers ((y : H z) : G) =
      Subgroup.zpowers ((w : G) * r * (w : G)⁻¹) := by
    have h := congrArg (fun S : Subgroup (H z) => S.map (H z).subtype) hw
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h
    simpa [rH, Subgroup.coe_mul, Subgroup.coe_inv] using h
  refine ⟨((w : G)⁻¹), (H z).inv_mem w.2, ?_⟩
  rw [CFSG.conjugate, inv_inv, MonoidHom.map_zpowers]
  simpa [MulAut.conj_apply] using hsubG.symm

theorem orderThree_subgroup_classes_H (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∃ g ∈ H z, CFSG.conjugate R g = zpowers ((sigma1Nine (z := z) D : ↥(H z)) : G) ∨
        CFSG.conjugate R g = zpowers ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ∨
        CFSG.conjugate R g = zpowers ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) := by
  intro R hRH hR
  obtain ⟨r, hRr, hr3⟩ :=
    CFSG.GroupTheory.exists_zpowers_eq_of_card_eq_prime Nat.prime_three hR
  have hrH : r ∈ H z := hRH (hRr ▸ Subgroup.mem_zpowers r)
  let rH : H z := ⟨r, hrH⟩
  have hrH3 : orderOf rH = 3 := by simpa [rH] using hr3
  have hq3 : orderOf (qH D rH) = 3 := by
    have hcube : (qH D rH) ^ 3 = 1 := by
      rw [← map_pow, show rH ^ 3 = 1 by rw [← hrH3]; exact pow_orderOf_eq_one rH,
        map_one]
    refine orderOf_eq_prime hcube ?_
    intro h1
    have hmem : rH ∈ (J z).subgroupOf (H z) := (J_mem_iff D rH).mpr h1
    have hdvd : 3 ∣ Nat.card ((J z).subgroupOf (H z)) := by
      have hd := Subgroup.orderOf_dvd_natCard ((J z).subgroupOf (H z)) hmem
      rw [hrH3] at hd
      exact hd
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_three_card_J_subgroupOf (z := z))) hdvd
  have hcardP : Nat.card (Subgroup.zpowers (qH D rH)) = 3 := by
    rw [Nat.card_zpowers, hq3]
  rcases qa45_orderThree_subgroup_classes (Subgroup.zpowers (qH D rH)) hcardP with
    ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
  · obtain ⟨g', hg'H, hconj⟩ :=
      exists_conj_of_model_conj (z := z) D h hrH hr3 (sigma1Nine_order (z := z) D)
        (qH_sigma1Nine (z := z) D) hg
    exact ⟨g', hg'H, Or.inl (by rw [hRr]; exact hconj)⟩
  · obtain ⟨g', hg'H, hconj⟩ :=
      exists_conj_of_model_conj (z := z) D h hrH hr3
        (by
          rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂)]
          exact orderOf_sigma1Nine_mul (z := z) D h hσ₂ hq₂ hc₂)
        (qH_mul_sigma2_eq (z := z) D hq₂) hg
    exact ⟨g', hg'H, Or.inr (Or.inr (by rw [hRr]; exact hconj))⟩
  · obtain ⟨g', hg'H, hconj⟩ :=
      exists_conj_of_model_conj (z := z) D h hrH hr3
        (by
          rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
          exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂)
        (qH_mul_sigma2_inv_eq (z := z) D hq₂) hg
    exact ⟨g', hg'H, Or.inr (Or.inl (by rw [hRr]; exact hconj))⟩

private theorem exists_inv_of_qH_eq_inv {σ m : H z} (hσ : orderOf σ = 3)
    (hm : qH D (m * σ * m⁻¹) = (qH D σ)⁻¹) :
    ∃ w ∈ H z, (w : G) * (σ : G) * (w : G)⁻¹ = ((σ : G))⁻¹ := by
  have hm3 : orderOf (m * σ * m⁻¹) = 3 := by
    rw [show m * σ * m⁻¹ = MulAut.conj m σ by rw [MulAut.conj_apply]]
    exact (MulEquiv.orderOf_eq (MulAut.conj m) σ).trans hσ
  have hcos : σ⁻¹ * (m * σ * m⁻¹)⁻¹ ∈ (J z).subgroupOf (H z) := by
    rw [J_mem_iff D]
    rw [map_mul, map_inv, map_inv, hm]
    group
  obtain ⟨j, hjN, hj⟩ := CFSG.GroupTheory.exists_conj_of_order_three_of_mul_inv_mem
    (isPGroup_J_subgroupOf (z := z)) (by rw [orderOf_inv, hσ]) hm3 hcos
  refine ⟨j * m, (H z).mul_mem j.2 m.2, ?_⟩
  have hconj : (j * m) * σ * (j * m)⁻¹ = σ⁻¹ := by
    calc (j * m) * σ * (j * m)⁻¹ = j * (m * σ * m⁻¹) * j⁻¹ := by group
      _ = σ⁻¹ := hj
  have hval := congrArg (fun x : H z => (x : G)) hconj
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hval

theorem exists_inv_sigma1Nine (h : Tim79a.ParrottHyp z) :
    ∃ w₁ ∈ H z, w₁ * ((sigma1Nine (z := z) D : ↥(H z)) : G) * w₁⁻¹ =
      ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ := by
  have hm : qH D (vH D * sigma1Nine D * (vH D)⁻¹) = (qH D (sigma1Nine D))⁻¹ := by
    rw [map_mul, map_mul, map_inv, qH_vH, qH_sigma1Nine]
    apply Subtype.ext
    exact sigma1_conj_v
  exact exists_inv_of_qH_eq_inv (z := z) D (sigma1Nine_order (z := z) D) hm

private theorem u_conj_sigma1_mul_sigma2_inv :
    u * (sigma1 * sigma2⁻¹) * u⁻¹ = (sigma1 * sigma2⁻¹)⁻¹ := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right u_sq
  have hu2 : u * sigma2 * u⁻¹ = sigma1 := by
    calc u * sigma2 * u⁻¹ = u * (u * sigma1 * u⁻¹) * u⁻¹ := by rw [sigma1_conj_u]
      _ = sigma1 := by
        rw [hu]
        rw [show u * (u * sigma1 * u) * u = (u * u) * sigma1 * (u * u) by
          simp only [mul_assoc]]
        rw [u_sq]
        simp
  calc u * (sigma1 * sigma2⁻¹) * u⁻¹
      = (u * sigma1 * u⁻¹) * (u * sigma2⁻¹ * u⁻¹) := by group
    _ = sigma2 * (u * sigma2 * u⁻¹)⁻¹ := by rw [sigma1_conj_u]; group
    _ = sigma2 * sigma1⁻¹ := by rw [hu2]
    _ = (sigma1 * sigma2⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv]

theorem exists_inv_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    ∃ w ∈ H z, w * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * w⁻¹ =
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)⁻¹ := by
  have hm : qH D (uH D * (sigma1Nine D * σ₂⁻¹) * (uH D)⁻¹) =
      (qH D (sigma1Nine D * σ₂⁻¹))⁻¹ := by
    rw [map_mul, map_mul, map_inv, qH_uH, qH_mul_sigma2_inv_eq (z := z) D hq₂]
    apply Subtype.ext
    exact u_conj_sigma1_mul_sigma2_inv
  exact exists_inv_of_qH_eq_inv (z := z) D
    (by
      rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
      exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂) hm

private theorem card_isSylowOf_two_eq_two_pow_factorization {T K : Subgroup G}
    (hT : IsSylowOf 2 T K) : Nat.card T = 2 ^ (Nat.card K).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hT.card_eq

theorem card_isSylowOf_centralizer_sigma1Nine (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    Nat.card T₁ = 2 ^ 7 := by
  have hcent : Nat.card (Subgroup.centralizer
      ({sigma1Nine (z := z) D} : Set ↥(H z))) = 10368 :=
    card_centralizer_sigma1Nine (z := z) (D := D) h
  have hK : H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) =
      (Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))).map (H z).subtype :=
    inf_centralizer_eq_map_centralizer (z := z) (sigma1Nine (z := z) D)
  have hcard : Nat.card ↥
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) = 10368 := by
    rw [hK, Subgroup.card_map_of_injective (H z).subtype_injective, hcent]
  have hfac : Nat.factorization 10368 2 = 7 := by
    have h10368 : 10368 = 2 ^ 7 * 81 := by norm_num
    rw [h10368, factorization_two_of_eq_two_pow_mul_odd (by norm_num) (by norm_num)]
  have := card_isSylowOf_two_eq_two_pow_factorization hT₁
  rw [hcard, hfac] at this
  simpa using this

theorem card_isSylowOf_centralizer_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (hE27 : E27LineCountData (z := z) (D := D) h σ₂) {T₂ : Subgroup G}
    (hT₂ : IsSylowOf 2 T₂
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) :
    Nat.card T₂ = 2 ^ 8 := by
  let y : H z := sigma1Nine (z := z) D * σ₂⁻¹
  have hy3 : orderOf y = 3 := by
    change orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  have hqy : qH D y =
      (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : QA45.originalSubgroup) :=
    qH_mul_sigma2_inv_eq (z := z) D hq₂
  have hZy : conjZ z y = 1 := conjZ_mul_sigma2_inv_eq_one (z := z) D h hq₂
  have hfix : fixDimV h y = 4 :=
    fixDimV_sigma1Nine_mul_sigma2_inv_eq_four_of_not_equalityBranch (z := z) D h hIII
      hσ₂ hq₂ hc₂ hE27
  have hJcard : Nat.card (centralizerJ y) = 64 := by
    rw [card_centralizerJ_eq_four_mul_two_pow_fixDim_of_conjZ (z := z) h hy3 hZy, hfix]
    norm_num
  have hqcard : Nat.card (Subgroup.centralizer
      ({⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩} :
        Set QA45.originalSubgroup)) = 108 := by
    rw [card_centralizer_QA45_eq_filter (sigma1 * sigma2⁻¹) sigma1_mul_sigma2_inv_mem_A]
    exact Certificates.certificate946005.centralizer_sigma1sigma2inv
  have hcent : Nat.card (Subgroup.centralizer ({y} : Set ↥(H z))) = 6912 := by
    rw [card_centralizer_eq_card_centralizerJ_mul_card_centralizer_QA45
      (z := z) (D := D) hy3 hqy, hJcard, hqcard]
  have hK : H z ⊓ centralizer ({((y : H z) : G)} : Set G) =
      (Subgroup.centralizer ({y} : Set ↥(H z))).map (H z).subtype :=
    inf_centralizer_eq_map_centralizer (z := z) y
  have hcard : Nat.card ↥(H z ⊓ centralizer ({((y : H z) : G)} : Set G)) = 6912 := by
    rw [hK, Subgroup.card_map_of_injective (H z).subtype_injective, hcent]
  have hfac : Nat.factorization 6912 2 = 8 := by
    have h6912 : 6912 = 2 ^ 8 * 27 := by norm_num
    rw [h6912, factorization_two_of_eq_two_pow_mul_odd (by norm_num) (by norm_num)]
  have := card_isSylowOf_two_eq_two_pow_factorization hT₂
  rw [hcard, hfac] at this
  simpa using this

theorem card_isSylowOf_centralizer_sigma1Nine_mul (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (hE27 : E27LineCountData (z := z) (D := D) h σ₂) {T₃ : Subgroup G}
    (hT₃ : IsSylowOf 2 T₃
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G))) :
    Nat.card T₃ = 2 ^ 5 := by
  let y : H z := sigma1Nine (z := z) D * σ₂
  have hy3 : orderOf y = 3 := by
    change orderOf (sigma1Nine (z := z) D * σ₂) = 3
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂)]
    exact orderOf_sigma1Nine_mul (z := z) D h hσ₂ hq₂ hc₂
  have hqy : qH D y =
      (⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩ : QA45.originalSubgroup) :=
    qH_mul_sigma2_eq (z := z) D hq₂
  have hZy : conjZ z y = 1 := conjZ_mul_sigma2_eq_one (z := z) D h hq₂
  have hfix : fixDimV h y = 0 :=
    fixDimV_sigma1Nine_mul_sigma2_eq_zero_of_not_equalityBranch (z := z) D h hIII
      hσ₂ hq₂ hc₂ hE27
  have hJcard : Nat.card (centralizerJ y) = 4 := by
    rw [card_centralizerJ_eq_four_mul_two_pow_fixDim_of_conjZ (z := z) h hy3 hZy, hfix]
    norm_num
  have hqcard : Nat.card (Subgroup.centralizer
      ({⟨sigma1 * sigma2, sigma1_mul_sigma2_mem_A⟩} :
        Set QA45.originalSubgroup)) = 216 := by
    rw [card_centralizer_QA45_eq_filter (sigma1 * sigma2) sigma1_mul_sigma2_mem_A]
    exact Certificates.certificate946005.centralizer_sigma1sigma2
  have hcent : Nat.card (Subgroup.centralizer ({y} : Set ↥(H z))) = 864 := by
    rw [card_centralizer_eq_card_centralizerJ_mul_card_centralizer_QA45
      (z := z) (D := D) hy3 hqy, hJcard, hqcard]
  have hK : H z ⊓ centralizer ({((y : H z) : G)} : Set G) =
      (Subgroup.centralizer ({y} : Set ↥(H z))).map (H z).subtype :=
    inf_centralizer_eq_map_centralizer (z := z) y
  have hcard : Nat.card ↥(H z ⊓ centralizer ({((y : H z) : G)} : Set G)) = 864 := by
    rw [hK, Subgroup.card_map_of_injective (H z).subtype_injective, hcent]
  have hfac : Nat.factorization 864 2 = 5 := by
    have h864 : 864 = 2 ^ 5 * 27 := by norm_num
    rw [h864, factorization_two_of_eq_two_pow_mul_odd (by norm_num) (by norm_num)]
  have := card_isSylowOf_two_eq_two_pow_factorization hT₃
  rw [hcard, hfac] at this
  simpa using this

end CFSG.RankThree.GF2n.Parrott
