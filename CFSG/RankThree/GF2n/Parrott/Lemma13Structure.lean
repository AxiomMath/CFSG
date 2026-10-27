module

public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
import all CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.RankThree.GF2n.Parrott.Section2Q8Final2
public import CFSG.RankThree.GF2n.Parrott.LiftSquare
import all CFSG.RankThree.GF2n.Parrott.Section2Products
import CFSG.RankThree.GF2n.Parrott.SigmaStarEquality
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13T
public import CFSG.RankThree.GF2n.Parrott.Section2Cases
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43 A1Section2Local
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem conjV_mem_map_pi_iff (h : Tim79a.ParrottHyp z) {A : Subgroup G} (g : ↥(H z))
    (hgA : ∀ a : G, a ∈ A ↔ (g : G) * a * (g : G)⁻¹ ∈ A) (v : QuotientV.V z) :
    conjV h g v ∈ (A.subgroupOf (J z)).map (QuotientV.pi z) ↔
      v ∈ (A.subgroupOf (J z)).map (QuotientV.pi z) := by
  constructor
  · rintro ⟨a, ha, hav⟩
    obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hjJ : ((g : G)⁻¹ * (a : G) * (g : G)) ∈ J z := by
      have := H_conj_mem_J (z := z) g⁻¹ a.2
      simpa using this
    refine ⟨⟨(g : G)⁻¹ * (a : G) * (g : G), hjJ⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · rw [hgA]
      have e : (g : G) * ((g : G)⁻¹ * (a : G) * (g : G)) * (g : G)⁻¹ = a := by group
      rw [e]
      exact haA
    · have hconj : conjV h g (QuotientV.pi z ⟨(g : G)⁻¹ * (a : G) * (g : G), hjJ⟩) =
          QuotientV.pi z a := by
        rw [conjV_pi_conj h g hjJ]
        congr 1
        apply Subtype.ext
        change (g : G) * ((g : G)⁻¹ * (a : G) * (g : G)) * (g : G)⁻¹ = (a : G)
        group
      apply (conjV h g).injective
      rw [hconj, hav]
  · rintro ⟨a, ha, rfl⟩
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    refine ⟨⟨(g : G) * (a : G) * (g : G)⁻¹, H_conj_mem_J (z := z) g a.2⟩,
      Subgroup.mem_subgroupOf.mpr ((hgA a).mp haA), ?_⟩
    rw [conjV_pi_conj h g a.2]

theorem card_map_pi_mul_card_inf_centerIn {A : Subgroup G} (hA : A ≤ J z) :
    Nat.card ((A.subgroupOf (J z)).map (QuotientV.pi z)) *
      Nat.card (A ⊓ centerIn (J z) : Subgroup G) = Nat.card A := by
  have h1 : Nat.card ((A.subgroupOf (J z)).map (QuotientV.pi z)) *
      Nat.card ((QuotientV.pi z).ker ⊓ A.subgroupOf (J z) : Subgroup (J z)) =
        Nat.card (A.subgroupOf (J z)) := by
    rw [← Subgroup.relIndex_ker (K := A.subgroupOf (J z)) (QuotientV.pi z)]
    exact Subgroup.relIndex_mul_card (H := (QuotientV.pi z).ker) (K := A.subgroupOf (J z))
  have hker : ((QuotientV.pi z).ker ⊓ A.subgroupOf (J z) : Subgroup (J z)) =
      (A ⊓ centerIn (J z) : Subgroup G).subgroupOf (J z) := by
    rw [QuotientV.pi_ker]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    tauto
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hA)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv] at h1
  exact h1


theorem mul_self_eq_one_of_mem_centerIn_J (h : Tim79a.ParrottHyp z) {e : G}
    (he : e ∈ centerIn (J z)) : e * e = 1 := by
  have := isKleinFour_centerIn_J (z := z) h
  have h2 : (⟨e, he⟩ : ↥(centerIn (J z))) ^ 2 = 1 := by
    rw [← IsKleinFour.exponent_two (G := ↥(centerIn (J z)))]
    exact Monoid.pow_exponent_eq_one _
  have := congrArg Subtype.val h2
  simpa [pow_two] using this

theorem commute_of_cube_of_mem_centerIn (h : Tim79a.ParrottHyp z) {g : ↥(H z)}
    (hg3 : g ^ 3 = 1) (hZ : conjZ z g = 1) {a : G}
    (hd : (g : G) * a * (g : G)⁻¹ * a⁻¹ ∈ centerIn (J z)) : (g : G) * a = a * (g : G) := by
  set d := (g : G) * a * (g : G)⁻¹ * a⁻¹ with hd_def
  have hgd : (g : G) * d = d * (g : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZ hd)).symm
  have hd2 : d * d = 1 := mul_self_eq_one_of_mem_centerIn_J h hd
  have hg3' : (g : G) * g * g = 1 := by
    have := congrArg Subtype.val hg3
    simpa [pow_succ, mul_assoc] using this
  have h1 : (g : G) * a * (g : G)⁻¹ = d * a := by rw [hd_def]; group
  have h2 : (g : G) * ((g : G) * a * (g : G)⁻¹) * (g : G)⁻¹ = d * d * a := by
    calc (g : G) * ((g : G) * a * (g : G)⁻¹) * (g : G)⁻¹ = (g : G) * (d * a) * (g : G)⁻¹ := by
          rw [h1]
      _ = ((g : G) * d) * a * (g : G)⁻¹ := by group
      _ = (d * (g : G)) * a * (g : G)⁻¹ := by rw [hgd]
      _ = d * ((g : G) * a * (g : G)⁻¹) := by group
      _ = d * (d * a) := by rw [h1]
      _ = d * d * a := by group
  have h3 : (g : G) * ((g : G) * ((g : G) * a * (g : G)⁻¹) * (g : G)⁻¹) * (g : G)⁻¹ = d * a := by
    rw [h2, hd2, one_mul, h1]
  have h4 : (g : G) * ((g : G) * ((g : G) * a * (g : G)⁻¹) * (g : G)⁻¹) * (g : G)⁻¹ = a := by
    calc (g : G) * ((g : G) * ((g : G) * a * (g : G)⁻¹) * (g : G)⁻¹) * (g : G)⁻¹
        = ((g : G) * g * g) * a * ((g : G) * g * g)⁻¹ := by group
      _ = a := by rw [hg3']; group
  have hd1 : d = 1 := by
    have e : a = d * a := h4.symm.trans h3
    calc d = d * a * a⁻¹ := by group
      _ = a * a⁻¹ := by rw [← e]
      _ = 1 := mul_inv_cancel a
  calc (g : G) * a = d * (a * (g : G)) := by rw [hd_def]; group
    _ = a * (g : G) := by rw [hd1, one_mul]

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem commute_of_mem_CJ_of_mem_commutator (h : Tim79a.ParrottHyp z) (σ : ↥(H z)) {b r : G}
    (hb : b ∈ CJ z (σ : G)) (hr : r ∈ ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆) :
    b * r = r * b := by
  set P : Subgroup G := (Subgroup.zpowers σ).map (H z).subtype with hP
  have hPeq : P = Subgroup.zpowers (σ : G) := map_zpowers_sigma_eq (z := z)
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm, -, -⟩ := h
    simpa [J, H] using hcomm
  have hPH : P ≤ H z := by
    rw [hPeq, Subgroup.zpowers_le]
    exact σ.2
  have h1 : ⁅⁅J z, CJ z (σ : G)⁆, P⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    calc ⁅J z, CJ z (σ : G)⁆ ≤ ⁅J z, J z⁆ := Subgroup.commutator_mono le_rfl inf_le_right
      _ = Subgroup.zpowers z := hJcomm
      _ ≤ Subgroup.centralizer (P : Set G) := by
        rw [Subgroup.zpowers_le]
        exact Subgroup.centralizer_le hPH (z_centralizes_H_A (z := z))
  have h2 : ⁅⁅CJ z (σ : G), P⁆, J z⁆ = ⊥ := by
    have hCP : ⁅CJ z (σ : G), P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      rw [hPeq] at hp
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      have hcσ : Commute c (σ : G) := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hc).1
      exact (hcσ.zpow_right k).eq.symm
    rw [hCP, Subgroup.commutator_bot_left]
  have h3 : ⁅⁅P, J z⁆, CJ z (σ : G)⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 hr) b
    hb

theorem mem_zpowers_of_mem_CJ_of_mem_commutator (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ3 : orderOf σ = 3) (hZ : conjZ z σ = 1) {a : G} (haB : a ∈ CJ z (σ : G))
    (haR : a ∈ ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆) : a ∈ Subgroup.zpowers z := by
  rw [← centralizer_commutator_eq_zpowers_z_of (z := z) h hσ3 hZ
    (conjV_ne_one_of_order_three h hσ3 hZ)]
  exact ⟨(mem_CJ.mp haB).1, haR⟩


theorem exists_mul_of_mem_J_of_orderOf_eq_three (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ3 : orderOf σ = 3) {j : G} (hj : j ∈ J z) :
    ∃ b ∈ CJ z (σ : G), ∃ r ∈ ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆, j = b * r := by
  have hJ := J_eq_sup_centralizer_commutator_singleton_of (z := z) h hσ3
  have hn : ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ ≤
      Subgroup.normalizer (CJ z (σ : G) : Set G) :=
    le_normalizer_of_commute fun r hr b hb => (commute_of_mem_CJ_of_mem_commutator h σ hb hr).symm
  have hj' : j ∈ (CJ z (σ : G) ⊔ ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ : Subgroup G) := by
    rw [show CJ z (σ : G) = J z ⊓ Subgroup.centralizer ({(σ : G)} : Set G) from inf_comm _ _,
      ← hJ]
    exact hj
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hj'
  obtain ⟨b, hb, r, hr, rfl⟩ := hj'
  exact ⟨b, hb, r, hr, rfl⟩

theorem mem_centerIn_of_mem_CJ_of_commute (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hσ3 : orderOf σ = 3) {b : G} (hb : b ∈ CJ z (σ : G))
    (hcomm : ∀ c ∈ CJ z (σ : G), b * c = c * b) : b ∈ centerIn (J z) := by
  refine ⟨(mem_CJ.mp hb).2, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
  obtain ⟨c, hc, r, hr, rfl⟩ := exists_mul_of_mem_J_of_orderOf_eq_three h hσ3 hj
  calc c * r * b = c * (r * b) := by group
    _ = c * (b * r) := by rw [commute_of_mem_CJ_of_mem_commutator h σ hb hr]
    _ = (c * b) * r := by group
    _ = (b * c) * r := by rw [hcomm c hc]
    _ = b * (c * r) := by group

theorem conjZ_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
  rw [map_mul, map_inv, conjZ_sigma1Nine h D, conjZ_eq_one_of_qH_eq_sigma2 (z := z) D h hq₂,
    inv_one, mul_one]

theorem exists_mul_of_mem_CJ_mul_inv (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {b : G}
    (hb : b ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) :
    ∃ a ∈ CJ z (sigma1Nine (z := z) D : G),
      ∃ q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓ sigma1Commutator (z := z) D,
        b = a * q := by
  have hsup := CJ_eq_sup_inf_sigma1Commutator_of_le (z := z) (D := D) h
    (x := sigma1Nine (z := z) D * σ₂⁻¹) (CJ_sigma1Nine_le_CJ_mul_inv D hEq)
  have hn : CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓ sigma1Commutator (z := z) D ≤
      Subgroup.normalizer (CJ z (sigma1Nine (z := z) D : G) : Set G) :=
    le_normalizer_of_commute fun q hq a ha =>
      (commute_of_mem_CJ_of_mem_commutator h (sigma1Nine (z := z) D) ha hq.2).symm
  rw [hsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hb
  obtain ⟨a, ha, q, hq, rfl⟩ := hb
  exact ⟨a, ha, q, hq, rfl⟩

theorem mem_inf_sigma1Commutator_conj_iff (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) (g : ↥(H z))
    (hgσ : g * (sigma1Nine (z := z) D * σ₂⁻¹) = (sigma1Nine (z := z) D * σ₂⁻¹) * g) (a : G) :
    a ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓ sigma1Commutator (z := z) D ↔
      (g : G) * a * (g : G)⁻¹ ∈
        CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓ sigma1Commutator (z := z) D := by
  have hgσ' : (g : G) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (g : G) := congrArg Subtype.val hgσ
  have hP : ∀ (y : ↥(H z)) (p : G), p ∈ sigma1Commutator (z := z) D →
      (y : G) * p * (y : G)⁻¹ ∈ sigma1Commutator (z := z) D :=
    fun y p hp => commutator_sigma1Nine_conj_mem (z := z) (D := D) h hEq hσ₂ hq₂ hcomm.eq.symm y p hp
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_CJ_conj_iff g.2 hgσ' a).mp h1, hP g a h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_CJ_conj_iff g.2 hgσ' a).mpr h1, ?_⟩
    have h3 := hP g⁻¹ _ h2
    have e : ((g⁻¹ : ↥(H z)) : G) * ((g : G) * a * (g : G)⁻¹) * ((g⁻¹ : ↥(H z)) : G)⁻¹ = a := by
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rwa [e] at h3


theorem conjV_fixes_Fsub_of_mem_P_H (h : Tim79a.ParrottHyp z)
    (hJ0 : (J0sub (z := z) (D := D)).Normal) {y : ↥(H z)} (hy : y ∈ P_H D)
    {v : QuotientV.V z} (hv : v ∈ Fsub (z := z) (sigma1Nine (z := z) D)) :
    conjV h y v = v := by
  have hq : qH (z := z) (D := D) y ∈
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    (mem_P_H_iff (z := z) (D := D) y).mp hy
  let a : QP45.originalSubgroup :=
    ⟨qH (z := z) (D := D) y, Subgroup.mem_subgroupOf.mp hq⟩
  have hact : actFsub (z := z) (D := D) h hJ0
      (QuotientGroup.mk' ((J z).subgroupOf (H z)) y) = 1 := by
    have h1 : actQFsub (z := z) (D := D) h hJ0 a = 1 := by
      rw [actQFsub_eq_one (z := z) (D := D) h hJ0]
      rfl
    have h2 : (D.toQA45 (z := z) (hN := hN)).symm
        (Subgroup.inclusion QP45_le_QA45 a) =
        QuotientGroup.mk' ((J z).subgroupOf (H z)) y := by
      have h3 : Subgroup.inclusion QP45_le_QA45 a = qH (z := z) (D := D) y := rfl
      rw [h3, toQA45_symm_qH]
    simpa [actQFsub, h2] using h1
  have happ : actionA h (QuotientGroup.mk' ((J z).subgroupOf (H z)) y) v = v := by
    have hfix : actFsub (z := z) (D := D) h hJ0
        (QuotientGroup.mk' ((J z).subgroupOf (H z)) y) ⟨v, hv⟩ = ⟨v, hv⟩ := by
      rw [hact]
      rfl
    exact congrArg Subtype.val hfix
  rw [← actionA_mk (z := z) h y]
  exact happ

theorem card_CJ_mul_inv_inf_sigma1Commutator (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Nat.card (CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      sigma1Commutator (z := z) D : Subgroup G) = 8 := by
  have h8 := card_CJcomm_sigma1sigma2inv_eq_eight_final (z := z) (D := D) h hEq hσ₂ hq₂
    hcomm.eq.symm
  have hle : CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      sigma1Commutator (z := z) D ≤ J z := inf_le_left.trans inf_le_right
  have heq : CJcomm (z := z) (D := D) (sigma1Nine (z := z) D * σ₂⁻¹) =
      (CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        sigma1Commutator (z := z) D).subgroupOf (J z) := by
    ext j
    simp only [CJcomm, centralizerJ, sigma1Commutator, CJ, Subgroup.mem_inf,
      Subgroup.mem_subgroupOf]
  rw [heq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h8
  exact h8

theorem card_CJ_mul_inv_of_equalityBranch (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Nat.card (CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) = 64 := by
  rw [card_CJ_eq_eight_mul_card_inf_sigma1Commutator (z := z) (D := D) h
      (CJ_sigma1Nine_le_CJ_mul_inv D hEq),
    card_CJ_mul_inv_inf_sigma1Commutator D h hσ₂ hq₂ hcomm hEq]

theorem fixDimV_mul_inv_of_equalityBranch (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) = 4 :=
  fixDimV_eq_four_of_card_inf_sigma1Commutator (z := z) (D := D) h
    (orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order D) hσ₂ (qH_sigma1Nine D) hq₂
      hcomm)
    (conjZ_sigma1Nine_mul_inv D h hq₂) (CJ_sigma1Nine_le_CJ_mul_inv D hEq)
    (card_CJ_mul_inv_inf_sigma1Commutator D h hσ₂ hq₂ hcomm hEq)

theorem card_commutatorV_mul_inv_of_equalityBranch (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Nat.card (commutatorV h (sigma1Nine (z := z) D * σ₂⁻¹)) = 16 := by
  have hσ3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 :=
    orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order D) hσ₂ (qH_sigma1Nine D) hq₂ hcomm
  have hkercard : Nat.card ↥(VComplementHom h (sigma1Nine (z := z) D * σ₂⁻¹)).ker = 16 := by
    rw [ker_VComplementHom_eq_autFixedSubgroup (z := z) h hσ3, card_fix,
      fixDimV_mul_inv_of_equalityBranch D h hσ₂ hq₂ hcomm hEq]
    norm_num
  have hcard := Subgroup.card_ker_mul_card_range (VComplementHom h (sigma1Nine (z := z) D * σ₂⁻¹))
  rw [hkercard, QuotientV.card_V h] at hcard
  rw [commutatorV_eq_range (z := z) h hσ3]
  omega

theorem card_map_pi_inf_sigma1Commutator (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Nat.card (((CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      sigma1Commutator (z := z) D).subgroupOf (J z)).map (QuotientV.pi z)) = 4 := by
  have hle : CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      sigma1Commutator (z := z) D ≤ J z := inf_le_left.trans inf_le_right
  have h1 := card_map_pi_mul_card_inf_centerIn hle
  have hPZ := commutator_sigma1Nine_inf_centerIn_eq_zpowers_z (z := z) h D
  have hQZ : (CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓ sigma1Commutator (z := z) D ⊓
      centerIn (J z) : Subgroup G) = Subgroup.zpowers z := by
    apply le_antisymm
    · intro q hq
      rw [← hPZ]
      exact ⟨hq.1.2, hq.2⟩
    · rw [Subgroup.zpowers_le]
      have hz : z ∈ ⁅(Subgroup.zpowers (sigma1Nine D)).map (H z).subtype, J z⁆ ⊓
          centerIn (J z) := by
        rw [hPZ]
        exact Subgroup.mem_zpowers z
      refine ⟨⟨mem_CJ.mpr ⟨?_, z_mem_J h⟩, hz.1⟩, hz.2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp
        (sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)).2).symm
  rw [hQZ, Nat.card_zpowers, h.1, card_CJ_mul_inv_inf_sigma1Commutator D h hσ₂ hq₂ hcomm hEq]
    at h1
  omega

theorem conj_mul_inv_mem_centerIn_of_mem_P_H (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {y : ↥(H z)}
    (hy : y ∈ P_H D) {a : G} (ha : a ∈ CJ z (sigma1Nine (z := z) D : G)) :
    (y : G) * a * (y : G)⁻¹ * a⁻¹ ∈ centerIn (J z) := by
  have hJ0 := J0sub_normal (z := z) (D := D) h hEq hσ₂ hq₂
  have haJ : a ∈ J z := (mem_CJ.mp ha).2
  have hv : QuotientV.pi z ⟨a, haJ⟩ ∈ Fsub (z := z) (sigma1Nine (z := z) D) :=
    ⟨⟨a, haJ⟩, mem_centralizerJ_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
      (mem_CJ.mp ha).1), rfl⟩
  have hfix := conjV_fixes_Fsub_of_mem_P_H D h hJ0 hy hv
  rw [conjV_pi_conj h y haJ] at hfix
  have hyaJ : (y : G) * a * (y : G)⁻¹ ∈ J z := H_conj_mem_J (z := z) y haJ
  have hone : QuotientV.pi z ⟨(y : G) * a * (y : G)⁻¹ * a⁻¹,
      (J z).mul_mem hyaJ ((J z).inv_mem haJ)⟩ = 1 := by
    have e : (⟨(y : G) * a * (y : G)⁻¹ * a⁻¹, (J z).mul_mem hyaJ ((J z).inv_mem haJ)⟩ : J z) =
        ⟨(y : G) * a * (y : G)⁻¹, hyaJ⟩ * (⟨a, haJ⟩ : J z)⁻¹ := rfl
    rw [e, map_mul, map_inv, hfix, mul_inv_cancel]
  exact (pi_eq_one_iff_mem_centerIn _).mp hone

theorem conj_mul_inv_mem_zpowers_of_mem_inf_sigma1Commutator (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {g : ↥(H z)}
    (hg : qH D g = (⟨t, t_mem_A⟩ : QA45.originalSubgroup))
    (hgσ : g * (sigma1Nine (z := z) D * σ₂⁻¹) = (sigma1Nine (z := z) D * σ₂⁻¹) * g) {q : G}
    (hq : q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓ sigma1Commutator (z := z) D) :
    (g : G) * q * (g : G)⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
  set σ₁ : ↥(H z) := sigma1Nine (z := z) D with hσ₁
  set Q : Subgroup G := CJ z ((σ₁ * σ₂⁻¹ : ↥(H z)) : G) ⊓ sigma1Commutator (z := z) D with hQ
  have hQJ : Q ≤ J z := inf_le_left.trans inf_le_right
  set W : Subgroup (QuotientV.V z) := (Q.subgroupOf (J z)).map (QuotientV.pi z) with hW
  have hgQ := mem_inf_sigma1Commutator_conj_iff D h hσ₂ hq₂ hcomm hEq g hgσ
  have hs1σ : σ₁ * (σ₁ * σ₂⁻¹) = (σ₁ * σ₂⁻¹) * σ₁ :=
    (Commute.mul_right (Commute.refl σ₁) hcomm.inv_right).eq
  have hs1Q := mem_inf_sigma1Commutator_conj_iff D h hσ₂ hq₂ hcomm hEq σ₁ hs1σ
  have hφ := conjV_mem_map_pi_iff h g hgQ
  have hβ := conjV_mem_map_pi_iff h σ₁ hs1Q
  have hB : Nat.card W = 4 := card_map_pi_inf_sigma1Commutator D h hσ₂ hq₂ hcomm hEq
  have hσ₁3 : σ₁ ^ 3 = 1 := by rw [← sigma1Nine_order (z := z) D]; exact pow_orderOf_eq_one _
  have hβ3 : ∀ v ∈ W, (conjV h σ₁ ^ 3) v = v := by
    intro v _
    rw [← map_pow, hσ₁3, map_one]
    rfl
  have hβfix : ∀ v ∈ W, conjV h σ₁ v = v → v = 1 := by
    rintro v ⟨q', hq', rfl⟩ hfix
    have hq'Q : (q' : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq'
    have hsqJ : (σ₁ : G) * q' * (σ₁ : G)⁻¹ ∈ J z := H_conj_mem_J (z := z) σ₁ q'.2
    have hfix' : QuotientV.pi z ⟨(σ₁ : G) * q' * (σ₁ : G)⁻¹, hsqJ⟩ = QuotientV.pi z q' := by
      rw [← conjV_pi_conj h σ₁ q'.2]
      exact hfix
    have hone : QuotientV.pi z ⟨(σ₁ : G) * q' * (σ₁ : G)⁻¹ * (q' : G)⁻¹,
        (J z).mul_mem hsqJ ((J z).inv_mem q'.2)⟩ = 1 := by
      have e : (⟨(σ₁ : G) * q' * (σ₁ : G)⁻¹ * (q' : G)⁻¹,
          (J z).mul_mem hsqJ ((J z).inv_mem q'.2)⟩ : J z) =
          ⟨(σ₁ : G) * q' * (σ₁ : G)⁻¹, hsqJ⟩ * (⟨(q' : G), q'.2⟩ : J z)⁻¹ := rfl
      rw [e, map_mul, map_inv, hfix', mul_inv_cancel]
    have hd := (pi_eq_one_iff_mem_centerIn _).mp hone
    have hc := commute_of_cube_of_mem_centerIn h hσ₁3 (conjZ_sigma1Nine h D) hd
    have hz : (q' : G) ∈ Subgroup.zpowers z := by
      rw [← centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
      exact ⟨⟨q'.2, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩, hq'Q.2⟩
    have hzc : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
    have hzZ : (q' : G) ∈ centerIn (J z) := Subgroup.zpowers_le.mpr hzc hz
    exact (pi_eq_one_iff_mem_centerIn q'.2).mpr hzZ
  have hg2 : ((g ^ 2 : ↥(H z)) : G) ∈ J z := by
    have hq1 : qH D (g ^ 2) = 1 := by
      rw [map_pow, hg]
      apply Subtype.ext
      simp [pow_two, t_sq]
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hq1)
  have hk : ∀ v ∈ W, (conjV h g ^ 2 ^ 1) v = v := by
    intro v _
    have h1 : conjV h (g ^ 2) = 1 :=
      MonoidHom.mem_ker.mp (J_le_ker_conjV (z := z) h (Subgroup.mem_subgroupOf.mpr hg2))
    rw [pow_one, ← map_pow, h1]
    rfl
  have hβφ : ∀ v ∈ W, conjV h σ₁ (conjV h g v) = conjV h g (conjV h σ₁ v) := by
    intro v _
    have hj : (g * σ₁)⁻¹ * (σ₁ * g) ∈ (J z).subgroupOf (H z) := by
      rw [J_mem_iff D, map_mul, map_inv, map_mul, map_mul, hg, qH_sigma1Nine]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [t_commute_sigma1.symm]
      group
    have e : conjV h (σ₁ * g) = conjV h (g * σ₁) := by
      have e1 : σ₁ * g = (g * σ₁) * ((g * σ₁)⁻¹ * (σ₁ * g)) := by group
      rw [e1, conjV_mul_mem_J (z := z) h (Subgroup.mem_subgroupOf.mp hj)]
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, e]
  have hfix := apply_eq_of_commute_of_cube W hB (conjV h σ₁) (conjV h g) hβ hφ hβ3 hβfix hk hβφ
  have hqW : QuotientV.pi z ⟨q, hQJ hq⟩ ∈ W := ⟨⟨q, hQJ hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  have h1 := hfix _ hqW
  rw [conjV_pi_conj h g (hQJ hq)] at h1
  have hgqJ : (g : G) * q * (g : G)⁻¹ ∈ J z := H_conj_mem_J (z := z) g (hQJ hq)
  have hone : QuotientV.pi z ⟨(g : G) * q * (g : G)⁻¹ * q⁻¹,
      (J z).mul_mem hgqJ ((J z).inv_mem (hQJ hq))⟩ = 1 := by
    have e : (⟨(g : G) * q * (g : G)⁻¹ * q⁻¹, (J z).mul_mem hgqJ ((J z).inv_mem (hQJ hq))⟩ :
        J z) = ⟨(g : G) * q * (g : G)⁻¹, hgqJ⟩ * (⟨q, hQJ hq⟩ : J z)⁻¹ := rfl
    rw [e, map_mul, map_inv, h1, mul_inv_cancel]
  have hZ := (pi_eq_one_iff_mem_centerIn _).mp hone
  have hQmem : (g : G) * q * (g : G)⁻¹ * q⁻¹ ∈ Q := Q.mul_mem ((hgQ q).mp hq) (Q.inv_mem hq)
  rw [← commutator_sigma1Nine_inf_centerIn_eq_zpowers_z (z := z) h D]
  exact ⟨hQmem.2, hZ⟩

theorem conj_mul_inv_mem_centerIn_of_mem_CJ_mul_inv_of_qH_eq_t (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {g : ↥(H z)}
    (hg : qH D g = (⟨t, t_mem_A⟩ : QA45.originalSubgroup))
    (hgσ : g * (sigma1Nine (z := z) D * σ₂⁻¹) = (sigma1Nine (z := z) D * σ₂⁻¹) * g) {b : G}
    (hb : b ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) :
    (g : G) * b * (g : G)⁻¹ * b⁻¹ ∈ centerIn (J z) := by
  obtain ⟨a, ha, q, hq, rfl⟩ := exists_mul_of_mem_CJ_mul_inv D h hEq hb
  have hgP : g ∈ P_H D := by
    rw [mem_P_H_iff, hg]
    exact t_mem_Q
  have he₁ := conj_mul_inv_mem_centerIn_of_mem_P_H D h hσ₂ hq₂ hEq hgP ha
  have he₂ := conj_mul_inv_mem_zpowers_of_mem_inf_sigma1Commutator D h hσ₂ hq₂ hcomm hEq hg hgσ hq
  have hzZ : Subgroup.zpowers z ≤ centerIn (J z) :=
    Subgroup.zpowers_le.mpr ⟨z_mem_J h, z_centralizes_J h⟩
  set e₁ := (g : G) * a * (g : G)⁻¹ * a⁻¹ with he₁_def
  set e₂ := (g : G) * q * (g : G)⁻¹ * q⁻¹ with he₂_def
  have haJ : a ∈ J z := (mem_CJ.mp ha).2
  have he₂a : e₂ * a = a * e₂ :=
    (Subgroup.mem_centralizer_iff.mp (hzZ he₂).2 a haJ).symm
  have e : (g : G) * (a * q) * (g : G)⁻¹ * (a * q)⁻¹ = e₁ * e₂ := by
    calc (g : G) * (a * q) * (g : G)⁻¹ * (a * q)⁻¹
        = e₁ * (a * e₂) * a⁻¹ := by rw [he₁_def, he₂_def]; group
      _ = e₁ * (e₂ * a) * a⁻¹ := by rw [he₂a]
      _ = e₁ * e₂ := by group
  rw [e]
  exact (centerIn (J z)).mul_mem he₁ (hzZ he₂)

end CFSG.RankThree.GF2n.Parrott
