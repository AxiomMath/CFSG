module

public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.RankThree.GF2n.Parrott.Section2Products

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {G : Type} [Group G] [Finite G] {z : G}

section Model

theorem commutator_QP45_eq_top : _root_.commutator ↥QP45.originalSubgroup = ⊤ := by
  haveI := isSimpleGroup_QP45_of_model
  rcases (instNormalCommutator ↥QP45.originalSubgroup).eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Dickson.I271.nonabelian_QP45
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact hab (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top a)) b
      (Subgroup.mem_top b)).symm
  · exact h

theorem QP45_subgroupOf_le_commutator_QA45 :
    QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤
      _root_.commutator ↥QA45.originalSubgroup := by
  intro a ha
  have hmem : (⟨(a : Equiv.Perm (Fin 45)), Subgroup.mem_subgroupOf.mp ha⟩ :
      ↥QP45.originalSubgroup) ∈ _root_.commutator ↥QP45.originalSubgroup := by
    rw [commutator_QP45_eq_top]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem (Subgroup.inclusion QP45_le_QA45) hmem
  rw [commutator_def, Subgroup.map_commutator] at hmap
  have hle : ⁅(⊤ : Subgroup ↥QP45.originalSubgroup).map (Subgroup.inclusion QP45_le_QA45),
      (⊤ : Subgroup ↥QP45.originalSubgroup).map (Subgroup.inclusion QP45_le_QA45)⁆ ≤
      _root_.commutator ↥QA45.originalSubgroup := by
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  exact hle hmap

end Model

section Main

variable [hN : ((J z).subgroupOf (H z)).Normal]

theorem conj_mem_CJ_of_commute {g σ : G} (hg : g ∈ H z) (hcomm : g * σ = σ * g) {y : G}
    (hy : y ∈ CJ z σ) : g * y * g⁻¹ ∈ CJ z σ := by
  obtain ⟨hyc, hyJ⟩ := mem_CJ.mp hy
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  refine mem_CJ.mpr ⟨?_, (Subgroup.mem_normalizer_iff.mp (hHN hg) y).mp hyJ⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
  have h1 : g⁻¹ * σ = σ * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  calc g * y * g⁻¹ * σ = g * y * (g⁻¹ * σ) := by group
    _ = g * y * (σ * g⁻¹) := by rw [h1]
    _ = g * (y * σ) * g⁻¹ := by group
    _ = g * (σ * y) * g⁻¹ := by rw [hyc]
    _ = g * σ * y * g⁻¹ := by group
    _ = σ * g * y * g⁻¹ := by rw [hcomm]
    _ = σ * (g * y * g⁻¹) := by group

theorem card_CJ_modEq_card_inf_CJ {σ₁ σ₂ : G} (hσ₂ : σ₂ ∈ H z) (hcomm : σ₂ * σ₁ = σ₁ * σ₂)
    (h3 : σ₂ ^ 3 = 1) :
    Nat.card ↥(CJ z σ₁) ≡ Nat.card ↥(CJ z σ₁ ⊓ CJ z σ₂) [MOD 3] := by
  classical
  haveI : Fintype ↥(CJ z σ₁) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Function.End ↥(CJ z σ₁) := fun y =>
    ⟨σ₂ * (y : G) * σ₂⁻¹, conj_mem_CJ_of_commute (z := z) hσ₂ hcomm y.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    show σ₂ * (σ₂ * (σ₂ * (y : G) * σ₂⁻¹) * σ₂⁻¹) * σ₂⁻¹ = (y : G)
    have h3' : σ₂ * σ₂ * σ₂ = 1 := by rw [← pow_three']; exact h3
    calc σ₂ * (σ₂ * (σ₂ * (y : G) * σ₂⁻¹) * σ₂⁻¹) * σ₂⁻¹ =
        (σ₂ * σ₂ * σ₂) * (y : G) * (σ₂ * σ₂ * σ₂)⁻¹ := by group
      _ = (y : G) := by rw [h3']; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  have hcard : Nat.card ↑(Function.fixedPoints f) = Nat.card ↥(CJ z σ₁ ⊓ CJ z σ₂) :=
    Nat.card_congr
    { toFun := fun y => ⟨y.1, Subgroup.mem_inf.mpr ⟨y.1.2, by
          refine mem_CJ.mpr ⟨?_, (mem_CJ.mp y.1.2).2⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hy : σ₂ * (y.1 : G) * σ₂⁻¹ = (y.1 : G) := congrArg Subtype.val y.2
          calc (y.1 : G) * σ₂ = σ₂ * (y.1 : G) * σ₂⁻¹ * σ₂ := by rw [hy]
            _ = σ₂ * (y.1 : G) := by group⟩⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩, by
          apply Subtype.ext
          show σ₂ * (x.1 : G) * σ₂⁻¹ = (x.1 : G)
          have hx := (Subgroup.mem_centralizer_singleton_iff.mp
            (mem_CJ.mp (Subgroup.mem_inf.mp x.2).2).1)
          rw [← hx]
          group⟩
      left_inv := fun y => rfl
      right_inv := fun x => rfl }
  rw [hcard] at hmod
  exact hmod

theorem centerIn_le_CJ_of_conjZ_eq_one {x : ↥(H z)} (hx : conjZ z x = 1) :
    centerIn (J z) ≤ CJ z (x : G) :=
  le_inf (centerIn_le_centralizer_of_conjZ_eq_one (z := z) hx) inf_le_left

theorem inf_CJ_eq_centerIn_of_forall_centralizerJ_ne (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN)
    (hIII : ∀ σ₂ : ↥(H z), orderOf σ₂ = 3 →
      qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) →
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ →
        centralizerJ (sigma1Nine (z := z) D) ≠ centralizerJ σ₂) :
    ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ ∧
      CJ z (sigma1Nine (z := z) D : G) ⊓ CJ z (σ₂ : G) = centerIn (J z) := by
  obtain ⟨σ₂, hσ₂3, hqσ₂, hcomm⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  refine ⟨σ₂, hσ₂3, hcomm, ?_⟩
  set σ₁ := sigma1Nine (z := z) D with hσ₁
  have hneG : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G) := fun heq =>
    hIII σ₂ hσ₂3 hqσ₂ hcomm (congrArg (fun K : Subgroup G => K.subgroupOf (J z)) heq)
  have hconjZ2 : conjZ z σ₂ = 1 := conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂
    (by rw [hqσ₂]; exact sigma2_mem_Q)
  have hZ1 : centerIn (J z) ≤ CJ z (σ₁ : G) :=
    centerIn_le_CJ_of_conjZ_eq_one (conjZ_sigma1Nine (z := z) h D)
  have hZ2 : centerIn (J z) ≤ CJ z (σ₂ : G) := centerIn_le_CJ_of_conjZ_eq_one hconjZ2
  have hc1 : Nat.card ↥(CJ z (σ₁ : G)) = 16 := by
    rw [card_CJ_eq_card_centralizerJ]
    exact card_centralizerJ_sigma1Nine (z := z) h D
  have hc2 : Nat.card ↥(CJ z (σ₂ : G)) = 16 := by
    have hconjV : conjV h σ₂ = conjV h (sigma2Nine (z := z) D) := by
      have hker : σ₂ * (sigma2Nine (z := z) D)⁻¹ ∈ (qH (z := z) D).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hqσ₂, qH_sigma2Nine, mul_inv_cancel]
      rw [ker_qH] at hker
      have h1 := J_le_ker_conjV h hker
      rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
    have hZJ : ∀ x : ↥(H z), conjZ z x = 1 →
        centralizerJ x ⊓ Subgroup.center (J z) = Subgroup.center (J z) := by
      intro x hx
      refine inf_eq_right.mpr fun j hj => ?_
      rw [mem_centralizerJ_iff]
      have hjZ : (j : G) ∈ centerIn (J z) := by
        have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
          rwa [QuotientV.centerIn_subgroupOf_eq_center]
        exact Subgroup.mem_subgroupOf.mp hj'
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (centerIn_le_centralizer_of_conjZ_eq_one (z := z) hx hjZ)
    have hcop : ∀ x : ↥(H z), orderOf x = 3 → Nat.Coprime (orderOf x) (Nat.card (J z)) := by
      intro x hx
      rw [hx, card_J h]
      norm_num
    have hf2 := card_centralizerJ_eq_card_inf_mul_card_autFixed h (hcop σ₂ hσ₂3)
    have hfS := card_centralizerJ_eq_card_inf_mul_card_autFixed h
      (hcop _ (orderOf_sigma2Nine (z := z) D))
    rw [hZJ σ₂ hconjZ2, hconjV] at hf2
    rw [hZJ _ (conjZ_sigma2Nine (z := z) h D), card_centralizerJ_sigma2Nine (z := z) h D] at hfS
    rw [card_CJ_eq_card_centralizerJ, hf2, ← hfS]
  have hcZ : Nat.card ↥(centerIn (J z)) = 4 := card_centerIn_J h
  have hcommG : (σ₂ : G) * (σ₁ : G) = (σ₁ : G) * (σ₂ : G) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hcomm
  have h3 : (σ₂ : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hσ₂3, pow_orderOf_eq_one, Subgroup.coe_one]
  have hmod := card_CJ_modEq_card_inf_CJ (z := z) σ₂.2 hcommG h3
  rw [hc1] at hmod
  set S := CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G) with hS
  have hZS : centerIn (J z) ≤ S := le_inf hZ1 hZ2
  have hS1 : S ≤ CJ z (σ₁ : G) := inf_le_left
  have hle16 : Nat.card S ≤ 16 := hc1 ▸ Nat.le_of_dvd (by rw [hc1]; norm_num)
    (Subgroup.card_dvd_of_le hS1)
  have hdvd4 : 4 ∣ Nat.card S := hcZ ▸ Subgroup.card_dvd_of_le hZS
  have hS16 : Nat.card S ≠ 16 := by
    intro h16
    have hEq : S = CJ z (σ₁ : G) := Subgroup.eq_of_le_of_card_ge hS1 (by rw [h16, hc1])
    have hle : CJ z (σ₁ : G) ≤ CJ z (σ₂ : G) := hEq ▸ inf_le_right
    exact hneG (Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2]))
  have hS4 : Nat.card S = 4 := by
    unfold Nat.ModEq at hmod
    omega
  exact (Subgroup.eq_of_le_of_card_ge hZS (by rw [hS4, hcZ])).symm

theorem J_le_commutator_sup_centerIn_of_forall_centralizerJ_ne (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN)
    (hIII : ∀ σ₂ : ↥(H z), orderOf σ₂ = 3 →
      qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) →
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ →
        centralizerJ (sigma1Nine (z := z) D) ≠ centralizerJ σ₂) :
    J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z) := by
  obtain ⟨σ₂, hσ₂3, hcomm, hinf⟩ := inf_CJ_eq_centerIn_of_forall_centralizerJ_ne (z := z) h D hIII
  set σ₁ := sigma1Nine (z := z) D with hσ₁
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp hN
  have hp3 : ∀ x : ↥(H z), orderOf x = 3 → IsPGroup 3 (Subgroup.zpowers (x : G)) := by
    intro x hx
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
  have hcopJ : Nat.Coprime 3 (Nat.card (J z)) := by
    rw [card_J h]
    norm_num
  have hcommG : (σ₂ : G) * (σ₁ : G) = (σ₁ : G) * (σ₂ : G) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hcomm
  have hcent : ∀ x : G, Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    intro x
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hA := le_sup_centralizer_commutator (p := 3) (Y := J z)
    (B := Subgroup.zpowers (σ₁ : G)) (hp3 σ₁ (sigma1Nine_order (z := z) D))
    (by rw [Subgroup.zpowers_le]; exact hHN σ₁.2) hcopJ
  rw [hcent, inf_comm] at hA
  have hnorm : Subgroup.zpowers (σ₂ : G) ≤ Subgroup.normalizer (CJ z (σ₁ : G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨conj_mem_CJ_of_commute (z := z) σ₂.2 hcommG, fun hy => ?_⟩
    have hcomm' : (σ₂ : G)⁻¹ * (σ₁ : G) = (σ₁ : G) * (σ₂ : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcommG, mul_assoc, mul_inv_cancel, mul_one]
    have := conj_mem_CJ_of_commute (z := z) (Subgroup.inv_mem _ σ₂.2) hcomm' hy
    simpa [mul_assoc] using this
  have hcop1 : Nat.Coprime 3 (Nat.card ↥(CJ z (σ₁ : G))) :=
    hcopJ.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hB := le_sup_centralizer_commutator (p := 3) (Y := CJ z (σ₁ : G))
    (B := Subgroup.zpowers (σ₂ : G)) (hp3 σ₂ hσ₂3) hnorm hcop1
  have hY2 : CJ z (σ₁ : G) ⊓ Subgroup.centralizer (Subgroup.zpowers (σ₂ : G) : Set G) =
      centerIn (J z) := by
    rw [hcent, ← hinf]
    ext x
    simp only [CJ, Subgroup.mem_inf]
    tauto
  rw [hY2] at hB
  have hc1 : ⁅J z, Subgroup.zpowers (σ₁ : G)⁆ ≤ ⁅H z, H z⁆ :=
    Subgroup.commutator_mono (J_le_H (z := z)) (by rw [Subgroup.zpowers_le]; exact σ₁.2)
  have hc2 : ⁅CJ z (σ₁ : G), Subgroup.zpowers (σ₂ : G)⁆ ≤ ⁅H z, H z⁆ :=
    Subgroup.commutator_mono (inf_le_right.trans (J_le_H (z := z)))
      (by rw [Subgroup.zpowers_le]; exact σ₂.2)
  calc J z ≤ CJ z (σ₁ : G) ⊔ ⁅J z, Subgroup.zpowers (σ₁ : G)⁆ := hA
    _ ≤ (centerIn (J z) ⊔ ⁅CJ z (σ₁ : G), Subgroup.zpowers (σ₂ : G)⁆) ⊔ ⁅H z, H z⁆ :=
        sup_le_sup hB hc1
    _ ≤ ⁅H z, H z⁆ ⊔ centerIn (J z) :=
        sup_le (sup_le le_sup_right (hc2.trans le_sup_left)) le_sup_left

theorem relIndex_commutator_sup_centerIn_of_forall_centralizerJ_ne (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN)
    (hIII : ∀ σ₂ : ↥(H z), orderOf σ₂ = 3 →
      qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) →
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ →
        centralizerJ (sigma1Nine (z := z) D) ≠ centralizerJ σ₂) :
    (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2 := by
  have hJ := J_le_commutator_sup_centerIn_of_forall_centralizerJ_ne (z := z) h D hIII
  have hEq : (⁅H z, H z⁆ ⊔ centerIn (J z)).subgroupOf (H z) = P_H (z := z) D := by
    apply le_antisymm
    · have hle : ⁅H z, H z⁆ ⊔ centerIn (J z) ≤ (P_H (z := z) D).map (H z).subtype := by
        refine sup_le (derived_le_P_H (z := z) (D := D)) ?_
        intro x hx
        have hxJ : x ∈ J z := (inf_le_left : centerIn (J z) ≤ J z) hx
        exact ⟨⟨x, J_le_H (z := z) hxJ⟩,
          J_le_P_H (z := z) D (Subgroup.mem_subgroupOf.mpr hxJ), rfl⟩
      calc (⁅H z, H z⁆ ⊔ centerIn (J z)).subgroupOf (H z)
          ≤ ((P_H (z := z) D).map (H z).subtype).subgroupOf (H z) := Subgroup.comap_mono hle
        _ = P_H (z := z) D :=
            Subgroup.comap_map_eq_self_of_injective (H z).subtype_injective _
    · intro x hx
      rw [mem_P_H_iff] at hx
      have hcomm := QP45_subgroupOf_le_commutator_QA45 hx
      have hmap : _root_.commutator ↥QA45.originalSubgroup =
          (_root_.commutator ↥(H z)).map (qH (z := z) D) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (qH_surjective (z := z) D)]
      rw [hmap] at hcomm
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hcomm
      have hyG : (y : G) ∈ ⁅H z, H z⁆ := by
        have := Subgroup.mem_map_of_mem (H z).subtype hy
        rwa [Subgroup.map_subtype_commutator] at this
      have hker : y⁻¹ * x ∈ (qH (z := z) D).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      rw [ker_qH] at hker
      have hJx : ((y⁻¹ * x : ↥(H z)) : G) ∈ J z := Subgroup.mem_subgroupOf.mp hker
      rw [Subgroup.mem_subgroupOf]
      have hx_eq : (x : G) = (y : G) * ((y⁻¹ * x : ↥(H z)) : G) := by simp
      rw [hx_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyG) (hJ hJx)
  show ((⁅H z, H z⁆ ⊔ centerIn (J z)).subgroupOf (H z)).index = 2
  rw [hEq]
  exact index_P_H (z := z) D

theorem centralizerJ_ne_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    centralizerJ (sigma1Nine (z := z) D) ≠ centralizerJ σ₂ :=
  fun hEq => hIII ⟨σ₂, hσ₂, hq, hEq⟩

theorem J_le_commutator_sup_centerIn_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z) :=
  J_le_commutator_sup_centerIn_of_forall_centralizerJ_ne h D
    fun _ hσ₂ hq _ => centralizerJ_ne_of_not_equalityBranch h D hIII hσ₂ hq

theorem relIndex_commutator_sup_centerIn_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2 :=
  relIndex_commutator_sup_centerIn_of_forall_centralizerJ_ne h D
    fun _ hσ₂ hq _ => centralizerJ_ne_of_not_equalityBranch h D hIII hσ₂ hq

end Main

end CFSG.RankThree.GF2n.Parrott
