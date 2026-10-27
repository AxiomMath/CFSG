module

public import CFSG.RankThree.GF2n.Parrott.A1LocalData
public import CFSG.RankThree.GF2n.Parrott.CentralizerFusion
import all CFSG.RankThree.GF2n.Parrott.CentralizerJoinQA45

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Model

open CentralizerJoinQA45Aux

private theorem f45_mul_self : f45 * f45 = 1 := by decide +kernel

private theorem f45_conj_mem_QP45
    {w : Equiv.Perm (Fin 45)}
    (hw : w ∈ QP45.originalSubgroup) : f45 * w * f45 ∈ QP45.originalSubgroup := by
  have hnorm : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two index_QP45
  have hinv : f45⁻¹ = f45 := inv_eq_of_mul_eq_one_right f45_mul_self
  have h := hnorm.conj_mem ⟨w, QP45_le_QA45 hw⟩ (Subgroup.mem_subgroupOf.mpr hw) ⟨f45, f45_mem⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa [hinv] using h

private theorem sup_centralizer_sigma_QP45 :
    Subgroup.centralizer ({(⟨sigma1, sigma1_mem_Q⟩ : QP45.originalSubgroup)} :
        Set QP45.originalSubgroup) ⊔
      Subgroup.centralizer ({(⟨sigma2, sigma2_mem_Q⟩ : QP45.originalSubgroup)} :
        Set QP45.originalSubgroup) = ⊤ := by
  set C₁ : Subgroup QP45.originalSubgroup :=
    Subgroup.centralizer ({(⟨sigma1, sigma1_mem_Q⟩ : QP45.originalSubgroup)} :
      Set QP45.originalSubgroup) with hC₁
  set C₂ : Subgroup QP45.originalSubgroup :=
    Subgroup.centralizer ({(⟨sigma2, sigma2_mem_Q⟩ : QP45.originalSubgroup)} :
      Set QP45.originalSubgroup) with hC₂
  have hxQ : x45 ∈ QP45.originalSubgroup := by
    rw [QP45_closure]
    exact Subgroup.subset_closure (by simp)
  have hyQ : y45 ∈ QP45.originalSubgroup := by
    rw [QP45_closure]
    exact Subgroup.subset_closure (by simp)
  have hy2 : y45⁻¹ * y45⁻¹ ∈ QP45.originalSubgroup :=
    mul_mem (inv_mem hyQ) (inv_mem hyQ)
  have haQ : y45⁻¹ * y45⁻¹ * f45 * y45⁻¹ * y45⁻¹ * f45 ∈ QP45.originalSubgroup := by
    have e : y45⁻¹ * y45⁻¹ * f45 * y45⁻¹ * y45⁻¹ * f45 =
        (y45⁻¹ * y45⁻¹) * (f45 * (y45⁻¹ * y45⁻¹) * f45) := by group
    rw [e]
    exact mul_mem hy2 (f45_conj_mem_QP45 hy2)
  have hbQ : f45 * y45 * y45 * f45 * y45⁻¹ * y45⁻¹ ∈ QP45.originalSubgroup := by
    have e : f45 * y45 * y45 * f45 * y45⁻¹ * y45⁻¹ =
        (f45 * (y45 * y45) * f45) * (y45⁻¹ * y45⁻¹) := by group
    rw [e]
    exact mul_mem (f45_conj_mem_QP45 (mul_mem hyQ hyQ)) hy2
  let xP : QP45.originalSubgroup := ⟨x45, hxQ⟩
  let yP : QP45.originalSubgroup := ⟨y45, hyQ⟩
  let aP : QP45.originalSubgroup := ⟨_, haQ⟩
  let bP : QP45.originalSubgroup := ⟨_, hbQ⟩
  have hx₁ : xP ∈ C₁ := by
    rw [hC₁, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext t_commute_sigma1
  have ha₂ : aP ∈ C₂ := by
    rw [hC₂, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext a_comm
  have hb₁ : bP ∈ C₁ := by
    rw [hC₁, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext b_comm
  have hxS : xP ∈ C₁ ⊔ C₂ := (le_sup_left : C₁ ≤ C₁ ⊔ C₂) hx₁
  have hyS : yP ∈ C₁ ⊔ C₂ := by
    have e : aP * bP = yP := Subtype.ext y45_eq_mul.symm
    rw [← e]
    exact (C₁ ⊔ C₂).mul_mem ((le_sup_right : C₂ ≤ C₁ ⊔ C₂) ha₂)
      ((le_sup_left : C₁ ≤ C₁ ⊔ C₂) hb₁)
  have hle : Subgroup.closure ({x45, y45} : Set (Equiv.Perm (Fin 45))) ≤
      (C₁ ⊔ C₂).map QP45.originalSubgroup.subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨xP, hxS, rfl⟩
    · exact ⟨yP, hyS, rfl⟩
  rw [eq_top_iff]
  intro g _
  have hg : (g : Equiv.Perm (Fin 45)) ∈
      Subgroup.closure ({x45, y45} : Set (Equiv.Perm (Fin 45))) := by
    rw [← QP45_closure]
    exact g.2
  obtain ⟨s, hs, hsg⟩ := hle hg
  have e : s = g := Subtype.ext hsg
  rwa [e] at hs

end Model

private theorem map_centralizer_qHP_of_orderOf_three
    [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientDataPSp (z := z) hN) (x : ↥(H z)) (hx : orderOf x = 3) :
    (Subgroup.centralizer ({x} : Set ↥(H z))).map (qHP D) =
      Subgroup.centralizer ({qHP D x} : Set QP45.originalSubgroup) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]
  · intro w hw
    obtain ⟨m₀, rfl⟩ := qHP_surjective D w
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hP : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    rw [Subgroup.mem_centralizer_singleton_iff] at hw
    obtain ⟨m, -, hm, hcomm⟩ := exists_commute_mem_fibre (qHP D) hP le_top
      (not_three_dvd_card_ker_inf D ⊤) (Subgroup.mem_top m₀) (by
        intro g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        rw [map_zpow]
        exact (Commute.zpow_left (Commute.symm hw) k).eq)
    have hmC : m ∈ Subgroup.centralizer ({x} : Set ↥(H z)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm x (Subgroup.mem_zpowers x)).symm
    exact Subgroup.mem_map.mpr ⟨m, hmC, hm⟩

private theorem sup_J_centralizer_s1HP_s2HP_eq_top
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN) :
    (J z).subgroupOf (H z) ⊔ Subgroup.centralizer ({s1HP D} : Set ↥(H z)) ⊔
      Subgroup.centralizer ({s2HP D} : Set ↥(H z)) = ⊤ := by
  set T : Subgroup ↥(H z) := (J z).subgroupOf (H z) ⊔
    Subgroup.centralizer ({s1HP D} : Set ↥(H z)) ⊔
      Subgroup.centralizer ({s2HP D} : Set ↥(H z)) with hT
  have hker : (qHP D).ker ≤ T := by
    rw [ker_qHP D]
    exact le_trans le_sup_left le_sup_left
  have hJ : ((J z).subgroupOf (H z)).map (qHP D) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (ker_qHP D).ge
  have hmap : T.map (qHP D) = ⊤ := by
    rw [hT, Subgroup.map_sup, Subgroup.map_sup, hJ,
      map_centralizer_qHP_of_orderOf_three D _ (orderOf_s1HP D),
      map_centralizer_qHP_of_orderOf_three D _ (orderOf_s2HP D), qHP_s1HP, qHP_s2HP,
      bot_sup_eq]
    exact sup_centralizer_sigma_QP45
  rw [← Subgroup.comap_map_eq_self hker, hmap, Subgroup.comap_top]

private theorem mem_normalizer_CJ_of_commute {σ c : G} (hc : c ∈ H z) (hcσ : c * σ = σ * c) :
    c ∈ Subgroup.normalizer (CJ z σ : Set G) := by
  have key : ∀ {d : G}, Commute d σ → d ∈ Subgroup.normalizer (J z : Set G) →
      ∀ {y : G}, y ∈ CJ z σ → d * y * d⁻¹ ∈ CJ z σ := by
    intro d hdσ hdJ y hy
    obtain ⟨hyσ, hyJ⟩ := mem_CJ.mp hy
    refine mem_CJ.mpr ⟨?_, (Subgroup.mem_normalizer_iff.mp hdJ y).mp hyJ⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyσ ⊢
    exact ((hdσ.mul_left hyσ).mul_left hdσ.inv_left).eq
  have hcJ : c ∈ Subgroup.normalizer (J z : Set G) := J_le_normalizer_A hc
  have hc' : Commute c σ := hcσ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key hc' hcJ
  · intro hy
    have h' := key hc'.inv_left (inv_mem hcJ) hy
    simpa [mul_assoc] using h'

private theorem J_le_normalizer_CJ_A1 (h : Tim79a.ParrottHypA1 z) {σ : G} (hσ : σ ∈ H z) :
    J z ≤ Subgroup.normalizer (CJ z σ : Set G) := by
  have hzC : z ∈ CJ z σ := mem_CJ.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hσ).symm, z_mem_J_A1 h⟩
  have hconj : ∀ {j x : G}, j ∈ J z → x ∈ CJ z σ → j * x * j⁻¹ ∈ CJ z σ := by
    intro j x hj hx
    have hcomm : ⁅j, x⁆ ∈ CJ z σ := by
      apply Subgroup.zpowers_le.mpr hzC
      rw [← h.commutator]
      exact Subgroup.commutator_mem_commutator hj (mem_CJ.mp hx).2
    have e : j * x * j⁻¹ = ⁅j, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (CJ z σ).mul_mem hcomm hx
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj hj
  · intro hx
    have h' := hconj ((J z).inv_mem hj) hx
    simpa [mul_assoc] using h'

theorem H_le_normalizer_CJ_s1HP_A1
    (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    H z ≤ Subgroup.normalizer (CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) : Set G) := by
  set D := quotientDataA1 h with hD
  set N : Subgroup ↥(H z) :=
    (Subgroup.normalizer (CJ z ((s1HP D : ↥(H z)) : G) : Set G)).comap (H z).subtype with hNdef
  have hJN : (J z).subgroupOf (H z) ≤ N := fun x hx =>
    J_le_normalizer_CJ_A1 h (s1HP D).2 (Subgroup.mem_subgroupOf.mp hx)
  have hC₁ : Subgroup.centralizer ({s1HP D} : Set ↥(H z)) ≤ N := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    exact mem_normalizer_CJ_of_commute c.2 (congrArg Subtype.val hc)
  have hC₂ : Subgroup.centralizer ({s2HP D} : Set ↥(H z)) ≤ N := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    change (c : G) ∈ Subgroup.normalizer (CJ z ((s1HP D : ↥(H z)) : G) : Set G)
    rw [heq]
    exact mem_normalizer_CJ_of_commute c.2 (congrArg Subtype.val hc)
  have htop : (⊤ : Subgroup ↥(H z)) ≤ N := by
    rw [← sup_J_centralizer_s1HP_s2HP_eq_top D]
    exact sup_le (sup_le hJN hC₁) hC₂
  intro x hx
  exact htop (Subgroup.mem_top ⟨x, hx⟩)

end CFSG.RankThree.GF2n.Parrott
