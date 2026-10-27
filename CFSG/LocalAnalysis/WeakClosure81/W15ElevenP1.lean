module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem relIndex_sup_eq_relIndex_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B h) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

theorem mem_tSub15_iff {M V₀ V U P : Subgroup G} {x : G} :
    x ∈ tSub15 M V₀ V U P ↔ x ∈ P ∧ x ∈ F11.CTilde M V₀ V ∧
      x ∈ centralizer (v1Sub15 V₀ U : Set G) := by
  unfold tSub15
  simp only [Subgroup.mem_inf, and_assoc]

theorem tSub15_le_P (M V₀ V U P : Subgroup G) : tSub15 M V₀ V U P ≤ P :=
  fun _ hx => (mem_tSub15_iff.1 hx).1

theorem tSub15_le_cTilde (M V₀ V U P : Subgroup G) :
    tSub15 M V₀ V U P ≤ F11.CTilde M V₀ V :=
  fun _ hx => (mem_tSub15_iff.1 hx).2.1

theorem tSub15_le_centralizer (M V₀ V U P : Subgroup G) :
    tSub15 M V₀ V U P ≤ centralizer (v1Sub15 V₀ U : Set G) :=
  fun _ hx => (mem_tSub15_iff.1 hx).2.2

theorem le_tSub15 {M V₀ V U P A : Subgroup G} (hP : A ≤ P) (hC : A ≤ F11.CTilde M V₀ V)
    (hV₁ : A ≤ centralizer (v1Sub15 V₀ U : Set G)) : A ≤ tSub15 M V₀ V U P :=
  fun _ hx => mem_tSub15_iff.2 ⟨hP hx, hC hx, hV₁ hx⟩

namespace Cfg1511

variable {M V₀ V U S H P Q₀ : Subgroup G} {p : ℕ}

theorem tSub15_le_H (c : Cfg1511 M V₀ V U S H P Q₀ p) : tSub15 M V₀ V U P ≤ H :=
  (tSub15_le_P M V₀ V U P).trans c.hyp.P_le

theorem tSub15_le_normalizer_kHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    tSub15 M V₀ V U P ≤ normalizer (kHull15 V₀ H : Set G) :=
  c.tSub15_le_H.trans (Hyp1510.le_normalizer_kHull15 V₀ H)

theorem kHull15_sup_tSub15_le_H (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    kHull15 V₀ H ⊔ tSub15 M V₀ V U P ≤ H :=
  sup_le c.hyp.kHull15_le c.tSub15_le_H

theorem V_le_tSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) : V ≤ tSub15 M V₀ V U P := by
  refine le_tSub15 (c.cex.V_le_S.trans c.hyp.S_le) ?_ ?_
  · intro x hx
    rw [FourteenTwo.mem_cTilde_iff_comm]
    refine ⟨c.cex.hyp.le_M hx, ?_, ?_⟩
    · rw [c.cex.hyp.h6.normalizer₀ c.cex.hyp.ne_bot]
      exact c.cex.hyp.le_M hx
    · intro v hv
      have hcomm : x * v = v * x :=
        B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hx hv
      have h1 : x * v * x⁻¹ * v⁻¹ = 1 := by
        rw [hcomm]
        group
      rw [h1]
      exact V₀.one_mem
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian
      (c.cex.hyp.h6.le (v1Sub15_le_left V₀ U hy)) hx

theorem U_le_tSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) : U ≤ tSub15 M V₀ V U P :=
  c.cex.le.trans c.V_le_tSub15

theorem V₀_le_tSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) : V₀ ≤ tSub15 M V₀ V U P :=
  c.cex.hyp.h6.le.trans c.V_le_tSub15

theorem iHull15_le_tSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    iHull15 V₀ U H ≤ tSub15 M V₀ V U P := by
  refine le_tSub15 (c.hyp.iHull15_le_P c.cex) ?_ ?_
  · intro x hx
    rw [FourteenTwo.mem_cTilde_iff_comm]
    refine ⟨c.P_le_M (c.hyp.iHull15_le_P c.cex hx), ?_, ?_⟩
    · rw [c.cex.hyp.h6.normalizer₀ c.cex.hyp.ne_bot]
      exact c.P_le_M (c.hyp.iHull15_le_P c.cex hx)
    · intro v hv
      obtain ⟨w, hw, u, hu, hwu⟩ := c.cex.decomp hv
      have hxu : u * x = x * u :=
        c.hyp.comm_iHull15_sup u (Subgroup.mem_sup_right hu) x (Subgroup.mem_sup_left hx)
      have hxN : x ∈ normalizer (V₀ : Set G) := by
        rw [c.cex.hyp.h6.normalizer₀ c.cex.hyp.ne_bot]
        exact c.P_le_M (c.hyp.iHull15_le_P c.cex hx)
      have hxwx : x * w * x⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hxN w).1 hw
      have hxux : x * u * x⁻¹ = u := by
        rw [← hxu]
        group
      have hid : x * (w * u) * x⁻¹ * (w * u)⁻¹ = (x * w * x⁻¹) * w⁻¹ := by
        calc x * (w * u) * x⁻¹ * (w * u)⁻¹
            = (x * w * x⁻¹) * (x * u * x⁻¹) * (u⁻¹ * w⁻¹) := by group
          _ = (x * w * x⁻¹) * w⁻¹ := by
              rw [hxux]
              group
      rw [hwu, hid]
      exact V₀.mul_mem hxwx (V₀.inv_mem hw)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact c.hyp.comm_iHull15_sup y
      (Subgroup.mem_sup_left (Hyp1510.v1Sub15_le_iHull15 V₀ U H hy))
      x (Subgroup.mem_sup_left hx)

theorem inf_kHull15_eq (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    P ⊓ kHull15 V₀ H = V₀ ⊔ iHull15 V₀ U H := by
  refine le_antisymm ?_ ?_
  · set Y : Subgroup G := P ⊓ kHull15 V₀ H with hY
    set W : Subgroup G := V₀ ⊔ iHull15 V₀ U H with hW
    change Y ≤ W
    have hWY : W ≤ Y := by
      rw [hW, hY]
      exact le_inf (sup_le c.hyp.V₀_le (c.hyp.iHull15_le_P c.cex))
        (sup_le (Hyp1510.V₀_le_kHull15 V₀ H) (Hyp1510.iHull15_le_kHull15 V₀ U H))
    have hY2 : IsPGroup 2 Y := by
      rw [hY]
      exact c.hyp.sylow.isPGroup.to_le inf_le_left
    obtain ⟨k, hk⟩ := hY2.exists_card_eq
    have hdvd : W.relIndex Y ∣ Nat.card Y := Subgroup.index_dvd_card (W.subgroupOf Y)
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hYK : Y ≤ kHull15 V₀ H := by
      rw [hY]
      exact inf_le_right
    have hrel : W.relIndex Y * Y.relIndex (kHull15 V₀ H)
        = W.relIndex (kHull15 V₀ H) :=
      Subgroup.relIndex_mul_relIndex W Y (kHull15 V₀ H) hWY hYK
    have hnot2 : ¬ 2 ∣ W.relIndex (kHull15 V₀ H) := by
      rw [hW]
      exact c.isSylowIn_two_sup.not_dvd_relIndex
    have hnotY : ¬ 2 ∣ W.relIndex Y := fun h2 =>
      hnot2 (hrel ▸ dvd_mul_of_dvd_left h2 _)
    have hj0 : j = 0 := by
      by_contra hjn
      exact hnotY (hj ▸ dvd_pow_self 2 hjn)
    rw [hj0, pow_zero] at hj
    exact Subgroup.relIndex_eq_one.1 hj
  · exact le_inf (sup_le c.hyp.V₀_le (c.hyp.iHull15_le_P c.cex))
      (sup_le (Hyp1510.V₀_le_kHull15 V₀ H) (Hyp1510.iHull15_le_kHull15 V₀ U H))

theorem tSub15_inf_kHull15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    tSub15 M V₀ V U P ⊓ kHull15 V₀ H = V₀ ⊔ iHull15 V₀ U H := by
  refine le_antisymm ?_ ?_
  · calc tSub15 M V₀ V U P ⊓ kHull15 V₀ H
        ≤ P ⊓ kHull15 V₀ H := inf_le_inf_right _ (tSub15_le_P M V₀ V U P)
      _ = V₀ ⊔ iHull15 V₀ U H := c.inf_kHull15_eq
  · exact le_inf (sup_le c.V₀_le_tSub15 c.iHull15_le_tSub15)
      (sup_le (Hyp1510.V₀_le_kHull15 V₀ H) (Hyp1510.iHull15_le_kHull15 V₀ U H))

theorem isSylowIn_two_tSub15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    IsSylowIn 2 (tSub15 M V₀ V U P) (kHull15 V₀ H ⊔ tSub15 M V₀ V U P) := by
  refine ⟨le_sup_right, c.hyp.sylow.isPGroup.to_le (tSub15_le_P M V₀ V U P), ?_⟩
  have h1 : (tSub15 M V₀ V U P).relIndex (kHull15 V₀ H ⊔ tSub15 M V₀ V U P)
      = (tSub15 M V₀ V U P).relIndex (kHull15 V₀ H) :=
    relIndex_sup_eq_relIndex_of_le_normalizer (A := kHull15 V₀ H)
      (B := tSub15 M V₀ V U P) c.tSub15_le_normalizer_kHull15
  rw [h1]
  have h2 : (tSub15 M V₀ V U P).relIndex (kHull15 V₀ H)
      = (tSub15 M V₀ V U P ⊓ kHull15 V₀ H).relIndex (kHull15 V₀ H) :=
    (Subgroup.inf_relIndex_right (tSub15 M V₀ V U P) (kHull15 V₀ H)).symm
  rw [h2, c.tSub15_inf_kHull15]
  exact c.isSylowIn_two_sup.not_dvd_relIndex

theorem qSub15_le_tSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    qSub15 M V₀ V U H P ≤ tSub15 M V₀ V U P :=
  pCoreOf_le_of_isSylowIn c.isSylowIn_two_tSub15

theorem not_commutator_le_iHull15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) : ¬ ⁅Q₀, V₀⁆ ≤ iHull15 V₀ U H := fun h =>
  c.not_le_iHull15 (c.le_commutator_sup.trans (sup_le h le_rfl))

theorem iHull15_le_pCoreOf_kHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    iHull15 V₀ U H ≤ pCoreOf 2 (kHull15 V₀ H) := by
  have hp : IsPGroup 2 (iHull15 V₀ U H) :=
    c.hyp.sylow.isPGroup.to_le (c.hyp.iHull15_le_P c.cex)
  have hK : kHull15 V₀ H ≤ normalizer (iHull15 V₀ U H : Set G) :=
    c.hyp.kHull15_le.trans (Hyp1510.le_normalizer_iHull15 V₀ U H)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Hyp1510.iHull15_le_kHull15 V₀ U H) hK hp

private theorem b15_exists_mul_of_mem_pCoreOf (c : Cfg1511 M V₀ V U S H P Q₀ p) {y : G}
    (hy : y ∈ pCoreOf 2 (kHull15 V₀ H)) :
    ∃ w ∈ V₀, ∃ i ∈ iHull15 V₀ U H, y = w * i := by
  have hyW : y ∈ V₀ ⊔ iHull15 V₀ U H := pCoreOf_le_of_isSylowIn c.isSylowIn_two_sup hy
  have hnorm : V₀ ≤ normalizer (iHull15 V₀ U H : Set G) :=
    c.hyp.V₀_le_H.trans (Hyp1510.le_normalizer_iHull15 V₀ U H)
  have hyW' : y ∈ (V₀ : Set G) * (iHull15 V₀ U H : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right V₀ (iHull15 V₀ U H) hnorm]
    exact hyW
  obtain ⟨w, hw, i, hi, hwi⟩ := hyW'
  exact ⟨w, hw, i, hi, hwi.symm⟩

private theorem b15_inf_pCoreOf_Q₀_le_iHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    pCoreOf 2 (kHull15 V₀ H) ⊓ Q₀ ≤ iHull15 V₀ U H := by
  intro y hy
  obtain ⟨hyY, hyQ⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨w, hw, i, hi, hwi⟩ := b15_exists_mul_of_mem_pCoreOf c hyY
  rw [hwi] at hyQ
  have hwQ : w ∈ Q₀ := by
    have h1 : (w * i) * i⁻¹ ∈ Q₀ := Q₀.mul_mem hyQ (Q₀.inv_mem (c.odd.iHull_le hi))
    simpa [mul_assoc] using h1
  have hwV1 : w ∈ v1Sub15 V₀ U := by
    rw [← c.inf_eq]
    exact Subgroup.mem_inf.2 ⟨hwQ, hw⟩
  rw [hwi]
  exact (iHull15 V₀ U H).mul_mem (Hyp1510.v1Sub15_le_iHull15 V₀ U H hwV1) hi

private theorem b15_commutator_mem_iHull15_of_mem_iHull (c : Cfg1511 M V₀ V U S H P Q₀ p)
    {q u : G} (hq : q ∈ Q₀) (hu : u ∈ iHull15 V₀ U H) :
    ⁅q, u⁆ ∈ iHull15 V₀ U H := by
  have hQI : Q₀ ≤ normalizer (iHull15 V₀ U H : Set G) :=
    c.odd.le_kHull.trans (c.hyp.kHull15_le.trans (Hyp1510.le_normalizer_iHull15 V₀ U H))
  have h1 : q * u * q⁻¹ ∈ iHull15 V₀ U H :=
    (Subgroup.mem_normalizer_iff.1 (hQI hq) u).1 hu
  have h2 : (q * u * q⁻¹) * u⁻¹ ∈ iHull15 V₀ U H :=
    (iHull15 V₀ U H).mul_mem h1 ((iHull15 V₀ U H).inv_mem hu)
  simpa [commutatorElement_def] using h2

private theorem b15_conj_mem_iHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p)
    {w x : G} (hw : w ∈ V₀) (hx : x ∈ iHull15 V₀ U H) :
    w * x * w⁻¹ ∈ iHull15 V₀ U H :=
  (Subgroup.mem_normalizer_iff.1
    ((c.hyp.V₀_le_H.trans (Hyp1510.le_normalizer_iHull15 V₀ U H)) hw) x).1 hx

private theorem b15_commutator_mem_iHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    ∀ q ∈ Q₀, ∀ y ∈ pCoreOf 2 (kHull15 V₀ H), ⁅q, y⁆ ∈ iHull15 V₀ U H := by
  intro q hq y hy
  have hYnorm : kHull15 V₀ H ≤ normalizer (pCoreOf 2 (kHull15 V₀ H) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kHull15 V₀ H)
  have hqK : q ∈ kHull15 V₀ H := c.odd.le_kHull hq
  have hconjY : q * y * q⁻¹ ∈ pCoreOf 2 (kHull15 V₀ H) :=
    (Subgroup.mem_normalizer_iff.1 (hYnorm hqK) y).1 hy
  have hmemY : ⁅q, y⁆ ∈ pCoreOf 2 (kHull15 V₀ H) := by
    rw [commutatorElement_def]
    exact (pCoreOf 2 (kHull15 V₀ H)).mul_mem hconjY
      ((pCoreOf 2 (kHull15 V₀ H)).inv_mem hy)
  have hyK : y ∈ kHull15 V₀ H :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (kHull15 V₀ H) hy
  have hconjQ : y * q⁻¹ * y⁻¹ ∈ Q₀ :=
    (Subgroup.mem_normalizer_iff.1 (c.odd.normal (c.hyp.kHull15_le hyK)) q⁻¹).1
      (Q₀.inv_mem hq)
  have hmemQ : ⁅q, y⁆ ∈ Q₀ := by
    rw [commutatorElement_def]
    simpa [mul_assoc] using Q₀.mul_mem hq hconjQ
  exact b15_inf_pCoreOf_Q₀_le_iHull15 c (Subgroup.mem_inf.2 ⟨hmemY, hmemQ⟩)

theorem pCoreOf_kHull15_le
    (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    pCoreOf 2 (kHull15 V₀ H) ≤ iHull15 V₀ U H := by
  by_contra hle
  obtain ⟨y, hyY, hyI⟩ := SetLike.not_le_iff_exists.1 hle
  obtain ⟨w, hw, i, hi, hwi⟩ := b15_exists_mul_of_mem_pCoreOf c hyY
  have hwV1 : w ∉ v1Sub15 V₀ U := by
    intro hw1
    apply hyI
    rw [hwi]
    exact (iHull15 V₀ U H).mul_mem (Hyp1510.v1Sub15_le_iHull15 V₀ U H hw1) hi
  have hqi : ∀ q ∈ Q₀, ⁅q, w⁆ ∈ iHull15 V₀ U H := by
    intro q hq
    have hyd : ⁅q, y⁆ ∈ iHull15 V₀ U H := b15_commutator_mem_iHull15 c q hq y hyY
    have hi_comm : ⁅q, i⁆ ∈ iHull15 V₀ U H :=
      b15_commutator_mem_iHull15_of_mem_iHull c hq hi
    have hconji : w * ⁅q, i⁆ * w⁻¹ ∈ iHull15 V₀ U H :=
      b15_conj_mem_iHull15 c hw hi_comm
    have hid : ⁅q, w * i⁆ = ⁅q, w⁆ * (w * ⁅q, i⁆ * w⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    rw [hwi] at hyd
    rw [hid] at hyd
    have heq : ⁅q, w⁆
        = (⁅q, w⁆ * (w * ⁅q, i⁆ * w⁻¹)) * (w * ⁅q, i⁆ * w⁻¹)⁻¹ := by
      group
    rw [heq]
    exact (iHull15 V₀ U H).mul_mem hyd ((iHull15 V₀ U H).inv_mem hconji)
  refine c.not_commutator_le_iHull15 (Subgroup.commutator_le.2 fun q hq v hv => ?_)
  by_cases hv1 : v ∈ v1Sub15 V₀ U
  · exact b15_commutator_mem_iHull15_of_mem_iHull c hq
      (Hyp1510.v1Sub15_le_iHull15 V₀ U H hv1)
  · have hv1mem : w⁻¹ * v ∈ v1Sub15 V₀ U :=
      inv_mul_mem_of_relIndex_eq_two (c.w81.relIndex_eq_two c.std c.cex) hw hv hwV1 hv1
    have hv_eq : v = w * (w⁻¹ * v) := by group
    have hid : ⁅q, v⁆ = ⁅q, w⁆ * (w * ⁅q, w⁻¹ * v⁆ * w⁻¹) := by
      rw [hv_eq, commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    rw [hid]
    exact (iHull15 V₀ U H).mul_mem (hqi q hq)
      (b15_conj_mem_iHull15 c hw (b15_commutator_mem_iHull15_of_mem_iHull c hq
        (Hyp1510.v1Sub15_le_iHull15 V₀ U H hv1mem)))

theorem pCoreOf_kHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    pCoreOf 2 (kHull15 V₀ H) = iHull15 V₀ U H :=
  le_antisymm c.pCoreOf_kHull15_le c.iHull15_le_pCoreOf_kHull15

theorem iHull15_le_qSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    iHull15 V₀ U H ≤ qSub15 M V₀ V U H P := by
  have hp : IsPGroup 2 (iHull15 V₀ U H) :=
    c.hyp.sylow.isPGroup.to_le (c.hyp.iHull15_le_P c.cex)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((Hyp1510.iHull15_le_kHull15 V₀ U H).trans le_sup_left)
    (c.kHull15_sup_tSub15_le_H.trans (Hyp1510.le_normalizer_iHull15 V₀ U H)) hp

theorem qSub15_inf_kHull15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    qSub15 M V₀ V U H P ⊓ kHull15 V₀ H = iHull15 V₀ U H := by
  refine le_antisymm ?_ ?_
  · have hKnormQ : kHull15 V₀ H ≤ normalizer (qSub15 M V₀ V U H P : Set G) :=
      le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
        (kHull15 V₀ H ⊔ tSub15 M V₀ V U P))
    have hp : IsPGroup 2 ((qSub15 M V₀ V U H P ⊓ kHull15 V₀ H : Subgroup G)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
        (kHull15 V₀ H ⊔ tSub15 M V₀ V U P)).to_le inf_le_left
    have hn : kHull15 V₀ H ≤ normalizer ((qSub15 M V₀ V U H P ⊓ kHull15 V₀ H :
        Subgroup G) : Set G) :=
      (le_inf hKnormQ (kHull15 V₀ H).le_normalizer).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := qSub15 M V₀ V U H P)
          (K := kHull15 V₀ H))
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hn hp
    rwa [c.pCoreOf_kHull15] at hle
  · exact le_inf c.iHull15_le_qSub15 (Hyp1510.iHull15_le_kHull15 V₀ U H)

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
