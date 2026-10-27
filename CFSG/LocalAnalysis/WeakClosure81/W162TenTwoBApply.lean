module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenCore
import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeDischarge
import CFSG.RankThree.PartOne.S11d.LayerDecomp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Index

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem w162_hyp7 (h : Cex15 M V₀ V U S) : Hyp7 V₀ := by
  refine ⟨h.hyp.elemAbelian₀, ?_, h.hyp.isTI⟩
  have hp : IsPGroup 2 V₀ := h.hyp.isPGroup.to_le h.hyp.h6.le
  rw [card_eq_two_pow_mSub hp]
  calc 2 = 2 ^ 1 := by norm_num
    _ < 2 ^ mSub V₀ := Nat.pow_lt_pow_right (by norm_num) h.one_lt_mSub

end Cex15

section Lift

variable {X : Type*} [Group X] {Q J : Subgroup X}

theorem w162_pow_mem_sup (hQJ : Q ≤ normalizer (J : Set X)) {p : ℕ}
    (hpow : ∀ q ∈ Q, q ^ p ∈ J) : ∀ y ∈ Q ⊔ J, y ^ p ∈ J := by
  intro y hy
  let N : Subgroup X := normalizer (J : Set X)
  have hQN : Q ≤ N := hQJ
  have hJN : J ≤ N := Subgroup.le_normalizer
  haveI : (J.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJN).2 le_rfl
  let π : ↥N →* ↥N ⧸ J.subgroupOf N := QuotientGroup.mk' (J.subgroupOf N)
  have hπmem : ∀ z : ↥N, π z = 1 ↔ (z : X) ∈ J := by
    intro z
    change (z : ↥N ⧸ J.subgroupOf N) = 1 ↔ (z : X) ∈ J
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hy' : y ∈ (↑(Q ⊔ J) : Set X) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q J hQJ, Set.mem_mul] at hy'
  obtain ⟨q, hq, j, hj, rfl⟩ := hy'
  have hqN : q ∈ N := hQN hq
  have hjN : j ∈ N := hJN hj
  have hπ : π (⟨q, hqN⟩ * ⟨j, hjN⟩) = π ⟨q, hqN⟩ := by
    rw [map_mul, (hπmem ⟨j, hjN⟩).mpr hj, mul_one]
  have hgoal : (((⟨q, hqN⟩ * ⟨j, hjN⟩ : ↥N) ^ p : ↥N) : X) ∈ J :=
    (hπmem _).mp (by
      rw [map_pow, hπ, ← map_pow]
      exact (hπmem (⟨q, hqN⟩ ^ p)).mpr (by simpa using hpow q hq))
  simpa using hgoal

theorem w162_comm_mem_sup (hQJ : Q ≤ normalizer (J : Set X))
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ J) : ∀ x ∈ Q ⊔ J, ∀ y ∈ Q ⊔ J, ⁅x, y⁆ ∈ J := by
  intro x hx y hy
  let N : Subgroup X := normalizer (J : Set X)
  have hQN : Q ≤ N := hQJ
  have hJN : J ≤ N := Subgroup.le_normalizer
  haveI : (J.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJN).2 le_rfl
  let π : ↥N →* ↥N ⧸ J.subgroupOf N := QuotientGroup.mk' (J.subgroupOf N)
  have hπmem : ∀ z : ↥N, π z = 1 ↔ (z : X) ∈ J := by
    intro z
    change (z : ↥N ⧸ J.subgroupOf N) = 1 ↔ (z : X) ∈ J
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right Q J hQJ
  have hx' : x ∈ (↑(Q ⊔ J) : Set X) := hx
  rw [hcoe, Set.mem_mul] at hx'
  obtain ⟨q, hq, j, hj, rfl⟩ := hx'
  have hy' : y ∈ (↑(Q ⊔ J) : Set X) := hy
  rw [hcoe, Set.mem_mul] at hy'
  obtain ⟨q', hq', j', hj', rfl⟩ := hy'
  have hqN : q ∈ N := hQN hq
  have hq'N : q' ∈ N := hQN hq'
  have hjN : j ∈ N := hJN hj
  have hj'N : j' ∈ N := hJN hj'
  have hπx : π (⟨q * j, N.mul_mem hqN hjN⟩ : ↥N) = π ⟨q, hqN⟩ := by
    show π (⟨q, hqN⟩ * ⟨j, hjN⟩) = π ⟨q, hqN⟩
    rw [map_mul, (hπmem ⟨j, hjN⟩).mpr hj, mul_one]
  have hπy : π (⟨q' * j', N.mul_mem hq'N hj'N⟩ : ↥N) = π ⟨q', hq'N⟩ := by
    show π (⟨q', hq'N⟩ * ⟨j', hj'N⟩) = π ⟨q', hq'N⟩
    rw [map_mul, (hπmem ⟨j', hj'N⟩).mpr hj', mul_one]
  have hstep : π ⁅(⟨q * j, N.mul_mem hqN hjN⟩ : ↥N),
        (⟨q' * j', N.mul_mem hq'N hj'N⟩ : ↥N)⁆ =
      π ⁅(⟨q, hqN⟩ : ↥N), (⟨q', hq'N⟩ : ↥N)⁆ := by
    simp only [map_commutatorElement, hπx, hπy]
  refine (hπmem (⁅(⟨q * j, N.mul_mem hqN hjN⟩ : ↥N),
    (⟨q' * j', N.mul_mem hq'N hj'N⟩ : ↥N)⁆)).mp ?_
  rw [hstep]
  exact (hπmem _).mpr (by
    change ⁅q, q'⁆ ∈ J
    exact hcomm q hq q' hq')

theorem w162_comm_comm_mem_sup (hQJ : Q ≤ normalizer (J : Set X))
    (hcl : ∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q, ⁅⁅x, y⁆, z⁆ ∈ J) :
    ∀ x ∈ Q ⊔ J, ∀ y ∈ Q ⊔ J, ∀ z ∈ Q ⊔ J, ⁅⁅x, y⁆, z⁆ ∈ J := by
  intro x hx y hy z hz
  let N : Subgroup X := normalizer (J : Set X)
  have hQN : Q ≤ N := hQJ
  have hJN : J ≤ N := Subgroup.le_normalizer
  haveI : (J.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJN).2 le_rfl
  let π : ↥N →* ↥N ⧸ J.subgroupOf N := QuotientGroup.mk' (J.subgroupOf N)
  have hπmem : ∀ w : ↥N, π w = 1 ↔ (w : X) ∈ J := by
    intro w
    change (w : ↥N ⧸ J.subgroupOf N) = 1 ↔ (w : X) ∈ J
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right Q J hQJ
  have hx' : x ∈ (↑(Q ⊔ J) : Set X) := hx
  rw [hcoe, Set.mem_mul] at hx'
  obtain ⟨q, hq, j, hj, rfl⟩ := hx'
  have hy' : y ∈ (↑(Q ⊔ J) : Set X) := hy
  rw [hcoe, Set.mem_mul] at hy'
  obtain ⟨q', hq', j', hj', rfl⟩ := hy'
  have hz' : z ∈ (↑(Q ⊔ J) : Set X) := hz
  rw [hcoe, Set.mem_mul] at hz'
  obtain ⟨q'', hq'', j'', hj'', rfl⟩ := hz'
  have hqN : q ∈ N := hQN hq
  have hq'N : q' ∈ N := hQN hq'
  have hq''N : q'' ∈ N := hQN hq''
  have hjN : j ∈ N := hJN hj
  have hj'N : j' ∈ N := hJN hj'
  have hj''N : j'' ∈ N := hJN hj''
  have hπx : π (⟨q * j, N.mul_mem hqN hjN⟩ : ↥N) = π ⟨q, hqN⟩ := by
    show π (⟨q, hqN⟩ * ⟨j, hjN⟩) = π ⟨q, hqN⟩
    rw [map_mul, (hπmem ⟨j, hjN⟩).mpr hj, mul_one]
  have hπy : π (⟨q' * j', N.mul_mem hq'N hj'N⟩ : ↥N) = π ⟨q', hq'N⟩ := by
    show π (⟨q', hq'N⟩ * ⟨j', hj'N⟩) = π ⟨q', hq'N⟩
    rw [map_mul, (hπmem ⟨j', hj'N⟩).mpr hj', mul_one]
  have hπz : π (⟨q'' * j'', N.mul_mem hq''N hj''N⟩ : ↥N) = π ⟨q'', hq''N⟩ := by
    show π (⟨q'', hq''N⟩ * ⟨j'', hj''N⟩) = π ⟨q'', hq''N⟩
    rw [map_mul, (hπmem ⟨j'', hj''N⟩).mpr hj'', mul_one]
  have hstep : π ⁅⁅(⟨q * j, N.mul_mem hqN hjN⟩ : ↥N),
        (⟨q' * j', N.mul_mem hq'N hj'N⟩ : ↥N)⁆,
        (⟨q'' * j'', N.mul_mem hq''N hj''N⟩ : ↥N)⁆ =
      π ⁅⁅(⟨q, hqN⟩ : ↥N), (⟨q', hq'N⟩ : ↥N)⁆, (⟨q'', hq''N⟩ : ↥N)⁆ := by
    simp only [map_commutatorElement, hπx, hπy, hπz]
  refine (hπmem (⁅⁅(⟨q * j, N.mul_mem hqN hjN⟩ : ↥N),
    (⟨q' * j', N.mul_mem hq'N hj'N⟩ : ↥N)⁆,
    (⟨q'' * j'', N.mul_mem hq''N hj''N⟩ : ↥N)⁆)).mp ?_
  rw [hstep]
  exact (hπmem _).mpr (by
    change ⁅⁅q, q'⁆, q''⁆ ∈ J
    exact hcl q hq q' hq' q'' hq'')

end Lift

namespace Hyp1510

variable {M V₀ V U S H P Q₀ J : Subgroup G}

theorem w162_inf_eq_v1 (hW : W15Eight1 G) (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hP : Hyp1510 V₀ V U S H P) (hIJ : iHull15 V₀ U H ≤ J) (hJ : J ≤ pCoreOf 2 H) :
    V₀ ⊓ J = v1Sub15 V₀ U := by
  refine le_antisymm ?_ (le_inf (v1Sub15_le_left V₀ U)
    ((Hyp1510.v1Sub15_le_iHull15 V₀ U H).trans hIJ))
  rw [← hP.inf_pCoreOf_eq hW hS h]
  exact inf_le_inf_left _ hJ

theorem w162_relIndex_J (hW : W15Eight1 G) (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hP : Hyp1510 V₀ V U S H P) (hIJ : iHull15 V₀ U H ≤ J) (hJ : J ≤ pCoreOf 2 H) :
    J.relIndex V₀ = 2 := by
  rw [← Subgroup.inf_relIndex_right J V₀, inf_comm, hP.w162_inf_eq_v1 hW hS h hIJ hJ]
  exact hW.relIndex_eq_two hS h

theorem w162_Q₀_inf_eq (hP : Hyp1510 V₀ V U S H P) (hQ : OddCore15 V₀ U H Q₀)
    (hIJ : iHull15 V₀ U H ≤ J) (hJ : J ≤ pCoreOf 2 H) : Q₀ ⊓ J = iHull15 V₀ U H := by
  refine le_antisymm ?_ (le_inf hQ.iHull_le hIJ)
  rintro x ⟨hxQ, hxJ⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hp2) ⟨x, hJ hxJ⟩
  exact CFSG.RankThree.PartOne.mem_of_two_power_of_odd_index (hQ.normal_subgroupOf hP) hQ.odd hxQ
    ⟨k, by simpa [Subgroup.orderOf_mk] using hk⟩

theorem w162_faithful (hI : NamedInputs15 G) (hW : W15Eight1 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P)
    (hQ : OddCore15 V₀ U H Q₀) (hIJ : iHull15 V₀ U H ≤ J) (hJ : J ≤ pCoreOf 2 H)
    (hJn : H ≤ normalizer (J : Set G)) :
    ∀ a ∈ V₀, (∀ y ∈ Q₀ ⊔ J, ⁅a, y⁆ ∈ J) → a ∈ J := by
  intro a ha hall
  by_contra haJ
  let V₁ : Subgroup G := v1Sub15 V₀ U
  have hV₁I : V₁ ≤ iHull15 V₀ U H := Hyp1510.v1Sub15_le_iHull15 V₀ U H
  have hV₁J : V₁ ≤ J := hV₁I.trans hIJ
  have hmemJ : ∀ v ∈ J, ∀ q ∈ Q₀, ⁅v, q⁆ ∈ J := by
    intro v hvJ q hq
    have hconj : q * v⁻¹ * q⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hJn (hQ.le_H hP hq)) v⁻¹).mp (J.inv_mem hvJ)
    have he : ⁅v, q⁆ = v * (q * v⁻¹ * q⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact J.mul_mem hvJ hconj
  have hcase : ∀ v ∈ V₀, ∀ q ∈ Q₀, ⁅v, q⁆ ∈ J := by
    intro v hv q hq
    by_cases hvJ : v ∈ J
    · exact hmemJ v hvJ q hq
    · have hnota : (⟨a, ha⟩ : ↥V₀)⁻¹ ∉ V₁.subgroupOf V₀ := fun hmem => by
        have h1 : a ∈ V₁ := by
          simpa using V₁.inv_mem (by simpa using Subgroup.mem_subgroupOf.mp hmem)
        exact haJ (hIJ (hV₁I h1))
      have hnotv : (⟨v, hv⟩ : ↥V₀) ∉ V₁.subgroupOf V₀ := fun hmem => by
        have h1 : v ∈ V₁ := by simpa using Subgroup.mem_subgroupOf.mp hmem
        exact hvJ (hV₁J h1)
      have hrel : (V₁.subgroupOf V₀).index = 2 := hW.relIndex_eq_two hS h
      have hin : (⟨a, ha⟩ : ↥V₀)⁻¹ * ⟨v, hv⟩ ∈ V₁.subgroupOf V₀ :=
        (Subgroup.mul_mem_iff_of_index_two hrel).mpr (iff_of_false hnota hnotv)
      have hwV₁ : a⁻¹ * v ∈ V₁ := by simpa using Subgroup.mem_subgroupOf.mp hin
      have hwV : a⁻¹ * v ∈ V₀ := v1Sub15_le_left V₀ U hwV₁
      have hwJ : a⁻¹ * v ∈ J := hV₁J hwV₁
      have h1 : ⁅a⁻¹ * v, q⁆ ∈ J := hmemJ (a⁻¹ * v) hwJ q hq
      have hconj : a * ⁅a⁻¹ * v, q⁆ * a⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hJn (hP.V₀_le_H ha)) ⁅a⁻¹ * v, q⁆).mp h1
      have haq : ⁅a, q⁆ ∈ J := hall q (Subgroup.mem_sup_left hq)
      have he : ⁅v, q⁆ = a * ⁅a⁻¹ * v, q⁆ * a⁻¹ * ⁅a, q⁆ := by
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      rw [he]
      exact J.mul_mem hconj haq
  have hcomm_le : ⁅Q₀, V₀⁆ ≤ J := by
    refine Subgroup.commutator_le.mpr fun q hq v hv => ?_
    rw [← commutatorElement_inv v q]
    exact J.inv_mem (hcase v hv q hq)
  have hQ_le_J : Q₀ ≤ J :=
    (hQ.le_commutator_sup hI hW hS h hP).trans (sup_le hcomm_le hIJ)
  have hQ_le_I : Q₀ ≤ iHull15 V₀ U H := by
    rw [← hP.w162_Q₀_inf_eq hQ hIJ hJ]
    exact le_inf le_rfl hQ_le_J
  exact OddCore15.not_le_iHull15 h hP hQ hQ_le_I

theorem w162_le_commutator (hI : NamedInputs15 G)
    (hW : W15Eight1 G) (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P)
    (hQ : OddCore15 V₀ U H Q₀) (hIJ : iHull15 V₀ U H ≤ J) :
    Q₀ ⊔ J ≤ ⁅Q₀ ⊔ J, V₀⁆ ⊔ J :=
  sup_le ((hQ.le_commutator_sup hI hW hS h hP).trans
    (sup_le_sup (Subgroup.commutator_mono le_sup_left le_rfl) hIJ)) le_sup_right

end Hyp1510

section Certified


namespace Hyp1510

variable {M V₀ V U S H P Q₀ : Subgroup G}

theorem w162_relIndex_shape (hI : NamedInputs15 G) (hW : W15Eight1 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) (hQ : OddCore15 V₀ U H Q₀) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ y ∈ Q₀, y ^ p ∈ iHull15 V₀ U H)
    (hcl : ∀ x ∈ Q₀, ∀ y ∈ Q₀, ∀ z ∈ Q₀, ⁅⁅x, y⁆, z⁆ ∈ iHull15 V₀ U H) :
    (iHull15 V₀ U H).relIndex Q₀ = p ∨
      ((iHull15 V₀ U H).relIndex Q₀ = p ^ 3 ∧ ∃ y ∈ Q₀, ∃ z ∈ Q₀, ⁅y, z⁆ ∉ iHull15 V₀ U H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J, hJdef⟩ : ∃ J : Subgroup G,
      J = iHull15 V₀ U H ⊔ iSub V₀ H (iHull15 V₀ U H) := ⟨_, rfl⟩
  have hhyp7 : Hyp7 V₀ := h.w162_hyp7
  have hIH : iHull15 V₀ U H ≤ H := (Hyp1510.iHull15_le_kHull15 V₀ U H).trans hP.kHull15_le
  have hEnorm : ((iHull15 V₀ U H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).2 (Hyp1510.le_normalizer_iHull15 V₀ U H)
  have hE : IsMulCommutative (iHull15 V₀ U H) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext
      (hP.comm_iHull15_sup a.1 (Subgroup.mem_sup_left a.2) b.1 (Subgroup.mem_sup_left b.2))
  have hpH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hiSub : iSub V₀ H (iHull15 V₀ U H) ≤ pCoreOf 2 H := iSup₂_le fun W _ => inf_le_right
  have hIJ : iHull15 V₀ U H ≤ J := hJdef ▸ le_sup_left
  have hIJ' : iSub V₀ H (iHull15 V₀ U H) ≤ J := hJdef ▸ le_sup_right
  have hJ : J ≤ pCoreOf 2 H := hJdef ▸ sup_le (hP.iHull15_le_pCoreOf h) hiSub
  have hJH : J ≤ H := hJ.trans hpH
  have hHJ : H ≤ normalizer (J : Set G) := by
    rw [hJdef]
    exact (le_inf (Hyp1510.le_normalizer_iHull15 V₀ U H)
      (le_normalizer_of_subgroupOf_normal (hiSub.trans hpH)
        (iSub_subgroupOf_normal hIH hEnorm))).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hJnorm : (J.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).2 hHJ
  have hQH : Q₀ ≤ H := hQ.le_H hP
  have hQnJ : Q₀ ≤ normalizer (J : Set G) := hQH.trans hHJ
  have hV1 : v1Sub15 V₀ U ≠ ⊥ := by
    intro hbot
    have h2 := hW.relIndex_eq_two hS h
    rw [hbot, Subgroup.relIndex_bot_left] at h2
    have h3 := hhyp7.2.1
    omega
  have hA : V₀ ∈ omegaSet V₀ H (iHull15 V₀ U H) := by
    refine mem_omegaSet.2 ⟨1, (CFSG.Quasithin.conjSubgroup_one V₀).symm, ?_,
      hP.fam.not_V₀_le_pCoreOf h⟩
    rw [inf_comm, hP.inf_iHull15_eq hW hS h]
    exact hV1
  have hYH : Q₀ ⊔ J ≤ H := sup_le hQH hJH
  have hAY : V₀ ≤ normalizer ((Q₀ ⊔ J : Subgroup G) : Set G) :=
    (le_inf (hP.V₀_le_H.trans hQ.normal) (hP.V₀_le_H.trans hHJ)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hres := sevenSixThree_holds G V₀ hhyp7 H (iHull15 V₀ U H) J V₀ (Q₀ ⊔ J) p hp hp2 hIH
    hEnorm hE hIJ' hJ hJnorm hA hP.V₀_le_H (hP.w162_relIndex_J hW hS h hIJ hJ) le_sup_right hYH
    hAY (hP.w162_le_commutator hI hW hS h hQ hIJ)
    (hP.w162_faithful hI hW hS h hQ hIJ hJ hHJ)
    (w162_pow_mem_sup hQnJ fun q hq => hIJ (hpow q hq))
    (w162_comm_comm_mem_sup hQnJ fun x hx y hy z hz => hIJ (hcl x hx y hy z hz))
  have hrel : J.relIndex (Q₀ ⊔ J) = (iHull15 V₀ U H).relIndex Q₀ := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.relIndex_sup_of_le_normalizer hQnJ,
      ← Subgroup.inf_relIndex_right J Q₀, inf_comm, hP.w162_Q₀_inf_eq hQ hIJ hJ]
  rw [hrel] at hres
  rcases hres with h1 | ⟨h2, y, hy, z, hz, hnot⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h2, ?_⟩
    by_contra hcon
    have hall : ∀ x ∈ Q₀, ∀ y ∈ Q₀, ⁅x, y⁆ ∈ iHull15 V₀ U H := fun x hx y hy =>
      by_contra fun hn => hcon ⟨x, hx, y, hy, hn⟩
    exact hnot (w162_comm_mem_sup hQnJ (fun x hx y hy => hIJ (hall x hx y hy)) y hy z hz)

end Hyp1510

end Certified

end CFSG.LocalAnalysis.WeakClosure81
