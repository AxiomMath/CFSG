module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenIdx
public import CFSG.LocalAnalysis.WeakClosure81.W15TenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure OddCore15 (V₀ U H Q₀ : Subgroup G) : Prop where
  iHull_le : iHull15 V₀ U H ≤ Q₀
  le_kHull : Q₀ ≤ kHull15 V₀ H
  normal : H ≤ normalizer (Q₀ : Set G)
  odd : Odd ((iHull15 V₀ U H).relIndex Q₀)
  sup_eq : Q₀ ⊔ V₀ = kHull15 V₀ H

namespace Hyp1510

variable {M V₀ V U S H P : Subgroup G}

theorem kHull15_le_conjClosure (hI : NamedInputs15 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    kHull15 V₀ H ≤ conjClosure V₀ (kHull15 V₀ H) := by
  have hdec := hP.exists_mul_mem_inf hI hS h
  refine conjClosure_le fun g hg z hz => ?_
  obtain ⟨k, hk, m, hm, rfl⟩ := hdec g hg
  have hmN : m ∈ normalizer (V₀ : Set G) := by
    rw [h.hyp.normalizer₀]
    exact hm.2
  have hz' : m * z * m⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hmN z).1 hz
  have h1 := mem_conjClosure hk hz'
  simpa [mul_assoc] using h1

end Hyp1510

private theorem b15_le_normalizer_commutator {C Q V : Subgroup G}
    (h : ∀ c ∈ C, ∀ a ∈ Q, ∀ b ∈ V, c * ⁅a, b⁆ * c⁻¹ ∈ ⁅Q, V⁆) :
    C ≤ normalizer ((⁅Q, V⁆ : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ d ∈ C, ∀ x ∈ ⁅Q, V⁆, d * x * d⁻¹ ∈ ⁅Q, V⁆ := by
    intro d hd x hx
    rw [Subgroup.commutator_def] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hg
        exact h d hd a ha b hb
    | one => simp
    | mul x y _ _ ihx ihy =>
        have he : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
        rw [he]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ih =>
        have he : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
        rw [he]
        exact Subgroup.inv_mem _ ih
  intro x
  exact ⟨key c hc x, fun hx => by
    have h1 := key c⁻¹ (C.inv_mem hc) (c * x * c⁻¹) hx
    simpa [mul_assoc] using h1⟩

private theorem b15_le_normalizer_sup {C A B : Subgroup G}
    (hA : C ≤ normalizer (A : Set G))
    (hB : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ A ⊔ B) :
    C ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ d ∈ C, ∀ x ∈ A ⊔ B, d * x * d⁻¹ ∈ A ⊔ B := by
    intro d hd x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
        rcases hg with hgA | hgB
        · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hA hd) g).1 hgA)
        · exact hB d hd g hgB
    | one => simp
    | mul x y _ _ ihx ihy =>
        have he : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
        rw [he]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ih =>
        have he : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
        rw [he]
        exact Subgroup.inv_mem _ ih
  intro x
  exact ⟨key c hc x, fun hx => by
    have h1 := key c⁻¹ (C.inv_mem hc) (c * x * c⁻¹) hx
    simpa [mul_assoc] using h1⟩

namespace OddCore15

variable {M V₀ V U S H P Q₀ : Subgroup G}

theorem le_H (hP : Hyp1510 V₀ V U S H P) (hQ : OddCore15 V₀ U H Q₀) : Q₀ ≤ H :=
  hQ.le_kHull.trans hP.kHull15_le

theorem normal_subgroupOf (hP : Hyp1510 V₀ V U S H P) (hQ : OddCore15 V₀ U H Q₀) :
    ((iHull15 V₀ U H).subgroupOf Q₀).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hQ.iHull_le).2
    ((hQ.le_H hP).trans (Hyp1510.le_normalizer_iHull15 V₀ U H))

theorem inf_eq (hW : W15Eight1 G) (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hP : Hyp1510 V₀ V U S H P) (hQ : OddCore15 V₀ U H Q₀) : Q₀ ⊓ V₀ = v1Sub15 V₀ U := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxQ, hxV⟩ := Subgroup.mem_inf.1 hx
    have hxI : x ∈ iHull15 V₀ U H := by
      haveI : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := hQ.normal_subgroupOf hP
      have hpow : (⟨x, hxQ⟩ : ↥Q₀) ^ ((iHull15 V₀ U H).subgroupOf Q₀).relIndex ⊤
          ∈ (iHull15 V₀ U H).subgroupOf Q₀ :=
        Subgroup.pow_relIndex_mem _ (Subgroup.mem_top _)
      have hrel : ((iHull15 V₀ U H).subgroupOf Q₀).relIndex ⊤
          = (iHull15 V₀ U H).relIndex Q₀ := by
        rw [Subgroup.relIndex_top_right]
        rfl
      have hmem : x ^ (iHull15 V₀ U H).relIndex Q₀ ∈ iHull15 V₀ U H := by
        rw [hrel] at hpow
        simpa using (Subgroup.mem_subgroupOf.mp hpow)
      obtain ⟨k, hk⟩ := hQ.odd
      have hx2 : x ^ 2 = 1 := h.hyp.elemAbelian₀.2 x hxV
      have hxm : x ^ (iHull15 V₀ U H).relIndex Q₀ = x := by
        rw [hk, pow_succ, pow_mul, hx2, one_pow, one_mul]
      rwa [hxm] at hmem
    rw [← hP.inf_iHull15_eq hW hS h]
    exact Subgroup.mem_inf.2 ⟨hxV, hxI⟩
  · intro x hx
    exact Subgroup.mem_inf.2 ⟨hQ.iHull_le (Hyp1510.v1Sub15_le_iHull15 V₀ U H hx),
      v1Sub15_le_left V₀ U hx⟩

theorem not_le_iHull15 (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P)
    (hQ : OddCore15 V₀ U H Q₀) : ¬ Q₀ ≤ iHull15 V₀ U H := by
  intro hle
  have hQeq : Q₀ = iHull15 V₀ U H := le_antisymm hle hQ.iHull_le
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI2 : IsPGroup 2 (iHull15 V₀ U H) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le (hP.iHull15_le_pCoreOf h)
  have hV2 : IsPGroup 2 V₀ := h.hyp.isPGroup.to_le h.hyp.h6.le
  have hnorm : V₀ ≤ normalizer (iHull15 V₀ U H : Set G) :=
    hP.V₀_le_H.trans (Hyp1510.le_normalizer_iHull15 V₀ U H)
  have hsup2 : IsPGroup 2 ↥(V₀ ⊔ iHull15 V₀ U H) :=
    IsPGroup.to_sup_of_normal_right' hV2 hI2 hnorm
  have hK2 : IsPGroup 2 (kHull15 V₀ H) := by
    have heq : kHull15 V₀ H = V₀ ⊔ iHull15 V₀ U H := by
      rw [← hQ.sup_eq, hQeq, sup_comm]
    rw [heq]
    exact hsup2
  exact hP.fam.not_V₀_le_pCoreOf h ((Hyp1510.V₀_le_kHull15 V₀ H).trans
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP.kHull15_le
      (Hyp1510.le_normalizer_kHull15 V₀ H) hK2))

theorem le_commutator_sup (hI : NamedInputs15 G) (hW : W15Eight1 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P)
    (hQ : OddCore15 V₀ U H Q₀) : Q₀ ≤ ⁅Q₀, V₀⁆ ⊔ iHull15 V₀ U H := by
  let D : Subgroup G := ⁅Q₀, V₀⁆
  let I : Subgroup G := iHull15 V₀ U H
  let L : Subgroup G := D ⊔ I
  let N : Subgroup G := L ⊔ V₀
  change Q₀ ≤ L
  have hD_le : D ≤ Q₀ := by
    refine Subgroup.commutator_le.2 fun q hq v hv => ?_
    have hvq : v * q⁻¹ * v⁻¹ ∈ Q₀ :=
      (Subgroup.mem_normalizer_iff.1 (hQ.normal (hP.V₀_le_H hv)) q⁻¹).1 (Q₀.inv_mem hq)
    simpa only [commutatorElement_def, mul_assoc] using Q₀.mul_mem hq hvq
  have hL_le : L ≤ Q₀ := sup_le hD_le hQ.iHull_le
  have hQD : Q₀ ≤ normalizer (D : Set G) := by
    refine b15_le_normalizer_commutator (C := Q₀) (Q := Q₀) (V := V₀) fun c hc a ha b hb => ?_
    have h1 : ⁅c * a, b⁆ ∈ ⁅Q₀, V₀⁆ :=
      Subgroup.commutator_mem_commutator (Q₀.mul_mem hc ha) hb
    have h2 : ⁅c, b⁆ ∈ ⁅Q₀, V₀⁆ := Subgroup.commutator_mem_commutator hc hb
    have he : c * ⁅a, b⁆ * c⁻¹ = ⁅c * a, b⁆ * ⁅c, b⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    rw [he]
    exact (⁅Q₀, V₀⁆).mul_mem h1 ((⁅Q₀, V₀⁆).inv_mem h2)
  have hVD : V₀ ≤ normalizer (D : Set G) := by
    refine b15_le_normalizer_commutator (C := V₀) (Q := Q₀) (V := V₀) fun c hc a ha b hb => ?_
    have hca : c * a * c⁻¹ ∈ Q₀ :=
      (Subgroup.mem_normalizer_iff.1 (hQ.normal (hP.V₀_le_H hc)) a).1 ha
    have hcb : c * b * c⁻¹ ∈ V₀ := V₀.mul_mem (V₀.mul_mem hc hb) (V₀.inv_mem hc)
    have he : c * ⁅a, b⁆ * c⁻¹ = ⁅c * a * c⁻¹, c * b * c⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [he]
    exact Subgroup.commutator_mem_commutator hca hcb
  have hQ_norm_L : Q₀ ≤ normalizer (L : Set G) :=
    (le_inf hQD (hQ.le_H hP |>.trans (Hyp1510.le_normalizer_iHull15 V₀ U H))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup D I)
  have hV_norm_L : V₀ ≤ normalizer (L : Set G) :=
    (le_inf hVD (hP.V₀_le_H.trans (Hyp1510.le_normalizer_iHull15 V₀ U H))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup D I)
  have hV_norm_N : V₀ ≤ normalizer (N : Set G) :=
    (le_inf hV_norm_L Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_sup L V₀)
  have hQ_norm_N : Q₀ ≤ normalizer (N : Set G) := by
    refine b15_le_normalizer_sup (C := Q₀) (A := L) (B := V₀) hQ_norm_L fun c hc b hb => ?_
    have hcomm : ⁅c, b⁆ ∈ D := Subgroup.commutator_mem_commutator hc hb
    have he : c * b * c⁻¹ = ⁅c, b⁆ * b := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact (L ⊔ V₀).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hcomm))
      (Subgroup.mem_sup_right hb)
  have hK_norm_N : kHull15 V₀ H ≤ normalizer (N : Set G) := by
    rw [← hQ.sup_eq]
    exact sup_le hQ_norm_N hV_norm_N
  have hconj_le : conjClosure V₀ (kHull15 V₀ H) ≤ N :=
    conjClosure_le fun k hk z hz =>
      (Subgroup.mem_normalizer_iff.1 (hK_norm_N hk) z).1 (Subgroup.mem_sup_right hz)
  have hK_le_N : kHull15 V₀ H ≤ N := (hP.kHull15_le_conjClosure hI hS h).trans hconj_le
  have hQ_le_N : Q₀ ≤ N := hQ.le_kHull.trans hK_le_N
  intro x hx
  have hxN : x ∈ N := hQ_le_N hx
  change x ∈ (↑(L ⊔ V₀) : Set G) at hxN
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L V₀ hV_norm_L] at hxN
  obtain ⟨l, hl, v, hv, hxv⟩ := hxN
  have hvQ : v ∈ Q₀ := by
    have hv_eq : v = l⁻¹ * x := by
      rw [← hxv]
      group
    rw [hv_eq]
    exact Q₀.mul_mem (Q₀.inv_mem (hL_le hl)) hx
  have hvV1 : v ∈ v1Sub15 V₀ U := by
    rw [← inf_eq hW hS h hP hQ]
    exact Subgroup.mem_inf.2 ⟨hvQ, hv⟩
  have hvL : v ∈ L := Subgroup.mem_sup_right (Hyp1510.v1Sub15_le_iHull15 V₀ U H hvV1)
  rw [← hxv]
  exact L.mul_mem hl hvL

end OddCore15

end CFSG.LocalAnalysis.WeakClosure81
