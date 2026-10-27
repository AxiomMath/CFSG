module

public import CFSG.OddTranspositions.PartThree.EightEight.StarBlocks
public import CFSG.OddTranspositions.SixNineUnconditional

import CFSG.OddTranspositions.BlockCover
import CFSG.OddTranspositions.PartFour.Line
import CFSG.OddTranspositions.PartThree.EightEight.DeltaOrbit
import CFSG.OddTranspositions.PartThree.EightEight.Eighteen
import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.OddTranspositions.PartThree.EightEight.ThirdCentralizer
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.PartThree.HalphaConj

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def perpBlocks (D α Δ₁ : Set G) : Set (Set G) :=
  {σ | σ ∈ blockClass α ∧ Disjoint σ Δ₁ ∧
    ∀ ρ ∈ blockClass α, (ρ ∩ Δ₁).Nonempty → σ ∈ Dalpha D ρ}

omit [Finite G] in
theorem pow_mem_closure_conjOrbit (hS : Setup G D) {x w y : G} (ht : IsTriangle D x w y)
    {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    (x * y * w) ^ n ∈ Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x) ∧
      ∀ k ∈ Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x),
        Commute k ((x * y * w) ^ n) := by
  classical
  let z : G := (x * y * w) ^ n
  let K₁ : Subgroup G := Subgroup.closure (conjOrbit (localGroup D z) x)
  have hzy : y ∈ conjOrbit (localGroup D z) x :=
    (mem_conjOrbit_of_third_kind hS ht hn hord).1
  have hzx : x ∈ conjOrbit (localGroup D z) x := self_mem_conjOrbit _ x
  have hze : x * y * z ∈ conjOrbit (localGroup D z) x :=
    mul_mul_pow_mem_conjOrbit hS ht hn hord
  have hmem : z ∈ K₁ := by
    have h := K₁.mul_mem (K₁.mul_mem (Subgroup.subset_closure hzx)
      (Subgroup.subset_closure hzy)) (Subgroup.subset_closure hze)
    rwa [show x * y * (x * y * z) = z from
      mul_mul_mul_mul_cancel_of_isTriangle hS.oddT ht z] at h
  have hxcent : x ∈ centSet D z :=
    ⟨ht.1, (IsTriangle.third_kind hS.oddT hS.normal ht hn hord).2.2.1.symm⟩
  refine ⟨hmem, ?_⟩
  intro k hk
  refine commute_of_mem_closure (S := conjOrbit (localGroup D z) x) (T := {z}) ?_ hk ?_
  · intro a ha b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact (conjOrbit_subset_centSet hS.normal hxcent ha).2
  · exact Subgroup.subset_closure (Set.mem_singleton z)

omit [Finite G] in
theorem conjOrbit_closure_conjOrbit_eq (hS : Setup G D) {x w y : G} (ht : IsTriangle D x w y)
    {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    conjOrbit (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)) x =
      conjOrbit (localGroup D ((x * y * w) ^ n)) x := by
  classical
  let z : G := (x * y * w) ^ n
  let K : Subgroup G := localGroup D z
  let Δ₁ : Set G := conjOrbit K x
  let K₁ : Subgroup G := Subgroup.closure Δ₁
  have hxcent : x ∈ centSet D z :=
    ⟨ht.1, (IsTriangle.third_kind hS.oddT hS.normal ht hn hord).2.2.1.symm⟩
  have hK₁le : K₁ ≤ K := by
    rw [Subgroup.closure_le]
    intro a ha
    exact mem_localGroup_of_mem (conjOrbit_subset_centSet hS.normal hxcent ha)
  have hnorm : ∀ p ∈ K, ∀ k ∈ K₁, p * k * p⁻¹ ∈ K₁ := by
    intro p hp k hk
    exact conj_mem_closure (S := Δ₁) (fun a ha => conj_mem_conjOrbit hp ha) hk
  have hmain : ∀ k ∈ K, ∃ k₁ ∈ K₁, ∀ a ∈ Δ₁, k * a * k⁻¹ = k₁ * a * k₁⁻¹ := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem a ha =>
        by_cases ha₁ : a ∈ Δ₁
        · exact ⟨a, Subgroup.subset_closure ha₁, fun b _ => rfl⟩
        · have hcomm : ∀ b ∈ Δ₁, Commute a b := fun b hb =>
            (commute_of_mem_conjOrbit_of_notMem hS.oddT hS.normal hxcent hb ha ha₁).symm
          refine ⟨1, K₁.one_mem, fun b hb => ?_⟩
          rw [one_mul, inv_one, mul_one, (hcomm b hb).eq]
          group
    | one => exact ⟨1, K₁.one_mem, fun b _ => by simp⟩
    | mul p q hp hq ihp ihq =>
        obtain ⟨kp, hkp, hkp'⟩ := ihp
        obtain ⟨kq, hkq, hkq'⟩ := ihq
        refine ⟨kp * kq, K₁.mul_mem hkp hkq, fun b hb => ?_⟩
        have hqb : q * b * q⁻¹ ∈ Δ₁ := conj_mem_conjOrbit hq hb
        calc (p * q) * b * (p * q)⁻¹ = p * (q * b * q⁻¹) * p⁻¹ := by group
          _ = kp * (q * b * q⁻¹) * kp⁻¹ := hkp' _ hqb
          _ = kp * (kq * b * kq⁻¹) * kp⁻¹ := by rw [hkq' b hb]
          _ = (kp * kq) * b * (kp * kq)⁻¹ := by group
    | inv p hp ihp =>
        obtain ⟨kp, hkp, hkp'⟩ := ihp
        refine ⟨kp⁻¹, K₁.inv_mem hkp, fun b hb => ?_⟩
        have hb' : p⁻¹ * b * p ∈ Δ₁ := by
          simpa using conj_mem_conjOrbit (K.inv_mem hp) hb
        have h1 : p * (p⁻¹ * b * p) * p⁻¹ = kp * (p⁻¹ * b * p) * kp⁻¹ := hkp' _ hb'
        have hb_eq : b = kp * (p⁻¹ * b * p) * kp⁻¹ := by
          rw [← h1]
          group
        have h2 : kp⁻¹ * b * kp = p⁻¹ * b * p⁻¹⁻¹ := by
          conv_lhs => rw [hb_eq]
          group
        calc p⁻¹ * b * p⁻¹⁻¹ = kp⁻¹ * b * kp := h2.symm
          _ = kp⁻¹ * b * (kp⁻¹)⁻¹ := by rw [inv_inv]
  ext v
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hK₁le hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨k₁, hk₁, hk₁'⟩ := hmain k hk
    exact ⟨k₁, hk₁, hk₁' x (self_mem_conjOrbit K x)⟩

omit [Finite G] in
theorem setOf_centSet_notMem_eq (hS : Setup G D) {x w y : G} (ht : IsTriangle D x w y) {n : ℕ}
    (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    {d | d ∈ centSet D ((x * y * w) ^ n) ∧ d ∉ conjOrbit (localGroup D ((x * y * w) ^ n)) x} =
      {d | d ∈ D ∧ ∀ a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x, Commute d a} := by
  classical
  let z : G := (x * y * w) ^ n
  let Δ₁ : Set G := conjOrbit (localGroup D z) x
  have hxcent : x ∈ centSet D z :=
    ⟨ht.1, (IsTriangle.third_kind hS.oddT hS.normal ht hn hord).2.2.1.symm⟩
  have hy₁ : y ∈ Δ₁ := (mem_conjOrbit_of_third_kind hS ht hn hord).1
  have hw₁ : w ∈ Δ₁ := (mem_conjOrbit_of_third_kind hS ht hn hord).2
  ext d
  constructor
  · rintro ⟨hdcent, hdO⟩
    exact ⟨hdcent.1, fun a ha =>
      (commute_of_mem_conjOrbit_of_notMem hS.oddT hS.normal hxcent ha hdcent hdO).symm⟩
  · rintro ⟨hdD, hdc⟩
    have hdx : Commute d x := hdc x (self_mem_conjOrbit _ x)
    have hdy : Commute d y := hdc y hy₁
    have hdw : Commute d w := hdc w hw₁
    refine ⟨⟨hdD, ?_⟩, ?_⟩
    · show Commute d z
      exact ((hdx.mul_right hdy).mul_right hdw).pow_right n
    · intro hdO
      obtain ⟨k, hk, hkd⟩ := hdO
      have hkw : k * w * k⁻¹ ∈ Δ₁ := conj_mem_conjOrbit hk hw₁
      have hcomm : Commute d (k * w * k⁻¹) := hdc _ hkw
      rw [hkd] at hcomm
      have hxw : Commute x w := by
        have h := hcomm.conj k⁻¹
        simp only [inv_inv] at h
        have e1 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
        have e2 : k⁻¹ * (k * w * k⁻¹) * k = w := by group
        rwa [e1, e2] at h
      exact ht.2.2.2.2.2.1 hxw

theorem commute_of_mem_perpBlocks (hC : HypothesisC D) {Δ₁ : Set G} (hΔ : Δ₁ ⊆ D)
    {σ : Set G} (hσ : σ ∈ perpBlocks D hC.alpha Δ₁) {s a : G} (hs : s ∈ σ) (ha : a ∈ Δ₁) :
    Commute s a := by
  obtain ⟨-, -, hσperp⟩ := hσ
  obtain ⟨ρ, hρclass, haρ⟩ :=
    exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha (hΔ ha)
  have hσDρ : σ ∈ Dalpha D ρ := hσperp ρ hρclass ⟨a, haρ, ha⟩
  exact ((mem_Dalpha_iff.mp hσDρ).2.2.2 a haρ s hs).symm

theorem commute_pow_of_mem_perpBlocks (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n)
    {σ : Set G} (hσ : σ ∈ perpBlocks D hC.alpha (conjOrbit (localGroup D ((x * y * w) ^ n)) x))
    {s : G} (hs : s ∈ σ) : Commute s ((x * y * w) ^ n) := by
  classical
  let z : G := (x * y * w) ^ n
  have hxcent : x ∈ centSet D z :=
    ⟨ht.1, (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1.symm⟩
  have hΔ : conjOrbit (localGroup D z) x ⊆ D :=
    fun a ha => (conjOrbit_subset_centSet hC.setup.normal hxcent ha).1
  have hx : x ∈ conjOrbit (localGroup D z) x := self_mem_conjOrbit _ x
  have hy : y ∈ conjOrbit (localGroup D z) x :=
    (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1
  have hw : w ∈ conjOrbit (localGroup D z) x :=
    (mem_conjOrbit_of_third_kind hC.setup ht hn hord).2
  have h := (commute_of_mem_perpBlocks hC hΔ hσ hs hx).mul_right
    (commute_of_mem_perpBlocks hC hΔ hσ hs hy)
  have h2 := h.mul_right (commute_of_mem_perpBlocks hC hΔ hσ hs hw)
  show Commute s z
  exact h2.pow_right n

theorem setOf_centSet_notMem_eq_sUnion (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    {d | d ∈ centSet D ((x * y * w) ^ n) ∧ d ∉ conjOrbit (localGroup D ((x * y * w) ^ n)) x} =
      ⋃₀ perpBlocks D hC.alpha (conjOrbit (localGroup D ((x * y * w) ^ n)) x) := by
  classical
  let z : G := (x * y * w) ^ n
  let Δ₁ : Set G := conjOrbit (localGroup D z) x
  have hxcent : x ∈ centSet D z :=
    ⟨ht.1, (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1.symm⟩
  have hΔ : Δ₁ ⊆ D := fun a ha => (conjOrbit_subset_centSet hC.setup.normal hxcent ha).1
  ext d
  constructor
  · rintro ⟨hdcent, hdO⟩
    obtain ⟨σ, hσclass, hdσ⟩ :=
      exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hdcent.1
    have hcommΔ : ∀ a ∈ Δ₁, Commute a d := fun a ha =>
      commute_of_mem_conjOrbit_of_notMem hC.setup.oddT hC.setup.normal hxcent ha hdcent hdO
    have hσΔ : Disjoint σ Δ₁ := by
      rw [Set.disjoint_left]
      intro a haσ haΔ
      have had : a ≠ d := fun h => hdO (h ▸ haΔ)
      exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hσclass haσ hdσ had)
        (hcommΔ a haΔ)
    refine Set.mem_sUnion.mpr ⟨σ, ?_, hdσ⟩
    refine ⟨hσclass, hσΔ, fun ρ hρ hmeet => ?_⟩
    obtain ⟨a, haρ, haΔ⟩ := hmeet
    have hρσ : ρ ≠ σ := by
      intro h
      have had : a ≠ d := fun h' => hdO (h' ▸ haΔ)
      exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hσclass (h ▸ haρ) hdσ had)
        (hcommΔ a haΔ)
    exact mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha
      hρ hσclass hρσ haρ hdσ (hcommΔ a haΔ)
  · intro hd
    rcases Set.mem_sUnion.mp hd with ⟨σ, hσP, hdσ⟩
    have hσclass : σ ∈ blockClass hC.alpha := hσP.1
    have hσdisj : Disjoint σ Δ₁ := hσP.2.1
    have hdD : d ∈ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hσclass hdσ
    exact ⟨⟨hdD, commute_pow_of_mem_perpBlocks hC ht hn hord hσP hdσ⟩,
      Set.disjoint_left.mp hσdisj hdσ⟩

theorem isStarTriangle_conj_of_mem_perpBlocks (hC : HypothesisC D) {x w y : G}
    (hst : IsStarTriangle hC x w y) {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n)
    {σ : Set G} (hσ : σ ∈ perpBlocks D hC.alpha (conjOrbit (localGroup D ((x * y * w) ^ n)) x))
    {g : G} (hg : σ = (fun r => g * r * g⁻¹) '' hC.alpha) :
    IsStarTriangle (hC.conj g) x w y := by
  classical
  obtain ⟨ht, hthird, -, -, -, hstar⟩ := hst
  obtain ⟨hσclass, -, hσperp⟩ := hσ
  let z : G := (x * y * w) ^ n
  let Δ₁ : Set G := conjOrbit (localGroup D z) x
  have hconjα : (hC.conj g).alpha = σ := by
    rw [HypothesisC.conj_alpha]
    exact hg.symm
  have hblockclass : blockClass (hC.conj g).alpha = blockClass hC.alpha := by
    rw [hconjα]
    exact blockClass_eq_of_mem_blockClass hσclass
  have hxcent : x ∈ centSet D z :=
    ⟨ht.1, (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1.symm⟩
  have hΔ : Δ₁ ⊆ D := fun a ha => (conjOrbit_subset_centSet hC.setup.normal hxcent ha).1
  have hmem : ∀ v ∈ Δ₁, v ∈ DalphaStar D σ := by
    intro v hv
    obtain ⟨ρ, hρclass, hvρ⟩ :=
      exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha (hΔ hv)
    exact ⟨ρ, CFSG.OddTranspositions.PartFour.mem_Dalpha_symm
      (hσperp ρ hρclass ⟨v, hvρ, hv⟩)
      (subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hρclass), hvρ⟩
  have hx₁ : x ∈ Δ₁ := self_mem_conjOrbit _ x
  have hy₁ : y ∈ Δ₁ := (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1
  have hw₁ : w ∈ Δ₁ := (mem_conjOrbit_of_third_kind hC.setup ht hn hord).2
  refine ⟨ht, hthird, ?_, ?_, ?_, ?_⟩
  · rw [hconjα]
    exact hmem x hx₁
  · rw [hconjα]
    exact hmem w hw₁
  · rw [hconjα]
    exact hmem y hy₁
  · intro γ hγ hwγ
    rw [hblockclass] at hγ
    exact hstar γ hγ hwγ

end CFSG.OddTranspositions.PartThree.EightEight
