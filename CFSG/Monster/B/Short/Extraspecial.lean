module

public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG

open Subgroup
open scoped commutatorElement

theorem isExtraspecialPGroup_iff {p : ℕ} {P : Type*} [Group P] :
    IsExtraspecialPGroup p P ↔ IsPGroup p P ∧ commutator P = center P ∧
      (⨅ M ∈ {M : Subgroup P | IsCoatom M}, M) = center P ∧ Nat.card (center P) = p :=
  Iff.rfl

theorem frattini_le_of_isElementaryAbelian_quotient {p : ℕ} [Fact p.Prime] {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (N : Subgroup P) [N.Normal]
    (hN : IsElementaryAbelian p (P ⧸ N)) : frattini P ≤ N := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  rw [frattini_eq_closure_commutator_union_powers (p := p), Subgroup.closure_le]
  rintro x (hx | ⟨y, rfl⟩)
  · have : IsMulCommutative (P ⧸ N) := hN.toIsMulCommutative
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).1 this hx
  · have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hN.exponent_dvd_p (QuotientGroup.mk y)
    rw [← QuotientGroup.mk_pow] at h
    exact (QuotientGroup.eq_one_iff _).1 h

namespace IsExtraspecialPGroup

variable {p : ℕ} {P : Type*} [Group P]

theorem isPGroup (h : IsExtraspecialPGroup p P) : IsPGroup p P := h.1

theorem commutator_eq (h : IsExtraspecialPGroup p P) : commutator P = center P := h.2.1

theorem frattini_eq (h : IsExtraspecialPGroup p P) : frattini P = center P := h.2.2.1

theorem natCard_center (h : IsExtraspecialPGroup p P) : Nat.card (center P) = p := h.2.2.2

theorem isElementaryAbelian_quotient_center [Fact p.Prime] [Finite P]
    (h : IsExtraspecialPGroup p P) : IsElementaryAbelian p (P ⧸ center P) := by
  have : Fact (IsPGroup p P) := ⟨h.1⟩
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center P)).2 h.2.1.le
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← h.2.2.1]
      exact pth_power_mem_frattini_of_isPGroup (p := p) x

theorem nontrivial_quotient_center [Fact p.Prime] (h : IsExtraspecialPGroup p P) :
    Nontrivial (P ⧸ center P) := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton, QuotientGroup.subsingleton_iff] at hn
  have hcomm : commutator P = ⊥ := by
    rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.1 (hn ▸ Subgroup.mem_top y : y ∈ center P)) x)
  have h1 : Nat.card (center P) = 1 := by
    rw [← h.2.1, hcomm, Subgroup.card_bot]
  exact (Fact.out : p.Prime).one_lt.ne' (h.2.2.2.symm.trans h1)

theorem isExtraspecial [Fact p.Prime] [Finite P] (h : IsExtraspecialPGroup p P) :
    IsExtraspecial p P where
  center_order_p := h.2.2.2
  quotient_elementary_abelian := h.isElementaryAbelian_quotient_center
  quotient_nontrivial := h.nontrivial_quotient_center

end IsExtraspecialPGroup

theorem IsExtraspecial.isExtraspecialPGroup {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]
    [Finite P] [hE : IsExtraspecial p P] : IsExtraspecialPGroup p P := by
  have hpg : IsPGroup p P := IsExtraspecial.isPGroup p P
  have hZ : Nat.card (center P) = p := IsExtraspecial.center_order_p p P
  have hQ : IsElementaryAbelian p (P ⧸ center P) := IsExtraspecial.quotient_elementary_abelian p P
  have hcomm_le : commutator P ≤ center P :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center P)).1 hQ.toIsMulCommutative
  have hcomm : commutator P = center P := by
    have hdvd : Nat.card (commutator P) ∣ p := hZ ▸ Subgroup.card_dvd_of_le hcomm_le
    rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | hp'
    · exfalso
      have hbot : commutator P = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have htop : center P = ⊤ := by
        rw [eq_top_iff]
        intro y _
        rw [Subgroup.mem_center_iff]
        intro x
        have hxy : ⁅x, y⁆ ∈ commutator P := by
          rw [_root_.commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxy
        exact hxy
      have hn : Nontrivial (P ⧸ center P) := IsExtraspecial.quotient_nontrivial p P
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff] at hn
      exact hn htop
    · exact Subgroup.eq_of_le_of_card_ge hcomm_le (by rw [hZ, hp'])
  have hfr : frattini P = center P := by
    refine le_antisymm (frattini_le_of_isElementaryAbelian_quotient hpg (center P) hQ) ?_
    have : Fact (IsPGroup p P) := ⟨hpg⟩
    rw [← hcomm]
    exact commutator_le_frattini_of_isPGroup (p := p)
  exact ⟨hpg, hcomm, hfr, hZ⟩

theorem isExtraspecialPGroup_iff_isExtraspecial {p : ℕ} [Fact p.Prime] {P : Type*} [Group P]
    [Finite P] : IsExtraspecialPGroup p P ↔ IsExtraspecial p P :=
  ⟨fun h => h.isExtraspecial, fun h => IsExtraspecial.isExtraspecialPGroup (hE := h)⟩

end CFSG
