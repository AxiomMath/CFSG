module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl3Sound
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl3Check
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Elts
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Easy
public import CFSG.GroupTheory.ElemAbelianClosure
public import Certificates.Certificate799602
public import CFSG.Quasithin.H13.J4Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.StandardType CFSG.Assembly
open CFSG.RankThree.PartTwo.Sec4.Item434F42

section P0

@[expose] noncomputable def T0 : Subgroup F42C := Subgroup.closure (Set.range sE)

@[expose] noncomputable def P0 : Subgroup F42C :=
  Classical.choose Certificates.certificate799602

theorem card_P0 : Nat.card ↥P0 = 729 :=
  (Classical.choose_spec Certificates.certificate799602).1.trans (by norm_num)

theorem elemAb_comm {G : Type} [Group G] {p k : ℕ} {B : Subgroup G} (h : IsElemAb p k B) :
    ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  intro x hx y hy
  have := h.1.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem elemAb_pow {G : Type} [Group G] {p k : ℕ} {B : Subgroup G} (h : IsElemAb p k B) :
    ∀ x ∈ B, x ^ p = 1 := by
  haveI := h.1
  intro x hx
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx

theorem e81_P0 {B : Subgroup F42C} (hB : B ≤ P0)
    (hBe : IsElemAb 3 4 B) : B = T0 :=
  (Classical.choose_spec Certificates.certificate799602).2.2.2.1 B hB hBe

theorem P0_sylow : IsSylowOf 3 P0 (⊤ : Subgroup F42C) := by
  haveI : Finite F42C := finite_adjF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isSylowOf_of_card_p le_top ?_
  rw [card_P0, Subgroup.card_top, card_F42C, factorization_three_card]
  norm_num

theorem zE_central : ∀ x ∈ P0, x * zE = zE * x :=
  (Classical.choose_spec Certificates.certificate799602).2.2.2.2.1

theorem class_cover_P0 :
    ∀ x ∈ P0, x ≠ 1 → x ^ 3 = 1 → IsConj x rAE ∨ IsConj x rBE ∨ IsConj x zE :=
  (Classical.choose_spec Certificates.certificate799602).2.2.2.2.2.1

theorem t0_lines :
    ∃ LA LB : Finset (Subgroup F42C), LA.card ≤ 12 ∧ LB.card ≤ 12 ∧ ∀ d ∈ T0, d ≠ 1 →
      (IsConj d rAE ∧ Subgroup.zpowers d ∈ LA) ∨ (IsConj d rBE ∧ Subgroup.zpowers d ∈ LB) ∨
        IsConj d zE :=
  (Classical.choose_spec Certificates.certificate799602).2.2.2.2.2.2.1

theorem phi_link_C :
    IsConj (ReeTag.F4.finiteExceptionalAut (ZMod 2) rAE) rBE :=
  (Classical.choose_spec Certificates.certificate799602).2.2.2.2.2.2.2.1

theorem inv_comm_C :
    ∀ t ∈ [tE, uE, tuE, vE], ∀ ρ ∈ [rAE, rBE], ∃ c : F42C, c * ρ * c⁻¹ * t = t * (c * ρ * c⁻¹) :=
  (Classical.choose_spec Certificates.certificate799602).2.2.2.2.2.2.2.2

@[expose] noncomputable def tgE : ℕ → F42C := fun a =>
  if a = 0 then rAE else if a = 1 then rBE else zE

theorem order_three_cases {x : F42C} (hx : orderOf x = 3) :
    (∃ c, c * x * c⁻¹ = rAE) ∨ (∃ c, c * x * c⁻¹ = rBE) ∨ (∃ c, c * x * c⁻¹ = zE) := by
  haveI : Finite F42C := finite_adjF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_sylowOf_p P0_sylow le_top hxp
  have hkx : k * x * k⁻¹ ∈ P0 := hk x (Subgroup.mem_zpowers x)
  have hne : k * x * k⁻¹ ≠ 1 := by
    intro h
    have : x = 1 := conj_eq_one_iff.1 h
    rw [this, orderOf_one] at hx
    omega
  have hcube : (k * x * k⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3]
    simp
  have e : ∀ c : F42C, c * k * x * (c * k)⁻¹ = c * (k * x * k⁻¹) * c⁻¹ := fun c => by group
  rcases class_cover_P0 _ hkx hne hcube with h | h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact Or.inl ⟨c * k, by rw [e, hc]⟩
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact Or.inr (Or.inl ⟨c * k, by rw [e, hc]⟩)
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact Or.inr (Or.inr ⟨c * k, by rw [e, hc]⟩)

end P0

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
