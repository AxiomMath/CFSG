module

public import CFSG.Quasithin.Vol2.Ch6NatMod

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Quasithin CFSG.SectionRank.Ccomm
open scoped commutatorElement

section Extraspecial

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem extraspecial_commutator_mem_center {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] [CFSG.IsExtraspecial p P] (a b : P) : ⁅a, b⁆ ∈ Subgroup.center P := by
  have hQel : CFSG.IsElementaryAbelian p (P ⧸ Subgroup.center P) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian p P
  have hQcomm : ∀ a b : P ⧸ Subgroup.center P, a * b = b * a := fun a b => mul_comm' a b
  rw [← QuotientGroup.eq_one_iff]
  have := map_commutatorElement (QuotientGroup.mk' (Subgroup.center P)) a b
  change ((⁅a, b⁆ : P) : P ⧸ Subgroup.center P) = 1
  rw [show ((⁅a, b⁆ : P) : P ⧸ Subgroup.center P) =
    ⁅(a : P ⧸ Subgroup.center P), (b : P ⧸ Subgroup.center P)⁆ from this]
  exact commutatorElement_eq_one_iff_mul_comm.2 (hQcomm _ _)

theorem extraspecial_commutator_eq_center {P : Type*} [Group P] [Finite P] {p : ℕ}
    [hp : Fact p.Prime] [CFSG.IsExtraspecial p P] : commutator P = Subgroup.center P := by
  have hZcard : Nat.card (Subgroup.center P) = p := CFSG.IsExtraspecial.center_order_p p P
  have hQnt : Nontrivial (P ⧸ Subgroup.center P) := CFSG.IsExtraspecial.quotient_nontrivial p P
  have hcommle : commutator P ≤ Subgroup.center P := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    exact fun a _ b _ => extraspecial_commutator_mem_center (p := p) a b
  have hnc : ∃ a b : P, a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨q, hq⟩ := exists_ne (1 : P ⧸ Subgroup.center P)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact hq ((QuotientGroup.eq_one_iff x).2 (Subgroup.mem_center_iff.2 fun g => h g x))
  obtain ⟨a, b, hab⟩ := hnc
  have hne : commutator P ≠ ⊥ := by
    intro h
    have hmem : ⁅a, b⁆ ∈ commutator P := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  have hdvd : Nat.card (commutator P) ∣ p := hZcard ▸ Subgroup.card_dvd_of_le hcommle
  rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
  · exact absurd (Subgroup.card_eq_one.1 h1) hne
  · exact Subgroup.eq_of_le_of_card_ge hcommle (by rw [h1, hZcard])

theorem extraspecial_center_le_frattini {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] [CFSG.IsExtraspecial p P] : Subgroup.center P ≤ frattini P := by
  rw [← extraspecial_commutator_eq_center (p := p), _root_.commutator_def, Subgroup.commutator_le]
  exact fun a _ b _ => commutator_mem_frattini (CFSG.IsExtraspecial.isPGroup p P) a b

end Extraspecial

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_centralizer_of_acts_trivially {D : Subgroup G} [CFSG.IsExtraspecial 2 ↥D]
    {x : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hxZ : ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ D ⊓ Subgroup.centralizer (D : Set G)) :
    ∃ d ∈ D, d⁻¹ * x ∈ Subgroup.centralizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α : MulAut ↥D := conjAct D ⟨x, hx⟩
  have hα : ∀ y : ↥D, ((α y : ↥D) : G) = x * y * x⁻¹ := fun y => conjAct_apply_coe ⟨x, hx⟩ y
  have hker : α ∈ (autQuotient (frattini ↥D)).ker := by
    rw [mem_ker_autQuotient]
    intro y
    refine extraspecial_center_le_frattini (p := 2) ?_
    rw [Subgroup.mem_center_iff]
    intro w
    have he := hxZ y y.2
    have hyc := Subgroup.mem_centralizer_iff.mp he.2 y y.2
    apply Subtype.ext
    have key : ((y⁻¹ * α y : ↥D) : G) = x * y * x⁻¹ * (y : G)⁻¹ := by
      show (y : G)⁻¹ * ((α y : ↥D) : G) = _
      rw [hα]
      have e1 : x * (y : G) * x⁻¹ = (x * y * x⁻¹ * (y : G)⁻¹) * y := by group
      calc (y : G)⁻¹ * (x * y * x⁻¹) = (y : G)⁻¹ * ((x * y * x⁻¹ * (y : G)⁻¹) * y) := by
            rw [← e1]
        _ = (y : G)⁻¹ * ((y : G) * (x * y * x⁻¹ * (y : G)⁻¹)) := by rw [← hyc]
        _ = x * y * x⁻¹ * (y : G)⁻¹ := by group
    show (w : G) * ((y⁻¹ * α y : ↥D) : G) = ((y⁻¹ * α y : ↥D) : G) * w
    rw [key]
    exact (Subgroup.mem_centralizer_iff.mp he.2 w w.2)
  rw [← range_conj_eq_ker_autQuotient_frattini (p := 2)] at hker
  obtain ⟨d, hd⟩ := hker
  refine ⟨(d : G), d.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥D => ((φ ⟨y, hy⟩ : ↥D) : G)) hd
  simp only [MulAut.conj_apply, hα] at h1
  have h2 : (d : G) * y * (d : G)⁻¹ = x * y * x⁻¹ := h1
  calc y * ((d : G)⁻¹ * x) = (d : G)⁻¹ * ((d : G) * y * (d : G)⁻¹) * x := by group
    _ = (d : G)⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
    _ = (d : G)⁻¹ * x * y := by group

end CFSG.Quasithin.H13.GM22
