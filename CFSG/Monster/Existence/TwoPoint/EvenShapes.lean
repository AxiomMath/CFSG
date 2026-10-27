module

public import CFSG.Monster.Existence.TwoPoint.Fi22
public import CFSG.Monster.Existence.TwoPoint.ShapeOneGriess
public import CFSG.Monster.Existence.TwoPointConj
public import CFSG.Monster.Existence.TwoPoint.LeechPlug
public import CFSG.Monster.Existence.TwoPoint.CoPairMcL
public import CFSG.Monster.Existence.TwoPoint.Classes

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section General

variable {G : Type} [Group G]

theorem isConj_conj_conj {u v : G} (g : G) (h : IsConj u v) : IsConj u (g * v * g⁻¹) :=
  h.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem tableVIISet_conj {a z₀ x y : G} (g : G) {K : TableVIIClass}
    (h : y ∈ tableVIISet a z₀ x K) : g * y * g⁻¹ ∈ tableVIISet a z₀ (g * x * g⁻¹) K := by
  have e : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  have ho : orderOf (g * (x * y) * g⁻¹) = orderOf (x * y) :=
    (orderOf_eq_of_isConj (isConj_iff.2 ⟨g, rfl⟩)).symm
  have hp : ∀ n : ℕ, (g * (x * y) * g⁻¹) ^ n = g * (x * y) ^ n * g⁻¹ := fun n => by
    rw [conj_pow]
  cases K with
  | two_A =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨isConj_conj_conj g h1, by rw [e]; exact isConj_conj_conj g h2⟩
  | two_B =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨isConj_conj_conj g h1, by rw [e]; exact isConj_conj_conj g h2⟩
  | four_A =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨isConj_conj_conj g h1, by rw [e, ho]; exact h2,
      by rw [e, hp]; exact isConj_conj_conj g h3⟩
  | four_B =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨isConj_conj_conj g h1, by rw [e, ho]; exact h2,
      by rw [e, hp]; exact isConj_conj_conj g h3⟩
  | six_A =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨isConj_conj_conj g h1, by rw [e, ho]; exact h2,
      by rw [e, hp]; exact isConj_conj_conj g h3⟩

theorem exists_base_rep {a z₀ α β : G} (hα : IsConj a α) {K : TableVIIClass}
    (hβ : β ∈ tableVIISet a z₀ α K) {i : Fin 9} (hs : TwoPointShape (cent2 α β) i) :
    ∃ y, y ∈ tableVIISet a z₀ a K ∧ TwoPointShape (cent2 a y) i := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hα
  refine ⟨g⁻¹ * β * g, ?_, ?_⟩
  · have := tableVIISet_conj g⁻¹ hβ
    rwa [inv_inv, show g⁻¹ * (g * a * g⁻¹) * g = a by group] at this
  · have := TwoPointShape.conj g⁻¹ hs
    rwa [inv_inv, show g⁻¹ * (g * a * g⁻¹) * g = a by group] at this

theorem twoPointShape_zero_of_isTwoACentralizer {a : G} (ha : orderOf a = 2)
    (h : IsTwoACentralizer a) : TwoPointShape (cent2 a a) 0 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have e' : ↥(cent a) ≃* ↥(cent2 a a) := MulEquiv.subgroupCongr (inf_idem _).symm
  refine HasTwoShape.of_mulEquiv (k := 1)
    (P := fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.B)) e'
    (fun _ _ _ _ f hX => hX.map fun g => f.symm.trans g) ?_
  refine ⟨Subgroup.center ↥(cent a), inferInstance, ?_, ⟨e⟩⟩
  have hc : Nat.card ↥((Subgroup.center ↥(cent a)).map (cent a).subtype) =
      Nat.card ↥(Subgroup.center ↥(cent a)) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [← hc, hZ, Nat.card_zpowers, ha, pow_one]

end General

section MGriess

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Code
  CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Visible CFSG.Monster.Generated

theorem isConj_tGriess_of_trace
    {g : MGriess} (hg : orderOf g = 2)
    (htr : LinearMap.trace ℚ SpaceB ((g : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 4372) :
    IsConj tGriess g := by
  rcases (involution_classes_MGriess_of_Gmat Census.generated_group_two_involution_classes).1 g hg
    with h | h
  · have := trace_eq_of_isConj_MGriess h
    rw [trace_xGriess, htr] at this
    norm_num at this
  · exact h

theorem orderOf_eq_two_of_mul_self {G : Type} [Group G] {g : G} (h1 : g ≠ 1) (h2 : g * g = 1) :
    orderOf g = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq, h2]) h1

theorem uGriess_mem_twoANbr :
    uGriess ∈ twoANbr tGriess tGriess := by
  have hu1 : uGriess ≠ 1 := uGriess_ne_one
  have htu1 : tGriess * uGriess ≠ 1 := fun h => uGriess_ne_tGriess
    (eq_of_mul_eq_one_of_mul_self tGriess_mul_self h)
  have htu2 : tGriess * uGriess * (tGriess * uGriess) = 1 := by
    calc tGriess * uGriess * (tGriess * uGriess) = tGriess * (uGriess * tGriess) * uGriess := by
          group
      _ = tGriess * (tGriess * uGriess) * uGriess := by rw [tGriess_mul_uGriess]
      _ = 1 := by rw [← mul_assoc, tGriess_mul_self, one_mul, uGriess_mul_self]
  refine ⟨isConj_tGriess_of_trace (orderOf_eq_two_of_mul_self hu1 uGriess_mul_self)
    (trace_of_mem_FE (right_mem_kleinSubgroup) hu1), ?_⟩
  refine isConj_tGriess_of_trace (orderOf_eq_two_of_mul_self htu1 htu2)
    (trace_of_mem_FE ?_ htu1)
  rw [mem_FE]
  exact Or.inr (Or.inr (Or.inr rfl))

theorem tGriess_mul_xGriess_mem_twoBNbr :
    tGriess * xGriess ∈ twoBNbr tGriess xGriess tGriess := by
  have htx : tGriess * xGriess = xGriess * tGriess := by
    rw [← rhoGriess_rStar, ← rhoGriess_zQ, ← rhoGriess_mul, ← rhoGriess_mul,
      Subgroup.mem_center_iff.1 Short.zQ_mem_center rStar]
  have h1 : tGriess * xGriess ≠ 1 := fun h => by
    have h' := eq_of_mul_eq_one_of_mul_self tGriess_mul_self h
    exact not_isConj_xGriess_tGriess (h' ▸ IsConj.refl _)
  have h2 : tGriess * xGriess * (tGriess * xGriess) = 1 := by
    calc tGriess * xGriess * (tGriess * xGriess) = tGriess * (xGriess * tGriess) * xGriess := by
          group
      _ = tGriess * (tGriess * xGriess) * xGriess := by rw [htx]
      _ = 1 := by
        rw [← mul_assoc, tGriess_mul_self, one_mul, mul_self_of_isConj orderOf_xGriess
          (IsConj.refl _)]
  refine ⟨isConj_tGriess_of_trace (orderOf_eq_two_of_mul_self h1 h2) ?_, ?_⟩
  · rw [htx]
    exact trace_x_mul_of_mem_FE left_mem_kleinSubgroup tGriess_ne_one
  · rw [← mul_assoc, tGriess_mul_self, one_mul]
    exact IsConj.refl _

theorem exists_six_A_rep
    (I : GMSInterfaces (phiB uBar) MGriess) :
    ∃ y, y ∈ tableVIISet tGriess xGriess tGriess .six_A ∧
      TwoPointShape (cent2 tGriess y) 8 := by
  obtain ⟨α, δ, hα, hδ, L, hL, hLc, hLs⟩ := exists_fi22_two_point
  have hc := table7_card I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap I.leechPair
    gmsF1Type_MGriess_uncond hα (K := .six_A) hδ
  have hLeq : L = cent2 α δ := Subgroup.eq_of_le_of_card_ge hL (by rw [hLc]; exact hc.le)
  subst hLeq
  exact exists_base_rep hα hδ hLs


theorem exists_four_A_rep :
    ∃ y, y ∈ tableVIISet tGriess xGriess tGriess .four_A ∧ TwoPointShape (cent2 tGriess y) 5 := by
  obtain ⟨α, β, hα, hβ, ho, hsq, N, hN, hext, hcard, ⟨e⟩⟩ := leech_fourA_shape_coW1
  obtain ⟨f⟩ := coPair_mcl
  have hs : TwoPointShape (cent2 α β) 5 := ⟨N, hN, hext, hcard, ⟨e.trans f⟩⟩
  have hβ' : β ∈ tableVIISet tGriess xGriess α .four_A := ⟨hβ, ho, by rw [hsq]; exact IsConj.refl _⟩
  exact exists_base_rep hα hβ' hs

end MGriess

end CFSG.Monster.Existence
