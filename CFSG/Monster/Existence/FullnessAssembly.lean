module

public import CFSG.Monster.Existence.Fullness
public import CFSG.Monster.Existence.InvolutionClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

theorem cfullA_le_Cgen_of_card (h : Nat.card DA = Nat.card Cbar) : CfullA ≤ Cgen := by
  have hS : ShatA = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [ShatA, MonoidHom.range_eq_map, Subgroup.card_map_of_injective iotaA_injective,
      Subgroup.card_top, h]
  intro g hg
  obtain ⟨c, hc⟩ : piA ⟨g, hg⟩ ∈ ShatA := hS ▸ Subgroup.mem_top _
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective Zstar c
  have hc' : piA (inclGenA c₀) = piA ⟨g, hg⟩ := hc
  rw [piA, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hc'
  have hz : (inclGenA c₀)⁻¹ * ⟨g, hg⟩ ∈ ZstarA := hc'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hg' : g = (c₀ : SpaceB ≃ₗ[ℚ] SpaceB) * tStar ^ k := by
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] at this
    have e : ((inclGenA c₀ : CfullA) : SpaceB ≃ₗ[ℚ] SpaceB) = c₀ := rfl
    rw [e] at this
    rw [show ((tStarA : CfullA) : SpaceB ≃ₗ[ℚ] SpaceB) = tStar from rfl] at this
    rw [this]
    group
  rw [hg']
  exact Cgen.mul_mem c₀.2 (Cgen.zpow_mem tStar_mem_Cgen k)

theorem cent_tGriess_le_GmatGriess_of_card (h : Nat.card DA = Nat.card Cbar) :
    Subgroup.centralizer {tGriess} ≤ GmatGriess := by
  intro g hg
  have hmem : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ CfullA := by
    rw [← map_cent_tGriess]
    exact ⟨g, hg, rfl⟩
  exact Cgen_le_Gmat (cfullA_le_Cgen_of_card h hmem)

theorem GmatGriess_eq_top_of
    (hcensus : ∀ g : Gmat, orderOf g = 2 → IsConj xGmat g ∨ IsConj tGmat g)
    (hCt : Subgroup.centralizer {tGriess} ≤ GmatGriess) : GmatGriess = ⊤ := by
  let ι : Gmat →* MGriess := Subgroup.inclusion Gmat_le_AutO
  have hι : ∀ g : Gmat, ((ι g : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) = g := fun _ => rfl
  have hxG : xGriess ∈ GmatGriess := (Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat))
  have htG : tGriess ∈ GmatGriess := (Cgen_le tStar_mem_Cgen).1
  have hCx : Subgroup.centralizer {xGriess} ≤ GmatGriess := by
    intro g hg
    have hmem : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
      rw [← map_cent_xGriess]
      exact ⟨g, hg, rfl⟩
    exact Hmat_le_Gmat hmem
  refine eq_top_of_two_classes GmatGriess hxG htG orderOf_xGriess orderOf_tGriess
    not_isConj_xGriess_tGriess ?_ ?_ hCx hCt
  · intro y hy hy2
    set g : Gmat := ⟨y, hy⟩ with hgdef
    have hg2 : orderOf g = 2 := by
      rw [← orderOf_injective ι (Subgroup.inclusion_injective Gmat_le_AutO) g]
      exact hy2
    have hιg : ι g = y := rfl
    rcases hcensus g hg2 with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      left
      refine ⟨ι c, c.2, ?_⟩
      rw [← hιg, ← hc, map_mul, map_mul, map_inv]
      rfl
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      right
      refine ⟨ι c, c.2, ?_⟩
      rw [← hιg, ← hc, map_mul, map_mul, map_inv]
      rfl
  · intro y hy
    obtain ⟨-, -, h3, -⟩ := (isTwoBCentralizer_MGriess xGriess (IsConj.refl _)).sylow
      orderOf_xGriess
    obtain ⟨c, hc⟩ := h3 y ⟨1, by rw [pow_one, ← hy, pow_orderOf_eq_one]⟩
    refine ⟨c, hCx hc⟩

theorem monster_existence_clauses_one_two_of
    (hcensus : ∀ g : Gmat, orderOf g = 2 → IsConj xGmat g ∨ IsConj tGmat g)
    (e : DA ≃* Blueprint.NativeSporadic.B)
    (hCbar : Nat.card Cbar = Nat.card Blueprint.NativeSporadic.B)
    (hGmat : Nat.card Gmat = CFSG.Open.monsterOrder) :
    (Finite MGriess ∧ IsSimpleGroup MGriess ∧ (∃ x y : MGriess, x * y ≠ y * x) ∧
      Nat.card MGriess = CFSG.Open.monsterOrder) ∧
    orderOf tGriess = 2 ∧ orderOf xGriess = 2 ∧ ¬ IsConj tGriess xGriess ∧
    (∀ t : MGriess, orderOf t = 2 → IsConj tGriess t ∨ IsConj xGriess t) ∧
    (∀ α, IsConj tGriess α → IsTwoACentralizer α) ∧
    (∀ ζ, IsConj xGriess ζ → IsTwoBCentralizer ζ) := by
  have hcard : Nat.card DA = Nat.card Cbar := by
    rw [Nat.card_congr e.toEquiv, hCbar]
  have htop := GmatGriess_eq_top_of hcensus (cent_tGriess_le_GmatGriess_of_card hcard)
  obtain ⟨hfin, hsimp, hnc⟩ := MGriess_finite_nonabelian_simple
  have hord : Nat.card MGriess = CFSG.Open.monsterOrder := by
    rw [← hGmat]
    have h1 : Nat.card GmatGriess = Nat.card MGriess := by
      rw [htop, Subgroup.card_top]
    rw [← h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Gmat_le_AutO).toEquiv)
  obtain ⟨hcl, hnc'⟩ := involution_classes_MGriess_of_Gmat hcensus
  refine ⟨⟨hfin, hsimp, hnc, hord⟩, orderOf_tGriess, orderOf_xGriess, fun h => hnc' h.symm,
    fun t ht => (hcl t ht).symm, fun α hα => ?_, fun ζ hζ => isTwoBCentralizer_MGriess ζ hζ⟩
  exact (isTwoACentralizer_tGriess_of_equiv e).of_isConj hα

end CFSG.Monster.Existence
