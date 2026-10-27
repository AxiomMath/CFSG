module

public import CFSG.Monster.Existence.TwoA
public import CFSG.Monster.Existence.Simple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

@[expose] noncomputable def tGmat : Gmat := ⟨tStar, (Cgen_le tStar_mem_Cgen).1⟩

theorem trace_tStar :
    LinearMap.trace ℚ SpaceB (tStar : SpaceB →ₗ[ℚ] SpaceB) = 4372 :=
  trace_rho_short isShortCoord_rStar

theorem trace_xmat' :
    LinearMap.trace ℚ SpaceB (xmat : SpaceB →ₗ[ℚ] SpaceB) = 276 := trace_xmat

theorem trace_eq_of_isConj {a b : SpaceB ≃ₗ[ℚ] SpaceB} (h : IsConj a b) :
    LinearMap.trace ℚ SpaceB (a : SpaceB →ₗ[ℚ] SpaceB) =
      LinearMap.trace ℚ SpaceB (b : SpaceB →ₗ[ℚ] SpaceB) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (trace_conj c a).symm

theorem not_isConj_xGriess_tGriess : ¬ IsConj xGriess tGriess := by
  intro h
  have h' : IsConj xmat tStar := by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact isConj_iff.2 ⟨c, congrArg Subtype.val hc⟩
  have := trace_eq_of_isConj h'
  rw [trace_xmat, trace_tStar] at this
  norm_num at this

theorem not_isConj_xGmat_tGmat : ¬ IsConj xGmat tGmat := by
  intro h
  have h' : IsConj xmat tStar := by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact isConj_iff.2 ⟨c, congrArg Subtype.val hc⟩
  have := trace_eq_of_isConj h'
  rw [trace_xmat, trace_tStar] at this
  norm_num at this

theorem orderOf_tGriess : orderOf tGriess = 2 := by
  rw [← orderOf_injective AutO.subtype AutO.subtype_injective]
  exact orderOf_tStar

theorem involution_classes_MGriess_of_Gmat
    (hcensus : ∀ g : Gmat, orderOf g = 2 → IsConj xGmat g ∨ IsConj tGmat g) :
    (∀ g : MGriess, orderOf g = 2 → IsConj xGriess g ∨ IsConj tGriess g) ∧
      ¬ IsConj xGriess tGriess := by
  refine ⟨fun g hg => ?_, not_isConj_xGriess_tGriess⟩
  obtain ⟨-, -, h3, -⟩ := (isTwoBCentralizer_MGriess xGriess (IsConj.refl _)).sylow orderOf_xGriess
  obtain ⟨c, hc⟩ := h3 g ⟨1, by rw [pow_one, ← hg, pow_orderOf_eq_one]⟩
  have hvis : ((c * g * c⁻¹ : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
    rw [← map_cent_xGriess]
    exact ⟨_, hc, rfl⟩
  have hmem : ((c * g * c⁻¹ : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat := Hmat_le_Gmat hvis
  set h : Gmat := ⟨_, hmem⟩
  have hh : orderOf h = 2 := by
    rw [← Subgroup.orderOf_coe h]
    change orderOf ((c * g * c⁻¹ : MGriess) : SpaceB ≃ₗ[ℚ] SpaceB) = 2
    rw [Subgroup.orderOf_coe,
      ← SemiconjBy.orderOf_eq c (x := g) (show c * g = c * g * c⁻¹ * c by group), hg]
  let ι : Gmat →* MGriess := Subgroup.inclusion Gmat_le_AutO
  have hι : ι h = c * g * c⁻¹ := rfl
  have hconj : IsConj (c * g * c⁻¹) g := (isConj_iff.2 ⟨c, rfl⟩).symm
  rcases hcensus h hh with h1 | h1
  · left
    have := ι.map_isConj h1
    rw [hι] at this
    exact (show ι xGmat = xGriess from rfl) ▸ this.trans hconj
  · right
    have := ι.map_isConj h1
    rw [hι] at this
    exact (show ι tGmat = tGriess from rfl) ▸ this.trans hconj

end CFSG.Monster.Existence
