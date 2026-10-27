module

public import CFSG.Monster.Existence.TwoPoint.FourDGen
public import CFSG.Monster.Existence.TwoPoint.FourDDelta

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem fd_isLongTriangle_conjSet {G : Type} [Group G] {a : G} {s : Set G}
    (h : IsLongTriangle a s) (g : G) : IsLongTriangle a (conjSet g s) :=
  ⟨h.1.conjSet g, fun hs => h.2 (by
    have := hs.conjSet g⁻¹
    rwa [conjSet_conjSet, inv_mul_cancel, show conjSet 1 s = s from by ext x; simp [conjSet]]
      at this)⟩

theorem exists_fourD_gamma
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hC : CTIB.CentralizerInput) :
    ∃ γ : MGriess, IsLongTriangle tGriess {tGriess, uGriess, γ} ∧
      ∀ D : Subgroup MGriess, D ≤ cent2 tGriess uGriess → 17 ∣ Nat.card D →
        (cent2 tGriess uGriess ⊓ cent γ) ⊔ D = cent2 tGriess uGriess := by
  have hG := Gmat_eq_AutO hcard
  obtain ⟨ρ, iv, hρ⟩ := exists_fourD_localMap
  set z : cgraph.neighborSet cv0 :=
    ⟨cvOf (elS a0_mem_Ehat), adj_cv0_elS a0_mem_Ehat a0_not_mem_N1⟩ with hz
  obtain ⟨γ, hγ⟩ := exists_fourD_gammaData hG z.2
  exact ⟨γ, isLongTriangle_of_fourD_gammaData hG z.2 hγ, fun D hD h17 =>
    fd_sup_eq_edge_of_dvd hG hC hρ z hγ hD h17⟩

theorem fourD_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
    (hC : CTIB.CentralizerInput) :
    ∀ α β : MGriess, IsConj tGriess α → IsConj tGriess β → IsConj tGriess (α * β) →
      ∃ γ δ : MGriess, IsLongTriangle tGriess {α, β, γ} ∧ IsConj tGriess δ ∧
        IsConj (α * δ) threeARep ∧ IsConj (β * δ) threeARep ∧
        (cent2 α β ⊓ cent γ) ⊔ (cent2 α β ⊓ cent δ) = cent2 α β ∧
        CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent δ) .PSp 4 2 1 := by
  have hG := gmsF1Type_MGriess_uncond
  obtain ⟨y, hy, -, -, -, h3A, h3C⟩ :=
    oddShapes_MGriess I hex hcard (natCard_cent_tGriess_of hA) hTh
      CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point'
  have hsep := oddTypesSeparated_MGriess I (hy 0).1 (hy 0).2 (hy 1).1 (hy 1).2 h3A h3C
  obtain ⟨γ₀, hT₀, hgen⟩ := exists_fourD_gamma hcard hC
  obtain ⟨δ₀, hδA, hδt, hδu, hδL, hδ17⟩ := exists_fourD_delta I hex hcard hA hTh
  intro α β hα hβ hαβ
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair_of_isConj I hG hex hsep hα hβ uGriess_mem_twoANbr.1
    (hαβ.symm.trans uGriess_mem_twoANbr.2)
  have hcj : ∀ X : MGriess, IsConj (g * X * g⁻¹) X := fun X => (isConj_iff.2 ⟨g, rfl⟩).symm
  refine ⟨g * γ₀ * g⁻¹, g * δ₀ * g⁻¹, ?_, hδA.trans (isConj_iff.2 ⟨g, rfl⟩), ?_, ?_, ?_, ?_⟩
  · have e : ({α, β, g * γ₀ * g⁻¹} : Set MGriess) = conjSet g {tGriess, uGriess, γ₀} := by
      rw [conjSet_insert, conjSet_insert, conjSet_singleton, hg1, hg2]
    rw [e]
    exact fd_isLongTriangle_conjSet hT₀ g
  · have e : α * (g * δ₀ * g⁻¹) = g * (tGriess * δ₀) * g⁻¹ := by rw [← hg1]; group
    rw [e]
    exact (hcj _).trans hδt
  · have e : β * (g * δ₀ * g⁻¹) = g * (uGriess * δ₀) * g⁻¹ := by rw [← hg2]; group
    rw [e]
    exact (hcj _).trans hδu
  · have h1 := hgen (cent2 tGriess uGriess ⊓ cent δ₀) inf_le_left hδ17
    have h2 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h1
    rw [Subgroup.map_sup, map_conj_cent2_inf_cent, map_conj_cent2_inf_cent, map_conj_cent2, hg1,
      hg2] at h2
    exact h2
  · exact fd_lieModel_cent2_inf_cent_of_conj g tGriess uGriess δ₀ α β (g * δ₀ * g⁻¹) hg1 hg2 rfl hδL

end CFSG.Monster.Existence
