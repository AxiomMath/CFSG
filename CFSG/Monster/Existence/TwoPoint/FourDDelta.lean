module

public import CFSG.Monster.Existence.TwoPoint.ThreeIII

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section General

variable {G : Type} [Group G]

theorem fd_isConj_mul_comm (a b : G) : IsConj (a * b) (b * a) :=
  isConj_iff.2 ⟨b, by group⟩

theorem fd_lieModel_cent2_inf_cent_of_conj (g α β γ α' β' γ' : G) (h1 : g * α * g⁻¹ = α')
    (h2 : g * β * g⁻¹ = β') (h3 : g * γ * g⁻¹ = γ')
    (h : CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent γ) .PSp 4 2 1) :
    CFSG.Blueprint.LieModel ↥(cent2 α' β' ⊓ cent γ') .PSp 4 2 1 := by
  subst h1 h2 h3
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (cent2InfCentConjEquiv g α β γ) h

theorem fd_natCard_cent2_inf_cent_of_conj (g α β γ α' β' γ' : G) (h1 : g * α * g⁻¹ = α')
    (h2 : g * β * g⁻¹ = β') (h3 : g * γ * g⁻¹ = γ') :
    Nat.card ↥(cent2 α' β' ⊓ cent γ') = Nat.card ↥(cent2 α β ⊓ cent γ) := by
  subst h1 h2 h3
  exact (Nat.card_congr (cent2InfCentConjEquiv g α β γ).toEquiv).symm

theorem fd_cent2_inf_cent_rotate (α β γ : G) : cent2 β γ ⊓ cent α = cent2 α β ⊓ cent γ := by
  ext x
  simp only [Subgroup.mem_inf]
  tauto

end General

section MGriess

open CFSG.Monster CFSG.Monster.Griess

theorem exists_fourD_delta
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000) :
    ∃ δ : MGriess, IsConj tGriess δ ∧ IsConj (tGriess * δ) threeARep ∧
      IsConj (uGriess * δ) threeARep ∧
      CFSG.Blueprint.LieModel ↥(cent2 tGriess uGriess ⊓ cent δ) .PSp 4 2 1 ∧
      17 ∣ Nat.card ↥(cent2 tGriess uGriess ⊓ cent δ) := by
  have hG := gmsF1Type_MGriess_uncond
  obtain ⟨y, hy, -, -, -, h3A, h3C⟩ :=
    oddShapes_MGriess I hex hcard (natCard_cent_tGriess_of hA) hTh
      CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point'
  have hsep := oddTypesSeparated_MGriess I (hy 0).1 (hy 0).2 (hy 1).1 (hy 1).2 h3A h3C
  have hKeq := fiK_eq_cent2_MGriess I hex hcard hA hTh
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair_of_isConj I hG hex hsep (α := fiBeta)
    (β := gammaZero) (y := uGriess) isConj_fiBeta isConj_gammaZero uGriess_mem_twoANbr.1
    (isConj_fiBeta_mul_gammaZero.symm.trans uGriess_mem_twoANbr.2)
  have ht : g⁻¹ * fiBeta * g = tGriess := by rw [← hg1]; group
  have hu : g⁻¹ * gammaZero * g = uGriess := by rw [← hg2]; group
  have ht' : g⁻¹ * fiBeta * g⁻¹⁻¹ = tGriess := by rw [inv_inv]; exact ht
  have hu' : g⁻¹ * gammaZero * g⁻¹⁻¹ = uGriess := by rw [inv_inv]; exact hu
  have hδ' : g⁻¹ * fiAlpha * g⁻¹⁻¹ = g⁻¹ * fiAlpha * g := by rw [inv_inv]
  have hback : ∀ X : MGriess, IsConj (g⁻¹ * X * g) X := fun X => isConj_iff.2 ⟨g, by group⟩
  have h17 : 17 ∣ Nat.card ↥(cent2 fiAlpha fiBeta ⊓ cent gammaZero) := by
    rw [Nat.card_congr (interEquivSpL hKeq (fun _ hi hi8 => fiE_commute_gammaZero hi hi8)
      fiE_eight_not_commute_gammaZero).toEquiv]
    exact seventeen_dvd_card_spL
  refine ⟨g⁻¹ * fiAlpha * g, isConj_fiAlpha.trans (isConj_iff.2 ⟨g⁻¹, hδ'⟩), ?_, ?_, ?_, ?_⟩
  · have e : tGriess * (g⁻¹ * fiAlpha * g) = g⁻¹ * (fiBeta * fiAlpha) * g := by
      rw [← ht]; group
    rw [e]
    exact (hback _).trans ((fd_isConj_mul_comm fiBeta fiAlpha).trans isConj_fiAlpha_mul_fiBeta)
  · have e : uGriess * (g⁻¹ * fiAlpha * g) = g⁻¹ * (gammaZero * fiAlpha) * g := by
      rw [← hu]; group
    rw [e]
    exact (hback _).trans ((fd_isConj_mul_comm gammaZero fiAlpha).trans
      (isConj_fiAlpha_mul_gammaZero I hex hcard hA hTh))
  · refine fd_lieModel_cent2_inf_cent_of_conj g⁻¹ fiBeta gammaZero fiAlpha tGriess uGriess
      (g⁻¹ * fiAlpha * g) ht' hu' hδ' ?_
    rw [fd_cent2_inf_cent_rotate]
    exact lieModel_cent2_inf_cent_gammaZero hKeq
  · rw [fd_natCard_cent2_inf_cent_of_conj g⁻¹ fiBeta gammaZero fiAlpha tGriess uGriess
      (g⁻¹ * fiAlpha * g) ht' hu' hδ', fd_cent2_inf_cent_rotate]
    exact h17

end MGriess

end CFSG.Monster.Existence
