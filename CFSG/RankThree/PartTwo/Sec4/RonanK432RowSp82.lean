module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432WreathProd
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp82Mat
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVSp82

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedScalars StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars glCongr_statedSp
  statedProjCongr)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit

local instance decEqH8 : DecidableEq H8 := inferInstance

theorem wreathFacts_sp8 : WreathFacts sp8Z sp8T where
  pow_z := by decide +kernel
  comm_z := by decide +kernel
  inj := by decide +kernel
  pow_t := by decide +kernel
  conj0 := by decide +kernel
  conj1 := by decide +kernel
  conj2 := by decide +kernel
  t_ne := by decide +kernel

theorem sp8E_pow_three : sp8E ^ 3 = 1 := by
  decide +kernel

theorem sp8E_comm : (∀ i, sp8Z i * sp8E = sp8E * sp8Z i) ∧ sp8T * sp8E = sp8E * sp8T := by
  decide +kernel

theorem sp8F_conj : sp8F * sp8Z 0 * sp8F⁻¹ = (sp8Z 0)⁻¹ ∧ sp8F * sp8Z 1 * sp8F⁻¹ = sp8Z 1 ∧
    sp8F * sp8Z 2 * sp8F⁻¹ = sp8Z 2 ∧ sp8F * sp8E * sp8F⁻¹ = sp8E := by
  decide +kernel

theorem sp8S_conj : sp8S * sp8E * sp8S⁻¹ = sp8Z 0 := by
  decide +kernel

theorem sp8E_not_mem_W : sp8E ∉ wreathW sp8Z sp8T := by
  intro h
  obtain ⟨v, j, hv⟩ := mem_wreathW wreathFacts_sp8 h
  have key : ∀ (v : Fin 3 → ZMod 3) (j : Fin 3), vecElt sp8Z v * sp8T ^ (j : ℕ) ≠ sp8E := by
    decide +kernel
  exact key v j hv.symm

noncomputable def gf21EquivS8 : GaloisField 2 1 ≃+* ZMod 2 :=
  (GaloisField.equivZmodP 2).toRingEquiv

theorem statedScalars_subgroupOf_sp8 :
    (StatedScalars (Fin 4 ⊕ Fin 4) (ZMod 2)).subgroupOf (StatedSp 4 (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨u, hu⟩ := hx
  have hall : ∀ v : (ZMod 2)ˣ, v = 1 := by decide
  have hu1 : u = 1 := hall u
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, hu1, map_one, OneMemClass.coe_one]

noncomputable def statedProjSp8Equiv : StatedProj (StatedSp 4 (ZMod 2)) ≃* H8 :=
  (QuotientGroup.quotientMulEquivOfEq statedScalars_subgroupOf_sp8).trans QuotientGroup.quotientBot

noncomputable def sp82Equiv : projSp 4 (GaloisField 2 1) ≃* H8 :=
  (projSpEquivStatedProj 4 (GaloisField 2 1)).trans
    ((statedProjCongr (glCongr gf21EquivS8) (glCongr_statedSp gf21EquivS8 4)
      (glCongr_statedScalars gf21EquivS8)).trans statedProjSp8Equiv)

theorem not_729_card_H8 : ¬ 729 ∣ Nat.card H8 := by
  have hf5 := Item434SmallTwoIV.factorization_card_projSp_four_two
  have hne : Nat.card (projSp 4 (GaloisField 2 1)) ≠ 0 := by
    intro h0
    rw [h0, Nat.factorization_zero] at hf5
    simp at hf5
  rw [← Nat.card_congr sp82Equiv.toEquiv]
  intro h
  have h6 : 3 ^ 6 ∣ Nat.card (projSp 4 (GaloisField 2 1)) := by
    norm_num
    exact h
  have h6' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h6
  rw [hf5] at h6'
  omega

theorem listRow_H8 : ListRow H8 :=
  listRow_of_wreath3_prod wreathFacts_sp8 (card_wreathW_eq_eighty_one wreathFacts_sp8)
    not_729_card_H8 sp8E_pow_three sp8E_comm.1 sp8E_comm.2 sp8E_not_mem_W
    sp8F_conj.1 sp8F_conj.2.1 sp8F_conj.2.2.1 sp8F_conj.2.2.2 sp8S_conj

theorem listRow_sp82 : ListRow (projSp 4 (GaloisField 2 1)) := by
  haveI : Finite (projSp 4 (GaloisField 2 1)) := Finite.of_equiv _ sp82Equiv.symm.toEquiv
  exact ListRow.of_mulEquiv sp82Equiv.symm listRow_H8

theorem outerRow_sp82 : OuterRow (projSp 4 (GaloisField 2 1)) := by
  haveI : Finite (projSp 4 (GaloisField 2 1)) := Finite.of_equiv _ sp82Equiv.symm.toEquiv
  exact outerRow_of_not_three_dvd_outer Item434SmallTwoIV.not_three_dvd_card_outer_projSp_four_two

theorem row_sp82 : RowOf (projSp 4 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSp 4 (GaloisField 2 1)) := Finite.of_equiv _ e.toEquiv
  exact GoodRow.of_mulEquiv (S := projSp 4 (GaloisField 2 1)) e.symm
    ⟨listRow_sp82, outerRow_sp82⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
