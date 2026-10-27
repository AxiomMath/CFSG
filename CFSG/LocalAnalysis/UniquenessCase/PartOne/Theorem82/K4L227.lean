module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFOut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

theorem center_eq_bot_of_k4a_hyp (Y : Type) [Group Y] [Finite Y]
    (hq : IsQuasisimple Y) (hodd : Odd (Nat.card (center Y)))
    (hmodel : LieModel (Y ⧸ center Y) .PSL 2 3 3) :
    center Y = ⊥ := by
  haveI : Group.IsPerfect Y := hq.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 3 3) 3 3
    (by norm_num) (by rw [GaloisField.card 3 3 (by norm_num)]) hmodel
  let π : Y →* CFSG.AGLEmbedding.PSL2GF 3 3 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center Y := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hC : π.ker ≤ Subgroup.center Y := le_of_eq hker
  have hoddπ : Odd (Nat.card π.ker) := by rw [hker]; exact hodd
  have h := (CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel
    (K := GaloisField 3 3) (E := Y) (p := 3) (f := 3)
    (by norm_num) (by rw [GaloisField.card 3 3 (by norm_num)]) π hπ hC hoddπ).1 (by norm_num)
  rwa [hker] at h

theorem card_eq_of_k4a_hyp (Y : Type) [Group Y] [Finite Y]
    (hq : IsQuasisimple Y) (hodd : Odd (Nat.card (center Y)))
    (hmodel : LieModel (Y ⧸ center Y) .PSL 2 3 3) :
    Nat.card Y = 2 ^ 2 * 3 ^ 3 * 7 * 13 := by
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_k4a_hyp Y hq hodd hmodel
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 3 3) 3 3
    (by norm_num) (by rw [GaloisField.card 3 3 (by norm_num)]) hmodel
  have hY : Nat.card Y = Nat.card (CFSG.AGLEmbedding.PSL2GF 3 3) := by
    calc Nat.card Y = Nat.card (Y ⧸ Subgroup.center Y) := by
          rw [hZ]
          exact (Nat.card_congr (QuotientGroup.quotientBot (G := Y)).toEquiv).symm
      _ = Nat.card (CFSG.AGLEmbedding.PSL2GF 3 3) := Nat.card_congr e.toEquiv
  rw [hY, CFSG.SectionRank.OddCover.card_psl_two (K := GaloisField 3 3) (p := 3) (f := 3)
    Nat.prime_three (by norm_num) (by rw [GaloisField.card 3 3 (by norm_num)])]
  norm_num

theorem card_mulAut_eq_of_k4a_hyp (Y : Type) [Group Y] [Finite Y]
    (hq : IsQuasisimple Y) (hodd : Odd (Nat.card (center Y)))
    (hmodel : LieModel (Y ⧸ center Y) .PSL 2 3 3) :
    Nat.card (MulAut Y) = 6 * Nat.card Y := by
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_k4a_hyp Y hq hodd hmodel
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 3 3) 3 3
    (by norm_num) (by rw [GaloisField.card 3 3 (by norm_num)]) hmodel
  let φ : Y ≃* CFSG.AGLEmbedding.PSL2GF 3 3 :=
    ((QuotientGroup.quotientBot (G := Y)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans e
  have haut : Nat.card (MulAut Y) = Nat.card (MulAut (CFSG.AGLEmbedding.PSL2GF 3 3)) :=
    Nat.card_congr (MulAut.congr φ).toEquiv
  rw [haut, CFSG.AGLEmbedding.card_mulAut_psl2GF 3 3 (by norm_num),
    card_eq_of_k4a_hyp Y hq hodd hmodel]
  norm_num

theorem commutator_mem_innAut_of_k4a_hyp (Y : Type) [Group Y] [Finite Y]
    (hq : IsQuasisimple Y) (hodd : Odd (Nat.card (center Y)))
    (hmodel : LieModel (Y ⧸ center Y) .PSL 2 3 3) (φ ψ : MulAut Y) :
    φ * ψ * φ⁻¹ * ψ⁻¹ ∈ innAut Y := by
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_k4a_hyp Y hq hodd hmodel
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 3 3) 3 3
    (by norm_num) (by rw [GaloisField.card 3 3 (by norm_num)]) hmodel
  let iso : Y ≃* CFSG.AGLEmbedding.PSL2GF 3 3 :=
    ((QuotientGroup.quotientBot (G := Y)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans e
  have hOut : CFSG.GH74.GLS.Stage2.Local.P27.OutAbel Y :=
    CFSG.GH74.GLS.Stage2.Local.P27.OutAbel.of_mulEquiv iso.symm
      (CFSG.GH74.GLS.Stage2.Local.P27.outAbel_psl2 (GaloisField 3 3))
  obtain ⟨j, hj⟩ := hOut φ ψ
  exact ⟨j, hj.symm⟩

theorem k4a_holds : K4a := by
  intro Y _ _ hq hodd hmodel
  exact ⟨card_eq_of_k4a_hyp Y hq hodd hmodel,
    card_mulAut_eq_of_k4a_hyp Y hq hodd hmodel,
    fun φ ψ => commutator_mem_innAut_of_k4a_hyp Y hq hodd hmodel φ ψ,
    fun p hp h5 => k5L227_holds Y hq hodd hmodel p hp h5⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
