module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporAll
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3Sylow
public import CFSG.RankThree.Asc83Table.J3
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.Asc83Table.PermTables

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open Subgroup

namespace Res423Three

theorem false_of_maximal_of_central {X : Type*} [Group X] [Finite X] {T Z W D : Subgroup X}
    (hZc : ∀ z ∈ Z, ∀ x ∈ T, x * z = z * x) (hZ : CFSG.Assembly.IsElemAbelian 3 Z)
    (hZ9 : Nat.card Z = 9) (hWT : W ≤ T) (hW27 : Nat.card W = 27)
    (hW : CFSG.Assembly.IsElemAbelian 3 W) (hDT : D ≤ T)
    (hD : Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D)
    (hD9 : Nat.card D = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyD, hy3, hyc⟩ : ∃ y : X, y ∉ D ∧ y ^ 3 = 1 ∧ ∀ a ∈ D, a * y = y * a := by
    by_cases hZD : Z ≤ D
    · have hDZ : D = Z := (Subgroup.eq_of_le_of_card_ge hZD (by rw [hD9, hZ9])).symm
      obtain ⟨w, hwW, hwZ⟩ : ∃ w ∈ W, w ∉ Z := by
        by_contra hc
        push Not at hc
        have := Subgroup.card_le_of_le (show W ≤ Z from hc)
        omega
      refine ⟨w, hDZ ▸ hwZ, hW.2 w hwW, fun a ha => ?_⟩
      rw [hDZ] at ha
      exact (hZc a ha w (hWT hwW)).symm
    · obtain ⟨z, hzZ, hzD⟩ : ∃ z ∈ Z, z ∉ D := by
        by_contra hc
        push Not at hc
        exact hZD hc
      exact ⟨z, hzD, hZ.2 z hzZ, fun a ha => hZc z hzZ a (hDT ha)⟩
  obtain ⟨hE, hEcard⟩ := Sec5.isElemAbelian_sup_zpowers hD.prop hyD hy3 hyc
  have h1 := Subgroup.card_le_of_le (hD.2 hE le_sup_left)
  rw [hEcard, hD9] at h1
  omega

theorem exists_E27_of_J3
    {X : Type} [Group X] [Finite X] (φ : X ≃* NativeSporadic.Carrier .J3) :
    ∃ W : Subgroup X, CFSG.Assembly.IsElemAbelian 3 W ∧ Nat.card W = 27 := by
  have : Finite NativeSporadic.J3 := Finite.of_equiv X φ.toEquiv
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (G' := NativeSporadic.J3) (p := 3)
      (by norm_num) φ, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.RankThree.Asc83Table.J3.native_J3.1
  obtain ⟨W, -, hW, hW27⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  rw [h3] at hW27
  exact ⟨W, ⟨hW.1, hW.2⟩, by rw [hW27]; norm_num⟩

end Res423Three

open Res423Three

theorem k423SporJ3 :
    K423SporJ3 := by
  rintro X _ _ ⟨φ⟩ D hD hD9 Y hY hα
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :=
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  obtain ⟨T, hDT⟩ := (Sec5.isPGroup_of_isElemAbelian hD.prop).exists_le_sylow
  have hF := CFSG.AGLEmbedding.kFactJ3Sylow X ⟨φ.trans b⟩ T
  obtain ⟨⟨hZcomm, hZ3⟩, hZ9⟩ := hF.center_elem
  obtain ⟨W, hW, hW27⟩ := exists_E27_of_J3 φ
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := (T : Subgroup X))
    (Sylow.card_eq_multiplicity T) (Sec5.isPGroup_of_isElemAbelian hW)
  refine false_of_maximal_of_central (T := T) (Z := CFSG.Quasithin.centerOf (T : Subgroup X))
    (W := W.map (MulAut.conj g⁻¹).toMonoidHom) (fun z hz x hx => ?_) ⟨hZcomm, hZ3⟩ hZ9
    (Item434AltPerm.map_conj_inv_le hg) ?_ (Res423Two.isElemAbelian_map' _ hW) hDT hD hD9
  · exact Subgroup.mem_centralizer_iff.mp hz.2 x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hW27]

end CFSG.RankThree.PartTwo.Sec4
