module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldE9
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldExc
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTits
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Open
open CFSG.Assembly.RankThreeEven (projSp projSU)


section Certs


theorem k419HasE9 : K419HasE9 := by
  intro K _ _ hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hK with ⟨n, hn⟩ | he | ⟨n, hn⟩ | hT | ⟨n, hn2, ⟨e⟩⟩ | he6
  ·
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hn.2
    haveI := Fintype.ofFinite F
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by
      rw [← Nat.card_eq_fintype_card, hF])
    exact HeringOF.HasE9.of_mulEquiv e.symm HeringOF.hasE9_adjointG2
  · obtain ⟨e⟩ := he
    exact HeringOF.HasE9.of_mulEquiv e.symm HeringOF.hasE9_projSU_three_three
  ·
    obtain ⟨-, -, -, -, -, hiso⟩ := ReeTag.large_Ree_model_Schreier K 2 n hn
    obtain ⟨hadm, a, hfa, F, _, _, hF, ⟨e⟩⟩ := hn
    haveI := Fintype.ofFinite F
    haveI : CharP F ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := n) (by
      rw [← Nat.card_eq_fintype_card, hF]
      rfl)
    have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
    obtain ⟨E⟩ := hiso a F hfa hF ⟨e⟩
    haveI : Finite (ReeTag.F4.reeGamma F a) := Subtype.finite
    obtain ⟨u, v, hu1, hu3, hv3, huv, hv⟩ :=
      CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.reeGamma_exists_e9 a F hF'
    exact HeringOF.HasE9.of_mulEquiv E.symm
      (HeringOF.exists_elemAbelian_of_commute hu3 hu1 hv3 huv hv)
  ·
    obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1 hT
    haveI : Finite CFSG.Sporadic.Schreier.Tits.titsD := Nat.finite_of_card_ne_zero (by
      rw [CFSG.Sporadic.Schreier.Tits.card_titsD]
      norm_num)
    have h3 : 3 ∣ Nat.card CFSG.Sporadic.Schreier.Tits.titsD := by
      rw [CFSG.Sporadic.Schreier.Tits.card_titsD]
      norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨y, hyx, hy3, hy⟩ := Res417Seven.exists_commute_of_titsD hx
    have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      omega
    exact HeringOF.HasE9.of_mulEquiv e.symm
      (HeringOF.exists_elemAbelian_of_commute hx3 hx1 hy3 hyx.symm hy)
  ·
    haveI : NeZero n := ⟨by omega⟩
    haveI : CharP (GaloisField 2 n) 2 := inferInstance
    haveI : Finite (projSp 2 (GaloisField 2 n)) := Finite.of_equiv _ e.toEquiv
    have hE : HeringOF.HasE9 (StatedSp 2 (GaloisField 2 n)) := HeringOF.hasE9_statedSp_two
    exact HeringOF.HasE9.of_mulEquiv e.symm (HeringOF.HasE9.of_mulEquiv
      ((CFSG.RankThree.PartOne.KFU.spEquivProj (K := GaloisField 2 n) (by norm_num : 1 ≤ 2)).trans
        (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n)).symm) hE)
  ·
    obtain ⟨e⟩ := he6
    exact HeringOF.HasE9.of_mulEquiv e.symm HeringOF.hasE9_alternatingGroup_six

end Certs

end CFSG.RankThree.PartTwo.Sec4
