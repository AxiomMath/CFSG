module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.RankThree.PartOne.LIT.RankProjective
import CFSG.RankThree.PartTwo.Sec19.SimsC198Crit
import CFSG.RankThree.PartTwo.Sec19.SimsC198Iso
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.BenderSuzuki.MatrixGroups

namespace PSL2

variable {F : Type} [Field F] [Finite F]

private theorem card_psl2_of_card_two (hF : Nat.card F = 2) :
    Nat.card (PSL2MatrixGroup F) = 6 := by
  have h := CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear F 2 (by norm_num)
  rw [hF] at h
  simpa using h

private theorem isMulCommutative_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsMulCommutative G) : IsMulCommutative H := by
  rw [isMulCommutative_iff] at h ⊢
  intro a b
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact h _ _

private theorem isMulCommutative_sylow_three (hF2 : Nat.card F ≠ 2)
    (Q : Sylow 3 (PSL2MatrixGroup F)) : IsMulCommutative (Q : Subgroup (PSL2MatrixGroup F)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h3 : ringChar F = 3
  · haveI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 3 := h3 ▸ ringChar.charP F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 3
    have hK : Nat.card F = 3 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    let Q0 := CFSG.SectionRank.OddCover.pslUSylow (K := F) (p := 3) (f := (n : ℕ))
      (by norm_num) hK
    have hQ0 : IsMulCommutative (Q0 : Subgroup (PSL2MatrixGroup F)) := by
      rw [CFSG.SectionRank.OddCover.coe_pslUSylow]
      exact (CFSG.SectionRank.OddCover.isElemAbelian_range_pslU (K := F) (p := 3)).1
    exact isMulCommutative_of_mulEquiv (Sylow.equiv Q0 Q) hQ0
  · have h4 : 4 ≤ Nat.card F := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      by_contra hlt
      have h3F : Nat.card F = 3 := by omega
      have : CharP F 3 := by
        haveI : Fintype F := Fintype.ofFinite F
        exact charP_of_card_eq_prime (by simpa [Nat.card_eq_fintype_card] using h3F)
      exact h3 (ringChar.eq F 3)
    haveI : IsCyclic (Q : Subgroup (PSL2MatrixGroup F)) :=
      CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_psl2 h3 h4 Q
    infer_instance

end PSL2

theorem noLocalDatum_PSL2 (F : Type) [Field F] [Finite F] : NoLocalDatum (PSL2MatrixGroup F) := by
  by_cases hF2 : Nat.card F = 2
  · exact noLocalDatum_of_not_dvd (by rw [PSL2.card_psl2_of_card_two hF2]; norm_num)
  · intro c L hLD
    obtain ⟨P, -, hP, hPnc⟩ := hLD.exists_nonabelian
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
    haveI := PSL2.isMulCommutative_sylow_three hF2 Q
    exact hPnc (isMulCommutative_anti hPQ)

theorem noLocalDatum_projSL_two (F : Type) [Field F] [Finite F] :
    NoLocalDatum (CFSG.Assembly.RankThreeEven.projSL 2 F) :=
  NoLocalDatum.of_mulEquiv (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL F) (noLocalDatum_PSL2 F)

end CFSG.RankThree.PartTwo.Sec19.SimsC198
