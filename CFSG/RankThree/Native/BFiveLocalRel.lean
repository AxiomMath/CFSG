module

public import CFSG.Monster.B.Pinned.Primes.FiveSubgroup
public import Certificates.Certificate8120
public import Certificates.Certificate20951

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native
  CFSG.Blueprint

theorem bFiveH_facts :
    (∀ i : Fin 4, hFive⁻¹ * qFive i * hFive =
      (List.ofFn fun j => qFive j ^ (bFiveHRows.getD i []).getD j 0).prod *
        zFive ^ bFiveHC.getD i 0) ∧
    hFive⁻¹ * zFive * hFive = zFive * zFive :=
  Certificates.certificate8120

theorem MFive_eq_f5M : MFive = f5M := by
  exact Certificates.certificate20951.2.2.2.1

theorem fiveActRows_val (i j : Fin 4) :
    (fiveActRows.getD i []).getD j 0 = (f5X i j).val := by
  revert i j
  exact Certificates.certificate20951.2.2.2.2.1

theorem fiveActC_val (i : Fin 4) :
    fiveActC.getD i 0 = FiveLocal.xc i := by
  revert i
  exact Certificates.certificate20951.2.2.2.2.2.1

theorem bFiveHRows_val (i j : Fin 4) :
    (bFiveHRows.getD i []).getD j 0 = (f5H i j).val := by
  revert i j
  exact Certificates.certificate20951.2.2.2.2.2.2.1

theorem bFiveHC_val (i : Fin 4) :
    bFiveHC.getD i 0 = FiveLocal.hc i := by
  revert i
  exact Certificates.certificate20951.2.2.2.2.2.2.2

theorem bFiveRel :
    FiveLocal.Rel xFive hFive qFive zFive where
  commData := MFive_eq_f5M ▸ commData_five
  z_eq := rfl
  orderOf_x := orderOf_xFive
  conj_x i := by
    rw [conj_qFive i]
    simp only [fiveActRows_val, fiveActC_val]
  conj_xz := pinned_B_five_primary_exact_relations.2.2.2.2.2.2.1
  conj_h i := by
    rw [bFiveH_facts.1 i]
    simp only [bFiveHRows_val, bFiveHC_val]
  conj_hz := by rw [bFiveH_facts.2, sq]

end CFSG.RankThree.Native
