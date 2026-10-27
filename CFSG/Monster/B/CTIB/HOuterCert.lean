module

public import CFSG.Monster.B.CTIB.Rank2158Witness
public meta import Certificates.Data.CFSGNative.CTIB.Coset
public import Certificates.Certificate3122
public import Certificates.Certificate3100
public import Certificates.Certificate3110
public import Certificates.Certificate3011
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B Native

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem qmul_4204845 : qmul gArr 10541 (2 ^ 22) = 4204845 :=
  Certificates.certificate3122.1

theorem isInv_4204845 :
    isInv gArr (liftImgsN 6).toArray (sqCode 6) 4204845 = true :=
  Certificates.certificate3122.2.1

theorem validK_4204845 : validK 6 4204845 = true := by
  rw [validK, ← liftImgsN_eq, isInv_4204845]
  decide

theorem fuseBfs_4204845 : (natBfs (fuseAct (liftImgsN 6).toArray
    ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray
    ((List.range 15).map fun j => deltaN 6 j).toArray) 37 46090 65).1.contains 4204845 = true :=
  Certificates.certificate3122.2.2

theorem fuseCert_4204845 : (fuseCert 6 (1, 64, 46090)).1.contains
    4204845 = true :=
  fuseBfs_4204845

theorem rs6_mul_xs :
    rs 6 * xs = cosetElt 6
    4204845 := by
  rw [rs6_eq, cosetElt, cosetElt, mul_assoc, ← qS_two_pow_22, qS_mul, qmul_4204845]

theorem rs8_eq :
    rs 8 = cosetElt 6 46090 := rfl

theorem mem_fClass_4204845 :
    cosetElt 6 4204845 ∈ fClass 6
    (cosetElt 6 46090) := by
  have hr : ((1, 64, 46090) : ℕ × ℕ × ℕ) ∈ fusionRecsN 6 := by
    rw [fusionRecs_eq.1]
    simp
  exact ((fOrbit_facts (Or.inl rfl) hr).2.2.2 4204845 validK_4204845).2 fuseCert_4204845

theorem isConj_rs6_mul_xs :
    IsConj (rs 6 * xs) (rs 8) := by
  obtain ⟨g, -, hg⟩ := conj_of_fClass (Or.inl rfl) mem_fClass_4204845
  rw [rs6_mul_xs, rs8_eq]
  exact isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]; exact hg⟩

theorem rank_rs6_mul_xs :
    ((βr (rs 6 * xs)) - 1).rank = 2168 :=
  (rank_beta_conj isConj_rs6_mul_xs).trans ((rank_rs (i := 8) (by norm_num)).trans rfl)

end CFSG.Monster.B.CTIB
