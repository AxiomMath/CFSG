module

public import CFSG.Monster.B.CTIB.UniqueComponent
public meta import Certificates.Data.CFSGNative.CTIB.Coset
public import CFSG.Monster.B.CTIB.Rank2158WitnessInputs
public import Certificates.Certificate3121
public import Certificates.Certificate3100
public import Certificates.Certificate3110
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate16022
public import Certificates.Certificate16951

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B Native

@[expose] noncomputable def e2158 :
    Sbp := (wordS' w2158)⁻¹ * qS 1 * wordS' w2158

theorem w2158_letters : ∀ l ∈ w2158, IsLetter2 l := by decide

theorem autApply_w2158 :
    autApply gArr (wordAut (genInvImgs ()) w2158) 1 = 4456968 :=
  Certificates.certificate3121.1

theorem qmul_2158 : qmul gArr 10541 4456968 = 273189 :=
  Certificates.certificate3121.2.1

theorem qmul_2158N :
    qmul gArr (autApply gArr (liftImgsN 6).toArray 4456968) 10541 = 273189 :=
  Certificates.certificate3121.2.2.1

theorem qmul_2158' : qmul gArr
    (autApply gArr (liftImgsK 6).toArray 4456968) 10541 = 273189 :=
  qmul_2158N

theorem isInv_273189 :
    isInv gArr (liftImgsN 6).toArray (sqCode 6) 273189 = true :=
  Certificates.certificate3121.2.2.2.1

theorem validK_273189 : validK 6 273189 = true := by
  rw [validK, ← liftImgsN_eq, isInv_273189]
  decide

theorem fuseBfs_273189 : (natBfs (fuseAct (liftImgsN 6).toArray
    ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray
    ((List.range 15).map fun j => deltaN 6 j).toArray) 37 61 32769).1.contains 273189 = true :=
  Certificates.certificate3121.2.2.2.2

theorem fuseCert_273189 : (fuseCert 6 (256, 32768, 61)).1.contains
    273189 = true :=
  fuseBfs_273189

theorem e2158_eq :
    e2158 = qS 4456968 := by
  have h := conj_wordS' w2158_letters
  rw [e2158, conj_qS h.2.2 h.1, autApply_w2158]

theorem rs6_eq :
    rs 6 = cosetElt 6 10541 := rfl

theorem rs5_eq :
    rs 5 = cosetElt 6 61 := rfl

theorem rs6_mul_e2158 :
    rs 6 * e2158 = cosetElt 6 273189 := by
  rw [e2158_eq, rs6_eq, cosetElt, cosetElt, mul_assoc, qS_mul, qmul_2158]

theorem e2158_mul_rs6 :
    e2158 * rs 6 = cosetElt 6 273189 := by
  rw [e2158_eq, rs6_eq, cosetElt, cosetElt]
  calc qS 4456968 * (hs 6 * qS 10541) = hs 6 * ((hs 6)⁻¹ * qS 4456968 * hs 6) * qS 10541 := by
        group
    _ = hs 6 * qS 273189 := by
        rw [conj_hs_qS (Or.inl rfl), mul_assoc, qS_mul, qmul_2158']

theorem commute_rs6_e2158 :
    Commute (rs 6) e2158 :=
    rs6_mul_e2158.trans e2158_mul_rs6.symm

theorem mem_fClass_2158 :
    cosetElt 6 273189 ∈ fClass 6
    (cosetElt 6 61) := by
  have hr : ((256, 32768, 61) : ℕ × ℕ × ℕ) ∈ fusionRecsN 6 := by
    rw [fusionRecs_eq.1]
    simp
  exact ((fOrbit_facts (Or.inl rfl) hr).2.2.2 273189 validK_273189).2 fuseCert_273189

theorem isConj_rs6_mul_e2158 :
    IsConj (rs 6 * e2158) (rs 5) := by
  obtain ⟨g, -, hg⟩ := conj_of_fClass (Or.inl rfl) mem_fClass_2158
  rw [rs6_mul_e2158, rs5_eq]
  exact isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]; exact hg⟩

theorem isConj_rs6_labelS :
    IsConj (rs 6) labelS :=
  isConj_labelS_of_rank (orderOf_two_iff.2 ⟨rs_mul_self (by norm_num), rs_ne_one (by norm_num)⟩)
    ((rank_rs (by norm_num)).trans rfl)

theorem isConj_e2158_labelS :
    IsConj e2158 labelS := by
  have h1 : IsConj e2158 (qS 1) :=
    isConj_iff.2 ⟨wordS' w2158, by rw [e2158]; group⟩
  exact h1.trans (isConj_of_mem_jClass labelS_mem_jClass).symm

theorem rs6_ne_e2158 :
    rs 6 ≠ e2158 := by
  intro h
  have h1 := isConj_rs6_mul_e2158
  rw [← h, rs_mul_self (by norm_num)] at h1
  exact rs_ne_one (i := 5) (by norm_num) (isConj_one_right.1 h1)

end CFSG.Monster.B.CTIB
