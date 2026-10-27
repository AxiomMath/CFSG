module

public import CFSG.Sporadic.J2.Representations.Module12Alg

public section

open Module CFSG.RepresentationTheory.GF2
namespace CFSG.Sporadic.J2.Module12

def Qlist : List ℕ := [
  0,
  1,
  2,
  3,
  4,
  5,
  6,
  7,
  8,
  9,
  10,
  11,
  12,
  13,
  14,
  15,
  16,
  17,
  18,
  19,
  20,
  21,
  22,
  23,
  24,
  25,
  26,
  27,
  28,
  29,
  30,
  31,
  32,
  33,
  34,
  35,
  36,
  37,
  38,
  39,
  40,
  41,
  42,
  43,
  44,
  45,
  46,
  47,
  48,
  49,
  50,
  51,
  52,
  53,
  54,
  55,
  56,
  57,
  58,
  59,
  60,
  61,
  62,
  63,
  64,
  65,
  66,
  67,
  68,
  69,
  70,
  71]

@[expose] def WQidata : List ℕ := [
  961861791950513433788,
  479135905613704647160,
  67089991558542914476,
  917320068723608040054,
  847842439572042383278,
  504134790449725849001,
  354666366110280390249,
  4634854086637711790316,
  1651344592619068282432,
  2005382004260611816834,
  1015923151435765511469,
  4435474189846353126110,
  104581293516205423837,
  770448836377956702569,
  561728715605276812226,
  1505261406215909414386,
  11970485262522806991,
  2223728966199226312508,
  767796605482194028764,
  1296181624503220899880,
  4720607429097323749103,
  4144064026891107234623,
  3316232325902954023433,
  4071827434145195376776,
  21737721030075900049,
  1176944018135068600171,
  722028426124172561102,
  1663041693393686161188,
  343900686174460790990,
  1889724638843591348026,
  1179788508616079257274,
  2490709407561248362292,
  1653101243005676165120,
  2587820163805531402568,
  2445218043803663988097,
  826289955807737754201,
  83987757405886586830,
  14929448204958179937,
  741283274959935079873,
  1761551618550558068107,
  749574397458464479435,
  1539716607206850934069,
  154574768823259461,
  2404423631903013461867,
  3065675080796207703888,
  2123518245638259932130,
  2635196842204563748139,
  819573901512715118844,
  745092085076643142470,
  346233463518365635094,
  909852960020108524402,
  2069023311898845650322,
  420752865905629795328,
  1085441689061422448574,
  1148801131979437255909,
  1839263284644882266212,
  3071019771719981361936,
  1856367984460326206108,
  1163225555379104677626,
  4445652841989252535733,
  1358373783087881852378,
  1428348636874174485710,
  1668615995987622077084,
  1142138376599258863740,
  1101068560184987420300,
  2129870800568315160212,
  4511708940599911221649,
  47663303221856883886,
  44584855890419506790,
  2270228214547865808123,
  2487899162770193036402,
  827862354927572325684]

@[expose] def Q (j : Fin 72) : ℕ := Qlist.getD j.val 0

@[expose] def WQmat : Matrix (Fin 72) (Fin 72) (ZMod 2) :=
  fun i j => ((wmask.getD i.val 0 >>> Q j) &&& 1 : ℕ)

@[expose] def WQinv : Matrix (Fin 72) (Fin 72) (ZMod 2) :=
  fun i j => ((WQidata.getD i.val 0 >>> j.val) &&& 1 : ℕ)

theorem Q_val (j : Fin 72) : Q j = j.val := by revert j; decide +kernel

@[expose] def Qrow (k : Fin 72) : Fin 12 :=
  ⟨Q k / 12, by have h1 := Q_val k; have h2 := k.isLt; omega⟩

@[expose] def Qcol (k : Fin 72) : Fin 12 :=
  ⟨Q k % 12, Nat.mod_lt _ (by decide)⟩

theorem Qrow_val (k : Fin 72) : (Qrow k).val = Q k / 12 := rfl

theorem Qcol_val (k : Fin 72) : (Qcol k).val = Q k % 12 := rfl

theorem Qrow_col (k : Fin 72) : 12 * (Qrow k).val + (Qcol k).val = Q k := by
  rw [Qrow_val, Qcol_val, Q_val]
  omega

theorem WQirow_0 : (WQinv * WQmat) 0 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 0 := by
  decide +kernel

theorem WQirow_1 : (WQinv * WQmat) 1 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 1 := by
  decide +kernel

theorem WQirow_2 : (WQinv * WQmat) 2 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 2 := by
  decide +kernel

theorem WQirow_3 : (WQinv * WQmat) 3 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 3 := by
  decide +kernel

theorem WQirow_4 : (WQinv * WQmat) 4 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 4 := by
  decide +kernel

theorem WQirow_5 : (WQinv * WQmat) 5 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 5 := by
  decide +kernel

theorem WQirow_6 : (WQinv * WQmat) 6 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 6 := by
  decide +kernel

theorem WQirow_7 : (WQinv * WQmat) 7 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 7 := by
  decide +kernel

theorem WQirow_8 : (WQinv * WQmat) 8 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 8 := by
  decide +kernel

theorem WQirow_9 : (WQinv * WQmat) 9 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 9 := by
  decide +kernel

theorem WQirow_10 : (WQinv * WQmat) 10 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 10 := by
  decide +kernel

theorem WQirow_11 : (WQinv * WQmat) 11 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 11 := by
  decide +kernel

theorem WQirow_12 : (WQinv * WQmat) 12 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 12 := by
  decide +kernel

theorem WQirow_13 : (WQinv * WQmat) 13 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 13 := by
  decide +kernel

theorem WQirow_14 : (WQinv * WQmat) 14 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 14 := by
  decide +kernel

theorem WQirow_15 : (WQinv * WQmat) 15 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 15 := by
  decide +kernel

theorem WQirow_16 : (WQinv * WQmat) 16 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 16 := by
  decide +kernel

theorem WQirow_17 : (WQinv * WQmat) 17 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 17 := by
  decide +kernel

theorem WQirow_18 : (WQinv * WQmat) 18 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 18 := by
  decide +kernel

theorem WQirow_19 : (WQinv * WQmat) 19 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 19 := by
  decide +kernel

theorem WQirow_20 : (WQinv * WQmat) 20 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 20 := by
  decide +kernel

theorem WQirow_21 : (WQinv * WQmat) 21 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 21 := by
  decide +kernel

theorem WQirow_22 : (WQinv * WQmat) 22 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 22 := by
  decide +kernel

theorem WQirow_23 : (WQinv * WQmat) 23 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 23 := by
  decide +kernel

theorem WQirow_24 : (WQinv * WQmat) 24 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 24 := by
  decide +kernel

theorem WQirow_25 : (WQinv * WQmat) 25 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 25 := by
  decide +kernel

theorem WQirow_26 : (WQinv * WQmat) 26 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 26 := by
  decide +kernel

theorem WQirow_27 : (WQinv * WQmat) 27 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 27 := by
  decide +kernel

theorem WQirow_28 : (WQinv * WQmat) 28 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 28 := by
  decide +kernel

theorem WQirow_29 : (WQinv * WQmat) 29 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 29 := by
  decide +kernel

theorem WQirow_30 : (WQinv * WQmat) 30 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 30 := by
  decide +kernel

theorem WQirow_31 : (WQinv * WQmat) 31 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 31 := by
  decide +kernel

theorem WQirow_32 : (WQinv * WQmat) 32 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 32 := by
  decide +kernel

theorem WQirow_33 : (WQinv * WQmat) 33 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 33 := by
  decide +kernel

theorem WQirow_34 : (WQinv * WQmat) 34 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 34 := by
  decide +kernel

theorem WQirow_35 : (WQinv * WQmat) 35 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 35 := by
  decide +kernel

theorem WQirow_36 : (WQinv * WQmat) 36 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 36 := by
  decide +kernel

theorem WQirow_37 : (WQinv * WQmat) 37 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 37 := by
  decide +kernel

theorem WQirow_38 : (WQinv * WQmat) 38 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 38 := by
  decide +kernel

theorem WQirow_39 : (WQinv * WQmat) 39 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 39 := by
  decide +kernel

theorem WQirow_40 : (WQinv * WQmat) 40 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 40 := by
  decide +kernel

theorem WQirow_41 : (WQinv * WQmat) 41 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 41 := by
  decide +kernel

theorem WQirow_42 : (WQinv * WQmat) 42 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 42 := by
  decide +kernel

theorem WQirow_43 : (WQinv * WQmat) 43 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 43 := by
  decide +kernel

theorem WQirow_44 : (WQinv * WQmat) 44 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 44 := by
  decide +kernel

theorem WQirow_45 : (WQinv * WQmat) 45 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 45 := by
  decide +kernel

theorem WQirow_46 : (WQinv * WQmat) 46 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 46 := by
  decide +kernel

theorem WQirow_47 : (WQinv * WQmat) 47 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 47 := by
  decide +kernel

theorem WQirow_48 : (WQinv * WQmat) 48 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 48 := by
  decide +kernel

theorem WQirow_49 : (WQinv * WQmat) 49 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 49 := by
  decide +kernel

theorem WQirow_50 : (WQinv * WQmat) 50 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 50 := by
  decide +kernel

theorem WQirow_51 : (WQinv * WQmat) 51 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 51 := by
  decide +kernel

theorem WQirow_52 : (WQinv * WQmat) 52 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 52 := by
  decide +kernel

theorem WQirow_53 : (WQinv * WQmat) 53 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 53 := by
  decide +kernel

theorem WQirow_54 : (WQinv * WQmat) 54 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 54 := by
  decide +kernel

theorem WQirow_55 : (WQinv * WQmat) 55 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 55 := by
  decide +kernel

theorem WQirow_56 : (WQinv * WQmat) 56 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 56 := by
  decide +kernel

theorem WQirow_57 : (WQinv * WQmat) 57 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 57 := by
  decide +kernel

theorem WQirow_58 : (WQinv * WQmat) 58 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 58 := by
  decide +kernel

theorem WQirow_59 : (WQinv * WQmat) 59 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 59 := by
  decide +kernel

theorem WQirow_60 : (WQinv * WQmat) 60 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 60 := by
  decide +kernel

theorem WQirow_61 : (WQinv * WQmat) 61 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 61 := by
  decide +kernel

theorem WQirow_62 : (WQinv * WQmat) 62 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 62 := by
  decide +kernel

theorem WQirow_63 : (WQinv * WQmat) 63 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 63 := by
  decide +kernel

theorem WQirow_64 : (WQinv * WQmat) 64 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 64 := by
  decide +kernel

theorem WQirow_65 : (WQinv * WQmat) 65 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 65 := by
  decide +kernel

theorem WQirow_66 : (WQinv * WQmat) 66 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 66 := by
  decide +kernel

theorem WQirow_67 : (WQinv * WQmat) 67 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 67 := by
  decide +kernel

theorem WQirow_68 : (WQinv * WQmat) 68 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 68 := by
  decide +kernel

theorem WQirow_69 : (WQinv * WQmat) 69 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 69 := by
  decide +kernel

theorem WQirow_70 : (WQinv * WQmat) 70 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 70 := by
  decide +kernel

theorem WQirow_71 : (WQinv * WQmat) 71 = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) 71 := by
  decide +kernel

theorem WQinv_mul : WQinv * WQmat = (1 : Matrix (Fin 72) (Fin 72) (ZMod 2)) := by
  funext i
  fin_cases i
  · exact WQirow_0
  · exact WQirow_1
  · exact WQirow_2
  · exact WQirow_3
  · exact WQirow_4
  · exact WQirow_5
  · exact WQirow_6
  · exact WQirow_7
  · exact WQirow_8
  · exact WQirow_9
  · exact WQirow_10
  · exact WQirow_11
  · exact WQirow_12
  · exact WQirow_13
  · exact WQirow_14
  · exact WQirow_15
  · exact WQirow_16
  · exact WQirow_17
  · exact WQirow_18
  · exact WQirow_19
  · exact WQirow_20
  · exact WQirow_21
  · exact WQirow_22
  · exact WQirow_23
  · exact WQirow_24
  · exact WQirow_25
  · exact WQirow_26
  · exact WQirow_27
  · exact WQirow_28
  · exact WQirow_29
  · exact WQirow_30
  · exact WQirow_31
  · exact WQirow_32
  · exact WQirow_33
  · exact WQirow_34
  · exact WQirow_35
  · exact WQirow_36
  · exact WQirow_37
  · exact WQirow_38
  · exact WQirow_39
  · exact WQirow_40
  · exact WQirow_41
  · exact WQirow_42
  · exact WQirow_43
  · exact WQirow_44
  · exact WQirow_45
  · exact WQirow_46
  · exact WQirow_47
  · exact WQirow_48
  · exact WQirow_49
  · exact WQirow_50
  · exact WQirow_51
  · exact WQirow_52
  · exact WQirow_53
  · exact WQirow_54
  · exact WQirow_55
  · exact WQirow_56
  · exact WQirow_57
  · exact WQirow_58
  · exact WQirow_59
  · exact WQirow_60
  · exact WQirow_61
  · exact WQirow_62
  · exact WQirow_63
  · exact WQirow_64
  · exact WQirow_65
  · exact WQirow_66
  · exact WQirow_67
  · exact WQirow_68
  · exact WQirow_69
  · exact WQirow_70
  · exact WQirow_71

end CFSG.Sporadic.J2.Module12
