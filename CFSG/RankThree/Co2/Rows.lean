module

public import CFSG.RankThree.Co2.Concrete
public import CFSG.Monster.B.TwoA.Co2Inv.CentOrder
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import Certificates.Certificate3054
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3055
public import Certificates.Certificate16022
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Blueprint CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert
  CFSG.Monster.B.Short CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot
  CFSG.Monster.SpinLattice CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts
  CFSG.Monster.B.TwoA.Co2Inv

@[expose] def HasRows (k : Kstab v0) (R : Array ℕ) : Prop := wAct v0 k = rowsEnd R

theorem HasRows.mul {k k' : Kstab v0} {R R' : Array ℕ} (h : HasRows k R) (h' : HasRows k' R') :
    HasRows (k * k') (rowsMul R R') := by
  unfold HasRows at *
  rw [wAct_mul, h, h', rowsEnd_mul]

theorem HasRows.one : HasRows 1 idRows := by
  unfold HasRows
  rw [wAct_one, rowsEnd_idRows]

theorem HasRows.inv {k : Kstab v0} {R S : Array ℕ} (h : HasRows k R)
    (hS : ∀ t < 22, (rowsMul R S)[t]! = idRows[t]!) : HasRows k⁻¹ S := by
  unfold HasRows at *
  have hr : rowsEnd S * wAct v0 k = 1 := by
    rw [h, rowsEnd_mul, ← rowsEnd_idRows]
    exact rowsEnd_congr hS
  have hl : wAct v0 k * wAct v0 k⁻¹ = 1 := by
    rw [← wAct_mul, inv_mul_cancel, wAct_one]
  calc wAct v0 k⁻¹ = (rowsEnd S * wAct v0 k) * wAct v0 k⁻¹ := by rw [hr, one_mul]
    _ = rowsEnd S := by rw [mul_assoc, hl, mul_one]

@[expose] def gC (j : ℕ) : Cr := if h : j < 21 then ⟨cGen ⟨j, h⟩, cGen_mem_Cr _⟩ else 1

theorem hasRows_gC {j : ℕ} (hj : j < 21) : HasRows (gC j : Kstab v0) candRows[j]! := by
  unfold HasRows
  rw [gC, dite_eq_left hj, wAct_cGen, cRows_eq_candRows j hj]

@[expose] def invC : Array (Array ℕ) := #[
  #[1, 798722, 894980, 880648, 845840, 3094580, 3980882, 3938444, 3045652, 31262, 31774, 2048,
    4096, 8192, 16384, 32768, 65536, 929792, 524288, 262144, 1943552, 2977792],
  #[1, 442372, 393218, 485392, 501768, 442936, 3558996, 443032, 2422034, 512, 31774, 2048, 4096,
    8192, 16384, 32768, 65536, 1490944, 1048576, 1943552, 262144, 3477504],
  #[1, 501768, 485392, 393218, 442372, 3550758, 501834, 3669126, 1441554, 512, 31774, 2048, 4096,
    8192, 16384, 32768, 65536, 2598912, 2097152, 2977792, 3477504, 262144],
  #[1, 880648, 845840, 798722, 894980, 855604, 1997900, 2049170, 855828, 31262, 31774, 2048,
    4096, 8192, 16384, 32768, 65536, 2977792, 2811904, 2598912, 4100096, 929792],
  #[1, 655362, 765968, 743428, 714760, 3899436, 1641542, 3672460, 2646164, 1024, 1566, 2048,
    4096, 8192, 16384, 126976, 32768, 524288, 131072, 262144, 3786752, 1792000],
  #[49153, 2, 442372, 714760, 845840, 1345592, 3981521, 128, 145693, 1215000, 2270228, 2048,
    4096, 8192, 32768, 16384, 126976, 131072, 262144, 524288, 1490944, 2811904],
  #[1, 2680956, 2632302, 2657398, 2641530, 3827270, 1599020, 2646164, 626060, 1566, 1024, 2048,
    4096, 16384, 8192, 32768, 126976, 2811904, 3477504, 131072, 1792000, 524288],
  #[1, 393218, 442372, 485392, 501768, 1345592, 3474034, 1329304, 2517396, 512, 1566, 2048, 8192,
    4096, 16384, 32768, 126976, 262144, 131072, 524288, 1490944, 3477504],
  #[1, 2, 442372, 765968, 880648, 32, 64, 1329304, 3672460, 1215000, 2323988, 2048, 4096, 8192,
    16384, 32768, 126976, 131072, 262144, 929792, 1490944, 3786752],
  #[1, 12317, 12315, 12311, 12303, 12351, 20575, 61599, 94495, 512, 1024, 28702, 26654, 22558,
    14366, 63518, 96286, 161793, 292865, 555009, 1079297, 2127873],
  #[12318, 2, 12315, 12311, 12303, 12351, 135263, 128, 256, 406047, 668703, 143389, 141341,
    137245, 161794, 178178, 210946, 14365, 407581, 669725, 1193986, 2242562],
  #[12318, 12317, 4, 12311, 12303, 442400, 1800256, 454815, 747807, 455199, 748575, 1060891,
    1058843, 1054747, 1079300, 1095684, 1128452, 1193988, 1325060, 1587204, 14363, 3160068],
  #[12318, 12317, 12315, 8, 12303, 880672, 2590784, 710815, 868639, 498207, 711711, 2109463,
    2107415, 2103319, 2127880, 2144264, 2177032, 2242568, 2373640, 2635784, 3160072, 14359],
  #[12318, 12317, 12315, 12311, 16, 765984, 4108352, 841887, 481567, 481823, 754719, 3295247,
    3297295, 3301391, 3276816, 3325968, 3358736, 3162128, 3555344, 3817488, 2244624, 1196048],
  #[12318, 12317, 442372, 880648, 765968, 32, 147551, 1329280, 3045632, 1214976, 3245056, 2080,
    4159, 8255, 16416, 32800, 65568, 131104, 262176, 524320, 1048608, 2097184],
  #[20510, 135197, 1800196, 2590728, 4108304, 147488, 64, 3932288, 1591552, 2357760, 1248256,
    8287, 14400, 2143, 26688, 43103, 75871, 141376, 272479, 534623, 1058880, 2107456],
  #[61470, 2, 454683, 710679, 841743, 1329184, 3932224, 128, 145664, 1198592, 2253824, 2176,
    4224, 8320, 16512, 32896, 65695, 131200, 262272, 524416, 1048704, 2097280],
  #[94238, 2, 747547, 868375, 481295, 3045408, 1591360, 145536, 256, 3152384, 1201152, 2304,
    4352, 8448, 16640, 33055, 65792, 131328, 262400, 524544, 1048832, 2097408],
  #[1, 405533, 454683, 497687, 481295, 1214496, 2357312, 1198208, 3152128, 512, 31744, 2560,
    4608, 8704, 16896, 33280, 66048, 131584, 262656, 524831, 1049088, 2097664],
  #[1, 667677, 747547, 710679, 753679, 3244064, 1247296, 2252928, 1200384, 31232, 1024, 3072,
    5120, 9216, 17408, 33792, 66560, 132096, 263199, 525312, 1049600, 2098176],
  #[18463, 133151, 1050655, 2099231, 3305503, 159779, 155715, 145565, 145693, 31262, 31774, 2048,
    4096, 8192, 14366, 63518, 96286, 14365, 407581, 669725, 14363, 14359]
]

theorem invC_check : ∀ j < 21, ∀ t < 22, (rowsMul candRows[j]! invC[j]!)[t]! = idRows[t]! := by
  decide +kernel

theorem hasRows_gC_inv {j : ℕ} (hj : j < 21) : HasRows ((gC j)⁻¹ : Cr) invC[j]! :=
  (hasRows_gC hj).inv (invC_check j hj)

theorem closure_gC : Subgroup.closure (gC '' {j | j < 21}) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨k, hk⟩ -
  have hk' : k ∈ Subgroup.closure (Set.range cGen) := by rw [← G21_eq, G21_eq_Cr]; exact hk
  have hmap : Subgroup.closure (Set.range cGen) ≤
      (Subgroup.closure (gC '' {j | j < 21})).map Cr.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨gC j, Subgroup.subset_closure ⟨j, j.2, rfl⟩, ?_⟩
    rw [gC, dite_eq_left j.2]
    rfl
  obtain ⟨k', hk'', e⟩ := hmap hk'
  have : k' = ⟨k, hk⟩ := Subtype.ext e
  exact this ▸ hk''

@[expose] def letterRows (j : ℕ) : Array ℕ := if j < 21 then candRows[j]! else invC[j - 21]!

@[expose] def letterCr (j : ℕ) : Cr := if j < 21 then gC j else (gC (j - 21))⁻¹

theorem hasRows_letterCr {j : ℕ} (hj : j < 42) :
    HasRows (letterCr j : Kstab v0) (letterRows j) := by
  unfold letterCr letterRows
  split_ifs with h
  · exact hasRows_gC h
  · exact hasRows_gC_inv (by omega)

@[expose] def wordRows (w : List ℕ) : Array ℕ :=
  w.foldl (fun A j => rowsMul A (letterRows j)) idRows

@[expose] def wordCr (w : List ℕ) : Cr := w.foldl (fun x j => x * letterCr j) 1

theorem foldl_hasRows : ∀ (w : List ℕ), (∀ j ∈ w, j < 42) → ∀ (x : Cr) (A : Array ℕ),
    HasRows (x : Kstab v0) A →
    HasRows ((w.foldl (fun x j => x * letterCr j) x : Cr) : Kstab v0)
      (w.foldl (fun A j => rowsMul A (letterRows j)) A)
  | [], _, _, _, h => h
  | j :: w, hw, x, A, h => by
    simp only [List.foldl_cons]
    exact foldl_hasRows w (fun i hi => hw i (List.mem_cons_of_mem _ hi)) _ _
      (h.mul (hasRows_letterCr (hw j List.mem_cons_self)))

theorem hasRows_wordCr {w : List ℕ} (hw : ∀ j ∈ w, j < 42) :
    HasRows (wordCr w : Kstab v0) (wordRows w) :=
  foldl_hasRows w hw 1 idRows HasRows.one

theorem foldl_mul_letterCr (w : List ℕ) (x : Cr) :
    w.foldl (fun x j => x * letterCr j) x = x * wordCr w := by
  induction w generalizing x with
  | nil => simp [wordCr]
  | cons j w ih =>
    simp only [List.foldl_cons, wordCr]
    rw [ih, ih (1 * letterCr j), one_mul, mul_assoc]

theorem wordCr_append (u v : List ℕ) : wordCr (u ++ v) = wordCr u * wordCr v := by
  rw [wordCr, List.foldl_append, foldl_mul_letterCr]
  rfl

@[expose, instance_reducible] def crConjAction : MulAction Cr (Module.End (ZMod 2) (Wv v0)) where
  smul g T := wAct v0 ((g : Kstab v0)⁻¹) * T * wAct v0 (g : Kstab v0)
  one_smul T := by
    change wAct v0 ((1 : Kstab v0)⁻¹) * T * wAct v0 1 = T
    rw [inv_one, wAct_one, one_mul, mul_one]
  mul_smul g h T := by
    change wAct v0 ((g : Kstab v0) * h)⁻¹ * T * wAct v0 ((g : Kstab v0) * h) =
      wAct v0 (g : Kstab v0)⁻¹ * (wAct v0 (h : Kstab v0)⁻¹ * T * wAct v0 (h : Kstab v0)) *
        wAct v0 (g : Kstab v0)
    rw [mul_inv_rev, wAct_mul, wAct_mul]
    simp only [mul_assoc]

attribute [local instance] crConjAction

end CFSG.RankThree.Co2
