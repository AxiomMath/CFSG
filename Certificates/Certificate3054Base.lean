
module

public import Certificates.Kernel.MonsterB.Conj3054.T
public import Certificates.Kernel.MonsterB.Conj3054.C0
public import Certificates.Kernel.MonsterB.Conj3054.C1
public import Certificates.Kernel.MonsterB.Conj3054.C2
public import Certificates.Kernel.MonsterB.Conj3054.C3
public import Certificates.Kernel.MonsterB.Conj3054.C4
public import Certificates.Kernel.MonsterB.Conj3054.C5
public import Certificates.Kernel.MonsterB.Conj3054.C6
public import Certificates.Kernel.MonsterB.Conj3054.C7
public import CFSG.Certificates.Kernel.MonsterB.MatConj22Sound

@[expose] public section

open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2 CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.Bfs
  CFSG.KC.MatConj CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch3054

set_option maxRecDepth 100000

@[expose] def INV : Array (Array ℕ) := #[
  #[3673722, 3202047, 1261813, 1058175, 765968, 1643863, 3201982, 1215000, 159003, 1329304,
    2284554, 2048, 4096, 3786752, 1048576, 16384, 929792, 262144, 1490944, 126976, 32768,
    2977792],
  #[3643428, 2738236, 1499140, 264871, 834212, 1077253, 3643814, 2963203, 327550, 1441554,
    2816244, 2048, 1048576, 1490944, 2598912, 2811904, 3477504, 2977792, 2097152, 3307520, 4096,
    262144],
  #[3034202, 3546059, 1947652, 620889, 825043, 3550758, 419447, 754397, 2806915, 715471, 3206674,
    2048, 8192, 1048576, 2977792, 16384, 3477504, 126976, 2598912, 262144, 1943552, 65536],
  #[3264757, 3177983, 743428, 1708654, 1107839, 875355, 1304554, 154383, 1241606, 1986949,
    3524357, 2048, 1792000, 4096, 32768, 3786752, 2097152, 2598912, 524288, 126976, 8192,
    3307520],
  #[3494177, 2358271, 806434, 2033724, 388319, 2187505, 590612, 1527178, 2505842, 2366502, 957175,
    2048, 3786752, 1490944, 3477504, 16384, 65536, 126976, 262144, 4096, 929792, 3307520],
  #[601505, 2889427, 1346096, 2086434, 3041151, 907087, 285834, 3416337, 2357854, 3094580,
    3672480, 2048, 4100096, 929792, 126976, 262144, 3477504, 2097152, 32768, 1048576, 524288,
    131072],
  #[1239775, 3783080, 335650, 1088747, 4116641, 2422034, 3159754, 565213, 775663, 2169285,
    1021399, 2048, 2811904, 32768, 3477504, 8192, 262144, 65536, 1943552, 1490944, 929792,
    1048576],
  #[2332877, 1427876, 1046312, 2770687, 1302689, 711518, 784454, 2468739, 2324000, 2612187,
    3524357, 2048, 2977792, 32768, 3307520, 8192, 131072, 1792000, 65536, 2598912, 2097152,
    929792],
  #[3182431, 2115455, 1045936, 1919652, 161579, 443032, 2726423, 3275794, 1304549, 2169285,
    1289752, 2048, 65536, 929792, 3477504, 8192, 2598912, 2811904, 1792000, 4096, 32768, 1048576],
  #[388319, 655362, 1107423, 3026010, 3220807, 2757866, 498883, 3813777, 1730821, 2428550,
    3011857, 2048, 524288, 8192, 32768, 2598912, 1490944, 4096, 262144, 131072, 1943552, 3477504],
  #[497825, 2007080, 1598000, 1044985, 961375, 1978875, 589381, 1591643, 2757866, 1346208, 855604,
    2048, 2977792, 4100096, 32768, 16384, 3786752, 2097152, 3477504, 1943552, 2598912, 131072],
  #[1051883, 3933407, 2787112, 499106, 70305, 159747, 2379163, 869086, 2428550, 441853, 616190,
    2048, 524288, 32768, 3307520, 1048576, 4096, 3786752, 1490944, 2598912, 2097152, 4100096],
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
  #[61470, 2, 454683, 710679, 841743, 1329184, 3932224, 128, 145664, 1198592, 2253824, 2176, 4224,
    8320, 16512, 32896, 65695, 131200, 262272, 524416, 1048704, 2097280],
  #[94238, 2, 747547, 868375, 481295, 3045408, 1591360, 145536, 256, 3152384, 1201152, 2304, 4352,
    8448, 16640, 33055, 65792, 131328, 262400, 524544, 1048832, 2097408],
  #[1, 405533, 454683, 497687, 481295, 1214496, 2357312, 1198208, 3152128, 512, 31744, 2560, 4608,
    8704, 16896, 33280, 66048, 131584, 262656, 524831, 1049088, 2097664],
  #[1, 667677, 747547, 710679, 753679, 3244064, 1247296, 2252928, 1200384, 31232, 1024, 3072,
    5120, 9216, 17408, 33792, 66560, 132096, 263199, 525312, 1049600, 2098176],
  #[18463, 133151, 1050655, 2099231, 3305503, 159779, 155715, 145565, 145693, 31262, 31774, 2048,
    4096, 8192, 14366, 63518, 96286, 14365, 407581, 669725, 14363, 14359]]

theorem kInvL : invRows.toList.map Array.toList = INV.toList.map Array.toList := by
  simp only [invRows, Native.invMat, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  decide +kernel

theorem kInv : invRows = INV :=
  Array.toList_inj.1 ((List.map_injective_iff.2 fun _ _ h => Array.toList_inj.1 h) kInvL)

theorem kGen : ∀ k < 24,
    (∀ b < 22, rowOf (Nat.land (Conj3054.GL k) (maskN 484)) b = (gRows k)[b]! ∧
      (gRows k)[b]! < 2 ^ 22) ∧
    (∀ a < 22, fget (Nat.shiftRight (Conj3054.GL k) 512) a 484 &&& ones22 =
      fget (Nat.shiftRight (Conj3054.GL k) 512) a 484) ∧
    ∀ a < 22, ∀ j < 22, rowOf (fget (Nat.shiftRight (Conj3054.GL k) 512) a 484) j =
      if (INV[k]!)[j]!.testBit a then 1 else 0 := by
  decide +kernel

theorem actC_eq {k : ℕ} (hk : k < 24) (n : ℕ) : actConj k n = Conj3054.actC k n := by
  obtain ⟨h1, h2, h3⟩ := kGen k hk
  have e := conjM_eq (G := gRows k) (GI := INV[k]!) (fun b hb => (h1 b hb).1)
    (fun b hb => (h1 b hb).2) h2 h3 n
  rw [actConj, conjRowsL, kInv]
  exact e.symm

theorem reach_iff {r x : ℕ} : Reach actConj 24 r x ↔ Reach Conj3054.actC 24 r x := by
  constructor
  · intro h
    induction h with
    | root => exact Reach.root
    | step k hk _ ih =>
      rw [actC_eq hk]
      exact Reach.step k hk ih
  · intro h
    induction h with
    | root => exact Reach.root
    | step k hk _ ih =>
      rw [← actC_eq hk]
      exact Reach.step k hk ih

open CertificateChecks.Conj3054 in
theorem kTree : treeOK actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 896 = true := by
  refine treeOK_of_chunks (by norm_num) ?_
  have h := sl_add none_lt t0 rfl
  have h := sl_add h t1 rfl
  have h := sl_add h t2 rfl
  have h := sl_add h t3 rfl
  have h := sl_add h t4 rfl
  have h := sl_add h t5 rfl
  have h := sl_add h t6 rfl
  have h := sl_add h t7 rfl
  have h := sl_add h t8 rfl
  have h := sl_add h t9 rfl
  have h := sl_add h t10 rfl
  have h := sl_add h t11 rfl
  have h := sl_add h t12 rfl
  exact sl_add h t13 rfl

open CertificateChecks.Conj3054 in
theorem kClose : closeOK actC 24 recC edgeC 56925 484 64 896 = true := by
  refine closeOK_of_chunks (by norm_num) ?_
  have h := sl_add none_lt c0_0 rfl
  have h := sl_add h c0_1 rfl
  have h := sl_add h c0_2 rfl
  have h := sl_add h c0_3 rfl
  have h := sl_add h c0_4 rfl
  have h := sl_add h c0_5 rfl
  have h := sl_add h c0_6 rfl
  have h := sl_add h c1_0 rfl
  have h := sl_add h c1_1 rfl
  have h := sl_add h c1_2 rfl
  have h := sl_add h c1_3 rfl
  have h := sl_add h c1_4 rfl
  have h := sl_add h c1_5 rfl
  have h := sl_add h c1_6 rfl
  have h := sl_add h c2_0 rfl
  have h := sl_add h c2_1 rfl
  have h := sl_add h c2_2 rfl
  have h := sl_add h c2_3 rfl
  have h := sl_add h c2_4 rfl
  have h := sl_add h c2_5 rfl
  have h := sl_add h c2_6 rfl
  have h := sl_add h c3_0 rfl
  have h := sl_add h c3_1 rfl
  have h := sl_add h c3_2 rfl
  have h := sl_add h c3_3 rfl
  have h := sl_add h c3_4 rfl
  have h := sl_add h c3_5 rfl
  have h := sl_add h c3_6 rfl
  have h := sl_add h c4_0 rfl
  have h := sl_add h c4_1 rfl
  have h := sl_add h c4_2 rfl
  have h := sl_add h c4_3 rfl
  have h := sl_add h c4_4 rfl
  have h := sl_add h c4_5 rfl
  have h := sl_add h c4_6 rfl
  have h := sl_add h c5_0 rfl
  have h := sl_add h c5_1 rfl
  have h := sl_add h c5_2 rfl
  have h := sl_add h c5_3 rfl
  have h := sl_add h c5_4 rfl
  have h := sl_add h c5_5 rfl
  have h := sl_add h c5_6 rfl
  have h := sl_add h c6_0 rfl
  have h := sl_add h c6_1 rfl
  have h := sl_add h c6_2 rfl
  have h := sl_add h c6_3 rfl
  have h := sl_add h c6_4 rfl
  have h := sl_add h c6_5 rfl
  have h := sl_add h c6_6 rfl
  have h := sl_add h c7_0 rfl
  have h := sl_add h c7_1 rfl
  have h := sl_add h c7_2 rfl
  have h := sl_add h c7_3 rfl
  have h := sl_add h c7_4 rfl
  have h := sl_add h c7_5 rfl
  exact sl_add h c7_6 rfl

theorem kRoot : rootConj = Conj3054.rootK := by decide +kernel

theorem valF_lt (r : ℕ) : valF 484 r < 2 ^ 484 := by
  change r &&& (1 <<< 484 - 1) < _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem validConj_of_lt {x : ℕ} (hx : x < 2 ^ 484) : validConj x = true := by
  have hl : (rowsOf x).toList = (List.range 22).map (rowOf x) := by simp [rowsOf]
  have e : encL (rowsOf x).toList = x := by
    refine eq_of_rowOf 22 _ _ (by simpa [hl] using encL_lt (rowsOf x).toList) hx fun t ht => ?_
    rw [rowOf_encL _ _ (by simp [hl, ht]), hl, map_range_get _ ht,
      Nat.mod_eq_of_lt (rowOf_lt22 x t)]
  simp [validConj, e]

theorem facts : natCertOK actConj 24 validConj rootConj conjCert = true ∧
    conjCert.pts.size = 56925 := by
  obtain ⟨S, hS, hcard, -, -, hmem⟩ := orbit_sound (by norm_num) kTree kClose
  have hS' : ∀ x, Reach actConj 24 rootConj x ↔ x ∈ S := fun x => by
    rw [kRoot]
    exact reach_iff.trans (hS x)
  have hv : ∀ x ∈ S, validConj x = true := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := (hmem x).1 hx
    exact validConj_of_lt (valF_lt _)
  obtain ⟨h1, -, h3, -⟩ := natBfs_spec (fuel := 60000) S hS' hv (by rw [hcard]; norm_num)
  exact ⟨h1, h3.trans hcard⟩

theorem kInvOK : (List.range 24).all (fun k => (List.range 22).all fun j =>
    Native.actD 22 (gRows k) ((invRows[k]!)[j]!) == 1 <<< j) = true := by
  rw [kInv]
  simp only [List.all_eq_true, List.mem_range]
  decide +kernel

theorem kRootRows : (List.range 22).all (fun t => rowOf rootConj t == (gRows 12)[t]!) = true := by
  simp only [List.all_eq_true, List.mem_range]
  decide +kernel

end CertificateChecks.Batch3054

namespace Certificates

open CertificateChecks

end Certificates
