module

public import CFSG.Monster.B.Classical.E6AdjointDefs
public import CFSG.Blueprint.ChevalleyRoots
import CFSG.LieType.Steinberg.Adjoint.Pairs

public noncomputable section

namespace CFSG.Monster.B.Classical.E6Adjoint

open CFSG.Blueprint.Chevalley

@[expose] def cartanForm (u w : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ i, u i * cartanPair i w

private theorem cartanForm_eq_iform (u w : Fin Tag.E6.rank → ℤ) :
    cartanForm u w = CFSG.LieType.Steinberg.Adjoint.iform u w := by
  simp only [cartanForm, cartanPair, CFSG.LieType.Steinberg.Adjoint.iform, Tag.symmetrizedCartan,
    Tag.symmetrizer, one_mul, Finset.mul_sum, mul_assoc]

theorem cartanForm_self_of_isRoot
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    cartanForm γ γ = 2 := by
  obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot hγ
  rw [cartanForm_eq_iform, hj]
  simp [Tag.symmetrizer]

theorem e6Certificate_length : e6Certificate.roots.length = 72 := by decide

theorem isRoot_certRoot
    {k : ℕ} (hk : k < 72) : IsRoot Tag.E6 (e6Certificate.root k) :=
  RootCertificate.isRoot_root e6Certificate_check k (by rw [e6Certificate_length]; exact hk)

@[expose] def lab (k : Fin 78) : Label Tag.E6 :=
  if h : (k : ℕ) < 6 then Sum.inl ⟨k, h⟩
  else Sum.inr ⟨e6Certificate.root ((k : ℕ) - 6), isRoot_certRoot (by omega)⟩

theorem lab_of_lt
    {k : Fin 78} (h : (k : ℕ) < 6) : lab k = Sum.inl ⟨k, h⟩ :=
  dite_eq_left h

theorem lab_of_ge {k : Fin 78} (h : ¬(k : ℕ) < 6) :
    lab k = Sum.inr ⟨e6Certificate.root ((k : ℕ) - 6), isRoot_certRoot (by omega)⟩ :=
  dite_eq_right h

theorem lab_surjective : Function.Surjective lab := by
  rintro (i | ⟨α, hα⟩)
  · exact ⟨⟨i, lt_trans i.2 (by decide)⟩, lab_of_lt i.2⟩
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq e6Certificate_check hα
    rw [e6Certificate_length] at hk
    refine ⟨⟨k + 6, by omega⟩, ?_⟩
    rw [lab_of_ge (by simp)]
    simp

variable (R : Type*) [CommRing R]

@[expose] def toVec (m : ℕ) : RootModule Tag.E6 R :=
  ∑ k : Fin 78, if m.testBit k then Finsupp.single (lab k) 1 else 0

@[expose] def lvec (L : List ℕ) : RootModule Tag.E6 R :=
  (L.map fun l => toVec R (1 <<< l)).sum

variable {R}

theorem toVec_zero : toVec R 0 = 0 := by
  simp [toVec]

theorem toVec_xor
    [CharP R 2] (m n : ℕ) : toVec R (m ^^^ n) = toVec R m + toVec R n := by
  simp only [toVec, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor]
  cases m.testBit k <;> cases n.testBit k <;>
    simp [← Finsupp.single_add, one_add_one_eq_two, CharTwo.two_eq_zero]

theorem toVec_one_shiftLeft
    (k : Fin 78) : toVec R (1 <<< (k : ℕ)) = Finsupp.single (lab k) 1 := by
  rw [toVec, Finset.sum_eq_single k]
  · simp [Nat.one_shiftLeft]
  · intro j _ hj
    have hj' : (k : ℕ) ≠ j := fun h => hj (Fin.ext h).symm
    simp [Nat.one_shiftLeft, hj']
  · simp

theorem toVec_one_shiftLeft' {l : ℕ} (hl : l < 78) :
    toVec R (1 <<< l) = Finsupp.single (lab ⟨l, hl⟩) 1 :=
  toVec_one_shiftLeft ⟨l, hl⟩

theorem toVec_of_lt {e : ℕ} (he : e < 64) :
    toVec R e = ∑ i : Fin Tag.E6.rank, (if e.testBit i then (1 : R) else 0) • hVec Tag.E6 R i := by
  symm
  refine Fintype.sum_of_injective
    (fun i : Fin Tag.E6.rank => (⟨i, lt_trans i.2 (by decide)⟩ : Fin 78))
    (fun i j h => Fin.ext (Fin.mk.inj h)) _ _ (fun k hk => ?_) (fun i => ?_)
  · have hk6 : ¬(k : ℕ) < 6 := fun h => hk ⟨⟨k, h⟩, rfl⟩
    have h64 : (64 : ℕ) ≤ 2 ^ (k : ℕ) :=
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : e.testBit k = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le he h64)
    simp [this]
  · rw [lab_of_lt (k := ⟨i, lt_trans i.2 (by decide)⟩) i.2]
    split_ifs <;> simp [hVec]

@[expose, irreducible] def bracketCodes : ℕ := Nat.ofDigits (2 ^ 320) [
    0x60005e5d5c5b0000005756005400525100000000004b4a00004700000000420000000000000000,
    0x81007f7e007c007a797800767574737271706f6e6d6c6b006968676665006362,
    0x636261605f5e5d5c5b005958575655545352000000004d4c4b004900000000004300000000000000,
    0x8786858400000000000000000000000000760000730071006f6e6d6c006a696867666564,
    0x64636261605f5e000000005958575655545300510000004d4c4b00490047460000430000400000,
    0x83828180007e7d7c7b000078770075007300007000006d6c006a69000000,
    0x6700006400000060000000005b5a595800560000535251004f4e4d004b4a49484700004400424100,
    0x8584838200000000007c000079780076757473727170006e006c6b006900,
    0x690067666500006200605f5e5d5c5b5a005857565554535200504f004d4c4b004900000045004300,
    0x838281807f7e7d7c007a79780000007400000000006e00000000,
    0x6b6a696867660064636261605f005d00005a595857005500000000004f4e4d000000000000000044,
    0x470000000000400000000000000000008000007d7c7b00797877767574737271706f6e6d6c,
    0x717000000000625e006800006700000000560000005d00005c00004a0000000000520000000001,
    0x490000000000410000000000000000007f0000000079007e000000737278000000006d69,
    0x6600000064627100005b006c0000005856670000006100600000004c5c00000000550054000002,
    0x5400000000004b00004700004200004285000086000000000000000000000000006f00006d000000,
    0x770000640000005f000000000000586c000053000000006300004c600000004600000057000004,
    0x5200004d004b4900004300434300000000008100007c008200007500007d000000006a00,
    0x69780000000074000000007000005a0000006b000000005100004e004a00004800000059000008,
    0x5700550000004f004d0000004400440000000000830000840000000000760000730000006e00,
    0x7a000000000065000000005e00005b000000560000530000670050004c00000060005d00000010,
    0x5900000000000000004f000000000045000000000000000080007c00790082000000007e0000,
    0x7d6e00006900007866006200745f0000710000580000006c00006800004e00006300610000000020,
    0x5100004200000000000001000000460000000000000000007b0000007500007200,
    0x7c740000000076756c6b00006f0000006e6360000000006600000065575400000000005b0000004b,
    0x50000005d0000405c0000420000520000000000474700470000000000000000817a00000000,
    0x72820000006a007d00000000645f0000770000000058530000007100000000004c00680000006700,
    0x4d4b0000000000000053000043000000000000000200000048000000000000007f00007900000000,
    0x680076007363000000005d6e006a00695957000000526500005f005e,
    0x6b0000000a00000061000041000000435c0000550054000000494949490000848700000000000000,
    0x6f00006d00000066000062000000000000005a007800005100740000004e4a700000000000,
    0x624d0000495e0000000000005643000000405100000004000000004a00004a8300000000860000,
    0x8300000078800000000070007b000000000000000061007300000000006d59000055690000000000,
    0x46000000000c6b000000000063000042004300000000005700005452004b4b4b4b4b00000000007e,
    0x76008400006e006a0000000000005f7d0000005a000000000077000000004e740000480000,
    0x644f000000000000475b0000584400425641530000000008000000004c004c4c0000008100,
    0x82850000000000000000000071007c006c79000067007500006000720000000000000000000000,
    0x48000070000000180000006b0000000000430044000000005d005900005755004d4d4d4d4d000000,
    0x800000007600730084000000000000006500005e7e000000007a0000000000510050004a0000,
    0x5400695200660000004b6249005f00005a450043580000000000000010000000004e004e000000,
    0x7d00830078008100747f00000000000000000000000000000000005c006e000000,
    0x71003000000000006c00680044004500006300610000000000590000004f4f4f00,
    0x7b0075007200000000000000826500005e00007e5b0056007a5300000000004c,
    0x576d55006a00000000004d640000000000000000445a00000000000000002000000000000050,
    0x515100510000000000000000000077008000007000007c6b00796700007600600000735d006f,
    0x5500006f000000006e004d490000006600000000654300000000005b00000000050000000046004a,
    0x5c0000525200525200000000007a000083007400000080006b000000007b61000000000000760059,
    0x4e480000007877000000000d00000000407000000043006800004700000000004b005d0000,
    0x48004c0000535353530000007f00000000730000006a6984000000005f00000000005a00007d0000,
    0x570000000075000000724f0000000047006a00000000444200006500005f0000005e0a0000000000,
    0x600000005c00540054545400820000870000000000000000000068000000630000005d7c007900,
    0x4e7d0000460000000000000e77000000740000410000420000006c006b000049004b0000,
    0x6700610000600000555500555500810000000000006f0086000066006400000000005a5800000000,
    0x51000000504a7e000000007a0000001a000000000000410000000044700000004900006b00004d,
    0x5e005b00004a4c00000056565656568000000000006f006d0086000000000000005b0000560000,
    0x7b000055790000000000004f00000072000000006d00004400004100400000006200000c00,
    0x4d6b00000063000000605d5757005757570000007e000085000000710000000000678000610000,
    0x538200000050000000480000460000001c7a0000000077000000420044000000000000004b0000,
    0x18000062005f0000004c4e00000058585858580000007c00760000006a0000006500008400000000,
    0x7f00005c00000000540000000000750000000000007247000000450042004100000066640000,
    0x4f0000000068000000006361005900595959000000007d0000008500710000006c00000081,
    0x840000000000000051004a00004800007e0000380000007a0000007800430045000000740000004d,
    0x300000640000000000004e50000000005a5a5a00000000007b0000006e006900006500005e00,
    0x8100007f5c000000005400000052000076004b004900007300006f004300006d00006a00,
    0xd000000660000460000654c00000051000056005b5b005b5b000000000077000000700000836b,
    0x61600000008000005500000000007c7b4f000000000000000075004441006f000000000000,
    0x4700490071007000000000520054006700000000005c00005c5c0000007a0000000085006c00,
    0x6462860000005a580000000000004e00000000000000000f007d00000000400000410078007700,
    0x7700004d00005200000000700000576800000067005d5d00005d5d7f0000000000006d0000,
    0x5e00000000005384000000005048008200000000001d000000407e000000000044000047,
    0x720000000e000000000069000048004a000065000000535600005e005e5e5e0000790073006a00,
    0x870000006800000000005d000059000000008000004f4d000000007b007900000044000000400073,
    0x7500000000721a0000006e6a0000480000694e0000000053000058005f5f005f5f00007e00000000,
    0x870068000000630000000000000000005281007f004b000000470000000000454200000000,
    0x7a000000000000770000005400000055005700006c006b000067606060606060007d0000,
    0x6f000000640000005b00008600000000504c00000046000000001e8200000000004100004244,
    0x45007e00004900007a0000004f780055000000007400005971000000006c00006100006161007c00,
    0x7b000000000066006200005b00005600865100004a00000000000000003a00000000004100000000,
    0x4100004000000000001c0000007200006d00004a004e0000690066005600580000626200626262,
    0x6363000000780071000000000085006100005c8300000000000000000000497f000000007b004500,
    0x4500000000007d004b0000004f7a000000005700000000005974000000000000006c6863000063,
    0x64646400000075006e0000655f00000000005300000000004800008446003c000000000082000042,
    0x7c004200410000790000000038000000000000006f004c005000006d006a000058005a0000006400,
    0x65000065650000007700000000006700008560005c00000054000000000081000000007f470000,
    0x4400007c007b00000000000f007600750000004600480000006e0000000051005300000000005b5e,
    0x62666600006666007a00000000000087006300000000595700000000004f4d0000800000000000,
    0x454100000000000000007b1d000000000046000000754e006f000051000000006e5800005b0000,
    0x7000000067676700676700000074006c000000610000000085005400000083000049000000000081,
    0x400000414400820000004700000000007e000000000000005500005c00007700005d00607100,
    0x7100680000006868790000006d006400000000005600000000504c8600000000001f0000,
    0x4000840000000045004700000082000000004f52000000007e7d0000595d00000000000078000063,
    0x6e005e005f62006969696969690000720069005f5e000000530000000000480000000000003d00,
    0x83000045430000004000007f0000001e000000007b00000048004a4e000000730000007200000000,
    0x5a0000005f00000064006a00006a6a00007800000068000000000087005900005200000000000000,
    0x4700000000420000000000810000007f3a00000000007c0048000079500000007600530000000073,
    0x77007400000000706b006b00006b0077000000000000005d0000875700520000004b0000,
    0x168600000000000000438400000000004900004b4d00000000005400550000570000007a000060,
    0x7a000061006300000000740000716c006c6c6c6c76006f00000000005a0000005100500000004600,
    0x3e00008600004100004245000000000000000000004f82000054000000000000007d00600000,
    0x560000005a000073006f6200006400006d00006d6d6d750000006600005b5800000000004c000046,
    0x8549000000000083004100000040000080003c0000007f00000000004a005000000079000000,
    0x7600000075000000005f000065000066696e6e6e006e6e000000700067000000005c0000550000,
    0x87004b0000000000454300008300000000001f000081000000460000484e00000000007b51000000,
    0x7c5a00005b00000000000076640066000000006d6f0000006f6f0074000000630000005900000000,
    0x490000000000854100000000000000833d0000000046000000818050000000510000000000,
    0x5d0000007e00006700000000006b7800007700007000707000700000006b0060000000555400,
    0x504a0000000000170000400000004300860000000000494d0084000000520000005500005c0000,
    0x820000000000616700007e007d000068006c00007800000071007100717173006d0000005a000000,
    0x4c00000000003f000040000000414500008647000000004f000000000000000000005c0000,
    0x5300565800007b7900005e005f00620000750000690000007200720000727200000062005856,
    0x4f000047870045000000408500000016000000000000000000004c00000000007f,
    0x8000007f0000005a000000005e0000790000000000766900006a6d00730073737373007100680000,
    0x5d000000005200004d000000008743000040000000003e000000000083000048004a5000000000,
    0x840000000000006100006300006b0000006c000000007d00007a0000007874747400007400700000,
    0x6600000000514e00004600003600000000004345000000004900004b000086000054000000000059,
    0x53580081000000005b00005f007c00006500007b6600000000006e0000727500757500756e00,
    0x6c006300000000004f000000000045420000008700001700008500460000004c00000000000000,
    0x51000000005a0000008100800000000000006500007c000000006a006e0000006f73760076007676,
    0x6b000000570000004d4b00000000430000000000873f000000004600000048500000000083,
    0x5c8600005d0000600084000067000000006b00820000000070000000007d000000000077000077,
    0x787800786a0064005a00005000000000130000000000420000470000004b00000000520000545700,
    0x595c000000860000000061000000840000006800007000000071000000000074007e007d00007878,
    0x7979790000796900620000004e4a0000003700004000004345000000000049000000005200000000,
    0x850000530056000000000000005e000000006400008000007f00006a006d00007c720073000000,
    0x7e007a0000007a0067005d00000000000047000044004000000036000000000087004c50000000,
    0x5900000000600061000063000086006b006c00000000008400000074000000000000820000000000,
    0x7500007b00007b000065005b00510046002600000000004400000000004d4f0000000055000057,
    0x51870000560000850000005b00005e62008300006500006600690080000000006e00000072000000,
    0x7500760000797c7c7c7c007c00610059004f00000000450000000000130000000000004a00000000,
    0x87530000000000855b00000000640000650000000000006a00000081000000806f000000,
    0x82000000007d7d007d0000006000570000000000444200000000370000004600004c500000,
    0x54005c00000000000000630000000000006800006c00000000718600000074770000840000780000,
    0x7a000000820000007e007e007e5f0058004e0000330000004245004700004b000052000000,
    0x55590000005d0000006100670000000068000000007000710000008600000000007800008400,
    0x81007900000000007f0000007f5e0056004a0027004000004400000000004d4f000000,
    0x585a000000000087005f00626400000000850069006a006d000000830072007300,
    0x7600000079007b00007c0000808000800000005c00520047000000400000002600000000004e,
    0x51000056000000005b0000005e00000000650000008700006d000000850000006f007300000083,
    0x75007600008300000000007c0000007f0081008100810055004d00440000000033000000004a5000,
    0x585a000000000000005f640000000000660000876a0000006e0000856f0000000000,
    0x7a00007d0000007e860000000000840000000082828200000054004b00420000002700000046004e,
    0x5700005d0000006063670000006800006c0000007100000000000000770000000000000000,
    0x870000007b000085000000007f0000800081000000838383000053004c0023004244470000004f00,
    0x5100005a0000000000620000000066000000696d0000006e00006f000073000000000076000000,
    0x820000000000000000000086000000840084000049004300230000004a4e00,
    0x5759005d0000006300006800006b007000000000000074007700780000000000007a00007d007e,
    0x7c000000007f00000000800081000087000000008300000000008500850048002b0043004b4d5200,
    0x565800005b0062640000660000006d000000006f00007200000000750000000000790000007b00,
    0x82000000000000000000008400000000000000000000000086000041002b004c0000,
    0x54555c00006061006700006b6c0070710000007400000077780000007a00000000007d7e00000000,
    0x80810000000000000000000083000000000000008500000000008700290041004900,
    0x530000005e5f00006500696a00006e0000727300000075760000007900000000007b7c0000007f,
    0x290048
  ]

@[expose, irreducible] def formBits : ℕ := Nat.ofDigits (2 ^ 320) [
    0x28000000000000000000580000000000000000009000000000000000000200000000000000000004,
    0x1000000000000000000010000000000000000000004000000000000000000,
    0x4000000000000001000000000000000000010000000000000000000100000000000000000001,
    0x100000000000000080000000000000000000000080000000000000020000000000000000000,
    0x4000000000000010000000000000000000000002000000000000004000000000000000000,
    0x20000000000000000000000008000000000000000000080000000000000400000000000000000,
    0x20000000000000080000000000000000001000000000000000000000000200000000000,
    0x2000000000000010000000000000000000000000800000000000004000000000000000,
    0x400000000000000400000000000000000008000000000000000000000004000000000,
    0x20000000000000040000000000000000000800000000000000000000000200000000,
    0x8000000000000000000100000000000000000000800000000000002000000000000,
    0x800000000000000000010000000000000002000000000000000000040000000000,
    0x200000000000000000000800000000000000200000000000000000004000000000,
    0x20000000000000000400000000000000000008000000000000000000000100000,
    0x8000000000000000000100000000000000000800000000000000000000010000,
    0x200000000000000000000010000000000000000040000000000000000000800000,
    0x8000000000000000000100000000000000000000040000000000000000000800,
    0x200000000000000000000400000000000000000008000000000000000000040,
    0x20000000000000000000100000000000000000008000000000000000000040,
    0x4
  ]

@[expose] def code (a b : ℕ) : ℕ :=
  (bracketCodes >>> (8 * (78 * a + b))) % 256

@[expose] def maskOf (e : ℕ) : ℕ :=
  if e < 64 then e else 1 <<< (e - 58)

@[expose] def idxOf (e : ℕ) : List ℕ :=
  if e < 64 then (List.range 6).filter fun i => e.testBit i else [e - 58]

@[expose] def brMask (a b : ℕ) : ℕ :=
  maskOf (code a b)

@[expose] def brIdx (a b : ℕ) : List ℕ :=
  idxOf (code a b)

@[expose] def fbit (a b : ℕ) : Bool :=
  formBits.testBit (78 * a + b)

@[expose] def xorMap (f : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | l :: L => f l ^^^ xorMap f L

@[expose] def xorBits (g : ℕ → Bool) : List ℕ → Bool
  | [] => false
  | l :: L => g l ^^ xorBits g L

@[expose] def entryOK (a b : ℕ) : Bool :=
  if ha : a < 6 then
    if b < 6 then code a b == 0
    else code a b ==
      if cartanPair ⟨a, ha⟩ (e6Certificate.root (b - 6)) % 2 == 0 then 0 else b + 58
  else if hb : b < 6 then
    code a b == if cartanPair ⟨b, hb⟩ (e6Certificate.root (a - 6)) % 2 == 0 then 0 else a + 58
  else
    if List.ofFn (e6Certificate.root (b - 6)) == List.ofFn (-e6Certificate.root (a - 6)) then
      decide (code a b < 64) && (List.finRange Tag.E6.rank).all fun i =>
        (code a b).testBit i == (e6Certificate.root (a - 6) i % 2 != 0)
    else if 64 ≤ code a b then
      List.ofFn (e6Certificate.root (code a b - 64)) ==
        List.ofFn (e6Certificate.root (a - 6) + e6Certificate.root (b - 6))
    else code a b == 0 &&
      cartanForm (e6Certificate.root (a - 6) + e6Certificate.root (b - 6))
        (e6Certificate.root (a - 6) + e6Certificate.root (b - 6)) != 2

@[expose] def formOK (a b : ℕ) : Bool :=
  if ha : a < 6 then
    if hb : b < 6 then fbit a b == (Tag.E6.cartan ⟨a, ha⟩ ⟨b, hb⟩ % 2 != 0)
    else fbit a b == false
  else if b < 6 then fbit a b == false
  else fbit a b ==
    (List.ofFn (e6Certificate.root (b - 6)) == List.ofFn (-e6Certificate.root (a - 6)))

@[expose] def allEntriesOK : Bool :=
  (List.range 78).all fun a => (List.range 78).all fun b =>
    decide (code a b < 136) && entryOK a b && formOK a b

theorem allEntriesOK_eq_true : allEntriesOK = true := by
  decide +kernel

@[expose] def jacOK (a b c : ℕ) : Bool :=
  (xorMap (brMask a) (brIdx b c) ^^^ xorMap (brMask b) (brIdx c a) ^^^
    xorMap (brMask c) (brIdx a b)) == 0

@[expose] def jacRows (lo n : ℕ) : Bool :=
  (List.range n).all fun i => (List.range 78).all fun b => (List.range 78).all fun c =>
    jacOK (lo + i) b c

@[expose] def invOK (a b c : ℕ) : Bool :=
  xorBits (fun l => fbit l c) (brIdx a b) == xorBits (fbit a) (brIdx b c)

@[expose] def invRows (lo n : ℕ) : Bool :=
  (List.range n).all fun i => (List.range 78).all fun b => (List.range 78).all fun c =>
    invOK (lo + i) b c

@[expose] def genOK (A x y : ℕ) : Bool :=
  (if xorBits (fbit A) (brIdx x y) then 1 <<< A else 0) ==
    ((if fbit A x then brMask A y else 0) ^^^
      xorMap (fun l => xorMap (brMask l) (brIdx A y)) (brIdx A x) ^^^
      (if fbit A y then brMask x A else 0))

@[expose] def adSqOK (A x : ℕ) : Bool :=
  xorMap (brMask A) (brIdx A x) == 0

@[expose] def simpleIdx : List ℕ :=
  [6, 7, 8, 9, 10, 11, 12, 14, 16, 18, 20, 22]

@[expose] def genRows (A : ℕ) : Bool :=
  (List.range 78).all fun x => adSqOK A x && (List.range 78).all fun y => genOK A x y

theorem entries_ok (a b : Fin 78) :
    code a b < 136 ∧ entryOK a b = true ∧ formOK a b = true := by
  have h := allEntriesOK_eq_true
  simp only [allEntriesOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h a a.2 b b.2
  exact ⟨h1, h2, h3⟩

theorem maskOf_of_ge {e : ℕ} (h : ¬e < 64) : maskOf e = 1 <<< (e - 58) := by
  rw [maskOf, ite_eq_right h]

theorem toVec_maskOf_add (b : Fin 78) (hb : ¬(b : ℕ) < 6) :
    toVec R (maskOf (b + 58)) = Finsupp.single (lab b) 1 := by
  rw [maskOf_of_ge (by omega), Nat.add_sub_cancel, toVec_one_shiftLeft]

section CharTwo

variable [CharP R 2]

theorem intCast_eq_ite_emod (n : ℤ) : (n : R) = if n % 2 = 0 then 0 else 1 := by
  rw [CharTwo.intCast_eq_ite]
  by_cases h : n % 2 = 0
  · rw [ite_eq_left (Int.even_iff.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt Int.even_iff.1 h), ite_eq_right h]

theorem bracket_lab (a b : Fin 78) :
    bracket R (Finsupp.single (lab a) 1) (Finsupp.single (lab b) 1) = toVec R (brMask a b) := by
  obtain ⟨hc, h, -⟩ := entries_ok a b
  rw [bracket_single]
  unfold entryOK at h
  by_cases ha : (a : ℕ) < 6 <;> by_cases hb : (b : ℕ) < 6
  · simp only [ha, hb, ↓reduceDIte, ↓reduceIte, beq_iff_eq] at h
    rw [lab_of_lt ha, lab_of_lt hb]
    simp [bracketLabel, brMask, h, maskOf, toVec_zero]
  · simp only [ha, hb, ↓reduceDIte, ↓reduceIte, beq_iff_eq] at h
    rw [lab_of_lt ha, lab_of_ge hb]
    simp only [bracketLabel]
    rw [intCast_eq_ite_emod, rootVec_eq_single (isRoot_certRoot (by omega))]
    by_cases hev : cartanPair ⟨a, ha⟩ (e6Certificate.root (b - 6)) % 2 = 0
    · simp only [hev, ↓reduceIte] at h
      simp [hev, brMask, h, maskOf, toVec_zero]
    · simp only [hev, ↓reduceIte] at h
      rw [brMask, h, toVec_maskOf_add b hb, lab_of_ge hb, ite_eq_right hev, one_smul]
  · simp only [ha, hb, ↓reduceDIte, beq_iff_eq] at h
    rw [lab_of_ge ha, lab_of_lt hb]
    simp only [bracketLabel]
    rw [intCast_eq_ite_emod, rootVec_eq_single (isRoot_certRoot (by omega))]
    by_cases hev : cartanPair ⟨b, hb⟩ (e6Certificate.root (a - 6)) % 2 = 0
    · simp only [hev, ↓reduceIte] at h
      simp [hev, brMask, h, maskOf, toVec_zero]
    · simp only [hev, ↓reduceIte] at h
      rw [brMask, h, toVec_maskOf_add a ha, lab_of_ge ha, ite_eq_right hev, one_smul]
  · simp only [ha, hb, ↓reduceDIte] at h
    rw [lab_of_ge ha, lab_of_ge hb]
    simp only [bracketLabel]
    by_cases hneg : e6Certificate.root (b - 6) = -e6Certificate.root (a - 6)
    · have hbeq : (List.ofFn (e6Certificate.root (b - 6)) ==
          List.ofFn (-e6Certificate.root (a - 6))) = true := by
        rw [hneg]
        exact beq_self_eq_true _
      simp only [hbeq, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_finRange, true_implies, beq_iff_eq] at h
      obtain ⟨hlt, hbits⟩ := h
      rw [ite_eq_left hneg, brMask, maskOf, ite_eq_left hlt, toVec_of_lt hlt]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intCast_eq_ite_emod, hbits i]
      by_cases h0 : e6Certificate.root (a - 6) i % 2 = 0 <;> simp [h0]
    · have hbeq : (List.ofFn (e6Certificate.root (b - 6)) ==
          List.ofFn (-e6Certificate.root (a - 6))) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h' => hneg (List.ofFn_injective h')
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h
      rw [ite_eq_right hneg]
      by_cases h64 : 64 ≤ code a b
      · simp only [h64, ↓reduceIte] at h
        have hsum := RootCertificate.eq_of_ofFn_beq h
        have hr : IsRoot Tag.E6 (e6Certificate.root (a - 6) + e6Certificate.root (b - 6)) :=
          hsum ▸ isRoot_certRoot (by omega)
        have hk : code a b - 58 < 78 := by omega
        have hlab : lab ⟨code a b - 58, hk⟩ = Sum.inr ⟨_, hr⟩ := by
          rw [lab_of_ge (by simp only; omega)]
          simp only [Sum.inr.injEq, Subtype.mk.injEq]
          rw [show code a b - 58 - 6 = code a b - 64 by omega]
          exact hsum
        rw [rootVec_eq_single hr, brMask, maskOf_of_ge (by omega), toVec_one_shiftLeft' hk, hlab]
      · simp only [h64, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
        obtain ⟨h0, hn⟩ := h
        rw [rootVec_eq_zero (fun hr => hn (cartanForm_self_of_isRoot hr)), brMask, h0]
        simp [maskOf, toVec_zero]

theorem form_lab (a b : Fin 78) :
    form R (Finsupp.single (lab a) 1) (Finsupp.single (lab b) 1) = if fbit a b then 1 else 0 := by
  obtain ⟨-, -, h⟩ := entries_ok a b
  rw [form_single]
  unfold formOK at h
  by_cases ha : (a : ℕ) < 6 <;> by_cases hb : (b : ℕ) < 6
  · simp only [ha, hb, ↓reduceDIte, beq_iff_eq] at h
    rw [lab_of_lt ha, lab_of_lt hb, h]
    simp only [formLabel]
    rw [intCast_eq_ite_emod]
    by_cases h0 : Tag.E6.cartan ⟨a, ha⟩ ⟨b, hb⟩ % 2 = 0 <;> simp [h0]
  · simp only [ha, hb, ↓reduceDIte, beq_iff_eq] at h
    rw [lab_of_lt ha, lab_of_ge hb, h]
    simp [formLabel]
  · simp only [ha, hb, ↓reduceDIte, ↓reduceIte, beq_iff_eq] at h
    rw [lab_of_ge ha, lab_of_lt hb, h]
    simp [formLabel]
  · simp only [ha, hb, ↓reduceDIte, ↓reduceIte, beq_iff_eq] at h
    rw [lab_of_ge ha, lab_of_ge hb, h]
    simp only [formLabel]
    by_cases hneg : e6Certificate.root (b - 6) = -e6Certificate.root (a - 6)
    · simp [hneg]
    · simp [hneg]

end CharTwo

theorem toVec_xorMap [CharP R 2] (f : ℕ → ℕ) (L : List ℕ) :
    toVec R (xorMap f L) = (L.map fun l => toVec R (f l)).sum := by
  induction L with
  | nil => simp [xorMap, toVec_zero]
  | cons l L ih => rw [xorMap, toVec_xor, ih, List.map_cons, List.sum_cons]

theorem xorBits_ite [CharP R 2] (g : ℕ → Bool) (L : List ℕ) :
    (if xorBits g L then (1 : R) else 0) = (L.map fun l => if g l then (1 : R) else 0).sum := by
  induction L with
  | nil => simp [xorBits]
  | cons l L ih =>
    rw [xorBits, List.map_cons, List.sum_cons, ← ih]
    cases g l <;> cases xorBits g L <;> simp [CharTwo.add_self_eq_zero]

theorem idxOf_lt {e : ℕ} (he : e < 136) : ∀ l ∈ idxOf e, l < 78 := by
  intro l hl
  unfold idxOf at hl
  split_ifs at hl with h
  · simp only [List.mem_filter, List.mem_range] at hl
    omega
  · simp only [List.mem_singleton] at hl
    omega

theorem xorMap_idxOf : ∀ e < 64, xorMap (fun l => 1 <<< l) (idxOf e) = e := by
  decide

theorem toVec_maskOf [CharP R 2] (e : ℕ) :
    toVec R (maskOf e) = lvec R (idxOf e) := by
  by_cases h : e < 64
  · rw [lvec, ← toVec_xorMap, xorMap_idxOf e h, maskOf, ite_eq_left h]
  · rw [maskOf_of_ge h, idxOf, ite_eq_right h, lvec]
    simp

theorem toVec_brMask
    [CharP R 2] (a b : Fin 78) : toVec R (brMask a b) = lvec R (brIdx a b) :=
  toVec_maskOf _

theorem brIdx_lt (a b : Fin 78) : ∀ l ∈ brIdx a b, l < 78 :=
  idxOf_lt (entries_ok a b).1

theorem lvec_cons
    (l : ℕ) (L : List ℕ) : lvec R (l :: L) = toVec R (1 <<< l) + lvec R L := by
  simp [lvec]

theorem lvec_nil : lvec R [] = 0 := by
  simp [lvec]

section CharTwo

variable [CharP R 2]

theorem bracket_lab_lvec
    (a : Fin 78) {L : List ℕ} (hL : ∀ l ∈ L, l < 78) :
    bracket R (Finsupp.single (lab a) 1) (lvec R L) = toVec R (xorMap (brMask a) L) := by
  rw [toVec_xorMap]
  induction L with
  | nil => simp [lvec_nil]
  | cons l L ih =>
    have hl : l < 78 := hL l List.mem_cons_self
    rw [lvec_cons, map_add, ih fun l' h' => hL l' (List.mem_cons_of_mem _ h'),
      toVec_one_shiftLeft' hl, bracket_lab, List.map_cons, List.sum_cons]

theorem bracket_lvec_lab
    (c : Fin 78) {L : List ℕ} (hL : ∀ l ∈ L, l < 78) :
    bracket R (lvec R L) (Finsupp.single (lab c) 1) =
      toVec R (xorMap (fun l => brMask l c) L) := by
  rw [toVec_xorMap]
  induction L with
  | nil => simp [lvec_nil]
  | cons l L ih =>
    have hl : l < 78 := hL l List.mem_cons_self
    rw [lvec_cons, map_add, LinearMap.add_apply, ih fun l' h' => hL l' (List.mem_cons_of_mem _ h'),
      toVec_one_shiftLeft' hl, bracket_lab, List.map_cons, List.sum_cons]

theorem form_lab_lvec
    (a : Fin 78) {L : List ℕ} (hL : ∀ l ∈ L, l < 78) :
    form R (Finsupp.single (lab a) 1) (lvec R L) = if xorBits (fbit a) L then 1 else 0 := by
  rw [xorBits_ite]
  induction L with
  | nil => simp [lvec_nil]
  | cons l L ih =>
    have hl : l < 78 := hL l List.mem_cons_self
    rw [lvec_cons, map_add, ih fun l' h' => hL l' (List.mem_cons_of_mem _ h'),
      toVec_one_shiftLeft' hl, form_lab, List.map_cons, List.sum_cons]

theorem form_lvec_lab
    (c : Fin 78) {L : List ℕ} (hL : ∀ l ∈ L, l < 78) :
    form R (lvec R L) (Finsupp.single (lab c) 1) =
      if xorBits (fun l => fbit l c) L then 1 else 0 := by
  rw [xorBits_ite]
  induction L with
  | nil => simp [lvec_nil]
  | cons l L ih =>
    have hl : l < 78 := hL l List.mem_cons_self
    rw [lvec_cons, map_add, LinearMap.add_apply, ih fun l' h' => hL l' (List.mem_cons_of_mem _ h'),
      toVec_one_shiftLeft' hl, form_lab, List.map_cons, List.sum_cons]

theorem bracket_lab_bracket_lab
    (a b c : Fin 78) :
    bracket R (Finsupp.single (lab a) 1)
        (bracket R (Finsupp.single (lab b) 1) (Finsupp.single (lab c) 1)) =
      toVec R (xorMap (brMask a) (brIdx b c)) := by
  rw [bracket_lab, toVec_brMask, bracket_lab_lvec a (brIdx_lt b c)]

theorem jacobi_lab
    {a b c : Fin 78} (h : jacOK a b c = true) :
    bracket R (Finsupp.single (lab a) 1)
        (bracket R (Finsupp.single (lab b) 1) (Finsupp.single (lab c) 1)) +
      bracket R (Finsupp.single (lab b) 1)
        (bracket R (Finsupp.single (lab c) 1) (Finsupp.single (lab a) 1)) +
      bracket R (Finsupp.single (lab c) 1)
        (bracket R (Finsupp.single (lab a) 1) (Finsupp.single (lab b) 1)) = 0 := by
  rw [bracket_lab_bracket_lab, bracket_lab_bracket_lab, bracket_lab_bracket_lab, ← toVec_xor,
    ← toVec_xor]
  rw [jacOK, beq_iff_eq] at h
  rw [h, toVec_zero]

theorem invariant_lab
    {a b c : Fin 78} (h : invOK a b c = true) :
    form R (bracket R (Finsupp.single (lab a) 1) (Finsupp.single (lab b) 1))
        (Finsupp.single (lab c) 1) =
      form R (Finsupp.single (lab a) 1)
        (bracket R (Finsupp.single (lab b) 1) (Finsupp.single (lab c) 1)) := by
  rw [bracket_lab, bracket_lab, toVec_brMask, toVec_brMask, form_lvec_lab c (brIdx_lt a b),
    form_lab_lvec a (brIdx_lt b c)]
  rw [invOK, beq_iff_eq] at h
  rw [h]

theorem adSq_lab
    {A x : Fin 78} (h : adSqOK A x = true) :
    bracket R (Finsupp.single (lab A) 1)
      (bracket R (Finsupp.single (lab A) 1) (Finsupp.single (lab x) 1)) = 0 := by
  rw [bracket_lab_bracket_lab]
  rw [adSqOK, beq_iff_eq] at h
  rw [h, toVec_zero]

omit [CharP R 2] in
theorem toVec_ite (p : Bool) (m : ℕ) :
    toVec R (if p then m else 0) = (if p then (1 : R) else 0) • toVec R m := by
  cases p <;> simp [toVec_zero]

theorem gen_lab
    {A x y : Fin 78} (h : genOK A x y = true) :
    form R (Finsupp.single (lab A) 1)
        (bracket R (Finsupp.single (lab x) 1) (Finsupp.single (lab y) 1)) •
        Finsupp.single (lab A) 1 =
      form R (Finsupp.single (lab A) 1) (Finsupp.single (lab x) 1) •
          bracket R (Finsupp.single (lab A) 1) (Finsupp.single (lab y) 1) +
        bracket R (bracket R (Finsupp.single (lab A) 1) (Finsupp.single (lab x) 1))
          (bracket R (Finsupp.single (lab A) 1) (Finsupp.single (lab y) 1)) +
        form R (Finsupp.single (lab A) 1) (Finsupp.single (lab y) 1) •
          bracket R (Finsupp.single (lab x) 1) (Finsupp.single (lab A) 1) := by
  have hDD : bracket R (bracket R (Finsupp.single (lab A) 1) (Finsupp.single (lab x) 1))
      (bracket R (Finsupp.single (lab A) 1) (Finsupp.single (lab y) 1)) =
      toVec R (xorMap (fun l => xorMap (brMask l) (brIdx A y)) (brIdx A x)) := by
    rw [bracket_lab A x, toVec_brMask, bracket_lab A y, toVec_brMask, toVec_xorMap]
    have hx := brIdx_lt A x
    generalize brIdx A x = L at hx ⊢
    induction L with
    | nil => simp [lvec_nil]
    | cons l L ih =>
      have hl : l < 78 := hx l List.mem_cons_self
      rw [lvec_cons, map_add, LinearMap.add_apply,
        ih fun l' h' => hx l' (List.mem_cons_of_mem _ h'), toVec_one_shiftLeft' hl,
        bracket_lab_lvec _ (brIdx_lt A y), List.map_cons, List.sum_cons]
  rw [genOK, beq_iff_eq] at h
  rw [hDD, bracket_lab x y, toVec_brMask x y, form_lab_lvec A (brIdx_lt x y), form_lab A x,
    form_lab A y, bracket_lab A y, bracket_lab x A, ← toVec_ite, ← toVec_ite,
    ← toVec_one_shiftLeft A, ← toVec_ite, ← toVec_xor, ← toVec_xor, h]

end CharTwo

end CFSG.Monster.B.Classical.E6Adjoint
