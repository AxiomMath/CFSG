module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Quasithin.Recognition.CertU33PresInputs
public import CFSG.Quasithin.Recognition.CertU33DcInputs
public import CFSG.Quasithin.Recognition.CertPermList

public section

namespace CFSG.ASVolI

open CFSG.CosetTable CFSG.Quasithin

@[expose] def burnsideF48s_invW {m : ℕ} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def burnsideF48s_g2dAmal : List (List (Fin 5 × Bool)) :=
  ["aaaa", "bbbb", "ss", "ABab", "sasB", "sbsA", "xxx", "XaxB", "Xbxba", "xsxs", "yyy",
    "Yabsysaa", "YsaaybA", "Asysay"].map u33Word

@[expose] def burnsideF48s_g2dCandV : List String := ["Xs", "Xaas", "Xabbs", "XbbsB"]

@[expose] def burnsideF48s_g2dRelW (j : ℕ) : List (Fin 5 × Bool) :=
  u33Word "Xs" ++ u33Word "Y" ++ u33Word (burnsideF48s_g2dCandV.getD j "") ++
    burnsideF48s_invW (u33Word "Y")

@[expose] def burnsideF48s_g2dCand (j : ℕ) : List (Fin 5 × Bool) :=
  (List.replicate 3 (burnsideF48s_g2dRelW j)).flatten

@[expose] def burnsideF48s_g2dWs (j : ℕ) : List (List (Fin 5 × Bool)) :=
  burnsideF48s_g2dAmal ++ [burnsideF48s_g2dCand j]

abbrev burnsideF48s_g2dWsB (j : ℕ) :=
  restrictWords (subsetOf 5 [0, 1, 2, 4]) (burnsideF48s_g2dWs j)

@[expose] def burnsideF48s_g2dTelF (i : ℕ) : List (Fin 5 × Bool) := u33Word (u33TelWords.getD i "")

@[expose] def burnsideF48s_g2dApairs : List (ℕ × ℕ) :=
  [(0, 5), (0, 18), (0, 29), (0, 30), (5, 0), (5, 8), (5, 19), (5, 22), (0, 0), (0, 1), (0, 2),
    (0, 3), (0, 4), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14),
    (0, 15), (0, 16), (0, 17), (0, 19), (0, 20), (0, 21), (0, 22), (0, 23), (0, 24), (0, 25),
    (0, 26), (0, 27), (0, 28), (0, 31), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7),
    (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18),
    (5, 20), (5, 21), (5, 23), (5, 24), (5, 25), (5, 26), (5, 27), (5, 28), (5, 29), (5, 30),
    (5, 31)]

@[expose] def burnsideF48s_g2dBpairs : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10),
    (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (0, 18), (0, 19), (0, 20),
    (0, 21), (0, 22), (0, 23), (0, 24), (0, 25), (0, 26), (0, 27), (0, 28), (0, 29), (0, 30),
    (0, 31), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9),
    (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (1, 18), (1, 19),
    (1, 20), (1, 21), (1, 22), (1, 23), (1, 24), (1, 25), (1, 26), (1, 27), (1, 28), (1, 29),
    (1, 30), (1, 31)]

@[expose] def burnsideF48s_g2dAF (k : ℕ) : List (Fin 5 × Bool) :=
  burnsideF48s_g2dTelF (burnsideF48s_g2dApairs.getD k (0, 0)).1 ++ u33Word "X" ++
    burnsideF48s_g2dTelF (burnsideF48s_g2dApairs.getD k (0, 0)).2

@[expose] def burnsideF48s_g2dBF (k : ℕ) : List (Fin 5 × Bool) :=
  burnsideF48s_g2dTelF (burnsideF48s_g2dBpairs.getD k (0, 0)).1 ++ u33Word "Y" ++
    burnsideF48s_g2dTelF (burnsideF48s_g2dBpairs.getD k (0, 0)).2

@[expose] def burnsideF48s_g2dGL : List (List ℕ) :=
  [[14, 20, 27, 6, 7, 5, 16, 19, 18, 1, 4, 2, 12, 15, 13, 0, 26, 17, 23, 10, 25, 8, 11, 21, 24, 9, 3, 22],
    [7, 18, 11, 3, 25, 24, 6, 9, 0, 8, 20, 22, 17, 10, 19, 4, 16, 5, 14, 1, 23, 15, 27, 13, 12, 21, 26, 2],
    [0, 10, 11, 12, 18, 16, 17, 14, 15, 13, 1, 2, 3, 9, 7, 8, 5, 6, 4, 19, 20, 21, 27, 25, 26, 23, 24, 22],
    [1, 10, 26, 24, 21, 22, 5, 20, 9, 25, 0, 3, 2, 15, 7, 23, 17, 27, 4, 19, 14, 18, 6, 13, 11, 8, 12, 16],
    [12, 13, 27, 7, 16, 8, 1, 18, 20, 26, 0, 11, 10, 6, 21, 9, 23, 25, 3, 17, 5, 24, 2, 4, 14, 19, 15, 22]]

@[expose] def burnsideF48s_g2dGLi : List (List ℕ) :=
  [[15, 9, 11, 26, 10, 5, 3, 4, 21, 25, 19, 22, 12, 14, 0, 13, 6, 17, 8, 7, 1, 23, 27, 18, 24, 20, 16, 2],
    [8, 19, 27, 3, 15, 17, 6, 0, 9, 7, 13, 2, 24, 23, 18, 21, 16, 12, 1, 14, 10, 25, 11, 20, 5, 4, 26, 22],
    [0, 10, 11, 12, 18, 16, 17, 14, 15, 13, 1, 2, 3, 9, 7, 8, 5, 6, 4, 19, 20, 21, 27, 25, 26, 23, 24, 22],
    [10, 0, 12, 11, 18, 6, 22, 14, 25, 8, 1, 24, 26, 23, 20, 13, 27, 16, 21, 19, 7, 4, 5, 15, 3, 9, 2, 17],
    [10, 6, 22, 18, 23, 20, 13, 3, 5, 15, 12, 11, 0, 1, 24, 26, 4, 19, 7, 25, 8, 14, 27, 16, 21, 17, 9, 2]]

@[expose] def burnsideF48s_g2dLetL (l : Fin 5 × Bool) : List ℕ :=
  (if l.2 then burnsideF48s_g2dGL else burnsideF48s_g2dGLi).getD l.1 []

@[expose] def burnsideF48s_g2dEvL (w : List (Fin 5 × Bool)) : List ℕ :=
  w.foldl (fun acc l => compL acc (burnsideF48s_g2dLetL l)) (List.range 28)

@[expose] def burnsideF48s_g2dTab : String :=
  "0001002003002cp3cp1cp0cp2033031030032ce3ce1ce0ce0041042043041cf0cf3cf2cf3012010011012cs3cs1cs0cs\
    0021022023020cu1cu2cu3cu2c93c91c90c90051052053052093091090091c50c53c52c530b20b00b10b1ci0ci3ci2ci\
    1080083082082cl3cl1cl0cl3062060061060cv1cv2cv3cv2c33c31c30c330e20e00e10e2073071070070cn1cn2cn3cn\
    00c10c20c30c3co2co0co1co0c41c42c43c400f10f20f30f1ch0ch3ch2ch00a10a20a30a2cj3cj1cj0cj20d30d10d00d\
    10h00h30h20h1ca0ca3ca2ca10g00g30g20g0ct1ct2ct3ct2c73c71c70c710n00n30n20n30m20m00m10m3cr2cr0cr1cr\
    0c01c02c03c030p20p00p10p1c80c83c82c830l20l00l10l20j30j10j00j3cd2cd0cd1cd3cb2cb0cb1cb00i10i20i30i\
    0cc1cc2cc3cc20o30o10o00o1cq0cq3cq2cq20k30k10k00k10q00q30q20q3ck2ck0ck1ck0c21c22c23c210u00u30u20u\
    1cg0cg3cg2cg10t00t30t20t3c12c10c11c130s20s00s10s3cm2cm0cm1cm20r30r10r00r3c62c60c61c610v00v30v20v\
    22332312302314e04e34e24e12802832822814l04l34l24l22932912902934524504514502012022032014p04p34p24p\
    22732712702724n34n14n04n14h04h34h24h22a32a12a02a12h02h32h22h34a24a04a14a02412422432434f24f04f14f\
    32122102112114s04s34s24s02212222232224u34u14u04u14804834824802l12l22l32l12g02g32g22g24t34t14t04t\
    22j32j12j02j04d14d24d34d24934914904922532512502534b24b04b14b22i32i12i02i14q04q34q24q12k02k32k22k\
    32b22b02b12b34i24i04i14i32622602612624v34v14v04v14g04g34g24g32t22t02t12t02c12c22c32c04o14o24o34o\
    24334314304302e12e22e32e34124104114102s12s22s32s12q02q32q22q04k14k24k34k04414424434422f32f12f02f\
    24j34j14j04j12d02d32d22d34m24m04m14m12r02r32r22r32m22m02m12m04r14r24r34r24734714704732n22n02n12n\
    34624604614632v22v02v12v04014024034002p12p22p32p04c14c24c34c12o02o32o22o04214224234232u22u02u12u\
    1q00q03q02q038p28p08p18p3q32q30q31q338e28e08e18e1q40q43q42q408f18f28f38f2q13q11q10q138s28s08s18s\
    1q20q23q22q218u08u38u28u3892890891891q50q53q52q53q92q90q91q90851852853852qb3qb1qb0qb08i18i28i38i\
    0q81q82q83q838l28l08l18l2q63q61q60q618v08v38v28v3832830831832qe3qe1qe0qe3q72q70q71q718n08n38n28n\
    1qc0qc3qc2qc28o38o18o08o1840843842841qf0qf3qf2qf08h18h28h38h1qa0qa3qa2qa38j28j08j18j3qd2qd0qd1qd\
    0qh1qh2qh3qh08a18a28a38a0qg1qg2qg3qg18t08t38t28t3872870871870qn1qn2qn3qn2qm3qm1qm0qm28r38r18r08r\
    1800803802802qp3qp1qp0qp0881882883882ql3ql1ql0ql3qj2qj0qj1qj28d38d18d08d28b38b18b08b1qi0qi3qi2qi\
    18c08c38c28c3qo2qo0qo1qo08q18q28q38q3qk2qk0qk1qk0qq1qq2qq3qq28k38k18k08k1820823822820qu1qu2qu3qu\
    08g18g28g38g0qt1qt2qt3qt2813811810812qs3qs1qs0qs28m38m18m08m3qr2qr0qr1qr2863861860860qv1qv2qv3qv\
    3h32h30h31h30ge1ge2ge3ge0h81h82h83h80gl1gl2gl3gl3h92h90h91h92g53g51g50g51h00h03h02h00gp1gp2gp3gp\
    3h72h70h71h73gn2gn0gn1gn0gh1gh2gh3gh3ha2ha0ha1ha0hh1hh2hh3hh2ga3ga1ga0ga1h40h43h42h42gf3gf1gf0gf\
    2h13h11h10h10gs1gs2gs3gs1h20h23h22h23gu2gu0gu1gu0g81g82g83g81hl0hl3hl2hl0hg1hg2hg3hg3gt2gt0gt1gt\
    3hj2hj0hj1hj1gd0gd3gd2gd3g92g90g91g93h52h50h51h52gb3gb1gb0gb3hi2hi0hi1hi0gq1gq2gq3gq0hk1hk2hk3hk\
    2hb3hb1hb0hb2gi3gi1gi0gi2h63h61h60h63gv2gv0gv1gv0gg1gg2gg3gg2ht3ht1ht0ht1hc0hc3hc2hc1go0go3go2go\
    3g32g30g31g31he0he3he2he2g13g11g10g11hs0hs3hs2hs0hq1hq2hq3hq1gk0gk3gk2gk1g40g43g42g43hf2hf0hf1hf\
    3gj2gj0gj1gj0hd1hd2hd3hd2gm3gm1gm0gm0hr1hr2hr3hr2hm3hm1hm0hm1gr0gr3gr2gr3g72g70g71g72hn3hn1hn0hn\
    2g63g61g60g62hv3hv1hv0hv1g00g03g02g01hp0hp3hp2hp1gc0gc3gc2gc0ho1ho2ho3ho1g20g23g22g22hu3hu1hu0hu\
    39029009019007p17p27p37p09319329339307e17e27e37e39429409419427f37f17f07f19109139129107s17s27s37s\
    39229209219237u27u07u17u07917927937939529509519509919929939927537517507519b09b39b29b27i37i17i07i\
    29839819809807l17l27l37l19609639629637v27v07v17v07317327337319e09e39e29e09719729739737n27n07n17n\
    39c29c09c19c17o07o37o27o37427407417439f29f09f19f27h37h17h07h39a29a09a19a07j17j27j37j09d19d29d39d\
    29h39h19h09h27a37a17a07a29g39g19g09g37t27t07t17t07717727737729n39n19n09n19m09m39m29m17r07r37r27r\
    37027007017019p09p39p29p27837817807819l09l39l29l09j19j29j39j17d07d37d27d17b07b37b27b39i29i09i19i\
    37c27c07c17c09o19o29o39o27q37q17q07q09k19k29k39k29q39q19q09q17k07k37k27k37227207217229u39u19u09u\
    27g37g17g07g29t39t19t09t17107137127119s09s39s29s17m07m37m27m09r19r29r39r17607637627629v39v19v09v\
    0331332333332je3je1je0je2383381380382jl3jl1jl0jl0391392393391j50j53j52j53302300301302jp3jp1jp0jp\
    0371372373370jn1jn2jn3jn2jh3jh1jh0jh03a13a23a33a23h33h13h03h1ja0ja3ja2ja3342340341341jf0jf3jf2jf\
    1310313312312js3js1js0js3322320321320ju1ju2ju3ju2j83j81j80j833l23l03l13l23g33g13g03g0jt1jt2jt3jt\
    03j13j23j33j3jd2jd0jd1jd0j91j92j93j90351352353351jb0jb3jb2jb03i13i23i33i2jq3jq1jq0jq23k33k13k03k\
    13b03b33b23b1ji0ji3ji2ji1360363362360jv1jv2jv3jv2jg3jg1jg0jg13t03t33t23t33c23c03c13c3jo2jo0jo1jo\
    0j31j32j33j333e23e03e13e1j10j13j12j133s23s03s13s23q33q13q03q3jk2jk0jk1jk3j42j40j41j403f13f23f33f\
    0jj1jj2jj3jj23d33d13d03d1jm0jm3jm2jm23r33r13r03r13m03m33m23m3jr2jr0jr1jr0j71j72j73j713n03n33n23n\
    1j60j63j62j613v03v33v23v3j02j00j01j033p23p03p13p3jc2jc0jc1jc23o33o13o03o3j22j20j21j213u03u33u23u\
    2603601600601bp0bp3bp2bp1630633632631be0be3be2be2643641640643bf2bf0bf1bf0611612613611bs0bs3bs2bs\
    2623621620622bu3bu1bu0bu1b90b93b92b92653651650651690693692693b52b50b51b506b16b26b36b3bi2bi0bi1bi\
    3682680681681bl0bl3bl2bl0661662663662bv3bv1bv0bv1b30b33b32b306e16e26e36e1670673672672bn3bn1bn0bn\
    26c36c16c06c0bo1bo2bo3bo2b43b41b40b426f36f16f06f3bh2bh0bh1bh26a36a16a06a1bj0bj3bj2bj16d06d36d26d\
    36h26h06h16h3ba2ba0ba1ba36g26g06g16g2bt3bt1bt0bt1b70b73b72b736n26n06n16n06m16m26m36m0br1br2br3br\
    2b03b01b00b006p16p26p36p3b82b80b81b806l16l26l36l16j06j36j26j0bd1bd2bd3bd0bb1bb2bb3bb26i36i16i06i\
    2bc3bc1bc0bc16o06o36o26o3bq2bq0bq1bq16k06k36k26k36q26q06q16q0bk1bk2bk3bk2b23b21b20b236u26u06u16u\
    3bg2bg0bg1bg36t26t06t16t0b11b12b13b106s16s26s36s0bm1bm2bm3bm16r06r36r26r0b61b62b63b636v26v06v16v\
    1m30m33m32m331e21e01e11e3m82m80m81m831l21l01l11l1m90m93m92m90151152153152m03m01m00m031p21p01p11p\
    1m70m73m72m711n01n31n21n31h21h01h11h1ma0ma3ma2ma3mh2mh0mh1mh01a11a21a31a2m43m41m40m401f11f21f31f\
    0m11m12m13m131s21s01s11s2m23m21m20m211u01u31u21u3182180181182ml3ml1ml0ml3mg2mg0mg1mg11t01t31t21t\
    1mj0mj3mj2mj21d31d11d01d1190193192191m50m53m52m501b11b21b31b1mi0mi3mi2mi31q21q01q11q3mk2mk0mk1mk\
    0mb1mb2mb3mb01i11i21i31i0m61m62m63m611v01v31v21v31g21g01g11g0mt1mt2mt3mt2mc3mc1mc0mc21o31o11o01o\
    1130133132132me3me1me0me0111112113112ms3ms1ms0ms3mq2mq0mq1mq21k31k11k01k2143141140141mf0mf3mf2mf\
    11j01j31j21j3md2md0md1md01m11m21m31m3mr2mr0mr1mr0mm1mm2mm3mm21r31r11r01r1170173172170mn1mn2mn3mn\
    0161162163160mv1mv2mv3mv2103101100102mp3mp1mp0mp21c31c11c01c3mo2mo0mo1mo2123121120120mu1mu2mu3mu\
    15n05n35n25n2n73n71n70n735e25e05e15e2n33n31n30n315t05t35t25t1ng0ng3ng2ng25d35d15d05d2nj3nj1nj0nj\
    15u05u35u25u0n21n22n23n22nl3nl1nl0nl15805835825835l25l05l15l1n80n83n82n825k35k15k05k1nq0nq3nq2nq\
    0551552553552n93n91n90n925o35o15o05o0nc1nc2nc3nc2ne3ne1ne0ne25335315305335p25p05p15p0n01n02n03n0\
    15v05v35v25v3n62n60n61n60nt1nt2nt3nt15g05g35g25g1na0na3na2na15h05h35h25h2ns3ns1ns0ns351251051151\
    05a15a25a35a1nh0nh3nh2nh05f15f25f35f0n41n42n43n42np3np1np0np05015025035025r35r15r05r3nm2nm0nm1nm\
    0nn1nn2nn3nn2573571570571n50n53n52n525935915905935s25s05s15s3n12n10n11n13nk2nk0nk1nk15q05q35q25q\
    0nv1nv2nv3nv3562560561561ni0ni3ni2ni35b25b05b15b05i15i25i35i3nb2nb0nb1nb0nu1nu2nu3nu052152252352\
    1nf0nf3nf2nf0541542543543nd2nd0nd1nd25j35j15j05j3nr2nr0nr1nr35m25m05m15m3no2no0no1no05c15c25c35c\
    1de0de3de2de2e33e31e30e33d52d50d51d52e93e91e90e91dl0dl3dl2dl1e80e83e82e82dn3dn1dn0dn2e73e71e70e7\
    1dp0dp3dp2dp0e01e02e03e02ea3ea1ea0ea1dh0dh3dh2dh3da2da0da1da1eh0eh3eh2eh2dt3dt1dt0dt1eg0eg3eg2eg\
    0dd1dd2dd3dd2ej3ej1ej0ej2du3du1du0du0e21e22e23e22e53e51e50e52d93d91d90d93df2df0df1df0e41e42e43e4\
    1ds0ds3ds2ds3e12e10e11e10el1el2el3el1d80d83d82d81ek0ek3ek2ek1dq0dq3dq2dq2ei3ei1ei0ei3db2db0db1db\
    0dk1dk2dk3dk1eq0eq3eq2eq0do1do2do3do0ec1ec2ec3ec2ef3ef1ef0ef0d41d42d43d42dv3dv1dv0dv3e62e60e61e6\
    0ee1ee2ee3ee2d33d31d30d31ed0ed3ed2ed2dj3dj1dj0dj3di2di0di1di3eb2eb0eb1eb3et2et0et1et1dg0dg3dg2dg\
    0es1es2es3es3d12d10d11d11er0er3er2er3dm2dm0dm1dm0dr1dr2dr3dr3em2em0em1em0ep1ep2ep3ep0d01d02d03d0\
    1eo0eo3eo2eo0dc1dc2dc3dc3en2en0en1en2d73d71d70d73ev2ev0ev1ev3d62d60d61d63eu2eu0eu1eu0d21d22d23d2\
    0vn1vn2vn3vn3i72i70i71i72ve3ve1ve0ve3i32i30i31i30vt1vt2vt3vt0ig1ig2ig3ig3vd2vd0vd1vd3ij2ij0ij1ij\
    0vu1vu2vu3vu1i20i23i22i23il2il0il1il0v81v82v83v82vl3vl1vl0vl0i81i82i83i83vk2vk0vk1vk0iq1iq2iq3iq\
    1v50v53v52v53i92i90i91i93vo2vo0vo1vo1ic0ic3ic2ic3ie2ie0ie1ie3v32v30v31v32vp3vp1vp0vp1i00i03i02i0\
    0vv1vv2vv3vv2i63i61i60i61it0it3it2it0vg1vg2vg3vg0ia1ia2ia3ia0vh1vh2vh3vh3is2is0is1is2v13v11v10v1\
    1va0va3va2va0ih1ih2ih3ih1vf0vf3vf2vf1i40i43i42i43ip2ip0ip1ip1v00v03v02v03vr2vr0vr1vr2im3im1im0im\
    1in0in3in2in3v72v70v71v70i51i52i53i53v92v90v91v92vs3vs1vs0vs2i13i11i10i12ik3ik1ik0ik0vq1vq2vq3vq\
    1iv0iv3iv2iv2v63v61v60v60ii1ii2ii3ii2vb3vb1vb0vb1vi0vi3vi2vi2ib3ib1ib0ib1iu0iu3iu2iu1v20v23v22v2\
    0if1if2if3if1v40v43v42v42id3id1id0id3vj2vj0vj1vj2ir3ir1ir0ir2vm3vm1vm0vm2io3io1io0io1vc0vc3vc2vc\
    0se1se2se3se3r32r30r31r32s53s51s50s53r92r90r91r90sl1sl2sl3sl0r81r82r83r83sn2sn0sn1sn3r72r70r71r7\
    0sp1sp2sp3sp1r00r03r02r03ra2ra0ra1ra0sh1sh2sh3sh2sa3sa1sa0sa0rh1rh2rh3rh3st2st0st1st0rg1rg2rg3rg\
    1sd0sd3sd2sd3rj2rj0rj1rj3su2su0su1su1r20r23r22r23r52r50r51r53s92s90s91s92sf3sf1sf0sf1r40r43r42r4\
    0ss1ss2ss3ss2r13r11r10r11rl0rl3rl2rl0s81s82s83s80rk1rk2rk3rk0sq1sq2sq3sq3ri2ri0ri1ri2sb3sb1sb0sb\
    1sk0sk3sk2sk0rq1rq2rq3rq1so0so3so2so1rc0rc3rc2rc3rf2rf0rf1rf1s40s43s42s43sv2sv0sv1sv2r63r61r60r6\
    1re0re3re2re3s32s30s31s30rd1rd2rd3rd3sj2sj0sj1sj2si3si1si0si2rb3rb1rb0rb2rt3rt1rt0rt0sg1sg2sg3sg\
    1rs0rs3rs2rs2s13s11s10s10rr1rr2rr3rr2sm3sm1sm0sm1sr0sr3sr2sr2rm3rm1rm0rm1rp0rp3rp2rp1s00s03s02s0\
    0ro1ro2ro3ro1sc0sc3sc2sc2rn3rn1rn0rn3s72s70s71s72rv3rv1rv0rv2s63s61s60s62ru3ru1ru0ru1s20s23s22s2\
    2kn3kn1kn0kn0l71l72l73l71ke0ke3ke2ke0l31l32l33l32kt3kt1kt0kt2lg3lg1lg0lg0kd1kd2kd3kd0lj1lj2lj3lj\
    2ku3ku1ku0ku3l22l20l21l20ll1ll2ll3ll2k83k81k80k81kl0kl3kl2kl2l83l81l80l80kk1kk2kk3kk2lq3lq1lq0lq\
    3k52k50k51k50l91l92l93l90ko1ko2ko3ko3lc2lc0lc1lc0le1le2le3le0k31k32k33k31kp0kp3kp2kp3l02l00l01l0\
    2kv3kv1kv0kv1l60l63l62l63lt2lt0lt1lt2kg3kg1kg0kg2la3la1la0la2kh3kh1kh0kh0ls1ls2ls3ls1k10k13k12k1\
    3ka2ka0ka1ka2lh3lh1lh0lh3kf2kf0kf1kf3l42l40l41l40lp1lp2lp3lp3k02k00k01k00kr1kr2kr3kr1lm0lm3lm2lm\
    3ln2ln0ln1ln0k71k72k73k72l53l51l50l50k91k92k93k91ks0ks3ks2ks1l10l13l12l11lk0lk3lk2lk2kq3kq1kq0kq\
    3lv2lv0lv1lv1k60k63k62k62li3li1li0li1kb0kb3kb2kb3ki2ki0ki1ki1lb0lb3lb2lb3lu2lu0lu1lu3k22k20k21k2\
    2lf3lf1lf0lf3k42k40k41k41ld0ld3ld2ld0kj1kj2kj3kj1lr0lr3lr2lr1km0km3km2km1lo0lo3lo2lo3kc2kc0kc1kc\
    2te3te1te0te0a31a32a33a31t50t53t52t50a91a92a93a92tl3tl1tl0tl2a83a81a80a80tn1tn2tn3tn0a71a72a73a7\
    2tp3tp1tp0tp3a02a00a01a00aa1aa2aa3aa2th3th1th0th1ta0ta3ta2ta2ah3ah1ah0ah0tt1tt2tt3tt2ag3ag1ag0ag\
    3td2td0td1td0aj1aj2aj3aj0tu1tu2tu3tu3a22a20a21a20a51a52a53a50t91t92t93t91tf0tf3tf2tf3a42a40a41a4\
    2ts3ts1ts0ts1a10a13a12a13al2al0al1al2t83t81t80t82ak3ak1ak0ak2tq3tq1tq0tq0ai1ai2ai3ai1tb0tb3tb2tb\
    3tk2tk0tk1tk2aq3aq1aq0aq3to2to0to1to3ac2ac0ac1ac0af1af2af3af3t42t40t41t40tv1tv2tv3tv1a60a63a62a6\
    3ae2ae0ae1ae0t31t32t33t32ad3ad1ad0ad0tj1tj2tj3tj1ti0ti3ti2ti1ab0ab3ab2ab1at0at3at2at2tg3tg1tg0tg\
    3as2as0as1as1t10t13t12t12ar3ar1ar0ar1tm0tm3tm2tm3tr2tr0tr1tr1am0am3am2am3ap2ap0ap1ap3t02t00t01t0\
    2ao3ao1ao0ao3tc2tc0tc1tc1an0an3an2an0t71t72t73t71av0av3av2av1t60t63t62t61au0au3au2au3t22t20t21t2\
    3pn2pn0pn1pn1o70o73o72o70pe1pe2pe3pe1o30o33o32o33pt2pt0pt1pt3og2og0og1og1pd0pd3pd2pd1oj0oj3oj2oj\
    3pu2pu0pu1pu2o23o21o20o21ol0ol3ol2ol3p82p80p81p80pl1pl2pl3pl3o82o80o81o81pk0pk3pk2pk3oq2oq0oq1oq\
    2p53p51p50p51o90o93o92o91po0po3po2po2oc3oc1oc0oc1oe0oe3oe2oe1p30p33p32p30pp1pp2pp3pp2o03o01o00o0\
    3pv2pv0pv1pv0o61o62o63o62ot3ot1ot0ot3pg2pg0pg1pg3oa2oa0oa1oa3ph2ph0ph1ph1os0os3os2os0p11p12p13p1\
    2pa3pa1pa0pa3oh2oh0oh1oh2pf3pf1pf0pf2o43o41o40o41op0op3op2op2p03p01p00p01pr0pr3pr2pr0om1om2om3om\
    2on3on1on0on1p70p73p72p73o52o50o51o51p90p93p92p90ps1ps2ps3ps0o11o12o13o10ok1ok2ok3ok3pq2pq0pq1pq\
    2ov3ov1ov0ov0p61p62p63p63oi2oi0oi1oi0pb1pb2pb3pb2pi3pi1pi0pi0ob1ob2ob3ob2ou3ou1ou0ou2p23p21p20p2\
    3of2of0of1of2p43p41p40p40od1od2od3od1pj0pj3pj2pj0or1or2or3or0pm1pm2pm3pm0oo1oo2oo3oo2pc3pc1pc0pc\
    3fe2fe0fe1fe1u30u33u32u30f51f52f53f51u90u93u92u93fl2fl0fl1fl3u82u80u81u81fn0fn3fn2fn1u70u73u72u7\
    3fp2fp0fp1fp2u03u01u00u01ua0ua3ua2ua3fh2fh0fh1fh0fa1fa2fa3fa3uh2uh0uh1uh1ft0ft3ft2ft3ug2ug0ug1ug\
    2fd3fd1fd0fd1uj0uj3uj2uj1fu0fu3fu2fu2u23u21u20u21u50u53u52u51f90f93f92f90ff1ff2ff3ff2u43u41u40u4\
    3fs2fs0fs1fs0u11u12u13u12ul3ul1ul0ul3f82f80f81f83uk2uk0uk1uk3fq2fq0fq1fq1ui0ui3ui2ui0fb1fb2fb3fb\
    2fk3fk1fk0fk3uq2uq0uq1uq2fo3fo1fo0fo2uc3uc1uc0uc1uf0uf3uf2uf2f43f41f40f41fv0fv3fv2fv0u61u62u63u6\
    2ue3ue1ue0ue1f30f33f32f33ud2ud0ud1ud1fj0fj3fj2fj0fi1fi2fi3fi0ub1ub2ub3ub0ut1ut2ut3ut3fg2fg0fg1fg\
    2us3us1us0us0f11f12f13f13ur2ur0ur1ur0fm1fm2fm3fm2fr3fr1fr0fr0um1um2um3um2up3up1up0up2f03f01f00f0\
    3uo2uo0uo1uo2fc3fc1fc0fc0un1un2un3un1f70f73f72f70uv1uv2uv3uv0f61f62f63f60uu1uu2uu3uu2f23f21f20f2"

@[expose] def burnsideF48s_g2dDig (c : Char) : ℕ :=
  if c.toNat < 58 then c.toNat - 48 else c.toNat - 87

@[expose] def burnsideF48s_g2dTL (_ : Unit := ()) : List (List ℕ) :=
  (List.range 32).map fun i => burnsideF48s_g2dEvL (burnsideF48s_g2dTelF i)

@[expose] def burnsideF48s_g2dTiL (_ : Unit := ()) : List (List ℕ) :=
  (List.range 32).map fun i => burnsideF48s_g2dEvL (burnsideF48s_invW (burnsideF48s_g2dTelF i))

@[expose] def burnsideF48s_g2dAL (_ : Unit := ()) : List (List ℕ) :=
  (List.range 64).map fun k => burnsideF48s_g2dEvL (burnsideF48s_g2dAF k)

@[expose] def burnsideF48s_g2dBL (_ : Unit := ()) : List (List ℕ) :=
  (List.range 64).map fun k => burnsideF48s_g2dEvL (burnsideF48s_g2dBF k)

@[expose] def burnsideF48s_g2dVL (_ : Unit := ()) : List (List ℕ) :=
  (List.range 4).map fun j => burnsideF48s_g2dEvL (u33Word (burnsideF48s_g2dCandV.getD j ""))

@[expose] def burnsideF48s_g2dCheckGens (_ : Unit := ()) : Bool :=
  (List.finRange 5).all fun i => decide (RepL (burnsideF48s_g2dGL.getD i []) (u33Img i)) &&
    decide (RepL (burnsideF48s_g2dGLi.getD i []) (u33Img i)⁻¹)

@[expose] def burnsideF48s_g2dCheckA (_ : Unit := ()) : Bool :=
  let TL := burnsideF48s_g2dTL ()
  let AL := burnsideF48s_g2dAL ()
  let XL := burnsideF48s_g2dEvL (u33Word "X")
  (List.range 32).all fun i₁ => (List.range 32).all fun i₂ =>
    !(decide (compL (compL (compL (TL.getD i₁ []) XL) (TL.getD i₂ []))
        (compL (compL (TL.getD i₁ []) XL) (TL.getD i₂ [])) = List.range 28)) ||
      (List.range 8).any fun k =>
        decide (compL (compL (TL.getD i₁ []) XL) (TL.getD i₂ []) = AL.getD k [])

@[expose] def burnsideF48s_g2dCheckB (_ : Unit := ()) : Bool :=
  let TL := burnsideF48s_g2dTL ()
  let BL := burnsideF48s_g2dBL ()
  let YL := burnsideF48s_g2dEvL (u33Word "Y")
  (List.range 32).all fun i₁ => (List.range 32).all fun i₂ =>
    (List.range 64).any fun k =>
      decide (compL (compL (TL.getD i₁ []) YL) (TL.getD i₂ []) = BL.getD k [])

@[expose] def burnsideF48s_g2dCheckCand (_ : Unit := ()) : Bool :=
  let TL := burnsideF48s_g2dTL ()
  let TiL := burnsideF48s_g2dTiL ()
  let AL := burnsideF48s_g2dAL ()
  let BL := burnsideF48s_g2dBL ()
  let VL := burnsideF48s_g2dVL ()
  let UL := burnsideF48s_g2dEvL (u33Word "Xs")
  let YL := burnsideF48s_g2dEvL (u33Word "Y")
  let cs := burnsideF48s_g2dTab.toList.toArray
  (List.range 8).all fun a => (List.range 64).all fun b => (List.range 8).all fun c =>
    decide (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c)) '0') < 4) &&
    decide (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 1) '0') < 32) &&
    decide (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 2) '0') < 32) &&
    decide (compL (compL (TL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 1) '0')) [])
        (AL.getD a [])) (TiL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 1) '0')) []) =
      UL) &&
    decide (compL (compL (compL (TL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 1) '0')) [])
        (BL.getD b [])) (TiL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 1) '0')) []))
        (TL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 2) '0')) []) = YL) &&
    decide (compL (compL (TiL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 2) '0')) [])
        (compL (compL (TL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 1) '0')) [])
          (AL.getD c [])) (TiL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 1) '0')) [])))
        (TL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c) + 2) '0')) []) =
      VL.getD (burnsideF48s_g2dDig (cs.getD (3 * (512 * a + 8 * b + c)) '0')) [])

end CFSG.ASVolI
