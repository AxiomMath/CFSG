module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public import Std.Data.HashSet

public section

namespace CFSG.StandardType.L34Sylow

open CFSG.PSL3Four.Native

@[expose] def pT : Tab :=
  #[15, 12, 17, 6, 3, 9, 4, 18, 8, 10, 5, 2, 20, 0, 14, 13, 16, 11, 19, 7, 1, 30, 32, 21, 33, 31,
    35, 24, 28, 41, 23, 37, 40, 27, 29, 39, 36, 25, 38, 26, 22, 34]

@[expose] def qT : Tab :=
  #[2, 0, 1, 3, 4, 9, 6, 19, 16, 10, 5, 20, 15, 11, 8, 17, 14, 12, 7, 18, 13, 30, 31, 21, 32, 33,
    26, 22, 38, 34, 23, 27, 37, 40, 41, 35, 28, 24, 36, 39, 25, 29]

@[expose] def aSixGen1T : Tab :=
  #[1, 10, 14, 6, 18, 0, 4, 3, 2, 12, 16, 8, 20, 9, 17, 13, 5, 11, 7, 19, 15, 30, 26, 38, 34, 22,
    27, 37, 23, 40, 28, 24, 41, 35, 29, 39, 36, 25, 21, 32, 31, 33]

@[expose] def aSixGen2T : Tab :=
  #[1, 2, 3, 4, 0, 8, 20, 12, 16, 14, 10, 18, 6, 17, 5, 13, 9, 11, 15, 7, 19, 36, 28, 40, 22, 32,
    26, 23, 31, 41, 27, 33, 38, 24, 29, 39, 25, 30, 21, 34, 37, 35]

@[expose] def aSixGen3T : Tab :=
  #[1, 10, 18, 14, 6, 0, 3, 2, 4, 11, 19, 15, 7, 12, 8, 20, 16, 9, 13, 5, 17, 30, 26, 34, 22, 38,
    27, 40, 37, 23, 29, 25, 39, 36, 21, 33, 32, 31, 28, 35, 24, 41]

@[expose] def aSixGen4T : Tab :=
  #[1, 2, 3, 4, 0, 9, 13, 5, 17, 19, 7, 15, 11, 16, 12, 20, 8, 6, 18, 10, 14, 31, 21, 33, 30, 32,
    26, 41, 36, 23, 29, 40, 34, 24, 27, 39, 35, 22, 28, 38, 37, 25]

@[expose] def aSixGen5T : Tab :=
  #[1, 2, 3, 4, 0, 15, 11, 19, 7, 5, 17, 9, 13, 10, 14, 6, 18, 20, 8, 16, 12, 23, 29, 35, 38, 32,
    26, 36, 41, 31, 21, 25, 22, 24, 28, 39, 33, 34, 27, 30, 37, 40]

@[expose] def aSixGen6T : Tab :=
  #[1, 13, 17, 5, 9, 4, 3, 0, 2, 6, 10, 14, 18, 20, 8, 16, 12, 11, 19, 15, 7, 39, 26, 37, 32, 24,
    21, 40, 41, 38, 27, 35, 31, 22, 29, 25, 36, 30, 28, 33, 23, 34]

@[expose] def repData5 : String :=
  "kh0jif52a6db439e7c18gznCwtylBADmrvsouFxpEq|0|22121222021|1211220210|0202211202;c9ba0j54e\
    g18k6hf32di7votyEulxwspCBFnAqzmrD|0|211021221|112212211|2002121122;jhik0c5e43d8a692gf1b7\
    zoFusylBAEpqxtnwCvmDr|0|0020200220|122211020|21121221100;a90cbkf52ei1674hg38djxnyDsuwvlr\
    CAoEzqpBtFm|0|022220200|02121211211|212102022;kh0jia25f4bd67e93g81cBnurEyAzlDqwosvCpxFtm\
    |0|212212200|20021121|21221200221;c9ba0e45jk81g3fh67id2xoACruwvlsDynFBtmzqEp|0|110212022\
    0|212022110220|21102120211;4i98fe5cj1320ag7h6bdkroxCAwpyFqltsDmvzBnEu|0|022102121200|022\
    1022210|22021221002;2jg96fk5a1043bhe87icdtnCzwvyEoqsrlFxBmADup|0|2002221211|102202120220\
    |20221211221;4f89ijc5e13207hagb6kdtoEyvwzCnqsrlDuApBFxm|0|02122020211|1021211202100|2002\
    2120;2ebh8a5kfic7d6j9g1430rnuEBAoCxFpwyqltsvmzD|0|0220020222|2100221100|02122100220;4a7h\
    ge5cj6kbdif981203roxCABnEuDmvzqltswpyF|0|00211222020|210221222|22211212210;2be8hfk5a7dic\
    j6g91430tnCzwADupFxBmqsrlvyEo|0|1022021212|1122221020|22121020;fk5a2h6c30dgejb17i489yzlA\
    BnDxsCmquwrpFtvEo|0|221202222112|020202202100|1221211221;jc5e49g26b17fa8d30kihuvlwxoszFt\
    pDAyCmqEBrn|3|0|1|2110200;cj54eh3f6id72k81g0ab9yzlABoEvtFprwuqmCsxDn|3|0|1|0200;ak2f5h4g\
    70bc9jd83i61eyBAlznDxsuqmCrwFpEotv|0|02102022200|202022021|202122112020;ec4j59k73b82ha1i\
    60gdfuxwlvoszFADptCyqmrnEB|0|100220221200|1212210202|20222110221;5kf2adh9160784jecbi3gDl\
    CEFnysxmzrvpAtuoBqw|0|2121202112|210221211220|2022210;5cj4e19hdgb3ikaf28067sltrqouFzpvCB\
    mwEAnxDy|0|0020211200|22102100210|022212211;5jce4dh913igbak2f8067ElFDCoytvpzqxmAswnBru|0\
    |12022121200|122212102120|22212110210;60578fhc3dkb4eia1gj92CznwtmyquDlEFvBpsrAxo|0|02112\
    2211|21021120021|12102222002;fd0egk5a26h3cb1j7498iDnysxClFEzmvrwoqBtpAu|0|02202212|22022\
    0|102222120;e45jci16a93k782bhf0dgwrpFyoqBDxluvCtnzAsEm|0|121211202|121020222021|21002102\
    2;b9c0ag5i3j1f72h8e6d4kvpsBCulxwtoEyDmzrAnqF|0|210021221|112212211|02122112220;7086539ke\
    4ahg1bjf2cidqxEpzmuCyBwoDFvAntlrs|6|0|1|2222;70865gha4ek93dic2fjb1CBspvmyquxAortzwnFlDE|\
    0|22120022|11002110220|02211020220;f2ka5j17bg0de94i863chvtyoEnqAFCspBzrDmwlux|0|12102021\
    221|2020211211|202021211210;j4ce5f1b783da926gi0khwtznCoqBDEsmAyrFpvlxu|0|0222020020|2102\
    22100210|12102121021;a90cbfk25ie6147gh83jdwnCtzuxlvrypFEsmABDoq|0|2102102210|02022021020\
    |12022202022;jhik0e4c58a3d2g69b7f1AorCxyBlzEwmstDpuvqnF|2|0|1|020220;5a2fkdh918706j4ce3g\
    biElFDCnBrumAswpzqxoytv|0|022220200|1102221211|1221210020;5kf2a19hd8706cej4g3ibsltrqnxDy\
    mwEApvCBouFz|0|2211021222|212212|00210211210;5cj4edh91i3bg2fak7608FlECDozsupyrwmBtxnAqv|\
    0|021121211210|02002110202|2121212211;60578gj92eia1dkb4fhc3CvpsBmyquroAxztnwDEFl|0|21102\
    200220|212122002220|22212002;a25fkei16bc09h74g8d3jAroxCnFvqupDtEwmsByzl|0|020220020|0212\
    222020|1221211202;e45jca61i7k39hb28gd0fBrnuEoDwqxmFtCvpsAzyl|0|00211221021|102021020|221\
    2112221;f2ka5b71jed0g8i49hc36AtDpunFvqCxorzBylwmEs|0|212112210|2211021122|0022022212;edg\
    f0cj5428hbia16739kFosuzCEDlAvqnxtBmrywp|0|21202100221|022220210|2122211222;e397k1ia645jc\
    0gdf2b8hqrlstxpzEowDBAFvnCymu|0|2022020210|0212110020|122021;5i3bg91dh4ecj8670fa2kwlxvup\
    ryFoqBDntzCmsAE|0|12022200200|21102021102|112102110;k6db4f52ah0jic8g1379eznCwtDmrvylBAxp\
    EqsouF|0|221202100|002221212110|211022020212;3e9k7i5gb14026cfhajd8rpwFyxoACqltsEnuBzmDv|\
    0|12020200210|022022210|1122122002;7c2dib1fj0865agh49k3eutApDFsozmqyCxlvwBrEn|0|22112122\
    11|2022220222|022122210;2gj69kfa510438ehbcd7isnyxDvCpBqtlrFzouAwmE|0|2112022200|22210022\
    02221|120202221100;58706hd192akfb3giejc4AlBzymEwsnFvqoCxrpDut|0|02021210|002122|12021122\
    12;5gb3ihd194ecj7086afk2BlAyzpCvsoDwqnEurmFxt|0|02122021020|00220200211|220021210200;6jg\
    29ie1a0578k4bdhcf3yrpwFvoEtmCuqzABlDxns|0|002102|021211220200|100200211;7id2cjf1b0865h4a\
    gk9e3ytEovFwprmCuqxnDsBzAl|0|2222002|0022221202|21102002020;ja8d34e5chik071fbg629BowqDEr\
    unyAzlvCsptxFm|0|12002222|20220222200|122220211020;2ic7da5kfebh813046gj9rnuEBFpwyAoCxvmz\
    Dqlts|0|211022121210|2110220|21020020;4bd6kjc5e7agh1032f9i8toEyvDuApBFxmwzCnqsrl|4|0|1|1\
    0211;a3dj816ei4h7g0c9b2fk5qrlstEzpxBDwonvFAumyC|0|222211021|022202202100|2212122211;e0df\
    g1ia62hb83k974jc5qrlstCymuAFvnowDBxpzE|0|1020021|22211020210|2221121;f3c6h1jb748i90dge2a\
    5kqtslrzExpwoBDnvFACymu|0|1221121100|02210212110|2210020;5gb3i91dhjce468072kfavluwxpsBCo\
    tyEnqAFmrzD|0|1122022211|100210211021|100200220;5870691dhfka2ig3b4cjewlxvumsAEntzCoqBDpr\
    yF|0|02211022022|2002020020|22211021122;6bk4da1eicfh39j2g0785urnEBDtpAzsFomqyCvlwx|5|0|1\
    |021210;7ah4gb1fj9ek3ci2d0658utApDBrEnxlvwmqyCFsoz|0|221200212|0221021002|102221102221;4\
    gh7acje5k6db89fi1203sozuFBvpCDynxqtlrwEmA|0|1002202220|120220211|1202210200;5bgi3hd19e4j\
    c86702kfaAlBzypDutoCxrnFvqmEws|0|12220202200|02200202|222121022220;6kbd4ie1ah3cfj9g20785\
    yrpwFDxnszABlmCuqvoEt|0|20200220|2022020021|21220220212;3f6chbg5ijda87ek91024tpDAuzCwnEv\
    yoqsrlxBFm|0|0212122121|020022122210|21021100221;c72ide45j3h6fkg819a0bxoACrFBtmzqEpuwvls\
    Dyn|0|221021202|22211221220|1211222002;kf52ad64b0hije397gc81CDlEFnztwymuqsvpBxrAo|0|2122\
    0210020|210221202120|2121202221210;gb53i9j62c1k80fdea74huvlwxptADsoFzBEnrCyqm|1|0|1|2210\
    200;ej45ch8b2ia16k3790dfgyABzloEvtrwFpCmquxsnD|0|2020222211|02110211|21122021020;gib35h7\
    a4j2690defkc18yBAlzpFwrvtoEsxDnCmqu|0|22220021|22022020212|21222021212;cej45d27ig8k1fh36\
    0b9aCFElDoArxsvpBuqymznwt|0|1102210220|02221212122|210022202212;5fka2hd196078cej43gbizly\
    ABnCwtmDvrpExqoFus|0|220202122|022202210200|2200211002;1ei6a342095hd7jbfkc8gxqpEzroCAlwu\
    vsDyntBmF|6|0|1|2221121;1fj7b0243gk8ceai6d59hCqyumtnzwsvpBlFEDrAxo|0|20212210211|1122220\
    20|12212221211;1jfb734208cgkae6id59hEqzxptoyvswmAlDCFrBun|0|1002122|212110211200|2212022\
    120;60578kd4bhf3cjg29ie1ayDnsxmCuqzlABrFpwvEto|0|022212120|20021121021|020212020020;fk5a\
    26h3cd0egbj714i98DzmvrnysxClFEwBoqtAup|0|1200220200|2222100210200|020200200210;jc5e4g962\
    1bf78a3dk0hisvpBCouFztlqryxnDEwAm|0|120222100|2102212102100|222200220210;h5d9182eb7a4g0k\
    ji6fc3mAEswlnpoBFtxzvDryquC|0|02022102200|02212221102|12110210;h5d91g4a7be283cf6ijk0pBCs\
    vlomnADtuywFrzqxE|0|02112102120|2221022021|2112020211;kaf25e973i0hj1cg86b4drxCoAnuEBywpF\
    Dvzmslqt|0|1221102122|2212022002|120211212102;5a2fkhd1978604jecg3ibBlAyznEurmFxtpCvsoDwq\
    |0|12210222102|1002221211|002112202220;5jce491dhgb3i2fak6780vluwxotyEpsBCmrzDnqAF|0|2212\
    10020|1020221022|1022002121;60578jg29ie1akd4bhf3cyvoEtmCuqrpwFzBlADsxn|0|21022022120|002\
    022221|021120222100;a25fkie61cb907hg4d8j3FrpywnAqvuoszEClDBxtm|0|02002122220|220221022|2\
    221102121;fd0ega2k53c6hj7b18i49EnuBrCFlDzqpxwAmstvoy|0|212212210|21021121|2100221;ihj0kb\
    g3527cd84f9ea61AptDuyBlzFvnqrCoxwsmE|0|0211222121100|0222210210|2212021211;j4ce5b7f1da83\
    6g92khi0DtupAoBqwEFlCyxsnvmrz|0|12110212202|212110210200|211211020;1a6ie3420dh59j7fb8gkc\
    EqzxprBunlDCFswmAtoyv|0|200211200|1222122102|02222020221;1fj7b3420c8kg6iaeh95dzqEpxtwCns\
    ouFlByArDmv|0|0222102100|1022110200|11022102020;5e4jc91dh3igbkaf27608xlwuvorACpqzEmtBFns\
    yD|0|2021102002|12102220020|2210222100;951hdgj26bca03ek7i4f8pvsCBlomnutDAwyrFxEzq|0|1210\
    21020200|221022022|20221022112;2a5kfjg963401d7ci8hbeEvotynBruqpzxAsmwFCDl|0|2211212110|1\
    21022100|1021022220;cj54ef6h372id1gk8b90atznCwovEyFmxBuDpAsrql|3|0|1|12122100;gde0fi35b7\
    ah4c81k2j96FprwyCEDlBxtmvqAnszuo|4|0|1|2112100;70865c2dib1fja4gh93ekuFsozmqyCtApDxvwlBnr\
    E|0|121002222|20221122211|0022210211;ak2f5g7h4c90b83jd1ei6sBvpCnxDyuFozrtqlEmwA|0|221120\
    022|200221102121|10200221102;ec4j5739k2hb8i6a1df0gFxBmtozsuAqnvCEDlrpyw|0|21022100211|12\
    2021022100|022022221;i49f81e6a35bg2cd70jkhqrlstwoBDpxEzyCumFAnv|0|020211222121|002202121\
    |1212220202;4i8f9ha7gjec50123k6dbyBAlzwrpFoEvtDnsxquCm|0|221202120|100212212110|02002211\
    222;6dkb4fhc30578g92je1iaCznwtDlEFmyqurAxovBps|0|11002210211|12120220220|2212020221;e93k\
    7i16a45jcfdg08h2bwrpFyxluvoqBDAsEmCtnz|0|2202022100|222021221|20212002121;8b2ehc1gk07569\
    fi4aj3dusFzoAtDpmqyCErnBwlxv|0|2211212211|21102210021|102212222100;icd2735bghj0k6ea1f498\
    zpExqFosuylBAwnCtrmvD|0|12112110202|1121221200|2022211020;fg0dej17b2ka56ch3984ivtyoECspB\
    nqAFwluxzrDm|0|11202212|222002120202|2022221212;ebh8245jcdgf0k3796i1aDoBqwAputClFErmzvxn\
    sy|0|02212002110|1121221210|020200221210;57860dh912akfig3bc4ejFlECDmBtxnAqvozsupyrw|0|20\
    21021200|102122|00220212;6gj92eia10578db4kf3hcCroAxvpsBmyquzwtnDFlE|0|102002|2200211220|\
    002020020021;kb46d2af5h0ji8c1ge973AnqFvDuptyBlzxroCsEmw|0|20202002020|210022121202|11222\
    0202100;j8a3de4c5hik0bf1729g6AorCxEwmsyBlzvqnFtDpu|0|021022202222|2122210021|0020220211;\
    fc3h62a5kd0egi9487bj1FnqvAzusoCEDltBxmwryp|0|2122112220|21220200220|022121211020;i72dcgb\
    53hj0ka16e4f89BpvsCFtxmyAzlwDqoruEn|0|1220200220|212212122200|21221222211;jad387b1f4ce5h\
    0ikg962BtFmxEunroDwqvpCsyAzl|0|20022221|021221221100|202021021220;a4h7g16ei3dj82k5f0bc9q\
    rlstBDwoEzpxumyCnvFA|0|222210021|021202122102|2021102120200;6cfh3a1eibk4d08579gj2urnEBzs\
    FoDtpAvlwxmqyC|5|0|1|021210;3a8jdi5gb6fhc1240ek79rpwFyEnuBzmDvxoACqlts|0|2021121121|2002\
    21222|0222021100;j62g9c5e4f71bh0ik38adzoFusvmDrtnwCEpqxylBA|0|2121212202|2202120200|1222\
    210210;2cid7kfa58hbe1304g69jsnyxDFzouAwmEvCpBqtlr|0|2022200200|102222021|221221;4k6dbcje\
    5gh7a10328i9fsozuFDynxBvpCwEmAqtlr|0|11221120212|12021220202|022211021100;a7hg4kf523j8d9\
    b0ce16ixnyDsBtFmEzqprCAouwvl|0|02222110022|202102122|12020200200;7k39ejf1bhag40586i2cdyt\
    EovxnDsBzAlFwprmCuq|0|21202221|12110210|2022120;c0b9a18gk27di36fh45ejqstrlumyCFAnvowDBzE\
    xp|0|02202212221|100221021|0222210210;b28eh17fj0ca94dk63i5gqtslrAFvnumyCpxEzDBow|0|20212\
    120200|221022022|1221212212;e0fgd9k73ai61bh82cj54uxwlvCyqmrnEBoszFADpt|4|0|1|022200;jih0\
    kf1b796g28a3d4e5cwtznCyrFpvlxuoqBDEsmA|0|210210211210|11212022200|00210212102;3chf6gbi58\
    adjk97e1024spBvCzuoFEAmwqtlrxDny|2|0|1|12120;7g4hafjb1e93kd2ic0658CtwnzBvspxorAmyquFElD|\
    0|202202121|1121211|2202002021;cid724ej5f6h381kg9a0bwoDqBFrpyzCntuxlvsAmE|0|22002202222|\
    002122120|12112102;fi4892a5k71bjc63hdeg0FnqvAwryptBxmCEDlzuso|0|02110220210|21021220|002\
    2221021;egfd0a61ih28b79k34jc5BrnuECvpsAzyloDwqxmFt|0|02112002|1022120022020|202110220221\
    ;8i9f4kg1cj3adhbe20567ysxDnwpFrEvotmCuqABzl|0|2200210020|0221020210|1121121202;bg5i3d46k\
    eh280a9cf7j1CDlEFpBsvAoxrtwnzuqym|1|0|1|1100210;ij0hk7dc2f849b35g1ae6tFmxByEvowCnzrlqspD\
    Au|0|2222002|2221120|12021202;af25kd38j0c9be6i1gh47CEFDlnztwuqymBpvsrxoA|0|021202021|022\
    02002022|1212222020;big53h2e8j71f0ca9kd64yABzlpFwrtvEoDnsxuqmC|0|21102210200|200202022|1\
    2221211022;fc63hj7b152ak4i98ed0gotvyEzFsunmlpCxrAwBqD|0|1202202002|210220220|112022;ig3b\
    5d72cea610hjkf498CFElDpBsvrxoAwtznymuq|0|112220212|11002100211|0020222100;hf63c0kjid519g\
    a74e2b8CymuqznwtlDFEAxroBspv|0|10022100200|2210220210|1212002210;9jg62bca015dh7e3kf48itu\
    pADvoyElsqrwzCnxFmB|0|10021002200|022112|2110202102;1kgc80243jfb7h5d9ia6eyqCmusnxDtvEorF\
    pwlAzB|0|12020212020|1022221021|120211200;d5h1972ci8aj36k4b0fegmFBxtlnpoEAwsCqyuDvrz|0|2\
    0222021|10222021210|211021021121;g6j29e0dfi5b3a74h18kcrCoxAvmzDpywFsqtlBunE|0|1102120211\
    |0221022211|100221022020;47agh302198ifk6dbe5cjxqEzpBmtFwulvoCrADysn|0|1021212220|2021022\
    21021|11210021100;2a5kfgj6943107dich8ebBvpCsnEurqowDAylzFtxm|0|2211212100|210212100|2021\
    221200;k2f5ac8g1ihj0db647e93FszuonAqvywrpxmtBDElC|0|212112200|2210021122|22121022211;c4j\
    5ekg816hf3d7i2ba90DsyxnoBqwzvrmuptAFClE|0|11211212|2002020020|002222121;4jec5g7ah9f8i6bd\
    k2130vBCpsotyEwxluqFAnDmzr|0|211002002002|21202210|2022211;ha47gijk0e82b63fc1d59rywpFBEu\
    nAoCxltqszvmD|0|21121211|1002102222|2112202110;gib35a4h769j2ef0d18kcrBunEpwFyvDmzsqtlCox\
    A|6|0|1|212102;i53gb49f8e1a6cd27jhk0owqDBplmnrxACyvEtFusz|0|1022110|121202220210|1202221\
    2112;i948fe1a635bg7dc2kh0jxroCAwlvupqzEysDnFtmB|0|21002112020|2022202120|200200;kj0ihg1c\
    82f5a97e36b4dvsCBpytEonqAFDrmzxlwu|0|11211002212|0220202220|102221221211;e8bh2k937c4j5gf\
    d01ia6sxDnyAwmEouFzrltqCvBp|0|02221|112221022021|202021200;793eka4gh0865bfj1ci2duBEnrxwl\
    vmqyCFozstDAp|0|1002002212100|212210|22121121002;e82bhjc45dgf03k97a1i6EovytAsmwCFlDrunBx\
    zpq|0|21202200220|0022022112|122122210;g7ah4i35bde0f296jck81FprwyBxtmCEDlszuovqAn|0|2222\
    021202110|21122021|1020200212110;ck1g8h3f609abje54i72dyzlABsxDnuqmCFprwoEvt|3|0|1|100220\
    ;b0ca917fj28eh35gi46dkqtslrumyCAFvnDBowpxEz|0|221021220|110220021|0021221202;7dc2igha4f1\
    jb0586e93kCBspvFlDEtzwnxAormyqu|0|21211202200|222202100|1121212200;6fc3heia1d4kb0857g92j\
    CroAxzwtnDFlEvpsBmyqu|0|00202121210|00210021102|2022020220;ke3972af581gchi0jb6d4AnqFvxro\
    CsEmwDuptyBlz|0|02002022002|1212200212|0200221210;7e93kfjb1g4ha0586dc2iCtwnzxorABvspFElD\
    myqu|0|02102212120|21202120|2021022002;8j3adkg1ci9f40675h2beysxDnEvotwpFrABzlmCuq|0|2112\
    221002|1121211|22021102;40123dbk6f9i8gah7ecj5CDlEFqumywtznoArxBpvs|0|11020021211|1020212\
    0200|1210202210;c0ab9d27if36hg18ke45jCFElDuqymznwtoArxsvpB|0|11212122200|21121102021|121\
    2120200;g629jb53ik8c147had0feDpAtuvmrzsnyxClFEBowq|0|0222002200|0212210211|021221200;7k9\
    e3id2ch4agjbf10658yFwprxDsnBlzAmCuqtEov|0|1202222|2100221002|11222202002;jc45ei0kh29g6da\
    837b1fFywrpouzsvqAntmBxEClD|0|12222021021|1021100210|02002021020;43102ahg7d6bk8fi9jc5eEB\
    rnuqzxpDlFCoytvwAms|0|222102122202|10211212120|022120221100;8f4i9gkc1da3je2hb0567CsBvpwn\
    tzEDlFmyquAxro|0|21211002221|12100200|11221210021;jk0hib7f1692gd3a84e5cDtupAyxsnvmrzoBqw\
    EFlC|0|2121121120|12212112002|110200220;bhe82fj17c09a6kd43i5gztCnwAyBluoFspExqDvmr|0|212\
    0021021121|22102002002|1211212112;0hkijfdeg65873124c9bazCntwylBAmDvruFsoqEpx|0|120210222\
    |2022202210|020211212110;0hkijab9c42137856gedfBunEryAzlqDowCpsvmtFx|0|0202222122|1212021\
    2110|00202112102;c3h6fid725je4g8k1ba90pFywrzEqxolnmuDAtsCvB|4|0|1|2112100;b4dk6eh285g3ic\
    a09j71foACrxDBwqplmntyEvuzsF|2|0|1|21002110;c2di7f36ha09bk1g854jenzCtwFqAvuEBroplmsxyD|1\
    |0|1|221100;3401279eka8jdgi5bhfc6BxmFtqwDoEunrzlyApvsC|0|22210022022|2200221122|12002110\
    0;324106fhc9ke7g5bija8dvzDmrqnFAxwulEtoypCsB|0|10020210202|1102122210|2100212021;h2be80k\
    ji4ag7159d3f6cqyumCAnFvBDwozxpElsrt|0|10221210212|1221102210|22210022212;d2c7i0feg3a8j4k\
    b615h9qCuymFnvAEzpxltsrDwBo|0|12002120210|1221002200|0210211220;kh0jid64b5fa21cg8937elDC\
    FEyzABnmpoxvuwsrtq|1|0|1|2211210;8c1gkf4i93jda6570he2bzwtnCsouFEqxpABlymDvr|0|2222021002\
    |11022110200|1202210200;7b1fjk39e4gahdic26508DxsyntpAuBqowmzrvFECl|0|202220210|100221002\
    10|02220212210;j6g92i0khe54c17bfa8d3rypFwvmzDoCAxEuBntqls|0|11211022221|122022210|211211\
    ;c9ba0h63fd27i5je41gk8lzAyBuvwxFDCEsrtqomnp|0|212220022210|022102202210|1212221122;ga74h\
    ck8192j60fdeb53iusFzoBnrEvxlwpDtACyqm|0|1020221210|22120211|110202211;36cfh1240igb5e9k7a\
    jd8rqsltzvmDpFywEnuBxACo|0|20200202022|1200212120200|0221122210;47agh2130if98dbk6cje5Fqn\
    AvBtmxwryposuzDlCE|0|12122122|21120212002|2020220202;d4b6k0feg195h2ic738jaqCuymDwBoltsrE\
    zpxFnvA|5|0|1|1021;2be8h5afkic7dg9j63014pnolmAuDtFrywqExzvBsC|0|202021002110|21002100|11\
    2002102211;k6db4ij0ha25fe9731g8cryFwpDvzmnEBustlqxoAC|0|12221022|2220211002|10210022;iae\
    16d72c3g5b84f9jhk0EFCDlrBunpxzqytovwmsA|0|02112121120|0022021022|20020021221;a74hgbc09jd\
    831i6ef25ktuDpABFxmEovynzwCrslq|0|2122002211|1102122211|20021211020;8kcg1eb2h94fi76503da\
    jxAorCsDynwulvEpzqmtBF|0|022211|22200212220|1202022121;gck81a74h92j6bi530defuBnrEsFzovxl\
    wCmyqptAD|0|20210210|1202110|1100211002;f52akj7b1c63he0gd48i9otvyEnmlpzFsuwBqDCxrA|0|020\
    210|220221202202|021102220;1bjf7gck859dhia6e3042psvBCtuADlomnqzExrFwy|2|0|1|1022;c8g1k2d\
    i7ej45ba90h3f6AFvnqsEmwoCxrzlByuDtp|0|202102200|2221120|0202002020;ga74h3ib5de0fj69281ck\
    EpxzqBrnuCFlDswmAvyot|0|12102222|22120221102|1221022210;h915d0kjic36fbe28a7g4uyqCmlxwvzs\
    FoBnrEADpt|5|0|1|220;igb53f849e1a6dc720khjCwtznpsvBrAxoymuqFElD|0|2222110021|222121210|0\
    0212112102;24103i7dcfak59g6j8hbewFrpyqBoDntzCAmsEvxul|0|2110022120|002212100|00212022;c8\
    g1k3h6fab09je54d27iEzpxqsAwmuBnrFlCDoytv|0|021002110|2212120220|110210212;j29g6i0khc45e7\
    1fbd3a8FywrpvqAnouzsEClDtmBx|0|200222112220|1021221210|112210220200;b82hei3g54dk69ac0fj1\
    7wpFryAEmsDqoBtznCuxlv|0|221211022|2112020022|002202200;a47ghbc09dj386e1ik52fDutApBowqEF\
    lCnsxyrzvm|0|1002020212|2021222200|02020021102;f1jb7c3h6849ik25ag0deszoFutqrlwEmACpvBnxD\
    y|0|1222021002|00202211211|1022112220;18gkc6aei7jbf03245dh9mrvzDsEwAtBFxlnpoquyC|0|10021\
    121221|022022|021222210;1i6eagck83204b7jf5dh9psvBCrFwyqzExlomntuAD|0|0222121|22022200200\
    |1102212102;16iae8kcg04327bfj5dh9mswAErDvzqyCulnpotxBF|0|021100211|2100200212|0202221002\
    0;bg35ie28h09cad6k4fj17CAxropvBsuqymtnzwDFlE|0|221021022|21002211210|020210022112;a38djc\
    b90hg74f5k26ie1zusoFEpqxBAylrDmvntCw|0|211022022|00212110222|22021021222;je54ckhi0926g38\
    ad7b1fxynsDoACrvluwtBmFEzqp|0|2200221021|10022102200|22112211;cgk18a9b072id4j5eh63fBunEr\
    svCpFxmtzlyAowqD|0|02202112021|2212211202|22020022211;fgde0849ika2517jbch63swEmACBpvnDyx\
    zoFutqrl|0|0221221211|202210222102|122202122;c6hf3i72da09be5j418gkrFypwzmDvuBEnstlqoxCA|\
    0|221221021|112020021200|211022021;ck81g4ej5b90ad7i263hfDowBqsxnyuAptzrmvFClE|0|00200212\
    210|12212220220|221212221120;0hkijbac924318765egfdAuDtpyBlzqnvFCrxomEws|0|220211200|2221\
    21022200|1120021202;7fb1jicd293ek4hga8605wFpyrtznCxuvlmsAEBoqD|0|2212221|2022121022|2220\
    211;jec54a38d692g17bfikh0rEuBnoxCAvzDmypFwtqls|6|0|1|1211021;46bdk1203ej5cag7hi98frqtslD\
    vzmoAxCwFpyBnEu|0|112020200210|202021212020|2022021100;hik0jfc6382eb47ag9d15wzntCyFprAsE\
    mluxvBoqD|0|20222202|20212211020|21212002122;edgf09k7316iahb2854cjlxvuwCDEFrsqtonpmAyzB|\
    0|121020|102202200202|2022100202;gedf0k18c962j3ib57ah4xsDynCroAvluwBtFmpqzE|0|0222211020\
    0|22021102|2102120202;gf0edc81k69j23ib5h47azsuFoCwntvmDrBAylpExq|0|00221022210|122121121\
    02|11021120020;g296je0dfb3i5h47a81ckACxorvqnFputDsmwEByzl|0|2221002021|0021221200|221022\
    2110"

@[expose] def repData7 : String :=
  "5068791dha2fkb3gic4ejulvxwmqyCnrBEoszFptAD|0|1121222|112122|022122020;50687hd19kf2aig3bj\
    e4cylzBAmCuqnDxsoEvtpFwr|0|122222120|1222022020|202221120;52akf19hd06874jec3gbiqlrtsnvFA\
    muCypxEzowDB|0|12122221|12112221|22002112220;54ecj19hd3igb2fak0876qlrtsowDBpxEzmuCynvFA|\
    0|002121100|02102112020|2212112210;159dh2034a6iek8gcf7bjnqvAFlmopruBEtCwzsyDx|0|21021202\
    1202020|0210020020200|2202100210;50687dh91fka2gib3ejc4ClDFEmyqunztwoArxpBsv|0|1222221211\
    00|1222112221|202021220020;159dh4302ei6acg8kjb7foqwBDlpnmrxACtEvyszFu|0|12122002112|2020\
    2222120|002210020;5kf2ahd190687j4ceibg3ylzBAnDxsmCuqpFwroEvt|0|202202112200|2222102121|2\
    2120020222;53igb19hd4ecj07682kfaqlrtspxEzowDBnvFAmuCy|0|102120|1221120210|02110210202;5c\
    j4e91dhbgi3ak2f0876ulvxwoszFptADmqyCnrBE|0|12212221002|212112122110|1221221002;159dh3420\
    iea6gck8bjf7pqxzElomnrwyFtDuAsBCv|0|12122102112|1210221220|20221222221;5fka2dh910687ec4j\
    g3ibClDFEnztwmyqupBsvoArx|0|0220210220|2222002121|0221002222;5bgi391dhcj4e0768afk2ulvxwp\
    tADoszFnrBEmqyC|0|2121102020|212112122100|2122121102;5i3bghd19jce40768k2afylzBApFwroEvtn\
    DxsmCuq|0|12121021020|0022021212|11212020220;5e4jcdh91gb3if2ka0876ClDFEoArxpBsvmyqunztw|\
    0|10022202122|00210222211|122221022200;ha47gk0ij2be8fc63591dnyDsxBuErAqvFlmopzCtw|0|2021\
    1212122|200200221120|2202222102;h4ag7ji0ke82bcf36591doyEtvBwDqArxClpnmzFsu|0|00212210|20\
    202202|2112022212;e45jc1ia6397k28hb0fgdqrlstowDBxpzECymuAFvn|0|112210200200|21121202120|\
    02121102210;f2ka51jb70ged498i36hcqtslrnvFACymuzExpwoBD|0|20020211002|02021210202|2112102\
    2112;70865b1fjc2di93eka4ghutApDmqyCFsozBrEnxlvw|0|202110202|202202121100|2211220020;6057\
    8ie1ajg29hf3ckd4byrpwFmCuqvoEtDxnszABl|0|002022021220|12220020220|2021200212;hg74aijk0b2\
    8e36cf591dpyFrwBvCsAtuDlomnzEqx|0|12022110|1211221120|0200211222;i35bg1e6a49f80khj27cdqr\
    lstpxEzwoBDFAnvyCum|0|2212221220|122220221100|12102002210;k2f5a1g8c0jhi46bd39e7qstrlnvFA\
    yCumxpzEDBow|0|12222002021|02221020210|1212022122;c4j5e18gk3fh62i7d09abqstrlowDBzExpumyC\
    FAnv|0|020212212|02220210|212121120;b3gi517fj4k6d09ca2eh8qtslrpxEzDBowAFvnumyC|0|0221212\
    2202|02122212200|020212202;80756c1gkb2eha3dj94fiusFzomqyCAtDpwlxvErnB|0|12202222021|0212\
    22002100|2222022220;60578eia1gj92fhc3dkb4CroAxmyquvpsBDFlEzwtn|0|2102120200|22212002202|\
    211021200;kh0ji2af5b46de7398gc1AnqFvyBlzDuptsEmwxroC|0|21102020200|1121220222|21021222;7\
    0865fjb1dic2ek93gha4CtwnzmyquFElDBvspxorA|0|11020020210|202212212200|02210022220;c9ba04e\
    j58kg1f36hi72dwoDqBuxlvsAmEFrpyzCnt|0|102220022121|122221121021|1200222112211;fd0eg2a5kc\
    3h67j1bi894FnqvACEDlzusowryptBxm|0|1022221021210|020220200|2002102122;80756kg1che2bjd3ai\
    f49ysxDnmCuqABzlwpFrEvot|0|2202112221|022212220200|20021211220;b9c0a3i5g7f1je8h2k4d6xpzE\
    quwvltFBmDysnArCo|0|002221022121|1222002021|12122202122;j3d8ac5e4hik0fb716g92zoFusEpqxyl\
    BAvmDrtnwC|0|10212200|12202121122|20022002112;48fi9cje51320gah7kdb6sozuFwEmAqtlrDynxBvpC\
    |0|02102021|202221222|112112121;k4bd6a25fh0jig1c873e9BnurEDqwoyAzlxFtmsvCp|0|12122100211\
    2|0202222112|1212222002;37k9ebg5i1402fh6cja8dtpDAuxBFmqsrlEvyozCwn|0|021102022220|210022\
    2211|0022002212;da3j8f0ge2c7i59h1kb46nCzwtEurBFqAvDyxslmop|0|222202110211|021121120210|2\
    2022120200;46kbde5cja7hg1032i8f9roxCADmvzBnEuwpyFqlts|0|1211002020|10212221211|020020;c2\
    7dij54e6f3hgk189a0bvotyEFnAqzmrDulxwspCB|0|2112222|02022112112020|002022211220;a3j8dkf52\
    7hg4e6i19cb0xnyDsEzqpBtFmuwvlrCAo|0|10220022102|12102002200|02102112211;3i5gbhc6fjda8021\
    4k7e9yzlABpFwrEotvxsnDquCm|0|2122021100|102221100202|121221211;4e5cjdbk6gh7af89i0231CDlE\
    FoArxBpvsqumywtzn|0|2122110020|200200222020|20210202021;2ka5fhb8e0413j6g9idc7yABzlnDxsqu\
    CmFprwvtoE|0|122002221|0212120211|22122212;2fak5dci70341eh8bg69jCFElDnztwqumyvsBpAoxr|0|\
    122102221|202122210|1120222002;7jbf14ahgcdi2e3k95806oBDqwtEvyFuszmnplxrCA|0|10021200220|\
    11210221210|22112212110;cj54e3h6fdi278kg1a09bEzpxqoytvFlCDuBnrsAwm|0|0221122110|21120200\
    20|202110212002;80756ehb2gkc1fi94dja3CAxromyqusBvpElFDwznt|0|10212220221|02110022121|020\
    22210221;c4j5e81kgf36hi2d790bawsEAmoqBDztCnulvxFrpy|0|2110211|1021202210|0212210220;7086\
    5id2cjf1bhg4ake39yFwprmCuqtEovxDsnBlzA|0|12121220022|0022021121|120220020;i6ea1j0hkg53b2\
    7cd98f4vyotErmDzpCsBwuxlFqnA|0|21222002200|22212102002|02112022120;b3gi571jfk4d690ace28h\
    xtBmFpqzEDsnyArCoulwv|0|2100211|11221020222|202222112;60578c3fhb4dka1ei92gjuzosFmqyCDpAt\
    vxlwrEBn|0|112110220|21022102220|1222102122;70865ke39hg4ajf1bid2cyxsnDmCuqBAlzFrwptovE|0\
    |12022122020|202102021|12221222;f2ka57bj1deg0i894ch63FtxmBnAqvCDlEzusowpry|0|021122211|0\
    2221021|1222021212;60578b4dkc3fh92gja1eiuDpAtmqyCzosFrBnEvwxl|0|20212021020|021022212100\
    |1122021200200;j7fb1hk0ia38dg9624e5cByzlAtxFmEnruoDwqvspC|0|12220022112|122220022210|121\
    020;7ek93gha40865fb1jd2icCBspvxAormyquFlDEtzwn|0|222212002122|002122112|21222022021;64bk\
    d3chf05782jg91eaiqzpExDowBmuCyrstlvFnA|0|02020212|1022121221|2022021100;79ek3b1fjah4g058\
    6cdi2utApDxlvwBrEnFsozmqyC|0|211020221220|22110020212|22112221220;6h3cfie1akbd40857j29gy\
    rpwFzABlDxnsvoEtmCuq|0|21020022202|02202121122|1212212002;c09abh3f6k1g8i2d7j4e5yzlABuqmC\
    sxDnoEvtFprw|0|10212020202|2102221221|02221212202;aie61h4g7j83d09bckf52yBAlzrwFpEotvnDxs\
    uqmC|0|022102122200|221022212|1102121122210;89i4fc1gkadj3bh2e0567usFzowlxvErnBmqyCAtDp|0\
    |11221120220|22021100212|1022002122110;7f1jbgha4dc2ie3k90658CBspvtzwnFlDEmyquxAor|0|1122\
    122210|120212220|1120211202;62g9j3chf1iea4dbk0785qzpExvFnArstlmuCyDowB|0|10210222100|222\
    0021200|10022122002;cf36hkg815e4ja09b2di7nsxyDzCtwoplmFvqAuBrE|0|2200211022|022102122100\
    |1210220211;926gj0acb15dh3k7e4fi8qumyCvnAFlrtswBDoxEpz|0|112|20202220021100|021002102;g7\
    h4ae0dfk8c1962j35ibxCAroBmtFsynDpqzEvuwl|0|21220222110|121211220220|22110021200;4e5cjbd6\
    khga78fi92013ADptuoCxrBlyzqFnvwEsm|0|122221222020|20021022110|1122002221;4ce5j89fikb6dga\
    h71032swAEmouFzDxynqlrtBvpC|0|10022212|121002120|0211202112;159dh8kcg7fjb02436aeimswAEln\
    potxBFrDvzqyCu|0|1021102112220|02211212022|2110212102;36cfh4012b5igk7e9d8ajDqoBwzmvrpuAt\
    ECFlxyns|0|12220212|22002112220|02221212222;fk5a23c6hegd071bj984ixzpqEnsyDCoArwulvtFBm|0\
    |1020222020210|20211211200|202212020;kaf2573e9hji0g81c4d6bBxtmFnEuryzlADqwospvC|0|002222\
    1202|002002211200|10020212;9jg620acbhd51k3e7i84fyuCqmvEtolBAzwrpFxnDs|0|12211220|1122211\
    2002|11221022110;fak52849idg0e3hc6j7b1EwsAmnBruCDFltoyvzqpx|0|02212212|0221021210|021122\
    022;2ka5f8ehb1304g9j6c7idsAEwmnxDyqrtlFouzvCpB|0|121212211|11212220221|1202212210221;g6j\
    29fd0e3b5ih47ack81zCtwnvDrmpExqsFouBlAy|0|20202212211|12112020022|112220222121;cf36h81kg\
    4j5e9ba0i72dwsEAmztCnoqBDFrpyulvx|0|220222102120|021020021|2110221002;bk4d671jf3gi5e8h29\
    c0axtBmFDsnypqzEulwvArCo|0|2211210220|021021202100|1021022022;f3c6ha2k5d0eg849ij17bEnuBr\
    zqpxCFlDtvoywAms|0|02210021220|222112022221|02022220;7hg4ake390865i2cdjbf1yxsnDBAlzmCuqt\
    ovEFrwp|0|202121002|11202120211|1022112002;fdeg07bj12ka5c63hi489FtxmBCDlEnAqvwpryzuso|0|\
    200212221211|21121200212|002212210;8dja3fi940756gc1ke2hbCwtznEFDlmyquAroxspBv|0|10022122\
    200|121212220|12122221;b6d4kfj173gi5h2e8c9a0ztCnwDvmrpExquoFsAyBl|0|12202220221|21211220\
    212|2022110200;e8bh2i16afg0d4c5j9k73wrpFyAsEmCtnzxluvoqBD|0|1121122221|022120202200|2021\
    122220;b28ehg5i36kd49ac0jf71vpsBCAnqFDmzrtoEyulxw|0|2112222|0211222002200|022220021020;a\
    h4g7ei168jd32k5fb09cAroxCByzlEwmsupDtnFvq|0|00221120|1212210220|1212202020;2i7dchb8ejg96\
    0341k5fayABzlFprwvtoEnDxsquCm|0|120202220|22122021021|222211202002;i7c2de1a6kjh09f483bg5\
    xroCAFtmBysDnpqzEwlvu|0|1121122221|211202102220|122112121022;big53c09adk462h8e7jf1Fuszop\
    yrwDCEltmBxAqnv|0|1220210022|210022|2122221122;jki0hg96283da17bfce45svpBCyxnDEwAmouFztlq\
    r|0|1102202200|11202211202|221021020202;i948fj0hk2cd7gb536a1evyotEwuxlFqnArmDzpCsB|0|121\
    22221|120212202102|2122112022;7bj1fa4ghcdi29k3e0658uBEnrtDApFozsmqyCxwlv|0|00200202110|2\
    02121222|20221221;ic7d26a1eh0kjf9843bg5zrmvDFuosyBAlpExqwnCt|0|12222210021|20222102002|1\
    120220211;df0ge7i2cj8a3195hb4k6tFmxBCwznEyovDpuAlrsq|0|11211021020|21200222022|222202112\
    2;hk0ij8eb2g74ac36f19d5sAmEwyxnDBCvplrqtzoFu|0|022220210210|0202200220|11212102220;4kb6d\
    fi895jce2013ahg7nwtCzDyxsoplmBruEqFvA|0|21021022110|0211210220|1022100211;defg072cikb463\
    8ja9h51xFtmBCAroDnyslvwuEqpz|0|12220220200|22002221120|022021121;d4b6kgef0h5917ci2aj83BC\
    psvDoqwlAyzErunFxmt|0|1202112212112|222112112102|2110211212;ad8j325fk7hg4i1e6c90bFnAqvEl\
    DCBmxtuoszrpyw|0|1102002210|121210020200|022112212;a74hg90cb38dje6i1k52fxuwvlBmtFEqpznyD\
    srCAo|0|2022002121|112102110|02002120210;g9j62b53ic1k8ah740defuptADvlwxsoFzCmyqBnrE|0|22\
    202222|2102102212|20022212021;6fhc34bkd8750i1ae9j2gwDBqoztCnmAEsvulxrpFy|0|112022022211|\
    221002|2211222212;3chf6a8jdbg5i01429ke7uEBrnzsFopADtxwlvqmCy|0|21221211002|11221121022|0\
    21122112122;c27di6f3hj54e9a0bgk18vzmrDFnAqotyEsCBpuwlx|0|220210211|110200210|22002022110\
    0;6db4kjg293fch8075aei1EvtyoDClFzpxqrBunmswA|0|22022202210|022022112121|21022222120;3hfc\
    64012gi5b7k9eajd8BqwDozyAlpCvsEunrxmFt|0|020211220|12102102020210|120212112021;4dk6b3021\
    jec5ag7h8fi9EqxpzDClFoytvwmsABurn|0|022121020|2120222002102|20021212112110;4bd6ka7hgcje5\
    9f8i0123uBEnrDtpAoFszqmCywxvl|0|21221202|1002020022|12021202"

@[expose] def dcData1 : String :=
  "012346587a9cbedgfihkjrmvDzqltsunBEypFwCoxA|0|2232003|030221300|20211;034129abc7856kjihed\
    gfxuwvlqEzpmBFtCroAynsD|0|32321220|2222332|20211"

@[expose] def dcData2 : String :=
  "012346587a9cbedgfihkjrmvDzqltsunBEypFwCoxA|0|2220303|20232200|32202213;056783412bc9aijhk\
    gedfpqzExmonluDAtCBvsywFr|0|23022231|3133213|0321230"

@[expose] def dcData3 : String :=
  "012346587a9cbedgfihkjrmvDzqltsunBEypFwCoxA|0|2232103|200211032|222232;034129abc7856kjihe\
    dgfxuwvlqEzpmBFtCroAynsD|0|13200311|20303332|203032"

@[expose] def dcData4 : String :=
  "012346587a9cbedgfihkjrmvDzqltsunBEypFwCoxA|0|32220303|110323120|1030312100;056783412bc9a\
    ijhkgedfpqzExmonluDAtCBvsywFr|0|2231103|312232303|13123003"

@[expose] def dcData5 : String :=
  "012346587a9cbedgfihkjrmvDzqltsunBEypFwCoxA|0|1300200|1102120|3002213203;05678egfdjikhcba\
    94321oCrAxmplnyvEtqBDwusFz|0|23302112|1102120|032132100"

@[expose] def dcData6 : String :=
  "012347856bc9afgdejkhitmFBxqsrluADpyEvoCwzn|0|123121|302113|00322030;03412defgjkhi8765a9c\
    bECDFlqxpzyovturBnmAsw|0|00303330|23203100|30331300"


@[expose] def pGens : Array Tab := #[pT, qT]

@[expose] def pGensWith (r : Tab) : Array Tab := #[pT, qT, r]

@[expose] def pGensWith2 (r g : Tab) : Array Tab := #[pT, qT, r, g]

@[expose] def mRs : Array Tab :=
  #[aSixGen1T, aSixGen2T, aSixGen3T, aSixGen4T, aSixGen5T, aSixGen6T]

@[expose] def hyper : Array (Array Nat) :=
  #[#[3, 18, 6, 19, 7, 4], #[5, 16, 9, 10, 8, 14], #[3, 16, 8, 6, 14, 4],
    #[5, 9, 10, 18, 7, 19], #[7, 18, 8, 19, 16, 14], #[3, 9, 10, 4, 6, 5]]

@[expose] def tgtGens : Array (Array Tab) :=
  #[gensS, pGensWith aSixGen1T, pGensWith aSixGen2T, pGensWith aSixGen3T, pGensWith aSixGen4T,
    pGensWith aSixGen5T, pGensWith aSixGen6T]

@[expose] def dcData : Array String := #[dcData1, dcData2, dcData3, dcData4, dcData5, dcData6]

@[expose] def decodeChar (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else if c.isLower then c.toNat - 87 else c.toNat - 29

structure Row where
  tab : Tab
  target : Nat
  words : List (List Nat)
deriving Inhabited

@[expose] def parseRow (s : String) : Row :=
  match s.splitOn "|" with
  | t :: g :: ws =>
    ⟨(t.toList.map decodeChar).toArray, g.toNat!, ws.map fun w => w.toList.map decodeChar⟩
  | _ => ⟨#[], 0, []⟩

@[expose] def parseRows (s : String) : Array Row := ((s.splitOn ";").map parseRow).toArray

@[expose] def tabsS (_ : Unit := ()) : Array Tab := (enumBFS 42 gensS 20160).tabs

@[expose] def closureOK (idxS : Std.HashMap Tab Nat) (ES gens : Array Tab) (E : Enum) : Bool :=
  enumOK 42 gens E && allBelow gens.size fun j => found idxS ES gens[j]!

@[expose] def wordTab (gs : Array Tab) (w : List Nat) : Tab :=
  w.foldr (fun j acc => comp 42 gs[j]! acc) (idTab 42)

@[expose] def wordsOK (gs tg : Array Tab) (ws : List (List Nat)) : Bool :=
  ws.length == tg.size && (ws.all fun w => w.all fun j => decide (j < gs.size)) &&
    allBelow tg.size fun i => wordTab gs (ws.getD i []) == tg[i]!

@[expose] def rowOK (idxS : Std.HashMap Tab Nat) (ES : Array Tab) (row : Row) : Bool :=
  found idxS ES row.tab && decide (row.target < tgtGens.size) &&
    wordsOK (pGensWith row.tab) tgtGens[row.target]! row.words

@[expose] def hyperOK (EM : Array Tab) (o : Array Nat) : Bool :=
  o.size == 6 && (allBelow 6 fun i => decide (o[i]! < 42)) &&
    (allBelow 6 fun i => allBelow 6 fun j => i == j || o[i]! != o[j]!) &&
    (allBelow EM.size fun k => allBelow 6 fun i => anyBelow 6 fun j => EM[k]![o[i]!]! == o[j]!) &&
    (allBelow EM.size fun k =>
      !(allBelow 6 fun i => EM[k]![o[i]!]! == o[i]!) || EM[k]! == idTab 42)

@[expose] def perfOK (EM : Array Tab) : Bool :=
  let inv := EM.map (invTab 42)
  let D := derivedData 42 EM inv
  derivedOK 42 EM inv D.1 D.2 && D.1.size == EM.size

@[expose] def dcSet (EM dc : Array Tab) : Std.HashSet Tab :=
  dc.toList.foldl (fun s g => EM.toList.foldl (fun s m =>
    let mg := comp 42 m g
    EM.toList.foldl (fun s m' => s.insert (comp 42 mg m')) s) s) {}

@[expose] def maxOK (idxS : Std.HashMap Tab Nat) (ES : Array Tab) (r : Tab) (EM : Array Tab)
    (dcs : Array Row) : Bool :=
  let idxM := indexOf EM
  let DC := dcSet EM (dcs.map (·.tab))
  (allBelow dcs.size fun i =>
    found idxS ES dcs[i]!.tab && wordsOK (pGensWith2 r dcs[i]!.tab) gensS dcs[i]!.words) &&
  (allBelow ES.size fun k => found idxM EM ES[k]! || DC.contains ES[k]!)

@[expose] def aSixOK (idxS : Std.HashMap Tab Nat) (ES : Array Tab) (r : Tab) (E : Enum)
    (o : Array Nat) (dcs : Array Row) : Bool :=
  closureOK idxS ES (pGensWith r) E && E.tabs.size == 360 && hyperOK E.tabs o && perfOK E.tabs &&
    maxOK idxS ES r E.tabs dcs

@[expose] def coverSet (m : Nat) (reps EP EPi : Array Tab) : Std.HashSet Tab :=
  reps.toList.foldl (fun s r => (List.range (m - 1)).foldl (fun s k =>
    let rk := powTab 42 r (k + 1)
    (List.range EP.size).foldl (fun s i => s.insert (conjTab 42 EP[i]! EPi[i]! rk)) s) s) {}

@[expose] def coverOK (m : Nat) (ES : Array Tab) (cover : Std.HashSet Tab) : Bool :=
  allBelow ES.size fun k =>
    ES[k]! == idTab 42 || !(powTab 42 ES[k]! m == idTab 42) || cover.contains ES[k]!

@[expose] def repsOK (m : Nat) (rows : Array Row) : Bool :=
  allBelow rows.size fun i => powTab 42 rows[i]!.tab m == idTab 42

@[expose] def l34SylowChecks (ES : Array Tab) (idxS : Std.HashMap Tab Nat) (EP : Enum)
    (EMs : Array Enum) : Bool :=
  let EPi := EP.tabs.map (invTab 42)
  let rows5 := parseRows repData5
  let rows7 := parseRows repData7
  closureOK idxS ES pGens EP && EP.tabs.size == 9 && invsOK 42 EP.tabs EPi &&
    mRs.size == 6 && hyper.size == 6 && dcData.size == 6 &&
    (allBelow 6 fun j => aSixOK idxS ES mRs[j]! EMs[j]! hyper[j]! (parseRows dcData[j]!)) &&
    repsOK 5 rows5 && repsOK 7 rows7 &&
    coverOK 5 ES (coverSet 5 (rows5.map (·.tab)) EP.tabs EPi) &&
    coverOK 7 ES (coverSet 7 (rows7.map (·.tab)) EP.tabs EPi) &&
    (allBelow rows5.size fun i => rowOK idxS ES rows5[i]!) &&
    (allBelow rows7.size fun i => rowOK idxS ES rows7[i]! && rows7[i]!.target == 0)

@[expose] def l34SylowCheck (_ : Unit := ()) : Bool :=
  let ES := tabsS ()
  l34SylowChecks ES (indexOf ES) (enumBFS 42 pGens 9)
    (mRs.map fun r => enumBFS 42 (pGensWith r) 360)

end CFSG.StandardType.L34Sylow
