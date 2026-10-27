module

public import Certificates.Data.CFSGNative.J4.Data

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

@[expose] def ptsOfString (s : String) : List (Nat × List Int) :=
  (s.splitOn " ").filterMap fun t =>
    if t.isEmpty then none
    else
      let cs := t.toList
      some ((String.ofList (cs.takeWhile Char.isDigit)).toNat?.getD 0,
        lettersOfString (String.ofList (cs.dropWhile Char.isDigit)))

@[expose] def idxWordsOfString (s : String) : List (List Nat) :=
  (s.splitOn " ").filterMap fun t =>
    if t.isEmpty then none
    else if t = "_" then some []
    else some (t.toList.map fun ch => ch.toNat - 'a'.toNat)

@[expose] def zWord : List Int :=
  lettersOfString "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabA"

@[expose] def conjWords : List (List Int) :=
  ["", "a", "b", "c", "aa", "ba", "ca", "ab", "bb", "ac", "baa"].map lettersOfString

@[expose] def letters : List Int := [1, 2, 3, -1, -2, -3]

@[expose] def letterRows : List (List Nat) :=
  [[2, 16, 128, 512, 731, 440, 1577, 1457, 1652, 925, 29],
   [4, 32, 256, 667, 1024, 1043, 795, 640, 1652, 647, 941],
   [8, 64, 278, 22, 365, 1241, 1695, 1796, 457, 16, 239],
   [925, 1, 349, 1730, 2, 232, 1344, 4, 1548, 8, 1535],
   [1087, 1726, 1, 184, 689, 2, 878, 76, 4, 204, 16],
   [1745, 962, 458, 1, 512, 1796, 2, 2014, 12, 618, 812]]

@[expose] def orbits : List (Nat × List (Nat × List Int) × List (List Nat)) :=
  [(1, ptsOfString
    "1 2a 4b 8c 925A 1087B 1745C 16aa 32ba 64ca 1726Ba 962Ca 128ab 256bb 278cb 349Ab 458Cb 512ac \
    667bc 22cc 1730Ac 184Bc 492bA 1720cA 1715BA 162CA 1043cB 155BB 752CB 705aC 1205bC 812AC \
    1392BC 587CC 731aaa 1024baa 365caa 689Baa 440aba 1241cba 232Aba 1796Cba 1577aca 795bca \
    1695cca 1344Aca 878Bca 1986aBa 783cBa 647ABa 1060BBa 405CBa 1633aCa 1352bCa 833ACa 1364BCa \
    1656CCa 1457aab 640bab 76Bab 2014Cab 1652abb 457cbb 1548Abb 12Cbb 852bcb 498ccb 1874Acb \
    1034Bcb 1843cAb 1868AAb 1373BAb 1300CAb 2044aCb 1419ACb 1312BCb 204Bac 618Cac 1765abc \
    1575cbc 1360Abc 678Cbc 59ccc 350Acc 1038Bcc 145bAc 292cAc 178AAc 1368CAc 1234aBc 1580ABc \
    583BBc 1748abA 103bbA 287CbA 290bcA 601ccA 987AcA 519cBA 1669ABA 1679CBA 1049aCA 237ACA \
    1776BCA 792CCA 724acB 1929bcB 1400aBB 1591cBB 196BBB 870aCB 1446ACB 7aaC 387caC 2001BaC \
    871CaC 1613abC 58bbC 1773CbC 891bAC 371AAC 115BAC 1193CAC 803aBC 525cBC 1625ABC 1574CBC \
    1958aCC 411BCC 1914CCC 1443baaa 676Caaa 29abaa 941bbaa 239cbaa 1535Abaa 739bcaa 2030Bcaa \
    1357aBaa 680cBaa 1660baba 879caba 579Baba 727Caba 860acba 1510Acba 1284Bcba 1811bAba \
    920BAba 217CAba 1396aCba 1630bCba 1080caca 1113Baca 146Caca 588bbca 234cbca 856Abca \
    1045bcca 25Bcca 1977cAca 890BAca 802CAca 735cBca 1074ABca 1897CBca 1348BaBa 1915acBa \
    291bABa 1610cABa 717AABa 293aBBa 1098ABBa 19BBBa 1506CBBa 412aCBa 496bCBa 1226ACBa 1735BCBa \
    713CCBa 1935BaCa 576abCa 1967cbCa 113AbCa 2028bACa 1870cACa 1945BACa 539aBCa 185bCCa \
    441BCCa 1089CCCa 926caab 1835Caab 1812cbab 1460Cbab 1951cBab 983BBab 382bCab 706cabb \
    1418Cabb 1559Acbb 1953Bcbb 511cAbb 616AAbb 101BAbb 141CAbb 923bCbb 459CCbb 744bbcb 1853cbcb \
    430Cbcb 2012bccb 931Accb 1668cAcb 138CAcb 828ABcb 1558BBcb 1705cAAb 131CAAb 691ABAb \
    1592CBAb 684ACAb 609BACb 280aBac 1564aCac 1844bCac 867ACac 1711CCac 1187cabc 682acbc \
    1053bcbc 606Bcbc 1713AAbc 1332bCbc 1597BCbc 369accc 1514cccc 1232AAcc 653aBcc 431cBcc \
    1896abAc 1030ccAc 89bCAc 334aaBc 1330CaBc 1698bABc 1318cABc 1795abbA 991CbbA 1389accA \
    21AccA 1428BccA 866BAcA 686bABA 1198BABA 333BBCA 1857bbcB 1696AbcB 68CbcB 1307BaCB 456cBaC \
    746aCaC 626CbAC 1590ABAC 1091aaBC 1412BABC 957caCC 780aBCC 2046cBCC 192BBCC 1769Cbaaa \
    1306Cabaa 48cBcba 580abcca 156cbcca 930AbCBa",
   [[1], [2], [4], [8], [16], [32], [64], [128], [1, 2, 16, 32, 64, 925, 1087, 1745],
    [2, 4, 8, 32, 64, 128, 1087, 1745], [1, 2, 4, 8, 16, 32, 1087]]),
   (3, ptsOfString
    "3 18a 36b 72c 924A 641B 1299C 715aa 1056ba 301ca 1039Ba 450Ca 312ab 1487cb 437Ab 1742Cb \
    1065ac 384bc 1673cc 898Ac 982Bc 488bA 1712cA 413AA 652BA 1651CA 1582aB 1820cB 913AB 1215BB \
    869CB 1184aC 509bC 109AC 1075CC 535aaa 419baa 469caa 471Baa 164Caa 421aba 1982bba 1078cba \
    1303Aba 1064Cba 1358aca 504bca 1048cca 742Aca 1152Bca 655aBa 423cBa 508ABa 552BBa 2036CBa \
    1532aCa 1999bCa 841ACa 1432BCa 1042CCa 1815aab 1276bab 1131cab 527Bab 1289Cab 1891acb \
    2045bcb 501ccb 692Acb 270Bcb 1507bAb 615cAb 1058AAb 1733BAb 1485CAb 648aCb 778bCb 1837ACb \
    1529BCb 1171CCb 935aac 1313bac 1173Bac 760Cac 965abc 1268bbc 1741cbc 1544Abc 2002Cbc 309bcc \
    2021ccc 172Acc 1047Bcc 1619bAc 1693cAc 1537AAc 1594BAc 1658CAc 1082aBc 121cBc 542ABc \
    2020BBc 1458CBc 1620abA 359bbA 1181cbA 1378AbA 213CbA 1362acA 953bcA 591ccA 1305AcA 547BcA \
    875bAA 1704cAA 520AAA 1663BAA 712CAA 1196aBA 1556cBA 1939ABA 57BBA 1151CBA 1752aCA 518bCA \
    961ACA 896BCA 339CCA 168aaB 1666baB 1382caB 1753BaB 1099CaB 1455acB 197bcB 347ccB 1126AcB \
    720BcB 631bAB 1976cAB 1439AAB 1546BAB 361CAB 1117aBB 791cBB 274ABB 215BBB 1326CBB 762aCB \
    767bCB 364ACB 1946BCB 635CCB 1044aaC 1342baC 818caC 94BaC 1014CaC 1037abC 1123bbC 1262cbC \
    1952AbC 1486CbC 1175bAC 846cAC 426AAC 2026BAC 28CAC 876aCC 922bCC 34BCC 827CCC 468aaaa \
    1955baaa 35caaa 253Baaa 1203Caaa 623abaa 195bbaa 604cbaa 1404Abaa 1477Cbaa 1973acaa 747bcaa \
    33ccaa 394Acaa 1449Bcaa 1957aBaa 97cBaa 395ABaa 265CBaa 1161aCaa 433ACaa 79BCaa 272CCaa \
    483baba 1140Baba 1997Caba 438abba 1654bbba 710cbba 1163Abba 409Cbba 1006acba 670bcba \
    1097Acba 1052Bcba 277cAba 304AAba 37BAba 933aCba 1317bCba 981ACba 170BCba 1401baca 1785caca \
    1405Baca 299Caca 1167abca 1383bbca 1520cbca 1376Abca 725Cbca 198acca 1334bcca 404ccca \
    831Acca 537Bcca 1583bAca 1028cAca 1272AAca 1363BAca 186CAca 1452aBca 2027cBca 1531ABca \
    92BBca 1266CBca 1214aaBa 952baBa 1628caBa 696BaBa 751acBa 451bcBa 842ccBa 1057AcBa 714BcBa \
    1127bABa 1254cABa 1085AABa 300BABa 799CABa 1247cBBa 1570ABBa 118BBBa 1391CBBa 1423aCBa \
    2006bCBa 1800ACBa 328BCBa 600CCBa 1994baCa 1033caCa 316BaCa 51CaCa 1278abCa 1402bbCa \
    485cbCa 700AbCa 590CbCa 1399bACa 1880cACa 1563AACa 1825BACa 1204CACa 771aBCa 1881cBCa \
    1335ABCa 593BBCa 1791CBCa 726aCCa 1933bCCa 1055BCCa 750CCCa 1981aaab 634baab 261caab \
    233Baab 614abab 446bbab 1472cbab 1998Abab 63Cbab 1438acab 1562bcab 759ccab 325Bcab 271aBab \
    344cBab 1035ABab 756BBab 1714CBab 1862bCab 1708ACab 114bacb 824cacb 863Cacb 1353bbcb \
    1041cbcb 599Abcb 1160Cbcb 1549accb 1784bccb 354Accb 1451Bccb 276bAcb 950cAcb 443AAcb \
    562BAcb 378CAcb 1252aBcb 137cBcb 402ABcb 1539BBcb 517CBcb 1115abAb 117bbAb 1068cbAb \
    1475AbAb 1771CbAb 1182acAb 1195bcAb 776ccAb 1889AcAb 288BcAb 1950bAAb 1142cAAb 1302AAAb \
    154aBAb 122cBAb 627ABAb 1984BBAb 385CBAb 1907aCAb 2013bCAb 693ACAb 1968BCAb 998CCAb 668baCb \
    1794caCb 56BaCb 1461CaCb 2041abCb 1608bbCb 399cbCb 199AbCb 210bACb 1255cACb 1809AACb \
    1116BACb 340CACb 1168aBCb 770ABCb 1282BBCb 1832CBCb 1893aCCb 1637ACCb 108BCCb 993CCCb \
    370aaac 836baac 858caac 2003abac 462bbac 1527cbac 134Abac 757Cbac 2037aBac 1944cBac \
    1849ABac 1747BBac 489CBac 358aCac 868ACac 179CCac 1779aabc 1132babc 348cabc 2004Babc \
    673Cabc 102abbc 805bbbc 1494cbbc 268Abbc 62Cbbc 666acbc 814bcbc 1201Acbc 1912Bcbc 945bAbc \
    821AAbc 100BAbc 327CAbc 1191aCbc 741bCbc 1724ACbc 1876CCbc 1429abcc 1379cbcc 1062Abcc \
    531Cbcc 1878accc 978bccc 1386cccc 1990Bccc 1288bAcc 733cAcc 247BAcc 273CAcc 596aBcc 220cBcc \
    1852ABcc 1525CBcc 1888abAc 1557bbAc 1861cbAc 809AbAc 1623CbAc 1640acAc 1077bcAc 499AcAc \
    1703BcAc 302bAAc 1642AAAc 1251BAAc 1943CAAc 755aBAc 1309cBAc 990ABAc 1129BBAc 1921CBAc \
    1242aCAc 153bCAc 1694ACAc 1799BCAc 1923CCAc 366aaBc 1293caBc 1189BaBc 1515CaBc 1864acBc \
    407bcBc 245AcBc 1370BcBc 1340bABc 61cABc 1940AABc 1146BABc 611CABc 1802ABBc 1017BBBc 88CBBc \
    171aCBc 1898bCBc 796ACBc 1109BCBc 568CCBc 2034aabA 1841babA 258BabA 654CabA 375abbA 721cbbA \
    357AbbA 979CbbA 1934ccbA 507AcbA 1643BcbA 753bAbA 800cAbA 1626AAbA 1478BAbA 449aCbA \
    1183bCbA 1926ACbA 1453BCbA 711CCbA 651aacA 738bacA 1684cacA 1909BacA 736CacA 313abcA \
    1279bbcA 887cbcA 949AbcA 1644CbcA 1830accA 1991cccA 331AccA 410BccA 838bAcA 85cAcA 1710AAcA \
    2032CAcA 567aBcA 1153cBcA 892ABcA 125CBcA 106abAA 324bbAA 1778AbAA 1417acAA 1314bcAA \
    820ccAA 985AcAA 42BcAA 6cAAA 1738AAAA 116BAAA 619CAAA 1112aBAA 1118ABAA 825BBAA 152CBAA \
    391bCAA 910ACAA 854BCAA 1463CCAA 1701baBA 231BaBA 573CaBA 475acBA 1066bcBA 132ccBA 1192AcBA \
    620BcBA 506bABA 353aBBA 1450cBBA 1588BBBA 980CBBA 1989aCBA 794bCBA 1110ACBA 1013BCBA \
    754CCBA 1578baCA 31caCA 503BaCA 1179CaCA 781abCA 326cbCA 98CbCA 1388bACA 74cACA 221AACA \
    2005BACA 1757cBCA 1536ABCA 1464CBCA 660aCCA 1821CCCA 1545aaaB 1032baaB 971caaB 246BaaB \
    219CaaB 1569abaB 906bbaB 1979cbaB 1522AbaB 360acaB 1009bcaB 566ccaB 1479BcaB 193aBaB 23cBaB \
    1518ABaB 1480BBaB 586CBaB 521bCaB 1505ACaB 1596CCaB 242aacB 947cacB 610BacB 1826CacB \
    159bbcB 133cbcB 1924AbcB 148accB 976bccB 1552AccB 994BccB 1413bAcB 1023cAcB 267AAcB 734aBcB \
    230cBcB 351BBcB 1974CBcB 1605abAB 613cbAB 294acAB 912ccAB 1495AcAB 671BcAB 1543cAAB \
    2038AAAB 209BAAB 550CAAB 400aBAB 169cBAB 1754BBAB 645CBAB 999aCAB 995bCAB 1787ACAB 2031BCAB \
    474CCAB 1645aaBB 1833baBB 490ccBB 1223AcBB 249BcBB 228cABB 1551AABB 465aBBB 424cBBB \
    1927ABBB 787BBBB 1345aCBB 625bCBB 1157ACBB 1553BCBB 1581CCBB 374aaCB 436baCB 1883BaCB \
    881CaCB 500abCB 176bbCB 1130CbCB 743bACB 1083AACB 977BACB 1729CACB 142aBCB 1801cBCB \
    1059BBCB 1879CBCB 1221aCCB 816bCCB 252ACCB 808BCCB 638CCCB 582aaaC 1709baaC 672BaaC \
    1649bbaC 1490cbaC 1159AbaC 1069CbaC 1690acaC 1216bcaC 1775AcaC 1634aBaC 732ABaC 2008BBaC \
    11CBaC 1410aCaC 758ACaC 2022BCaC 694CCaC 50babC 487cabC 1174BabC 737cbbC 173acbC 1261ccbC \
    461bAbC 150BAbC 297ACbC 1329BCbC 1781CCbC 1848AbAC 555CbAC 336acAC 1107bcAC 1542ccAC \
    1441BcAC 578cAAC 1612BAAC 789CAAC 1476aBAC 1534BBAC 91aCAC 1947bCAC 1949ACAC 248aaCC 96baCC \
    797BaCC 147abCC 200bbCC 1147CbCC 1177cBCC 1222CBCC 1176aCCC 1631bCCC 944ACCC 66BCCC 624CCCC \
    1975aaaaa 41caaaa 406Baaaa 1050Caaaa 495abaaa 675cbaaa 139Abaaa 1155Cbaaa 1079bcaaa \
    1169ccaaa 884Acaaa 643Bcaaa 633aBaaa 1319cBaaa 428ABaaa 1474CBaaa 282bCaaa 1677ACaaa \
    110BCaaa 1253CCaaa 1584babaa 798cabaa 408Babaa 447bbbaa 467cbbaa 719Cbbaa 1519acbaa \
    1762ccbaa 1354bAbaa 454AAbaa 368BAbaa 2029CAbaa 1395aCbaa 1350bCbaa 1143ACbaa 932aacaa \
    1225bacaa 664cacaa 1561Bacaa 943abcaa 1456bbcaa 1292cbcaa 250Abcaa 442accaa 1233cccaa \
    885Accaa 1615bAcaa 1691cAcaa 203AAcaa 1614BAcaa 1600ABcaa 1245BBcaa 1322CBcaa 383aaBaa \
    201baBaa 1675CaBaa 1804bcBaa 1589AcBaa 1875BcBaa 1611bABaa 1683cABaa 704CABaa 1259bCBaa \
    851ACBaa 1756CCBaa 1966aaCaa 946baCaa 1243BaCaa 546CaCaa 1407AACaa 1732BACaa 1031CACaa \
    1211aBCaa 2007cBCaa 323ABCaa 342BBCaa 1199aCCaa 628bCCaa 1550ACCaa 524CCCaa 1094ababa \
    984bbaba 1219cbaba 60Ababa 722cBaba 264ABaba 460BBaba 2016CBaba 701ACaba 1916BCaba 396CCaba \
    54aabba 559cabba 1092Babba 222Cabba 642cbbba 257Abbba 149acbba 572bcbba 1040Acbba 1361Bcbba \
    914bAbba 165AAbba 480CAbba 853ACbba 1662BCbba 1369aacba 1499cacba 183Cacba 1639abcba \
    1980bbcba 1936Abcba 1469Cbcba 553bAcba 1646cAcba 1504AAcba 70aBcba 130cBcba 536BBcba \
    880bcAba 1230AcAba 1149cAAba 1766AAAba 695BAAba 314aBAba 1084BBAba 1208BaCba 1447CaCba \
    206bbCba 1249cbCba 49cACba 386AACba 1381BACba 161CACba 907cBCba 793CBCba 289abaca 1102bbaca \
    774Abaca 377acaca 1286Acaca 1482Bcaca 417aBaca 773cBaca 603ABaca 1359BBaca 1502aCaca \
    216bCaca 954ACaca 575BCaca 538CCaca 1854aabca 658babca 1699cabca 612Babca 362abbca 574cbbca \
    1178Abbca 255Cbbca 1682acbca 1105bcbca 1629Acbca 389Bcbca 864cAbca 1627AAbca 888BAbca \
    1560bCbca 1377BCbca 187bacca 205cacca 1437Bacca 1492Cacca 1434abcca 1258bbcca 581Abcca \
    414accca 1718cccca 1887bAcca 749AAcca 67BAcca 355cBcca 1365ABcca 1786BBcca 1722CBcca \
    1670bbAca 1390cbAca 284AbAca 157acAca 685bcAca 505ccAca 1186AcAca 17BcAca 190bAAca \
    1238cAAca 649aBAca 1692cBAca 1325ABAca 1073CBAca 1218aCAca 40bCAca 1273BCAca 281CCAca \
    224aaBca 1019caBca 227BaBca 561CaBca 105bcBca 777AcBca 1774bABca 1367cABca 956BABca \
    1650aBBca 969CBBca 80ACBca 1855BCBca 1119aaaBa 1256BaaBa 315abaBa 1275bbaBa 895cbaBa \
    189CbaBa 1834AcaBa 1871aBaBa 1572ABaBa 177CBaBa 815aacBa 1200bacBa 1995bbcBa 26cbcBa \
    212AbcBa 707CbcBa 464accBa 1808cccBa 1415AccBa 1440BccBa 1978bAcBa 1086cAcBa 1674AAcBa \
    761CAcBa 533aBcBa 477cBcBa 911ABcBa 1512BBcBa 1653CBcBa 1822abABa 1409bbABa 1015cbABa \
    662AbABa 243CbABa 1797bcABa 279AAABa 1573BAABa 306CAABa 1356aBABa 379ABABa 191BBABa \
    1731CBABa 844bCABa 65BCABa 972acBBa 337ccBBa 1210AcBBa 955BcBBa 1310AABBa 1632BABBa \
    1408CABBa 1498aBBBa 637cBBBa 1270ABBBa 1890BBBBa 1806CBBBa 874aCBBa 320BCBBa 254CCBBa \
    330aaCBa 608BaCBa 38CaCBa 1063abCBa 997bbCBa 2017AbCBa 1337AACBa 605aBCBa 1856cBCBa \
    1422ABCBa 15CBCBa 904ACCBa 427BCCBa 1148abaCa 1150bbaCa 251cbaCa 124AbaCa 543acaCa 241ccaCa \
    160AcaCa 526BBaCa 55bCaCa 886ACaCa 630aabCa 1021CabCa 307abbCa 1509CbbCa 352AcbCa 1818BcbCa \
    928cAbCa 1913AAbCa 650BAbCa 1828aCbCa 551bCbCa 1445BCbCa 1746ccACa 123AcACa 1941bAACa \
    84BAACa 1511cBACa 1100ACACa 1239baBCa 401caBCa 585BaBCa 772acBCa 730bcBCa 1484cABCa \
    472AABCa 39BABCa 765CABCa 1901aBBCa 1751ABBCa 1324BBBCa 1721CBBCa 1114ACBCa 432caCCa \
    1470CaCCa 1601bbCCa 1850cbCCa 398CbCCa 202cBCCa 510ABCCa 1524CBCCa 813aCCCa 570ACCCa \
    420aaaab 1618baaab 1697Baaab 1162Caaab 877cbaab 865Abaab 1782acaab 1904bcaab 1228Acaab \
    1372cBaab 1959BBaab 1180aabab 768cabab 1311Babab 1892Cabab 1884bbbab 569cbbab 380Abbab \
    223Cbbab 1521acbab 1090bcbab 1719Acbab 822Bcbab 1406bAbab 493cAbab 1533BAbab 497aCbab \
    940bCbab 1257ACbab 476CCbab 915aacab 226bacab 1271Cacab 843abcab 1937bbcab 452cbcab \
    1012accab 1895Accab 989Bccab 1813CBcab 1483baBab 129caBab 1236CaBab 1420AcBab 1598CABab \
    1321cBBab 376CBBab 1346aCBab 921bCBab 1304ACBab 845abCab 2023AbCab 832CbCab 644AACab \
    43BACab 87CACab 1659bcacb 44Acacb 905aCacb 1212CCacb 1004Abbcb 708acbcb 1961bcbcb 1931AAbcb \
    1964aCbcb 1267CCbcb 927Cbccb 975cAccb 1224CAccb 677cBccb 1768CBccb 1071abAcb 434cbAcb \
    966CbAcb 939acAcb 1624bAAcb 807cAAcb 194BAAcb 1988CAAcb 238aBAcb 1508cBAcb 1217BBAcb \
    2015BCAcb 1737CCAcb 1829baBcb 817BaBcb 1971acBcb 1371AcBcb 1227BcBcb 1547AABcb 1095BABcb \
    899bCBcb 1393CCBcb 1789aabAb 1859cabAb 565cbbAb 541CbbAb 1061bcbAb 1323AAbAb 439BAbAb \
    1565bCbAb 1285ACbAb 453BCbAb 1164CCbAb 1686bacAb 77AbcAb 1764CbcAb 2025accAb 463cccAb \
    112BccAb 82bAcAb 1996aBcAb 1296cBcAb 14abAAb 1567cbAAb 1906BcAAb 285cAAAb 1599caBAb \
    1882acBAb 435bcBAb 893ccBAb 873AcBAb 2011BcBAb 883cABAb 639CABAb 1727ABBAb 1018BBBAb \
    967aCBAb 1264bCBAb 259CCBAb 1138baCAb 597caCAb 900BaCAb 346bbCAb 703AbCAb 908CbCAb 958cACAb \
    1963CACAb 806aBCAb 902cBCAb 182CCCAb 1655abaCb 1948bbaCb 1918bcaCb 1638BcaCb 1442cBaCb \
    1576ABaCb 523BBaCb 1749BCaCb 1761CCaCb 1805aabCb 1287cabCb 343acbCb 1867bcbCb 1925ccbCb \
    418BAbCb 1467bbACb 1351AbACb 1566CbACb 687acACb 1793bcACb 83cAACb 1622BAACb 1435CAACb \
    1647aBACb 229CBACb 111bCACb 964CCACb 1911aaBCb 1235bABCb 1541AABCb 1657aBBCb 1010ABBCb \
    1706BBBCb 470bCBCb 1489ACBCb 338baCCb 622caCCb 1930BaCCb 1297aBCCb 53ACCCb 1135CCCCb \
    674caaac 1736Caaac 1616cbaac 942Cbaac 779acaac 1661ccaac 392cabac 970Babac 1108bbbac \
    1497Cbbac 1397bcbac 1111ccbac 996aCbac 1894ACbac 1421aaBac 158acBac 837bcBac 1865ccBac \
    1343AcBac 669BcBac 1772BABac 974BBBac 393CBBac 1540CCBac 373aaCac 729caCac 763bACac \
    1194CACac 1728aCCac 882ACCac 126BCCac 1993CCCac 937cbabc 1992Ababc 1851ccabc 214cBabc \
    1942aCabc 889ACabc 1213BCabc 1121CCabc 784cabbc 1491Babbc 1294Cabbc 484bbbbc 1054cbbbc \
    403AAbbc 455CAbbc 936bCbbc 1908ACbbc 1767aacbc 859bbcbc 1088cbcbc 1899Cbcbc 1676AAcbc \
    1744BAcbc 1831CAcbc 702aBcbc 445BBcbc 1101CBcbc 1636bbAbc 1070AAAbc 848cBAbc 1269ABAbc \
    1740CBAbc 207aCAbc 397ACAbc 1158aaCbc 1839CaCbc 319abCbc 847cACbc 646AACbc 390aCCbc \
    262BCCbc 1617cabcc 1568CAbcc 918ACbcc 1938caccc 367cbccc 835Abccc 1144Cbccc 1000acccc \
    1788aBccc 2019ABccc 1349BBccc 1858bbAcc 801CbAcc 494ccAcc 332AcAcc 1903ABAcc 785BBAcc \
    1197aCAcc 1427ACAcc 1780caBcc 963acBcc 502ccBcc 298BcBcc 1166AABcc 1763CCBcc 86babAc \
    948BabAc 473abbAc 140cbbAc 1845AbbAc 1928BcbAc 1209bacAc 1020abcAc 698bbcAc 1093cbcAc \
    1454cAcAc 788BAcAc 1819aBcAc 636cBcAc 2010ABcAc 530BBcAc 1104cbAAc 1281CbAAc 1462BAAAc \
    1411CAAAc 811baBAc 988BaBAc 2035AcBAc 1571BcBAc 723bABAc 1244AABAc 1459CABAc 2043BBBAc \
    71aCBAc 69CCBAc 1165baCAc 1331CaCAc 1384abCAc 782CbCAc 1681CACAc 104cBCAc 1530bCCAc 99ACCAc \
    903CCCAc 1283CaaBc 1606bcaBc 46ccaBc 2033AcaBc 1170BcaBc 556cBaBc 1120BBaBc 769ACaBc \
    269BCaBc 1770CCaBc 1758bacBc 1983cacBc 329CacBc 1790cbcBc 1902AAcBc 1426cbABc 481acABc \
    1609cAABc 548BAABc 1374CAABc 1863aBABc 1513CBABc 127CCABc 1336AABBc 515CCBBc 144AbCBc \
    872bACBc 429CACBc 1133aBCBc 766aCCBc 2039BaabA 1685ababA 1671BCabA 857BabbA 1816bcbbA \
    120bAbbA 657cAbbA 356AAbbA 986BCbbA 681CCbbA 1347bAcbA 850CBcbA 1595AbAbA 1635CbAbA \
    1280ccAbA 135CAAbA 491cBAbA 90caCbA 1817BaCbA 554CbCbA 1579BACbA 1011cBCbA 1248CBCbA \
    151aCCbA 1866caacA 697BaacA 166CaacA 1298cbacA 1920ccacA 544BcacA 1339BBacA 855CBacA \
    1807bCacA 1444ACacA 690CCacA 1416cbbcA 1106AbbcA 1759bcbcA 917BcbcA 1465bCbcA 621baccA \
    2000bAccA 1554AAccA 1308CAccA 1136acAcA 1922AcAcA 1026bAAcA 1295aCAcA 1750bCAcA 1621ACAcA \
    1274caBcA 951CaBcA 1707CABcA 540CCBcA 528cabAA 529AbbAA 558CacAA 1985abcAA 1471cbcAA \
    1403cccAA 305cAcAA 1500BAcAA 522bAAAA 1648AAAAA 1528BAAAA 1840bCAAA 1803caBAA 303CaBAA \
    1827AABAA 1139cBBAA 1051bCBAA 1503CCBAA 1488bbCAA 1667BACAA 1969CACAA 1917cBCAA 1960BBCAA \
    107BCCAA 1315CCCAA 1725bbaBA 416BBaBA 1025CBaBA 345AccBA 804cAcBA 584bbCBA 1430bACBA \
    1424aBCBA 73acaCA 167ACaCA 992CCaCA 1900babCA 1103bcbCA 1493BcbCA 1220CCbCA 1517CbACA \
    1081acACA 1301BAACA 909CBACA 1838bcBCA 1481BcBCA 699aCBCA 595BCBCA 560BaCCA 225caaaB \
    310bbaaB 829AbaaB 208CBaaB 849aCaaB 24ACaaB 938BCaaB 1341babaB 308acbaB 30BcbaB 1137bAbaB \
    415baBaB 1316bcBaB 1002bABaB 1277CBBaB 1956aCBaB 235aaacB 1604bcacB 1398AcacB 534cBacB \
    786ACacB 1029AbbcB 1246bAbcB 1886CAbcB 1919caccB 764BaccB 834AbccB 2009aBccB 1366BBccB \
    311AbAcB 78aaBcB 422caBcB 688acBcB 20aBBcB 1869ABBcB 1932BabAB 840ccbAB 839bacAB 1538AccAB \
    775BAcAB 549CAcAB 9BBcAB 1846AcAAB 321aBAAB 1755ABAAB 1972bCAAB 444ACAAB 286aaBAB 244baBAB \
    1036bcBAB 211aBBAB 95cBBAB 716ACBAB 52AbCAB 1965CbCAB 448BBCAB 1555CCCAB 466bbaBB 1265AcABB \
    661bAABB 740BAABB 1003baBBB 1448BaBBB 514ccBBB 318AABBB 532BABBB 589CABBB 1824aBBBB \
    1734baCBB 1523CaCBB 819cbCBB 1122BACBB 1001CACBB 1431CBCBB 1702bCCBB 830BBaCB 2047bCaCB \
    659bbbCB 1436aCbCB 75AAACB 826CAACB 295cBACB 1380BBACB 363CBACB 181bCACB 1473bcBCB 296ccBCB \
    1700AcBCB 1327cACCB 564bCCCB 1814BCCCB 188baaaC 1291abaaC 973cBaaC 960AbbaC 1716AcbaC \
    1717cAbaC 1172BCbaC 901abcaC 372cbcaC 486cABaC 968aaCaC 1385cACaC 2018BACaC 1860aBCaC \
    728bcabC 1593AcbbC 1466bccbC 2042aBAbC 1688BBCbC 665ACCbC 1067bCbAC 1877cbcAC 10bccAC \
    425cccAC 1125BBcAC 1743ccAAC 143CBAAC 1607BCAAC 823BaBAC 1760aaCAC 577bACAC 1798CbaCC \
    516ABaCC 1970bcBCC 790bCBCC 1680caCCC 1206AbCCC 1072bcbaaa 629BAbaaa 1678cccaaa 513BBcaaa \
    1237aaBaaa 1185ccBaaa 1046BACaaa 1387BBCaaa 1263CCCaaa 1355cbabaa 663aCbbaa 163bCbbaa \
    335ACbbaa 1154bccbaa 592abAbaa 1145bbAbaa 260cAAbaa 1433BAAbaa 1496CAAbaa 934ABAbaa \
    1290CBAbaa 1672CCAbaa 1783acacaa 479babcaa 1602bcbcaa 283CAbcaa 1586bcccaa 1468Bcccaa \
    175AcAcaa 718CAAcaa 27AbaBaa 1124AbcBaa 5aCABaa 47abCBaa 218AACBaa 894CbaCaa 602AAACaa \
    1872CBACaa 656BCACaa 897baBCaa 1665baCCaa 557cbCCaa 617AACCaa 929CCCCaa 919acbaba \
    1231CAbaba 13CABaba 1016BCBaba 1962CACaba 1250caabba 482ABabba 1425AAbbba 2024aacbba \
    709Cacbba 1188cbcbba 748bACbba 1987ABCbba 93baacba 478bAbcba 1823ACbcba 81bAAcba 571baBcba \
    1333BAcAba 263AAAAba 1501aBAAba 1022cBAAba 1739CaBAba 1687bCACba 862AcBCba 1328aCBCba \
    1141BaBaca 810BABaca 1777cBBaca 322BBBaca 1792bbCaca 1260cBCaca 1190CBabca 1202bbcbca \
    1207AAcbca 632acAbca 388cbCbca 45abbcca 916abAcca 1008cbAAca 1842CaCAca 1810ABCBca \
    1526CaaaBa 1240babaBa 1096caacBa 607cbacBa 1723bcbcBa 1847aaccBa 1007baccBa 1910bbAcBa \
    1603BaBcBa 1905CaBcBa 1134BabABa 1885bbbABa 745CaBABa 1873BBCABa 1587cccBBa 1338aaBBBa \
    563ccBBBa 598cBaCBa 959bCBCBa 1027ACBCBa 240AcbaCa 1229CAbaCa 236AAcaCa 341bCbbCa 545AbCbCa \
    317AbAACa 1156ABBBCa 180Abaaab 1414cacaab 1954AcAbab 2040baCbab 683Caacab 1128AAcBab \
    861AbCBab 266ccAccb 1689ACBccb 1394abAAcb 136cBCAcb 1516ACCAcb 1320cbcbAb 1836aCCbAb \
    174aBcAAb 1375CbbaCb 1076bcaaac 1585bcbaac 275ABCabc 1641BBCabc 119aCbcbc 1005CACAcc \
    381BCCBcc 1664CBBBAc 594cBCaaB 679aCAcAB",
   [[3, 72, 641, 715], [72, 641, 715], [18, 36, 72, 301, 715, 924], [36, 72, 715, 924, 1056, 1299],
    [18, 72, 641, 715], [18, 72, 301, 715, 924], [36, 715, 924, 1056, 1299], [3, 36, 72, 301, 450],
    [3, 301, 641, 924, 1056, 1299], [36, 301, 450, 715], [18, 72, 301, 715, 924, 1056]])]

@[expose] def sgWords : List (List Int) :=
  [lettersOfString
    "a",
   lettersOfString
    "b",
   lettersOfString
    "BABAABc",
   lettersOfString
    "BBAbbb",
   lettersOfString
    "BBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABc",
   lettersOfString
    "BBBabbCbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABc",
   lettersOfString
    "CbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCb\
    aababCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbBBBabbBBBabbCbaa\
    babBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbCbaababBBAbb\
    bBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABc",
   lettersOfString
    "CbaababCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaabab\
    BBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababCb\
    aababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbb\
    bBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbCbaababBBAbbbBBBabbBBBabbC\
    baababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcB\
    BBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABc",
   lettersOfString
    "CbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababCbaababCbaababBBBabbBBBabbBABAABc\
    BBAbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBB\
    BabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBa\
    bbBABAABcBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbB\
    ABAABcBABAABcBBBabbCbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcB\
    BBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBB\
    abbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABc",
   lettersOfString
    "CbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCb\
    aababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababCbaababCbaababBBBabbBBBabbBABAABcBB\
    AbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBa\
    bbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabb\
    BABAABcBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBAB\
    AABcBABAABcBBBabbCbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBB\
    abbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBab\
    bBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbCbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBA\
    BAABcBABAABcBABAABcBABAABc",
   lettersOfString
    "CbaababCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaabab\
    BBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbCbaababBBA\
    bbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbb\
    bBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcCbaababCbaababCbaababCbaababBBBa\
    bbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbC\
    baababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbCbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAb\
    bbBABAABcBABAABcBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaab\
    abBBAbbbBBAbbbBABAABcBABAABcCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBab\
    bBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbB\
    ABAABcBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBB\
    AbbbBBAbbbBBBabbCbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBa\
    bbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabb\
    CbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcCbaababCbaababBBBabb\
    BBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBB\
    BabbBABAABcBBAbbbBBAbbbCbaababCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABA\
    ABcBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbb\
    bBBAbbbBBBabbCbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBabbB\
    BBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbCba\
    ababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBabbBBBabbCbaababBBAb\
    bbBBAbbbBABAABcBABAABcCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababCbaababCbaa\
    babBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaababCbaababCbaababBBBabbBBBab\
    bBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcCbaababC\
    baababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCba\
    ababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbBBBabbBBBabbCbaababBBAbb\
    bBBAbbbBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbCbaababBBAbbbBBBabbB\
    BBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBA\
    BAABc",
   lettersOfString
    "CbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCb\
    aababCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaababBB\
    BabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbCbaababBBAbb\
    bBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbB\
    ABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbCbaababBBAbbbBBBabbBBBabbCba\
    ababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCba\
    ababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaab\
    abCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaababBBBab\
    bBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbCbaababBBAbbbBB\
    BabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABA\
    ABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbCbaababBBAbbbBBBabbBBBabbCbaaba\
    bBBAbbbBBAbbbBABAABcBABAABcBABAABcBABAABcBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcCbaaba\
    bCbaababCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbBBBabbBABAABcBBAbbbCbaababCbaababCbaaba\
    bBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababBBAbbbCbaababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCb\
    aababCbaababBBBabbBBBabbBABAABcBBAbbbBBAbbbCbaababCbaababCbaababCbaababBBBabbBBBabbBABAABcBB\
    AbbbBBAbbbBBBabbBABAABcBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcBBBabbBBBabbCbaaba\
    bBBAbbbBBAbbbBABAABcBABAABcBBBabbCbaababBBAbbbBBBabbBBBabbCbaababBBAbbbBBAbbbBABAABcBABAABcB\
    ABAABcBABAABcBABAABc"]

@[expose] def sgRows : List (List Nat) :=
  [[2, 16, 128, 512, 731, 440, 1577, 1457, 1652, 925, 29],
   [4, 32, 256, 667, 1024, 1043, 795, 640, 1652, 647, 941],
   [1, 1660, 601, 21, 1613, 492, 280, 1548, 539, 1457, 349],
   [1, 1091, 1795, 1348, 1241, 1045, 1843, 146, 812, 1389, 411],
   [1, 2, 795, 1318, 21, 1043, 987, 4, 1843, 64, 1060],
   [1, 2, 576, 856, 706, 1776, 1625, 349, 1428, 1053, 278],
   [1, 2, 4, 1510, 923, 89, 1053, 333, 382, 1630, 1720],
   [1, 2, 4, 735, 19, 492, 856, 131, 204, 280, 1929],
   [1, 2, 4, 731, 19, 752, 68, 128, 983, 519, 1945],
   [1, 2, 4, 991, 926, 492, 25, 706, 204, 601, 1705],
   [1, 2, 4, 8, 16, 1548, 1656, 145, 1835, 1087, 1043],
   [1, 2, 4, 8, 16, 162, 192, 128, 387, 640, 1043]]

@[expose] def chainBase : List Nat := [1, 2, 4, 8, 32]

@[expose] def chainLevels : List (List (List Nat)) :=
  [idxWordsOfString
    "_ a b aa ba ca da ab bb cb db eb fb aaa baa caa daa eaa faa gaa haa jaa aba bba cba dba fba \
    gba iba kba lba aca bca cca dca eca fca hca ica jca kca ada bda cda dda eda fda gda hda ida \
    jda kda lda aab bab fab gab hab kab abb cbb dbb ebb fbb gbb hbb ibb kbb lbb acb dcb ecb fcb \
    gcb hcb icb jcb kcb bdb ddb edb fdb gdb hdb idb kdb ldb aeb beb ceb eeb geb jeb keb leb afb \
    bfb cfb ffb kfb baaa eaaa gaaa haaa iaaa jaaa kaaa abaa bbaa ebaa fbaa gbaa hbaa ibaa bcaa \
    ccaa fcaa gcaa kcaa adaa ddaa edaa hdaa jdaa kdaa beaa deaa heaa bfaa dfaa efaa gfaa hfaa \
    kfaa chaa dhaa bjaa djaa caba daba eaba haba cbba jbba acba bcba dcba ecba fcba gcba kcba \
    cdba gdba hdba jdba kdba afba cfba efba ffba hfba kfba lfba cgba egba ggba igba aiba kiba \
    liba bkba ckba dkba alba dlba flba baca caca abca cbca dbca ebca hbca kbca jcca aeca jeca \
    leca bfca ffca ifca jfca ahca bhca ihca jhca bica fica jica ijca ljca ckca aada cada hada \
    iada jada icda jcda lcda hdda jdda beda geda heda jeda keda leda dfda kfda lfda dgda hgda \
    ehda lhda aida kida djda ejda gjda bkda jkda bbab dbab ibab kbab bkab kabb labb dcbb lcbb \
    adbb idbb aebb bebb eebb hebb hfbb bgbb chbb fhbb kibb aacb aecb bhcb bicb ficb dbdb jbdb \
    bddb bfdb baeb iaeb bkfb agaaa abbaa chbaa abcaa cbcaa accaa achaa dbjaa ecaba afcba bhfba \
    gaada",
   idxWordsOfString
    "_ c d cc dc ec fc gc hc ic jc kc cd dd ed fd gd hd id jd kd ld ccc dcc ecc fcc hcc icc jcc \
    cdc ddc edc gdc hdc jdc kdc cec dec eec fec gec hec iec jec kec lec cfc dfc efc ffc gfc hfc \
    ifc jfc cgc egc ggc hgc jgc chc dhc ehc ihc jhc khc dic fic jic kic cjc ejc ijc ljc ckc dkc \
    fkc hkc jkc ccd dcd fcd gcd hcd icd jcd lcd cdd edd hdd jdd ced ded fed ged hed ied jed ked \
    led cfd dfd gfd kfd lfd cgd dgd hgd jgd kgd dhd ehd lhd cid kid cjd djd ejd gjd dkd jkd cld \
    dld dccc eccc gccc hccc jccc lccc cdcc edcc jdcc kdcc cecc fecc gecc hecc jecc cfcc dfcc \
    efcc jfcc kfcc lfcc chcc dhcc fhcc dicc ccdc dcdc ecdc fcdc gddc hddc kddc eedc fedc jedc \
    kedc egdc fgdc hgdc ehdc fjdc gjdc kjdc ckdc ccec dcec kcec gdec jdec ldec ceec jeec efec \
    cgec fgec ggec jgec lgec jhec khec diec fiec giec jiec liec ekec lkec dlec flec jlec ecfc \
    fcfc kcfc cdfc ddfc ldfc cefc gefc hefc kefc dffc cgfc dgfc egfc cifc fjfc ccgc kegc ehgc \
    hchc dehc ejhc dkic ccjc icjc hejc lejc kckc jdkc efkc dccd ffcd ihcd hcdd gedd dged ekfd \
    ldfcc eeedc",
   idxWordsOfString
    "_ e f ee fe ge je ke le ef ff kf eee efe ffe hfe jfe ige jge kge kje hke jle eff ekf fkf \
    feee jeee keee jige",
   idxWordsOfString
    "_ g h i j gg hg ig jg kg ih jh gi ji ki gj kj lj ggg hgg igg ihg khg jig kig ijg ljg gkg \
    gji lji kgj ikj",
   idxWordsOfString
    "_ k l lk"]

@[expose] def xpWord : List Int := lettersOfString "BCBBCBBCB"

@[expose] def w0Lo : Nat := 4712128852136459333

@[expose] def w0Hi : Nat := 100917737537689

end CFSG.Sporadic.J4.QT
