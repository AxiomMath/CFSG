module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Alt7
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329G2
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Lie
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Mat
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329M12Row
public import CFSG.Quasithin.Vol2.GoldschmidtC58Proved
public import CFSG.Quasithin.Vol2.GoldschmidtTD317
public import CFSG.Quasithin.Vol2.GoldschmidtTD32
public import CFSG.Quasithin.Vol2.GoldschmidtCor332
public import CFSG.Quasithin.Background.SmithB45Holds
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

theorem stmt3_2_9C_of
    (h325 : Stmt3_2_5) (h316 : Theorem316Statement) : Stmt3_2_9C :=
  stmt3_2_9C_of_rows theoremC58_proved (as317Sylow_of_nonsolvable as317SylowNonsolvable_proved)
    stmt3_2_3_proved h325 stmt3_2_2_eight_proved Cor332.stmt3_3_2MTwo_holds h316 asB45_holds
    row329Alt7_holds row329G2_holds row329Orth_holds row329Nine_holds row329M12_holds
    row329HatM22_holds row329M22_holds row329M23_holds row329M24_holds

end CFSG.Quasithin.H13
