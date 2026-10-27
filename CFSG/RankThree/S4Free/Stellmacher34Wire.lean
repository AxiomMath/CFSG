module

public import CFSG.RankThree.S4Free.Stellmacher34
public import CFSG.RankThree.S4Free.Stellmacher29SzHost
public import CFSG.RankThree.S4Free.StellmacherThmAGen

public section

namespace CFSG.RankThree.S4Free.Stell34

universe u v

theorem thmA_sz :
    Stell33.ThmA.{u} .sz :=
  fun _ _ _ hV _ hsz hO2 hS3 _ hAH hA =>
    Stell.two_mul_rk_le_rkIdx_of_szSections hV hsz hO2 hS3 hAH hA

theorem stellmacherSzAll_of_hyp29
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput)
    (h29 : Stell.Hyp29.{u} .sz) : StellmacherSzAll.{u, v} :=
  stellmacherSzAll_of_inputs thmA_sz h29 (hyp24Sz_holds hSub) hyp25dSz_holds

theorem stellmacherSzAll_holds
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) : StellmacherSzAll.{u, v} :=
  stellmacherSzAll_of_hyp29 hSub (Stell.hyp29_sz hSub)

end CFSG.RankThree.S4Free.Stell34
