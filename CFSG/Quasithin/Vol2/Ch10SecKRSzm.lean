module

public import CFSG.Quasithin.Vol2.Ch10SecKRSzl
public import CFSG.Quasithin.Vol2.Ch10SecKRSi
public import CFSG.Quasithin.Vol2.Ch10SecKRSj
public import CFSG.Quasithin.Vol2.Ch10SecKRSzd
public import CFSG.Quasithin.Vol2.Ch10SecQ9G32

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open KRS C10P4F

theorem l32Step4_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two)
    (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7)
    (hK8a : FactK8a) (hK8b : FactK8b) (h318 : A318Facts) (h36' : A36ForSQTK)
    (hE : Ch11.SecA.FactA318ExclTwo) (hK7L5 : C10P4F.FactK7L5) (h51 : AsB51) :
    C10P4F.L32Step4 := by
  intro G _ _ T L I t w J c _ hch hVe hq hL he5 hCJ hcv
  obtain ⟨eL⟩ := hL
  obtain ⟨e5⟩ := he5
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  obtain ⟨eJ⟩ := nonempty_quotient_equiv hVe hJN hCJ e5
  have hcV1 : cV1 T L I = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxV : (x : G) ∈ fsuCVM T L I :=
      ⟨SecA.fsuUL_le_fsuVM T L I x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [hcv, Subgroup.mem_bot] at hxV
    exact Subgroup.mem_bot.mpr (Subtype.ext hxV)
  have hV1W := c.fsuUL_le_VI h37 h38 h1011 h1012 h1027 h322 hK8a hK8b (Or.inr hcV1)
  have hcase := case3_or_case5 c.hyp h1011 h1027 ⟨eL⟩
  obtain ⟨hab, h⟩ := Conf.exists_altL5 c h37 h38 h1026 h1011 h1012 h1027 h322 hK8a hK8b h51 hch
    hVe hq e5 hCJ hcv
  rcases coords_of_altL5 hJN (Conf.commutator_VI_eq c hV1W) h with
    hN | hA | hsum | ⟨k, hk2, -, hds⟩
  · obtain ⟨C⟩ := hN
    exact Conf.false_of_multiCoord c h37 h38 h322 h1011 h318 h36' hE hK7L5 hVe hq e5 eJ eL hCJ
      hcv hV1W hcase (natToMulti C) (i₀ := 0) rfl
  · obtain ⟨C⟩ := hA
    exact Conf.false_of_altCoord c h37 h38 h1011 h318 h36' hE hK7L5 hVe hq e5 eJ eL hCJ hcv hV1W
      hcase C
  · obtain ⟨C, hCd⟩ := exists_multiCoord_of_sumNatDual hJN hsum
    exact Conf.false_of_multiCoord c h37 h38 h322 h1011 h318 h36' hE hK7L5 hVe hq e5 eJ eL hCJ
      hcv hV1W hcase C (i₀ := 0) (by rw [hCd]; rfl)
  · obtain ⟨C, hCd⟩ := exists_multiCoord_of_copies hJN (by omega) hds
    exact Conf.false_of_multiCoord c h37 h38 h322 h1011 h318 h36' hE hK7L5 hVe hq e5 eJ eL hCJ
      hcv hV1W hcase C (i₀ := ⟨0, by omega⟩) (by rw [hCd])

theorem obl10_2_9L32Branch_of_B51
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two)
    (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7)
    (h1028 : Stmt10_2_8) (hK8a : FactK8a) (hK8b : FactK8b) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hK7 : FactK7) (hE : Ch11.SecA.FactA318ExclTwo)
    (hK7L4 : C10P4F.FactK7L4) (hK7L5 : C10P4F.FactK7L5) (hL4A : C10P4F.FactL4Aut)
    (hL5I : C10P4F.FactL5Inv) (h51 : AsB51) : Obl10_2_9L32Branch :=
  obl10_2_9L32Branch_of h37 h38 h322 h1011 h1012 h1026 h1027 h1028 hK8a hK8b h318 h36' hK7 hE
    hK7L4 hK7L5 hL4A hL5I
    (l32Step4_of h37 h38 h322 h1011 h1012 h1026 h1027 hK8a hK8b h318 h36' hE hK7L5 h51)

end CFSG.Quasithin.Vol2.Ch10.SecC
