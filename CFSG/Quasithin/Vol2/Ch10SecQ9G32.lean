module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G31
public import CFSG.Quasithin.Vol2.Ch10SecC9L32
public import CFSG.Quasithin.Vol2.Ch10SecQ9G16

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

namespace C10P4F

@[expose] def L32Step4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (t w : G) (J : Subgroup G),
    Conf T L I t w J → ¬ CFSG.Open.IsQuasisimple ↥J →
    CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) →
    ∀ hVe : IsElemAbelian 2 (VI T L I J w), CFSG.Open.IsQuasisimple ↥(autI hVe J) →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    Nonempty (↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
    J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J → fsuCVM T L I = ⊥ → False

end C10P4F

theorem obl10_2_9L32Branch_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two)
    (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7)
    (h1028 : Stmt10_2_8) (hK8a : FactK8a) (hK8b : FactK8b) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hK7 : FactK7) (hE : Ch11.SecA.FactA318ExclTwo)
    (hK7L4 : C10P4F.FactK7L4) (hK7L5 : C10P4F.FactK7L5) (hL4A : C10P4F.FactL4Aut)
    (hL5I : C10P4F.FactL5Inv) (hStep4 : C10P4F.L32Step4) : Obl10_2_9L32Branch := by
  intro G _ _ T L I t w J c hJq hch hVe hq hL hcases hCJ
  obtain ⟨eL⟩ := hL
  rcases hcases with ⟨hblk, ⟨eA7⟩⟩ | he4 | he5
  · rcases C10P4F.case3_or_case5 c.hyp h1011 h1027 ⟨eL⟩ with h3 | h5
    · exact C10P4F.Conf.false_of_case3_A7 c h37 h38 h1011 h318 h36' hK7 hE hVe hCJ eL eA7 h3
    · exact C10P4F.Conf.false_of_case5_A7 c h37 h38 h1011 h1012 h1027 h322 hK8a hK8b hVe hblk h5
  · obtain ⟨e4⟩ := he4
    rcases C10P4F.case3_or_case5 c.hyp h1011 h1027 ⟨eL⟩ with h3 | h5
    · exact C10P4F.Conf.false_of_case3_L4 c h37 h38 h1011 h318 h36' hE hK7L4 hVe hq hCJ eL e4 h3
    · exact C10P4F.Conf.false_of_case5_L4 c h37 h38 h322 h1011 h318 h36' hE hK7L4 hL4A hVe hq
        hCJ eL e4 h5
  · obtain ⟨e5⟩ := he5
    by_cases hcv : fsuCVM T L I = ⊥
    · exact hStep4 G T L I t w J c hJq hch hVe hq ⟨eL⟩ ⟨e5⟩ hCJ hcv
    · exact C10P4F.Conf.false_of_L5_cv c h37 h38 h1011 h1012 h1026 h1028 h318 h36' hE hK7L5 hL5I
        hVe hq hCJ eL e5 hcv

end CFSG.Quasithin.Vol2.Ch10.SecC
