module

public import CFSG.Quasithin.Vol2.Ch10SecC9S5g
public import CFSG.Quasithin.Vol2.Ch10SecCWC
public import CFSG.Quasithin.Vol2.Ch10SecC9L32
public import CFSG.Quasithin.Vol2.Ch10SecC9S5c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Conf

variable {J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem false_of_caseB (h124 : C124StatementSQTK (G := G))
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2)
    (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7) (h322 : TmpL6_3_2_2_two) (hK8a : FactK8a)
    (hK8b : FactK8b) (h318 : A318Facts) (h36' : A36ForSQTK) (hK4 : FactK4) (hK7 : FactK7)
    (hE : Ch11.SecA.FactA318ExclTwo) (hObl : Obl10_2_9L32Branch)
    (hq : ¬ CFSG.Open.IsQuasisimple ↥J)
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hI : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (hcore : S5Core (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)))
      (T ⊓ Subgroup.centralizer ({w} : Set G)) J L (VI T L I J w) hVe)
    (hQ : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (e : ↥(autI hVe J) ≃* ↥(alternatingGroup (Fin 7)))
    (hL : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    False := by
  have hA := c.isAltQuotient h37 h38 h1011 h1026 h1027 hK8a hK8b hF hVe hQ e
  have hblk := c.c124SQTK h124 h37 h38 h1011 h1026 h1027 hK8a hK8b hq hF hA
  obtain ⟨hCJ, hL3, hA5⟩ := hK4 G _ _ J L (VI T L I J w) hVe hcore hA hblk
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  obtain ⟨eJ⟩ := nonempty_quotient_equiv hVe hJN hCJ e
  rcases hL with hL5 | hL32
  · obtain ⟨eL⟩ := hL5
    have hV1 := c.fsuUL_le_VI h37 h38 h1011 h1012 h1027 h322 hK8a hK8b
      (Or.inl (not_case_three_of_A5 eL))
    rcases hA5 ⟨eL⟩ (c.commutator_VI_J hV1) with hIrr | ⟨h3v, h3N⟩
    · exact c.false_of_b1 h1026 hV1 hIrr
    · exact c.false_of_b2 h37 h38 h1011 h318 h36' hK7 hE eJ hCJ hV1 h3v h3N
  · exact hObl G T L I t w J c hq hF hVe hI hL32 (Or.inl ⟨hL3 hL32, ⟨e⟩⟩) hCJ

theorem false_of_S5 (h124 : C124StatementSQTK (G := G))
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2)
    (h1013 : Stmt10_1_3) (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7) (h322 : TmpL6_3_2_2_two)
    (hK8a : FactK8a) (hK8b : FactK8b) (h318 : A318Facts) (h36' : A36ForSQTK) (hK2 : FactK2)
    (hK4 : FactK4) (hK7 : FactK7) (hE : Ch11.SecA.FactA318ExclTwo) (hObl : Obl10_2_9L32Branch)
    (hq : ¬ CFSG.Open.IsQuasisimple ↥J)
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hI : CFSG.Open.IsQuasisimple ↥(autI hVe J)) :
    False := by
  have hyp := c.hyp
  have hcore := c.s5Core h37 h38 h1011 h1026 h1027 hK8a hK8b hq hF hVe hI
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hV1el : IsElemAbelian 2 (fsuUL T L I) :=
    B2F.isElemAbelian_mono hV1V (SecA.isElemAbelian_fsuVM hyp)
  have hOC : pCoreOf 2 L ≤ Subgroup.centralizer (fsuUL T L I : Set G) :=
    (pCoreOf_L_le_centralizer hyp h1011).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV1V))
  have hJN : J ⊓ Subgroup.normalizer (fsuUL T L I : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun g hg => fsuM_inf_centralizer_le h37 h38 hyp c.ht c.htn c.claim.1 c.claim.2.1
      ⟨(h1026 G T L I hyp).2.1 L (Or.inl rfl) hg.2, c.J_le hg.1⟩
  obtain ⟨hQ, hcases⟩ := hK2 G _ _ J L (fsuUL T L I) (VI T L I J w) hVe hcore
    (c.fsuUL_le_L h37 h38 h1011) hV1el (c.le_normalizer_fsuUL' h37 h38) (commutator_fsuUL_eq hyp)
    hOC hJN (modCase_of h37 h38 hyp h1011 h1027 c.ht c.htn)
  rcases hcases with ⟨n, hn, F, _, _, hF2, ⟨eL⟩, htor⟩ | ⟨⟨e⟩, hL⟩ | ⟨hL3, hI', hCJ⟩
  · exact c.false_of_caseA h37 h38 h1011 h1012 h1013 h1026 h1027 h322 hK8a hK8b hn hF2 eL htor
  · exact c.false_of_caseB h124 h37 h38 h1011 h1012 h1026 h1027 h322 hK8a hK8b h318 h36' hK4 hK7
      hE hObl hq hF hVe hI hcore hQ e hL
  · exact hObl G T L I t w J c hq hF hVe hI hL3 (Or.inr hI') hCJ

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
