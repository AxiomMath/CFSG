module

public import CFSG.Quasithin.Vol2.Ch10SecC10TI
public import CFSG.Quasithin.Vol2.Ch10StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13

theorem stmt10_2_10_of (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1013 : Stmt10_1_3)
    (h1026 : Stmt10_2_6) (h1029 : Stmt10_2_9) : Stmt10_2_10 := by
  intro G _ _ T L I hyp
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal
  have hloc := hyp.fsu.maximal.1
  have hn := SecA.fsuL0_le_normalizer hloc
  have hnt : ∀ t ∈ T, fsuL0 T L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
    fun t ht => SecA.fsuL0_le_normalizer_conjugate hloc (SecA.le_fsuM T L ht)
  refine ⟨fun t ht htn g hg => inf_conjSubgroup_eq_bot hyp h1011 h1013 h1026 h1029 hsimp ht htn
    (SecA.fsuL0_eq_sup h37 h38 hyp ht htn) hn (hnt t ht) hg, fun hcv K hK => ?_⟩
  rcases hK with hK | ⟨t, ht, htn, hK⟩
  · obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
    exact isTISetIn_of_cvm_eq_bot hyp h1011 h1013 h1026 h1029 hsimp ht htn
      (SecA.fsuL0_eq_sup h37 h38 hyp ht htn) hn (hnt t ht) hcv (Or.inl hK)
  · exact isTISetIn_of_cvm_eq_bot hyp h1011 h1013 h1026 h1029 hsimp ht htn
      (SecA.fsuL0_eq_sup h37 h38 hyp ht htn) hn (hnt t ht) hcv (Or.inr hK)

end CFSG.Quasithin.Vol2.Ch10.SecC
