module

public import CFSG.Quasithin.Vol2.Ch12Sec9Final
public import CFSG.Quasithin.Vol2.Ch12Sec9Setup
public import CFSG.Quasithin.H13.LinearSelected

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem linear_selected_natural_configuration_producer (h1222 : Stmt12_2_2)
    (h1251 : Stmt12_5_1) (h12634 : Stmt12_6_34) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1283 : Lemma12_8_3) (h1294 : Lemma12_9_4) (h1297 : Lemma12_9_7)
    (h1299 : Lemma12_9_9) (hfin : Final1291) :
    LinearSelectedNaturalConfigurationProducer := by
  intro G _ _ T L n hsimple hnonab hqtke hT hex hmax hf hq hn hlin hsel
  obtain ⟨V, hcx⟩ := exists_cx1291 h1222 h1251 h12634 hsimple hnonab hqtke hT hex hmax hf hq hn
    hlin hsel
  exact config_of_cx1291 h1222 h1283 (lemma12_9_3_one h1222 h37 h38 h39) h1294 h1297 h1299 hfin
    hcx

theorem linear_selected_natural_configuration_producer_of_12_2_13 (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1251 : Stmt12_5_1) (h12634 : Stmt12_6_34) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1294 : Lemma12_9_4) (h1297 : Lemma12_9_7)
    (h1299 : Lemma12_9_9) (hfin : Final1291) :
    LinearSelectedNaturalConfigurationProducer :=
  linear_selected_natural_configuration_producer h1222 h1251 h12634 h37 h38 h39
    (lemma12_8_3 h12213) h1294 h1297 h1299 hfin

end CFSG.Quasithin.H13
