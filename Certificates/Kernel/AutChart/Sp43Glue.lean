module

public import CFSG.Certificates.Kernel.F48Small.AutCSound
public import CFSG.Certificates.Kernel.Common.StrSplit
public import Certificates.Kernel.AutChart.Sp43Sub

public section

namespace CertificateChecks.KernelAutChart

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L

theorem words_eq (s : String) (cs : List Char) (e : s = String.ofList cs) :
    burnsideF48s_autc_words s = autcWords cs := by
  have hc : ("," : String) = String.singleton ',' := by decide
  rw [burnsideF48s_autc_words, e, hc, CFSG.KC.Str.splitOn_ofList, autcWords, autcSplit_nil,
    List.map_map]
  congr 1
  funext l
  simp [burnsideF48s_autc_word]

theorem wB_eq : burnsideF48s_autc_sp43BW () = autcWords Sp43B.chars :=
  words_eq _ _ Sp43B.eq

theorem w1_eq : burnsideF48s_autc_sp43P1W () = autcWords Sp43P1.chars :=
  words_eq _ _ Sp43P1.eq

theorem w2_eq : burnsideF48s_autc_sp43P2W () = autcWords Sp43P2.chars :=
  words_eq _ _ Sp43P2.eq

theorem letOK : LetOK 45 5 (burnsideF48s_autc_sp43gl ()) (burnsideF48s_autc_sp43gli ()) :=
  autc_letOK ch7545let

theorem checkSub_true : burnsideF48s_autc_sp43_checkSub () = true := by
  rw [burnsideF48s_autc_sp43_checkSub, wB_eq, w1_eq, w2_eq]
  simp only [Bool.and_eq_true]
  exact ⟨⟨autc_groupB_of letOK ch7545headB ch7545groupB,
    autc_groupB_of letOK ch7545head1 ch7545group1⟩, autc_groupB_of letOK ch7545head2 ch7545group2⟩

theorem checkInf_true : burnsideF48s_autc_sp43_checkInf () = true := by
  have h := autc_inf_of letOK (autcWords Sp43P1.chars) (autcWords Sp43P2.chars)
    (autcWords Sp43B.chars) ch7545inf
  rw [← wB_eq, ← w1_eq, ← w2_eq] at h
  exact h

end CertificateChecks.KernelAutChart
