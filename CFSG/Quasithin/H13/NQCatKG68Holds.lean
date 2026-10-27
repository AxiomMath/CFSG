module

public import CFSG.Quasithin.H13.NQCatKG68SingerL3
public import CFSG.Quasithin.H13.NQCatKG68SingerG2
public import CFSG.Quasithin.H13.NQCatKG68SingerD4
public import CFSG.Quasithin.H13.NQCatKG68SingerF4
public import CFSG.Quasithin.H13.NQCatKG68SingerBender
public import CFSG.Quasithin.H13.NQCatKG68SingerSp4
public import CFSG.Quasithin.H13.NQCatKG68Vac
public import CFSG.Quasithin.H13.NQCatKG68U33
public import CFSG.Quasithin.H13.KGFact68CSL2
public import CFSG.Quasithin.H13.KGFact68Lie
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Setup.X6

theorem cartanSingerCover_of_stated_psl_three {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 f) : CartanSingerCover X := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : CharP F 2 := NQCat.LieMult.charP_two_of_card hF
  exact CartanSingerCover.of_mulEquiv (e.trans (Setup.X7a.statedSLEquivProjectiveSL 3 F))
    Singer.L3.cartanSingerCover_l3

theorem cartanSinger_of_stated_psp {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) : CartanSinger X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := NQCat.LieMult.charP_two_of_card hK
  exact CartanSinger.of_mulEquiv (e.trans (QuasithinUnique.Lin2.Five.projEquiv K).symm)
    Singer.Sp4.cartanSinger_sp4

theorem cartanSingerCover_of_isL34OrG24
    {S : Type} [Group S] [Finite S] (hS : Ch1.IsL34OrG24 S) : CartanSingerCover S := by
  rcases hS with h | h
  · exact cartanSingerCover_of_stated_psl_three h
  · obtain ⟨hf, F, _, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_G2_model h
    exact CartanSingerCover.of_mulEquiv e (Singer.G2.cartanSingerCover_g2 hF hf)

theorem cartanSinger_of_sqtkCharTwoLie
    {S : Type} [Group S] [Finite S]
    (hS : Ch1.SQTKCharTwoLie S ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 3 1) :
    CartanSinger S := by
  rcases hS with ((⟨f, hL2 | hL3 | hU3 | hSp | hG2 | hD4 | hF4 | hSz⟩ | hT) | ⟨n, hn, hL⟩) | hU
  · exact (cartanSingerCover_of_stated_psl_two hL2.2).cartanSinger
  · exact (cartanSingerCover_of_stated_psl_three hL3.2).cartanSinger
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hU3.1 hU3.2
    exact (CartanSingerCover.of_mulEquiv e (Singer.cartanSingerCover_psu3 hU3.1)).cartanSinger
  · exact cartanSinger_of_stated_psp hSp.2
  · obtain ⟨hf, F, _, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_G2_model hG2.2
    exact (CartanSingerCover.of_mulEquiv e (Singer.G2.cartanSingerCover_g2 hF hf)).cartanSinger
  · obtain ⟨hn, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hD4.2
    exact (CartanSingerCover.of_mulEquiv e (Singer.D4.cartanSingerCover_d4 σ hn hK hσ)).cartanSinger
  · obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hF4.2.2
    subst hfa
    exact (CartanSingerCover.of_mulEquiv e (Singer.F4.cartanSingerCover_f4 ha hK)).cartanSinger
  · obtain ⟨a, ha, -, ⟨e⟩⟩ :=
      CFSG.ComponentClassification.GMS78.exists_mulEquiv_sz_of_suzukiModel hSz.2.2
    exact (CartanSingerCover.of_mulEquiv e (Singer.cartanSingerCover_sz ha)).cartanSinger
  · exact (cartanSingerCover_tits hT).cartanSinger
  · exact (cartanSingerCover_of_stated_psl_binary (Or.inr hn) hL).cartanSinger
  · exact (cartanSingerCover_psu33 hU).cartanSinger

theorem e68ComponentFactsLie_of_inner
    (hInn : Ch1.EvenLieAutInner) (hU33 : U33AutInner) : E6.E68ComponentFactsLie :=
  e68ComponentFactsLie_of hInn hU33 fun _ _ _ hS => cartanSinger_of_sqtkCharTwoLie hS

theorem e68ComponentFactsCover_of_inner
    (hInn : Ch1.EvenLieAutInner) : E6.E68ComponentFactsCover :=
  e68ComponentFactsCover_of hInn fun _ _ _ hS => cartanSingerCover_of_isL34OrG24 hS

end CFSG.Quasithin.H13.KG68
