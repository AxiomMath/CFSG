module

public import CFSG.Milestones.ASVolI.C61.PAppDK5
public import CFSG.Milestones.ASVolI.C61.PAppDC61
public import CFSG.Milestones.ASVolI.C61.PAppDK4

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.burnsideC56_P.DoubleA3
open CFSG.QuasithinUnique.DoubleA3 hiding A3A3 A3A3.V_isPGroup A3A3.blockU0_eq A3A3.center_L0
  A3A3.comm_elem A3A3.conjJoin_ne A3A3.conj_cases A3A3.inf_Ls A3A3.inf_S_L0 A3A3.isA4 A3A3.isA4s
  A3A3.isShort A3A3.isSylowTwoOf_V A3A3.le_normalizer_V A3A3.normalizer_conjR exists_A3A3

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

theorem exists_gcfg (h : A3A3 T M H S L s) : Nonempty (GCfg T M H S L) := by
  obtain ⟨sp⟩ := A3x.exists_spec h
  exact ⟨{ hcs := h.cs
           U := blockU L ⊔ blockU2 L s
           hUdef := (A3x.hUeq h).symm
           P := A3x.piS sp
           hB := A3x.piS_im_B sp
           hS := A3x.piS_im_S sp
           hUQ := A3x.U_le_Q (h := h)
           hQ := A3x.hQ_cent h
           hUD := A3x.U_inf_D h
           hQeq := A3x.Q_eq sp
           hU1 := le_sup_left }⟩

theorem c61A3Double {G : Type} [Group G] [Finite G]
    {T M H S L : Subgroup G} (hcs : burnsideC56_CS G T M H S L) (h3 : IsAltType L 3)
    (hne : conjJoin S L ≠ L) : C61Concl T H S L := by
  obtain ⟨s, h⟩ := exists_A3A3 hcs h3 hne
  obtain ⟨C⟩ := exists_gcfg h
  exact c61_gen C (A3x.hU0 h) (fun hj _ => hne hj) (Or.inr ⟨h3, hne⟩) (fun _ hj => hne hj)

end CFSG.QuasithinUnique.burnsideC56_P.AppD
