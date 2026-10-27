module

public import CFSG.Quasithin.EmptyFaithful.S153YA3K5
public import CFSG.Quasithin.EmptyFaithful.S153YGCfg
public import CFSG.Quasithin.EmptyFaithful.S153YA3K4

public section

namespace CFSG.Quasithin.YG.AppD

open CFSG.QuasithinUnique.AppD
open CFSG.QuasithinUnique.DoubleA3
open CFSG.Quasithin.YG.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G} {s : G}

theorem exists_gcfg (h : A3A3 H S L s) : Nonempty (GCfg H S L) := by
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

end CFSG.Quasithin.YG.AppD
