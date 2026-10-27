module

public import CFSG.Quasithin.Background.H156Gen

public section

namespace CFSG.Quasithin.H156

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem inducesOn_of_map' {V W : Type*} [CommGroup V] [CommGroup W] (eg : V ≃* W)
    {G : Subgroup (MulAut V)} {U Z : Subgroup V} {G' : Subgroup (MulAut W)} {U' Z' : Subgroup W}
    {A : Type*} [CommGroup A] {Γ : Subgroup (MulAut A)}
    (hG : G.map (congrHom eg) = G') (hU : U.map eg.toMonoidHom = U')
    (hZ : Z.map eg.toMonoidHom = Z') (h : InducesOn G' U' Z' A Γ) : InducesOn G U Z A Γ := by
  subst hG hU hZ
  exact inducesOn_of_map eg h

end CFSG.Quasithin.H156
