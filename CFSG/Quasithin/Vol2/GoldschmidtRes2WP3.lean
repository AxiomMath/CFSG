module

public import CFSG.Quasithin.Vol2.Ch3E213MP3E
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WPkgDefs

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M

theorem pkgOddPaired215W
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) : PkgOddPaired215W := by
  intro G _ _ H T M V K hS h1 p hp hp8 hPSL _ haut _
  obtain ⟨g, hg, hpair, hc2, hne, hker, ℓ, b, hℓ, hℓ2, hb, hcard, -, -⟩ :=
    exists_dihedral_member_of_oddPaired h38 hS h1 hp hp8 hPSL haut
  have hcard' : (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g)).relIndex (Ch3n.pairI V g) =
      2 * ℓ ^ b := by rw [hker, hcard]
  exact ⟨g, hg, hpair, hc2, hne, relIndex_le_of_dihedral hpair hc2 hℓ hℓ2 hb hcard',
    e215DataW_of_dihedral hpair hc2 hne hℓ hℓ2 hcard'⟩

end CFSG.Quasithin.Res2
