module

public import CFSG.Quasithin.AppendixH.H9.H92.OrthoBasis
public import CFSG.Quasithin.AppendixH.H9.H92.S6Embed
public import CFSG.Quasithin.AppendixH.H9.H92.NonsingularVec
public import CFSG.Quasithin.AppendixH.H9.H92.ConjTransport.ConjugateStructure
public import CFSG.Quasithin.AppendixH.H9.H92.ConjTransport.OuterCentralizer

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem isSymNatural_of_outer_involution (t : MulAut (PairN 5)) (ht : t ∈ Mg 5) (htL : t ∉ Lg 5)
    (ht2 : orderOf t = 2) :
    G6.IsSymNatural (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))))
      (commOn (fixV (Subgroup.zpowers t))
        (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))))) 6 := by
  obtain ⟨g, hg, rfl⟩ := isConjIn_swap_of_outer_involution t ht htL ht2
  exact isSymNatural_conj_centralizer (L := Lg 5) g (swapN 5) (conjAut_Lg_eq_of_mem_Mg hg)
    isSymNatural_swap

theorem exists_nonsingular_vec_of_outer_involution (t : MulAut (PairN 5)) (ht : t ∈ Mg 5)
    (htL : t ∉ Lg 5) (ht2 : orderOf t = 2) :
    ∃ v ∈ fixV (Subgroup.zpowers t), pairQn 5 v = 1 ∧
      (∀ g ∈ Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5))), g v = v) ∧
      fixV (Subgroup.zpowers t) =
        Subgroup.zpowers v ⊔ commOn (fixV (Subgroup.zpowers t))
          (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5)))) ∧
      Subgroup.zpowers v ⊓ commOn (fixV (Subgroup.zpowers t))
          (Lg 5 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 5)))) = ⊥ := by
  obtain ⟨g, hg, rfl⟩ := isConjIn_swap_of_outer_involution t ht htL ht2
  exact exists_vec_conj_centralizer (L := Lg 5) g (swapN 5) (pairQn 5) (pairQn_of_mem_Mg hg)
    (conjAut_Lg_eq_of_mem_Mg hg) exists_nonsingular_vec_swap

end CFSG.ASVolI.ChH
