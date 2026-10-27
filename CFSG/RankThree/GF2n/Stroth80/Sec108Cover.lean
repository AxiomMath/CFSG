module

public import CFSG.RankThree.GF2n.Stroth80.Sec108AS
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open CFSG CFSG.Blueprint

private def compM12 {E S : Type} [Group E] [Group S] (π : E →* S)
    (e : S ≃* NativeSporadic.Carrier TauCeti.SporadicName.M12) :
    E →* NativeSporadic.M12 where
  toFun x := e (π x)
  map_one' := by
    rw [map_one π]
    exact e.map_one
  map_mul' x y := by
    rw [map_mul π]
    exact e.map_mul (π x) (π y)

private def compJ2 {E S : Type} [Group E] [Group S] (π : E →* S)
    (e : S ≃* NativeSporadic.Carrier TauCeti.SporadicName.J2) :
    E →* NativeSporadic.J2 where
  toFun x := e (π x)
  map_one' := by
    rw [map_one π]
    exact e.map_one
  map_mul' x y := by
    rw [map_mul π]
    exact e.map_mul (π x) (π y)

theorem sec108OddCoverStatement :
    Sec108OddCoverStatement := by
  intro E S _ _ _ _ π hπ hK hodd hS
  rcases hS with hS | hS
  · obtain ⟨e⟩ := hS
    have hker : (compM12 π e).ker = π.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      exact e.map_eq_one_iff
    have hsurj : Function.Surjective (compM12 π e) := e.surjective.comp hπ
    have hsplit := CFSG.SectionRank.M12_perfect_odd_cover_trivial
      (compM12 π e) hsurj (hker.trans_le hK) (by rw [hker]; exact hodd)
    rwa [hker] at hsplit
  · obtain ⟨e⟩ := hS
    have hker : (compJ2 π e).ker = π.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      exact e.map_eq_one_iff
    have hsurj : Function.Surjective (compJ2 π e) := e.surjective.comp hπ
    have hsplit := CFSG.SectionRank.J2_perfect_odd_cover_trivial
      (compJ2 π e) hsurj (hker.trans_le hK) (by rw [hker]; exact hodd)
    rwa [hker] at hsplit

end CFSG.RankThree.GF2n.Stroth80.Sec108
