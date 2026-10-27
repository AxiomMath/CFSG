module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeJ2
public import CFSG.Quasithin.Background.A318POutSpor

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint

theorem noCover3_j2 :
    NoCover3 NativeSporadic.J2 := by
  intro L _ _ hq hZ ⟨φ⟩
  haveI : Group.IsPerfect L := hq.1
  set π : L →* NativeSporadic.J2 := φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    with hπ
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨q, rfl⟩ := φ.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hker : π.ker = Subgroup.center L := by
    ext l
    simp only [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff φ φ.injective, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
    rw [hn]
    exact Odd.pow (by decide)
  rw [← hker]
  exact CFSG.SectionRank.J2_perfect_odd_cover_trivial π hsurj hker.le hodd

theorem listRow_j2 :
    ListRow NativeSporadic.J2 := fun _ _ _ =>
  Or.inr (Or.inr ⟨⟨MulEquiv.refl _⟩,
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.real3_of_j2
      (X := NativeSporadic.J2) (MulEquiv.refl _), noCover3_j2⟩)

theorem outerRow_j2 :
    OuterRow NativeSporadic.J2 := by
  apply outerRow_of_not_three_dvd_outer
  haveI : Finite (NativeSporadic.Carrier .J2) := inferInstanceAs (Finite NativeSporadic.J2)
  exact CFSG.Quasithin.A318P.not_dvd_outer_J2 (S := NativeSporadic.J2) (MulEquiv.refl _)
    Nat.prime_three (by norm_num)

theorem row_carrier_j2 :
    RowOf (NativeSporadic.Carrier .J2) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.J2) e.symm ⟨listRow_j2, outerRow_j2⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
