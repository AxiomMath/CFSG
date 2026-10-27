module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Small
public import CFSG.Quasithin.H13.NQCatKGSmallRank

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem smallGroup625Fact_holds
    : SmallGroup625Fact := by
  refine ⟨NQCat.j2_exists_isElemAbelianOfRank_three_two, ?_,
    NQCat.trialityD4_two_exists_isElemAbelianOfRank_seven_two, ?_⟩
  · intro X _ _ hX hodd hJ
    obtain ⟨e⟩ := hJ
    have : Group.IsPerfect X := hX
    let π : X →* CFSG.Blueprint.NativeSporadic.J2 :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center X := by
      ext x
      rw [MonoidHom.mem_ker]
      show e (QuotientGroup.mk' _ x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h := CFSG.SectionRank.J2_perfect_odd_cover_trivial π hπ hker.le
      (by rw [hker]; exact hodd)
    rwa [hker] at h
  · intro X _ _ hX hodd hD
    have : Group.IsPerfect X := hX
    have hker : (QuotientGroup.mk' (Subgroup.center X)).ker = Subgroup.center X :=
      QuotientGroup.ker_mk' _
    have h := CFSG.SectionRank.triality_even_perfect_odd_cover_trivial hD
      (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _) hker.le
      (by rw [hker]; exact hodd)
    rwa [hker] at h

end CFSG.Quasithin.H13
