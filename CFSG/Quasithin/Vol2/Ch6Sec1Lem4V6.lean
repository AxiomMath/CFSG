module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem titsCenterFact614_holds
    : TitsCenterFact614 := by
  intro X _ _ hX hodd hT
  have : Group.IsPerfect X := hX
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hT
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h := CFSG.SectionRank.Tits_perfect_odd_cover_trivial hK π hπ hker.le
    (by rw [hker]; exact hodd)
  rwa [hker] at h

end CFSG.Quasithin.H13
