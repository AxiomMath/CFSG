module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

theorem kAdjConcl_conj_iff {G : Type} [Group G] {Kstar : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (Kstar : Set G)) {t : G} {r m : ℕ} :
    KAdjConcl Kstar (e * t * e⁻¹) r m ↔ KAdjConcl Kstar t r m := by
  have key : ∀ {e : G}, e ∈ Subgroup.normalizer (Kstar : Set G) → ∀ {t : G},
      KAdjConcl Kstar t r m → KAdjConcl Kstar (e * t * e⁻¹) r m := by
    intro e he t h
    have hK : Kstar.map (MulAut.conj e).toMonoidHom = Kstar :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp he
    have := kAdjConcl_map (MulAut.conj e) h
    rw [hK] at this
    simpa [MulAut.conj_apply] using this
  refine ⟨fun h => ?_, key he⟩
  have := key (inv_mem he) h
  simpa [mul_assoc] using this

theorem kAdjConcl_conj {G : Type} [Group G] {Kstar : Subgroup G} {t : G} {r m : ℕ} (e : G)
    (he : e ∈ Subgroup.normalizer (Kstar : Set G)) (h : KAdjConcl Kstar (e * t * e⁻¹) r m) :
    KAdjConcl Kstar t r m :=
  (kAdjConcl_conj_iff he).1 h

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
