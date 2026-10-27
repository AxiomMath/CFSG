module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.RankThree.Classical

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

variable {r : ℕ} {K : Type} [Field K]

theorem exists_sp_of_isometry {u : Module.End K (Fin r ⊕ Fin r → K)}
    (hiso : ∀ v w, spForm r K (u v) (u w) = spForm r K v w) :
    ∃ g : StatedSp r K, spEnd g = u := by
  have hinj : Function.Injective u := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact (spForm_nondegenerate (r := r) (K := K)).1 v fun w => by
      rw [← hiso, hv, map_zero, LinearMap.zero_apply]
  have hsurj : Function.Surjective u := LinearMap.injective_iff_surjective.1 hinj
  set e := LinearEquiv.ofBijective u ⟨hinj, hsurj⟩ with he
  let U : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) :=
    ⟨u, e.symm.toLinearMap, LinearMap.ext fun v => e.apply_symm_apply v,
      LinearMap.ext fun v => e.symm_apply_apply v⟩
  have hmem : U ∈ sesqUnitaryGroup (spForm r K) := mem_sesqUnitaryGroup.mpr hiso
  rw [← range_spLin] at hmem
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, ?_⟩
  change ((spLin r K g : LinearMap.GeneralLinearGroup K _) : Module.End K _) = u
  rw [hg]

end CFSG.RankThree.Classical
