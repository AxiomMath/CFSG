module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly UCoord

theorem ggTorusReflGenW_of_permEltSC {p r d : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusPermEltSC p d R) : GGTorusReflGenW p r R I := by
  intro L' _ _ ψ A hA v hv
  obtain ⟨hψ, hker, hperf, hAab, hAI, -, h3, hsc⟩ := hA
  obtain ⟨Θ, hW, hP, hN⟩ := exists_permModel hp hZ hIp hcp h hψ hker hperf hAab hAI h3 hsc
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
  have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
  obtain ⟨π, hπ⟩ := hN n hcN
  set H : Subgroup (MulAut ↥(sumZero d p)) :=
    (Subgroup.closure (ggTorusReflSet p A)).comap (MulAut.congr Θ).toMonoidHom with hH
  have hsw : ∀ i j : Fin d, i ≠ j → permAutV (Equiv.swap i j) ∈ H := by
    intro i j hij
    obtain ⟨m, hm, hmα⟩ := hP (Equiv.swap i j)
    obtain ⟨hpow, hfix⟩ := isPseudoReflection_permAutV_swap hp hp2 hij
    refine Subgroup.subset_closure ⟨m, hm, hW m hm, hmα.symm, ?_, ?_⟩
    · rw [← map_pow, sq, ← permAutV_mul, Equiv.swap_mul_self, permAutV_one, map_one]
    · exact (ggIsPseudoReflection_congr Θ hpow hfix).2
  have hmem := mem_closure_permAutV hsw π
  rw [hH, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hmem
  rw [hv', hπ]
  exact hmem

end CFSG.StandardType
