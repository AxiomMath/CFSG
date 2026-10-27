module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcInduced

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

theorem ggTorusReflGenW_of_signedEltSC {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) : GGTorusReflGenW p r R I := by
  refine NbrTableBExc.ggTorusReflGenW_of_pow ?_
  intro L' _ _ ψ A hA v hv
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, hsc⟩ := hA
  obtain ⟨k, Θ, -, hW, hS, hP, hN⟩ := exists_signedModelSC hp hp2
    (fun φ hφ => hIp φ hφ.1 hφ.2) hZ hcp h hψ hker hperf hAe hAI h3 hsc
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
  have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
  set H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
    (Subgroup.closure (ggTorusReflSet p A)).comap (MulAut.congr Θ).toMonoidHom with hH
  have hgen : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)), α ^ 2 = 1 →
      Nat.card {f // α f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)) →
      (∃ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hm = MulAut.congr Θ α) → α ∈ H := by
    rintro α hα2 hαfix ⟨m, hm, hmα⟩
    refine Subgroup.subset_closure ⟨m, hm, hW m hm, hmα.symm, ?_⟩
    exact ⟨by rw [← map_pow, hα2, map_one],
      (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 hα2) hαfix).2⟩
  have hsH : ∀ i, sgnAut i ∈ H := fun i =>
    hgen _ (sgnAut_sq i) (card_fix_sgnAut hp hp2 i) (hS i)
  have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := fun a b hab =>
    hgen _ (permAut_swap_sq a b) (card_fix_permAut_swap hp hp2 hab) (hP _)
  have hmem := mem_of_isSignedPerm hsH htH (hN n hcN)
  rw [hH, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hmem
  rw [hv']
  exact hmem

end CFSG.StandardType

end
