module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

theorem qtwoDRMStab_normalizes (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hx : x ∈ Bs) {a : MulAut ↥Bs}
    (ha : a ∈ ggInduced ⊤ Bs) (hax : a ⟨x, hx⟩ = ⟨x, hx⟩) {w : MulAut ↥Bs}
    (hw : w ∈ ggAutomizer L Bs) : a * w * a⁻¹ ∈ ggAutomizer L Bs := by
  obtain ⟨g, -, hgN, hga⟩ := ha
  obtain ⟨l, hlL, hlN, hlw⟩ := mem_ggAutomizer_iff.mp hw
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := ha₀ G p B x L hcfg.1.1.1
  have hgx : g * x * g⁻¹ = x := by
    have h := hga ⟨x, hx⟩
    rw [hax] at h
    exact h.symm
  have hgC : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [hgx]
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_sstar hS hnc hgC
  have hainv : ∀ b : ↥Bs, ((a⁻¹ b : ↥Bs) : G) = g⁻¹ * (b : G) * g := by
    intro b
    have h := hga (a⁻¹ b)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group
  refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgL l).mp hlL
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN)
  · intro b
    simp only [MulAut.mul_apply]
    rw [hga, hlw, hainv]
    group

end CFSG.StandardType.QTwo

end
