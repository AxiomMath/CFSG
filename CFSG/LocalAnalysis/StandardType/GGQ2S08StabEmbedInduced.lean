module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08x2_induced_exists
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) (hx : x ∈ Bs) (ψ : MulAut ↥Bs)
    (hψ : ψ ∈ ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :
    ∃ g : G, g ∈ Subgroup.normalizer (Bs : Set G) ∧ g ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = g * b * g⁻¹ := by
  have hSstar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  obtain ⟨g, -, hgB, hg⟩ := mem_ggAutomizer_iff.mp hψ.1
  have hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    simpa [MulAut.smul_def] using (MulAction.mem_stabilizer_iff.mp hψ.2)
  have hgx : g * x * g⁻¹ = x := by
    have h2 := hg ⟨x, hx⟩
    rw [hψx] at h2
    exact h2.symm
  have hnx : g * x = x * g := by
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hgx]
  have hgZ : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    have h1 := Subgroup.normalizer_le_normalizer_closure ({x} : Set G)
      (Subgroup.centralizer_le_normalizer ({x} : Set G)
        (Subgroup.mem_centralizer_singleton_iff.mpr hnx))
    rw [← Subgroup.zpowers_eq_closure] at h1
    exact h1
  exact ⟨g, hgB, mem_normalizer_of_sstar' hSstar hnc hgZ, hg⟩

end CFSG.StandardType

end
