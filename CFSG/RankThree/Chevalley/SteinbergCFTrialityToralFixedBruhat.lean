module

public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

theorem graphFixed_toral_centralizer_Bruhat_factors (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) (a : Fin t.tag.rank → Kˣ) {g : ModGL t.tag K}
    (hg : g ∈ graphFixedRootGroup t K σ.toRingHom)
    (hga : g ∈ Subgroup.centralizer {rootDiagUnit t.tag a}) :
    ∃ w ∈ relWeylTwist t, w ∈ rootCharStabilizer a ∧
      ∃ h ∈ graphFixedRootTorus t K σ.toRingHom,
      ∃ u ∈ rootSpan t.tag K (rootCharKernel a ∩ {α | IsRoot t.tag α ∧ 0 < height α}) ⊓
          twistedFixedGroup t K σ.toRingHom,
      ∃ v ∈ rootSpan t.tag K (rootCharKernel a ∩ inversionSet w) ⊓
          twistedFixedGroup t K σ.toRingHom,
        g = h * u * canonicalRep (coxeterSystem t.tag) K w * v := by
  obtain ⟨hX, huniq, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors t.tag K a
  have hgC : g ∈ adjointGroup t.tag K :=
    ((mem_twistedFixedGroup_iff_twistHom t K σ.toRingHom).1
      (graphFixedRootGroup_le t K σ.toRingHom hg)).1
  obtain ⟨w, hwa, h, hh, u, hu, v, hv, rfl⟩ := hX _ (Subgroup.mem_inf.2 ⟨hgC, hga⟩)
  have hg' : h * u * canonicalRep (coxeterSystem t.tag) K w * v ∈
      (graphFixedRootGroup t K σ.toRingHom : Set (ModGL t.tag K)) := hg
  rw [graphFixedRootGroup_eq_iUnion σ.surjective, Set.mem_iUnion] at hg'
  obtain ⟨⟨w', hw'⟩, hcell⟩ := hg'
  obtain ⟨⟨b, v₁⟩, ⟨hb, hv₁⟩, hbv⟩ := (bijOn_graphFixedRootBruhatCell σ.surjective hw').2.2 hcell
  simp only at hb hv₁ hbv
  have hb' : b ∈ (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
      (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) := by
    rw [← graphFixedRootBorel_eq_mul σ.surjective]
    exact hb
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hb'
  have hh₁T : h₁ ∈ torusGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh₁).1).1
  have hu₁U : u₁ ∈ posUnipotent t.tag K := (Subgroup.mem_inf.1 hu₁).1
  have huU : u ∈ posUnipotent t.tag K := (rootSpan_mono Set.inter_subset_right) hu
  have hvI : v ∈ rootSpan t.tag K (inversionSet w) := (rootSpan_mono Set.inter_subset_right) hv
  obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq w w' h h₁ u u₁ v v₁ hh hh₁T huU hu₁U hvI
    (Subgroup.mem_inf.1 hv₁).1 hbv.symm
  exact ⟨w, hw', hwa, h, hh₁, u, Subgroup.mem_inf.2 ⟨hu, (Subgroup.mem_inf.1 hu₁).2⟩, v,
    Subgroup.mem_inf.2 ⟨hv, (Subgroup.mem_inf.1 hv₁).2⟩, rfl⟩

end CFSG.RankThree.Chevalley
