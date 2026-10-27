module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepConjAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open E6Dep

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTPStdFrame {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    (hM : GGE6DepModelKnown) (hNI : GGE6DepNonIsoPt) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hinn : GGInnerDiagAll 3 B Bs x L D J)
    (hnt : GGNoTransvection 3 Bs) {y : G} {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K)
    (hE : GGE6DepPerpCfg 3 Bs L K) (hxL : x ∉ L) :
    ∃ (hxBs : x ∈ Bs) (hyBs : y ∈ Bs) (ι : Additive ↥Bs ≃+ E6Dep.Vec6),
      E6Dep.GGE6DepCoord Bs L x hxBs ι ∧ ι (Additive.ofMul ⟨y, hyBs⟩) = E6Dep.xs := by
  classical
  obtain ⟨hyBs, hxy, hKy, hxK⟩ := ggE6Dep_nbr_facts hcfg hnbr
  obtain ⟨-, hBs, -, hLx, -⟩ := hcfg.tableB_facts
  have hSC := hcfg.2.1.2.2.2
  obtain ⟨-, hcardBs, hD, lab₀, hlab₀, -, hmarkK⟩ := id hE
  obtain ⟨hBsN, hxBs, R, _, I, ψ, Φ, T, w, ι, hTB, hcard, hwith, hZ, hBsL, hι5, hιL, hιΦ, h₁, h₂,
    hNIP⟩ := ggE6Dep_frameL hRig hM hNI hcfg hinn.1 hE hxL
  have hι : GGE6DepCoord Bs L x hxBs ι := ⟨hι5, hιL, h₁, h₂⟩
  obtain ⟨Λ, _, _, b, ρ, ρa, hρrefl, hρa, hLgen, hKgen⟩ := ggDatum_reflections hD
  have hρK : ∀ l : Λ, l ≠ b → ρ l ∈ ggAutomizer K Bs := fun l hl => by
    rw [hKgen]
    exact Subgroup.subset_closure (Or.inl ⟨⟨l, hl⟩, rfl⟩)
  have hρy : ∀ l : Λ, l ≠ b → ρ l ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := fun l hl =>
    ggAutomizer_fix_of_centralizes hyBs hKy (ρ l) (hρK l hl)
  have hiso' : norm6 (hpart (ι (Additive.ofMul ⟨y, hyBs⟩))) ≠ 0 := by
    rw [hpart_eq_coordF_gamma hxBs hyBs hLx hBsL hBsN Φ hι5 hιL hιΦ]
    exact ggE6Dep_nonIso_of_prop hcfg hnbr hBsN hyBs hNIP ψ hTB hcard hwith
  obtain ⟨ι', c, g, hι', hyι, hg, hgfix, hS⟩ :=
    ggE6Dep_standardPosition hxBs hyBs hxy hι b ρ hρrefl hLgen hρy hiso'
  have hy1 : y ≠ 1 := fun h => hxy (h ▸ Subgroup.one_mem _)
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  have hSK : ∀ i : Fin 5, ∃ φ ∈ ggAutomizer K Bs, ActsAs ι' φ (gS i) := by
    intro i
    obtain ⟨φ, hφ, hact⟩ := hS i
    refine ⟨φ, ?_, hact⟩
    rw [hKgen]
    exact Subgroup.closure_mono Set.subset_union_left hφ
  have hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    ggE6Dep_centK hxBs hyBs hι'.1 hyι hSK hKy hxK
  obtain ⟨κ, hκ⟩ :=
    ggE6Dep_frameK hRig hM hy1 hBs hSC hcardBs hlab₀ hmarkK (hinn.2 y K hnbr) hker
  obtain ⟨s, t, u, w', hstu, hw0, hu, hφK⟩ :=
    ggE6Dep_glueK hyBs hy1 hy3 hcardBs hKy hyι hκ hρrefl hρa hKgen hg hgfix hS
  obtain ⟨hs0, hu0⟩ := ggE6Dep_noTv hnt hι'.2.2.2 hstu hw0 hφK
  subst hs0 hu0
  have htw : t * w' = 2 := by simpa using hstu
  have hc0 : c = 0 := by
    have key : ∀ a c : ZMod 3, a ≠ 0 → 0 + a * c = 0 → c = 0 := by decide +kernel
    exact key w' c hw0 hu
  subst hc0
  have hy0 : ι' (Additive.ofMul ⟨y, hyBs⟩) = xs := by
    rw [hyι]
    simp
  exact ⟨hxBs, hyBs, ι', hι', hy0⟩

end CFSG.StandardType

end
