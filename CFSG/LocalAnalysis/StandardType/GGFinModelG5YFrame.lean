module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5YBasic
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5LangDatum
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5RankOne
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Bridge
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section YFrame

theorem ggG5_Y_frame_refl
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} (n : ℕ) (hf : 1 ≤ f)
    (F : GGLangFrame t p f ht) {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hβ : β ∈ F.frame) :
    ggG5_Y F (rootReflection (ggLangReidx (rank_eq_langTag f ht) β)) ∈
      (ggIota t n f hf).range := by
  let hR := rank_eq_langTag f ht
  let α : Fin (langTag t).rank → ℤ := ggLangReidx hR β
  have hα : IsRoot (langTag t) α := by
    dsimp only [α]
    exact (mem_roots_iff_isRoot f ht β).1 (F.frame_root β hβ)
  have hgraph : ggGraphLat t α = α := by
    dsimp only [α]
    exact F.frame_graph β hβ
  have hπ : permLattice ((finCongr hR).permCongr (piB t p f)) α = α := by
    have h0 := congrArg (ggLangReidx hR) (F.frame_fixed β hβ)
    rw [ggReidx_latPerm_permLattice hR (piB t p f) β] at h0
    simpa only [α] using h0
  have hcanon : canonicalRep (coxeterSystem (langTag t)) GGL (rootReflection α) =
      rootSL2 (langTag t) GGL α (nSL (1 : GGLˣ)) := by
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo
      (M := GGL) hα]
    rfl
  have hYeq : ggG5_Y F (rootReflection α) =
      rootSL2 (langTag t) GGL α (F.z * nSL (1 : GGLˣ) * F.z⁻¹) := by
    rw [ggG5_Y, hcanon]
    exact F.act β hβ (nSL (1 : GGLˣ))
  have hYfix : ggG5_Y F (rootReflection α) ∈ F.M.D.fix :=
    ggG5_Y_mem_fix F (rootReflection α) (ggG5_commPi_reflection ht hα hπ)
  have hPhiY : ggPhi t f (rootSL2 (langTag t) GGL α
        (F.z * nSL (1 : GGLˣ) * F.z⁻¹)) =
      rootSL2 (langTag t) GGL α (F.z * nSL (1 : GGLˣ) * F.z⁻¹) := by
    have h := ((LangDatum.mem_fix (D := F.M.D)).1 hYfix).2
    rw [F.M.hΦ] at h
    exact (congrArg (fun z => ggPhi t f z) hYeq.symm).trans (h.trans hYeq)
  have hFrA : Matrix.SpecialLinearGroup.map (ggFrobT f)
        (F.z * nSL (1 : GGLˣ) * F.z⁻¹) = F.z * nSL (1 : GGLˣ) * F.z⁻¹ := by
    apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (K := GGL) α
    rw [← ggG5_phi_rootSL2 ht f hα hgraph]
    exact hPhiY
  have hA₀ : F.z * nSL (1 : GGLˣ) * F.z⁻¹ ∈ ratSL2 f := by
    change Matrix.SpecialLinearGroup.map (ggFrobT f)
        (F.z * nSL (1 : GGLˣ) * F.z⁻¹) =
      (MonoidHom.id (SL2 GGL)) (F.z * nSL (1 : GGLˣ) * F.z⁻¹)
    simpa using hFrA
  have hYrat : ggG5_Y F (rootReflection α) ∈ ratRankOne t f α := by
    rw [ggG5_ratRankOne_eq ht f hα hgraph]
    exact Subgroup.mem_map.mpr ⟨_, hA₀, hYeq.symm⟩
  obtain ⟨δ, hδ, hmap⟩ := ggG5_bridge_lang ht n f hf hα hgraph
  have hYmap : ggG5_Y F (rootReflection α) ∈
      (((ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)).map
        (ggIotaK t n f hf)) := by
    rw [hmap]
    exact hYrat
  obtain ⟨k, hk, hkY⟩ := Subgroup.mem_map.mp hYmap
  refine ⟨QuotientGroup.mk k, ?_⟩
  change ggIotaK t n f hf k = ggG5_Y F (rootReflection α)
  exact hkY

end YFrame

end CFSG.StandardType.GGFinModel.G5
