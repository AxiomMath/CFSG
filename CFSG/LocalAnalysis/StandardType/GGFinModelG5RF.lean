module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5RankOne
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Transfer
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Bridge
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5FrameRank
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5WeylDict
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Theta
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Plain
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Conj
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section RF

private theorem g5_mem_normalizer_conj {G : Type*} [Group G] (H : Subgroup G) (x Y : G) :
    Y * x * Y⁻¹ ∈ Subgroup.normalizer
        ((H.map (MulAut.conj Y).toMonoidHom : Subgroup G) : Set G) ↔
      x ∈ Subgroup.normalizer (H : Set G) := by
  have key : (H.map (MulAut.conj Y).toMonoidHom).map (MulAut.conj (Y * x * Y⁻¹)).toMonoidHom
      = (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj Y).toMonoidHom :=
    (Subgroup.map_map_conj H (MulAut.conj Y).toMonoidHom x).symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
  change (H.map (MulAut.conj Y).toMonoidHom).map (MulAut.conj (Y * x * Y⁻¹)).toMonoidHom
      = H.map (MulAut.conj Y).toMonoidHom ↔
    H.map (MulAut.conj x).toMonoidHom = H
  rw [key]
  constructor
  · intro h
    exact Subgroup.map_injective (MulAut.conj Y).injective h
  · intro h
    rw [h]

private theorem g5_mem_centralizer_conj {G : Type*} [Group G] (H : Subgroup G) (x Y : G) :
    Y * x * Y⁻¹ ∈ Subgroup.centralizer
        ((H.map (MulAut.conj Y).toMonoidHom : Subgroup G) : Set G) ↔
      x ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx k hk
    have h1 : Y * k * Y⁻¹ ∈ (H.map (MulAut.conj Y).toMonoidHom : Subgroup G) :=
      Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    have h2 := hx (Y * k * Y⁻¹) h1
    calc k * x = Y⁻¹ * ((Y * k * Y⁻¹) * (Y * x * Y⁻¹)) * Y := by group
      _ = Y⁻¹ * ((Y * x * Y⁻¹) * (Y * k * Y⁻¹)) * Y := by rw [h2]
      _ = x * k := by group
  · intro hx h hh
    obtain ⟨k, hk, hkY⟩ := Subgroup.mem_map.mp hh
    have hkY' : h = Y * k * Y⁻¹ := by
      rw [← hkY]
      rfl
    rw [hkY']
    have h2 := hx k hk
    calc (Y * k * Y⁻¹) * (Y * x * Y⁻¹) = Y * (k * x) * Y⁻¹ := by group
      _ = Y * (x * k) * Y⁻¹ := by rw [h2]
      _ = (Y * x * Y⁻¹) * (Y * k * Y⁻¹) := by group

private theorem g5_conj_conj_map {C : Type*} [Group C] (S : Subgroup C) (a : C) :
    (S.map (MulAut.conj : C →* MulAut C)).map (MulAut.conj (MulAut.conj a)).toMonoidHom
      = (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj : C →* MulAut C) :=
  (Subgroup.map_map_conj S (MulAut.conj : C →* MulAut C) a).symm

theorem ggG5_rf
    {t : StatedLieTag} {n f p : ℕ} [NeZero p] {ht : GGExcFive t} (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) (F : GGLangFrame t p f ht) :
    GGClauseRF t n f p (ggPsiU t n f) (F.M.torusData (n := n) hf hp hp2 hreg).ggBfull (piB t p f)
      (F.M.torusData (n := n) hf hp hp2 hreg).ggCoord := by
  classical
  let hT := F.M.torusData (n := n) hf hp hp2 hreg
  intro α hα hfix
  obtain ⟨β, hβF, u₀, hu₀, hu₀α⟩ := F.cover_rf α hα hfix
  have hβroots : β ∈ (ggU (absTag t) 6 f).D.roots := F.frame_root β hβF
  have hβ' : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β) :=
    (mem_roots_iff_isRoot f ht β).mp hβroots
  have hfix' : ggGraphLat t (ggLangReidx (rank_eq_langTag f ht) β) =
      ggLangReidx (rank_eq_langTag f ht) β := F.frame_graph β hβF
  obtain ⟨δ, hδclass, hδR⟩ := ggG5_bridge_lang ht n f hf hβ' hfix'
  have hYmem : F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u₀ * F.M.D.g0⁻¹ ∈
      (ggIota t n f hf).range := ggG5_Y_mem_range n hf hp hp2 hreg F u₀ hu₀
  obtain ⟨c, hc⟩ := hYmem
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (N := Subgroup.center (ggU t n f).K) c
  have hιk : ggIotaK t n f hf k =
      F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u₀ * F.M.D.g0⁻¹ := by
    rw [ggIotaK, MonoidHom.comp_apply, hk, hc]
  let Y : ModGL (langTag t) GGL :=
    F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u₀ * F.M.D.g0⁻¹
  let a : GGKb t n f := QuotientGroup.mk' (Subgroup.center (ggU t n f).K) k
  let R : Subgroup (ggU t n f).K := (ggU t n f).D.rootGroup δ ⊔ (ggU t n f).D.rootGroup (-δ)
  let S₀ : Subgroup (GGKb t n f) := R.map (QuotientGroup.mk' (Subgroup.center (ggU t n f).K))
  let S : Subgroup (GGKb t n f) := S₀.map (MulAut.conj a).toMonoidHom
  have hψ : ggPsiU t n f = (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)).comp
      (QuotientGroup.mk' (Subgroup.center (ggU t n f).K)) := rfl
  have hψk : ggPsiU t n f k = MulAut.conj a := rfl
  have hιa : ggIota t n f hf a = Y := by
    change ggIota t n f hf (QuotientGroup.mk' (Subgroup.center (ggU t n f).K) k) =
      F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u₀ * F.M.D.g0⁻¹
    rw [← hιk]
    rfl
  have hS₀ι : S₀.map (ggIota t n f hf) =
      ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β) := by
    change (R.map (QuotientGroup.mk' (Subgroup.center (ggU t n f).K))).map (ggIota t n f hf)
      = ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β)
    rw [Subgroup.map_map]
    change R.map (ggIotaK t n f hf) = ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β)
    exact hδR
  have hmapψ : R.map (ggPsiU t n f) =
      S₀.map (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)) := by
    rw [hψ, ← Subgroup.map_map]
  have hJ : (ggRankOneSub (ggU t n f).D (ggPsiU t n f) δ).map
        (MulAut.conj (ggPsiU t n f k)).toMonoidHom
      = S.map (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f)) := by
    change ((R : Subgroup (ggU t n f).K).map (ggPsiU t n f)).map
        (MulAut.conj (ggPsiU t n f k)).toMonoidHom
      = (S₀.map (MulAut.conj a).toMonoidHom).map
          (MulAut.conj : GGKb t n f →* MulAut (GGKb t n f))
    rw [hmapψ, hψk]
    exact g5_conj_conj_map S₀ a
  have hcomp : (ggIota t n f hf).comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (ggIota t n f hf a)).toMonoidHom.comp (ggIota t n f hf) := by
    apply MonoidHom.ext
    intro c
    show ggIota t n f hf (a * c * a⁻¹) =
      ggIota t n f hf a * ggIota t n f hf c * (ggIota t n f hf a)⁻¹
    simp only [map_mul, map_inv]
  have hSι : S.map (ggIota t n f hf) =
      (ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β)).map
        (MulAut.conj Y).toMonoidHom := by
    change (S₀.map (MulAut.conj a).toMonoidHom).map (ggIota t n f hf) =
      (ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β)).map
        (MulAut.conj Y).toMonoidHom
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hS₀ι, hιa]
  refine ⟨δ, k, hδclass, ?_, ?_⟩
  ·
    intro b hb
    obtain ⟨z, hz⟩ := hb
    obtain ⟨z', hz'eq, _hz'char⟩ := ggG5_Y_conj_uMap (ht := ht) F hT u₀ hu₀ z
    have hYrel : hT.uMap z = Y * hT.uMap z' * Y⁻¹ := by
      change hT.uMap z =
        (F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u₀ * F.M.D.g0⁻¹) *
          hT.uMap z' *
        (F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u₀ * F.M.D.g0⁻¹)⁻¹
      rw [← hz'eq]
      group
    rw [← hz, hJ]
    refine (ggG5_normalizer_iff (ht := ht) hT z S).mpr ?_
    rw [hSι, hYrel]
    exact (g5_mem_normalizer_conj (ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β))
      (hT.uMap z') Y).mpr (ggG5_frame_normalizer (ht := ht) F hT hβF z')
  ·
    intro b
    have hb_mem : (b : MulAut (GGKb t n f)) ∈ hT.ggBfull := Subtype.coe_prop b
    obtain ⟨z, hz⟩ := hb_mem
    have hb' : b = ⟨hT.ggBetaHom z, ⟨z, rfl⟩⟩ := Subtype.ext hz.symm
    obtain ⟨z', hz'eq, hz'char⟩ := ggG5_Y_conj_uMap (ht := ht) F hT u₀ hu₀ z
    have hYrel : hT.uMap z = Y * hT.uMap z' * Y⁻¹ := by
      change hT.uMap z =
        (F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u₀ * F.M.D.g0⁻¹) *
          hT.uMap z' *
        (F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u₀ * F.M.D.g0⁻¹)⁻¹
      rw [← hz'eq]
      group
    have hcoord : Multiplicative.toAdd (hT.ggCoord ⟨hT.ggBetaHom z, ⟨z, rfl⟩⟩) =
        (Multiplicative.toAdd z).1 := by
      rw [hT.ggCoord_apply z]
      rfl
    rw [hb', hJ, hcoord]
    rw [(ggG5_centralizer_iff (ht := ht) hT z S)]
    rw [hSι, hYrel]
    rw [(g5_mem_centralizer_conj (ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β))
      (hT.uMap z') Y)]
    rw [(ggG5_frame_centralizer_iff (ht := ht) F hT hβF z')]
    rw [hz'char β α hu₀α.symm]

end RF

end CFSG.StandardType.GGFinModel.G5
