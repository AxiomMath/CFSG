module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4Iso
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms

public section

namespace CFSG.StandardType.LieKnownR2.F4

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley

private theorem l10sf4c_noCentral_map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {R : Subgroup G} (h : GGRootNoCentralAt (⊤ : Subgroup G) R) :
    GGRootNoCentralAt (⊤ : Subgroup H) (R.map e.toMonoidHom) := by
  intro A B hRA hAB hB hNA hNB hc
  simp only [top_inf_eq] at hB hNA hNB hc
  refine ggRootNormNoCentral_map_mulEquiv e ?_ A B hRA hAB hB hNA hNB hc
  intro A' B' hRA' hAB' hB' hNA' hNB' hc'
  exact h A' B' hRA' hAB' (by simpa only [top_inf_eq] using hB')
    (by simpa only [top_inf_eq] using hNA') (by simpa only [top_inf_eq] using hNB')
    (by simpa only [top_inf_eq] using hc')

private theorem l10sf4c_noCentral_of_noCentralAt {G : Type} [Group G] {K R : Subgroup G}
    (hRK : R ≤ K) (h : GGRootNoCentralAt K R) :
    GGRootNormNoCentral (R.subgroupOf K) := by
  intro A B hRA hAB hBcore hNA hNB hcomm
  set N : Subgroup G := K ⊓ Subgroup.normalizer (R : Set G) with hNdef
  have hNK : Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) = N.subgroupOf K := by
    rw [hNdef, Subgroup.inf_subgroupOf_left]
    exact (Subgroup.subgroupOf_normalizer_eq hRK).symm
  have hcoreMap :
      (pCoreOf 2 (Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K))).map K.subtype =
        pCoreOf 2 N := by
    rw [hNK, GGRootNorm.pCoreOf_subgroupOf inf_le_left]
    exact Subgroup.map_subgroupOf_eq_of_le ((GGRootNorm.pCoreOf_le N).trans inf_le_left)
  have hnormMap : ∀ {S : Subgroup K},
      Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) ≤
        Subgroup.normalizer (S : Set K) →
      N ≤ Subgroup.normalizer ((S.map K.subtype : Subgroup G) : Set G) := by
    intro S hS
    rw [Subgroup.le_normalizer_iff]
    intro n hn x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hnK : (⟨n, hn.1⟩ : K) ∈
        Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) := by
      rw [hNK]
      exact Subgroup.mem_subgroupOf.mpr hn
    have hs' : (⟨n, hn.1⟩ : K) * s * (⟨n, hn.1⟩ : K)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hS hnK) s).mp hs
    exact Subgroup.mem_map.mpr ⟨_, hs', by simp⟩
  have hcommMap : ⁅B.map K.subtype, N⁆ ≤ A.map K.subtype := by
    have h1 : (⁅B, Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K)⁆).map K.subtype ≤
        A.map K.subtype := Subgroup.map_mono hcomm
    rwa [Subgroup.map_commutator, hNK, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h1
  have key := h (A.map K.subtype) (B.map K.subtype)
    (by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRK]
      exact Subgroup.map_mono hRA)
    (Subgroup.map_mono hAB) ((Subgroup.map_mono hBcore).trans (le_of_eq hcoreMap))
    (hnormMap hNA) (hnormMap hNB) hcommMap
  intro b hb
  exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp
    (key (Subgroup.mem_map_of_mem K.subtype hb))

private theorem l10sf4c_noCentral_maxHeight
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ₀ : Fin (f4Datum K).rank → ℤ} (hγ₀ : γ₀ ∈ (f4Datum K).roots)
    (hmax : ∀ δ ∈ (f4Datum K).roots, ∑ i, δ i ≤ ∑ i, γ₀ i) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(adjointGroup .F4 K)) ((f4Datum K).rootGroup γ₀) := by
  have hγθ : γ₀ = CFSG.SeitzReduction.highRoot .F4 :=
    Short.eq_highRoot_of_maxHeight_F4 K hγ₀ hmax
  have hR : (f4Datum K).rootGroup γ₀ =
      (rootSubgroup .F4 K (CFSG.SeitzReduction.highRoot .F4)).subgroupOf (adjointGroup .F4 K) := by
    rw [hγθ]
    change rootGroup (rootOperatorFamily .F4) K (CFSG.SeitzReduction.highRoot .F4) =
      (rootSubgroup .F4 K (CFSG.SeitzReduction.highRoot .F4)).subgroupOf (adjointGroup .F4 K)
    rw [rootGroup_of_isRoot (CFSG.SeitzReduction.isRoot_highRoot .F4)]
    exact ((rootOperatorFamily .F4).subgroupOf_rootSubgroup_eq K
      ⟨CFSG.SeitzReduction.highRoot .F4, CFSG.SeitzReduction.isRoot_highRoot .F4⟩).symm
  rw [hR]
  intro A B hRA hAB hB hNA hNB hc
  simp only [top_inf_eq] at hB hNA hNB hc
  exact l10sf4c_noCentral_of_noCentralAt
    (rootSubgroup_le_adjointGroup (CFSG.SeitzReduction.highRoot .F4))
    (ExcNC.rootNoCentral_highRoot_exc .F4 (Or.inr (Or.inr (Or.inr rfl))) K)
    A B hRA hAB hB hNA hNB hc

private theorem l10sf4c_noCentral_long
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {β : Fin (f4Datum K).rank → ℤ} (hl : GGLongRoot (f4Datum K) β) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(adjointGroup .F4 K)) ((f4Datum K).rootGroup β) := by
  obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hl
  have hNC : GGRootNoCentralAt (⊤ : Subgroup ↥(adjointGroup .F4 K))
      ((f4Datum K).rootGroup γ₀) :=
    l10sf4c_noCentral_maxHeight hγ₀ hmax
  have hct := Short.f4_isCTGroupDatum_exact K
  have hact := CFSG.LieType.Steinberg.actsAs_nrep hct w
  have hmap : ((f4Datum K).rootGroup γ₀).map
      (MulAut.conj (CFSG.LieType.Steinberg.nrep hct w)).toMonoidHom =
        (f4Datum K).rootGroup β := by
    rw [hact γ₀ hγ₀, ← hβeq]
  have h := l10sf4c_noCentral_map_mulEquiv
    (MulAut.conj (CFSG.LieType.Steinberg.nrep hct w)) hNC
  rwa [hmap] at h

private theorem l10sf4c_noCentral_root
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {β : Fin (f4Datum K).rank → ℤ} (hβ : β ∈ (f4Datum K).roots) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(adjointGroup .F4 K)) ((f4Datum K).rootGroup β) := by
  rcases Classical.em (GGLongRoot (f4Datum K) β) with hl | hs
  · exact l10sf4c_noCentral_long hl
  · obtain ⟨β', hβ', hmapβ, -, hlong⟩ :=
      Short.finiteExceptionalAut_F4_map_rootGroup K hβ
    have hNCβ' : GGRootNoCentralAt (⊤ : Subgroup ↥(adjointGroup .F4 K))
        ((f4Datum K).rootGroup β') := l10sf4c_noCentral_long (hlong.mpr hs)
    have hgoal : ((f4Datum K).rootGroup β').map
        (ReeTag.F4.finiteExceptionalAut K).symm.toMonoidHom =
          (f4Datum K).rootGroup β := by
      rw [← hmapβ]
      exact GGRootNorm.map_symm_map (ReeTag.F4.finiteExceptionalAut K) ((f4Datum K).rootGroup β)
    have h := l10sf4c_noCentral_map_mulEquiv
      (ReeTag.F4.finiteExceptionalAut K).symm hNCβ'
    rwa [hgoal] at h

theorem ggRootNoCentral_f4
    {n f : ℕ}
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (u : (ggU .F4 n f).K) :
    GGRootNoCentralAt (⊤ : Subgroup (ggU .F4 n f).K)
      (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u) := by
  have hNC : GGRootNoCentralAt (⊤ : Subgroup (ggU .F4 n f).K)
      ((ggU .F4 n f).D.rootGroup β) :=
    l10sf4c_noCentral_root (K := GaloisField 2 f) hβ
  have hmap : ((ggU .F4 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom =
      ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u := by
    simp only [ggRootSub, Subgroup.map_id]
  have h := l10sf4c_noCentral_map_mulEquiv (MulAut.conj u) hNC
  rwa [hmap] at h

theorem ggRootNoCentralAt_ggU_f4
    {n f : ℕ} {X : Type} [Group X] [Finite X]
    (φ : (ggU .F4 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .F4 n f).K)
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (u : (ggU .F4 n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .F4 n f).D φ β u) := by
  have hcenter : Subgroup.center (ggU .F4 n f).K = ⊥ :=
    center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)
  have hker_bot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hodd : Odd (Nat.card φ.ker) := by
    rw [hker_bot, Subgroup.card_bot]
    exact odd_one
  have hR : IsPGroup 2 (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u) :=
    Short.rootGroup_isPGroup_F4 hβ u rfl
  have hbase : GGRootNoCentralAt (⊤ : Subgroup (ggU .F4 n f).K)
      (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u) :=
    ggRootNoCentral_f4 hβ u
  have h := SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker φ hker hodd hR hbase
  have hgoal : (ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u).map φ =
      ggRootSub (ggU .F4 n f).D φ β u :=
    (Short.ggRootSub_eq_map (ggU .F4 n f).D φ β u).symm
  rwa [hgoal] at h

end CFSG.StandardType.LieKnownR2.F4
