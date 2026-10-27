module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ItemThree
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped commutatorElement

namespace CFSG.StandardType.LieKnownR2.POmega

private theorem forms_top_symm_map {E : Type} [Group E] (R : Subgroup E) :
    R.map (Subgroup.topEquiv (G := E)).symm.toMonoidHom = R.subgroupOf (⊤ : Subgroup E) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using hy
  · intro hx
    exact ⟨x.1, Subgroup.mem_subgroupOf.mp hx, Subtype.ext rfl⟩

private theorem forms_noCentral_of_noCentralAt {G : Type} [Group G] {K R : Subgroup G}
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

private theorem forms_inner_range_plus_of_eq
    {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp : 3 ≤ n) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadPlus n F), Spin.plusDatum n F hp⟩)
    {X : Type} [Group X] (φ : L.K →* X)
    (hker : φ.ker ≤ Subgroup.center L.K)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (u : L.K) :
    GGRootNormInner ((ggRootSub L.D φ β u).subgroupOf φ.range) := by
  subst hL
  have hcenter : Subgroup.center ↥(spinGroup (Spin.quadPlus n F)) = ⊥ :=
    CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := F) hp
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have h0 : GGRootNormInner
      (((Spin.plusDatum n F hp).rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    ggRootNormInner_spinPlus hn hβ u
  have hsub : GGRootNormInner
      ((((Spin.plusDatum n F hp).rootGroup β).map (MulAut.conj u).toMonoidHom).subgroupOf
        (⊤ : Subgroup ↥(spinGroup (Spin.quadPlus n F)))) := by
    rw [← forms_top_symm_map
      (((Spin.plusDatum n F hp).rootGroup β).map (MulAut.conj u).toMonoidHom)]
    exact ggRootNormInner_map_mulEquiv
      (Subgroup.topEquiv (G := ↥(spinGroup (Spin.quadPlus n F)))).symm h0
  refine ggRootNormInner_of_map_injective φ hφinj (K' := ⊤)
    (R' := ((Spin.plusDatum n F hp).rootGroup β).map (MulAut.conj u).toMonoidHom)
    (K := φ.range) (R := ggRootSub (Spin.plusDatum n F hp) φ β u) ?_ rfl hsub
  rw [Subgroup.map_top]

private theorem forms_inner_range_minus_of_eq
    {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadMinus n F b c), Spin.Twisted.minusDatum n hirr⟩)
    {X : Type} [Group X] (φ : L.K →* X)
    (hker : φ.ker ≤ Subgroup.center L.K)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots)
    (hl : GGLongRoot L.D β) (u : L.K) :
    GGRootNormInner ((ggRootSub L.D φ β u).subgroupOf φ.range) := by
  subst hL
  have hcenter : Subgroup.center ↥(spinGroup (Spin.quadMinus n F b c)) = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn hirr
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have h0 : GGRootNormInner
      (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    ggRootNormInner_spinMinus hn hirr hβ hl u
  have hsub : GGRootNormInner
      ((((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom).subgroupOf
        (⊤ : Subgroup ↥(spinGroup (Spin.quadMinus n F b c)))) := by
    rw [← forms_top_symm_map
      (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom)]
    exact ggRootNormInner_map_mulEquiv
      (Subgroup.topEquiv (G := ↥(spinGroup (Spin.quadMinus n F b c)))).symm h0
  refine ggRootNormInner_of_map_injective φ hφinj (K' := ⊤)
    (R' := ((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom)
    (K := φ.range) (R := ggRootSub (Spin.Twisted.minusDatum n hirr) φ β u) ?_ rfl hsub
  rw [Subgroup.map_top]

private theorem forms_noCentralAt_plus_of_eq
    {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp : 3 ≤ n) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadPlus n F), Spin.plusDatum n F hp⟩)
    {X : Type} [Group X] (φ : L.K →* X)
    (hker : φ.ker ≤ Subgroup.center L.K)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) (u : L.K) :
    GGRootNoCentralAt φ.range (ggRootSub L.D φ β u) := by
  subst hL
  have hcenter : Subgroup.center ↥(spinGroup (Spin.quadPlus n F)) = ⊥ :=
    CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := F) hp
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have h0 : GGRootNoCentralAt (⊤ : Subgroup ↥(spinGroup (Spin.quadPlus n F)))
      (((Spin.plusDatum n F hp).rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    ggRootNoCentral_spinPlus hn hβ u
  have hsub : GGRootNormNoCentral
      ((((Spin.plusDatum n F hp).rootGroup β).map (MulAut.conj u).toMonoidHom).subgroupOf
        (⊤ : Subgroup ↥(spinGroup (Spin.quadPlus n F)))) :=
    forms_noCentral_of_noCentralAt le_top h0
  have hmain : GGRootNormNoCentral
      ((ggRootSub (Spin.plusDatum n F hp) φ β u).subgroupOf φ.range) := by
    refine ggRootNormNoCentral_of_map_injective φ hφinj (K' := ⊤)
      (R' := ((Spin.plusDatum n F hp).rootGroup β).map (MulAut.conj u).toMonoidHom)
      (K := φ.range) (R := ggRootSub (Spin.plusDatum n F hp) φ β u) ?_ rfl hsub
    rw [Subgroup.map_top]
  exact ggRootNormNoCentral_ambient (Subgroup.map_le_range _ _) hmain

private theorem forms_noCentralAt_minus_of_eq
    {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (L : LieUniversal)
    (hL : L = ⟨spinGroup (Spin.quadMinus n F b c), Spin.Twisted.minusDatum n hirr⟩)
    {X : Type} [Group X] (φ : L.K →* X)
    (hker : φ.ker ≤ Subgroup.center L.K)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots)
    (hl : GGLongRoot L.D β) (u : L.K) :
    GGRootNoCentralAt φ.range (ggRootSub L.D φ β u) := by
  subst hL
  have hcenter : Subgroup.center ↥(spinGroup (Spin.quadMinus n F b c)) = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn hirr
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have h0 : GGRootNoCentralAt (⊤ : Subgroup ↥(spinGroup (Spin.quadMinus n F b c)))
      (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    ggRootNoCentral_spinMinus hn hirr hβ hl u
  have hsub : GGRootNormNoCentral
      ((((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom).subgroupOf
        (⊤ : Subgroup ↥(spinGroup (Spin.quadMinus n F b c)))) :=
    forms_noCentral_of_noCentralAt le_top h0
  have hmain : GGRootNormNoCentral
      ((ggRootSub (Spin.Twisted.minusDatum n hirr) φ β u).subgroupOf φ.range) := by
    refine ggRootNormNoCentral_of_map_injective φ hφinj (K' := ⊤)
      (R' := ((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom)
      (K := φ.range) (R := ggRootSub (Spin.Twisted.minusDatum n hirr) φ β u) ?_ rfl hsub
    rw [Subgroup.map_top]
  exact ggRootNormNoCentral_ambient (Subgroup.map_le_range _ _) hmain

theorem ggRootInnerAt_ggU_pomegaPlus
    {n f : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (φ : (ggU .POmegaPlus n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    {β : Fin (ggU .POmegaPlus n f).D.rank → ℤ} (hβ : β ∈ (ggU .POmegaPlus n f).D.roots)
    (u : (ggU .POmegaPlus n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .POmegaPlus n f).D φ β u) := by
  have hn3 : 3 ≤ n := by omega
  have e : ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
      Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  have hI := forms_inner_range_plus_of_eq (F := GaloisField 2 f) hn hn3
    (ggU .POmegaPlus n f) e φ hker hβ u
  intro Y hY2 hYK hYR hNY
  refine ggRootNormInner_le_sup_centralizer ?_ hYK hYR hY2 hNY hI
  exact Subgroup.map_le_range _ _

theorem itemThree_ggU_pomegaPlus
    {n f : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (ψ : (ggU .POmegaPlus n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    {β : Fin (ggU .POmegaPlus n f).D.rank → ℤ} (hβ : β ∈ (ggU .POmegaPlus n f).D.roots)
    (u : (ggU .POmegaPlus n f).K) {R : Subgroup X}
    (hR : R = ggRootSub (ggU .POmegaPlus n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have hn3 : 3 ≤ n := by omega
  have e : ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
      Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  have hI := forms_inner_range_plus_of_eq (F := GaloisField 2 f) hn hn3
    (ggU .POmegaPlus n f) e ψ hker hβ u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

theorem ggRootNoCentralAt_ggU_pomegaPlus
    {n f : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (φ : (ggU .POmegaPlus n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    {β : Fin (ggU .POmegaPlus n f).D.rank → ℤ} (hβ : β ∈ (ggU .POmegaPlus n f).D.roots)
    (u : (ggU .POmegaPlus n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .POmegaPlus n f).D φ β u) := by
  have hn3 : 3 ≤ n := by omega
  have e : ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
      Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  exact forms_noCentralAt_plus_of_eq (F := GaloisField 2 f) hn hn3
    (ggU .POmegaPlus n f) e φ hker hβ u

theorem ggRootInnerAt_ggU_pomegaMinus
    {n f : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (φ : (ggU .POmegaMinus n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    {β : Fin (ggU .POmegaMinus n f).D.rank → ℤ} (hβ : β ∈ (ggU .POmegaMinus n f).D.roots)
    (hl : GGLongRoot (ggU .POmegaMinus n f).D β) (u : (ggU .POmegaMinus n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .POmegaMinus n f).D φ β u) := by
  have e : ggU .POmegaMinus n f = ⟨spinGroup (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
      Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ := by
    simp only [ggU, lieUniversal]
  have hI := forms_inner_range_minus_of_eq hn (minusCoeffs_irr 2 f)
    (ggU .POmegaMinus n f) e φ hker hβ hl u
  intro Y hY2 hYK hYR hNY
  refine ggRootNormInner_le_sup_centralizer ?_ hYK hYR hY2 hNY hI
  exact Subgroup.map_le_range _ _

theorem itemThree_ggU_pomegaMinus
    {n f : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (ψ : (ggU .POmegaMinus n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    {β : Fin (ggU .POmegaMinus n f).D.rank → ℤ} (hβ : β ∈ (ggU .POmegaMinus n f).D.roots)
    (hl : GGLongRoot (ggU .POmegaMinus n f).D β) (u : (ggU .POmegaMinus n f).K) {R : Subgroup X}
    (hR : R = ggRootSub (ggU .POmegaMinus n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have e : ggU .POmegaMinus n f = ⟨spinGroup (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
      Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ := by
    simp only [ggU, lieUniversal]
  have hI := forms_inner_range_minus_of_eq hn (minusCoeffs_irr 2 f)
    (ggU .POmegaMinus n f) e ψ hker hβ hl u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

theorem ggRootNoCentralAt_ggU_pomegaMinus
    {n f : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] [Finite X]
    (φ : (ggU .POmegaMinus n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    {β : Fin (ggU .POmegaMinus n f).D.rank → ℤ} (hβ : β ∈ (ggU .POmegaMinus n f).D.roots)
    (hl : GGLongRoot (ggU .POmegaMinus n f).D β) (u : (ggU .POmegaMinus n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .POmegaMinus n f).D φ β u) := by
  have e : ggU .POmegaMinus n f = ⟨spinGroup (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
      Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ := by
    simp only [ggU, lieUniversal]
  exact forms_noCentralAt_minus_of_eq hn (minusCoeffs_irr 2 f)
    (ggU .POmegaMinus n f) e φ hker hβ hl u

end CFSG.StandardType.LieKnownR2.POmega
