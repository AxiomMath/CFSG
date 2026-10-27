module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.StandardType.GGSecFiveJReflOfCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRoot
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRootJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPosDef
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen
import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.Timmesfeld.ARS.CaseERootSys

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem mem_ggAutomizer_of_ggRankOneIn_le {G : Type} [Group G] [Finite G] {X J Bs : Subgroup G}
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hr2 : r * r = 1)
    (hJ : ggRankOneIn X Bs r ≤ J) : r ∈ ggAutomizer J Bs := by
  obtain ⟨m, hmR, hmN, hm⟩ := ggExists_weylElt_of_mem_ggAutomizer hr hr2
  exact mem_ggAutomizer_iff.mpr ⟨m, hJ hmR, hmN, hm⟩

theorem ggWeyl_orderOf_conj_mul_conj_eq_three {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (w : (coxeterMatrix hA).Group) {a b : I}
    (hab : A a b = -1) (hba : A b a = -1) :
    orderOf (w * (coxeterMatrix hA).simple a * w⁻¹ *
      (w * (coxeterMatrix hA).simple b * w⁻¹)) = 3 := by
  have hconj : w * (coxeterMatrix hA).simple a * w⁻¹ *
      (w * (coxeterMatrix hA).simple b * w⁻¹) =
      MulAut.conj w ((coxeterMatrix hA).simple a * (coxeterMatrix hA).simple b) := by
    rw [MulAut.conj_apply]
    group
  rw [hconj, MulEquiv.orderOf_eq]
  have h := CoxeterSystem.orderOf_simple_mul_simple (coxeterMatrix hA).toCoxeterSystem a b
  rw [CoxeterMatrix.toCoxeterSystem_simple] at h
  rw [h]
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  rw [show A a b * A b a = 1 by rw [hab, hba]; norm_num, TauCeti.coxeterOrder_one]

section Frame

private theorem ggSecFiveJA2_refl_of_frame {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs L J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    {ε : (coxeterMatrix (ggU t n f).D.isFiniteType).Group ≃* ↥(ggAutomizer L Bs)}
    (hεrefl : ∀ i, GGIsReflection p
      ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer L Bs)) :
        MulAut ↥Bs))
    (hεlevi : ∀ (w : (coxeterMatrix (ggU t n f).D.isFiniteType).Group)
      (i : Fin (ggU t n f).D.rank),
      ggRankOneIn L Bs
        ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
        (ggRootLevi (ggU t n f).D
          (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ)
    {w : (coxeterMatrix (ggU t n f).D.isFiniteType).Group} {i : Fin (ggU t n f).D.rank}
    (hJ : (ggRootLevi (ggU t n f).D
      (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ ≤ J) :
    ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈ ggAutomizer J Bs ∧
      GGIsReflection p
        ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
  have hrA : ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs :=
    (ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)).2
  have hconj : ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
      ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
        ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) :
          ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
        ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  have hrefl : GGIsReflection p
      ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
        ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
    rw [hconj]
    exact GGIsReflection.conj' (hεrefl i) _
  have hr2 : ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
      ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
        ↥(ggAutomizer L Bs)) : MulAut ↥Bs) = 1 := by
    simpa [sq] using hrefl.1
  have hlev : ggRankOneIn L Bs
      ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
        ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ≤ J := by
    rw [hεlevi w i]
    exact hJ
  exact ⟨mem_ggAutomizer_of_ggRankOneIn_le hrA hr2 hlev, hrefl⟩

private theorem ggSecFiveJA2_orderOf_of_frame {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ε : (coxeterMatrix (ggU t n f).D.isFiniteType).Group ≃* ↥(ggAutomizer L Bs)}
    {w : (coxeterMatrix (ggU t n f).D.isFiniteType).Group}
    {a b : Fin (ggU t n f).D.rank}
    (hab : (ggU t n f).D.cartan a b = -1) (hba : (ggU t n f).D.cartan b a = -1) :
    orderOf (((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple a * w⁻¹) :
        ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
      ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple b * w⁻¹) :
        ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) = 3 := by
  have hmul : ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple a * w⁻¹) :
        ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
      ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple b * w⁻¹) :
        ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
      ((ε ((w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple a * w⁻¹) *
          (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple b * w⁻¹)) :
        ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
    rw [← Subgroup.coe_mul, ← map_mul]
  rw [hmul, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact ggWeyl_orderOf_conj_mul_conj_eq_three (ggU t n f).D.isFiniteType w hab hba

end Frame

theorem ggSecFiveJA2Input_of_lBalance
    (hL : GGLBalanceInput) : GGSecFiveJA2Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit
  have hcfg0 : GGSecFiveRouteCfg p B Bs x L D J 𝒦 := hcfg
  have ha₀ : GGLNoncyclicInput := ggLNoncyclicInput_holds
  obtain ⟨t, n, f, ψ, hloc, hstd, ε, hεrefl, hεlevi, -⟩ :=
    s2jn_exists_tableBFrame G p B Bs x L D J 𝒦 hcfg hsplit
  obtain ⟨r₀, hr₀, hrefl₀⟩ :=
    s2jn_ggSecFiveJReflInput'_of_core ggJRootCoreInput_holds G p B Bs x L D J 𝒦 hcfg hsplit
  obtain ⟨β, hβ, β', hβ', hsum⟩ :=
    ggKGCent_exists_root_add ha₀ hL hcfg0 hr₀ hrefl₀ (X := L) (Or.inl rfl) hloc hstd
  obtain ⟨⟨hp, hp2, hadm, hrank⟩, ⟨hker, -, ht, hpf⟩, -, -, -⟩ := id hloc
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, xp, C, O, hE⟩ :=
    ggStdPos_bruhatData (f := f) hrank ht
  have hNJ := SecFiveL1Odd.centralizer_le_normalizer_J ha₀ hcfg0
  have hDB := SecFiveL1Odd.le_bstar hcfg0
  have hlev : ∀ δ ∈ ggKGCentRoots (ggU t n f).D ψ D,
      (ggRootLevi (ggU t n f).D δ).map ψ ≤ J := by
    intro δ hδ
    have hδJ := ggKGCent_rootGroup_le ha₀ hL hcfg0 hr₀ hrefl₀ (X := L) (Or.inl rfl) hloc hstd hδ
    rw [ggRootLevi, Subgroup.map_sup]
    exact sup_le hδJ (ggKGCent_neg_mem hct hE hdiv ψ hker hstd hDB hNJ hδ hδJ).2
  have hβr : β ∈ roots (ggU t n f).D.isFiniteType ∅ := by
    rw [← hdiv]
    exact hβ.1
  have hβ'r : β' ∈ roots (ggU t n f).D.isFiniteType ∅ := by
    rw [← hdiv]
    exact hβ'.1
  have hsumr : β + β' ∈ roots (ggU t n f).D.isFiniteType ∅ := by
    rw [← hdiv]
    exact hsum
  have hpd := ggU_cartan_posDef (f := f) hrank ht
  obtain ⟨w, a, b, hab, hwa, hwb⟩ :=
    CFSG.Timmesfeld.ARS.exists_weylAction_pair (ggU t n f).D.isFiniteType hpd hβr hβ'r hsumr
  have hba : (ggU t n f).D.cartan b a = -1 := by
    rw [CFSG.Timmesfeld.ARS.cartan_symm_of_posDef hpd b a, hab]
  have hJa : (ggRootLevi (ggU t n f).D
      (weylAction (ggU t n f).D.isFiniteType w (Pi.single a 1))).map ψ ≤ J := by
    rw [hwa]
    exact hlev β hβ
  have hJb : (ggRootLevi (ggU t n f).D
      (weylAction (ggU t n f).D.isFiniteType w (Pi.single b 1))).map ψ ≤ J := by
    rw [hwb]
    exact hlev β' hβ'
  obtain ⟨hr, hrefl⟩ := ggSecFiveJA2_refl_of_frame (w := w) (i := a) hεrefl hεlevi hJa
  obtain ⟨hr', hrefl'⟩ := ggSecFiveJA2_refl_of_frame (w := w) (i := b) hεrefl hεlevi hJb
  exact ⟨_, hr, _, hr', hrefl, hrefl', ggSecFiveJA2_orderOf_of_frame (ε := ε) (w := w) hab hba⟩

end CFSG.StandardType

end
