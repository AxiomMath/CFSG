module

public import CFSG.LocalAnalysis.StandardType.GGN2Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNI1
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CRed
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CD4
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU5
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Nine
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Cube
import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GSurvBr
import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Fix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggN2I1_core {R : Type} [Group R] [Finite R]
    (hR : GGHasLabel (⟨.D, 4, 1⟩ : LargeEvenLabel) R)
    {r : R} (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) {K : Subgroup R}
    (hK : IsComponentOf K (Subgroup.centralizer ({r} : Set R)))
    (hKlab : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    {F : Subgroup R} (hF : IsElemAbelian 3 F) (hrF : r ∈ F)
    (hFK : ∀ e ∈ F, ∀ j ∈ K, e * j = j * e) : F ≤ Subgroup.zpowers r := by
  obtain ⟨Kf, hKf, hKffin, hKfcard, ⟨e0⟩⟩ := by
    unfold GGHasLabel at hR
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hR
    unfold LargeEvenRecipeOmegaPlus at hR
    exact hR
  have hKfcard2 : Nat.card Kf = 2 := by
    rw [hKfcard]
    norm_num
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_ringEquiv_zmod_two hKfcard2
  have eR : R ≃* CFSG.AGLEmbedding.Om8 :=
    e0.trans (CFSG.LocalAnalysis.GLTheoremA.CatB.statedProjEquivZMod2 φ
      (CFSG.LocalAnalysis.GLTheoremA.CatB.glCongr_statedOmega_plus φ 4))
  have hcatD4 : CFSG.Yardstones.Md0ec50421ce4.catalogIs R
      CFSG.LocalAnalysis.GLTheoremA.S9.isD4two :=
    CFSG.LocalAnalysis.GLTheoremA.I107G.catalogIs_of_model
      (TauCeti.CFSGIndex.lie ⟨.D 4 CFSG.LocalAnalysis.GLTheoremA.I107G.pp2,
        CFSG.LocalAnalysis.GLTheoremA.I107G.valid_D4⟩)
      (by
        show CFSG.LocalAnalysis.GLTheoremA.I107G.pp2.card = 2
        simp [CFSG.LocalAnalysis.GLTheoremA.I107G.pp2, TauCeti.PrimePower.card_def])
      (fun h => CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_d4two h) eR
  have hcatHost : CFSG.Yardstones.Md0ec50421ce4.catalogIs R
      CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.IsU42Host := by
    obtain ⟨i, hi, e⟩ := hcatD4
    exact ⟨i, Or.inl hi, e⟩
  have hcatKZ : CFSG.Yardstones.Md0ec50421ce4.catalogIs
      (↥K ⧸ Subgroup.center ↥K) CFSG.LocalAnalysis.GLTheoremA.S9.isU4two := by
    obtain ⟨K', hK'f, hK'fin, hK'card, ⟨eK⟩⟩ := by
      unfold GGHasLabel at hKlab
      dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hKlab
      unfold LargeEvenRecipeUnitary at hKlab
      exact hKlab
    have hK'card4 : Nat.card K' = 4 := by
      rw [hK'card]
      norm_num
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj hK'card4 eK
  have hU4 : CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.HasU4Quot K :=
    ⟨↥K ⧸ Subgroup.center ↥K, inferInstance, hcatKZ,
      ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _⟩⟩
  have hperf : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  have hrord : orderOf r = 3 := orderOf_eq_prime hr3 hr1
  obtain ⟨-, -, hgen, hZ⟩ :=
    LocalAnalysis.GLTheoremA.CatB.U42Cat.u42E27CentAt_of_hosts
        (LocalAnalysis.GLTheoremA.CatB.U42Cat.centShapeOn_of_centSplitOn
            LocalAnalysis.GLTheoremA.CatB.U42Cat.centSplitOn_Om8)
        (LocalAnalysis.GLTheoremA.CatB.U42Cat.centShapeOn_of_centSplitOn
            LocalAnalysis.GLTheoremA.CatB.U42Cat.centSplitOn_M5)
        (LocalAnalysis.GLTheoremA.CatB.U42Cat.centShapeOn_of_centSplitOn
            (LocalAnalysis.GLTheoremA.CatB.U42Cat.centSplitOn_S6_of
                LocalAnalysis.GLTheoremA.CatB.U42Cat.u6NineFact_holds
                LocalAnalysis.GLTheoremA.CatB.U42Cat.u6CubeFact_holds)) R hcatHost r hrord K hK.1 hperf hU4
  intro e he
  have heC : e ∈ Subgroup.centralizer ({r} : Set R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact (congrArg Subtype.val (hF.1.is_comm.comm ⟨e, he⟩ ⟨r, hrF⟩)).symm
  obtain ⟨n, k, hkK, hek⟩ := hgen e heC
  have hk_eq : k = (r ^ n)⁻¹ * e := by
    rw [hek]
    group
  have hecent : e ∈ Subgroup.centralizer (K : Set R) :=
    Subgroup.mem_centralizer_iff.mpr fun j hj => (hFK e he j hj).symm
  have hrcent : r ∈ Subgroup.centralizer (K : Set R) :=
    Subgroup.mem_centralizer_iff.mpr fun j hj => (hFK r hrF j hj).symm
  have hkcent : k ∈ Subgroup.centralizer (K : Set R) := by
    have h1 : (r ^ n)⁻¹ ∈ Subgroup.centralizer (K : Set R) :=
      (Subgroup.centralizer (K : Set R)).inv_mem
        ((Subgroup.centralizer (K : Set R)).pow_mem hrcent n)
    have h2 : (r ^ n)⁻¹ * e ∈ Subgroup.centralizer (K : Set R) :=
      (Subgroup.centralizer (K : Set R)).mul_mem h1 hecent
    rwa [← hk_eq] at h2
  have hkcenter : (⟨k, hkK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro j
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hkcent (j : R) j.2)
  have hk1 : k = 1 := by
    have hk1' : (⟨k, hkK⟩ : ↥K) = 1 := Subgroup.mem_bot.mp (hZ ▸ hkcenter)
    exact Subtype.ext_iff.mp hk1'
  refine Subgroup.mem_zpowers_iff.mpr ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, hek, hk1, mul_one]

end CFSG.StandardType

end
