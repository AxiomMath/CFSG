module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeGL
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCommutant
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsPiGL

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.StandardType.LayerFacts
open CFSG.RankThree.PartOne.KCLinComm
open Matrix

private theorem ggA6_SL_coreFamily_aux {F : Type} [Field F] [Finite F] [CharP F 2] (N : ℕ)
    (P : Subgroup (GL (Fin N) F)) (hP : Odd (Nat.card P)) :
    ∃ (β : Type) (S : β → Subgroup (GL (Fin N) F)),
      LayerCores.IsCoreFamily (Matrix.SpecialLinearGroup.toGL.range ⊓
        Subgroup.centralizer (P : Set (GL (Fin N) F))) S ∧
      ∀ c, GGA6CharTwoLie ↥(S c) := by
  classical
  have hA : (Nat.card P : F) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ Nat.card P := (CharP.cast_eq_zero_iff F 2 (Nat.card P)).mp h0
    obtain ⟨k, hk⟩ := h2
    obtain ⟨j, hj⟩ := hP
    omega
  obtain ⟨r, D, d, _, _, _, θ, hθinj, hθrange⟩ :=
    LayerFacts.exists_piGL_centralizer (n := N) P hA
  haveI : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D i)).injective 2
  let β := {b : Fin r // GoodBlock D d b}
  let S : β → Subgroup (GL (Fin N) F) := fun b => (blockSL D d b.1).map θ
  have hSmap : ∀ b, S b = (blockSL D d b.1).map θ := fun b => rfl
  have hcore : LayerCores.IsCoreFamily θ.range S := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro b
      rw [hSmap b]
      exact Subgroup.map_le_range θ _
    · intro b u hu s hs
      rw [hSmap b] at hs
      obtain ⟨v, rfl⟩ := hu
      obtain ⟨w, hw, rfl⟩ := hs
      exact ⟨v * w * v⁻¹, conj_mem_blockSL b.1 v hw, by rw [map_mul, map_mul, map_inv]⟩
    · intro b
      rw [hSmap b]
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective (blockSL D d b.1) θ hθinj)
        (isQuasisimple_blockSL b.1 b.2.1 b.2.2)
    · obtain ⟨k, hk⟩ := exists_derivedSeries_le_goodSL (E := D) (m := d)
      refine ⟨k, ?_⟩
      have h1 : ggDer θ.range k = (derivedSeries (PiGL D d) k).map θ := by
        rw [← ggDer_top (G := PiGL D d) k, map_ggDer θ (⊤ : Subgroup (PiGL D d)) k,
          Subgroup.map_top]
      rw [h1]
      calc (derivedSeries (PiGL D d) k).map θ ≤ (goodSL D d).map θ := Subgroup.map_mono hk
        _ = ⨆ b, S b := by
            rw [goodSL, Subgroup.map_iSup]
    · intro z hz hzc hz2
      have hgoodmap : (⨆ b, S b) = (goodSL D d).map θ := by
        rw [goodSL, Subgroup.map_iSup]
      rw [hgoodmap] at hz hzc
      obtain ⟨w, hw, rfl⟩ := hz
      have hw2 : w ^ 2 = 1 := hθinj (by rw [map_pow, hz2, map_one])
      have hwc : ∀ y ∈ goodSL D d, w * y = y * w := by
        intro y hy
        apply hθinj
        rw [map_mul, map_mul]
        exact hzc (θ y) (Subgroup.mem_map_of_mem θ hy)
      rw [eq_one_of_mem_goodSL_of_commute hw hwc hw2, map_one]
  have hSC : ∀ b, S b ≤ Matrix.SpecialLinearGroup.toGL.range ⊓
      Subgroup.centralizer (P : Set (GL (Fin N) F)) := by
    intro b x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hle : S b ≤ Matrix.SpecialLinearGroup.toGL.range := by
        have hperf : ⁅S b, S b⁆ = S b :=
          ggCommutator_eq_of_isQuasisimple (hcore.2.2.1 b)
        calc S b = ⁅S b, S b⁆ := hperf.symm
          _ ≤ ⁅(⊤ : Subgroup (GL (Fin N) F)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
          _ ≤ Matrix.SpecialLinearGroup.toGL.range := by
              rw [SpecialLinearGroup.range_toGL_eq_ker_det]
              exact Abelianization.commutator_subset_ker GeneralLinearGroup.det
      exact hle hx
    · show x ∈ Subgroup.centralizer (P : Set (GL (Fin N) F))
      have hle : S b ≤ Subgroup.centralizer (P : Set (GL (Fin N) F)) := by
        rw [← hθrange]
        exact Subgroup.map_le_range θ _
      exact hle hx
  refine ⟨β, S, ?_, ?_⟩
  · exact hcore.mono (by rw [← hθrange]; exact inf_le_right) hSC
  · intro b
    haveI : CharP (D b.1) 2 :=
      charP_of_injective_algebraMap (algebraMap F (D b.1)).injective 2
    have e : Matrix.SpecialLinearGroup (Fin (d b.1)) (D b.1) ≃* ↥(S b) :=
      (MonoidHom.ofInjective (blockEmbed_injective (E := D) (m := d) b.1)).trans
        (Subgroup.equivMapOfInjective (blockSL D d b.1) θ hθinj)
    exact GGA6CharTwoLie.of_mulEquiv e (CoreShape.gga6CharTwoLie_SL (d b.1) b.2)

theorem ggA6_shape_SL {F : Type} [Field F] [Finite F] [CharP F 2] (N : ℕ)
    (P : Subgroup (GL (Fin N) F)) (hP : Odd (Nat.card P))
    (J : Subgroup (GL (Fin N) F))
    (hJ : IsComponentOf J (Matrix.SpecialLinearGroup.toGL.range ⊓
      Subgroup.centralizer (P : Set (GL (Fin N) F)))) : GGA6CharTwoLie J := by
  obtain ⟨β, S, hS, hshape⟩ := ggA6_SL_coreFamily_aux N P hP
  exact GGA6CharTwoLie_of_isCoreFamily hS hshape hJ

end CFSG.StandardType.A6Red
