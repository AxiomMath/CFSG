module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBE7Adj
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E7Bridge

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.HighestRoot CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.SeitzReduction CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule

theorem rckIIPair_E7
    (n : ℕ) (hadm : StatedLieAdmissible .E7 n 2 1) : RCKIIPair .E7 n := by
  obtain ⟨β, x', V', hβ, hlong, hroot', hx2', hx1', hxV', hVab', hVcard', hVN', hconj'⟩ :=
    rckIIPairAdj_E7
  have hβroot : IsRoot .E7 β := mem_adjDatum_roots.1 hβ
  have hβmem2 : β ∈ (e7Datum (GaloisField 2 1)).roots := by
    rw [MinData.Valid.minDatum_roots]
    exact hβroot
  have hβmem : β ∈ (ggU .E7 n 1).D.roots := hβmem2
  have hlongmem : GGLongRoot (ggU .E7 n 1).D β := by
    change GGLongRoot (e7Datum (GaloisField 2 1)) β
    have hsym : ∀ i j, (e7Datum (GaloisField 2 1)).cartan i j =
        (e7Datum (GaloisField 2 1)).cartan j i := cartanE_symm 7
    exact ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7
      hsym rfl hβmem2
  let e : (ggU .E7 n 1).K ≃* rckp7_G :=
    CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 1)
  let x : (ggU .E7 n 1).K := e.symm x'
  let V : Subgroup (ggU .E7 n 1).K := V'.map e.symm.toMonoidHom
  have hmap : ((ggU .E7 n 1).D.rootGroup β).map e.toMonoidHom = rckp7_D.rootGroup β :=
    CFSG.StandardType.LieKnownR2.E7.map_e7MinEquivAdjoint_rootGroup
      (K := GaloisField 2 1) hβroot
  have hsymm : (rckp7_D.rootGroup β).map e.symm.toMonoidHom = (ggU .E7 n 1).D.rootGroup β := by
    rw [← hmap, CFSG.StandardType.GGRootNorm.map_symm_map e ((ggU .E7 n 1).D.rootGroup β)]
  have hroot : (ggU .E7 n 1).D.rootGroup β = Subgroup.zpowers x := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hmap, hroot']
    simp [x]
  have hx2 : x * x = 1 := by
    show e.symm x' * e.symm x' = 1
    rw [← map_mul, hx2', map_one]
  have hx1 : x ≠ 1 := by
    intro h
    apply hx1'
    simpa [x] using congrArg e h
  have hxV : x ∈ V := by
    show e.symm x' ∈ V'.map e.symm.toMonoidHom
    exact Subgroup.mem_map.mpr ⟨x', hxV', rfl⟩
  have hVab : IsElemAbelian 2 V :=
    ggIsElemAbelian_map hVab' e.symm.toMonoidHom
  have hVcard : Nat.card V = 4 := by
    change Nat.card (V'.map e.symm.toMonoidHom) = 4
    rw [Subgroup.card_map_of_injective e.symm.injective, hVcard']
  have hpc : (pCoreOf 2 (Subgroup.normalizer (rckp7_D.rootGroup β))).map e.symm.toMonoidHom =
      pCoreOf 2 (Subgroup.normalizer
        (((ggU .E7 n 1).D.rootGroup β : Subgroup (ggU .E7 n 1).K) : Set (ggU .E7 n 1).K)) := by
    rw [← CFSG.StandardType.GGRootNorm.pCoreOf_map_mulEquiv e.symm
        (Subgroup.normalizer (rckp7_D.rootGroup β)),
      ← CFSG.StandardType.GGRootNorm.normalizer_map_mulEquiv e.symm (rckp7_D.rootGroup β),
      hsymm]
  have hVN : V ≤ pCoreOf 2 (Subgroup.normalizer
      (((ggU .E7 n 1).D.rootGroup β : Subgroup (ggU .E7 n 1).K) : Set (ggU .E7 n 1).K)) := by
    rw [← hpc]
    show V'.map e.symm.toMonoidHom ≤ _
    exact Subgroup.map_mono hVN'
  have hconj : ∀ v ∈ V, v ≠ 1 → ∃ j : (ggU .E7 n 1).K, v = j * x * j⁻¹ := by
    intro v hv hv1
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
    have hv'1 : v' ≠ 1 := by
      intro h
      apply hv1
      rw [h, map_one]
    obtain ⟨j', hj'⟩ := hconj' v' hv' hv'1
    refine ⟨e.symm j', ?_⟩
    rw [hj']
    simp [x]
  unfold RCKIIPair
  exact ⟨β, x, V, hβmem, hlongmem, hroot, hx2, hx1, hxV, hVab, hVcard, hVN, hconj⟩

end CFSG.StandardType.RCKK1II
