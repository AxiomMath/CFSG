module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derFixOrth
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derLayerCent
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derLayerSimple
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derLayerComp
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSpOne
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLift

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48gL_gpow_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {L' : Type} [Group L'] [Finite L']
    (hK : Nat.card K = 2)
    (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K 4)) (hψ : Function.Surjective ψ)
    {e : MulAut L'} (he3 : e ^ 3 = 1)
    {g : LargeEvenProj (LargeEvenSpGroup K 4)} (hg : ∀ l : L', ψ (e l) = g * ψ l * g⁻¹) :
    g ^ 3 = 1 := by
  have hcube : ∀ l : L', ψ l = g ^ 3 * ψ l * (g ^ 3)⁻¹ := by
    intro l
    have h1 : ψ (e (e (e l))) = g * (g * (g * ψ l * g⁻¹) * g⁻¹) * g⁻¹ := by
      rw [hg (e (e l)), hg (e l), hg l]
    have h2 : g * (g * (g * ψ l * g⁻¹) * g⁻¹) * g⁻¹ = g ^ 3 * ψ l * (g ^ 3)⁻¹ := by
      rw [pow_three]; group
    have hfix : e (e (e l)) = l := by
      have h := congrArg (fun f : MulAut L' => f l) he3
      change (e ^ 3) l = l at h
      exact h
    rw [hfix] at h1
    rw [← h2]
    exact h1
  have hcomm : ∀ l : L', g ^ 3 * ψ l = ψ l * g ^ 3 := by
    intro l
    have h := hcube l
    calc g ^ 3 * ψ l = (g ^ 3 * ψ l * (g ^ 3)⁻¹) * g ^ 3 := by rw [pow_three]; group
      _ = ψ l * g ^ 3 := by rw [← h]
  have hcenter : g ^ 3 ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K 4)) := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    exact (hcomm l).symm
  rw [TableBSymp.center_spProj_eq_bot (K := K) (m := 4), Subgroup.mem_bot] at hcenter
  exact hcenter

private lemma l48gL_map_fix {K : Type} [Field K] [Finite K] [CharP K 2]
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K 4))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ2 : IsPGroup 2 (Subgroup.center L')) {e : MulAut L'} (he3 : e ^ 3 = 1)
    {g : LargeEvenProj (LargeEvenSpGroup K 4)} (hg : ∀ l : L', ψ (e l) = g * ψ l * g⁻¹) :
    (ggFixSub e).map ψ =
      Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4))) := by
  have hlift : ggFix (MulAut.conj g) = (ggFix e).map ψ := by
    refine CFSG.StandardType.Line63.H5.map_ggFix_eq_of_lift ψ hψ hker (hZ2.to_le hker) he3 ?_
    intro l
    rw [MulAut.conj_apply, ← hg l]
  have hCg : ggFix (MulAut.conj g) =
      Subgroup.centralizer ({g} : Set (LargeEvenProj (LargeEvenSpGroup K 4))) := by
    ext r
    rw [mem_ggFix, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc r * g = (MulAut.conj g r) * g := by rw [h]
        _ = g * r := by rw [MulAut.conj_apply]; group
    · intro h
      rw [MulAut.conj_apply, ← h]
      group
  exact (hCg.symm.trans hlift).symm

theorem ggB2der_layer_sixfix {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K 4))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L'))
    {e : MulAut L'} (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    {g : LargeEvenProj (LargeEvenSpGroup K 4)} (hg : ∀ l : L', ψ (e l) = g * ψ l * g⁻¹)
    (hW : Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)) = 6) :
    IsComponentOf (LargeEvenLayer (ggFixSub e)) (ggFixSub e) ∧
      (LargeEvenLayer (ggFixSub e)).map ψ =
        ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)),
          ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g))⁆ ∧
      ¬ LargeEvenSmall (LargeEvenLayer (ggFixSub e)) := by
  have hg3 : g ^ 3 = 1 := l48gL_gpow_three hK ψ hψ he3 hg
  obtain ⟨hcompl, -, -, -⟩ := ggB2der_fix_orth_decomp hK SmallRule.spRep (SmallRule.spBilin K 4)
    SmallRule.spBilin_nondegenerate SmallRule.spBilin_isRefl SmallRule.spRep_isometry hg3
  obtain ⟨hle, hnorm, hder⟩ := ggB2der_sixfix_centralizer hK hg3 rfl hW
  obtain ⟨hsimp, hperfS, h7⟩ := ggB2der_spFixPerp_simple hK hW hcompl
  exact ggB2der_layer_of_normal_image ψ hker (l48gL_map_fix ψ hψ hker hZ2 he3 hg) hle hnorm hder
    hsimp hperfS h7

end CFSG.StandardType
