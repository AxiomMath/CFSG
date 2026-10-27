module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_le_normalizer_beta {D : Data G} {L : Subgroup G} :
    D.T ≤ Subgroup.normalizer (conjClosure D.M L ⊓
      normalizer (D.T ⊓ conjClosure D.M L : Set G) : Set G) := by
  have hTX : D.T ≤ Subgroup.normalizer (conjClosure D.M L : Set G) :=
    D.sylowM.le.trans (uc22p22v_le_normalizer_conjClosure D.M L)
  have hTP : D.T ≤ Subgroup.normalizer (D.T ⊓ conjClosure D.M L : Set G) := by
    intro t ht
    change t ∈ Subgroup.normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxT, hxX⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨D.T.mul_mem (D.T.mul_mem ht hxT) (D.T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp (hTX ht) x).mp hxX⟩
    · intro hx
      obtain ⟨hxT, hxX⟩ := Subgroup.mem_inf.mp hx
      have h1 : t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x := by group
      rw [← h1]
      exact Subgroup.mem_inf.mpr
        ⟨D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hxT) (D.T.inv_mem (D.T.inv_mem ht)),
          (Subgroup.mem_normalizer_iff.mp (hTX (D.T.inv_mem ht)) _).mp hxX⟩
  exact (le_inf hTX (hTP.trans (Subgroup.le_normalizer
      (H := Subgroup.normalizer (D.T ⊓ conjClosure D.M L : Set G))))).trans
      Subgroup.inf_normalizer_le_normalizer_inf

theorem uc22r3e5c_permutes_cartan {D : Data G} {L : Subgroup G}
    {C : Subgroup G}
    (hCX : C ≤ conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G))
    (hβPC : (conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G) : Set G) =
      (D.T ⊓ conjClosure D.M L : Set G) * (C : Set G)) :
    Permutes C D.T := by
  have hTβ := uc22r3e5c_le_normalizer_beta (D := D) (L := L)
  have hforward : (C : Set G) * (D.T : Set G) ⊆ (D.T : Set G) * (C : Set G) := by
    rintro _ ⟨c, hc, t, ht, rfl⟩
    have hcβ : c ∈ (conjClosure D.M L ⊓
        normalizer (D.T ⊓ conjClosure D.M L : Set G) : Set G) := hCX hc
    have hmem : t⁻¹ * c * t ∈ (conjClosure D.M L ⊓
        normalizer (D.T ⊓ conjClosure D.M L : Set G) : Set G) := by
      have h := (Subgroup.mem_normalizer_iff (H := (conjClosure D.M L ⊓
        normalizer (D.T ⊓ conjClosure D.M L : Set G) : Subgroup G))).mp
        (hTβ (D.T.inv_mem ht)) c
      simpa using h.mp hcβ
    rw [hβPC] at hmem
    obtain ⟨p, hp, c', hc', hpc⟩ := hmem
    obtain ⟨hpT, -⟩ := Subgroup.mem_inf.mp hp
    refine ⟨t * p, D.T.mul_mem ht hpT, c', hc', ?_⟩
    calc (t * p) * c' = t * (p * c') := by group
      _ = t * (t⁻¹ * c * t) := congrArg (fun z => t * z) hpc
      _ = c * t := by group
  refine Set.Subset.antisymm hforward ?_
  rintro _ ⟨t, ht, c, hc, rfl⟩
  have h1 : c⁻¹ * t⁻¹ ∈ (D.T : Set G) * (C : Set G) :=
    hforward ⟨c⁻¹, C.inv_mem hc, t⁻¹, D.T.inv_mem ht, rfl⟩
  obtain ⟨t', ht', c', hc', htc⟩ := h1
  refine ⟨c'⁻¹, C.inv_mem hc', t'⁻¹, D.T.inv_mem ht', ?_⟩
  have h2 : t * c = (c⁻¹ * t⁻¹)⁻¹ := by group
  calc c'⁻¹ * t'⁻¹ = (t' * c')⁻¹ := by group
    _ = (c⁻¹ * t⁻¹)⁻¹ := by rw [← htc]
    _ = t * c := h2.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
