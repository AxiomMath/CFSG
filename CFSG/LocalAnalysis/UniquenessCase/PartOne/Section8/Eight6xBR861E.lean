module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreConj
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Gamma614Application

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

@[expose] def HasGammaE9 {G : Type} [Group G] [Finite G] (D : Data G) (X : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
    rankThreeGamma 1 3 E ≤ D.M ∧ E ≤ normalizer (X : Set G)

theorem hasGammaE9_of_pRank {G : Type} [Group G] [Finite G] {D : Data G} {L Q P X : Subgroup G}
    (hc : Cex856 D L Q P)
    (hrk : 1 < CFSG.Open.pRank 3 (centralizer (X : Set G) ⊓ L)) : HasGammaE9 D X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEH, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2)
      (H := centralizer (X : Set G) ⊓ L) hrk
  have hEL : E ≤ L := hEH.trans inf_le_right
  have hEX : E ≤ normalizer (X : Set G) :=
    (hEH.trans inf_le_left).trans (Subgroup.centralizer_le_normalizer _)
  have hLM : L ≤ D.M := hc.mem.1.le
  have hE3 : IsPGroup 3 E := IsPGroup.of_card hEcard
  have hE3' : IsPGroup 3 (E.subgroupOf L) := hE3.comap_subtype
  obtain ⟨T, hET⟩ := hE3'.exists_le_sylow
  have hT : IsSylowOf 3 ((T : Subgroup ↥L).map L.subtype) L := ⟨T, rfl⟩
  have hEle : E ≤ (T : Subgroup ↥L).map L.subtype := by
    intro x hx
    exact ⟨⟨x, hEL hx⟩, hET (show (⟨x, hEL hx⟩ : ↥L) ∈ E.subgroupOf L from hx), rfl⟩
  obtain ⟨k, hkL, hk⟩ := hc.sylowQ.exists_mem_conj hT
  have hTeq : (T : Subgroup ↥L).map L.subtype = GLBConj k⁻¹ Q := by
    ext x
    constructor
    · intro hx
      exact ⟨k⁻¹ * x * k, (hk x).1 hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨q, hq, rfl⟩
      refine (hk _).2 ?_
      simpa [MulAut.conj_apply, mul_assoc] using hq
  have hΓT : rankThreeGamma 1 3 ((T : Subgroup ↥L).map L.subtype) ≤ D.M := by
    rw [hTeq]
    change CFSG.Open.GLBCore 3 1 (GLBConj k⁻¹ Q) ≤ D.M
    rw [CFSG.HardMathSupport.Solomon.Proving.GLBCore_gLBConj]
    rintro x ⟨y, hy, rfl⟩
    have hyM : y ∈ D.M := hc.gamma hy
    have hkM : k ∈ D.M := hLM hkL
    simp only [inv_inv]
    exact D.M.mul_mem (D.M.mul_mem hkM hyM) (D.M.inv_mem hkM)
  exact ⟨E, hEL.trans hLM, hEel, hEcard, gamma_le_of_gammaQ_of_le hEle hΓT, hEX⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
