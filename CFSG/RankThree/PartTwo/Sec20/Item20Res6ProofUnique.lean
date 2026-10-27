module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofSteps
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec18.Rem187

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step202CMem : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201One G A M L N c →
    ∀ K₀ ∈ oTwoComponentsIn M, 3 ∣ Nat.card K₀ → c ∈ K₀

theorem step202Unique_of (h189 : Sec18.Item189) (hcm : Step202CMem) : Step202Unique := by
  intro G _ _ A M L N c h K₀ hK₀ h3
  set K := kTwenty M c with hKdef
  obtain ⟨H, hH18, hH187, -, -⟩ := exists_sec18H_of_hyp201One h
  obtain ⟨⟨hKC, -⟩, -, -⟩ := h189 G A M H c hH18 hH187
  have hK₀M : K₀ ≤ M := le_of_mem_oTwoComponentsIn hK₀
  have hKK₀ : K ≤ K₀ := by
    rw [hKdef, kTwenty, normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    have hK₀' : K₀.map (MulAut.conj m⁻¹).toMonoidHom ∈ oTwoComponentsIn M :=
      Sec18.map_conj_mem_oTwoComponentsIn hK₀ (M.inv_mem hm)
    have h3' : 3 ∣ Nat.card (K₀.map (MulAut.conj m⁻¹).toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective]
    obtain ⟨k, hk, hkc⟩ := hcm G A M L N c h _ hK₀' h3'
    have e : m * c * m⁻¹ = k := by
      rw [← hkc]
      simp [mul_assoc]
    rw [SetLike.mem_coe, e]
    exact hk
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := Sec18.commutator_eq_of_mem_oTwoComponentsIn hK₀
  have hres : inSubgroup perfectResidual K₀ = K₀ :=
    le_antisymm (Subgroup.map_subtype_le _) (Sec18.le_inSubgroup_perfectResidual hK₀p le_rfl)
  have hK₀K₀ : inSubgroup perfectResidual K₀ ∈ oTwoComponentsIn K₀ := by
    rw [hres]
    refine Sec18.mem_oTwoComponentsIn_of_le hK₀ le_rfl ?_
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.Normal.isSubnormal inferInstance
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hKn : (K.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKK₀).mpr (hK₀M.trans hMK)
  have heq := Sec18.eq_inSubgroup_perfectResidual_of_isSubnormal hK₀K₀ hKK₀ hKn.isSubnormal
    (Sec18.commutator_eq_of_mem_oTwoComponentsIn hKC) (Sec18.ne_bot_of_mem_oTwoComponentsIn hKC)
  rw [hres] at heq
  exact heq.symm

end CFSG.RankThree.PartTwo.Sec20
