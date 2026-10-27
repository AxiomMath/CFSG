module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSystem
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagE
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagAdjoint
import CFSG.GH74.L5U5.IdentUnitary
import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan

theorem ggWeakPhanSL_subgroupOf {G : Type} [Group G] {ι : Type} {M : CoxeterMatrix ι} {n : ℕ}
    {N : CoxeterMatrix (Fin n)} (e' : Fin n ≃ ι) (hM : M = N.reindex e') {f : ℕ}
    (hq : 4 ≤ 2 ^ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {H : Subgroup G} (S : ι → Subgroup G)
    (hiso : ∀ i, Nonempty (Su K 2 f 2 ≃* S i))
    (hcomm : ∀ i j, i ≠ j → M.M i j = 2 → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a)
    (hpair : ∀ i j, M.M i j = 3 → ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W (S i) (S j))
    (hgen : ⨆ i, S i = H) :
    WeakPhanSL K 2 f N (fun k => (S (e' k)).subgroupOf H)
      (fun k l => (S (e' k)).subgroupOf H ⊔ (S (e' l)).subgroupOf H) := by
  have hSH : ∀ i, S i ≤ H := fun i => hgen ▸ le_iSup S i
  have hq2 : (2 : ℕ) ^ f ≠ 2 := by omega
  have hlab : ∀ k l, M.M (e' k) (e' l) = N.M k l := by
    intro k l
    rw [hM, coxeterMatrix_reindex_apply_equiv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨φ⟩ := hiso (e' k)
    exact ⟨φ.trans (Subgroup.subgroupOfEquivOfLe (hSH (e' k))).symm⟩
  · intro k l _
    rfl
  · intro k l hkl a ha b hb
    have hne : k ≠ l := by
      rintro rfl
      have := N.diagonal k
      omega
    apply Subtype.ext
    exact hcomm (e' k) (e' l) (fun h => hne (e'.injective h)) (by rw [hlab]; exact hkl) a ha b hb
  · intro k l hkl
    obtain ⟨W₀, hW₀⟩ := hpair (e' k) (e' l) (by rw [hlab]; exact hkl)
    have h1 := CFSG.GH74.L5U5.unitaryBlockStandardPair_subgroupOf hK hq2 hW₀ H (hSH _) (hSH _)
    have h2 := CFSG.GH74.L5U5.unitaryBlockStandardPair_eq_sup hK hq2 h1
    rw [h2] at h1
    exact h1
  · apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    have hU : ∀ k, ((S (e' k)).subgroupOf H).map H.subtype = S (e' k) := fun k =>
      Subgroup.subgroupOf_map_subtype _ _ |>.trans (inf_eq_left.mpr (hSH _))
    simp only [hU]
    rw [← hgen]
    exact (Equiv.iSup_comp (g := S) e')

theorem ggSecFiveData_of_phanE_system
    (hPE : PhanEInput2) {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hJ : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) {ι : Type} {M : CoxeterMatrix ι}
    (hE : GGIsWeylMatrixE M) {f : ℕ} (hq : 4 ≤ 2 ^ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (S : ι → Subgroup G) (hiso : ∀ i, Nonempty (Su K 2 f 2 ≃* S i))
    (hcomm : ∀ i j, i ≠ j → M.M i j = 2 → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a)
    (hpair : ∀ i j, M.M i j = 3 → ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W (S i) (S j))
    (hgen : ⨆ i, S i = L ⊔ ⨆ K ∈ 𝒦, K) :
    GGSecFiveData p B x L D J := by
  set H : Subgroup G := L ⊔ ⨆ K ∈ 𝒦, K with hH
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h; norm_num at hq
    · exact h
  have hrangeH : ∀ {Y : Type} [Group Y] (θ : Y →* ↥H), Function.Surjective θ →
      (H.subtype.comp θ).range = ggG0 p B x L D J := by
    intro Y _ θ hθ
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hθ, Subgroup.map_top,
      Subgroup.range_subtype, hJ]
  have hkerH : ∀ {Y : Type} [Group Y] (θ : Y →* ↥H), (H.subtype.comp θ).ker = θ.ker := by
    intro Y _ θ
    exact MonoidHom.ker_comp_of_injective θ H.subtype H.subtype_injective
  obtain ⟨h6, h7, h8⟩ := hPE K f hK hq
  rcases hE with ⟨e', hM⟩ | ⟨e', hM⟩ | ⟨e', hM⟩
  · obtain ⟨θ, hθ, hker⟩ := h6 _ _ (ggWeakPhanSL_subgroupOf e' hM hq K hK S hiso hcomm hpair hgen)
    have hadm : StatedLieAdmissible .twistedE6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    refine Or.inr (Or.inr ⟨.twistedE6, 0, f, ?_⟩)
    exact ggSecFivePres_of_psi_twistedE6 hadm (by decide) (H.subtype.comp θ)
      ((hkerH θ).le.trans hker) (hrangeH θ hθ)
  · obtain ⟨θ, hθ, hker⟩ := h7 _ _ (ggWeakPhanSL_subgroupOf e' hM hq K hK S hiso hcomm hpair hgen)
    have hadm : StatedLieAdmissible .E7 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    refine Or.inr (Or.inr ⟨.E7, 0, f, ?_⟩)
    exact ggSecFivePres_of_psi_E7 hadm (by decide) (H.subtype.comp θ)
      ((hkerH θ).le.trans hker) (hrangeH θ hθ)
  · obtain ⟨θ, hθ, hker⟩ := h8 _ _ (ggWeakPhanSL_subgroupOf e' hM hq K hK S hiso hcomm hpair hgen)
    have hadm : StatedLieAdmissible .E8 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    refine Or.inr (Or.inr ⟨.E8, 0, f, ?_⟩)
    exact ggSecFivePres_of_psi_E8 hadm (by decide) (H.subtype.comp θ)
      ((hkerH θ).le.trans hker) (hrangeH θ hθ)

theorem ggSecFiveData_phanE_of_big
    (hPE : PhanEInput2) (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput)
    (hPair : GGSecFivePhanPairInput) (hNbr : GGSecFiveNonSplitNbrInput)
    (hJ : GGSecFiveJoinPhanEInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hs : ¬ GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) :
    GGSecFiveData p B x L D J := by
  obtain ⟨f, hf4, -, hsys⟩ := ggSecFivePhanSystem_of_prim hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hs
    hpres (fun i j hij => GGIsWeylMatrixE.le_three hE i j hij) hbig
  have hf : 2 * f ≠ 0 := by
    rintro h
    have : f = 0 := by omega
    subst this
    norm_num at hf4
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) hf, ← pow_mul, mul_comm]
  obtain ⟨hiso, hcomm, hpair, hgen⟩ := hsys (GaloisField 2 (2 * f)) hK
  have hG0 := hJ G p B Bs x L D J 𝒦 hcfg hs ⟨ι, M, e, hpres, hE, hbig⟩
  exact ggSecFiveData_of_phanE_system hPE hG0 hE hf4 (GaloisField 2 (2 * f)) hK _ hiso hcomm
    hpair hgen

end CFSG.StandardType

end
