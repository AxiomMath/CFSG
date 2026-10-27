module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanADefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPhanA5Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGPhanMarkedA
public import CFSG.LocalAnalysis.StandardType.GGPhanCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneDefs
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSystem
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.GH74.L5U5.IdentUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan

private lemma ggPhanAMarked_le_three_A (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (CoxeterMatrix.A m).M i j ≤ 3 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> omega

theorem ggSecFivePhanA_weakSystem {G : Type} [Group G] {H : Subgroup G} {ι : Type}
    {M : CoxeterMatrix ι} {m : ℕ} (e' : Fin m ≃ ι) (hM : M = (CoxeterMatrix.A m).reindex e')
    {f : ℕ} (hq : 4 ≤ 2 ^ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (S : ι → Subgroup G)
    (hiso : ∀ i, Nonempty (Su K 2 f 2 ≃* S i))
    (hcomm : ∀ i j, i ≠ j → M.M i j = 2 → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a)
    (hpair : ∀ i j, M.M i j = 3 → ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W (S i) (S j))
    (hgen : ⨆ i, S i = H) :
    WeakPhanSL K 2 f (CoxeterMatrix.A m) (fun k : Fin m => (S (e' k)).subgroupOf H)
      (fun k l => (S (e' k)).subgroupOf H ⊔ (S (e' l)).subgroupOf H) := by
  have hSH : ∀ i, S i ≤ H := fun i => hgen ▸ le_iSup S i
  have hq2 : (2 : ℕ) ^ f ≠ 2 := by omega
  have hlab : ∀ k l, M.M (e' k) (e' l) = (CoxeterMatrix.A m).M k l := by
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
      have := (CoxeterMatrix.A m).diagonal k
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
    have hU : ∀ k : Fin m, ((S (e' k)).subgroupOf H).map H.subtype = S (e' k) := fun k =>
      Subgroup.subgroupOf_map_subtype _ _ |>.trans (inf_eq_left.mpr (hSH _))
    simp only [hU]
    rw [← hgen]
    exact (Equiv.iSup_comp (g := S) e')

theorem ggSecFivePhanA_marked
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput)
    (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hJ : GGSecFiveJoinPhanA5Input)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} (σ : Fin m ≃ ι) (hm : 5 ≤ m)
    (hM : M = (CoxeterMatrix.A m).reindex σ)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) :
    ∃ f : ℕ, 4 ≤ 2 ^ f ∧
      ∃ θ : Su (GaloisField 2 (2 * f)) 2 f (m + 1) →* G,
        θ.ker ≤ Subgroup.center (Su (GaloisField 2 (2 * f)) 2 f (m + 1)) ∧
        θ.range = L ⊔ ⨆ K ∈ 𝒦, K ∧ ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K ∧
        (ggSuPairBlock (GaloisField 2 (2 * f)) 2 f (m + 1) ⟨0, by omega⟩ ⟨1, by omega⟩).map θ =
          ggRankOnePerf Bs
            ((e (M.simple (σ ⟨0, by omega⟩)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∧
        ∃ ψs : (ggU .PSU (m + 1) f).K →* G,
          GGPresentsG0 (ggG0 p B x L D J) (ggU .PSU (m + 1) f).D .PSU (m + 1) f ψs := by
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    rw [hM, CoxeterMatrix.reindex_apply]
    exact ggPhanAMarked_le_three_A m (σ.symm i) (σ.symm j) (fun h => hij (σ.symm.injective h))
  obtain ⟨f, hf4, -, hsys⟩ :=
    ggSecFivePhanSystem_of_prim hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hns hpres hle3 hbig
  have hf : 2 * f ≠ 0 := by
    rintro h
    have : f = 0 := by omega
    subst this
    norm_num at hf4
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) hf, ← pow_mul, mul_comm]
  obtain ⟨hiso, hcomm, hpair, hgen⟩ := hsys (GaloisField 2 (2 * f)) hK
  have hG0 := hJ G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, ⟨m, σ, hm, hM⟩, hbig⟩
  have hW := ggSecFivePhanA_weakSystem (H := L ⊔ ⨆ K ∈ 𝒦, K) σ hM hf4
    (GaloisField 2 (2 * f)) hK _ hiso hcomm hpair hgen
  obtain ⟨θ, hθs, hθk, hmk⟩ :=
    weakPhan_recognition_marked_pair_of_four_le (GaloisField 2 (2 * f)) 2 f hK hf4
      (by omega : 3 ≤ m) hW.weakPhanA
  have hSH : ∀ i, ggRankOnePerf Bs
      ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ≤ L ⊔ ⨆ K ∈ 𝒦, K :=
    fun i => hgen ▸ le_iSup (fun i => ggRankOnePerf Bs
      ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) i
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      norm_num at hf4
    · exact h
  have hadm : StatedLieAdmissible .PSU (m + 1) 2 f :=
    ⟨Nat.prime_two, hf1, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  have hrank : 3 ≤ bnRank .PSU (m + 1) := by simp only [bnRank]; omega
  obtain ⟨θu, hθus, hθuk⟩ :=
    weakPhanA_lieUniversalPSU (p := 2) Nat.prime_two (GaloisField 2 (2 * f)) hK hf4
      (by omega : 3 ≤ m) hW.weakPhanA
  have hψuker : ((L ⊔ ⨆ K ∈ 𝒦, K).subtype.comp θu).ker ≤ Subgroup.center (ggU .PSU (m + 1) f).K :=
    (MonoidHom.ker_comp_of_injective θu (L ⊔ ⨆ K ∈ 𝒦, K).subtype
      (L ⊔ ⨆ K ∈ 𝒦, K).subtype_injective).le.trans hθuk
  have hψurange : ((L ⊔ ⨆ K ∈ 𝒦, K).subtype.comp θu).range = ggG0 p B x L D J := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hθus, Subgroup.map_top,
      Subgroup.range_subtype, hG0]
  obtain ⟨ψs, hψs⟩ := ggPresentsG0_of_secFivePres
    (ggSecFivePres_of_psi_PSU hadm hrank ((L ⊔ ⨆ K ∈ 𝒦, K).subtype.comp θu) hψuker hψurange)
  refine ⟨f, hf4, (L ⊔ ⨆ K ∈ 𝒦, K).subtype.comp θ, ?_, ?_, hG0, ?_, ψs, hψs⟩
  · refine (MonoidHom.ker_comp_of_injective θ (L ⊔ ⨆ K ∈ 𝒦, K).subtype
      (L ⊔ ⨆ K ∈ 𝒦, K).subtype_injective).le.trans hθk
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hθs, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map]
    have h0 := hmk ⟨0, by omega⟩
    simp only at h0
    rw [h0]
    exact (Subgroup.subgroupOf_map_subtype _ _).trans (inf_eq_left.mpr (hSH _))

end CFSG.StandardType

end
