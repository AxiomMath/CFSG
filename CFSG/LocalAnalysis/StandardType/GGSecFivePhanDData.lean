module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSystem
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagSpin
import CFSG.GH74.L5U5.IdentUnitary
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan

theorem ggSecFiveData_of_phanD_system
    (hPD : PhanDInput2) {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hJ : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) {ι : Type} {M : CoxeterMatrix ι} {m : ℕ}
    (hm : 4 ≤ m) (e' : Fin m ≃ ι) (hM : M = (ggCoxeterMatrixD m).reindex e') {f : ℕ}
    (hq : 4 ≤ 2 ^ f) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (S : ι → Subgroup G) (hiso : ∀ i, Nonempty (Su K 2 f 2 ≃* S i))
    (hcomm : ∀ i j, i ≠ j → M.M i j = 2 → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a)
    (hpair : ∀ i j, M.M i j = 3 → ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W (S i) (S j))
    (hgen : ⨆ i, S i = L ⊔ ⨆ K ∈ 𝒦, K) :
    GGSecFiveData p B x L D J := by
  set H : Subgroup G := L ⊔ ⨆ K ∈ 𝒦, K with hH
  have hSH : ∀ i, S i ≤ H := fun i => hgen ▸ le_iSup S i
  have hq2 : (2 : ℕ) ^ f ≠ 2 := by omega
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h; norm_num at hq
    · exact h
  let U : Fin m → Subgroup ↥H := fun k => (S (e' k)).subgroupOf H
  let W : Fin m → Fin m → Subgroup ↥H := fun k l => U k ⊔ U l
  have hlab : ∀ k l, M.M (e' k) (e' l) = (ggCoxeterMatrixD m).M k l := by
    intro k l
    rw [hM, coxeterMatrix_reindex_apply_equiv]
  have hsys : WeakPhanSL K 2 f (ggCoxeterMatrixD m) U W := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k
      obtain ⟨φ⟩ := hiso (e' k)
      exact ⟨φ.trans (Subgroup.subgroupOfEquivOfLe (hSH (e' k))).symm⟩
    · intro k l _
      rfl
    · intro k l hkl a ha b hb
      have hne : k ≠ l := by
        rintro rfl
        have := (ggCoxeterMatrixD m).diagonal k
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
      have hU : ∀ k, (U k).map H.subtype = S (e' k) := fun k =>
        Subgroup.subgroupOf_map_subtype _ _ |>.trans (inf_eq_left.mpr (hSH _))
      simp only [hU]
      rw [← hgen]
      exact (Equiv.iSup_comp (g := S) e')
  obtain ⟨hEven, hOdd⟩ := hPD K f hK hq m hm U W hsys
  have hrangeH : ∀ {Y : Type} [Group Y] (θ : Y →* ↥H), Function.Surjective θ →
      (H.subtype.comp θ).range = ggG0 p B x L D J := by
    intro Y _ θ hθ
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hθ, Subgroup.map_top,
      Subgroup.range_subtype, hJ]
  have hkerH : ∀ {Y : Type} [Group Y] (θ : Y →* ↥H), (H.subtype.comp θ).ker = θ.ker := by
    intro Y _ θ
    exact MonoidHom.ker_comp_of_injective θ H.subtype H.subtype_injective
  rcases Nat.even_or_odd m with hev | hodd
  · obtain ⟨θ, hθ, hker⟩ := hEven hev
    have hadm : StatedLieAdmissible .POmegaPlus m 2 f := ⟨Nat.prime_two, hf, hm⟩
    have hrank : 3 ≤ bnRank .POmegaPlus m := by simp only [bnRank]; omega
    refine Or.inr (Or.inr ⟨.POmegaPlus, m, f, ?_⟩)
    exact ggSecFivePres_of_psi_POmegaPlus hadm hrank (H.subtype.comp θ)
      ((hkerH θ).le.trans hker) (hrangeH θ hθ)
  · obtain ⟨θ, hθ, hker⟩ := hOdd hodd
    have hadm : StatedLieAdmissible .POmegaMinus m 2 f := ⟨Nat.prime_two, hf, hm⟩
    have hrank : 3 ≤ bnRank .POmegaMinus m := by simp only [bnRank]; omega
    refine Or.inr (Or.inr ⟨.POmegaMinus, m, f, ?_⟩)
    exact ggSecFivePres_of_psi_POmegaMinus hadm hrank (H.subtype.comp θ)
      ((hkerH θ).le.trans hker) (hrangeH θ hθ)

theorem ggSecFiveDataResAt_phanD
    (hPD : PhanDInput2) (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput)
    (hPair : GGSecFivePhanPairInput) (hNbr : GGSecFiveNonSplitNbrInput)
    (hJ : GGSecFiveJoinPhanInput) (hQ2 : GGSecFiveDataResPhanDQTwoInput) :
    GGSecFiveDataResAt (fun M => GGIsWeylMatrixD M) := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres hDm
  obtain ⟨m, e', hm, hM⟩ := hDm
  by_cases hs : GGSplitLie p L
  · exact absurd ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inl (Or.inr ⟨m, e', hm, hM⟩)⟩ hNotReg
  have hWeyl : GGIsWeylMatrixAD M := Or.inr ⟨m, e', hm, hM⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := fun i j hij =>
    GGIsWeylMatrixAD.le_three hWeyl i j hij
  by_cases h6 : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6
  · exact hQ2 G p B Bs x L D J 𝒦 hcfg hNotReg hs ι M e hpres ⟨m, e', hm, hM⟩ h6
  have hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
    fun r hrA hrC h => h6 ⟨r, hrA, hrC, h⟩
  obtain ⟨f, hf4, -, hsys⟩ :=
    ggSecFivePhanSystem_of_prim hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hs hpres hle3 hbig
  have hf : 2 * f ≠ 0 := by
    rintro h
    have : f = 0 := by omega
    subst this
    norm_num at hf4
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) hf, ← pow_mul, mul_comm]
  obtain ⟨hiso, hcomm, hpair, hgen⟩ := hsys (GaloisField 2 (2 * f)) hK
  have hG0 := hJ G p B Bs x L D J 𝒦 hcfg hs ⟨ι, M, e, hpres, ⟨m, e', hm, hM⟩, hbig⟩
  exact ggSecFiveData_of_phanD_system hPD hG0 hm e' hM hf4 (GaloisField 2 (2 * f)) hK _ hiso
    hcomm hpair hgen

end CFSG.StandardType

end
