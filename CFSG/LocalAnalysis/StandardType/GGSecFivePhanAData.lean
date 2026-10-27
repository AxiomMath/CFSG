module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanADefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPhanA5Defs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSystem
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
import CFSG.GH74.L5U5.IdentUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan

theorem ggSecFive_three_le_card_of_tbfix (hT : GGTBFixInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} [Fintype ι] {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) : 3 ≤ Fintype.card ι := by
  have hR := hcfg.1
  have hWC := hcfg.2.1
  obtain ⟨hp, hBs, hxBs, h4⟩ := ggConfig_bstar_facts hR.1
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hR.1.1.2.2.2.2.2.2.2 hR.1.2.2
  have hfix := hT G p B Bs x L D J hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hnbr
    (hWC y K hnbr) (Or.inr hWC)
  let F₀ : Subgroup ↥Bs := (Subgroup.zpowers x).subgroupOf Bs
  have hWT : GGWeylOfType p M (ggAutomizerJoin L Bs 𝒦) := ⟨e, hpres.2⟩
  have hAL : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  have h1 : Nat.card Bs ≤ p ^ Fintype.card ι * Nat.card F₀ :=
    card_le_pow_mul_card_of_weylOfType hWT F₀
      (fun b hb => hfix b (fun φ hφ => hb φ (hAL hφ)))
  have h2 : Nat.card F₀ ≤ p := by
    refine card_le_of_le_zpowers hp hBs hxBs F₀ (fun b hb => ?_)
    exact Subgroup.mem_subgroupOf.mp hb
  by_contra hlt
  have h3 : Nat.card Bs ≤ p ^ 3 := by
    calc Nat.card Bs ≤ p ^ Fintype.card ι * Nat.card F₀ := h1
      _ ≤ p ^ 2 * p := Nat.mul_le_mul (Nat.pow_le_pow_right hp.pos (by omega)) h2
      _ = p ^ 3 := by ring
  exact absurd (h4.trans h3)
    (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 3 < 4)))

theorem ggSecFiveData_of_phanA_system
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hJ : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) {ι : Type} {M : CoxeterMatrix ι} {m : ℕ}
    (hm : 5 ≤ m) (e' : Fin m ≃ ι) (hM : M = (CoxeterMatrix.A m).reindex e') {f : ℕ}
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
  have hlab : ∀ k l, M.M (e' k) (e' l) = (CoxeterMatrix.A m).M k l := by
    intro k l
    rw [hM, coxeterMatrix_reindex_apply_equiv]
  have hsys : WeakPhanSL K 2 f (CoxeterMatrix.A m) U W := by
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
      have hU : ∀ k, (U k).map H.subtype = S (e' k) := fun k =>
        Subgroup.subgroupOf_map_subtype _ _ |>.trans (inf_eq_left.mpr (hSH _))
      simp only [hU]
      rw [← hgen]
      exact (Equiv.iSup_comp (g := S) e')
  obtain ⟨θ, hθ, hker⟩ :=
    phanA_isCentralQuotientOf K 2 f Nat.prime_two hK hq (by omega : 3 ≤ m) U W hsys
  have hadm : StatedLieAdmissible .PSU (m + 1) 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  have hrank : 3 ≤ bnRank .PSU (m + 1) := by simp only [bnRank]; omega
  refine Or.inr (Or.inr ⟨.PSU, m + 1, f, ?_⟩)
  refine ggSecFivePres_of_psi_PSU hadm hrank (H.subtype.comp θ)
    ((MonoidHom.ker_comp_of_injective θ H.subtype H.subtype_injective).le.trans hker) ?_
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hθ, Subgroup.map_top,
    Subgroup.range_subtype, hJ]

theorem ggSecFiveDataResAt_phanA
    (hT : GGTBFixInput) (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput) (hL2 : GGSecFiveL2PhanInput)
    (hPair : GGSecFivePhanPairInput) (hNbr : GGSecFiveNonSplitNbrInput)
    (hJ : GGSecFiveJoinPhanA5Input) (hS : GGSecFiveDataResPhanASmallInput)
    (hQ2 : GGSecFiveDataResPhanAQTwoInput) :
    GGSecFiveDataResAt (fun M => GGIsWeylMatrixA M) := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hNotReg ι M e hpres hAm
  obtain ⟨m, e', hm1, hM⟩ := hAm
  haveI : Fintype ι := Fintype.ofEquiv (Fin m) e'
  have hcard : Fintype.card ι = m := by rw [Fintype.card_congr e'.symm, Fintype.card_fin]
  have hm3 : 3 ≤ m := hcard ▸ ggSecFive_three_le_card_of_tbfix hT hcfg hpres
  by_cases hs : GGSplitLie p L
  · exact absurd ⟨𝒦, hcfg, hs, ι, M, e, hpres, Or.inl (Or.inl ⟨m, e', hm3, hM⟩)⟩ hNotReg
  rcases Nat.lt_or_ge m 5 with hm5 | hm5
  · exact hS G p B Bs x L D J 𝒦 hcfg hNotReg hs ι M e hpres ⟨m, e', by omega, hM⟩
  have hWeyl : GGIsWeylMatrixAD M := Or.inl ⟨m, e', hm3, hM⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := fun i j hij =>
    GGIsWeylMatrixAD.le_three hWeyl i j hij
  by_cases h6 : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6
  · exact hQ2 G p B Bs x L D J 𝒦 hcfg hNotReg hs ι M e hpres ⟨m, e', hm5, hM⟩ h6
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
  have hG0 := hJ G p B Bs x L D J 𝒦 hcfg hs ⟨ι, M, e, hpres, ⟨m, e', hm5, hM⟩, hbig⟩
  exact ggSecFiveData_of_phanA_system hG0 hm5 e' hM hf4 (GaloisField 2 (2 * f)) hK _ hiso
    hcomm hpair hgen

end CFSG.StandardType

end
