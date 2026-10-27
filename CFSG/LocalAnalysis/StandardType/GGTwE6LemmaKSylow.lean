module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKData
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylFix

public noncomputable section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding.R3
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open scoped Matrix

theorem mul_mem_lemKMats {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : M ∈ e6SylMats)
    (hN : N ∈ e6SylMats) : M * N ∈ e6SylMats := by
  obtain ⟨A, hA, rfl⟩ := mem_e6SylMats.1 hM
  obtain ⟨B, hB, rfl⟩ := mem_e6SylMats.1 hN
  exact mem_e6SylMats.2 ⟨_, lemKFacts.mul_mem A hA B hB, toMatL_mmulL 3 6 A B⟩

theorem pow_mem_lemKMats {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : M ∈ e6SylMats) :
    ∀ k : ℕ, M ^ k ∈ e6SylMats
  | 0 => by rw [pow_zero]; exact one_mem_e6SylMats
  | k + 1 => by rw [pow_succ]; exact mul_mem_lemKMats (pow_mem_lemKMats hM k) hM

@[expose] def lemKP : Subgroup (WeylGroup Tag.E6) where
  carrier := {w | e6WeylMat w ∈ e6SylMats}
  mul_mem' {a b} ha hb := by
    have ha' : e6WeylMat a ∈ e6SylMats := ha
    have hb' : e6WeylMat b ∈ e6SylMats := hb
    have h := mul_mem_lemKMats ha' hb'
    rw [← map_mul] at h
    exact h
  one_mem' := by
    have h := one_mem_e6SylMats
    rw [← map_one e6WeylMat] at h
    exact h
  inv_mem' {w} hw := by
    have hw' : e6WeylMat w ∈ e6SylMats := hw
    have hpos := orderOf_pos w
    have h : w⁻¹ = w ^ (orderOf w - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    have h2 := pow_mem_lemKMats hw' (orderOf w - 1)
    rw [← map_pow, ← h] at h2
    exact h2

theorem mem_lemKP {w : WeylGroup Tag.E6} : w ∈ lemKP ↔ e6WeylMat w ∈ e6SylMats := Iff.rfl

private theorem card_lemKMats : e6SylMats.card = 81 := by
  rw [e6SylMats, List.toFinset_card_of_nodup, List.length_map, lemKFacts.length]
  exact List.Nodup.map_on
    (fun A hA B hB h => toMatL_inj6 (e6SylL_spec A hA) (e6SylL_spec B hB) h) lemKFacts.nodup

section Sylow


theorem card_lemKP : Nat.card lemKP = 81 := by
  rw [← card_lemKMats, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨e6WeylMat w, mem_lemKP.1 w.2⟩) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (e6WeylMat_injective (congrArg Subtype.val h))
  · rintro ⟨M, hM⟩
    obtain ⟨A, hA, rfl⟩ := mem_e6SylMats.1 hM
    obtain ⟨w, hw⟩ := mem_mrange_of_mem_e6SylL hA
    exact ⟨⟨w, mem_lemKP.2 (hw ▸ hM)⟩, Subtype.ext hw⟩

theorem exists_conj_le_lemKP {H : Subgroup (WeylGroup Tag.E6)} (hH : IsPGroup 3 H) :
    ∃ g : WeylGroup Tag.E6, ∀ x ∈ H, g⁻¹ * x * g ∈ lemKP := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card lemKP = 3 ^ (Nat.card (WeylGroup Tag.E6)).factorization 3 := by
    rw [card_lemKP, card_weylGroup_E6', factorization_51840]
    norm_num
  let Q : Sylow 3 (WeylGroup Tag.E6) := Sylow.ofCard lemKP hcard
  have hQ : (Q : Subgroup (WeylGroup Tag.E6)) = lemKP := Sylow.coe_ofCard lemKP hcard
  obtain ⟨P, hHP⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := WeylGroup Tag.E6)
      (P : Sylow 3 (WeylGroup Tag.E6)) Q
  refine ⟨g⁻¹, fun x hx => ?_⟩
  have hxP : x ∈ P := hHP hx
  have hmem : g * x * g⁻¹ ∈ (g • P : Sylow 3 (WeylGroup Tag.E6)) := by
    change g * x * g⁻¹ ∈ ((g • P : Sylow 3 (WeylGroup Tag.E6)) :
      Subgroup (WeylGroup Tag.E6))
    rw [Sylow.coe_subgroup_smul, ← MulAut.conj_apply g x]
    exact Subgroup.smul_mem_pointwise_smul_iff.2 hxP
  rw [hg] at hmem
  change g * x * g⁻¹ ∈ (Q : Subgroup (WeylGroup Tag.E6)) at hmem
  rw [hQ] at hmem
  simpa [inv_inv] using hmem

end Sylow

end CFSG.StandardType.TwE6LemmaK
