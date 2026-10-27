module

public import CFSG.RankThree.PartTwo.Sec4.E27.FixG2Model
public import CFSG.RankThree.PartTwo.Sec4.E27.InnerRank
public import CFSG.RankThree.PartTwo.Sec4.E27.FixStandard

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Open TauCeti
open CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof CFSG.AGLEmbeddingD2
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem le_closure_centralizers_of_equiv {Y Q : Type} [Group Y] [Group Q] {H A : Subgroup Y}
    (hAH : A ≤ H) (e : ↥H ≃* Q)
    (h : Subgroup.closure {c : Q | ∃ b ∈ (A.subgroupOf H).map e.toMonoidHom, b ≠ 1 ∧
      c * b = b * c} = ⊤) :
    H ≤ Subgroup.closure {x : Y | x ∈ H ∧ ∃ b ∈ A, b ≠ 1 ∧ x * b = b * x} := by
  intro x hx
  set SH : Set ↥H := {y | ∃ b ∈ A.subgroupOf H, b ≠ 1 ∧ y * b = b * y} with hSHdef
  have hsub1 : e.symm.toMonoidHom '' {c : Q | ∃ b ∈ (A.subgroupOf H).map e.toMonoidHom, b ≠ 1 ∧
      c * b = b * c} ⊆ SH := by
    rintro _ ⟨c, ⟨_, ⟨a, ha, rfl⟩, hb1, hcb⟩, rfl⟩
    refine ⟨a, ha, fun h => hb1 (by simp [h]), ?_⟩
    have := congrArg e.symm hcb
    simpa [map_mul] using this
  have hSH : Subgroup.closure SH = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have h1 : e y ∈ Subgroup.closure {c : Q | ∃ b ∈ (A.subgroupOf H).map e.toMonoidHom, b ≠ 1 ∧
        c * b = b * c} := by rw [h]; trivial
    have h2 : e.symm.toMonoidHom (e y) ∈ (Subgroup.closure {c : Q | ∃ b ∈
        (A.subgroupOf H).map e.toMonoidHom, b ≠ 1 ∧ c * b = b * c}).map e.symm.toMonoidHom :=
      ⟨_, h1, rfl⟩
    rw [MonoidHom.map_closure] at h2
    simpa using (Subgroup.closure_mono hsub1) h2
  have hsub2 : H.subtype '' SH ⊆ {x : Y | x ∈ H ∧ ∃ b ∈ A, b ≠ 1 ∧ x * b = b * x} := by
    rintro _ ⟨y, ⟨b, hb, hb1, hyb⟩, rfl⟩
    refine ⟨y.2, (b : Y), hb, fun h => hb1 (Subtype.ext h), ?_⟩
    exact congrArg Subtype.val hyb
  have h3 : H.subtype ⟨x, hx⟩ ∈ (Subgroup.closure SH).map H.subtype :=
    ⟨⟨x, hx⟩, by rw [hSH]; trivial, rfl⟩
  rw [MonoidHom.map_closure] at h3
  exact (Subgroup.closure_mono hsub2) h3



theorem fixPlaneGen_g2_three {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 4 ≤ f)
    (hK : Nat.card K = 2 ^ f) : FixPlaneGen (adjointGroup .G2 K) 3 := by
  classical
  haveI : CharP K 2 := charP_two_of_card hK
  refine fixPlaneGen_of_standard (MulAut.conj : adjointGroup .G2 K →* MulAut _).range
    {g | ∃ σ : K ≃+* K, orderOf σ = 3 ∧ g = entrywiseAdjointAut .G2 σ} ?_ ?_
  · intro α hα
    obtain ⟨h0, σ, hσ, h⟩ := exists_conj_entrywise Nat.prime_three (by omega) hK α hα
    refine ⟨(MulAut.conj h0)⁻¹, ?_, entrywiseAdjointAut .G2 σ, ⟨σ, hσ, rfl⟩, ?_⟩
    · exact (MulAut.conj : adjointGroup .G2 K →* MulAut _).range.inv_mem ⟨h0, rfl⟩
    · rw [← h]
      group
  · rintro _ ⟨σ, hσ, rfl⟩ A hA hAa hAc
    rw [fixedSubgroup_entrywise_eq] at hA ⊢
    have hcard := SEITZ6.card_eq_card_fixSubfield_pow σ
    rw [hσ, hK] at hcard
    have hdvd : Nat.card (fixSubfield σ) ∣ 2 ^ f := by
      rw [hcard]
      exact dvd_pow_self _ (by norm_num)
    obtain ⟨m, hm, hmk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hmk, ← pow_mul] at hcard
    have hfm : f = m * 3 := Nat.pow_right_injective (le_refl 2) hcard
    have hm2 : 2 ≤ m := by omega
    let q0 : PrimePower := ⟨2, m, Nat.prime_two, by omega⟩
    have hq0 : q0.card = Nat.card (fixSubfield σ) := by
      rw [PrimePower.card_def]
      exact hmk.symm
    have hv : (LieTypeIndex.G2 q0).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
        simp only [LieTypeIndex.inStandardRange_iff]
        omega
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    let ε := g2FixedEquiv σ
    refine le_closure_centralizers_of_equiv hA ε ?_
    refine g2_plane_closure q0 rfl hv hq0.symm _ ?_ ?_
    · exact CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hAa _) _
    · rw [Subgroup.card_map_of_injective ε.injective]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAc]

theorem seitz27_g2 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 4 ≤ f)
    (hK : Nat.card K = 2 ^ f) : Seitz27 (adjointGroup .G2 K) :=
  seitz27_g2_of_plane hf hK (fixPlaneGen_g2_three hf hK)

end CFSG.RankThree.PartTwo.Sec4.E27
