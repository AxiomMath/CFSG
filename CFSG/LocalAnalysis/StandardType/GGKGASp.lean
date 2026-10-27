module

public import CFSG.LocalAnalysis.StandardType.GGKGAAutomizer
public import CFSG.LocalAnalysis.StandardType.GGKGARank
public import CFSG.LocalAnalysis.StandardType.GGKGADefs
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative TableBSymp

namespace KGA

theorem kga_torusSCRank_sp
    {K : Type} [Field K] [Finite K] [CharP K 2] {N p : ℕ}
    (hN : 1 ≤ N) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K ^ 2 - 1) :
    GGTorusSCRank p N (LargeEvenProj (LargeEvenSpGroup K N))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K N)) := by
  have hfac : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
    obtain ⟨q, hq⟩ : ∃ q, Nat.card K = q + 1 :=
      ⟨Nat.card K - 1, by have := Nat.card_pos (α := K); omega⟩
    rw [hq]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rcases (Nat.Prime.dvd_mul hp).1 (hfac ▸ hpq) with h | h
  · exact ggTorusSCRank_sp hN hp h
  · exact kga_torusSCRank_split hN hp hp2 h

theorem kga_torusSCRank_recipe
    {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (2 ^ n) ^ 2 - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ GGTorusSCRank p l R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    kga_torusSCRank_sp hl hp hp2 (by rw [hK]; exact hpq)⟩

theorem kga_torusSCRank_label
    {p f N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : 1 ≤ N)
    (hpq : p ∣ (2 ^ f) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.C, N, f⟩ fun R _ I _ => GGTorusSCRank p N R I :=
  fun _ hQ => kga_torusSCRank_recipe hp hp2 hpq hN hQ

theorem kga_sp_split
    {K : Type} [Field K] [Finite K] [CharP K 2] {N p : ℕ} (hN : 3 ≤ N)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusAutCardSC p (LargeEvenProj (LargeEvenSpGroup K N))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K N)) N
      (2 ^ N * N.factorial) := by
  have : NeZero N := ⟨by omega⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  have hrk : p ^ N ≤ Nat.card A :=
    kga_torusSCRank_split (by omega) hp hp2 hpq L' ψ hψ hker hperf A hA hAI hsc
  obtain ⟨k, Θ, -, -, hsgn, hperm, hsp⟩ := exists_signedModel hp hp2 TableBSymp.sp_I_subset_inn
    TableBSymp.center_spProj_eq_bot (SpModel.ggTorusSignedElt_sp hp hp2 hpq) hψ hker hperf hA hAI
    hrk h3
  have hk : k = N := kga_k_eq hp Θ hrk (kga_card_le_sp hp hp2 hψ hker hperf hA hAI)
  subst hk
  exact ⟨hrk, kga_card_automizer hp hp2 Θ hsgn hperm hsp⟩

theorem kga_sp_nonsplit
    {K : Type} [Field K] [Finite K] [CharP K 2] {N p : ℕ} (hN : 3 ≤ N)
    (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) :
    GGTorusAutCardSC p (LargeEvenProj (LargeEvenSpGroup K N))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K N)) N
      (2 ^ N * N.factorial) := by
  have : NeZero N := ⟨by omega⟩
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  obtain ⟨hsgnSC, hcp⟩ := ggSpNonsplitTorusInput_holds K N p (by omega) hp hpq
  have hrk : p ^ N ≤ Nat.card A :=
    ggTorusSCRank_sp (by omega) hp hpq L' ψ hψ hker hperf A hA hAI hsc
  obtain ⟨k, Θ, -, -, hsgn, hperm, hsp⟩ := exists_signedModelSC hp hp2
    TableBSymp.sp_I_subset_inn TableBSymp.center_spProj_eq_bot hcp hsgnSC hψ hker hperf hA hAI
    h3 hsc
  have hk : k = N := kga_k_eq hp Θ hrk (kga_card_le_sp hp hp2 hψ hker hperf hA hAI)
  subst hk
  exact ⟨hrk, kga_card_automizer hp hp2 Θ hsgn hperm hsp⟩


theorem kga_sp
    {K : Type} [Field K] [Finite K] [CharP K 2] {N p : ℕ} (hN : 3 ≤ N)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K ^ 2 - 1) :
    GGTorusAutCardSC p (LargeEvenProj (LargeEvenSpGroup K N))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K N)) N
      (2 ^ N * N.factorial) := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hfac : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
    obtain ⟨q, hq'⟩ : ∃ q, Nat.card K = q + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hq']
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rcases (Nat.Prime.dvd_mul hp).1 (hfac ▸ hpq) with h | h
  · exact kga_sp_nonsplit hN hp h
  · exact kga_sp_split hN hp hp2 h

theorem kga_sp_of_pos
    {K : Type} [Field K] [Finite K] [CharP K 2] {N p : ℕ}
    (hN : 1 ≤ N) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K ^ 2 - 1) :
    GGTorusAutCardSC p (LargeEvenProj (LargeEvenSpGroup K N))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K N)) N
      (2 ^ N * N.factorial) := by
  by_cases hN3 : 3 ≤ N
  · exact kga_sp hN3 hp hp2 hpq
  · have : NeZero N := ⟨by omega⟩
    intro L' _ _ ψ hψ hker hperf A hA hAI h3 _
    have hle := kga_card_le_sp hp hp2 hψ hker hperf hA hAI
    have hlt : p ^ N < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact False.elim ((not_lt_of_ge (h3.trans hle)) hlt)

theorem kga_recipe
    {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (2 ^ n) ^ 2 - 1) (hl : 3 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ GGTorusAutCardSC p R I l (2 ^ l * l.factorial) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, kga_sp hl hp hp2 (by rw [hK]; exact hpq)⟩

theorem kga_label
    {p f N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : 3 ≤ N)
    (hpq : p ∣ (2 ^ f) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.C, N, f⟩ fun R _ I _ => GGTorusAutCardSC p R I N (2 ^ N * N.factorial) :=
  fun _ hQ => kga_recipe hp hp2 hpq hN hQ

theorem kga_label_of_pos
    {p f N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : 1 ≤ N)
    (hpq : p ∣ (2 ^ f) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.C, N, f⟩ fun R _ I _ => GGTorusAutCardSC p R I N (2 ^ N * N.factorial) := by
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    kga_sp_of_pos hN hp hp2 (by rw [hK]; exact hpq)⟩

theorem ggPumpCAutKnown_of_F4
    (hF4 : GGPumpCAutKnownF4) : GGPumpCAutKnown := by
  intro p hp hp2 f hf hpq
  exact ⟨fun N hN => kga_label hp hp2 hN hpq, hF4 p hp hp2 f hf hpq⟩

end KGA

end CFSG.StandardType

end
