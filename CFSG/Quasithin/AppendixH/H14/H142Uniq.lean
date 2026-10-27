module

public import CFSG.Quasithin.AppendixH.H14.H142Std
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM23

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Open
open CFSG.QuasithinUnique.Unc25G2.M2x
open scoped Pointwise

theorem qTab1_ne_hTab : ∀ n < 16, ∃ i < 24, (qTabArr[1]!)[i]! ≠ (hTabArr[n]!)[i]! := by
  decide +kernel

theorem stdEQ_ne_stdEH : stdEQ ≠ stdEH := by
  intro h
  have hmem : tabPerm qTabArr 1 ∈ stdEH := by
    rw [← h]
    exact tabPerm_mem_tabSub qTab_ok (by norm_num)
  obtain ⟨n, hn, heq⟩ := (mem_tabSub hTab_ok).mp hmem
  obtain ⟨i, hi, hne⟩ := qTab1_ne_hTab n hn
  apply hne
  have h1 : HasArr (tabPerm qTabArr 1) qTabArr[1]! := hasArr_tabPerm qTab_ok (by norm_num)
  have h2 : HasArr (tabPerm hTabArr n) hTabArr[n]! := hasArr_tabPerm hTab_ok hn
  have hval := congrArg (fun σ : S24 => ((σ ⟨i, hi⟩ : Fin 24) : ℕ)) heq
  rw [h1 ⟨i, hi⟩, h2 ⟨i, hi⟩] at hval
  exact hval

theorem inter_le_MY_sextet {a : Fin 24} {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))}
    {B : Finset (Fin 24)} {T₀ : Subgroup S24} (hS : IsSextet S) (hB : B ∈ S) (haB : a ∈ B)
    (hstS : ∀ g ∈ T₀, g • S = S) : T₀ ⊓ M23g a ≤ MY (M23g a) (S.erase B) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  rw [MY, Subgroup.mem_inf]
  refine ⟨hg.2, MulAction.mem_stabilizer_iff.mpr ?_⟩
  have hga : g a = a := ((mem_M23g_iff a g).mp hg.2).2
  have hgB : g • B = B := by
    have hgBmem : g • B ∈ S := by
      have : g • B ∈ g • S := Finset.smul_mem_smul_finset hB
      rwa [hstS g hg.1] at this
    by_contra hne
    have hdisj : Disjoint B (g • B) := hS.2.2.1 B hB (g • B) hgBmem (fun h => hne h.symm)
    have ha_gB : a ∈ g • B := by
      rw [Finset.mem_smul_finset]
      exact ⟨a, haB, by rw [Equiv.Perm.smul_def]; exact hga⟩
    exact (Finset.not_disjoint_iff.mpr ⟨a, haB, ha_gB⟩) hdisj
  rw [smul_erase_sextet, hstS g hg.1, hgB]

theorem inter_le_MY_octad {a : Fin 24} {O : Finset (Fin 24)} {T₀ : Subgroup S24}
    (hstO : ∀ g ∈ T₀, g • O = O) : T₀ ⊓ M23g a ≤ MY (M23g a) (O.erase a) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  rw [MY, Subgroup.mem_inf]
  refine ⟨hg.2, MulAction.mem_stabilizer_iff.mpr ?_⟩
  have hga : g a = a := ((mem_M23g_iff a g).mp hg.2).2
  rw [smul_erase_point, hstO g hg.1, hga]

theorem pCoreOf_le_of_isSylowIn {Γ M T : Subgroup S24} (hTM : T ≤ M) (hMΓ : M ≤ Γ)
    (hT : IsSylowIn 2 T Γ) : pCoreOf 2 M ≤ T := by
  refine pCoreOf_le_of_sylow (H := M) (P := T) hTM hT.2.1 ?_
  intro h2
  apply hT.2.2
  have hdvd : T.relIndex M ∣ T.relIndex Γ :=
    ⟨M.relIndex Γ, (Subgroup.relIndex_mul_relIndex T M Γ hTM hMΓ).symm⟩
  exact h2.trans hdvd

theorem elemAb_subgroupOf {G : Type*} [Group G] {K L : Subgroup G}
    (h : IsElemAbelian 2 K) : ElemAb (K.subgroupOf L) := by
  have h' := (isElemAbelian_two_iff K).mp h
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    exact Subtype.ext (h'.1 x.1 hx y.1 hy)
  · intro x hx
    exact Subtype.ext (h'.2 x.1 hx)

theorem eq_of_isE16
    {a : Fin 24} {T : Subgroup S24} (hT : IsSylowIn 2 T (M23g a)) {K₁ K₂ : Subgroup S24}
    (h₁ : K₁ ≤ T) (h₂ : K₂ ≤ T) (e₁ : IsElemAbelian 2 K₁) (e₂ : IsElemAbelian 2 K₂)
    (c₁ : Nat.card ↥K₁ = 16) (c₂ : Nat.card ↥K₂ = 16) (hne : K₁ ≠ K₂) {A : Subgroup S24}
    (hA : A ≤ T) (eA : IsElemAbelian 2 A) (cA : Nat.card ↥A = 16) : A = K₁ ∨ A = K₂ := by
  have h2E : TwoE ↥(M23g a) := twoE_M23.of_equiv (nonempty_iso_M23g a).some.symm
  obtain ⟨Ea, Eb, _ga, _gb, _hEaP, _hEbP, _hEane, _hEaab, _hEbab, _hcEa, _hcEb, hcl, -,
    -, -, -⟩ :=
    h2E.exists_at (P := T.subgroupOf (M23g a))
      (hT.2.1.comap_subtype (K := M23g a))
      (by simpa only [Subgroup.relIndex] using hT.2.2)
  have hK₁M : K₁ ≤ M23g a := h₁.trans hT.1
  have hK₂M : K₂ ≤ M23g a := h₂.trans hT.1
  have hAM : A ≤ M23g a := hA.trans hT.1
  have hK₁'P : K₁.subgroupOf (M23g a) ≤ T.subgroupOf (M23g a) :=
    Subgroup.subgroupOf_mono (M23g a) h₁
  have hK₂'P : K₂.subgroupOf (M23g a) ≤ T.subgroupOf (M23g a) :=
    Subgroup.subgroupOf_mono (M23g a) h₂
  have hA'P : A.subgroupOf (M23g a) ≤ T.subgroupOf (M23g a) :=
    Subgroup.subgroupOf_mono (M23g a) hA
  have he₁' : ElemAb (K₁.subgroupOf (M23g a)) := elemAb_subgroupOf e₁
  have he₂' : ElemAb (K₂.subgroupOf (M23g a)) := elemAb_subgroupOf e₂
  have heA' : ElemAb (A.subgroupOf (M23g a)) := elemAb_subgroupOf eA
  have hc₁' : Nat.card ↥(K₁.subgroupOf (M23g a)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₁M).toEquiv, c₁]
  have hc₂' : Nat.card ↥(K₂.subgroupOf (M23g a)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₂M).toEquiv, c₂]
  have hcA' : Nat.card ↥(A.subgroupOf (M23g a)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, cA]
  have h₁' := hcl (K₁.subgroupOf (M23g a)) hK₁'P he₁' hc₁'
  have h₂' := hcl (K₂.subgroupOf (M23g a)) hK₂'P he₂' hc₂'
  have hA' := hcl (A.subgroupOf (M23g a)) hA'P heA' hcA'
  have hKne' : K₁.subgroupOf (M23g a) ≠ K₂.subgroupOf (M23g a) := by
    intro h
    apply hne
    have hmap := congrArg (Subgroup.map (M23g a).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hK₁M,
      Subgroup.map_subgroupOf_eq_of_le hK₂M] at hmap
  have hAmem : A.subgroupOf (M23g a) = K₁.subgroupOf (M23g a) ∨
      A.subgroupOf (M23g a) = K₂.subgroupOf (M23g a) := by
    have hset : Ea = K₁.subgroupOf (M23g a) ∨ Ea = K₂.subgroupOf (M23g a) := by
      rcases h₁' with h1 | h1
      · exact Or.inl h1.symm
      · rcases h₂' with h2 | h2
        · exact Or.inr h2.symm
        · exact absurd (h1.trans h2.symm) hKne'
    have hset2 : Eb = K₁.subgroupOf (M23g a) ∨ Eb = K₂.subgroupOf (M23g a) := by
      rcases h₂' with h2 | h2
      · rcases h₁' with h1 | h1
        · exact absurd (h1.trans h2.symm) hKne'
        · exact Or.inl h1.symm
      · rcases h₁' with h1 | h1
        · exact Or.inr h2.symm
        · exact absurd (h1.trans h2.symm) hKne'
    rcases hA' with hAe | hAe
    · rcases hset with hset | hset
      · exact Or.inl (hAe.trans hset)
      · exact Or.inr (hAe.trans hset)
    · rcases hset2 with hset | hset
      · exact Or.inl (hAe.trans hset)
      · exact Or.inr (hAe.trans hset)
  rcases hAmem with h | h
  · left
    have hmap := congrArg (Subgroup.map (M23g a).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hAM,
      Subgroup.map_subgroupOf_eq_of_le hK₁M] at hmap
  · right
    have hmap := congrArg (Subgroup.map (M23g a).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hAM,
      Subgroup.map_subgroupOf_eq_of_le hK₂M] at hmap

theorem h142_part1
    {a : Fin 24} {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (hS : IsSextet S) (hB : B ∈ S) (haB : a ∈ B) (haO : a ∈ O)
    (hOu : ∃ B₁ ∈ S, ∃ B₂ ∈ S, B₁ ≠ B₂ ∧ O = B₁ ∪ B₂) (hstO : ∀ g ∈ T₀, g • O = O)
    (hstS : ∀ g ∈ T₀, g • S = S) (hT : IsSylowIn 2 (T₀ ⊓ M23g a) (M23g a)) :
    KY (M23g a) (S.erase B) ≠ KY (M23g a) (O.erase a) ∧
      ∀ A : Subgroup S24, (A ≤ T₀ ⊓ M23g a ∧ IsElemAbelian 2 A ∧ Nat.card ↥A = 2 ^ 4) ↔
        (A = KY (M23g a) (S.erase B) ∨ A = KY (M23g a) (O.erase a)) := by
  obtain ⟨c, hcM24, hca, hcQ, hcH⟩ := exists_std_data hS hB haB haO hOu
  have hQle : T₀ ⊓ M23g a ≤ MY (M23g a) (S.erase B) :=
    inter_le_MY_sextet (O := O) hS hB haB hstS
  have hHle : T₀ ⊓ M23g a ≤ MY (M23g a) (O.erase a) :=
    inter_le_MY_octad hstO
  have hKQle : KY (M23g a) (S.erase B) ≤ T₀ ⊓ M23g a :=
    pCoreOf_le_of_isSylowIn hQle inf_le_left hT
  have hKHle : KY (M23g a) (O.erase a) ≤ T₀ ⊓ M23g a :=
    pCoreOf_le_of_isSylowIn hHle inf_le_left hT
  have hconjQ := conj_stdQ (a := a) (Q := S.erase B) (c := c) hcM24 hca hcQ
  have hconjH := conj_stdH (a := a) (H := O.erase a) (c := c) hcM24 hca hcH
  have heabQ : IsElemAbelian 2 (KY (M23g a) (S.erase B)) :=
    isElemAbelian_of_map_conj 2 c (by rw [hconjQ.2]; exact isElemAbelian_stdEQ)
  have heabH : IsElemAbelian 2 (KY (M23g a) (O.erase a)) :=
    isElemAbelian_of_map_conj 2 c (by rw [hconjH.2]; exact isElemAbelian_stdEH)
  have hcardQ : Nat.card ↥(KY (M23g a) (S.erase B)) = 16 := by
    rw [← card_map_conj c (KY (M23g a) (S.erase B)), hconjQ.2, card_stdEQ]
  have hcardH : Nat.card ↥(KY (M23g a) (O.erase a)) = 16 := by
    rw [← card_map_conj c (KY (M23g a) (O.erase a)), hconjH.2, card_stdEH]
  have hKne : KY (M23g a) (S.erase B) ≠ KY (M23g a) (O.erase a) := by
    intro h
    apply stdEQ_ne_stdEH
    have hmap := congrArg (Subgroup.map (MulAut.conj c).toMonoidHom) h
    rwa [hconjQ.2, hconjH.2] at hmap
  have hE16 : ∀ A : Subgroup S24, A ≤ T₀ ⊓ M23g a → IsElemAbelian 2 A →
      Nat.card ↥A = 16 →
      A = KY (M23g a) (S.erase B) ∨ A = KY (M23g a) (O.erase a) :=
    fun A hA eA cA => eq_of_isE16 (K₁ := KY (M23g a) (S.erase B))
      (K₂ := KY (M23g a) (O.erase a)) hT hKQle hKHle heabQ heabH hcardQ hcardH hKne hA eA cA
  refine ⟨hKne, fun A => ⟨?_, ?_⟩⟩
  · rintro ⟨hA, eA, cA⟩
    exact hE16 A hA eA (by rw [cA]; norm_num)
  · rintro (hA | hA)
    · refine ⟨by rw [hA]; exact hKQle, by rw [hA]; exact heabQ, by rw [hA, hcardQ]; norm_num⟩
    · refine ⟨by rw [hA]; exact hKHle, by rw [hA]; exact heabH, by rw [hA, hcardH]; norm_num⟩

end CFSG.Quasithin.AppendixH.H14
