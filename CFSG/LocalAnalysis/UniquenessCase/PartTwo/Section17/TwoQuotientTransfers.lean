module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TwoQuotientLift
public import CFSG.GroupTheory.PermutesPullback
public import CFSG.GroupTheory.PermutingProducts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_noncentral_three_K1Nine_of_pow {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ}
    (hpow : ∀ s ∈ S1Nine D L, s ^ n ∈ Subgroup.centralizer (K1Nine D L : Set (Mbar9 D)))
    (hK : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), Inputs1719.KYForm Y K S →
      Nonempty (↥K ≃* Bar2 L) → (∀ s ∈ S, s ^ n = 1) →
      ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
        ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S) :
    ∃ E : Subgroup (Mbar9 D), E ≤ K1Nine D L ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ E ≤ (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype ∧
      Permutes E (S1Nine D L) := by
  have hZ := odd_card_center_K1Nine hL
  have hS : IsPGroup 2 (S1Nine D L) :=
    (isSylowOf_Tbar (D := D)).isPGroup.to_le inf_le_left
  have hSK : S1Nine D L ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := inf_le_right
  let hCnorm := CFSG.GroupTheory.twoQuotientC_normal hSK
  have : (CFSG.GroupTheory.twoQuotientC (K1Nine D L) (S1Nine D L)).Normal := hCnorm
  let Y := CFSG.GroupTheory.twoQuotientY (K1Nine D L) (S1Nine D L) hCnorm
  let KY := CFSG.GroupTheory.twoQuotientKY (K1Nine D L) (S1Nine D L) hCnorm
  let SY := CFSG.GroupTheory.twoQuotientSY (K1Nine D L) (S1Nine D L) hCnorm
  obtain ⟨hky, hKYe, hexp⟩ := twoQuotientKYForm_of_calC hL
  obtain ⟨EY, hEYK, hEYne, hEYp, hEYexp, hEYnc, hEYperm⟩ :=
    hK Y KY SY hky hKYe (hexp n hpow)
  let J : Subgroup (Mbar9 D) := K1Nine D L ⊔ S1Nine D L
  let π : ↥J →* Y := QuotientGroup.mk' (CFSG.GroupTheory.twoQuotientC
    (K1Nine D L) (S1Nine D L))
  let A₀ : Subgroup ↥J := EY.comap π ⊓ (K1Nine D L).subgroupOf J
  obtain ⟨E, hEK, ⟨eE⟩, hEeq⟩ :=
    CFSG.GroupTheory.twoQuotient_lift_subgroup hZ hS hSK (E_Y := EY) hEYK
  have hEeq' : E = A₀.map J.subtype := hEeq
  have hXeq : E.subgroupOf J = A₀ := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [hEeq']
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_subtype_le A₀)]
  have hXmap : (E.subgroupOf J).map π = EY := by
    rw [hXeq]
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      exact (Subgroup.mem_inf.mp ha).1
    · intro y hy
      have hyK : y ∈ twoQuotientKY (K1Nine D L) (S1Nine D L) hCnorm := hEYK hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hyK
      have hkA : k ∈ A₀ := by
        refine Subgroup.mem_inf.mpr ⟨?_, hk⟩
        rw [Subgroup.mem_comap, hky]
        exact hy
      exact Subgroup.mem_map.mpr ⟨k, hkA, hky⟩
  have hC_le_SJ : CFSG.GroupTheory.twoQuotientC (K1Nine D L) (S1Nine D L) ≤
      (S1Nine D L).subgroupOf J := by
    intro c hc
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).1
  have hEpermJ : ((E.subgroupOf J : Set ↥J) * ((S1Nine D L).subgroupOf J : Set ↥J) =
      ((S1Nine D L).subgroupOf J : Set ↥J) * (E.subgroupOf J : Set ↥J)) := by
    have h1 : ((E.subgroupOf J).map π : Set Y) * (SY : Set Y) =
        (SY : Set Y) * ((E.subgroupOf J).map π : Set Y) := by
      rw [hXmap]
      exact hEYperm
    have hkerπ : π.ker ≤ (S1Nine D L).subgroupOf J := by
      rw [show π.ker = CFSG.GroupTheory.twoQuotientC (K1Nine D L) (S1Nine D L) from
        QuotientGroup.ker_mk' _]
      exact hC_le_SJ
    exact permutes_of_map_permutes π hkerπ h1
  have hEperm : Permutes E (S1Nine D L) := by
    have h1 := CFSG.GroupTheory.map_permutes_map (f := J.subtype) hEpermJ
    rwa [Subgroup.map_subgroupOf_eq_of_le (hEK.trans (le_sup_left : K1Nine D L ≤ J)),
      Subgroup.map_subgroupOf_eq_of_le (le_sup_right : S1Nine D L ≤ J)] at h1
  have hEp : IsPGroup 3 ↥E := hEYp.of_equiv eE.symm
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have h1 : eE ⟨x, hx⟩ ^ 3 = 1 :=
      Subtype.ext (by simpa using hEYexp _ (eE ⟨x, hx⟩).2)
    have h2 : eE ((⟨x, hx⟩ : ↥E) ^ 3) = eE 1 := by
      rw [map_pow, map_one]
      exact h1
    have h3 : (⟨x, hx⟩ : ↥E) ^ 3 = 1 := eE.injective h2
    simpa using congrArg (fun z : ↥E => (z : Mbar9 D)) h3
  have hEnc : ¬ E ≤ (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype := by
    intro hEcent
    apply hEYnc
    intro y hy
    have hy' : y ∈ (E.subgroupOf J).map π := by rwa [hXmap]
    obtain ⟨x, hxX, hxy⟩ := Subgroup.mem_map.mp hy'
    rw [← hxy] at hy ⊢
    refine Subgroup.mem_map.mpr ⟨⟨π x, hEYK hy⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨k', hk', hky⟩ := Subgroup.mem_map.mp k.2
    have hkK : ((k' : ↥J) : Mbar9 D) ∈ K1Nine D L := hk'
    have hkeq : k = (⟨π k', by rw [hky]; exact k.2⟩ : ↥KY) := Subtype.ext hky.symm
    rw [hkeq]
    have hxE : ((x : ↥J) : Mbar9 D) ∈ E := Subgroup.mem_subgroupOf.mp hxX
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hEcent hxE)
    have hcommJ : Commute x k' := by
      have hEq : (⟨((k' : ↥J) : Mbar9 D), hkK⟩ : ↥(K1Nine D L)) * z =
          z * ⟨((k' : ↥J) : Mbar9 D), hkK⟩ := Subgroup.mem_center_iff.mp hz _
      have h' := congrArg (K1Nine D L).subtype hEq
      change J.subtype k' * (K1Nine D L).subtype z =
        (K1Nine D L).subtype z * J.subtype k' at h'
      rw [hzx] at h'
      exact Subtype.ext h'.symm
    have hcommJeq : x * k' = k' * x := hcommJ
    have hcommπ : π x * π k' = π k' * π x := by
      rw [← map_mul, ← map_mul]
      exact congrArg π hcommJeq
    exact Subtype.ext hcommπ.symm
  have hEne : E ≠ ⊥ := by
    intro hbot
    apply hEYne
    rw [← hXmap, show E.subgroupOf J = ⊥ by rw [hbot]; exact Subgroup.bot_subgroupOf J,
      Subgroup.map_bot]
  exact ⟨E, hEK, hEne, hEp, hEexp, hEnc, hEperm⟩

theorem exists_pair_of_calC_of_bar2Inv {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))
    (Φ : ∀ (X : Type) [Group X] [Finite X], Subgroup X → Prop)
    (hΦ : ∀ (X X' : Type) [Group X] [Finite X] [Group X'] [Finite X'] (H : Subgroup X)
      (H' : Subgroup X'), Nonempty (Bar2 H ≃* Bar2 H') → (Φ X H ↔ Φ X' H'))
    (hfact : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y),
      Inputs1719.KYForm Y K S → Nonempty (↥K ≃* Bar2 L) →
      ∃ H₁ H₂ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ H₁ ⊔ H₂ = ⊤ ∧ Φ Y H₁ ∧ Φ Y H₂ ∧
        3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂) :
    ∃ H₁ H₂ : Subgroup G, D.T ≤ H₁ ∧ D.T ≤ H₂ ∧ H₁ ≤ L ⊔ D.T ∧ H₂ ≤ L ⊔ D.T ∧
      H₁ ⊔ H₂ = L ⊔ D.T ∧ Φ G H₁ ∧ Φ G H₂ ∧ 3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂ := by
  obtain ⟨Y, hYgrp, hYfin, KY, SY, f', hky, hKYe, hf'surj, hker2, -, hTmap, -⟩ :=
    exists_twoQuotient_lift hL hnorm
  obtain ⟨P₁, P₂, hSP₁, hSP₂, hsup, hFS₁, hFS₂, h3₁, h3₂⟩ := hfact Y KY SY hky hKYe
  let H : Subgroup G := L ⊔ D.T
  have hSmap₁ : (D.T.subgroupOf H).map f' ≤ P₁ := by
    rw [show D.T.subgroupOf H = D.T.subgroupOf (L ⊔ D.T) from rfl, hTmap]
    exact hSP₁
  have hSmap₂ : (D.T.subgroupOf H).map f' ≤ P₂ := by
    rw [show D.T.subgroupOf H = D.T.subgroupOf (L ⊔ D.T) from rfl, hTmap]
    exact hSP₂
  let K₁ : Subgroup ↥H := P₁.comap f'
  let K₂ : Subgroup ↥H := P₂.comap f'
  have hTK₁ : D.T.subgroupOf H ≤ K₁ := fun t ht =>
    Subgroup.mem_comap.mpr (hSmap₁ (Subgroup.mem_map_of_mem f' ht))
  have hTK₂ : D.T.subgroupOf H ≤ K₂ := fun t ht =>
    Subgroup.mem_comap.mpr (hSmap₂ (Subgroup.mem_map_of_mem f' ht))
  have hjoinK : K₁ ⊔ K₂ = ⊤ := by
    rw [Subgroup.comap_sup_eq f' P₁ P₂ hf'surj, hsup, Subgroup.comap_top]
  have hFSK₁ : Φ ↥H K₁ := by
    obtain ⟨e⟩ := bar2_comap_mulEquiv f' hf'surj hker2 P₁
    exact (hΦ _ _ K₁ P₁ ⟨e⟩).mpr hFS₁
  have hFSK₂ : Φ ↥H K₂ := by
    obtain ⟨e⟩ := bar2_comap_mulEquiv f' hf'surj hker2 P₂
    exact (hΦ _ _ K₂ P₂ ⟨e⟩).mpr hFS₂
  have h3K₁ : 3 ∣ Nat.card ↥K₁ := by
    have hdvd : Nat.card ↥P₁ ∣ Nat.card ↥K₁ := by
      have h := Subgroup.card_map_dvd (H := K₁) f'
      rwa [Subgroup.map_comap_eq_self_of_surjective hf'surj] at h
    exact h3₁.trans hdvd
  have h3K₂ : 3 ∣ Nat.card ↥K₂ := by
    have hdvd : Nat.card ↥P₂ ∣ Nat.card ↥K₂ := by
      have h := Subgroup.card_map_dvd (H := K₂) f'
      rwa [Subgroup.map_comap_eq_self_of_surjective hf'surj] at h
    exact h3₂.trans hdvd
  refine ⟨K₁.map H.subtype, K₂.map H.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc D.T = (D.T.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_sup_right : D.T ≤ L ⊔ D.T)).symm
      _ ≤ K₁.map H.subtype := Subgroup.map_mono hTK₁
  · calc D.T = (D.T.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_sup_right : D.T ≤ L ⊔ D.T)).symm
      _ ≤ K₂.map H.subtype := Subgroup.map_mono hTK₂
  · exact Subgroup.map_subtype_le K₁
  · exact Subgroup.map_subtype_le K₂
  · calc K₁.map H.subtype ⊔ K₂.map H.subtype = (K₁ ⊔ K₂).map H.subtype :=
        (Subgroup.map_sup ..).symm
      _ = (⊤ : Subgroup ↥H).map H.subtype := by rw [hjoinK]
      _ = H := by rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = L ⊔ D.T := rfl
  · obtain ⟨e⟩ := nonempty_bar2_mulEquiv_map_subtype K₁
    exact (hΦ _ _ K₁ (K₁.map H.subtype) ⟨e⟩).mp hFSK₁
  · obtain ⟨e⟩ := nonempty_bar2_mulEquiv_map_subtype K₂
    exact (hΦ _ _ K₂ (K₂.map H.subtype) ⟨e⟩).mp hFSK₂
  · rwa [Subgroup.card_map_of_injective H.subtype_injective]
  · rwa [Subgroup.card_map_of_injective H.subtype_injective]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
