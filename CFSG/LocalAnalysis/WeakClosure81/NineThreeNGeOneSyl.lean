module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeEight

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ}

private theorem nine3_isSylowIn_of_le_top {H T : Subgroup G} (hTG : IsSylowIn 2 T ⊤)
    (hTH : T ≤ H) : IsSylowIn 2 T H := by
  refine ⟨hTH, hTG.isPGroup, ?_⟩
  intro hdvd
  have h1 := Subgroup.relIndex_mul_relIndex T H ⊤ hTH le_top
  exact hTG.not_dvd_relIndex (h1 ▸ dvd_mul_of_dvd_left hdvd (H.relIndex ⊤))

private theorem nine3_isSylowIn_conj {P H : Subgroup G} (hP : IsSylowIn 2 P H) (g : G) :
    IsSylowIn 2 (conjSubgroup P g) (conjSubgroup H g) := by
  refine ⟨E3.conjSubgroup_mono_left g hP.le, E3.isPGroup_conjSubgroup hP.isPGroup g, ?_⟩
  rw [E3.relIndex_conjSubgroup]
  exact hP.not_dvd_relIndex

private theorem nine3_exists_conj_of_isSylowIn {H P Q : Subgroup G}
    (hP : IsSylowIn 2 P H) (hQ : IsSylowIn 2 Q H) :
    ∃ h ∈ H, conjSubgroup P h = Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh, hle⟩ := E3.exists_le_conj_of_isSylowIn hP hQ.le hQ.isPGroup
  refine ⟨h, hh, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [E3.card_conjSubgroup, IsSylowIn.card_eq hP, IsSylowIn.card_eq hQ]

theorem nine3_normal_of_card_delta_two (h : Nine3Core V T A K S X p)
    (h2 : Nat.card ↥(nineDelta V S) = 2) : T ≤ normalizer (A : Set G) := by
  classical
  have hVA : nineDelta V S = ({V, A} : Set (Subgroup G)) := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · intro B hB
      rcases hB with rfl | rfl
      · exact h.V_mem_nineDelta
      · exact h.A_mem_nineDelta
    · rw [Set.ncard_pair h.ne.symm]
      have h3 : (nineDelta V S).ncard = 2 := by rw [← Nat.card_coe_set_eq, h2]
      omega
  have hconj_mem : ∀ B : Subgroup G, IsGConj V B → B ≤ T ⊓ normalizer (A : Set G) →
      B ∈ nineDelta V S := by
    intro B hBconj hBle
    refine ⟨hBconj, ?_⟩
    have h1 : B ≤ E3.wClos V 0 (T ⊓ normalizer (A : Set G)) := by
      obtain ⟨g, hg⟩ := hBconj
      rw [hg] at hBle ⊢
      exact conjSubgroup_le_wClos_zero hBle
    exact h1.trans ((nine_three_four_wClos h).trans (nine_three_four_centralizer h))
  let N₁ : Subgroup G := T ⊓ normalizer (A : Set G)
  have hA_le_N₁ : A ≤ N₁ := le_inf h.leT Subgroup.le_normalizer
  have hEq : T ⊓ normalizer (N₁ : Set G) = N₁ := by
    refine le_antisymm ?_ (le_inf inf_le_left Subgroup.le_normalizer)
    intro t ht
    have htT : t ∈ T := ht.1
    have htN : t ∈ normalizer (N₁ : Set G) := ht.2
    have hcN₁ : conjSubgroup N₁ t = N₁ :=
      conjSubgroup_eq_iff_mem_normalizer.mpr htN
    have hcA_le : conjSubgroup A t ≤ N₁ := by
      calc conjSubgroup A t ≤ conjSubgroup N₁ t := E3.conjSubgroup_mono_left t hA_le_N₁
        _ = N₁ := hcN₁
    have hconj : IsGConj V (conjSubgroup A t) := by
      obtain ⟨g0, hg0⟩ := h.conj
      exact ⟨g0 * t, by rw [hg0, CFSG.Quasithin.conjSubgroup_conjSubgroup]⟩
    have hmem := hconj_mem (conjSubgroup A t) hconj hcA_le
    rw [hVA] at hmem
    rcases hmem with hcase | hcase
    · exfalso
      have hVt : conjSubgroup V t = V :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (h.h9.sylow.le htT)
      have hVtinv : conjSubgroup V t⁻¹ = V := by
        have hh := E3.conjSubgroup_conj_inv V t
        rwa [hVt] at hh
      have hAV : A = V := by
        calc A = conjSubgroup (conjSubgroup A t) t⁻¹ := (E3.conjSubgroup_conj_inv A t).symm
          _ = conjSubgroup V t⁻¹ := by rw [hcase]
          _ = V := hVtinv
      exact h.ne hAV
    · exact ⟨htT, conjSubgroup_eq_iff_mem_normalizer.mp hcase⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnil : Group.IsNilpotent ↥T := IsPGroup.isNilpotent h.h9.sylow.isPGroup
  have hnc : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent
  have hnormeq : normalizer (N₁.subgroupOf T) = N₁.subgroupOf T := by
    have h1 : (normalizer (N₁ : Set G)).subgroupOf T = normalizer (N₁.subgroupOf T) :=
      Subgroup.subgroupOf_normalizer_eq inf_le_left
    have h2 : (T ⊓ normalizer (N₁ : Set G)).subgroupOf T = N₁.subgroupOf T :=
      congrArg (·.subgroupOf T) hEq
    rw [Subgroup.inf_subgroupOf_left] at h2
    rw [← h1]
    exact h2
  have htop : N₁.subgroupOf T = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) (N₁.subgroupOf T) hnormeq
  have hTN₁ : T ≤ N₁ := Subgroup.subgroupOf_eq_top.mp htop
  exact hTN₁.trans inf_le_right

theorem nine3_eq_of_normal_of_sylow {V T A : Subgroup G}
    (hM : IsSylowIn 2 T (normalizer (V : Set G))) (hTG : IsSylowIn 2 T ⊤)
    (hN : normalizer (T : Set G) ≤ normalizer (V : Set G)) (hA : IsGConj V A)
    (hAT : T ≤ normalizer (A : Set G)) : A = V := by
  obtain ⟨g, hg⟩ := hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM1 : IsSylowIn 2 T (normalizer (A : Set G)) := nine3_isSylowIn_of_le_top hTG hAT
  have hMg : conjSubgroup (normalizer (V : Set G)) g = normalizer (A : Set G) := by
    rw [hg]
    exact E3.conjSubgroup_normalizer V g
  have hM1' : IsSylowIn 2 (conjSubgroup T g) (normalizer (A : Set G)) := by
    rw [← hMg]
    exact nine3_isSylowIn_conj hM g
  obtain ⟨k, hkM1, hkc⟩ := nine3_exists_conj_of_isSylowIn hM1' hM1
  have hTn : conjSubgroup T (g * k) = T := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, hkc]
  have hnNT : g * k ∈ normalizer (T : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hTn
  have hnNV : g * k ∈ normalizer (V : Set G) := hN hnNT
  have hVn : conjSubgroup V (g * k) = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hnNV
  have hAk : conjSubgroup A k = A := conjSubgroup_eq_iff_mem_normalizer.mpr hkM1
  have hVnA : conjSubgroup V (g * k) = A := by
    rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, ← hg, hAk]
  exact hVnA.symm.trans hVn

theorem nine3NGeOne_of_isSylowIn_top (h : Nine3Core V T A K S X p) (hTG : IsSylowIn 2 T ⊤)
    (hN : normalizer (T : Set G) ≤ normalizer (V : Set G)) : Nine3NGeOne V S := by
  by_contra h3
  simp only [Nine3NGeOne] at h3
  have hlt : Nat.card ↥(nineDelta V S) < 3 := not_le.mp h3
  have hle : Nat.card ↥(nineDelta V S) ≤ 2 := by omega
  have hsub : ({V, A} : Set (Subgroup G)) ⊆ nineDelta V S := by
    intro B hB
    rcases hB with rfl | rfl
    · exact h.V_mem_nineDelta
    · exact h.A_mem_nineDelta
  have h2le : 2 ≤ Nat.card ↥(nineDelta V S) := by
    rw [Nat.card_coe_set_eq]
    calc 2 = ({V, A} : Set (Subgroup G)).ncard := (Set.ncard_pair h.ne.symm).symm
      _ ≤ (nineDelta V S).ncard := Set.ncard_le_ncard hsub
  have h2 : Nat.card ↥(nineDelta V S) = 2 := le_antisymm hle h2le
  have hAT : T ≤ normalizer (A : Set G) := nine3_normal_of_card_delta_two h h2
  exact h.ne (nine3_eq_of_normal_of_sylow h.h9.sylow hTG hN h.conj hAT)

end CFSG.LocalAnalysis.WeakClosure81

end
