module

public import CFSG.LocalAnalysis.WeakClosure81.FiveOneTrans
public import CFSG.LocalAnalysis.WeakClosure81.FiveNorm
public import CFSG.LocalAnalysis.WeakClosure81.FiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem five_one_max {H M A : Subgroup G} (h : Sec5Hyp H M A) (hM : IsMaxSubgroupIn H M)
    (hN : 1 < (maxOver H A).ncard) :
    H = ⨆ N ∈ {N | N ∈ maxOver H A ∧ Odd (M.relIndex N)}, N := by
  let J : Subgroup G := ⨆ N ∈ {N | N ∈ maxOver H A ∧ Odd (M.relIndex N)}, N
  have hMH : M ≤ H := hM.le
  have hMmem : M ∈ maxOver H A := ⟨hM, h.le_M⟩
  have hA2 : IsPGroup 2 A :=
    fun y => ⟨1, Subtype.ext (by simpa using h.isElemAbelian.2 y y.2)⟩
  have key : ∀ N₁ : Subgroup G, N₁ ∈ maxOver H A → N₁ ≠ M → Odd (M.relIndex N₁) → H ≤ J := by
    intro N₁ hN₁mem hN₁ne hN₁odd
    have hN₁H : N₁ ≤ H := hN₁mem.1.le
    have hMJ : M ≤ J := by
      refine le_iSup₂_of_le M ⟨hMmem, ?_⟩ le_rfl
      rw [Subgroup.relIndex_self]
      exact ⟨0, by norm_num⟩
    have hN₁J : N₁ ≤ J := le_iSup₂_of_le N₁ ⟨hN₁mem, hN₁odd⟩ le_rfl
    have hnot : ¬ N₁ ≤ M := by
      intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hEq := hN₁mem.1.eq_of_lt_of_le hlt hMH
        exact h.not_le (le_of_eq hEq.symm)
      · exact hN₁ne heq
    have hMlt : M < M ⊔ N₁ :=
      lt_of_le_of_ne le_sup_left (fun heq => hnot (heq.symm ▸ le_sup_right))
    have hsupH : M ⊔ N₁ ≤ H := sup_le hMH hN₁H
    have hsup : M ⊔ N₁ = H := hM.eq_of_lt_of_le hMlt hsupH
    calc H = M ⊔ N₁ := hsup.symm
      _ ≤ J := sup_le hMJ hN₁J
  have hex : ∃ N : Subgroup G, N ∈ maxOver H A ∧ N ≠ M := by
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (s := maxOver H A)).mp hN
    by_cases haM : a = M
    · exact ⟨b, hb, fun hbM => hab (haM.trans hbM.symm)⟩
    · exact ⟨a, ha, haM⟩
  obtain ⟨Nex, hNexMem, hNexNe⟩ := hex
  let Nset' : Set (Subgroup G) := {N | N ∈ maxOver H A ∧ N ≠ M}
  have hNex' : Nex ∈ Nset' := ⟨hNexMem, hNexNe⟩
  obtain ⟨N, hNmem, hNmax⟩ :=
    Set.exists_max_image Nset' (fun N => (Nat.card ↥(M ⊓ N)).factorization 2)
      (Set.toFinite Nset') ⟨Nex, hNex'⟩
  have hNmaxH : N ≤ H := hNmem.1.1.le
  have hAN : A ≤ N := hNmem.1.2
  have hNne : N ≠ M := hNmem.2
  have hAD : A ≤ M ⊓ N := le_inf h.le_M hAN
  obtain ⟨S, hS_syl, hAS⟩ := exists_isSylowIn_ge 2 hAD hA2
  have hS2 : IsPGroup 2 S := hS_syl.isPGroup
  have hSM : S ≤ M := hS_syl.le.trans inf_le_left
  have hSN : S ≤ N := hS_syl.le.trans inf_le_right
  have hSH : S ≤ H := hSM.trans hMH
  have hScard : Nat.card S = 2 ^ (Nat.card ↥(M ⊓ N)).factorization 2 := hS_syl.card_eq
  have MAX : ∀ L ∈ Nset', ∀ X : Subgroup G, X ≤ M ⊓ L → IsPGroup 2 X → ¬ S < X := by
    intro L hL X hXL hX2 hSX
    have hcardlt : Nat.card S < Nat.card X := Subgroup.card_lt_of_lt hSX
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hX2
    have hdvd : 2 ^ k ∣ Nat.card ↥(M ⊓ L) := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hXL
    have hkL : k ≤ (Nat.card ↥(M ⊓ L)).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos (α := ↥(M ⊓ L))).ne').mp hdvd
    have hkN : k ≤ (Nat.card ↥(M ⊓ N)).factorization 2 := hkL.trans (hNmax L hL)
    have hle : Nat.card X ≤ Nat.card S := by
      rw [hk, hScard]
      exact pow_le_pow_right' (by norm_num) hkN
    exact (not_le_of_gt hcardlt) hle
  show H = J
  refine le_antisymm ?_ ?_
  ·
    by_cases hcase : Odd (M.relIndex N)
    · exact key N hNmem.1 hNne hcase
    ·
      have h2SrelN : 2 ∣ S.relIndex N := by
        by_contra h2
        have hoddSN : Odd (S.relIndex N) :=
          Nat.not_even_iff_odd.mp (fun hev => h2 (even_iff_two_dvd.mp hev))
        have hdiv : M.relIndex N ∣ S.relIndex N :=
          Subgroup.relIndex_dvd_of_le_left (H := S) (K := M) (L := N) hSM
        exact hcase (Odd.of_dvd_nat hoddSN hdiv)
      have h2SrelM : 2 ∣ S.relIndex M := by
        by_contra h2
        have hoddSM : Odd (S.relIndex M) :=
          Nat.not_even_iff_odd.mp (fun hev => h2 (even_iff_two_dvd.mp hev))
        have hoddSH : Odd (S.relIndex H) := by
          rw [← Subgroup.relIndex_mul_relIndex S M H hSM hMH]
          exact Odd.mul hoddSM h.odd_relIndex
        have hoddSN : Odd (S.relIndex N) := by
          have hmul : Odd (S.relIndex N * N.relIndex H) := by
            rw [Subgroup.relIndex_mul_relIndex S N H hSN hNmaxH]
            exact hoddSH
          exact Nat.Odd.of_mul_left hmul
        exact (Nat.not_even_iff_odd.mpr hoddSN) (even_iff_two_dvd.mpr h2SrelN)
      have hnotMnorm : ¬ (M.subgroupOf H).Normal := by
        intro hMnorm
        have hnorm : N ≤ Subgroup.normalizer (M : Set G) :=
          hNmaxH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMH).mp hMnorm)
        have hnotNM : ¬ N ≤ M := by
          intro hle
          rcases lt_or_eq_of_le hle with hlt | heq
          · have hEq := hNmem.1.1.eq_of_lt_of_le hlt hMH
            exact h.not_le (le_of_eq hEq.symm)
          · exact hNne heq
        have hMlt : M < N ⊔ M :=
          lt_of_le_of_ne le_sup_right (fun heq => hnotNM (heq.symm ▸ le_sup_left))
        have hsupH : N ⊔ M ≤ H := sup_le hNmaxH hMH
        have hsup : N ⊔ M = H := hM.eq_of_lt_of_le hMlt hsupH
        have hoddMN : Odd (M.relIndex N) := by
          rw [← A4.relIndex_sup_eq_of_le_normalizer' (D := M) (T := N) hnorm, hsup]
          exact h.odd_relIndex
        exact hcase hoddMN
      obtain ⟨R, hR_syl, hSR⟩ := exists_isSylowIn_ge 2 hSM hS2
      obtain ⟨RN, hRN_syl, hSRN⟩ := exists_isSylowIn_ge 2 hSN hS2
      have hR2 : IsPGroup 2 R := hR_syl.isPGroup
      have hRN2 : IsPGroup 2 RN := hRN_syl.isPGroup
      have hneR : S ≠ R := fun heq => hR_syl.not_dvd_relIndex (heq ▸ h2SrelM)
      have hneRN : S ≠ RN := fun heq => hRN_syl.not_dvd_relIndex (heq ▸ h2SrelN)
      have hTM_lt : S < R ⊓ Subgroup.normalizer (S : Set G) :=
        lt_inf_normalizer_of_isPGroup hR2 hSR hneR
      have hTN_lt : S < RN ⊓ Subgroup.normalizer (S : Set G) :=
        lt_inf_normalizer_of_isPGroup hRN2 hSRN hneRN
      have hHnorm : H ≤ Subgroup.normalizer (S : Set G) := by
        by_contra hnotHnorm
        have hHn_lt : H ⊓ Subgroup.normalizer (S : Set G) < H :=
          lt_of_le_of_ne inf_le_left (fun heq => hnotHnorm (heq ▸ inf_le_right))
        obtain ⟨L, hLmax, hHnL⟩ := exists_isMaxSubgroupIn hHn_lt
        have hTM_Hn : R ⊓ Subgroup.normalizer (S : Set G) ≤
            H ⊓ Subgroup.normalizer (S : Set G) :=
          le_inf (inf_le_left.trans (hR_syl.le.trans hMH)) inf_le_right
        have hTM_L : R ⊓ Subgroup.normalizer (S : Set G) ≤ L := hTM_Hn.trans hHnL
        have hAL : A ≤ L := hAS.trans ((le_of_lt hTM_lt).trans hTM_L)
        have hLmem : L ∈ maxOver H A := ⟨hLmax, hAL⟩
        by_cases hLM : L = M
        · have hHnM : H ⊓ Subgroup.normalizer (S : Set G) ≤ M := hHnL.trans (le_of_eq hLM)
          have hTN_N : RN ⊓ Subgroup.normalizer (S : Set G) ≤ N :=
            inf_le_left.trans hRN_syl.le
          have hTN_Hn : RN ⊓ Subgroup.normalizer (S : Set G) ≤
              H ⊓ Subgroup.normalizer (S : Set G) :=
            le_inf (inf_le_left.trans (hRN_syl.le.trans hNmaxH)) inf_le_right
          have hTN_sub : RN ⊓ Subgroup.normalizer (S : Set G) ≤ M ⊓ N :=
            le_inf (hTN_Hn.trans hHnM) hTN_N
          exact (MAX N hNmem _ hTN_sub hRN2.to_inf_left) hTN_lt
        · exact (MAX L ⟨hLmem, hLM⟩ _ (le_inf (inf_le_left.trans hR_syl.le) hTM_L)
            hR2.to_inf_left) hTM_lt
      have hSn : (S.subgroupOf H).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
      have hu : ∀ X L : Subgroup G, S < X → X ≤ M → IsPGroup 2 X → IsMaxSubgroupIn H L →
          X ≤ L → L = M := by
        intro X L hSX hXM hX2 hLmax hXL
        by_contra hLM
        have hAL : A ≤ L := hAS.trans ((le_of_lt hSX).trans hXL)
        exact (MAX L ⟨⟨hLmax, hAL⟩, hLM⟩ X (le_inf hXM hXL) hX2) hSX
      obtain ⟨N₀, hN₀max, hSN₀, hN₀notM, hN₀odd⟩ :=
        five_one_end hM h.odd_relIndex hS2 hSM hSn h2SrelM hnotMnorm hu
      exact key N₀ ⟨hN₀max, hAS.trans hSN₀⟩ (fun hEq => hN₀notM (le_of_eq hEq)) hN₀odd
  · refine iSup₂_le ?_
    intro N hN
    exact (hN.1.1).le

end CFSG.LocalAnalysis.WeakClosure81
