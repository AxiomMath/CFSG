module

public import CFSG.LocalAnalysis.WeakClosure81.FiveOneMax
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem b5_FiveOne_conjSubgroup_inv_eq_conjSub (X : Subgroup G) (g : G) :
    conjSubgroup X g⁻¹ = B6.conjSub g X := by
  ext x
  rw [mem_conjSubgroup_iff, B6.mem_conjSub]
  simp

theorem five_one {H M A : Subgroup G} (h : Sec5Hyp H M A) (hN : 1 < (maxOver H A).ncard) :
    ∃ g ∈ H, conjSubgroup A g ≤ M ∧
      H = ⨆ N ∈ {N | N ∈ maxOver H (conjSubgroup A g) ∧ Odd (M.relIndex N)}, N := by
  classical
  have hA2 : IsPGroup 2 A := h.isElemAbelian.isPGroup
  have hM₁H : M ⊓ H ≤ H := inf_le_right
  have hM₁ne : M ⊓ H ≠ H := by
    intro heq
    exact h.not_le (heq ▸ inf_le_left)
  have hM₁lt : M ⊓ H < H := lt_of_le_of_ne hM₁H hM₁ne
  obtain ⟨M₀, hM₀, hM₁M₀⟩ := exists_isMaxSubgroupIn hM₁lt
  have hM₀H : M₀ ≤ H := hM₀.le
  have hnotHleM₀ : ¬ H ≤ M₀ := not_le_of_gt hM₀.1
  have hAM₁ : A ≤ M ⊓ H := le_inf h.le_M h.le_group
  have hAM₀ : A ≤ M₀ := hAM₁.trans hM₁M₀
  have hoddM₁H : Odd ((M ⊓ H).relIndex H) := by
    rw [inf_relIndex_right]
    exact h.odd_relIndex
  have hmul : (M ⊓ H).relIndex M₀ * M₀.relIndex H = (M ⊓ H).relIndex H :=
    Subgroup.relIndex_mul_relIndex (M ⊓ H) M₀ H hM₁M₀ hM₀H
  have hoddM₁M₀ : Odd ((M ⊓ H).relIndex M₀) :=
    Nat.Odd.of_mul_left (hmul.symm ▸ hoddM₁H)
  have hoddM₀H : Odd (M₀.relIndex H) :=
    Nat.Odd.of_mul_right (hmul.symm ▸ hoddM₁H)
  have hM₁eq : M ⊓ H = M ⊓ M₀ :=
    le_antisymm (le_inf inf_le_left hM₁M₀) (le_inf inf_le_left (inf_le_right.trans hM₀H))
  have hMrelM₀ : M.relIndex M₀ = (M ⊓ H).relIndex M₀ := by
    rw [hM₁eq]
    exact (Subgroup.inf_relIndex_right M M₀).symm
  have hoddMrelM₀ : Odd (M.relIndex M₀) := by
    rw [hMrelM₀]
    exact hoddM₁M₀
  have h₀ : Sec5Hyp H M₀ A :=
    ⟨h.isElemAbelian, h.le_group, hAM₀, hnotHleM₀, hoddM₀H⟩
  have hmax := five_one_max h₀ hM₀ hN
  have hexN : ∃ N : Subgroup G, N ∈ maxOver H A ∧ N ≠ M₀ ∧ Odd (M₀.relIndex N) := by
    by_contra hcon
    have hle : (⨆ N ∈ {N | N ∈ maxOver H A ∧ Odd (M₀.relIndex N)}, N) ≤ M₀ := by
      refine iSup₂_le fun N hN => ?_
      have h1 : ¬ (N ∈ maxOver H A ∧ N ≠ M₀ ∧ Odd (M₀.relIndex N)) := not_exists.mp hcon N
      by_cases hNM₀ : N = M₀
      · exact hNM₀.le
      · exact absurd ⟨hN.1, hNM₀, hN.2⟩ h1
    apply hnotHleM₀
    rw [hmax]
    exact hle
  obtain ⟨N, hNmax, hNne, hNodd⟩ := hexN
  have hA_inf : A ≤ N ⊓ M₀ := le_inf hNmax.2 hAM₀
  obtain ⟨P, hP, hAP⟩ := exists_isSylowIn_ge 2 hA_inf hA2
  have hPNle : P ≤ N := hP.1.trans inf_le_left
  have hPM₀ : P ≤ M₀ := hP.1.trans inf_le_right
  have hPN : IsSylowIn 2 P N := by
    refine ⟨hPNle, hP.isPGroup, ?_⟩
    have hodd1 : Odd (P.relIndex (N ⊓ M₀)) :=
      Nat.not_even_iff_odd.mp fun he => hP.not_dvd_relIndex (even_iff_two_dvd.mp he)
    have hodd2 : Odd ((N ⊓ M₀).relIndex N) := by
      rw [Subgroup.inf_relIndex_left]
      exact hNodd
    have hoddprod : Odd (P.relIndex N) := by
      rw [← Subgroup.relIndex_mul_relIndex P (N ⊓ M₀) N hP.1 inf_le_left]
      exact hodd1.mul hodd2
    exact fun hdvd => (Nat.not_even_iff_odd.mpr hoddprod) (even_iff_two_dvd.mpr hdvd)
  obtain ⟨R, hR, hPR⟩ := exists_isSylowIn_ge 2 hPM₀ hP.isPGroup
  obtain ⟨R', hR', hR'M₁⟩ := A4.exists_isSylowTwoOf_le_of_odd hM₁M₀ hoddM₁M₀
  obtain ⟨g₀, hg₀M₀, hg₀conj⟩ :=
    B6.isSylowTwoOf_exists_conj (show IsSylowTwoOf R M₀ from hR) hR'
  have hg₀H : g₀ ∈ H := hM₀H hg₀M₀
  have hconjH : B6.conjSub g₀ H = H := B6.conjSub_eq_self (Subgroup.le_normalizer hg₀H)
  have hconjM₀ : B6.conjSub g₀ M₀ = M₀ := B6.conjSub_eq_self (Subgroup.le_normalizer hg₀M₀)
  set N' : Subgroup G := B6.conjSub g₀ N with hN'def
  set P' : Subgroup G := B6.conjSub g₀ P with hP'def
  have hconjA_le_M : B6.conjSub g₀ A ≤ M := by
    calc B6.conjSub g₀ A ≤ B6.conjSub g₀ P := (B6.conjSub g₀).monotone hAP
      _ ≤ B6.conjSub g₀ R := (B6.conjSub g₀).monotone hPR
      _ = R' := hg₀conj.symm
      _ ≤ M ⊓ H := hR'M₁
      _ ≤ M := inf_le_left
  have hconjA_le_M₀ : B6.conjSub g₀ A ≤ M₀ := by
    calc B6.conjSub g₀ A ≤ B6.conjSub g₀ P := (B6.conjSub g₀).monotone hAP
      _ ≤ B6.conjSub g₀ R := (B6.conjSub g₀).monotone hPR
      _ = R' := hg₀conj.symm
      _ ≤ M ⊓ H := hR'M₁
      _ ≤ M₀ := hM₁M₀
  have hN'max_conj : B6.conjSub g₀ N ∈ maxOver H (B6.conjSub g₀ A) := by
    have hmaxOver : maxOver H (B6.conjSub g₀ A) = B6.conjSub g₀ '' maxOver H A := by
      have hh := maxOver_conjSub (g := g₀) (U := H) (X := A)
      rwa [hconjH] at hh
    rw [hmaxOver]
    exact ⟨N, hNmax, rfl⟩
  have hN'max : N' ∈ maxOver H (B6.conjSub g₀ A) := by
    rw [hN'def]
    exact hN'max_conj
  have hN'maxConj : N' ∈ maxOver H (conjSubgroup A g₀⁻¹) := by
    rw [b5_FiveOne_conjSubgroup_inv_eq_conjSub]
    exact hN'max
  have hM₀maxConj : M₀ ∈ maxOver H (conjSubgroup A g₀⁻¹) := by
    rw [b5_FiveOne_conjSubgroup_inv_eq_conjSub]
    exact ⟨hM₀, hconjA_le_M₀⟩
  have hP'M : P' ≤ M := by
    rw [hP'def]
    calc B6.conjSub g₀ P ≤ B6.conjSub g₀ R := (B6.conjSub g₀).monotone hPR
      _ = R' := hg₀conj.symm
      _ ≤ M ⊓ H := hR'M₁
      _ ≤ M := inf_le_left
  have hP'N' : P' ≤ N' := by
    rw [hP'def, hN'def]
    exact (B6.conjSub g₀).monotone hPNle
  have hP'N'_sylow : IsSylowTwoOf P' N' := by
    rw [hP'def, hN'def]
    exact B6.isSylowTwoOf_conjSub (show IsSylowTwoOf P N from hPN) g₀
  have hMrelN'_dvd : M.relIndex N' ∣ P'.relIndex N' :=
    Subgroup.relIndex_dvd_of_le_left N' hP'M
  have hoddP'relN' : Odd (P'.relIndex N') :=
    Nat.not_even_iff_odd.mp fun he => hP'N'_sylow.2.2 (even_iff_two_dvd.mp he)
  have hoddMrelN' : Odd (M.relIndex N') :=
    Odd.of_dvd_nat hoddP'relN' hMrelN'_dvd
  have hN'neM₀ : N' ≠ M₀ := by
    intro heq
    apply hNne
    have h2 : B6.conjSub g₀ N = B6.conjSub g₀ M₀ := by
      rw [← hN'def, heq, hconjM₀]
    exact (B6.conjSub g₀).injective h2
  have hN'notleM₀ : ¬ N' ≤ M₀ := by
    intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hMH : M₀ = H := hN'max.1.eq_of_lt_of_le hlt hM₀.le
      exact hnotHleM₀ hMH.symm.le
    · exact hN'neM₀ heq
  have hM₀supN' : M₀ ⊔ N' = H := by
    refine hM₀.eq_of_lt_of_le ?_ (sup_le hM₀.le hN'max.1.le)
    exact lt_of_le_of_ne le_sup_left (fun hh => hN'notleM₀ (le_sup_right.trans hh.symm.le))
  refine ⟨g₀⁻¹, H.inv_mem hg₀H, ?_, ?_⟩
  · rwa [b5_FiveOne_conjSubgroup_inv_eq_conjSub]
  · refine le_antisymm ?_ ?_
    · calc H = M₀ ⊔ N' := hM₀supN'.symm
        _ ≤ ⨆ N ∈ {N | N ∈ maxOver H (conjSubgroup A g₀⁻¹) ∧ Odd (M.relIndex N)}, N :=
          sup_le (le_iSup₂_of_le M₀ ⟨hM₀maxConj, hoddMrelM₀⟩ le_rfl)
            (le_iSup₂_of_le N' ⟨hN'maxConj, hoddMrelN'⟩ le_rfl)
    · exact iSup₂_le fun N hN => hN.1.1.le

end CFSG.LocalAnalysis.WeakClosure81
