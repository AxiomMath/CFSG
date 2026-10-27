module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveAbelian
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveFactors

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem mem_uniqueSet_inf_of_r8101 (D : Data G)
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ A B : Subgroup G}
    (hV₀ : V₀ ≠ ⊥) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X)
    (hc4 : F08.Case8100FourR D ![L, conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hAT : Permutes A D.T) (hBM : B ≤ D.M)
    (hBcard : Nat.card B = p) (hAB : ⁅A, B⁆ = A) (hBT : Permutes B D.T)
    (hR8101 : F08.R8101R D) :
    r = 31 ∧ A ⊓ L ∈ uniqueSet D.M ∧ A ⊓ conjSubgroup L x ∈ uniqueSet D.M := by
  have h8100' := h8100
  have hc4' := hc4
  obtain ⟨hLcal, hLne, hshape, hr, hrdvd, hpSig, hA₀card, hA₀le, hXprod, hMNX⟩ := h8100
  obtain ⟨hset0, hSzL, hp5, -, φ, hφ, hker⟩ := hc4
  have hrdvd' : r ∣ 2 ^ n - 1 := by
    have := hrdvd
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at this
    exact this
  have hshape0 : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hshape 0
  have hn5 : n = 5 := by
    rcases hshape0 with hN | hN
    · exact (CFSG.LocalAnalysis.UniquenessCase.UC22.P2214S.false_of_isSz_of_isL2 hSzL hN).elim
    · exact eq_five_of_isSz_five hN hSzL
  have hr31 : r = 31 := by
    have hdvd31 : r ∣ 31 := by
      have := hrdvd'
      rw [hn5] at this
      norm_num at this ⊢
      exact this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd31 with h | h
    · exact absurd h hr.ne_one
    · exact h
  obtain ⟨hA₁card, hA₂card, hA₁₂, hinf, hBcard5, hBn₁, hBn₂, hAeq, hfpf⟩ :=
    factors_of_case8100Four D hV₀ ctx h8100' hc4' hAsyl hAT hBM hBcard hAB hBT
  have h8100₁ : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p (A ⊓ L) X :=
    ⟨hLcal, hLne, hshape, hr, hrdvd, hpSig, hA₁card.trans hr31.symm,
      Or.inl (by simpa using inf_le_right), hXprod, hMNX⟩
  have hU₁ : A ⊓ L ∈ uniqueSet D.M :=
    hR8101 ![L, conjSubgroup L x] ![n, n] r p (A ⊓ L) X h8100₁ (Or.inr hc4')
  have h8100₂ : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p
      (A ⊓ conjSubgroup L x) X :=
    ⟨hLcal, hLne, hshape, hr, hrdvd, hpSig, hA₂card.trans hr31.symm,
      Or.inr (by simpa using inf_le_right), hXprod, hMNX⟩
  have hU₂ : A ⊓ conjSubgroup L x ∈ uniqueSet D.M :=
    hR8101 ![L, conjSubgroup L x] ![n, n] r p (A ⊓ conjSubgroup L x) X h8100₂ (Or.inr hc4')
  exact ⟨hr31, hU₁, hU₂⟩

theorem gap17_45_uniqueMaxFiveSE_of_nonabChief (D : Data G)
    (V₀ V : Subgroup G) (hK : S17.Gap17_45_NonabChief D V₀ V) :
    S17.Gap17_45_UniqueMaxFiveSE D V₀ V := by
  intro L X p n l r C Dc Gamma x A₀ A B hV₀ ctx h8100 hc4 hAsyl hAT hBM hBcard hAB hBT
    hcent hsp hR8101
  have h8100' := h8100
  have hc4' := hc4
  obtain ⟨hLcal, hLne, hshape, hr, hrdvd, hpSig, hA₀card, hA₀le, hXprod, hMNX⟩ := h8100
  have hp : p.Prime := (D.sig_prime p hpSig).1
  have hLM : L ≤ D.M := s13_le_of_mem_calC (by simpa using hLcal 0)
  have hKM : conjSubgroup L x ≤ D.M := s13_le_of_mem_calC (by simpa using hLcal 1)
  have hXprod' : (X : Set G) = (L : Set G) * (conjSubgroup L x : Set G) := by
    simpa using hXprod
  have hXM : X ≤ D.M := by
    intro z hz
    have hz' : z ∈ (L : Set G) * (conjSubgroup L x : Set G) := by rwa [← hXprod']
    obtain ⟨a, ha, b, hb, rfl⟩ := hz'
    exact D.M.mul_mem (hLM ha) (hKM hb)
  have hAM : A ≤ D.M := hAsyl.le.trans hXM
  have hMcal : D.M ∈ calMOf (A ⊔ B ⊔ D.T) :=
    ⟨D.maxLocal, sup_le (sup_le hAM hBM) D.sylowM.le⟩
  obtain ⟨hA₁card, hA₂card, hA₁₂, hinf, hBcard5, hBn₁, hBn₂, hAeq, hfpf⟩ :=
    factors_of_case8100Four D hV₀ ctx h8100' hc4' hAsyl hAT hBM hBcard hAB hBT
  obtain ⟨hr31, hU₁, hU₂⟩ :=
    mem_uniqueSet_inf_of_r8101 D hV₀ ctx h8100' hc4' hAsyl hAT hBM hBcard hAB hBT hR8101
  have hBne : B ≠ ⊥ := by
    intro h
    have : p = 1 := by rw [← hBcard, h, Subgroup.card_bot]
    exact hp.ne_one this
  have hBp : IsPGroup p B := IsPGroup.of_card (n := 1) (by rw [hBcard, pow_one])
  have hUB : B ∈ uniqueSet D.M := uc22p22r_mem_uniqueSet_of_sp D hp hsp hBM hBp hBne
  unfold UniqueMax
  refine Set.ext fun N => ⟨fun hN => ?_, fun hN => ?_⟩
  · rw [Set.mem_singleton_iff]
    by_contra hne
    have hNM : ¬ N ≤ D.M := fun hle => hne (hN.1.2 D.M D.maxLocal.1 hle).symm
    obtain ⟨H, hD₀H, hHN, hHM, hmin⟩ := exists_minimal_between hN.2 hNM
    have hYH : kerM D.M H ≤ H := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_left D.M H
    have hYM : kerM D.M H ≤ D.M :=
      CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_right D.M H
    have hYn : H ≤ normalizer (kerM D.M H : Set G) := le_normalizer_kerM D.M H
    have hYlt : kerM D.M H < H := lt_of_le_of_ne hYH fun h => hHM (h ▸ hYM)
    obtain ⟨R, hYR, hRH, hRn, hminR⟩ := exists_minimal_normal_above hYlt
    have hRM : ¬ R ≤ D.M := fun h =>
      (not_le_of_gt hYR) (le_kerM_of_normal hRH hRn h)
    have hA₁H : A ⊓ L ≤ H :=
      (inf_le_left.trans (le_sup_left.trans le_sup_left)).trans hD₀H
    have hA₂H : A ⊓ conjSubgroup L x ≤ H :=
      (inf_le_left.trans (le_sup_left.trans le_sup_left)).trans hD₀H
    have hBH : B ≤ H := (le_sup_right.trans le_sup_left).trans hD₀H
    have hD₀M : A ⊔ B ⊔ D.T ≤ D.M := sup_le (sup_le hAM hBM) D.sylowM.le
    have hHeq : (A ⊔ B ⊔ D.T) ⊔ R = H :=
      hmin ((A ⊔ B ⊔ D.T) ⊔ R) le_sup_left (sup_le hD₀H hRH)
        (fun hle => hRM (le_sup_right.trans hle))
    have hHMR : H ≤ (H ⊓ D.M) ⊔ R := by
      calc H = (A ⊔ B ⊔ D.T) ⊔ R := hHeq.symm
        _ ≤ (H ⊓ D.M) ⊔ R := sup_le_sup_right (le_inf hD₀H hD₀M) R
    by_cases hab : ⁅R, R⁆ ≤ kerM D.M H
    · exact false_of_abelian_chief D hA₁card hA₂card hA₁₂ hinf hBcard5
        hBn₁ hBn₂ hfpf hU₁ hU₂ hUB hA₁H hA₂H hBH hYR hRH hRn hminR hHMR hab
    · exact hK L X p n l r C Dc Gamma x A₀ A B hV₀ ctx h8100' hc4' hAsyl hAT hBM hBcard
        hAB hBT hcent hsp hR8101 N H R hN hne hD₀H hHN hHM hmin hYR hRH hRn hminR hab
  · rw [Set.mem_singleton_iff] at hN
    subst hN
    exact hMcal


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
