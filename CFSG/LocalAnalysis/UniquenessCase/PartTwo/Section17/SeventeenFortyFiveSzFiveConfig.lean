module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveAssembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
open CFSG.LocalAnalysis.RankThreeUC
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem no_abelian_minimal_above (D : Data G)
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ A B : Subgroup G}
    (hV₀ : V₀ ≠ ⊥) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X)
    (hc4 : F08.Case8100FourR D ![L, conjSubgroup L x] p X)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X) (hAT : Permutes A D.T) (hBM : B ≤ D.M)
    (hBcard : Nat.card B = p) (hAB : ⁅A, B⁆ = A) (hBT : Permutes B D.T)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (hR8101 : F08.R8101R D)
    {H : Subgroup G}
    (hD₀H : A ⊔ B ⊔ D.T ≤ H)
    (hmin : ∀ H' : Subgroup G, A ⊔ B ⊔ D.T ≤ H' → H' ≤ H → ¬ H' ≤ D.M → H' = H)
    {W : Subgroup G} (hYW : kerM D.M H < W) (hWH : W ≤ H)
    (hWn : H ≤ normalizer (W : Set G))
    (hminW : ∀ W' : Subgroup G, kerM D.M H ≤ W' → W' ≤ W →
      H ≤ normalizer (W' : Set G) → W' = kerM D.M H ∨ W' = W) :
    ¬ ⁅W, W⁆ ≤ kerM D.M H := by
  classical
  have h8100' := h8100
  have hc4' := hc4
  obtain ⟨hLcal, -, -, -, -, hpSig, -, -, hXprod, -⟩ := h8100
  obtain ⟨hA₁card, hA₂card, hA₁₂, hinf, hBcard5, hBn₁, hBn₂, -, hfpf⟩ :=
    factors_of_case8100Four D hV₀ ctx h8100' hc4' hAsyl hAT hBM hBcard hAB hBT
  obtain ⟨-, hU₁, hU₂⟩ :=
    mem_uniqueSet_inf_of_r8101 D hV₀ ctx h8100' hc4' hAsyl hAT hBM hBcard hAB hBT hR8101
  have hp : p.Prime := (D.sig_prime p hpSig).1
  have hBne : B ≠ ⊥ := by
    intro h
    have : p = 1 := by rw [← hBcard, h, Subgroup.card_bot]
    exact hp.ne_one this
  have hBp : IsPGroup p B := IsPGroup.of_card (n := 1) (by rw [hBcard, pow_one])
  have hUB : B ∈ uniqueSet D.M := uc22p22r_mem_uniqueSet_of_sp D hp hsp hBM hBp hBne
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
  have hD₀M : A ⊔ B ⊔ D.T ≤ D.M := sup_le (sup_le hAM hBM) D.sylowM.le
  have hWM : ¬ W ≤ D.M := by
    intro hle
    exact (not_le_of_gt hYW) (le_kerM_of_normal hWH hWn hle)
  have hKle : (A ⊔ B ⊔ D.T) ⊔ W ≤ H := sup_le hD₀H hWH
  have hKnotM : ¬ (A ⊔ B ⊔ D.T) ⊔ W ≤ D.M := fun hle => hWM (le_sup_right.trans hle)
  have hHeq : (A ⊔ B ⊔ D.T) ⊔ W = H := hmin _ le_sup_left hKle hKnotM
  have hHMR : H ≤ (H ⊓ D.M) ⊔ W := by
    calc H = (A ⊔ B ⊔ D.T) ⊔ W := hHeq.symm
      _ ≤ (H ⊓ D.M) ⊔ W := sup_le_sup_right (le_inf hD₀H hD₀M) W
  have hA₁H : A ⊓ L ≤ H := (inf_le_left.trans (le_sup_left.trans le_sup_left)).trans hD₀H
  have hA₂H : A ⊓ conjSubgroup L x ≤ H :=
    (inf_le_left.trans (le_sup_left.trans le_sup_left)).trans hD₀H
  have hBH : B ≤ H := (le_sup_right.trans le_sup_left).trans hD₀H
  exact fun habW =>
    false_of_abelian_chief D hA₁card hA₂card hA₁₂ hinf hBcard5 hBn₁ hBn₂ hfpf
      hU₁ hU₂ hUB hA₁H hA₂H hBH hYW hWH hWn hminW hHMR habW

@[expose] def NonabComponentConfig (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
    (A₀ A B : Subgroup G),
    V₀ ≠ ⊥ → Ctx17_42 D V₀ V L X p n l C Dc Gamma →
    F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X →
    F08.Case8100FourR D ![L, conjSubgroup L x] p X →
    CFSG.ABGLocalTools.IsSylowOf r A X → Permutes A D.T → B ≤ D.M →
    Nat.card B = p → ⁅A, B⁆ = A → Permutes B D.T →
    centralizer (D.Z : Set G) ≤ D.M →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M → F08.R8101R D →
    ∀ N H R : Subgroup G, N ∈ calMOf (A ⊔ B ⊔ D.T) → N ≠ D.M →
      A ⊔ B ⊔ D.T ≤ H → H ≤ N → ¬ H ≤ D.M →
      (∀ H' : Subgroup G, A ⊔ B ⊔ D.T ≤ H' → H' ≤ H → ¬ H' ≤ D.M → H' = H) →
      kerM D.M H < R → R ≤ H → H ≤ normalizer (R : Set G) →
      (∀ W : Subgroup G, kerM D.M H ≤ W → W ≤ R → H ≤ normalizer (W : Set G) →
        W = kerM D.M H ∨ W = R) →
      ¬ ⁅R, R⁆ ≤ kerM D.M H →
      (∀ W : Subgroup G, kerM D.M H < W → W ≤ H → H ≤ normalizer (W : Set G) →
        (∀ W' : Subgroup G, kerM D.M H ≤ W' → W' ≤ W → H ≤ normalizer (W' : Set G) →
          W' = kerM D.M H ∨ W' = W) → ¬ ⁅W, W⁆ ≤ kerM D.M H) →
      ∃ (X' : Type) (_ : Group X') (_ : Finite X') (L' A₁ A₂ B' T ML : Subgroup X'),
        L'.Normal ∧ IsSimpleGroup L' ∧ ¬ IsMulCommutative L' ∧ CFSG.Open.IsKGroup L' ∧
        centralizer (L' : Set X') = ⊥ ∧
        Nat.card A₁ = 31 ∧ Nat.card A₂ = 31 ∧ A₁ ⊓ A₂ = ⊥ ∧
        A₁ ≤ centralizer (A₂ : Set X') ∧
        Nat.card B' = 5 ∧ B' ≤ normalizer (A₁ : Set X') ∧
        B' ≤ normalizer (A₂ : Set X') ∧
        ⁅A₁ ⊔ A₂, B'⁆ = A₁ ⊔ A₂ ∧
        (∀ D' : Subgroup X', D' ≤ A₁ ⊔ A₂ → Nat.card D' = 31 →
          B' ≤ normalizer (D' : Set X') → D' = A₁ ∨ D' = A₂) ∧
        IsPGroup 2 T ∧
        (((A₁ ⊔ A₂ : Subgroup X') : Set X') * (T : Set X') =
          (T : Set X') * (((A₁ ⊔ A₂ : Subgroup X') : Set X'))) ∧
        ((B' : Set X') * (T : Set X') = (T : Set X') * (B' : Set X')) ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L') L' ∧
        ML ≤ L' ∧ ML ≠ L' ∧ T ⊓ L' ≤ ML ∧
        (∀ C' : Subgroup X', IsMulCommutative C' → (A₁ ≤ C' ∨ A₂ ≤ C' ∨ B' ≤ C') →
          L' ⊓ normalizer (C' : Set X') ≤ ML) ∧
        (5 ∣ Nat.card L' →
          CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 (ML.subgroupOf L'))

theorem gap17_45_nonabChief_of_config (D : Data G)
    (V₀ V : Subgroup G) (hC : Gap17_45_NonabComponent)
    (hConf : NonabComponentConfig D V₀ V) :
    Gap17_45_NonabChief D V₀ V := by
  intro L X p n l r C Dc Gamma x A₀ A B hV₀ ctx h8100 hc4 hAsyl hAT hBM hBcard hAB hBT
    hcent hsp hR8101
  intro N H R hN hne hD₀H hHN hHM hmin hYR hRH hRn hminR hab
  have hF : ∀ W : Subgroup G, kerM D.M H < W → W ≤ H → H ≤ normalizer (W : Set G) →
      (∀ W' : Subgroup G, kerM D.M H ≤ W' → W' ≤ W → H ≤ normalizer (W' : Set G) →
        W' = kerM D.M H ∨ W' = W) → ¬ ⁅W, W⁆ ≤ kerM D.M H :=
    fun W hYW hWH hWn hminW =>
      no_abelian_minimal_above D hV₀ ctx h8100 hc4 hAsyl hAT hBM hBcard hAB hBT hsp hR8101
        hD₀H hmin hYW hWH hWn hminW
  obtain ⟨X', hX'G, hX'F, L', A₁, A₂, B', T, ML, hL'norm, hL'simple, hL'nonab, hL'K,
    hcent', hA₁card, hA₂card, hA₁₂, hA₁cent, hB'card, hB'n₁, hB'n₂, hAB', hlines, hT2,
    hAT', hBT', hTsyl, hMLle, hMLne, hTML, hLift, hStr⟩ :=
    hConf L X p n l r C Dc Gamma x A₀ A B hV₀ ctx h8100 hc4 hAsyl hAT hBM hBcard hAB hBT
      hcent hsp hR8101 N H R hN hne hD₀H hHN hHM hmin hYR hRH hRn hminR hab hF
  exact hC X' L' A₁ A₂ B' T ML hL'norm hL'simple hL'nonab hL'K hcent' hA₁card hA₂card hA₁₂
    hA₁cent hB'card hB'n₁ hB'n₂ hAB' hlines hT2 hAT' hBT' hTsyl hMLle hMLne hTML hLift hStr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
