module

import CFSG.Timmesfeld.Transvection.OddTranslations
import CFSG.Timmesfeld.Transvection.OddResiduePerp
import CFSG.Timmesfeld.Transvection.OddSpExclusion
import CFSG.Timmesfeld.Transvection.OddLocal
import CFSG.Timmesfeld.Transvection.OddSU3Torus
public import CFSG.Timmesfeld.Transvection.FrameResidue
public import CFSG.Timmesfeld.Transvection.OddSU3Chord
public import CFSG.Timmesfeld.Transvection.RankThreeA2Coords

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

section Certificates


theorem IsMaxFrame.mem_of_mem_map_heis_sup_of_conjSub_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) {M : Subgroup H} (hM : M ∈ frameResidue Δ P Q i)
    (hMl : M ∉ lineOf Δ (P i) (Q i)) {u : H}
    (hu : u ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
      (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
        shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k))
    (huP : conjSub (P i) u = P i) (huQ : conjSub (Q i) u = Q i) (huM : conjSub M u = M) :
    u ∈ P k :=
  IsMaxFrame.mem_of_mem_map_heis_of_conjSub_eq h hML hq hF hns hFn hcard hθr hθk hθt hθb hmem
    hik hM hMl
    (IsFrame.mem_map_heis_of_mem_sup_of_conjSub_eq h hML hq hF.toIsFrame hFn hcard hθr hθt hθb
      hik hu huP huQ)
    huM

theorem IsMaxFrame.card_map_heis_sup_eq (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q k)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθk : Odd (Nat.card θ.ker)) (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k) :
    Nat.card ↥((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) = (2 ^ n) ^ 7 := by
  have hqk : Nat.card (P k) = 2 ^ n := hcard (P k) (hF.memP k)
  have hB := card_map_heis_of_odd hFn hθk
  have hY₁ : Nat.card ↥(shortRootGroup Δ (P k) (Q k) (Q i) (P i)) = Nat.card (P k) ^ 2 := by
    rw [shortRootGroup_swap_pairs (Q i) (P i) (P k) (Q k)]
    exact IsMaxFrame.card_shortRootGroup_of_not_isSmallFrame h hML hq hF hik hns
  have hY₂ : Nat.card ↥(shortRootGroup Δ (P k) (Q k) (P i) (Q i)) = Nat.card (P k) ^ 2 := by
    rw [shortRootGroup_swap_pairs (P i) (Q i) (P k) (Q k)]
    exact IsMaxFrame.card_shortRootGroup_flip_of_not_isSmallFrame h hML hq hF hik hns
  have hmul :=
    IsFrame.card_map_heis_sup_mul h hML hq hF.toIsFrame hFn hcard hθr hθt hθb hik
  have hsup := IsFrame.card_sup_shortRootGroup h hq hF.toIsFrame hik
  rw [hsup, hY₁, hY₂, hqk, hB] at hmul
  refine Nat.eq_of_mul_eq_mul_right (m := 2 ^ n) (pow_pos (by norm_num) n) ?_
  rw [hmul]
  ring

end Certificates

end CFSG.Timmesfeld.Transvection
