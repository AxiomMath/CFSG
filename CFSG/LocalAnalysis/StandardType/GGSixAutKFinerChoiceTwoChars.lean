module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} [NeZero n] {L : Type} [Field L]
  [Algebra K L] [Module.Finite K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E)

@[expose] def comb2 {s : ℕ} (t₁ t₂ : Fin s → ZMod 3) (a : ZMod 3 × ZMod 3) : Fin s → ZMod 3 :=
  a.1 • t₁ + a.2 • t₂

theorem comb2_apply {s : ℕ} (t₁ t₂ : Fin s → ZMod 3) (a : ZMod 3 × ZMod 3) (i : Fin s) :
    comb2 t₁ t₂ a i = dot3 a (t₁ i, t₂ i) := by
  simp [comb2, dot3]

namespace SpFrame

theorem chars_of_quasisimple (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (hL : finrank K L = 2) (hs : 4 ≤ F.s) (t₁ t₂ : Fin F.s → ZMod 3)
    (hind : ∀ a : ZMod 3 × ZMod 3, a ≠ 0 → comb2 t₁ t₂ a ≠ 0)
    {J' : Subgroup (StatedSp n K)} (hJq : CFSG.IsQuasisimple J')
    (hJc : ∀ a, J' ≤ Subgroup.centralizer {F.tor (comb2 t₁ t₂ a)})
    (hcount : ∀ U : Finset (Fin F.s),
      (∀ i ∈ U, ∀ g ∈ J', F.tor (Pi.single i 1) * g = g * F.tor (Pi.single i 1)) →
        3 ^ U.card ≤ 27) :
    (∃ i j, i ≠ j ∧ ∃ b : Bool, ∀ a, comb2 t₁ t₂ a i = sgnZ b (comb2 t₁ t₂ a j)) ∧
      (F.s = 4 → ∃ i j, i ≠ j ∧ ∀ a, comb2 t₁ t₂ a i = 0 ∧ comb2 t₁ t₂ a j = 0) := by
  classical
  set c : Fin F.s → ZMod 3 × ZMod 3 := fun i => (t₁ i, t₂ i) with hc
  have hcomb : ∀ a i, comb2 t₁ t₂ a i = dot3 a (c i) := fun a i => comb2_apply t₁ t₂ a i
  have hJp : ⁅J', J'⁆ = J' := LayerFacts.ggCommutator_eq_of_isQuasisimple hJq
  have hsupp : ∀ a, (F.suppSet (comb2 t₁ t₂ a)).card = wt3 c a := fun a => by
    rw [suppSet, wt3]
    simp only [hcomb]
  have hA : (lowSupp c).card ≤ 3 := by
    have h27 := hcount (lowSupp c) fun i hi g hg => by
      simp only [lowSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨a, ha, hw⟩ := hi
      have hle := F.le_spFixedFactor hK hζo hL (c := comb2 t₁ t₂ a) (by rw [hsupp]; exact hw)
        hJp (hJc a)
      have hmem := F.tor_mem_spSupported hK hζo (comb2 t₁ t₂ a) (Pi.single i 1)
        (fun l hl => by
          by_cases hli : l = i
          · subst hli
            rw [hcomb] at hl
            exact absurd hl ha
          · exact Pi.single_eq_of_ne hli 1) (O := {phi3 K}) rfl
      exact (commute_of_mem_spFixedFactor hK (F.tor_pow_three hζo.pow_eq_one _)
        (fun h => phi3_ne_X_sub_one (Set.mem_singleton_iff.mp h).symm) (hle hg) hmem).symm
    by_contra h4
    have : 3 ^ 4 ≤ 3 ^ (lowSupp c).card := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hB : F.s = 4 → ∀ a, wt3 c a ≠ 3 := by
    intro h4 a hw
    set κ := comb2 t₁ t₂ a with hκ
    have hκ0 : κ ≠ 0 := by
      intro h0
      have : (F.suppSet κ).card = 0 := by
        rw [h0, Finset.card_eq_zero, suppSet, Finset.filter_eq_empty_iff]
        intro l _
        simp
      rw [hsupp] at this
      omega
    have hle := F.le_spFixedFactor hK hζo hL (c := κ) (by rw [hsupp, hw]) hJp (hJc a)
    have hsplit : (F.zeroSet κ).card + (F.suppSet κ).card = F.s := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin F.s)))
        (fun l => κ l = 0)
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact h
    have hd : spFixedDim (F.tor κ) = 2 := by
      rw [F.spFixedDim_tor hζo hL, show (F.zeroSet κ).card = 1 by rw [hsupp] at hsplit; omega]
    have hcard := card_spFixedFactor_of_dim_two (F.blocks_tor hK hζo hκ0) hd
    rw [hK] at hcard
    have hsolv : Group.IsSolvable ↥(spFixedFactor (F.tor κ)) :=
      isSolvable_of_card_primeFactors_le_two
        (by rw [hcard]; exact SevSpNs.card_primeFactors_six)
    exact ClNonsplit.not_isQuasisimple_of_le hsolv hle hJq
  obtain ⟨h1, h2⟩ := chars_rel hs (fun a ha => by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (hind a ha)
      exact ⟨i, by rw [← hcomb]; exact hi⟩) hA hB
  refine ⟨?_, fun h4 => ?_⟩
  · obtain ⟨i, j, hij, h⟩ := h1
    rcases h with h | h
    · exact ⟨i, j, hij, false, fun a => by rw [hcomb, hcomb, h, sgnZ_false]⟩
    · refine ⟨i, j, hij, true, fun a => ?_⟩
      rw [hcomb, hcomb, h, sgnZ_true]
      simp [dot3]
      ring
  · obtain ⟨i, j, hij, hi, hj⟩ := h2 h4
    exact ⟨i, j, hij, fun a => ⟨by rw [hcomb, hi, dot3_zero_right],
      by rw [hcomb, hj, dot3_zero_right]⟩⟩

end SpFrame

end ChoiceTwo

end CFSG.StandardType
