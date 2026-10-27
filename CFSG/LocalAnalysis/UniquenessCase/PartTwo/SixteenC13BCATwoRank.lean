module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c13bcA_card_internalDirect {A : Type*} [Group A] {K L X : Subgroup A}
    (h : IsInternalDirect K L X) : Nat.card ↥X = Nat.card ↥K * Nat.card ↥L := by
  have hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k := by
    intro k hk l hl
    have hkcent : k ∈ Subgroup.centralizer (L : Set A) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h.1) hk
    exact (Subgroup.mem_centralizer_iff.1 hkcent l hl).symm
  have hcomm : ∀ (k : ↥K) (l : ↥L), Commute (K.subtype k) (L.subtype l) :=
    fun k l => hKL k k.2 l l.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod K.subtype L.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨K.subtype_injective, L.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 h.2.1
  have hrange : (MonoidHom.noncommCoprod K.subtype L.subtype hcomm).range = X := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact h.2.2
  have hc := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hrange, Nat.card_prod] at hc
  exact hc.symm

theorem s16c13bcA_card_isLn_three {X : Type} [Group X] (h : IsLn X 3 1) : Nat.card X = 168 := by
  have hc := CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two h
  rw [hc]
  decide

theorem s16c13bcA_false_of_three_le_pRank {A : Type} [Group A] [Finite A] {K L X : Subgroup A}
    (hdir : IsInternalDirect K L X) (hK : Nat.card ↥K = 6)
    (hL : Nat.card ↥L = 120 ∨ Nat.card ↥L = 168) (h3 : 3 ≤ CFSG.Open.pRank 3 X) : False := by
  obtain ⟨E, -, hE⟩ := exists_isElemAbelian_subgroupOf_of_le_pRank Nat.prime_three h3
  have h1 : Nat.card ↥E ∣ Nat.card ↥X := Subgroup.card_subgroup_dvd_card E
  rw [s16c13bcA_card_internalDirect hdir, hK, hE] at h1
  rcases hL with hL | hL
  · rw [hL] at h1
    revert h1
    decide
  · rw [hL] at h1
    revert h1
    decide

theorem s16c13bcA_sumOfNat_of_two {W : Type} [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (h₀ : N H J₀ ⊥) (h₁ : N H J₁ ⊥) (hi : J₀ ⊓ J₁ = ⊥)
    (hj : J₀ ⊔ J₁ = ⊤) : SumOfNat N H ⊤ ⊥ 2 := by
  let I : Fin 2 → Subgroup W := ![J₀, J₁]
  have hrest : ∀ i j : Fin 2, i ≠ j → (⨆ (k : Fin 2) (_ : k ≠ i), I k) = I j := by
    intro i j hij
    refine le_antisymm (iSup₂_le fun k hk => ?_) (le_iSup₂ (f := fun k (_ : k ≠ i) => I k) j
      (Ne.symm hij))
    have : k = j := by omega
    rw [this]
  refine ⟨I, fun i => bot_le, ?_, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    constructor
    · rw [hrest 0 1 (by decide), bot_sup_eq]
      exact hi.le
    · rw [hrest 1 0 (by decide), bot_sup_eq]
      exact (inf_comm J₁ J₀ ▸ hi).le
  · have hall : (⨆ i, I i) = J₀ ⊔ J₁ := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    rw [hall, bot_sup_eq]
    exact hj
  · rw [Fin.forall_fin_two]
    exact ⟨h₀, h₁⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
