module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeJ2Local17
public import CFSG.Quasithin.Background.RonanE114HeMain
public import CFSG.LocalAnalysis.WeakClosure81.InFSqPrimeTwoGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

@[expose] def K_HeOuterParabolics : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    CFSG.Open.IsQuasisimple ↥K → Odd (Nat.card (Subgroup.center ↥K)) →
    IsSpor ↥K .He → K ≠ ⊤ →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∃ H₁ H₂ H₃ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ S ≤ H₃ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
            CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ ∧
              H₁ ⊔ H₂ ⊔ H₃ = ⊤

open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl) in
open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB CFSG.Quasithin.RonanE114.HeOver in
theorem heParabolics_of_lat {Γ : Type} [Group Γ] [Finite Γ] (hl : CFSG.Quasithin.ModH.HeLat Γ)
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [hK : K.Normal] (hKtop : K = ⊤) (e : ↥K ≃* Γ)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ H₁ H₂ H₃ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ S ≤ H₃ ∧
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ ∧
            H₁ ⊔ H₂ ⊔ H₃ = ⊤ := by
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  obtain ⟨e', he'⟩ := exists_equiv_sylow e hSK hl.S_sylow
  have hSinf : S ⊓ K = S := inf_eq_left.mpr (hKtop ▸ le_top)
  have hKidx : ∃ a : ℕ, K.index = 2 ^ a := ⟨0, by rw [hKtop, Subgroup.index_top]; rfl⟩
  have hcardS : Nat.card S = 1024 := by
    have h1 : Nat.card ↥(S ⊓ K) = Nat.card hl.S := by
      rw [← he', Subgroup.card_map_of_injective e'.injective]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
    rw [hSinf] at h1
    rw [h1, ← Y0_eq_S hl, card_Y_idx hl (by norm_num)]
    rfl
  have hSH : ∀ j, S ≤ ((hl.Y j).map e'.symm.toMonoidHom).map K.subtype := fun j => by
    have h := (le_pull_iff e' inf_le_right).mpr (he' ▸ hl.S_le_Y j)
    rwa [hSinf] at h
  have hF : ∀ j < 11, heIdx j = 3 →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1
        (((hl.Y j).map e'.symm.toMonoidHom).map K.subtype) := by
    intro j hj h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc : Nat.card ↥(((hl.Y j).map e'.symm.toMonoidHom).map K.subtype) =
        3 ^ 1 * Nat.card S := by
      rw [Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective e'.symm.injective, card_Y_idx hl hj, h3, hcardS]
      norm_num
    obtain ⟨A, -, -, hAc, -, hAS, hAP⟩ :=
      exists_permutes_of_overgroup hK hKidx hS.2.1 (hSH j) (p := 3) (n := 1) (by norm_num) hc
    rw [← hAS]
    exact CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group A S 3
      Nat.prime_three (by decide) (by rw [hAc]; norm_num) hS.2.1 hAP
  have hgen : hl.Y 1 ⊔ hl.Y 8 ⊔ hl.Y 10 = ⊤ := by
    have hSle : hl.S ≤ hl.Y 1 ⊔ hl.Y 8 ⊔ hl.Y 10 :=
      (hl.S_le_Y 1).trans (le_sup_left.trans le_sup_left)
    rcases hl.complete _ hSle with ⟨j, hj, hjeq⟩ | htop
    · exfalso
      have h1 : hl.Y 1 ≤ hl.Y j := by
        rw [← hjeq]; exact le_sup_left.trans le_sup_left
      have h8 : hl.Y 8 ≤ hl.Y j := by
        rw [← hjeq]; exact le_sup_right.trans le_sup_left
      have h10 : hl.Y 10 ≤ hl.Y j := by
        rw [← hjeq]; exact le_sup_right
      have m1 := (hl.le_iff (by norm_num) hj).1 h1
      have m8 := (hl.le_iff (by norm_num) hj).1 h8
      have m10 := (hl.le_iff (by norm_num) hj).1 h10
      revert m1 m8 m10
      interval_cases j <;> decide
    · exact htop
  have hjoin : ((hl.Y 1).map e'.symm.toMonoidHom).map K.subtype ⊔
      ((hl.Y 8).map e'.symm.toMonoidHom).map K.subtype ⊔
        ((hl.Y 10).map e'.symm.toMonoidHom).map K.subtype = ⊤ := by
    rw [← pull_sup, ← pull_sup, hgen, pull_top, hKtop]
  exact ⟨_, _, _, hSH 1, hSH 8, hSH 10, hF 1 (by norm_num) rfl, hF 8 (by norm_num) rfl,
    hF 10 (by norm_num) rfl, hjoin⟩

theorem k_HeParabolics_of_outer
    (hOut : K_HeOuterParabolics) : K_HeParabolics := by
  intro Y _ _ K hKN hq hodd hHe hcent hidx S hS
  by_cases hKtop : K = ⊤
  · have := hKN
    obtain ⟨e₀⟩ := hHe
    exact heParabolics_of_lat CFSG.Quasithin.RonanE114.HeOver.heLatNative hKtop
      (e₀.trans CFSG.Sporadic.He.heEquivJ) hS
  · exact hOut Y K hKN hq hodd hHe hKtop hcent hidx S hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
