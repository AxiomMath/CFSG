module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2SwapOrb
public import CFSG.Quasithin.EmptyFaithful.S151S4D

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

set_option linter.unusedSectionVars false

section Min

variable {G : Type} [Group G] [Finite G]

theorem isMinParabolic_of_invariant {L S D : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hS2 : IsPGroup 2 ↥S)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (hDL : D ≤ L) (hSD : S ⊓ L ≤ D) (hDne : D ≠ L)
    (hSDn : S ≤ Subgroup.normalizer (D : Set G))
    (hmax : ∀ K : Subgroup G, S ≤ Subgroup.normalizer (K : Set G) → S ⊓ L ≤ K → K ≤ L →
      K ≠ L → K ≤ D)
    (hnn : ¬ L ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) :
    IsMinParabolicOf (L ⊔ S) (L ⊔ S) := by
  have hSH : IsSylowTwoOf S (L ⊔ S) := S151S4.sylow_sup_of_normalizes hSN hS2 hsyl
  have hX_le : D ⊔ S ≤ L ⊔ S := sup_le (hDL.trans le_sup_left) le_sup_right
  have hXne : D ⊔ S ≠ L ⊔ S := by
    intro hXeq
    apply hDne
    refine le_antisymm hDL (fun l hl => ?_)
    have hl' : l ∈ D ⊔ S := hXeq ▸ Subgroup.mem_sup_left hl
    obtain ⟨b, hb, s, hs, hbs⟩ := zb_mem_sup hSDn hl'
    have hsL : s ∈ L := by
      have : s = b⁻¹ * l := by rw [hbs]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (hDL hb)) hl
    have hsD : s ∈ D := hSD ⟨hs, hsL⟩
    rw [hbs]
    exact D.mul_mem hb hsD
  have hXH : D ⊔ S < L ⊔ S := lt_of_le_of_ne hX_le hXne
  have hmaxX : ∀ Y : Subgroup G, S ≤ Y → Y < L ⊔ S → Y ≤ D ⊔ S := by
    intro Y hSY hYH
    have hY1 : Y ⊓ L ≤ D := by
      refine hmax (Y ⊓ L) (fun s hs => ?_) (le_inf (inf_le_left.trans hSY) inf_le_right)
        inf_le_right ?_
      · exact zb_mem_normalizer_inf (Subgroup.le_normalizer (hSY hs)) (hSN hs)
      · intro hYL
        have hLY : L ≤ Y := by
          intro x hx
          have hx' : x ∈ Y ⊓ L := by
            rw [hYL]
            exact hx
          exact hx'.1
        exact absurd (sup_le hLY hSY) (not_le_of_gt hYH)
    intro y hy
    obtain ⟨l, hl, s, hs, rfl⟩ := zb_mem_sup hSN (hYH.le hy)
    have hlY : l ∈ Y := by
      have := Y.mul_mem hy (Y.inv_mem (hSY hs))
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hY1 ⟨hlY, hl⟩)) (Subgroup.mem_sup_right hs)
  have hnn' : ¬ (L ⊔ S) ≤ Subgroup.normalizer (S : Set G) := by
    intro hH
    apply hnn
    intro l hl
    exact zb_mem_normalizer_inf (hH (Subgroup.mem_sup_left hl)) (Subgroup.le_normalizer hl)
  have hmaxX' : IsMaxSubgroupIn (L ⊔ S) (D ⊔ S) := by
    refine ⟨hXH, fun K hXK hKH => ?_⟩
    by_contra hne
    exact absurd (hmaxX K (le_sup_right.trans hXK.le) (lt_of_le_of_ne hKH hne)) (not_le_of_gt hXK)
  have huniq : IsUniqueMaxOver (L ⊔ S) S (D ⊔ S) := by
    unfold IsUniqueMaxOver
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨hmaxX', le_sup_right⟩, fun N hN => ?_⟩
    have hNX : N ≤ D ⊔ S := hmaxX N hN.2 hN.1.1
    by_contra hne
    exact absurd (hN.1.2 _ (lt_of_le_of_ne hNX hne) hXH.le) (ne_of_lt hXH)
  exact (minParabolic_iff.mp ⟨hSH, hnn', huniq⟩).1

end Min

section Swap

variable {G : Type} [Group G] [Finite G] {Y : Type} [Group Y] [Finite Y]
  {L SL : Subgroup G} {ρ : ↥L →* Y} {U : Subgroup Y} {P : Fin 2 → Subgroup Y}

theorem isMinParabolic_of_swap (h : RkData L SL ρ U P)
    (hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ CFSG.Open.pCore 2 ↥L = ⊤)
    {S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hS2 : IsPGroup 2 ↥S)
    (hSL : SL = S ⊓ L) {s₀ : G} (hs₀ : s₀ ∈ S)
    (hsw : B6.conjSub s₀ (parUp L ρ (P 0)) = parUp L ρ (P 1)) :
    IsMinParabolicOf (L ⊔ S) (L ⊔ S) := by
  have hQ : pCoreOf 2 L ≤ SL :=
    pCoreOf_two_le_of_sylowIn h.sylow.1 h.sylow.2.1 h.sylow.2.2
  have hSSL : ∀ t ∈ S, t ∈ Subgroup.normalizer (SL : Set G) := fun t ht => by
    rw [hSL]
    exact zb_mem_normalizer_inf (Subgroup.le_normalizer ht) (hSN ht)
  have hsw' : B6.conjSub s₀ (parUp L ρ (P 1)) = parUp L ρ (P 0) := by
    rcases swap_or_fix h hperf hQ (hSN hs₀) (hSSL s₀ hs₀) with ⟨h0, -⟩ | ⟨-, h1⟩
    · exact absurd (h0.symm.trans hsw) (parUp_zero_ne_one h)
    · exact h1
  refine isMinParabolic_of_invariant (D := parUp L ρ (P 0) ⊓ parUp L ρ (P 1)) hSN hS2
    (hSL ▸ h.sylow) (inf_le_left.trans (parUp_le _)) ?_ ?_ ?_ ?_ ?_
  · exact hSL ▸ le_inf (sl_le_parUp h 0) (sl_le_parUp h 1)
  · intro hD
    exact parUp_ne_top h 0 (le_antisymm (parUp_le _) (hD.symm.le.trans inf_le_left))
  · intro t ht
    apply mem_normalizer_of_conjSub_eq
    rw [OrderIso.map_inf]
    rcases swap_or_fix h hperf hQ (hSN ht) (hSSL t ht) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0, h1]
    · rw [h0, h1, inf_comm]
  · intro K hK hSK hKL hne
    obtain ⟨j, hj⟩ := exists_le_parUp h hperf hQ hKL (by rw [hSL]; exact hSK) hne
    have hKc : B6.conjSub s₀ K = K := B6.conjSub_eq_self (hK hs₀)
    have hjc : K ≤ B6.conjSub s₀ (parUp L ρ (P j)) := hKc ▸ (B6.conjSub s₀).monotone hj
    have hfin : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    rcases hfin j with rfl | rfl
    · exact le_inf hj (hsw ▸ hjc)
    · exact le_inf (hsw' ▸ hjc) hj
  · intro hnn
    have h1 : L ≤ parUp L ρ (P 0) := by
      intro x hx
      exact inf_normalizer_le_parUp h 0 ⟨hx, by rw [hSL]; exact hnn hx⟩
    exact parUp_ne_top h 0 (le_antisymm (parUp_le _) h1)

end Swap

end CFSG.Quasithin.Rk2
