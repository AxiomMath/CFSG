module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def NoExcess (ρ : Representation (ZMod 2) G V) (X : Subgroup G)
    (N : Submodule (ZMod 2) V) : Prop :=
  Nat.card X * Nat.card (fixOn ρ X N) ≤ Nat.card N * Nat.card (cenOn ρ X N)

variable {ρ : Representation (ZMod 2) G V}

theorem fixSub_eq_sup_of_isCompl {X : Subgroup G} {N W : Submodule (ZMod 2) V}
    (hNW : IsCompl N W) (hN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X N) (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X W) :
    fixSub ρ X = fixOn ρ X N ⊔ fixOn ρ X W := by
  refine le_antisymm (fun v hv => ?_) (sup_le inf_le_right inf_le_right)
  have hv' : v ∈ N ⊔ W := hNW.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨n, hn, w, hw, rfl⟩ := Submodule.mem_sup.1 hv'
  have key : ∀ x ∈ X, ρ x n = n ∧ ρ x w = w := fun x hx => by
    have h1 : ρ x n - n ∈ N := sub_mem (hN x hx n hn) hn
    have h2 : ρ x w - w ∈ W := sub_mem (hW x hx w hw) hw
    have hsum : ρ x n - n + (ρ x w - w) = 0 := by
      have h := mem_fixSub.1 hv x hx
      rw [map_add] at h
      calc ρ x n - n + (ρ x w - w) = ρ x n + ρ x w - (n + w) := by abel
        _ = 0 := by rw [h, sub_self]
    have h3 : ρ x n - n = -(ρ x w - w) := eq_neg_of_add_eq_zero_left hsum
    have h0 : ρ x n - n = 0 :=
      (Submodule.disjoint_def.1 hNW.disjoint) _ h1 (h3 ▸ neg_mem h2)
    have h0' : ρ x w - w = 0 := by rw [← neg_eq_zero, ← h3, h0]
    exact ⟨sub_eq_zero.1 h0, sub_eq_zero.1 h0'⟩
  exact Submodule.add_mem_sup (mem_fixOn.2 ⟨hn, fun x hx => (key x hx).1⟩)
    (mem_fixOn.2 ⟨hw, fun x hx => (key x hx).2⟩)

theorem card_fixSub_eq_mul_of_isCompl [Finite V] {X : Subgroup G} {N W : Submodule (ZMod 2) V}
    (hNW : IsCompl N W) (hN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X N) (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X W) :
    Nat.card (fixSub ρ X) = Nat.card (fixOn ρ X N) * Nat.card (fixOn ρ X W) := by
  have h := card_inf_mul_card_sup (fixOn ρ X N) (fixOn ρ X W)
  have hbot : fixOn ρ X N ⊓ fixOn ρ X W = ⊥ := eq_bot_iff.2 fun v hv =>
    (Submodule.disjoint_def.1 hNW.disjoint) v (mem_fixOn.1 (Submodule.mem_inf.1 hv).1).1
      (mem_fixOn.1 (Submodule.mem_inf.1 hv).2).1
  rw [hbot, ← fixSub_eq_sup_of_isCompl hNW hN hW, card_eq_two_pow_finrank ⊥, finrank_bot,
    pow_zero, one_mul] at h
  exact h

theorem strip_one [Finite G] [Finite V] {A : Subgroup G} {N W : Submodule (ZMod 2) V}
    (hA : IsBestOffender ρ A) (hNW : IsCompl N W) (hN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ A N)
    (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ A W) (hE : NoExcess ρ A N) :
    IsBestOffender ρ (cenOn ρ A N) ∧ fixOn ρ (cenOn ρ A N) W ≤ fixSub ρ A := by
  set A' := cenOn ρ A N with hA'def
  have hA'A : A' ≤ A := fun x hx => hx.1
  have hfixN : fixOn ρ A' N = N := inf_eq_left.2 fun n hn => mem_fixSub.2 fun x hx => hx.2 n hn
  have hsA := card_fixSub_eq_mul_of_isCompl hNW hN hW
  have hsA' : Nat.card (fixSub ρ A') = Nat.card N * Nat.card (fixOn ρ A' W) := by
    rw [card_fixSub_eq_mul_of_isCompl hNW (fun x hx => hN x (hA'A hx))
      (fun x hx => hW x (hA'A hx)), hfixN]
  have hmono : fixOn ρ A W ≤ fixOn ρ A' W := inf_le_inf_left W (fixSub_antitone hA'A)
  have hcmono : Nat.card (fixOn ρ A W) ≤ Nat.card (fixOn ρ A' W) := by
    rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank]
    exact Nat.pow_le_pow_right (by norm_num) (Submodule.finrank_mono hmono)
  have hE' : Nat.card A * Nat.card (fixOn ρ A N) ≤ Nat.card N * Nat.card A' := hE
  have hchain : Nat.card A * Nat.card (fixSub ρ A) ≤
      Nat.card A' * Nat.card N * Nat.card (fixOn ρ A W) := by
    rw [hsA, ← mul_assoc, mul_comm (Nat.card A') (Nat.card N)]
    exact Nat.mul_le_mul_right _ hE'
  have hfix' : Nat.card A' * Nat.card (fixSub ρ A') =
      Nat.card A' * Nat.card N * Nat.card (fixOn ρ A' W) := by
    rw [hsA', mul_assoc]
  refine ⟨fun B hB => ?_, ?_⟩
  · calc Nat.card B * Nat.card (fixSub ρ B) ≤ Nat.card A * Nat.card (fixSub ρ A) :=
          hA B (hB.trans hA'A)
      _ ≤ Nat.card A' * Nat.card N * Nat.card (fixOn ρ A W) := hchain
      _ ≤ Nat.card A' * Nat.card N * Nat.card (fixOn ρ A' W) := Nat.mul_le_mul_left _ hcmono
      _ = Nat.card A' * Nat.card (fixSub ρ A') := hfix'.symm
  · have h1 : Nat.card A' * Nat.card N * Nat.card (fixOn ρ A' W) ≤
        Nat.card A' * Nat.card N * Nat.card (fixOn ρ A W) :=
      hfix' ▸ (hA A' hA'A).trans hchain
    have h2 := Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos Nat.card_pos Nat.card_pos)
    rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank] at h2
    have heq : fixOn ρ A W = fixOn ρ A' W :=
      Submodule.eq_of_le_of_finrank_le hmono ((Nat.pow_le_pow_iff_right (by norm_num)).1 h2)
    rw [← heq]
    exact inf_le_right

theorem le_fixSub_of_strip [Finite G] [Finite V] {ι : Type} (N W : ι → Submodule (ZMod 2) V)
    {T : Submodule (ZMod 2) V} (J : Finset ι) :
    ∀ {A : Subgroup G}, IsBestOffender ρ A →
      (∀ k ∈ J, IsCompl (N k) (W k) ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ A (N k) ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ A (W k) ∧
        T ≤ W k ∧ ∀ X ≤ A, NoExcess ρ X (N k)) →
      (∀ b ∈ A, (∀ k ∈ J, ∀ n ∈ N k, ρ b n = n) → ∀ t ∈ T, ρ b t = t) → T ≤ fixSub ρ A := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro A _ _ hT t ht
    exact mem_fixSub.2 fun b hb => hT b hb (fun k hk => absurd hk (Finset.notMem_empty k)) t ht
  | @insert k J hk ih =>
    intro A hA hJ hT
    obtain ⟨hNW, hN, hW, hTW, hE⟩ := hJ k (Finset.mem_insert_self k J)
    obtain ⟨hA', hle⟩ := strip_one hA hNW hN hW (hE A le_rfl)
    have hA'A : cenOn ρ A (N k) ≤ A := fun x hx => hx.1
    have hT' : T ≤ fixSub ρ (cenOn ρ A (N k)) := by
      refine ih hA' (fun l hl => ?_) (fun b hb hbN => hT b hb.1 fun l hl => ?_)
      · obtain ⟨h1, h2, h3, h4, h5⟩ := hJ l (Finset.mem_insert_of_mem hl)
        exact ⟨h1, fun x hx => h2 x (hA'A hx), fun x hx => h3 x (hA'A hx), h4,
          fun X hX => h5 X (hX.trans hA'A)⟩
      · rcases Finset.mem_insert.1 hl with rfl | hl
        · exact hb.2
        · exact hbN l hl
    exact (le_inf hTW hT').trans hle

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
