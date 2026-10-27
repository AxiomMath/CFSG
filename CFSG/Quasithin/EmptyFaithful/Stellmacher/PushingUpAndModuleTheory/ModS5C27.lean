module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassificationBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Base

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ}

theorem commW_mono_left (M : Model n) {B B' : Subgroup (Perm (Fin n))} (h : B ≤ B')
    (U : Subgroup M.W) : commW M B U ≤ commW M B' U := by
  unfold commW
  refine Subgroup.closure_mono ?_
  rintro _ ⟨b, hb, u, hu, rfl⟩
  exact ⟨b, h hb, u, hu, rfl⟩

theorem commW_mono_right (M : Model n) (B : Subgroup (Perm (Fin n))) {U U' : Subgroup M.W}
    (h : U ≤ U') : commW M B U ≤ commW M B U' := by
  unfold commW
  refine Subgroup.closure_mono ?_
  rintro _ ⟨b, hb, u, hu, rfl⟩
  exact ⟨b, hb, u, h hu, rfl⟩

theorem commW_eq_bot_iff (M : Model n) (B : Subgroup (Perm (Fin n))) (U : Subgroup M.W) :
    commW M B U = ⊥ ↔ ∀ b ∈ B, ∀ u ∈ U, M.act b u = u := by
  constructor
  · intro h b hb u hu
    have : M.act b u * u⁻¹ ∈ commW M B U := Subgroup.subset_closure ⟨b, hb, u, hu, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact mul_inv_eq_one.mp this
  · intro h
    rw [eq_bot_iff]
    unfold commW
    rw [Subgroup.closure_le]
    rintro _ ⟨b, hb, u, hu, rfl⟩
    rw [h b hb u hu, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem odd_orderOf_threeCyc012 : Odd (orderOf threeCyc012) :=
  Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (by unfold threeCyc012; decide +kernel))

theorem odd_orderOf_threeCyc234 : Odd (orderOf threeCyc234) :=
  Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (by unfold threeCyc234; decide +kernel))

theorem threeCyc012_mem_alt : threeCyc012 ∈ alternatingGroup (Fin 5) :=
  Perm.mem_alternatingGroup.mpr (by unfold threeCyc012; decide +kernel)

theorem threeCyc234_mem_alt : threeCyc234 ∈ alternatingGroup (Fin 5) :=
  Perm.mem_alternatingGroup.mpr (by unfold threeCyc234; decide +kernel)

theorem idx_orth_threeCyc012 : idx orth threeCyc012 = 4 := by
  rw [idx_orth]
  have h1 : threeCyc012 ≠ 1 := by unfold threeCyc012; decide +kernel
  have h2 : threeCyc012 ^ 2 ≠ 1 := by unfold threeCyc012; decide +kernel
  have h3 : threeCyc012 ^ 3 = 1 := by unfold threeCyc012; decide +kernel
  simp only [h1, h2, h3, ↓reduceIte]

theorem idx_orth_threeCyc234 : idx orth threeCyc234 = 4 := by
  rw [idx_orth]
  have h1 : threeCyc234 ≠ 1 := by unfold threeCyc234; decide +kernel
  have h2 : threeCyc234 ^ 2 ≠ 1 := by unfold threeCyc234; decide +kernel
  have h3 : threeCyc234 ^ 3 = 1 := by unfold threeCyc234; decide +kernel
  simp only [h1, h2, h3, ↓reduceIte]

theorem fixW_orth_alt5 : fixW orth (alternatingGroup (Fin 5)) = ⊥ := by
  have hinv := isInvSub_fixW_of_normal orth (alternatingGroup.normal (α := Fin 5))
  rcases irreducible_orth _ (fun σ y hy => hinv σ (Subgroup.mem_top σ) y hy) with h | h
  · exact h
  · exfalso
    have h1 : fixW orth (Subgroup.zpowers threeCyc012) = ⊤ := by
      rw [eq_top_iff, ← h]
      exact fixW_antitone orth (Subgroup.zpowers_le.mpr threeCyc012_mem_alt)
    have h2 := idx_orth_threeCyc012
    unfold idx at h2
    rw [h1, Subgroup.index_top] at h2
    omega

private theorem card_orth_restrict {E : Model 5} {Z : Subgroup E.W} (hZ : IsInvSub E ⊤ Z)
    (e : (E.restrict Z hZ).Iso orth) : Nat.card Z = 16 := by
  have h := e.card_eq
  rw [card_orth] at h
  exact h

private theorem fixW_restrict_alt_eq_bot {E : Model 5} {Z : Subgroup E.W} (hZ : IsInvSub E ⊤ Z)
    (e : (E.restrict Z hZ).Iso orth) :
    fixW (E.restrict Z hZ) (alternatingGroup (Fin 5)) = ⊥ := by
  have h := e.fixW_eq (alternatingGroup (Fin 5))
  rw [fixW_orth_alt5] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.toMulEquiv.injective).mp h.symm

private theorem idx_le_four {E : Model 5} {Z : Subgroup E.W} (hZ : IsInvSub E ⊤ Z)
    (e : (E.restrict Z hZ).Iso orth) (hEZ : commW E (alternatingGroup (Fin 5)) ⊤ ≤ Z)
    {t : Perm (Fin 5)} (ht : t ∈ alternatingGroup (Fin 5)) (hodd : Odd (orderOf t))
    (h4 : idx orth t = 4) : idx E t ≤ 4 := by
  have h1 : commW E (Subgroup.zpowers t) ⊤ ≤ Z :=
    le_trans (commW_mono_left E (Subgroup.zpowers_le.mpr ht) ⊤) hEZ
  have h2 : Nat.card (commW E (Subgroup.zpowers t) ⊤) ≤ Nat.card (commW E (Subgroup.zpowers t) Z) := by
    apply Subgroup.card_le_of_le
    calc commW E (Subgroup.zpowers t) ⊤
        = commW E (Subgroup.zpowers t) (commW E (Subgroup.zpowers t) ⊤) :=
          (bf3_commW_commW E hodd).symm
      _ ≤ commW E (Subgroup.zpowers t) Z := commW_mono_right E _ h1
  have h3 := idx_restrict_eq_card_commW E Z hZ t
  rw [← e.idx_eq, h4] at h3
  unfold idx
  rw [bf1]
  omega

theorem c27b_isCompl (E : Model 5) {Z : Subgroup E.W} (hZ : IsInvSub E ⊤ Z)
    (e : (E.restrict Z hZ).Iso orth) (hEZ : commW E (alternatingGroup (Fin 5)) ⊤ ≤ Z) :
    IsCompl Z (fixW E (alternatingGroup (Fin 5))) := by
  set A := alternatingGroup (Fin 5) with hA
  have ht := idx_le_four hZ e hEZ threeCyc012_mem_alt odd_orderOf_threeCyc012 idx_orth_threeCyc012
  have hs := idx_le_four hZ e hEZ threeCyc234_mem_alt odd_orderOf_threeCyc234 idx_orth_threeCyc234
  have hCle : fixW E (Subgroup.zpowers threeCyc012) ⊓ fixW E (Subgroup.zpowers threeCyc234) ≤ fixW E A := by
    intro w hw
    rw [Subgroup.mem_inf, mem_fixW_zpowers, mem_fixW_zpowers] at hw
    have : w ∈ fixW E (Subgroup.closure {threeCyc012, threeCyc234}) := by
      rw [mem_fixW_closure]
      intro x hx
      rcases hx with rfl | rfl
      · exact hw.1
      · exact hw.2
    exact fixW_antitone E alt5_le_closure_threeCycles this
  have hidx : (fixW E A).index ≤ 16 := by
    have h1 : (fixW E A).index ≤ (fixW E (Subgroup.zpowers threeCyc012) ⊓
        fixW E (Subgroup.zpowers threeCyc234)).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
        (Subgroup.index_dvd_of_le hCle)
    have h2 := Subgroup.index_inf_le (H := fixW E (Subgroup.zpowers threeCyc012))
      (K := fixW E (Subgroup.zpowers threeCyc234))
    calc (fixW E A).index ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ 4 * 4 := Nat.mul_le_mul ht hs
  have hfixR : fixW (E.restrict Z hZ) A = ⊥ := fixW_restrict_alt_eq_bot hZ e
  have hdisj : Z ⊓ fixW E A = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    have h1 := (E.restrictMk_mem_fixW Z hZ A z hz.1).mpr hz.2
    rw [hfixR, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hcardZ : Nat.card Z = 16 := card_orth_restrict hZ e
  have hrel1 : (fixW E A).relIndex Z = 16 := by
    have : (fixW E A).subgroupOf Z = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      have : (z : E.W) ∈ Z ⊓ fixW E A := ⟨z.2, hz⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact Subtype.ext this
    unfold Subgroup.relIndex
    rw [this, Subgroup.index_bot, hcardZ]
  have hrel2 : (fixW E A).relIndex (Z ⊔ fixW E A) = 16 := by
    rw [sup_comm, Subgroup.relIndex_sup_left, hrel1]
  have hle : fixW E A ≤ Z ⊔ fixW E A := le_sup_right
  have h3 := Subgroup.relIndex_mul_index hle
  rw [hrel2] at h3
  have hpos : 0 < (Z ⊔ fixW E A).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have h4 : (Z ⊔ fixW E A).index = 1 := by
    have : 16 * (Z ⊔ fixW E A).index ≤ 16 := h3 ▸ hidx
    omega
  exact ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr (Subgroup.index_eq_one.mp h4)⟩

theorem c27b_eq_top (E : Model 5) {Z : Subgroup E.W} (hZ : IsInvSub E ⊤ Z)
    (e : (E.restrict Z hZ).Iso orth) (hEZ : commW E (alternatingGroup (Fin 5)) ⊤ ≤ Z)
    (hfix : fixW E (alternatingGroup (Fin 5)) = ⊥) : Z = ⊤ := by
  have h := (c27b_isCompl E hZ e hEZ).codisjoint
  rw [hfix, codisjoint_bot] at h
  exact h

end CFSG.Quasithin.F53Mod
