module

public import CFSG.LargeExtraspecial.SL4ModClassSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module CFSG.Sporadic.SmallF2 Native CFSG.Sporadic.SmallF2.Native Matrix

private theorem w183_echelonOK_spec {n : ℕ} {L masks piv : Array ℕ}
    (h : echelonOK n L masks piv = true) :
    n ≤ masks.size ∧ n ≤ piv.size ∧ ∀ k < n,
      piv[k]! < 105 ∧ (xorSel masks[k]! L).testBit piv[k]! = true ∧
        ∀ j, j < n → k < j → (xorSel masks[j]! L).testBit piv[k]! = false := by
  rw [echelonOK, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  simp only [List.mem_range] at h
  refine ⟨h.1.1, h.1.2, fun k hk => ?_⟩
  have hk' := h.2 k hk
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk'
  refine ⟨hk'.1.1, hk'.1.2, fun j hj hkj => ?_⟩
  have hj' := hk'.2 j (List.mem_range.mpr hj)
  rw [Bool.or_eq_true] at hj'
  rcases hj' with h | h
  · exact absurd (decide_eq_true_eq.mp h) (by omega)
  · exact Bool.eq_false_of_not_eq_true' h

theorem false_of_validClass_oversize {d : ℕ} {refs : Array (Array (Array ℕ))}
    {taus : Array (Array ℕ)} {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)}
    (hX : IsIrredTau taus X d) {m : ℕ} (hm : vec m ∈ X) {c : ClassCert}
    (hc : validClass d refs taus m c = true) (hk : c.kind = 0) : False := by
  rw [validClass, Bool.and_eq_true] at hc
  obtain ⟨hd, hc⟩ := hc
  have hL := mem_of_derivOK hX.1 hm hd
  have hk' : (c.kind == 0) = true := by rw [hk]; rfl
  rw [ite_eq_left hk'] at hc
  rw [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, hech⟩ := hc
  obtain ⟨-, -, hspec⟩ := w183_echelonOK_spec hech
  have hli : LinearIndependent (ZMod 2)
      (fun k : Fin (d + 1) => vec (xorSel c.masks[k.val]! c.L)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k₀
    induction k₀ using Fin.strong_induction_on with
    | h k₀ ih =>
      obtain ⟨hpiv, hset, hclear⟩ := hspec k₀.val k₀.isLt
      have hcoord : (∑ k : Fin (d + 1),
          (g k • vec (xorSel c.masks[k.val]! c.L)) ⟨c.piv[k₀.val]!, hpiv⟩) = 0 := by
        have h := congrFun hg ⟨c.piv[k₀.val]!, hpiv⟩
        rw [Fintype.sum_apply, Pi.zero_apply] at h
        exact h
      have hsingle : (∑ k : Fin (d + 1),
          (g k • vec (xorSel c.masks[k.val]! c.L)) ⟨c.piv[k₀.val]!, hpiv⟩) =
          (g k₀ • vec (xorSel c.masks[k₀.val]! c.L)) ⟨c.piv[k₀.val]!, hpiv⟩ := by
        refine Finset.sum_eq_single k₀ ?_ ?_
        · intro b _ hbne
          rw [Pi.smul_apply]
          have hbval : b.val ≠ k₀.val := fun h => hbne (Fin.ext h)
          rcases lt_or_gt_of_ne hbval with hlt | hgt
          · rw [ih b (Fin.lt_iff_val_lt_val.mpr hlt), zero_smul]
          · have hbit0 : (vec (xorSel c.masks[b.val]! c.L))
                ⟨c.piv[k₀.val]!, hpiv⟩ = 0 := by
              rw [vec, toVecD_apply]
              simp [hclear b.val b.isLt hgt]
            rw [hbit0, smul_zero]
        · intro hmem
          exact absurd (Finset.mem_univ k₀) hmem
      have hbit1 : (vec (xorSel c.masks[k₀.val]! c.L)) ⟨c.piv[k₀.val]!, hpiv⟩ = 1 := by
        rw [vec, toVecD_apply]
        simp [hset]
      rw [hsingle, Pi.smul_apply, hbit1, smul_eq_mul, mul_one] at hcoord
      exact hcoord
  let v : Fin (d + 1) → X := fun k =>
    ⟨vec (xorSel c.masks[k.val]! c.L), xorSel_mem (c.masks[k.val]!) hL⟩
  have hv : LinearIndependent (ZMod 2) v := LinearIndependent.of_comp X.subtype hli
  have hle := hv.fintype_card_le_finrank
  rw [Fintype.card_fin, hX.2.1] at hle
  omega

end CFSG.LargeExtraspecial.SL4Mod
