module

public import CFSG.Sporadic.Schreier.LySylowRep
public import CFSG.Sporadic.Ly.Primitive

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true)

@[expose] def stm (i j : ℕ) : ℕ := (sTab[i]!)[j]!

theorem mulTab_parts :
    (∀ i < 256, ∀ j < 256, stm i j < 256) ∧ (∀ j < 256, stm 0 j = j) ∧
    ∀ i, 1 ≤ i → i < 256 → ∀ j < 256, stm i j = (sLam[sLab[i]!]!)[stm sPar[i]! j]! := by
  have h := sylow_parts.2.2.1
  unfold mulTabOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hsz, hrows⟩, h0⟩, hrec⟩ := h
  refine ⟨fun i hi j hj => ?_, fun j hj => ?_, fun i hi1 hi j hj => ?_⟩
  · rw [Array.all_eq_true] at hrows
    have := hrows i (by rw [hsz]; exact hi)
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at this
    have h' := this.2 j (by rw [this.1]; exact hj)
    unfold stm
    rwa [getElem!_pos sTab i (by rw [hsz]; exact hi), getElem!_pos _ j (by rw [this.1]; exact hj)]
  · have := (allIn_eq_true.1 h0) j (Nat.zero_le _) hj
    simpa [stm] using this
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 hrec) i hi1 hi)) j (Nat.zero_le _) hj
    simpa [stm] using this

theorem sTree_mul :
    ∀ i < 256, ∀ j < 256, sTree i * sTree j = sTree (stm i j) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi j hj
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [sTree_zero, one_mul, mulTab_parts.2.1 j hj]
    · obtain ⟨hp, hl, -⟩ := enum_parts.2.2.2.2.2.2.2.2.1 i hpos hi
      rw [sTree_succ hpos hi, mul_assoc, ih _ hp (by omega) j hj,
        sylowGen_mul_sTree ⟨sLab[i]!, hl⟩ (mulTab_parts.1 _ (by omega) j hj),
        mulTab_parts.2.2 i hpos hi j hj]

theorem card_J_ge : 255 ≤ Nat.card J := by rw [card_J]; norm_num

theorem sylowList_eq :
    sylowList = (List.range 256).map sTree := by
  rw [sylowList_def]
  have hlen : ((List.finRange 6).map fun (k : Fin 6) (g : J) => sylowGen k * g).length = 6 := by
    simp
  apply bfsList_eq (n := 256) (x := sTree)
    (img := fun k i => (sLam[k]!)[i]!) (par := fun j => sPar[j]!) (lab := fun j => sLab[j]!)
  · intro j hj1 hj2
    have := enum_parts.2.2.2.2.2.2.2.2.2.1 j hj1 hj2
    simp only [LySchreier.discPos, hlen, sylowPos] at this ⊢
    omega
  · intro i hi j hj h
    exact sTree_inj hi hj h
  · intro i hi k hk
    rw [hlen] at hk
    refine ⟨(enum_parts.2.2.2.2.1 k hk).2 i hi, ?_⟩
    simp only [List.getElem_map, List.getElem_finRange]
    exact sylowGen_mul_sTree ⟨k, hk⟩ hi
  · intro j hj1 hj2
    obtain ⟨hp, hl, hlam⟩ := enum_parts.2.2.2.2.2.2.2.2.1 j hj1 hj2
    exact ⟨hp, by rw [hlen]; exact hl, hlam⟩
  · intro i hi k hk
    rw [hlen] at hk
    have := enum_parts.2.2.2.2.2.2.2.2.2.2 i hi k hk
    simp only [LySchreier.discPos, hlen, sylowPos] at this ⊢
    rcases this with h | h
    · exact Or.inl h
    · right; omega
  · norm_num
  · exact sTree_zero
  · have := card_J_ge
    omega

theorem sylowElt_eq
    {i : ℕ} (hi : i < 256) : sylowElt i = sTree i := by
  rw [sylowElt, sylowList_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  rfl

theorem sylowGen_mem
    (k : Fin 6) : sylowGen k ∈ lyS := Subgroup.subset_closure ⟨k, rfl⟩

theorem sTree_mem :
    ∀ i < 256, sTree i ∈ lyS := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [sTree_zero]; exact lyS.one_mem
    · obtain ⟨hp, hl, -⟩ := enum_parts.2.2.2.2.2.2.2.2.1 i hpos hi
      rw [sTree_succ hpos hi]
      exact lyS.mul_mem (sylowGen_mem _) (ih _ hp (by omega))

end CFSG.Sporadic.LySchreier
