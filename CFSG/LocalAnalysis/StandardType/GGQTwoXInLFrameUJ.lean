module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUBlockJ
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUCardS
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggQTwoXInLU_coordJ {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI : GGQTwoI1 Bs D J) (hn3 : 3 ∣ n) (hn6 : 6 ≤ n)
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K) :
    ∃ C' : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K,
      J = (TableBUE.blockSU (K := K) (n := 1) ((Finset.univ.erase 0).erase 1)).map C'.φ ∧
      ∀ b : ↥Bs, (b : G) ∈ D ↔ ∀ i j : Fin (n + 1), i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 →
        (C'.ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) i =
          (C'.ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) j := by
  obtain ⟨S, hS0, hJS, hDS⟩ := ggQTwoXInLU_blockJ hS hI hn3 hn6 C
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hDBs : D ≤ Bs := hDJ.1.1.trans hS.1.1.2.1.1
  have hD9 : Nat.card ↥D = 9 := by
    rw [hDJ.1.2.2.1]
    norm_num
  obtain ⟨j, hj0, rfl⟩ := ggQTwoXInLU_cardS hn6 C hDBs hD9 hS0 hDS
  have h01 : (0 : Fin (n + 1)) ≠ 1 := fun h => by
    have := Fin.zero_eq_one_iff.mp h
    omega
  have hσ0 : Equiv.swap 1 j 0 = 0 := Equiv.swap_apply_of_ne_of_ne h01 hj0.symm
  obtain ⟨C', hι, hblk⟩ := C.toAt.relabel (Equiv.swap 1 j) hσ0
  have hmap : ((Finset.univ.erase 0).erase j).map (Equiv.swap 1 j).symm.toEmbedding =
      (Finset.univ.erase 0).erase 1 := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_erase, Finset.mem_univ, and_true]
    rcases eq_or_ne i 1 with rfl | hi1
    · simp [Equiv.swap_apply_left, hj0]
    rcases eq_or_ne i j with rfl | hij
    · simp [Equiv.swap_apply_right, hi1, hi1.symm, hj0, h01.symm]
    rw [Equiv.swap_apply_of_ne_of_ne hi1 hij]
    simp [hi1, hij]
  have hmem : ∀ i, Equiv.swap 1 j i ∈ (Finset.univ.erase 0).erase j ↔ i ≠ 0 ∧ i ≠ 1 := by
    intro i
    have h : i ∈ ((Finset.univ.erase 0).erase j).map (Equiv.swap 1 j).symm.toEmbedding ↔
        i ∈ (Finset.univ.erase 0).erase 1 := by
      rw [hmap]
    simp only [Finset.mem_map_equiv, Equiv.symm_symm] at h
    rw [h]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  refine ⟨C'.toCoord, ?_, fun b => ?_⟩
  · have h1 := hblk ((Finset.univ.erase 0).erase j)
    rw [hmap, GGQTwoXInLUCoord.toAt_φ] at h1
    rw [GGQTwoXInLUCoordAt.toCoord_φ, h1]
    exact hJS
  · rw [hDS b, GGQTwoXInLUCoordAt.toCoord_ι, hι b, GGQTwoXInLUCoord.toAt_ι]
    constructor
    · intro h i k hi0 hi1 hk0 hk1
      exact h _ ((hmem i).mpr ⟨hi0, hi1⟩) _ ((hmem k).mpr ⟨hk0, hk1⟩)
    · intro h i hi k hk
      have hi' := (hmem (Equiv.swap 1 j i)).mp (by rwa [Equiv.swap_apply_self])
      have hk' := (hmem (Equiv.swap 1 j k)).mp (by rwa [Equiv.swap_apply_self])
      have := h _ _ hi'.1 hi'.2 hk'.1 hk'.2
      simpa only [Equiv.swap_apply_self] using this

end CFSG.StandardType

end
