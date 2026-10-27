module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenCover
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenLine
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenPair
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.SuSplitRootGen

theorem ggTorusRootGenAvoidKG_unitarySplit
    {K : Type} [Field K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) (r : ℕ) :
    GGTorusRootGenAvoidKG p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hrA h3 hsc
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · exfalso
      rw [hn0] at hK
      norm_num at hK
      haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact hn
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos (by omega : 0 < n)]
      rw [pow_succ, Nat.pred_eq_sub_one]
      ring
    have hdvd : 2 ∣ 2 * 2 ^ (n - 1) - 1 := by
      rw [← h2n]
      exact hpq
    exact Nat.two_not_dvd_two_mul_sub_one (n := 2 ^ (n - 1)) (by positivity) hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  rcases (show d = 3 ∨ 4 ≤ d by omega) with rfl | hd4
  ·
    exfalso
    have hle := card_le_of_three hK hp hpq hψ hker hperf hA hAI
    have h3p : p ^ 3 ≤ p ^ 1 := by simpa using h3.trans hle
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3p
    omega
  ·
    obtain ⟨r', ε, h, ζ, τ, φ, hdr, hε, hζ, -, hτ, hφs, hφker, hkerp, hM, hτc⟩ :=
      exists_isCoverTorusModel hK hd4 hp hpq hψ hker hperf hA hAI hsc
    haveI : Finite K := h.finite
    have hcard := card_eq_of_isCoverTorusModel hM hτc
    have h3r : p ^ 3 ≤ p ^ r' := by
      rw [← hcard]
      exact h3
    have hr3 : 3 ≤ r' := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3r
    haveI : Finite (hypSU h r' ε) := Subtype.finite
    let ι : Type := Fin r' ⊕ {x : Fin r' × Fin r' // x.1 ≠ x.2}
    haveI : Nonempty ι := ⟨Sum.inl ⟨0, by omega⟩⟩
    let w : ι → hypSU h r' ε :=
      Sum.elim (fun m => lineWeyl h ε m) (fun x => pairWeyl h ε x.1.1 x.1.2)
    let f : ι → (Fin r' → ZMod p) → Fin r' → ZMod p :=
      Sum.elim (fun m => SlNsRootGen.negMap m)
        (fun x => SlNsRootGen.swapMap x.1.1 x.1.2)
    let S : ι → Subgroup (hypSU h r' ε) :=
      Sum.elim (fun m => lineBlock h m) (fun x => pairBlock h ε x.1.1 x.1.2)
    refine ggTorusRootGenAvoid_of_cover (p := p) (s := r') (H := hypSU h r' ε)
      (L' := L') (ι := ι) hp hφs hφker hkerp hM hτc w f S ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ·
      rintro (m | x) t
      · exact lineWeyl_conj h hp hζ.pow_eq_one hτ m t
      · exact pairWeyl_conj h hτ x.1.1 x.1.2 t
    ·
      rintro (m | x) t
      · exact SlNsRootGen.negMap_negMap m t
      · exact SlNsRootGen.swapMap_swapMap x.1.1 x.1.2 t
    ·
      rintro (m | x)
      · exact SlNsRootGen.card_fixed_negMap hp2 m
      · exact SlNsRootGen.card_fixed_swapMap x.2
    ·
      rintro (m | x)
      · exact lineWeyl_mem_lineBlock h m
      · exact pairWeyl_mem_pairBlock h x.1.1 x.1.2
    ·
      rintro (m | x)
      · exact isComponentOf_lineBlock h hp hp2 hpq hζ hτ hε m
      · exact isComponentOf_pairBlock h hp hp2 hζ hτ hε x.2
    ·
      rintro (m | x)
      · exact dvd_card_lineBlock h hp hζ hτ m
      · exact dvd_card_pairBlock h hp hζ x.2
    ·
      intro j
      rcases j with m₀ | x₀
      · rw [eq_top_iff, ← iSup_blocks_avoid_line_eq_top h hε hr3 m₀]
        refine sup_le ?_ ?_
        · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
          exact le_iSup₂_of_le (Sum.inr ⟨(i, j), hij⟩)
            (SlNsRootGen.swapMap_ne_negMap hij m₀) le_rfl
        · refine iSup_le fun m => iSup_le fun hm => ?_
          exact le_iSup₂_of_le (Sum.inl m)
            (fun heq => hm (SlNsRootGen.eq_of_negMap_eq hp2 heq)) le_rfl
      · rw [eq_top_iff, ← iSup_blocks_avoid_pair_eq_top h hε hr3 x₀.1.1 x₀.1.2]
        refine sup_le ?_ ?_
        · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
          exact le_iSup₂_of_le (Sum.inr ⟨(i, j), hij.1⟩)
            (fun heq => hij.2 (SlNsRootGen.pair_eq_of_swapMap_eq hij.1 x₀.2 heq)) le_rfl
        · refine iSup_le fun m => ?_
          exact le_iSup₂_of_le (Sum.inl m)
            (fun heq => SlNsRootGen.swapMap_ne_negMap x₀.2 m heq.symm) le_rfl

end CFSG.StandardType

end
