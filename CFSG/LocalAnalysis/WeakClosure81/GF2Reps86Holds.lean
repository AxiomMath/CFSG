module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Ind
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Base
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Big
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Conv
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Emb
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Nine
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Seven
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Step
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Tools

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsIrrOn)
open GF2Reps86

theorem GF2Reps86.t86_of_nine_le {n : ℕ} (hn : 9 ≤ n) : T86 n := by
  induction n, hn using Nat.le_induction with
  | base => exact t86_nine t86_seven
  | succ n hn ih =>
    exact t86_of_ten_le (by omega) (by simpa using ih) (noFpf_of_ten_le noFpf_ten (by omega))

theorem w4Lem8_6_holds : W4Lem8_6 := by
  intro W _ _ hW Y L t n hLY hF hAlt hn hirrL htY hto hm
  obtain ⟨ι⟩ := hAlt
  have hn5 : 5 ≤ n := by omega
  obtain ⟨ψ, hψ, hA, hpre, -⟩ := exists_embedding_of_fstar hLY hF hn5 (by omega) ι
  obtain ⟨t', rfl⟩ : ∃ t' : ↥Y, (t' : MulAut W) = t := ⟨⟨t, htY⟩, rfl⟩
  have hirr : IsIrrOn Y ⊤ ⊥ :=
    ⟨hirrL.1, fun _ _ _ _ => Subgroup.mem_top _, fun y _ u hu => by
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one],
      fun J hJ h0 h1 => hirrL.2.2.2 J (fun l hl u hu => hJ l (hLY hl) u hu) h0 h1⟩
  have hfix : fixV (altPre ψ) = ⊥ := fixV_altPre_eq_bot (by omega) hA hirr
  have hnat : NatVia ψ ⊤ → AlternatingNatural L ⊤ ⊥ n := fun h => by
    have h' := alternatingNatural_of_natVia hn5 hψ hA hfix h
    rwa [hpre] at h'
  have ht2 : t' ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (t' : MulAut W)
    rw [hto] at h
    exact Subtype.ext (by simpa using h)
  have ht1 : ψ t' ≠ 1 := by
    intro h
    have h1 : (t' : MulAut W) = 1 := congrArg Subtype.val (hψ (h.trans (map_one ψ).symm))
    rw [h1, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hidx : (fixV (Subgroup.zpowers (t' : MulAut W))).index ≤ 8 :=
    index_le_eight_of_mQuot_le_three hW hm
  by_cases hsw : (ψ t').IsSwap
  · exact Or.inr (hnat (natVia_top_of_swap hW (by omega) hψ hA hirr hfix hsw hidx))
  rcases hn with rfl | hn9
  · rcases seven_irr hW hψ hA hirr ht2 ht1 hsw hidx with h | ⟨hcard, hr⟩
    · exact Or.inr (hnat h)
    · refine Or.inl ⟨rfl, hcard, le_antisymm (fun y hy => ?_) hLY⟩
      have h1 : ψ ⟨y, hy⟩ ∈ ψ.range := ⟨⟨y, hy⟩, rfl⟩
      rw [hr] at h1
      rw [← hpre]
      exact coe_mem_altPre_iff.2 h1
  · rcases t86_of_nine_le hn9 W hW Y ψ hψ hA t' ht2 ht1 hsw hidx with h | ⟨h7, -⟩
    · rw [commV_eq_top_of_fixV_eq_bot hirr altPre_le hfix] at h
      exact Or.inr (hnat h)
    · omega

end CFSG.LocalAnalysis.WeakClosure81

end
