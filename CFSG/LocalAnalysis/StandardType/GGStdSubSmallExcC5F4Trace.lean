module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralTrace
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Orb
import all CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree CFSG.LieType.Simplicity.TitsBits CFSG.StandardType.TableBF4TwoInputs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

section Pos

variable {τ : Tag} {R : Type}
  [Field R]

theorem trace_eq_sum_posCoord (A : Module.End R (RootModule τ R)) :
    LinearMap.trace R (RootModule τ R) A =
      ∑ p ∈ Finset.range (dim τ), posCoord τ R p (A (posVec τ R p)) := by
  rw [trace_eq_sum_coord]
  symm
  refine Finset.sum_bij (fun p hp => posLabel p (Finset.mem_range.1 hp))
    (fun _ _ => Finset.mem_univ _) (fun p _ q _ h => posLabel_injective _ _ h) (fun b _ => ?_)
    (fun p hp => ?_)
  · obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
    exact ⟨p, Finset.mem_range.2 hp, rfl⟩
  · have hp' := Finset.mem_range.1 hp
    rw [posVec_eq_single hp', posCoord, dif_pos hp', Finsupp.lapply_apply]

theorem trace_toEnd {K : Type} [Field K] (A : ℕ) :
    LinearMap.trace K (RootModule ReeTag.F4.tag K) (toEnd K A) =
      ∑ c ∈ Finset.range 52, bitK K (A.testBit (52 * c + c)) := by
  rw [trace_eq_sum_posCoord, dim_F4]
  exact Finset.sum_congr rfl fun c hc =>
    posCoord_toEnd_posVec A (Finset.mem_range.1 hc) (Finset.mem_range.1 hc)

end Pos

theorem sum_bitK {K : Type} [Field K] (s : Finset ℕ) (b : ℕ → Bool) :
    ∑ c ∈ s, bitK K (b c) = ((s.filter fun c => b c = true).card : K) := by
  rw [Finset.natCast_card_filter]
  rfl

theorem card_diag_s0s1s2 :
    ((Finset.range 52).filter fun c =>
      (mul (mul (mul (pack (eltBits 1)) (pack (eltBits 6)))
          (mul (pack (eltBits 7)) (pack (eltBits 14))))
        (mul (pack (eltBits 15)) (pack (eltBits 23)))).testBit (52 * c + c) = true).card = 20 := by
  decide +kernel

section Delta

variable
  {K : Type} [Field K] [CharP K 2]

theorem hasBits_torus3_vecDelta :
    HasBits K (TableBF4Two.torus3 K vecDelta)
      (mul (mul (mul (pack (eltBits 1)) (pack (eltBits 6)))
          (mul (pack (eltBits 7)) (pack (eltBits 14))))
        (mul (pack (eltBits 15)) (pack (eltBits 23)))) := by
  have e : TableBF4Two.torus3 K vecDelta =
      TableBF4Two.torusGen K 0 * TableBF4Two.torusGen K 1 * TableBF4Two.torusGen K 2 := by
    rw [torusGen_eq_torus3, torusGen_eq_torus3, torusGen_eq_torus3, ← map_mul, ← map_mul]
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [e]
  exact ((hasBits_rho 0).mul (hasBits_rho 1)).mul (hasBits_rho 2)

theorem trace_torus3_vecDelta :
    LinearMap.trace K (RootModule Tag.F4 K)
      (((TableBF4Two.torus3 K vecDelta : adjointGroup .F4 K) : ModGL Tag.F4 K) :
        Module.End K (RootModule Tag.F4 K)) = 0 := by
  have hb : (((TableBF4Two.torus3 K vecDelta : adjointGroup .F4 K) : ModGL Tag.F4 K) :
      Module.End K (RootModule Tag.F4 K)) =
        toEnd K (mul (mul (mul (pack (eltBits 1)) (pack (eltBits 6)))
          (mul (pack (eltBits 7)) (pack (eltBits 14))))
            (mul (pack (eltBits 15)) (pack (eltBits 23)))) :=
    hasBits_torus3_vecDelta
  have h := trace_toEnd (K := K) (mul (mul (mul (pack (eltBits 1)) (pack (eltBits 6)))
    (mul (pack (eltBits 7)) (pack (eltBits 14)))) (mul (pack (eltBits 15)) (pack (eltBits 23))))
  rw [sum_bitK, card_diag_s0s1s2, ← hb] at h
  exact h.trans ((CharP.cast_eq_zero_iff K 2 20).2 (by norm_num))

end Delta

end CFSG.StandardType.SmallExc.F4Two

end
