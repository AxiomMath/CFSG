module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumD
public import CFSG.LocalAnalysis.StandardType.GGFrameModelSignedTable
public import CFSG.LocalAnalysis.StandardType.GGEvenSignedNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType.FrameRoute

open SpCoord

variable {k : ℕ}

theorem sgnAut_mul_swap_pow_four (i a b : Fin k) :
    ((sgnAut i : MulAut (Fin k → Multiplicative (ZMod 3))) *
      permAut (Equiv.swap a b)) ^ 4 = 1 := by
  let t : MulAut (Fin k → Multiplicative (ZMod 3)) := permAut (Equiv.swap a b)
  have ht : t ^ 2 = 1 := permAut_swap_sq a b
  have hc : t * sgnAut i * t⁻¹ = sgnAut (Equiv.swap a b i) :=
    ggSpSigned_conj_permAut_sgnAut 3 k (Equiv.swap a b) i
  have hs : (sgnAut i * t) ^ 2 = sgnAut i * sgnAut (Equiv.swap a b i) := by
    calc
      _ = sgnAut i * (t * sgnAut i * t⁻¹) * t ^ 2 := by
        simp only [pow_two]
        group
      _ = sgnAut i * sgnAut (Equiv.swap a b i) := by rw [hc, ht, mul_one]
  change (sgnAut i * t) ^ 4 = 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs,
    (sgnAut_commute_sgnAut i (Equiv.swap a b i)).mul_pow, sgnAut_sq, sgnAut_sq,
    one_mul]

theorem sgnAut_mul_negSwap_pow_four (i a b : Fin k) (hab : a ≠ b) :
    (sgnAut i * negSwapAut a b) ^ 4 = 1 := by
  have ha : (sgnAut a : MulAut (Fin k → Multiplicative (ZMod 3))) * sgnAut a = 1 :=
    by simpa only [pow_two] using sgnAut_sq (p := 3) a
  have hb : (sgnAut b : MulAut (Fin k → Multiplicative (ZMod 3))) * sgnAut b = 1 :=
    by simpa only [pow_two] using sgnAut_sq (p := 3) b
  by_cases hia : i = a
  · subst i
    have heq : sgnAut a * negSwapAut a b = sgnAut b * permAut (Equiv.swap a b) := by
      simp only [negSwapAut, ← mul_assoc, ha, one_mul]
    rw [heq]
    exact sgnAut_mul_swap_pow_four b a b
  · by_cases hib : i = b
    · subst i
      have heq : sgnAut b * negSwapAut a b = sgnAut a * permAut (Equiv.swap a b) := by
        unfold negSwapAut
        calc
          _ = (sgnAut b * sgnAut a) * sgnAut b * permAut (Equiv.swap a b) := by group
          _ = sgnAut a * permAut (Equiv.swap a b) := by
            rw [sgnAut_mul_comm b a, mul_assoc (sgnAut a), hb, mul_one]
      rw [heq]
      exact sgnAut_mul_swap_pow_four a a b
    · have hc := (sgnAut_commute_negSwapAut_iff i hab).mpr ⟨hia, hib⟩
      have ht : (negSwapAut a b) ^ 2 = 1 := OrthExcEven.sgnTransp_sq hab
      rw [hc.mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul,
        sgnAut_sq, ht]
      simp

theorem sgnAut_mul_signedReflection_pow_four (i : Fin k)
    {t : MulAut (Fin k → Multiplicative (ZMod 3))}
    (ht : t ∈ modelReflSet (signedPermSet k)) :
    (sgnAut i * t) ^ 4 = 1 := by
  rcases (mem_modelReflSet_signedPermSet_iff t).mp ht with
    ⟨j, rfl⟩ | ⟨a, b, hab, rfl | rfl⟩
  · rw [(sgnAut_commute_sgnAut i j).mul_pow, show (4 : ℕ) = 2 * 2 from rfl,
      pow_mul, pow_mul, sgnAut_sq, sgnAut_sq]
    simp
  · exact sgnAut_mul_swap_pow_four i a b
  · exact sgnAut_mul_negSwap_pow_four i a b hab

theorem evenSignedReflection_of_order_three
    {r t : MulAut (Fin k → Multiplicative (ZMod 3))}
    (hr : r ∈ modelReflSet (signedPermSet k))
    (ht : t ∈ modelReflSet (signedPermSet k))
    (horder : orderOf (r * t) = 3) :
    r ∈ modelReflSet (evenSignedPermSet k) := by
  rcases (mem_modelReflSet_signedPermSet_iff r).mp hr with
    ⟨i, rfl⟩ | h
  · have hd := orderOf_dvd_of_pow_eq_one (sgnAut_mul_signedReflection_pow_four i ht)
    rw [horder] at hd
    norm_num at hd
  · exact (mem_modelReflSet_evenSignedPermSet_iff r).mpr h

theorem d5_signed_simple_even
    {H : Subgroup (MulAut (Fin k → Multiplicative (ZMod 3)))}
    (f : (ggCoxeterMatrixD 5).Group ≃* H)
    (hr : ∀ i : Fin 5, (f ((ggCoxeterMatrixD 5).simple i) :
      MulAut (Fin k → Multiplicative (ZMod 3))) ∈ modelReflSet (signedPermSet k)) :
    ∀ i : Fin 5, (f ((ggCoxeterMatrixD 5).simple i) :
      MulAut (Fin k → Multiplicative (ZMod 3))) ∈ modelReflSet (evenSignedPermSet k) := by
  have hneighbors : ∀ i : Fin 5, ∃ j : Fin 5, ggCoxeterMatrixD 5 i j = 3 := by
    change ∀ i : Fin 5, ∃ j : Fin 5,
      (if i = j then 1 else if CartanMatrix.D 5 i j = 0 then 2 else 3) = (3 : ℕ)
    decide +kernel
  intro i
  obtain ⟨j, hij⟩ := hneighbors i
  apply evenSignedReflection_of_order_three (hr i) (hr j)
  calc
    _ = orderOf (f ((ggCoxeterMatrixD 5).simple i * (ggCoxeterMatrixD 5).simple j)) := by
      rw [map_mul, ← Subgroup.coe_mul, Subgroup.orderOf_coe]
    _ = orderOf ((ggCoxeterMatrixD 5).simple i * (ggCoxeterMatrixD 5).simple j) :=
      f.orderOf_eq _
    _ = ggCoxeterMatrixD 5 i j := by
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        (ggCoxeterMatrixD 5).toCoxeterSystem.orderOf_simple_mul_simple i j
    _ = 3 := hij

end CFSG.StandardType.FrameRoute

end
