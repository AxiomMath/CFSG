module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K]

theorem invariant_flagSpace_one {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ Q3 K 0)
    {w : Fin 3 → K} (hw : w ∈ flagSpace 3 K 1) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ flagSpace 3 K 1 := by
  have h : (flagSpace 3 K 1).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) = flagSpace 3 K 1 :=
    hg
  rw [← h]
  exact Submodule.mem_map_of_mem hw

theorem card_flagSpace [Finite K] {i : ℕ} (hi : i ≤ 3) :
    Nat.card (flagSpace 3 K i) = Nat.card K ^ i := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(flagSpace 3 K i)), finrank_flagSpace hi]

theorem mem_Q3_one_of_upper {g : SpecialLinearGroup (Fin 3) K}
    (h10 : (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) : g ∈ Q3 K 1 := by
  refine upperTriangular_le_Q3 1 fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]

@[expose] def tv02 (s : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, s; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def tv01 (s : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, s, 0; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def dg01 (c : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![(c : K), 0, 0; 0, ((c⁻¹ : Kˣ) : K), 0; 0, 0, 1], by simp [det_fin_three]⟩

theorem flagSpace_two_le_of_invariant {W : AddSubgroup (Fin 3 → K)} (hW : W ≠ ⊥)
    (hinv : ∀ g ∈ Q3 K 1, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) :
    ((flagSpace 3 K 2 : Submodule K (Fin 3 → K)) : Set (Fin 3 → K)) ⊆ W := by
  obtain ⟨w, hw, hw0⟩ := W.bot_or_exists_ne_zero.resolve_left hW
  have he0 : ∀ c : K, Pi.single (0 : Fin 3) c ∈ W := by
    intro c
    by_cases h2 : w 2 = 0
    · by_cases h1 : w 1 = 0
      · have h0 : w 0 ≠ 0 := by
          intro h0
          apply hw0
          ext i
          fin_cases i <;> simp_all
        by_cases hc : c = 0
        · rw [hc, Pi.single_zero]
          exact W.zero_mem
        · have hu : IsUnit (c / w 0) := (div_ne_zero hc h0).isUnit
          have hg := hinv (dg01 hu.unit) (mem_Q3_one_of_upper (by rfl) (by rfl) (by rfl)) w hw
          convert hg using 1
          ext i
          fin_cases i <;> simp [dg01, mulVec, dotProduct, Fin.sum_univ_three, h1, h2, h0]
      · have hg := hinv (tv01 (c / w 1)) (mem_Q3_one_of_upper (by rfl) (by rfl) (by rfl)) w hw
        have := W.sub_mem hg hw
        convert this using 1
        ext i
        fin_cases i <;> simp [tv01, dotProduct, Fin.sum_univ_three, h1, h2]
    · have hg := hinv (tv02 (c / w 2)) (mem_Q3_one_of_upper (by rfl) (by rfl) (by rfl)) w hw
      have := W.sub_mem hg hw
      convert this using 1
      ext i
      fin_cases i <;> simp [tv02, dotProduct, Fin.sum_univ_three, h2]
  have hr : reflection 3 K 1 le_rfl (by norm_num) ∈ Q3 K 1 := by
    rw [Q3_eq, ← reflElt_of_lt le_rfl (by norm_num)]
    exact (reflElt_mem_flagStabilizer_singleton_iff le_rfl (by norm_num)).2 (by norm_num)
  have he1 : ∀ c : K, Pi.single (1 : Fin 3) c ∈ W := by
    intro c
    have := hinv _ hr _ (he0 c)
    convert this using 1
    ext i
    fin_cases i <;> simp [reflectionMatrix, mulVec, dotProduct, Fin.sum_univ_three]
  intro v hv
  have hv2 : v 2 = 0 := (mem_flagSpace.1 hv) 2 (by decide)
  have hv' : v = Pi.single (0 : Fin 3) (v 0) + Pi.single (1 : Fin 3) (v 1) := by
    ext i
    fin_cases i <;> simp [hv2]
  rw [hv']
  exact W.add_mem (he0 _) (he1 _)

end CFSG.Quasithin.H13.NQCat.NGT
