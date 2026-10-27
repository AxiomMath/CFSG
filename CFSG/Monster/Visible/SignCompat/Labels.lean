module

public import CFSG.Monster.Visible.SignCompat.Compat
import Mathlib.Tactic.ReduceModChar
public import CFSG.Monster.Griess.TrialityBasis.Classes

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess Matrix
open scoped symmDiff

@[expose] def signLiftPair (e : Parker) : Pvis := ⟨(YU e, gO e.code), YU_gO_mem_Pvis e⟩

theorem coe_signLiftPair (e : Parker) :
    (signLiftPair e : GL SpinIdx ℚ × latticeO) = (YU e, gO e.code) := rfl

namespace SignCompat

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

theorem conjQ_signLiftPair (e : Parker) (r : Q) : conjQ (signLiftPair e) r = conjYQ e r :=
  Subtype.ext rfl

theorem mat_signLiftPair (e : Parker) : mat (signLiftPair e).1.2 = gmat e.code := rfl

theorem coe_signLiftPair_fst (e : Parker) :
    (((signLiftPair e).1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = Ymat e := rfl

theorem mul_s_zero (k : ZMod 2) (x : SpinCoord) :
    (⟨k, 0, 0⟩ : SpinCoord) * x = ⟨k + x.s, x.a, x.δ⟩ := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, pair_zero_right, add_zero]
  · simp only [SpinCoord.mul_a, zero_add]
  · simp only [SpinCoord.mul_δ, zero_add]

theorem Xlift_eq_sgn_smul_of_symm {r r' : Q} {k : ZMod 2}
    (h : spinEquiv.symm r' = ⟨k, 0, 0⟩ * spinEquiv.symm r) : Xlift r' = sgn k • Xlift r := by
  refine Xlift_eq_sgn_smul ?_ ?_
  · unfold coordOf
    rw [h, mul_s_zero]
  · unfold centralCoord
    rw [h, mul_s_zero]

theorem Xlift_conjYQ_of_conjY (e : Parker) {r t : Q} {k : ZMod 2}
    (h : conjY e (spinEquiv.symm r) = ⟨k, 0, 0⟩ * spinEquiv.symm t) :
    Xlift (conjYQ e r) = sgn k • Xlift t :=
  Xlift_eq_sgn_smul_of_symm ((symm_conjYQ e r).trans h)

theorem conjY_even (e : Parker) (b : C) {ε : Cocode} (h : pair ΩC ε = 0) :
    conjY e ⟨0, b, ε⟩ = ⟨θ b e.code + pair e.code ε, b + (θ e.code b + pair e.code ε) • ΩC,
      Acocode e.code b + ε⟩ := by
  rw [conjY, conjD_of_even e h]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, SpinCoord.mul_δ, conjT, pair_zero_right, pair_smul_left,
      pair_ΩC_Acocode, mul_zero, add_zero, zero_add]
  · simp only [SpinCoord.mul_a, conjT, zero_add, add_smul, add_assoc]
  · simp only [SpinCoord.mul_δ, conjT, zero_add]

theorem conjY_odd (e : Parker) (b : C) {ε : Cocode} (h : pair ΩC ε = 1) :
    conjY e ⟨0, b, ε⟩ = ⟨θ b e.code + e.sign,
      b + e.code + (θ e.code b + P (e.code : Fin 24 → ZMod 2) + pair e.code ε) • ΩC,
      Acocode e.code b + (thetaD e.code + ε)⟩ := by
  rw [conjY, conjD_of_odd e h]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, SpinCoord.mul_δ, conjT, pair_zero_right, zero_add,
      pair_Acocode, Submodule.coe_add, Submodule.coe_smul, coe_ΩC, A_add_right, A_smul_Ω_right,
      A_self_mid e.code.2 b.2, add_zero]
  · simp only [SpinCoord.mul_a, conjT, zero_add]
    module
  · simp only [SpinCoord.mul_δ, conjT, zero_add]

theorem Acocode_add_smul_ΩC (a b : C) (t : ZMod 2) : Acocode a (b + t • ΩC) = Acocode a b := by
  refine ext_pair fun u => ?_
  rw [pair_Acocode, pair_Acocode, Submodule.coe_add, Submodule.coe_smul, coe_ΩC,
    A_comm₂₃ (a : Fin 24 → ZMod 2) ((b : Fin 24 → ZMod 2) + t • Ω) u, A_add_right,
    A_smul_Ω_right a u t, add_zero, A_comm₂₃]

theorem Acocode_comm (a b : C) : Acocode a b = Acocode b a := by
  rw [Acocode, Acocode, mul_comm]

theorem Acocode_zero_right (a : C) : Acocode a 0 = 0 := by
  rw [Acocode, ZeroMemClass.coe_zero, mul_zero]
  exact Submodule.Quotient.mk_zero _

theorem Acocode_ΩC (a : C) : Acocode a ΩC = 0 := by
  have h := Acocode_add_smul_ΩC a 0 1
  rwa [zero_add, one_smul, Acocode_zero_right] at h

theorem thetaD_add_smul_ΩC (b : C) (t : ZMod 2) : thetaD (b + t • ΩC) = thetaD b :=
  (thetaD_unique fun u => by rw [pair_thetaD, θ_add_smul_ΩC]).symm

theorem θ_right_add_smul_ΩC (a b : C) (t : ZMod 2) : θ a (b + t • ΩC) = θ a b := by
  rw [θ_add_right, θ_smul_right, θ_ΩC_right, mul_zero, add_zero]

theorem K_add_smul_ΩC_right (a b : C) (t : ZMod 2) :
    K (a : Fin 24 → ZMod 2) ((b + t • ΩC : C) : Fin 24 → ZMod 2) = K (a : Fin 24 → ZMod 2) b := by
  rw [Submodule.coe_add, Submodule.coe_smul, coe_ΩC, K_add_smul_Ω]

theorem P_add_smul_ΩC (b : C) (t : ZMod 2) :
    P (((b + t • ΩC : C)) : Fin 24 → ZMod 2) = P (b : Fin 24 → ZMod 2) := by
  rw [Submodule.coe_add, Submodule.coe_smul, coe_ΩC, P_add_smul_Ω b.2]

theorem P_coe_shift (a : C) (c : C₀) :
    P ((shift a c : C) : Fin 24 → ZMod 2) =
      P ((c : C) : Fin 24 → ZMod 2) + P (a : Fin 24 → ZMod 2) +
        K ((c : C) : Fin 24 → ZMod 2) a := by
  rw [coe_shift, P_add_smul_ΩC, Submodule.coe_add, P_add (c : C).2 a.2]

theorem coe_shift_apply (a : C) (c : C₀) (i : Fin 24) :
    ((shift a c : C) : Fin 24 → ZMod 2) i =
      ((c : C) : Fin 24 → ZMod 2) i + (a : Fin 24 → ZMod 2) i + μ₀ a := by
  rw [coe_shift]
  simp [Ω]

theorem spinCoord_conj_X (e : Parker) (x : SpinCoord) :
    (⟨e.sign, e.code, thetaD e.code⟩ : SpinCoord)⁻¹ * x * ⟨e.sign, e.code, thetaD e.code⟩ =
      ⟨θ e.code x.a + pair e.code x.δ, 0, 0⟩ * x := by
  rw [mul_s_zero]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, SpinCoord.inv_s, SpinCoord.inv_δ, SpinCoord.mul_δ,
      pair_add_right, pair_thetaD]
    linear_combination (norm := (ring_nf; try reduce_mod_char))
      (0 : ZMod 2) * two_eq_zero'
  · simp only [SpinCoord.mul_a, SpinCoord.inv_a]
    rw [add_comm e.code x.a, add_assoc, add_self_C', add_zero]
  · simp only [SpinCoord.mul_δ, SpinCoord.inv_δ]
    rw [add_comm (thetaD e.code) x.δ, add_assoc, add_self_cocode, add_zero]

theorem symm_XQ_conj (e : Parker) (t : Q) :
    spinEquiv.symm ((XQ e)⁻¹ * t * XQ e) =
      ⟨θ e.code (spinEquiv.symm t).a + pair e.code (spinEquiv.symm t).δ, 0, 0⟩ *
        spinEquiv.symm t :=
  have hX : spinEquiv.symm (XQ e) = ⟨e.sign, e.code, thetaD e.code⟩ :=
    (congrArg spinEquiv.symm (CFSG.Monster.SpinLattice.XQ_eq e)).trans
      (spinEquiv.symm_apply_apply _)
  calc spinEquiv.symm ((XQ e)⁻¹ * t * XQ e)
      = spinEquiv.symm (XQ e)⁻¹ * spinEquiv.symm t * spinEquiv.symm (XQ e) :=
        (map_mul spinEquiv.symm ((XQ e)⁻¹ * t) (XQ e)).trans
          (congrArg (· * spinEquiv.symm (XQ e)) (map_mul spinEquiv.symm (XQ e)⁻¹ t))
    _ = (spinEquiv.symm (XQ e))⁻¹ * spinEquiv.symm t * spinEquiv.symm (XQ e) :=
        congrArg (fun y => y * spinEquiv.symm t * spinEquiv.symm (XQ e))
          (map_inv spinEquiv.symm (XQ e))
    _ = (⟨e.sign, e.code, thetaD e.code⟩ : SpinCoord)⁻¹ * spinEquiv.symm t *
          ⟨e.sign, e.code, thetaD e.code⟩ :=
        congrArg (fun y => y⁻¹ * spinEquiv.symm t * y) hX
    _ = _ := spinCoord_conj_X e _

theorem Xlift_XQ_conj (e : Parker) (t : Q) :
    Xlift ((XQ e)⁻¹ * t * XQ e) =
      sgn (θ e.code (spinEquiv.symm t).a + pair e.code (spinEquiv.symm t).δ) • Xlift t :=
  Xlift_eq_sgn_smul_of_symm (symm_XQ_conj e t)

theorem symm_rMinus (i j : Fin 24) : spinEquiv.symm (rMinus i j) = ⟨0, 0, deltaPair i j⟩ := by
  rw [rMinus_eq]
  exact spinEquiv.symm_apply_apply _

theorem symm_rPlus (i j : Fin 24) : spinEquiv.symm (rPlus i j) = ⟨0, ΩC, deltaPair i j⟩ := by
  rw [rPlus_eq, thetaD_ΩC, zero_add]
  exact spinEquiv.symm_apply_apply _

theorem symm_rOdd (c : C₀) (i : Fin 24) :
    spinEquiv.symm (rOdd c i) =
      ⟨0, aOdd c i, thetaD (aOdd c i) + Submodule.Quotient.mk (Pi.single i 1)⟩ := by
  rw [rOdd_eq]
  exact spinEquiv.symm_apply_apply _

theorem symm_rOct (d : C) (δ : Finset (Fin 24)) :
    spinEquiv.symm (rOct d δ) =
      ⟨0, aOct d δ, thetaD (aOct d δ) + Submodule.Quotient.mk (Octad.ind δ)⟩ := by
  rw [rOct_eq]
  exact spinEquiv.symm_apply_apply _

theorem pair_deltaPair (a : C) (i j : Fin 24) :
    pair a (deltaPair i j) = (a : Fin 24 → ZMod 2) i + (a : Fin 24 → ZMod 2) j := by
  rw [deltaPair, pair_mk, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]

theorem pair_ΩC_deltaPair (i j : Fin 24) : pair ΩC (deltaPair i j) = 0 := by
  rw [pair_deltaPair, coe_ΩC]
  rfl

theorem pair_single (a : C) (i : Fin 24) :
    pair a (Submodule.Quotient.mk (Pi.single i 1)) = (a : Fin 24 → ZMod 2) i := by
  rw [pair_mk, dotProduct_single, mul_one]

theorem conjY_rMinus (e : Parker) (i j : Fin 24) :
    conjY e (spinEquiv.symm (rMinus i j)) =
      ⟨pair e.code (deltaPair i j), pair e.code (deltaPair i j) • ΩC, deltaPair i j⟩ := by
  rw [symm_rMinus, conjY_even e 0 (pair_ΩC_deltaPair i j)]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [θ_zero_left, zero_add]
  · simp only [θ_zero_right, zero_add]
  · simp only [Acocode_zero_right, zero_add]

theorem conjY_rPlus (e : Parker) (i j : Fin 24) :
    conjY e (spinEquiv.symm (rPlus i j)) =
      ⟨pair e.code (deltaPair i j), ΩC + pair e.code (deltaPair i j) • ΩC, deltaPair i j⟩ := by
  rw [symm_rPlus, conjY_even e ΩC (pair_ΩC_deltaPair i j)]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [θ_ΩC_left, zero_add]
  · simp only [θ_ΩC_right, zero_add]
  · simp only [Acocode_ΩC, zero_add]

theorem Xlift_conjYQ_rMinus_of_zero (e : Parker) {i j : Fin 24}
    (h : pair e.code (deltaPair i j) = 0) : Xlift (conjYQ e (rMinus i j)) = Xlift (rMinus i j) := by
  have h' := Xlift_conjYQ_of_conjY e (r := rMinus i j) (t := rMinus i j) (k := 0) (by
    rw [conjY_rMinus, h, symm_rMinus]
    refine SpinCoord.ext ?_ ?_ ?_ <;> simp)
  rw [h', sgn_zero, one_smul]

theorem Xlift_conjYQ_rPlus_of_zero (e : Parker) {i j : Fin 24}
    (h : pair e.code (deltaPair i j) = 0) : Xlift (conjYQ e (rPlus i j)) = Xlift (rPlus i j) := by
  have h' := Xlift_conjYQ_of_conjY e (r := rPlus i j) (t := rPlus i j) (k := 0) (by
    rw [conjY_rPlus, h, symm_rPlus]
    refine SpinCoord.ext ?_ ?_ ?_ <;> simp)
  rw [h', sgn_zero, one_smul]

theorem Xlift_conjYQ_rMinus_of_one (e : Parker) {i j : Fin 24}
    (h : pair e.code (deltaPair i j) = 1) : Xlift (conjYQ e (rMinus i j)) = -Xlift (rPlus i j) := by
  have h' := Xlift_conjYQ_of_conjY e (r := rMinus i j) (t := rPlus i j) (k := 1) (by
    rw [conjY_rMinus, h, symm_rPlus]
    refine SpinCoord.ext ?_ ?_ ?_ <;> simp)
  rw [h', show sgn 1 = -1 from rfl, neg_one_smul]

theorem Xlift_conjYQ_rPlus_of_one (e : Parker) {i j : Fin 24}
    (h : pair e.code (deltaPair i j) = 1) : Xlift (conjYQ e (rPlus i j)) = -Xlift (rMinus i j) := by
  have h' := Xlift_conjYQ_of_conjY e (r := rPlus i j) (t := rMinus i j) (k := 1) (by
    rw [conjY_rPlus, h, symm_rMinus]
    refine SpinCoord.ext ?_ ?_ ?_ <;> simp [add_self_C'])
  rw [h', show sgn 1 = -1 from rfl, neg_one_smul]

theorem θ_aOdd_left (c : C₀) (i : Fin 24) (f : C) : θ (aOdd c i) f = θ (c : C) f := by
  rw [aOdd, θ_add_smul_ΩC]

theorem θ_aOdd_right (a : C) (c : C₀) (i : Fin 24) : θ a (aOdd c i) = θ a (c : C) := by
  rw [aOdd, θ_right_add_smul_ΩC]

theorem pair_ΩC_rOdd_δ (c : C₀) (i : Fin 24) :
    pair ΩC (thetaD (aOdd c i) + Submodule.Quotient.mk (Pi.single i 1)) = 1 := by
  rw [map_add, pair_ΩC_thetaD, pair_single, coe_ΩC, zero_add]
  rfl

theorem mOdd_shift (a : C) (c : C₀) (i : Fin 24) :
    mOdd (shift a c) i = mOdd c i + (a : Fin 24 → ZMod 2) i + μ₀ a + P (a : Fin 24 → ZMod 2) +
      K ((c : C) : Fin 24 → ZMod 2) a := by
  rw [mOdd, mOdd, coe_shift_apply, P_coe_shift]
  ring

theorem conjY_rOdd (e : Parker) (c : C₀) (i : Fin 24) :
    conjY e (spinEquiv.symm (rOdd c i)) =
      ⟨e.sign + θ (c : C) e.code, 0, 0⟩ * spinEquiv.symm (rOdd (shift e.code c) i) := by
  rw [symm_rOdd, conjY_odd e _ (pair_ΩC_rOdd_δ c i), symm_rOdd, mul_s_zero]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [θ_aOdd_left, add_zero]
    ring
  · simp only [map_add, pair_thetaD, pair_single, θ_aOdd_left, θ_aOdd_right]
    have hK := θ_add_θ_swap e.code (c : C)
    have hcoef : mOdd c i + (θ e.code (c : C) + P (e.code : Fin 24 → ZMod 2) +
        (θ (c : C) e.code + (e.code : Fin 24 → ZMod 2) i)) =
          μ₀ e.code + mOdd (shift e.code c) i := by
      rw [mOdd_shift, K_comm]
      linear_combination (norm := (ring_nf; try reduce_mod_char)) hK
    calc aOdd c i + e.code + (θ e.code (c : C) + P (e.code : Fin 24 → ZMod 2) +
          (θ (c : C) e.code + (e.code : Fin 24 → ZMod 2) i)) • ΩC
        = (c : C) + e.code + (mOdd c i + (θ e.code (c : C) + P (e.code : Fin 24 → ZMod 2) +
          (θ (c : C) e.code + (e.code : Fin 24 → ZMod 2) i))) • ΩC := by
          rw [aOdd]
          module
      _ = (c : C) + e.code + (μ₀ e.code + mOdd (shift e.code c) i) • ΩC := by rw [hcoef]
      _ = aOdd (shift e.code c) i := by
          rw [aOdd, coe_shift]
          module
  · have e1 : aOdd (shift e.code c) i = ((c : C) + e.code) +
        (μ₀ e.code + mOdd (shift e.code c) i) • ΩC := by
      rw [aOdd, coe_shift]
      module
    rw [e1, thetaD_add_smul_ΩC, aOdd, Acocode_add_smul_ΩC, thetaD_add_smul_ΩC, thetaD_add,
      Acocode_comm]
    abel_nf

theorem Xlift_conjYQ_rOdd (e : Parker) (c : C₀) (i : Fin 24) :
    Xlift (conjYQ e (rOdd c i)) =
      sgn (e.sign + θ (c : C) e.code) • Xlift (rOdd (shift e.code c) i) :=
  Xlift_conjYQ_of_conjY e (conjY_rOdd e c i)

theorem ind_symmDiff (δ ε : Finset (Fin 24)) :
    Octad.ind (δ ∆ ε) = Octad.ind δ + Octad.ind ε := by
  funext k
  simp only [Octad.ind_apply, Pi.add_apply, Finset.mem_symmDiff]
  by_cases h1 : k ∈ δ <;> by_cases h2 : k ∈ ε <;> simp [h1, h2]
  rfl

theorem ind_inter_supp (d a : Fin 24 → ZMod 2) :
    Octad.ind (supp d ∩ supp a) = d * a := by
  funext k
  simp only [Octad.ind_apply, Finset.mem_inter, supp, Finset.mem_filter, Finset.mem_univ,
    true_and, Pi.mul_apply]
  rcases zmod2_cases (d k) with h1 | h1 <;> rcases zmod2_cases (a k) with h2 | h2 <;>
    simp [h1, h2]

theorem symmDiff_subset {d δ ε : Finset (Fin 24)} (hδ : δ ⊆ d) (hε : ε ⊆ d) : δ ∆ ε ⊆ d := by
  intro k hk
  rcases Finset.mem_symmDiff.1 hk with h | h
  · exact hδ h.1
  · exact hε h.1

theorem even_card_symmDiff {d δ ε : Finset (Fin 24)} (hδ : δ ⊆ d) (hδe : Even δ.card)
    (hε : ε ⊆ d) (hεe : Even ε.card) : Even (δ ∆ ε).card := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← Octad.sum_ind (symmDiff_subset hδ hε), ind_symmDiff]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [Octad.sum_ind hδ, Octad.sum_ind hε, (ZMod.natCast_eq_zero_iff_even).2 hδe,
    (ZMod.natCast_eq_zero_iff_even).2 hεe, add_zero]

theorem cls_symmDiff {d δ ε : Finset (Fin 24)} (hδ : δ ⊆ d) (hδe : Even δ.card)
    (hε : ε ⊆ d) (hεe : Even ε.card) :
    Octad.cls d (δ ∆ ε) = Octad.cls d δ + Octad.cls d ε := by
  rw [Octad.cls_eq (symmDiff_subset hδ hε) (even_card_symmDiff hδ hδe hε hεe),
    Octad.cls_eq hδ hδe, Octad.cls_eq hε hεe, ← map_add]
  congr 1
  exact Subtype.ext (ind_symmDiff δ ε)

@[expose] def octMeet (a : C) (d : OctadWord) : Finset (Fin 24) :=
  octSupp d ∩ supp (a : Fin 24 → ZMod 2)

theorem octMeet_subset (a : C) (d : OctadWord) : octMeet a d ⊆ octSupp d :=
  Finset.inter_subset_left

theorem even_card_octMeet (a : C) (d : OctadWord) : Even (octMeet a d).card := by
  rw [octMeet, supp_inter, card_supp]
  exact even_iff_two_dvd.2 (two_dvd_hammingNorm_mul (d : C).2 a.2)

theorem four_dvd_card_octSupp (d : OctadWord) : 4 ∣ (octSupp d).card := by
  rw [card_octSupp]
  norm_num

theorem K_eq_card_octMeet (a : C) (d : OctadWord) :
    K (a : Fin 24 → ZMod 2) ((d : C) : Fin 24 → ZMod 2) =
      (((octMeet a d).card / 2 : ℕ) : ZMod 2) := by
  rw [K, octMeet, Finset.inter_comm]

theorem dotProduct_ind (a : C) (d : OctadWord) {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d) :
    (a : Fin 24 → ZMod 2) ⬝ᵥ Octad.ind δ = ((δ ∩ octMeet a d).card : ZMod 2) := by
  have h1 : (a : Fin 24 → ZMod 2) ⬝ᵥ Octad.ind δ = ∑ k ∈ δ, (a : Fin 24 → ZMod 2) k :=
    Octad.sum_mul_ind _ (Finset.subset_univ δ)
  have h2 : δ ∩ octMeet a d = δ.filter fun k => (a : Fin 24 → ZMod 2) k ≠ 0 := by
    ext k
    rw [Finset.mem_inter, Finset.mem_filter, octMeet, Finset.mem_inter,
      CFSG.Monster.Griess.mem_supp_iff (d := (a : Fin 24 → ZMod 2))]
    exact ⟨fun ⟨h, _, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, hδ h, h'⟩⟩
  rw [h1, h2, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases zmod2_cases ((a : Fin 24 → ZMod 2) k) with h | h <;> simp [h]

theorem nOct_symmDiff (a : C) (d : OctadWord) {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    nOct (δ ∆ octMeet a d) = nOct δ + K (a : Fin 24 → ZMod 2) ((d : C) : Fin 24 → ZMod 2) +
      (a : Fin 24 → ZMod 2) ⬝ᵥ Octad.ind δ := by
  have h4 := four_dvd_card_octSupp d
  have hm := octMeet_subset a d
  have hme := even_card_octMeet a d
  rw [nOct, nOct, ← Octad.quadForm_cls h4 (symmDiff_subset hδ hm) (even_card_symmDiff hδ he hm hme),
    ← Octad.quadForm_cls h4 hδ he, cls_symmDiff hδ he hm hme, K_eq_card_octMeet,
    ← Octad.quadForm_cls h4 hm hme, dotProduct_ind a d hδ,
    ← Octad.polarBilin_quadForm_cls h4 hδ he hm hme, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar]
  ring

theorem pair_ΩC_rOct_δ (d : C) {δ : Finset (Fin 24)} (he : Even δ.card) :
    pair ΩC (thetaD (aOct d δ) + Submodule.Quotient.mk (Octad.ind δ)) = 0 := by
  rw [map_add, pair_ΩC_thetaD, pair_mk, zero_add, coe_ΩC]
  have h : Ω ⬝ᵥ Octad.ind δ = ∑ k ∈ δ, (1 : ZMod 2) :=
    Octad.sum_mul_ind _ (Finset.subset_univ δ)
  rw [h, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact (ZMod.natCast_eq_zero_iff_even).2 he

theorem conjY_rOct (e : Parker) (d : OctadWord) {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    conjY e (spinEquiv.symm (rOct d δ)) =
      ⟨(e.code : Fin 24 → ZMod 2) ⬝ᵥ Octad.ind δ, 0, 0⟩ *
        spinEquiv.symm (rOct d (δ ∆ octMeet e.code d)) := by
  rw [symm_rOct, conjY_even e _ (pair_ΩC_rOct_δ d he), symm_rOct, mul_s_zero]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [map_add, pair_thetaD, pair_mk, add_zero]
    linear_combination (norm := (ring_nf; try reduce_mod_char)) (0 : ZMod 2) * two_eq_zero'
  · simp only [map_add, pair_thetaD, pair_mk]
    have hK := θ_add_θ_swap e.code (aOct d δ)
    have hK' : K (e.code : Fin 24 → ZMod 2) ((aOct d δ : C) : Fin 24 → ZMod 2) =
        K (e.code : Fin 24 → ZMod 2) ((d : C) : Fin 24 → ZMod 2) := by
      rw [aOct, K_add_smul_ΩC_right]
    rw [hK'] at hK
    set T := θ e.code (aOct d δ) + (θ (aOct d δ) e.code +
        (e.code : Fin 24 → ZMod 2) ⬝ᵥ Octad.ind δ) with hT
    have hcoef : nOct δ + T = nOct (δ ∆ octMeet e.code d) := by
      rw [nOct_symmDiff e.code d hδ he, hT]
      linear_combination (norm := (ring_nf; try reduce_mod_char)) hK
    calc aOct (d : C) δ + T • ΩC = (d : C) + (nOct δ + T) • ΩC := by
          rw [aOct, add_assoc, ← add_smul]
      _ = aOct (d : C) (δ ∆ octMeet e.code d) := by rw [hcoef]; rfl
  · have hind : Octad.ind (δ ∆ octMeet e.code d) =
        Octad.ind δ + (e.code : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2) := by
      rw [ind_symmDiff, octMeet, ind_inter_supp, mul_comm]
    rw [aOct, aOct, Acocode_add_smul_ΩC, thetaD_add_smul_ΩC, thetaD_add_smul_ΩC, hind,
      Submodule.Quotient.mk_add, Acocode]
    abel_nf

theorem Xlift_conjYQ_rOct (e : Parker) (d : OctadWord) {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    Xlift (conjYQ e (rOct d δ)) =
      sgn ((e.code : Fin 24 → ZMod 2) ⬝ᵥ Octad.ind δ) • Xlift (rOct d (δ ∆ octMeet e.code d)) :=
  Xlift_conjYQ_of_conjY e (conjY_rOct e d hδ he)

end SignCompat

end CFSG.Monster.Visible
