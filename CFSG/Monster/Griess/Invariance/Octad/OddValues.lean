module

public import CFSG.Monster.Griess.Invariance.Octad.Basic
public import CFSG.Monster.Spin.FourierPauli

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess.OctadInv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix Module

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem f2_mul_add : ∀ x y : ZMod 2, y * (x + y) = x * y + y := by decide

private theorem f2_mul_add_one : ∀ x y : ZMod 2, y * (x + y + 1) = x * y := by decide

private theorem f2_sub_aux : ∀ p q t : ZMod 2, p * q - q * (p + q + t) = (1 + t) * q := by decide

theorem coe_cond {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC) :
    ((a : C) : Fin 24 → ZMod 2) + (b : C) = ((d : C) : Fin 24 → ZMod 2) + μ₀ d • Ω := by
  have h := congrArg (fun x : C => (x : Fin 24 → ZMod 2)) hc
  simpa only [Submodule.coe_add, Submodule.coe_smul, coe_ΩC] using h

theorem coord_of_cond {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC)
    (k : Fin 24) :
    ((d : C) : Fin 24 → ZMod 2) k =
      ((a : C) : Fin 24 → ZMod 2) k + ((b : C) : Fin 24 → ZMod 2) k + μ₀ d := by
  have h := congrFun (coe_cond hc) k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Ω, mul_one] at h
  rw [h, add_assoc, add_self_F2, add_zero]

theorem oct_eq_of_cond {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC) :
    (d : C) = (a : C) + b + μ₀ d • ΩC := by
  rw [hc, add_assoc, add_self_F2, add_zero]

theorem odd_eq_of_cond {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC) :
    (b : C) = (a : C) + d + μ₀ d • ΩC := by
  rw [add_assoc, ← hc, ← add_assoc, add_self_F2, zero_add]

theorem θ_add_smul_ΩC_left (x y : C) (t : ZMod 2) : θ (x + t • ΩC) y = θ x y := by
  rcases zmod2_cases t with rfl | rfl
  · rw [zero_smul, add_zero]
  · rw [one_smul]
    exact θ_add_Ω x y

theorem θ_add_smul_ΩC_right (x y : C) (t : ZMod 2) : θ x (y + t • ΩC) = θ x y := by
  rw [θ_add_right, θ_smul_right, θ_ΩC_right, mul_zero, add_zero]

theorem K_odd_odd {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC) :
    K ((a : C) : Fin 24 → ZMod 2) (b : C) =
      P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) := by
  have h1 := P_add (a : C).2 (b : C).2
  rw [coe_cond hc, P_add_smul_Ω (d : C).2, P_oct] at h1
  linear_combination -h1 - (P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2)) *
    two_eq_zero'

theorem θ_oct_odd {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC) :
    θ (d : C) (a : C) = θ (a : C) (b : C) + P ((b : C) : Fin 24 → ZMod 2) := by
  rw [oct_eq_of_cond hc, θ_add_smul_ΩC_left, θ_add_left, θ_self, θ_swap (a : C) (b : C),
    K_odd_odd hc, A_self_mid (a : C).2 (b : C).2]
  linear_combination (P ((a : C) : Fin 24 → ZMod 2)) * two_eq_zero'

theorem θ_oct_odd' {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC) :
    θ (d : C) (b : C) = θ (d : C) (a : C) := by
  rw [odd_eq_of_cond hc, θ_add_smul_ΩC_right, θ_add_right, θ_self, P_oct, add_zero]

@[expose] noncomputable def etaOf (b : C₀) (d : OctadWord) : Octad.EvenQuot (octSupp d) :=
  Octad.cls (octSupp d) (supp ((b : C) : Fin 24 → ZMod 2) ∩ octSupp d)

theorem inter_subset_octSupp (b : C₀) (d : OctadWord) :
    supp ((b : C) : Fin 24 → ZMod 2) ∩ octSupp d ⊆ octSupp d :=
  Finset.inter_subset_right

theorem card_supp_inter (x y : Fin 24 → ZMod 2) :
    (supp x ∩ supp y).card = hammingNorm (x * y) := by
  rw [supp_inter, card_supp]

theorem even_card_inter (b : C₀) (d : OctadWord) :
    Even (supp ((b : C) : Fin 24 → ZMod 2) ∩ octSupp d).card := by
  rw [card_supp_inter]
  exact even_iff_two_dvd.2 (two_dvd_hammingNorm_mul (b : C).2 (d : C).2)

theorem ind_inter_eq_mul (x y : Fin 24 → ZMod 2) : Octad.ind (supp x ∩ supp y) = x * y := by
  rw [supp_inter]
  exact Octad.ind_wordSupport (x * y)

theorem mul_oct_mem_evenSubsets (b : C₀) (d : OctadWord) :
    ((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2) ∈ Octad.evenSubsets (octSupp d) := by
  rw [← ind_inter_eq_mul]
  exact Octad.ind_mem_evenSubsets (inter_subset_octSupp b d) (even_card_inter b d)

theorem octMk_mul_oct (b : C₀) (d : OctadWord) :
    Octad.mk (octSupp d) ⟨((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2),
      mul_oct_mem_evenSubsets b d⟩ =
      etaOf b d := by
  have h := octMk_eq_cls (inter_subset_octSupp b d) (even_card_inter b d)
  have e : (⟨((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2),
      mul_oct_mem_evenSubsets b d⟩ :
      Octad.evenSubsets (octSupp d)) =
      ⟨Octad.ind (supp ((b : C) : Fin 24 → ZMod 2) ∩ octSupp d),
        Octad.ind_mem_evenSubsets (inter_subset_octSupp b d) (even_card_inter b d)⟩ :=
    Subtype.ext (ind_inter_eq_mul _ _).symm
  rw [e, h]
  rfl

theorem qd_etaOf {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC) :
    qd d (etaOf b d) = P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) := by
  rw [etaOf, Octad.quadForm_cls (four_dvd_card_octSupp d) (inter_subset_octSupp b d)
    (even_card_inter b d), card_supp_inter, ← K_odd_odd hc, K_eq]
  have hd := coord_of_cond hc
  have hev1 := two_dvd_hammingNorm_mul (b : C).2 (d : C).2
  have hev2 := two_dvd_hammingNorm_mul (a : C).2 (b : C).2
  have h4 := four_dvd_wt (b : C).2
  rcases zmod2_cases (μ₀ (d : C)) with ht | ht
  · have e : ((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2) =
        ((a : C) : Fin 24 → ZMod 2) * ((b : C) : Fin 24 → ZMod 2) + (b : C) := by
      funext k
      rw [Pi.mul_apply, hd k, ht, add_zero, Pi.add_apply, Pi.mul_apply]
      exact f2_mul_add _ _
    have h := Code.hammingNorm_add_add
      (((a : C) : Fin 24 → ZMod 2) * ((b : C) : Fin 24 → ZMod 2)) (b : C)
    have hab : ((a : C) : Fin 24 → ZMod 2) * ((b : C) : Fin 24 → ZMod 2) *
        ((b : C) : Fin 24 → ZMod 2) =
        ((a : C) : Fin 24 → ZMod 2) * ((b : C) : Fin 24 → ZMod 2) := by
      funext k
      simp only [Pi.mul_apply]
      rcases zmod2_cases (((b : C) : Fin 24 → ZMod 2) k) with h | h <;> rw [h] <;> ring
    rw [hab, ← e] at h
    rw [ZMod.natCast_eq_natCast_iff']
    omega
  · have e : ((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2) =
        ((a : C) : Fin 24 → ZMod 2) * ((b : C) : Fin 24 → ZMod 2) := by
      funext k
      rw [Pi.mul_apply, hd k, ht, Pi.mul_apply]
      exact f2_mul_add_one _ _
    rw [e]

theorem bd_etaOf_pair (b : C₀) (d : OctadWord) {i j : Fin 24} (hij : i ≠ j)
    (hi : i ∈ octSupp d) (hj : j ∈ octSupp d) :
    bd d (etaOf b d) (Octad.cls (octSupp d) {i, j}) =
      ((b : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j := by
  rw [etaOf, bd_cls (inter_subset_octSupp b d) (even_card_inter b d) (pair_subset_octSupp hi hj)
    (even_card_pair hij), card_inter_pair _ hij, ind_inter_eq_mul, Pi.mul_apply, Pi.mul_apply,
    coe_apply_eq_one hi, coe_apply_eq_one hj, mul_one, mul_one]

theorem bd_etaOf_octRep (b : C₀) (d : OctadWord) (w : Octad.EvenQuot (octSupp d)) :
    bd d (etaOf b d) w =
      ((supp ((b : C) : Fin 24 → ZMod 2) ∩ octRep d w).card : ZMod 2) := by
  conv_lhs => rw [← cls_octRep d w]
  rw [etaOf, bd_cls (inter_subset_octSupp b d) (even_card_inter b d) (octRep_subset d w)
    (octRep_even d w), Finset.inter_assoc, Finset.inter_eq_right.2 (octRep_subset d w)]

theorem pair_ind_card (b : C) (δ : Finset (Fin 24)) :
    pair b (Submodule.Quotient.mk (Octad.ind δ)) =
      ((supp (b : Fin 24 → ZMod 2) ∩ δ).card : ZMod 2) := by
  rw [pair_mk, dotProduct]
  conv_lhs => rw [← Octad.ind_wordSupport (b : Fin 24 → ZMod 2)]
  have h : ∀ i, Octad.ind (Octad.wordSupport (b : Fin 24 → ZMod 2)) i * Octad.ind δ i =
      Octad.ind (supp (b : Fin 24 → ZMod 2) ∩ δ) i := by
    intro i
    simp only [Octad.ind, ite_zero_mul_ite_zero, mul_one, Finset.mem_inter]
    rfl
  simp only [h]
  exact Octad.sum_ind (Finset.subset_univ _)

@[expose] noncomputable def oddOctVal (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) : ℚ :=
  open Classical in
  if (a : C) + b = d + μ₀ d • ΩC then
    (if i = j ∧ i ∉ octSupp d ∧ v = etaOf b d then sgn (θ (d : C) (a : C))
    else if i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
        v = etaOf b d + Octad.cls (octSupp d) {i, j} then
      sgn (θ (d : C) (a : C) + ((b : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j)
    else 0)
  else 0

theorem mOdd_eq (a : C₀) (i : Fin 24) :
    mOdd a i = ((a : C) : Fin 24 → ZMod 2) i + P ((a : C) : Fin 24 → ZMod 2) := rfl

theorem odd_fst_iff (a b : C₀) (d : OctadWord) (n m m' : ZMod 2) :
    (d : C) + n • ΩC = (a : C) + m • ΩC + ((b : C) + m' • ΩC) ↔
      ((a : C) + b = d + μ₀ d • ΩC ∧ n + m + m' = μ₀ d) := by
  have e : (a : C) + m • ΩC + ((b : C) + m' • ΩC) = (a : C) + b + (m + m') • ΩC := by
    rw [add_smul]
    abel
  rw [e]
  constructor
  · intro h
    have hab : (a : C) + b = d + (n + m + m') • ΩC := by
      calc (a : C) + b = (a : C) + b + (m + m') • ΩC + (m + m') • ΩC := by
            rw [add_assoc ((a : C) + b), add_self_F2, add_zero]
        _ = d + n • ΩC + (m + m') • ΩC := by rw [h]
        _ = d + (n + m + m') • ΩC := by rw [add_assoc, ← add_smul, add_assoc]
    have hμ := congrArg μ₀ hab
    rw [map_add, map_add, μ₀_coe, μ₀_coe, map_smul, μ₀_ΩC, smul_eq_mul, mul_one, add_zero] at hμ
    have ht : n + m + m' = μ₀ d := (add_eq_zero_iff'.1 hμ.symm)
    exact ⟨by rw [hab, ht], ht⟩
  · rintro ⟨hab, ht⟩
    have e2 : μ₀ (d : C) + (m + m') = n := by
      rw [← ht]
      linear_combination (m + m') * two_eq_zero'
    rw [hab, add_assoc, ← add_smul, e2]

theorem odd_snd_iff {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC)
    (x : Fin 24 → ZMod 2) (i j : Fin 24) :
    thetaD (d : C) + Submodule.Quotient.mk x =
        thetaD (a : C) + Submodule.Quotient.mk (Pi.single i 1) +
          (thetaD (b : C) + Submodule.Quotient.mk (Pi.single j 1)) ↔
      (Submodule.Quotient.mk (x + ((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2) +
        (Pi.single i 1 + Pi.single j 1)) : Cocode) = 0 := by
  have hθ : thetaD (d : C) = thetaD (a : C) + thetaD (b : C) + Acocode (a : C) (b : C) := by
    rw [oct_eq_of_cond hc, thetaD_add_smul_ΩC, thetaD_add]
  have hA : Acocode (a : C) (b : C) =
      Submodule.Quotient.mk (((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2)) := by
    rw [Acocode, Submodule.Quotient.eq]
    have hd := coord_of_cond hc
    have e : ((a : C) : Fin 24 → ZMod 2) * ((b : C) : Fin 24 → ZMod 2) -
        ((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2) =
        (1 + μ₀ (d : C)) • ((b : C) : Fin 24 → ZMod 2) := by
      funext k
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hd k]
      exact f2_sub_aux _ _ _
    rw [e]
    exact C.smul_mem _ (b : C).2
  rw [hθ, hA, eq_iff_add_eq_zero_F2]
  have e : thetaD (a : C) + thetaD (b : C) +
      Submodule.Quotient.mk (((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2)) +
        Submodule.Quotient.mk x +
      (thetaD (a : C) + Submodule.Quotient.mk (Pi.single i 1) +
        (thetaD (b : C) + Submodule.Quotient.mk (Pi.single j 1))) =
      (thetaD (a : C) + thetaD (a : C)) + (thetaD (b : C) + thetaD (b : C)) +
        (Submodule.Quotient.mk x +
          Submodule.Quotient.mk (((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2)) +
          (Submodule.Quotient.mk (Pi.single i 1) + Submodule.Quotient.mk (Pi.single j 1))) := by
    abel
  rw [e, add_self_F2, add_self_F2, zero_add, zero_add, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add]

theorem pair_oddLab (a b : C₀) (i j : Fin 24) :
    pair (oddLab b j).1.1 (oddLab a i).1.2 =
      θ (a : C) (b : C) + ((b : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j +
        P ((b : C) : Fin 24 → ZMod 2) := by
  simp only [oddLab_fst]
  rw [pair_add_smul_ΩC_thetaD, pair_mk, pair_mk, dotProduct_single, dotProduct_single, coe_ΩC,
    mOdd_eq]
  simp only [Ω, mul_one]
  ring

theorem cocode_cond_same (b : C₀) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    (Submodule.Quotient.mk (Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) *
      ((d : C) : Fin 24 → ZMod 2)) : Cocode) = 0 ↔ v = etaOf b d := by
  have hx : Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2) ∈
      Octad.evenSubsets (octSupp d) :=
    add_mem (ind_mem_octRep d v) (mul_oct_mem_evenSubsets b d)
  have e : Octad.mk (octSupp d) ⟨_, hx⟩ = v + etaOf b d := by
    calc Octad.mk (octSupp d) ⟨_, hx⟩ =
        Octad.mk (octSupp d) ⟨Octad.ind (octRep d v), ind_mem_octRep d v⟩ +
          Octad.mk (octSupp d) ⟨((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2),
            mul_oct_mem_evenSubsets b d⟩ := by
          rw [← map_add]
          rfl
      _ = v + etaOf b d := by rw [octMk_octRep, octMk_mul_oct]
  calc (Submodule.Quotient.mk (Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) *
        ((d : C) : Fin 24 → ZMod 2)) : Cocode) = 0 ↔ Octad.mk (octSupp d) ⟨_, hx⟩ = 0 :=
        mk_eq_zero_iff_octMk_eq_zero ⟨_, hx⟩
    _ ↔ v = etaOf b d := by rw [e, ← eq_iff_add_eq_zero_F2]

theorem cocode_cond_pair (b : C₀) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) {i j : Fin 24}
    (hij : i ≠ j) (hi : i ∈ octSupp d) (hj : j ∈ octSupp d) :
    (Submodule.Quotient.mk (Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) *
      ((d : C) : Fin 24 → ZMod 2) + (Pi.single i 1 + Pi.single j 1)) : Cocode) = 0 ↔
      v = etaOf b d + Octad.cls (octSupp d) {i, j} := by
  have hpair := Octad.ind_mem_evenSubsets (pair_subset_octSupp hi hj) (even_card_pair hij)
  have hx : Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2) +
      Octad.ind {i, j} ∈ Octad.evenSubsets (octSupp d) :=
    add_mem (add_mem (ind_mem_octRep d v) (mul_oct_mem_evenSubsets b d)) hpair
  have e : Octad.mk (octSupp d) ⟨_, hx⟩ = v + etaOf b d + Octad.cls (octSupp d) {i, j} := by
    calc Octad.mk (octSupp d) ⟨_, hx⟩ =
        Octad.mk (octSupp d) ⟨Octad.ind (octRep d v), ind_mem_octRep d v⟩ +
          Octad.mk (octSupp d) ⟨((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2),
            mul_oct_mem_evenSubsets b d⟩ +
          Octad.mk (octSupp d) ⟨Octad.ind {i, j}, hpair⟩ := by
          rw [← map_add, ← map_add]
          rfl
      _ = v + etaOf b d + Octad.cls (octSupp d) {i, j} := by
          rw [octMk_octRep, octMk_mul_oct,
            octMk_eq_cls (pair_subset_octSupp hi hj) (even_card_pair hij)]
  rw [← ind_pair hij]
  calc (Submodule.Quotient.mk (Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) *
        ((d : C) : Fin 24 → ZMod 2) + Octad.ind {i, j}) : Cocode) = 0 ↔
        Octad.mk (octSupp d) ⟨_, hx⟩ = 0 := mk_eq_zero_iff_octMk_eq_zero ⟨_, hx⟩
    _ ↔ v = etaOf b d + Octad.cls (octSupp d) {i, j} := by
        rw [e, add_assoc, ← eq_iff_add_eq_zero_F2]

theorem cocode_cond_out (b : C₀) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) {i j : Fin 24}
    (hij : i ≠ j) (hout : ¬(i ∈ octSupp d ∧ j ∈ octSupp d)) :
    (Submodule.Quotient.mk (Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) *
      ((d : C) : Fin 24 → ZMod 2) + (Pi.single i 1 + Pi.single j 1)) : Cocode) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  refine not_mem_C_of_outside hij (fun k hk => ?_) hout
  rw [Pi.add_apply, Pi.add_apply, Pi.mul_apply, coe_apply_eq_zero hk, mul_zero, add_zero,
    Octad.ind_apply, ite_eq_right fun h => hk (octRep_subset d v h), zero_add]

theorem qd_pair {d : OctadWord} {i j : Fin 24} (hij : i ≠ j) (hi : i ∈ octSupp d)
    (hj : j ∈ octSupp d) : qd d (Octad.cls (octSupp d) {i, j}) = 1 := by
  rw [Octad.quadForm_cls (four_dvd_card_octSupp d) (pair_subset_octSupp hi hj)
    (even_card_pair hij), Finset.card_pair hij]
  rfl

theorem odd_oct_cond_iff (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    (octLab ⟨d, v⟩).1 = (oddLab a i).1 + (oddLab b j).1 ↔
      ((a : C) + b = d + μ₀ d • ΩC ∧ nOct (octRep d v) + mOdd a i + mOdd b j = μ₀ d) ∧
        thetaD (d : C) + Submodule.Quotient.mk (Octad.ind (octRep d v)) =
          thetaD (a : C) + Submodule.Quotient.mk (Pi.single i 1) +
            (thetaD (b : C) + Submodule.Quotient.mk (Pi.single j 1)) := by
  rw [octLab_fst, oddLab_fst, oddLab_fst, Prod.mk_add_mk, Prod.mk.injEq, odd_fst_iff]

theorem odd_oct_cond_iff' {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC)
    (i j : Fin 24) (v : Octad.EvenQuot (octSupp d)) :
    (octLab ⟨d, v⟩).1 = (oddLab a i).1 + (oddLab b j).1 ↔
      nOct (octRep d v) + mOdd a i + mOdd b j = μ₀ d ∧
        (Submodule.Quotient.mk (Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) *
          ((d : C) : Fin 24 → ZMod 2) + (Pi.single i 1 + Pi.single j 1)) : Cocode) = 0 := by
  rw [odd_oct_cond_iff, odd_snd_iff hc]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hc, h.1⟩, h.2⟩⟩

theorem tau_odd_oct_of_not {a b : C₀} {d : OctadWord} (hc : ¬(a : C) + b = d + μ₀ d • ΩC)
    (i j : Fin 24) (v : Octad.EvenQuot (octSupp d)) :
    tau (oddLab a i) (oddLab b j) (octLab ⟨d, v⟩) = 0 := by
  rw [tau_eq, ite_eq_right fun h => hc ((odd_oct_cond_iff a b i j d v).1 h).1.1]

theorem nOct_add_mOdd_same {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC)
    (i : Fin 24) : qd d (etaOf b d) + mOdd a i + mOdd b i =
      ((d : C) : Fin 24 → ZMod 2) i + μ₀ d := by
  rw [qd_etaOf hc, mOdd_eq, mOdd_eq, coord_of_cond hc i]
  linear_combination (P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) -
    μ₀ (d : C)) * two_eq_zero'

theorem tau_odd_oct_same {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC)
    (i : Fin 24) (v : Octad.EvenQuot (octSupp d)) :
    tau (oddLab a i) (oddLab b i) (octLab ⟨d, v⟩) =
      if i ∉ octSupp d ∧ v = etaOf b d then sgn (θ (d : C) (a : C)) else 0 := by
  have hcond := odd_oct_cond_iff' hc i i v
  rw [add_self_F2 (Pi.single i (1 : ZMod 2) : Fin 24 → ZMod 2),
    add_zero (Octad.ind (octRep d v) + ((b : C) : Fin 24 → ZMod 2) * ((d : C) : Fin 24 → ZMod 2)),
    cocode_cond_same] at hcond
  rw [tau_eq, pair_oddLab]
  by_cases hv : v = etaOf b d
  · have hsum : nOct (octRep d v) + mOdd a i + mOdd b i =
        ((d : C) : Fin 24 → ZMod 2) i + μ₀ d := by
      rw [nOct_octRep, hv]
      exact nOct_add_mOdd_same hc i
    by_cases hi : i ∈ octSupp d
    · have hL : ¬((octLab ⟨d, v⟩).1 = (oddLab a i).1 + (oddLab b i).1) := fun h => by
        have h2 := (hcond.1 h).1
        rw [hsum, coe_apply_eq_one hi] at h2
        exact one_ne_zero (by linear_combination h2 : (1 : ZMod 2) = 0)
      have hR : ¬(i ∉ octSupp d ∧ v = etaOf b d) := fun h => h.1 hi
      rw [ite_eq_right hL, ite_eq_right hR]
    · have hL : (octLab ⟨d, v⟩).1 = (oddLab a i).1 + (oddLab b i).1 :=
        hcond.2 ⟨by rw [hsum, coe_apply_eq_zero hi, zero_add], hv⟩
      have hR : i ∉ octSupp d ∧ v = etaOf b d := ⟨hi, hv⟩
      rw [ite_eq_left hL, ite_eq_left hR, θ_oct_odd hc]
      exact congrArg sgn (by linear_combination (((b : C) : Fin 24 → ZMod 2) i) * two_eq_zero')
  · have hL : ¬((octLab ⟨d, v⟩).1 = (oddLab a i).1 + (oddLab b i).1) :=
      fun h => hv (hcond.1 h).2
    have hR : ¬(i ∉ octSupp d ∧ v = etaOf b d) := fun h => hv h.2
    rw [ite_eq_right hL, ite_eq_right hR]

theorem nOct_add_mOdd_pair {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC)
    {i j : Fin 24} (hij : i ≠ j) (hi : i ∈ octSupp d) (hj : j ∈ octSupp d) :
    qd d (etaOf b d + Octad.cls (octSupp d) {i, j}) + mOdd a i + mOdd b j = μ₀ d := by
  have hdi := coord_of_cond hc i
  rw [coe_apply_eq_one hi] at hdi
  rw [qd_add, qd_etaOf hc, qd_pair hij hi hj, bd_etaOf_pair b d hij hi hj, mOdd_eq, mOdd_eq]
  linear_combination hdi + (P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
    ((b : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j +
    ((a : C) : Fin 24 → ZMod 2) i) * two_eq_zero'

theorem tau_odd_oct_pair_in {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC)
    {i j : Fin 24} (hij : i ≠ j) (hi : i ∈ octSupp d) (hj : j ∈ octSupp d)
    (v : Octad.EvenQuot (octSupp d)) :
    tau (oddLab a i) (oddLab b j) (octLab ⟨d, v⟩) =
      if v = etaOf b d + Octad.cls (octSupp d) {i, j} then
        sgn (θ (d : C) (a : C) + ((b : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j)
      else 0 := by
  have hcond := odd_oct_cond_iff' hc i j v
  rw [cocode_cond_pair b d v hij hi hj] at hcond
  rw [tau_eq, pair_oddLab]
  by_cases hv : v = etaOf b d + Octad.cls (octSupp d) {i, j}
  · have hsum : nOct (octRep d v) + mOdd a i + mOdd b j = μ₀ d := by
      rw [nOct_octRep, hv]
      exact nOct_add_mOdd_pair hc hij hi hj
    rw [ite_eq_left (hcond.2 ⟨hsum, hv⟩), ite_eq_left hv, θ_oct_odd hc]
    exact congrArg sgn (by ring)
  · rw [ite_eq_right (fun h => hv (hcond.1 h).2), ite_eq_right hv]

theorem tau_odd_oct_pair_out {a b : C₀} {d : OctadWord} (hc : (a : C) + b = d + μ₀ d • ΩC)
    {i j : Fin 24} (hij : i ≠ j) (hout : ¬(i ∈ octSupp d ∧ j ∈ octSupp d))
    (v : Octad.EvenQuot (octSupp d)) :
    tau (oddLab a i) (oddLab b j) (octLab ⟨d, v⟩) = 0 := by
  rw [tau_eq, ite_eq_right fun h =>
    cocode_cond_out b d v hij hout ((odd_oct_cond_iff' hc i j v).1 h).2]

theorem T_sect0_sect0_oct (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (sectVec a i 0) (sectVec b j 0) (octVec ⟨d, v⟩) = oddOctVal a b i j d v := by
  rw [sectVec_zero, sectVec_zero, octVec_eq, T_sgl3, oddOctVal]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [ite_eq_left hc]
    by_cases hij : i = j
    · subst hij
      rw [tau_odd_oct_same hc,
        ite_eq_right (show ¬(i ≠ i ∧ i ∈ octSupp d ∧ i ∈ octSupp d ∧
          v = etaOf b d + Octad.cls (octSupp d) {i, i}) from fun h => h.1 rfl)]
      by_cases h : i ∉ octSupp d ∧ v = etaOf b d
      · rw [ite_eq_left h, ite_eq_left (show i = i ∧ i ∉ octSupp d ∧ v = etaOf b d from
          ⟨rfl, h⟩)]
      · rw [ite_eq_right h, ite_eq_right (show ¬(i = i ∧ i ∉ octSupp d ∧ v = etaOf b d) from
          fun h' => h h'.2)]
    · rw [ite_eq_right (show ¬(i = j ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hij h.1)]
      by_cases hin : i ∈ octSupp d ∧ j ∈ octSupp d
      · rw [tau_odd_oct_pair_in hc hij hin.1 hin.2]
        by_cases hv : v = etaOf b d + Octad.cls (octSupp d) {i, j}
        · rw [ite_eq_left hv, ite_eq_left (show i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
            v = etaOf b d + Octad.cls (octSupp d) {i, j} from ⟨hij, hin.1, hin.2, hv⟩)]
        · rw [ite_eq_right hv, ite_eq_right (show ¬(i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
            v = etaOf b d + Octad.cls (octSupp d) {i, j}) from fun h => hv h.2.2.2)]
      · rw [tau_odd_oct_pair_out hc hij hin, ite_eq_right (show ¬(i ≠ j ∧ i ∈ octSupp d ∧
          j ∈ octSupp d ∧ v = etaOf b d + Octad.cls (octSupp d) {i, j}) from
            fun h => hin ⟨h.2.1, h.2.2.1⟩)]
  · rw [tau_odd_oct_of_not hc, ite_eq_right hc]

theorem shift_add_smul_ΩC (x : C) (n : ZMod 2) (c : C₀) : shift (x + n • ΩC) c = shift x c := by
  rw [shift_add]
  rcases zmod2_cases n with rfl | rfl
  · rw [zero_smul, shift_zero]
  · rw [one_smul, shift_ΩC]

theorem shift_oct_eq_iff (a b : C₀) (d : OctadWord) :
    shift (d : C) a = b ↔ (a : C) + b = d + μ₀ d • ΩC := by
  have e : (a : C) + d + μ₀ (d : C) • ΩC + b = (a : C) + b + ((d : C) + μ₀ (d : C) • ΩC) := by
    abel
  rw [Subtype.ext_iff, coe_shift, eq_iff_add_eq_zero_F2, e, ← eq_iff_add_eq_zero_F2]

theorem coe_rOctQ (d : OctadWord) (w : Octad.EvenQuot (octSupp d)) :
    ((rOctQ d w : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      qmatR ℚ 0 ((d : C) + nOct (octRep d w) • ΩC)
        (thetaD (d : C) + Submodule.Quotient.mk (Octad.ind (octRep d w))) := by
  rw [coe_Q_eq]
  have h1 : centralCoord (rOctQ d w) = 0 := centralCoord_rOct _ _
  have h2 : coordOf (rOctQ d w) = ((d : C) + nOct (octRep d w) • ΩC,
      thetaD (d : C) + Submodule.Quotient.mk (Octad.ind (octRep d w))) := octLab_fst d w
  rw [h1, h2]

theorem E_vecMul_oct_dotProduct (η : ZMod 2) (a b : C₀) (d : OctadWord)
    (w : Octad.EvenQuot (octSupp d)) :
    (Spin.E η a ᵥ* ((rOctQ d w : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ Spin.E η b =
      if (a : C) + b = d + μ₀ d • ΩC then
        sgn (η * (μ₀ (d : C) + qd d w) + θ (d : C) (b : C) + bd d (etaOf b d) w) else 0 := by
  have hpΩ : pair ΩC (thetaD (d : C) + Submodule.Quotient.mk (Octad.ind (octRep d w))) = 0 := by
    rw [pair_add_right, pair_ΩC_thetaD, pair_ΩC_ind (octRep_even d w), add_zero]
  have hμ : μ₀ ((d : C) + nOct (octRep d w) • ΩC) = μ₀ (d : C) + qd d w := by
    rw [map_add, map_smul, μ₀_ΩC, smul_eq_mul, mul_one, nOct_octRep]
  rw [coe_rOctQ, E_vecMul_qmatR, smul_dotProduct, E_dotProduct_E, smul_eq_mul, hpΩ, add_zero,
    shift_add_smul_ΩC, hμ, zero_add]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · have hb := (shift_oct_eq_iff a b d).2 hc
    rw [hb, ite_eq_left rfl, ite_eq_left hc, mul_one, pair_add_right, pair_thetaD, pair_ind_card,
      ← bd_etaOf_octRep, add_assoc]
  · rw [ite_eq_right (fun h => hc ((shift_oct_eq_iff a b d).1 (congrArg Prod.snd h))),
      mul_zero, ite_eq_right hc]

theorem isShortCoord_rOctQ (d : OctadWord) (w : Octad.EvenQuot (octSupp d)) :
    IsShortCoord (coordOf (rOctQ d w)) :=
  isShortCoord_labelElt (.inr (.inr (.inr ⟨d, w⟩)))

theorem octVec_eq_Xlift (d : OctadWord) (w : Octad.EvenQuot (octSupp d)) :
    octVec ⟨d, w⟩ = inX (Xlift (rOctQ d w)) :=
  tbasis_oct ⟨d, w⟩

theorem sectVec_one (a : C₀) (i : Fin 24) :
    sectVec a i 1 =
      inW (tensor (sgn (((a : C) : Fin 24 → ZMod 2) i) • Spin.E 1 a) (Pi.single i 1)) := by
  show tbasis (.inr (.inr (.inl (a, i, 1)))) = _
  rw [tbasis_odd_one]
  show ((0 : symMat), (0 : SpaceX), sgn (((a : C) : Fin 24 → ZMod 2) i) •
    tensor (Spin.E 1 a) (Pi.single i 1)) = ((0 : symMat), (0 : SpaceX),
      tensor (sgn (((a : C) : Fin 24 → ZMod 2) i) • Spin.E 1 a) (Pi.single i 1))
  rw [tensor, tensor, smul_vecMulVec]

theorem sectVec_two (a : C₀) (i : Fin 24) :
    sectVec a i 2 =
      inW (tensor (sgn (P ((a : C) : Fin 24 → ZMod 2)) • Spin.E 0 a) (Pi.single i 1)) := by
  show tbasis (.inr (.inr (.inl (a, i, 2)))) = _
  rw [tbasis_odd_two]
  show ((0 : symMat), (0 : SpaceX), sgn (P ((a : C) : Fin 24 → ZMod 2)) •
    tensor (Spin.E 0 a) (Pi.single i 1)) = ((0 : symMat), (0 : SpaceX),
      tensor (sgn (P ((a : C) : Fin 24 → ZMod 2)) • Spin.E 0 a) (Pi.single i 1))
  rw [tensor, tensor, smul_vecMulVec]

@[expose] noncomputable def oddBr (i j : Fin 24) (d : OctadWord) (w : Octad.EvenQuot (octSupp d)) :
    ℚ :=
  ((if i = j then 1 else 0) - uQ (octLab ⟨d, w⟩) i * uQ (octLab ⟨d, w⟩) j / 4) / 8

theorem T_sect1_sect1_oct (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (w : Octad.EvenQuot (octSupp d)) :
    T (sectVec a i 1) (sectVec b j 1) (octVec ⟨d, w⟩) =
      (if (a : C) + b = d + μ₀ d • ΩC then
        sgn (((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j + μ₀ (d : C) +
          qd d w + θ (d : C) (b : C) + bd d (etaOf b d) w) else 0) * oddBr i j d w := by
  rw [sectVec_one, sectVec_one, octVec_eq_Xlift, T_tensor_tensor_Xlift _ _ _ _
    (isShortCoord_rOctQ d w), smul_vecMul, smul_dotProduct, dotProduct_smul,
    E_vecMul_oct_dotProduct, single_dotProduct_single, single_dotProduct, single_dotProduct,
    one_mul, one_mul, smul_eq_mul, smul_eq_mul, oddBr]
  have e : (⟨coordOf (rOctQ d w), isShortCoord_rOctQ d w⟩ : ShortIdx) = octLab ⟨d, w⟩ := rfl
  rw [e]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [ite_eq_left hc, ite_eq_left hc, one_mul]
    simp only [sgn_add]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]
    ring

theorem T_sect2_sect2_oct (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (w : Octad.EvenQuot (octSupp d)) :
    T (sectVec a i 2) (sectVec b j 2) (octVec ⟨d, w⟩) =
      (if (a : C) + b = d + μ₀ d • ΩC then
        sgn (P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
          θ (d : C) (b : C) + bd d (etaOf b d) w) else 0) * oddBr i j d w := by
  rw [sectVec_two, sectVec_two, octVec_eq_Xlift, T_tensor_tensor_Xlift _ _ _ _
    (isShortCoord_rOctQ d w), smul_vecMul, smul_dotProduct, dotProduct_smul,
    E_vecMul_oct_dotProduct, single_dotProduct_single, single_dotProduct, single_dotProduct,
    one_mul, one_mul, smul_eq_mul, smul_eq_mul, oddBr]
  have e : (⟨coordOf (rOctQ d w), isShortCoord_rOctQ d w⟩ : ShortIdx) = octLab ⟨d, w⟩ := rfl
  rw [e]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [ite_eq_left hc, ite_eq_left hc, zero_mul, zero_add]
    simp only [sgn_add]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]
    ring

end CFSG.Monster.Griess.OctadInv
