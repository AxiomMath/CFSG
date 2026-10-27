module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessDickson
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessTrace
import CFSG.Dihedral.Glauberman.DicksonMaxCases

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {k : Type} [Field k]

noncomputable abbrev pslMk (k : Type) [Field k] : SL(2, k) →* PSL2MatrixGroup k :=
  QuotientGroup.mk' (Subgroup.center SL(2, k))

theorem pslMk_eq_one_iff (h2 : (2 : k) ≠ 0) (x : SL(2, k)) :
    pslMk k x = 1 ↔ x = 1 ∨ x = -1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hx⟩
    rw [Fintype.card_fin] at hr
    have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp hr' with h | h
    · left
      ext i j
      rw [← hx, show r = 1 by linear_combination h]
      simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal]
    · right
      ext i j
      rw [← hx, show r = -1 by linear_combination h]
      simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal]
      split_ifs <;> simp
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      ext i j
      simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal]
      split_ifs <;> simp

theorem card_eq_two_mul_card_map (h2 : (2 : k) ≠ 0) {L : Subgroup SL(2, k)}
    (hL : (-1 : SL(2, k)) ∈ L) : Nat.card L = 2 * Nat.card (L.map (pslMk k)) := by
  classical
  set φ := (pslMk k).comp L.subtype with hφ
  have hrange : φ.range = L.map (pslMk k) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange] at hcard
  have hne : (-1 : SL(2, k)) ≠ 1 := by
    intro h
    have := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
    simp at this
    apply h2
    linear_combination -this
  have hker : Nat.card φ.ker = 2 := by
    have : (φ.ker : Set L) = {1, ⟨-1, hL⟩} := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, hφ, MonoidHom.comp_apply,
        Subgroup.coe_subtype, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [pslMk_eq_one_iff h2]
      constructor
      · rintro (h | h)
        · left; exact Subtype.ext h
        · right; exact Subtype.ext h
      · rintro (h | h)
        · left; rw [h]; rfl
        · right; rw [h]
    rw [← SetLike.coe_sort_coe, this, Nat.card_eq_fintype_card, Set.card_insert,
      Set.card_singleton]
    · simp only [Set.mem_singleton_iff]
      intro h
      exact hne (congrArg Subtype.val h).symm
  rw [hcard, hker, mul_comm]

variable [Finite k] {p f : ℕ} [hp : Fact p.Prime] [CharP k p]

theorem closure_eq_of_dickson (hp5 : 5 ≤ p) (hk : Nat.card k = p ^ f)
    (G : Subgroup SL(2, k)) (hG : Nat.card G ≤ p * (p ^ 2 - 1))
    {g δ : SL(2, k)} (hgG : g ∈ G) (hδG : δ ∈ G) (hnG : (-1 : SL(2, k)) ∈ G)
    (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1)
    (hg : ∀ j : ℕ, 1 ≤ j → j ≤ 5 → g ^ j ≠ 1 ∧ g ^ j ≠ -1)
    (htr2 : ((δ * g * δ⁻¹ * g⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k).trace ≠ 2)
    (htr2' : ((δ * g * δ⁻¹ * g⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k).trace ≠ -2) :
    Subgroup.closure {g, δ, -1} = G := by
  classical
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff k p 2).mp h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  set L := Subgroup.closure ({g, δ, -1} : Set SL(2, k)) with hL
  have hLG : L ≤ G := by
    rw [hL, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hgG
    · exact hδG
    · exact hnG
  have hgL : g ∈ L := Subgroup.subset_closure (by simp)
  have hδL : δ ∈ L := Subgroup.subset_closure (by simp)
  have hnL : (-1 : SL(2, k)) ∈ L := Subgroup.subset_closure (by simp)
  set π := pslMk k with hπ
  set H := L.map π with hH
  set gH : H := ⟨π g, Subgroup.mem_map_of_mem _ hgL⟩
  set δH : H := ⟨π δ, Subgroup.mem_map_of_mem _ hδL⟩
  have hpowH : ∀ (x : SL(2, k)) (hx : x ∈ L) (j : ℕ),
      ((⟨π x, Subgroup.mem_map_of_mem _ hx⟩ : H) ^ j = 1 ↔ x ^ j = 1 ∨ x ^ j = -1) := by
    intro x hx j
    rw [← pslMk_eq_one_iff h2, map_pow, Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one]
  have hneg1 : (-1 : SL(2, k)) ≠ 1 := by
    intro h
    have := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
    simp at this
    apply h2
    linear_combination -this
  have hδn : δ ≠ -1 := by
    intro h
    rw [h] at hδ3
    have : ((-1 : SL(2, k)) ^ 3) = -1 := by
      rw [pow_succ, pow_two]
      ext i j
      simp [Matrix.mul_apply]
    exact hneg1 (this.symm.trans hδ3)
  have hord : ∀ z : H, (∀ j, 1 ≤ j → j ≤ 2 → z ^ j ≠ 1) → 2 < orderOf z := by
    intro z hz
    have hpos : 0 < orderOf z := orderOf_pos z
    by_contra hle
    push Not at hle
    exact hz (orderOf z) hpos hle (pow_orderOf_eq_one z)
  have hδ2 : δ ^ 2 ≠ 1 ∧ δ ^ 2 ≠ -1 := by
    constructor
    · intro h
      apply hδ1
      calc δ = δ ^ 3 * (δ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hδ3, h, inv_one, one_mul]
    · intro h
      apply hδn
      calc δ = δ ^ 3 * (δ ^ 2)⁻¹ := by group
        _ = -1 := by
          rw [hδ3, h, one_mul]
          ext i j
          simp [Matrix.inv_def]
  have hδH : 2 < orderOf δH := by
    refine hord δH (fun j hj1 hj2 h => ?_)
    rcases (hpowH δ hδL j).mp h with h' | h'
    · interval_cases j
      · exact hδ1 (by simpa using h')
      · exact hδ2.1 h'
    · interval_cases j
      · exact hδn (by simpa using h')
      · exact hδ2.2 h'
  have hgpow : ∀ j, 1 ≤ j → j ≤ 5 → gH ^ j ≠ 1 := by
    intro j hj1 hj5 h
    rcases (hpowH g hgL j).mp h with h' | h'
    · exact (hg j hj1 hj5).1 h'
    · exact (hg j hj1 hj5).2 h'
  have hgH : 2 < orderOf gH := hord gH (fun j hj1 hj2 => hgpow j hj1 (by omega))
  set c := δ * g * δ⁻¹ * g⁻¹ with hc
  have hcL : c ∈ L := mul_mem (mul_mem (mul_mem hδL hgL) (inv_mem hδL)) (inv_mem hgL)
  have hcH : δH * gH * δH⁻¹ * gH⁻¹ = ⟨π c, Subgroup.mem_map_of_mem _ hcL⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc, map_mul, map_inv]
    rfl
  have htr1 : ((1 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k).trace = 2 := by
    simp [Matrix.trace_fin_two]
  have htrn : ((-1 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k).trace = -2 := by
    simp [Matrix.trace_fin_two]
  have hxy : δH * gH ≠ gH * δH := by
    intro h
    have h1 : δH * gH * δH⁻¹ * gH⁻¹ = 1 := by
      rw [h]; group
    rw [hcH] at h1
    have h1' : (⟨π c, Subgroup.mem_map_of_mem _ hcL⟩ : H) ^ 1 = 1 := by rw [pow_one]; exact h1
    rcases (hpowH c hcL 1).mp h1' with h' | h'
    · rw [pow_one] at h'
      exact htr2 (by rw [h', htr1])
    · rw [pow_one] at h'
      exact htr2' (by rw [h', htrn])
  rcases dickson_large hk H hδH hgH hxy (hgpow 2 (by norm_num) (by norm_num))
      (hgpow 3 (by norm_num) (by norm_num)) (hgpow 4 (by norm_num) (by norm_num))
      (hgpow 5 (by norm_num) (by norm_num)) (by
        intro N hN hNel hall
        have hcN := hall δH gH
        have hexp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hNel.exponent_dvd_p ⟨_, hcN⟩
        have hc' : (δH * gH * δH⁻¹ * gH⁻¹) ^ p = 1 := by
          have := congrArg Subtype.val hexp
          simpa using this
        rw [hcH] at hc'
        have hcp : c ^ (2 * p) = 1 := by
          rcases (hpowH c hcL p).mp hc' with h' | h'
          · rw [pow_mul', h', one_pow]
          · rw [pow_mul', h']
            ext i j
            simp [sq]
        have hm : ((c : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) ^ (2 * p) = 1 := by
          have := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k)) hcp
          simpa using this
        rcases trace_eq_two_or_neg_two (p := p) hp2 (c.2) hm with h' | h'
        · exact htr2 h'
        · exact htr2' h') with
    ⟨m, hm0, hmf, ⟨eH⟩⟩ | ⟨m, hm0, hmf, ⟨eH⟩⟩
  ·
    have hcardH : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr eH.toEquiv]
      exact CFSG.Glauberman.Dickson.MaxCases.card_psl2_galoisField' hp2 hm0
    have hLcard := card_eq_two_mul_card_map h2 hnL
    have hodd : 2 ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
      have hpo : Odd (p ^ m) := (hp.out.odd_of_ne_two hp2).pow
      obtain ⟨t, ht⟩ := hpo
      refine Dvd.dvd.mul_left ?_ _
      rw [ht]
      refine ⟨2 * t ^ 2 + 2 * t, ?_⟩
      ring_nf
      omega
    have hL2 : Nat.card L = p ^ m * ((p ^ m) ^ 2 - 1) := by
      rw [hLcard, ← hH, hcardH, Nat.mul_div_cancel' hodd]
    have hLle : Nat.card L ≤ Nat.card G := Subgroup.card_le_of_le hLG
    have hpm : p ^ m ≤ p := by
      by_contra hlt
      push Not at hlt
      have h1 : p * (p ^ 2 - 1) < p ^ m * ((p ^ m) ^ 2 - 1) := by
        have hp1 : 1 ≤ p := hp.out.one_lt.le
        have : p ^ 2 < (p ^ m) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
        exact Nat.mul_lt_mul'' hlt (Nat.sub_lt_sub_right (Nat.one_le_pow _ _ (by omega)) this)
      exact absurd (hL2 ▸ hLle.trans hG) (not_le.mpr h1)
    have hm1 : m = 1 := by
      have : p ^ m ≤ p ^ 1 := by rwa [pow_one]
      have := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp this
      omega
    subst hm1
    rw [pow_one] at hL2
    exact Subgroup.eq_of_le_of_card_ge hLG (hG.trans hL2.symm.le)
  ·
    exfalso
    have hcardH : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr eH.toEquiv]
      exact CFSG.Glauberman.Dickson.MaxCases.card_pgl2_galoisField' hm0
    have hLcard := card_eq_two_mul_card_map h2 hnL
    have hLle : Nat.card L ≤ Nat.card G := Subgroup.card_le_of_le hLG
    have hpm : p ≤ p ^ m := Nat.le_self_pow hm0 p
    have h1 : p * (p ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) := by
      have : p ^ 2 ≤ (p ^ m) ^ 2 := Nat.pow_le_pow_left hpm 2
      exact Nat.mul_le_mul hpm (by omega)
    have hpos : 0 < p * (p ^ 2 - 1) := by
      have : 1 < p ^ 2 := by nlinarith
      exact Nat.mul_pos (by omega) (by omega)
    rw [← hH, hcardH] at hLcard
    generalize p ^ m * ((p ^ m) ^ 2 - 1) = X at *
    generalize p * (p ^ 2 - 1) = P at *
    omega

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
