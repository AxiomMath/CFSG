module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Ring
public import CFSG.RankThree.PartOne.SEITZ2.G2F2Conj

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
open scoped commutatorElement Matrix

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem cartan_e0_rt4 : (∑ j, (Tag.G2).cartan e0 j * (rt 4) j) = 1 := by decide +kernel

omit [CharP K 2] in
theorem cartan_e0_rt5 : (∑ j, (Tag.G2).cartan e0 j * (rt 5) j) = 1 := by decide +kernel

omit [CharP K 2] in
theorem weyl_mem_of_rational {k : Subfield K} {H : Subgroup (adjointGroup .G2 K)}
    (hRH : ∀ p < 12, ∀ c ∈ k, xp p c ∈ H) :
    weylElement .G2 K e0 ∈ H ∧ weylElement .G2 K e1 ∈ H := by
  refine ⟨?_, ?_⟩
  · rw [weylElement_e0_eq]
    exact H.mul_mem (H.mul_mem (hRH 0 (by norm_num) 1 k.one_mem)
      (hRH 2 (by norm_num) (-1) (k.neg_mem k.one_mem))) (hRH 0 (by norm_num) 1 k.one_mem)
  · rw [weylElement_e1_eq]
    exact H.mul_mem (H.mul_mem (hRH 1 (by norm_num) 1 k.one_mem)
      (hRH 5 (by norm_num) (-1) (k.neg_mem k.one_mem))) (hRH 1 (by norm_num) 1 k.one_mem)

theorem eq_top_of_full_seven_f2 {k : Subfield K} {H : Subgroup (adjointGroup .G2 K)}
    (hRH : ∀ p < 12, ∀ c ∈ k, xp p c ∈ H) (h7 : Full H 7) {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    H = ⊤ := by
  obtain ⟨hw0, hw1⟩ := weyl_mem_of_rational hRH
  have h3 : Full H 3 := h7.conj e0 (by norm_num) reflect_7 hw0
  have h0 : Full H 0 := h3.conj e1 (by norm_num) reflect_3 hw1
  have h2 : Full H 2 := h0.conj e0 (by norm_num) reflect_0 hw0
  set U : Kˣ := Units.mk0 u hu0 with hU
  have hUv : (U : K) = u := rfl
  have hτ0 : torusElement .G2 K e0 U ∈ H := by
    rw [torusElement_e0_eq]
    exact H.mul_mem (H.mul_mem (H.mul_mem (h0 _) (h2 _)) (h0 _)) (H.inv_mem hw0)
  have hτ : Wg K * torusElement .G2 K e0 U * (Wg K)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hw0 hw1) hτ0) (H.inv_mem (H.mul_mem hw0 hw1))
  rw [Wg_torus0] at hτ
  have hconj : ∀ (p : ℕ) (hp : p < 12) (c : K), torusElement .G2 K e0 (U ^ 2) *
      torusElement .G2 K e1 U * xp p c * (torusElement .G2 K e0 (U ^ 2) *
        torusElement .G2 K e1 U)⁻¹ =
      xp p ((((U ^ 2) ^ (∑ j, (Tag.G2).cartan e0 j * (rt p) j) : Kˣ) : K) *
        (((U ^ (∑ j, (Tag.G2).cartan e1 j * (rt p) j) : Kˣ) : K) * c)) := by
    intro p hp c
    rw [show torusElement .G2 K e0 (U ^ 2) * torusElement .G2 K e1 U * xp p c *
        (torusElement .G2 K e0 (U ^ 2) * torusElement .G2 K e1 U)⁻¹ =
        torusElement .G2 K e0 (U ^ 2) * (torusElement .G2 K e1 U * xp p c *
          (torusElement .G2 K e1 U)⁻¹) * (torusElement .G2 K e0 (U ^ 2))⁻¹ by group,
      torusElement_conj_xp e1 hp, torusElement_conj_xp e0 hp]
  have ha₁ : ∀ c, torusElement .G2 K e0 (U ^ 2) * torusElement .G2 K e1 U * xp 4 c *
      (torusElement .G2 K e0 (U ^ 2) * torusElement .G2 K e1 U)⁻¹ = xp 4 (u * c) := by
    intro c
    rw [hconj 4 (by norm_num) c, cartan_e0_rt4, cartan_e1_rt4]
    congr 1
    simp only [zpow_one, zpow_neg, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hUv]
    field_simp
  have ha₂ : ∀ c, torusElement .G2 K e0 (U ^ 2) * torusElement .G2 K e1 U * xp 5 c *
      (torusElement .G2 K e0 (U ^ 2) * torusElement .G2 K e1 U)⁻¹ = xp 5 (1 * c) := by
    intro c
    rw [hconj 5 (by norm_num) c, cartan_e0_rt5, cartan_e1_rt5]
    congr 1
    simp only [zpow_neg, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, zpow_ofNat, hUv]
    field_simp
  exact eq_top_of_full_seven_of_weyl hw0 hw1 h7 (hRH 11 (by norm_num) 1 k.one_mem) hτ
    (a₁ := u) (a₂ := 1) hu1 ha₁ ha₂

theorem comm_x0_x3 (s d : K) : ⁅xp 0 s, xp 3 d⁆ = xp 7 (s * d) :=
  comm_of_swap _ _ _ (swap_03 s d)

theorem full_seven_of_full_ten {H : Subgroup (adjointGroup .G2 K)}
    (hw0 : weylElement .G2 K e0 ∈ H) (hw1 : weylElement .G2 K e1 ∈ H) (h10 : Full H 10) :
    Full H 7 :=
  ((((h10.conj e0 (by norm_num) reflect_10 hw0).conj e1 (by norm_num) rf_e1_6 hw1).conj e0
    (by norm_num) rf_e0_2 hw0).conj e1 (by norm_num) reflect_0' hw1).conj e0 (by norm_num)
    reflect_3' hw0

theorem full_ten_of_irrational [Finite K] {k : Subfield K} (hk : Nat.card k = 2) {d : ℕ}
    (hd : d.Prime) (hK : Nat.card K = Nat.card k ^ d) {H : Subgroup (adjointGroup .G2 K)}
    (hRH : ∀ p < 12, ∀ c ∈ k, xp p c ∈ H) {μ : K} (hμk : μ ∉ k) (hμ : xp 10 μ ∈ H) :
    Full H 10 := by
  obtain ⟨hw0, hw1⟩ := weyl_mem_of_rational hRH
  have h10to0 : ∀ t : K, xp 10 t ∈ H → xp 0 t ∈ H := fun t h =>
    mem_of_conj_weyl e0 (p := 2) (q := 0) (by norm_num) rf_e0_2 hw0
      (mem_of_conj_weyl e1 (p := 6) (q := 2) (by norm_num) rf_e1_6 hw1
        (mem_of_conj_weyl e0 (p := 10) (q := 6) (by norm_num) reflect_10 hw0 h))
  have h10to3 : ∀ t : K, xp 10 t ∈ H → xp 3 t ∈ H := fun t h =>
    mem_of_conj_weyl e1 (p := 0) (q := 3) (by norm_num) reflect_0' hw1 (h10to0 t h)
  have h7to10 : ∀ t : K, xp 7 t ∈ H → xp 10 t ∈ H := fun t h =>
    mem_of_conj_weyl e0 (p := 6) (q := 10) (by norm_num) reflect_6 hw0
      (mem_of_conj_weyl e1 (p := 2) (q := 6) (by norm_num) reflect_2 hw1
        (mem_of_conj_weyl e0 (p := 0) (q := 2) (by norm_num) reflect_0 hw0
          (mem_of_conj_weyl e1 (p := 3) (q := 0) (by norm_num) reflect_3 hw1
            (mem_of_conj_weyl e0 (p := 7) (q := 3) (by norm_num) reflect_7 hw0 h))))
  let T : Subring K :=
    { carrier := {t | xp 10 t ∈ H}
      mul_mem' := fun {s t} hs ht => by
        have h0 := h10to0 s hs
        have h3 := h10to3 t ht
        have hc : ⁅xp 0 s, xp 3 t⁆ ∈ H := by
          rw [commutatorElement_def]
          exact H.mul_mem (H.mul_mem (H.mul_mem h0 h3) (H.inv_mem h0)) (H.inv_mem h3)
        rw [comm_x0_x3] at hc
        exact h7to10 _ hc
      one_mem' := hRH 10 (by norm_num) 1 k.one_mem
      add_mem' := fun {s t} hs ht => by
        show xp 10 (s + t) ∈ H
        rw [xp_add]
        exact H.mul_mem hs ht
      zero_mem' := by
        show xp 10 0 ∈ H
        rw [xp_zero]
        exact H.one_mem
      neg_mem' := fun {s} hs => by
        show xp 10 (-s) ∈ H
        rw [CharTwo.neg_eq]
        exact hs }
  have hT : T = ⊤ := subring_eq_top_of_card_prime hd (by rw [hK, hk]) T (a := μ) hμ
    (fun h => hμk (h ▸ k.zero_mem)) (fun h => hμk (h ▸ k.one_mem))
  intro t
  have : t ∈ T := hT ▸ Subring.mem_top t
  exact this

end CFSG.RankThree.PartOne.SEITZ2
