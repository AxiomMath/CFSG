module

public import CFSG.Quasithin.Vol2.Ch11SecBK4R
public import CFSG.Quasithin.Vol2.Ch11SecBK4L
public import CFSG.Quasithin.Vol2.Ch11SecBK4Q

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

namespace BK4

variable {F : Type} [Field F] [CharP F 2]

omit [Field F] [CharP F 2] in
theorem four_le_of_card {n : ℕ} (hK : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : 4 ≤ Nat.card F := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem U0_le_stabQ (h : ℕ) : G2Q8.U0 F ≤ G2Q8.stabQ (G2Q8.stdF F h) := by
  intro u hu
  refine G2Q8.mem_stabQ.mpr fun w => ⟨fun hw => G2Q8.FlagUni.mem hu hw, fun hw => ?_⟩
  have := G2Q8.FlagUni.mem ((G2Q8.U0 F).inv_mem hu) hw
  rwa [G2Q8.g2Act_inv_apply] at this

variable (F) in
@[expose] noncomputable def levi2D : ↥(G2Q8.stabQ2Det F) →* SL(2, F) where
  toFun g := ⟨G2Q8.levi2Mat g.1, g.2.2⟩
  map_one' := Subtype.ext G2Q8.levi2Mat_one
  map_mul' _ h := Subtype.ext (G2Q8.levi2Mat_mul h.2.1)

theorem le_stabQ_one_of_le_stabQ_two [Finite F] (h4 : 4 ≤ Nat.card F)
    {Y : Subgroup ↥(cayleyGroup F)} (hY : Group.IsSolvable Y) (hU : G2Q8.U0 F ≤ Y)
    (hY2 : Y ≤ G2Q8.stabQ (G2Q8.stdF F 2)) : Y ≤ G2Q8.stabQ (G2Q8.stdF F 1) := by
  have hJs : Group.IsSolvable ((Y.subgroupOf (G2Q8.stabQ2Det F)).map (levi2D F)) :=
    isSolvable_map _ (isSolvable_subgroupOf hY _)
  have hUJ : utri F ≤ (Y.subgroupOf (G2Q8.stabQ2Det F)).map (levi2D F) := by
    intro x hx
    obtain ⟨s, rfl⟩ := mem_utri_iff.mp hx
    have hmem : g2Y ![0, s, 0] ∈ G2Q8.U0 F := G2Q8.g2Y_mem_U0 s 0
    have hdet : (G2Q8.levi2Mat (g2Y ![0, s, 0])).det = 1 := by
      rw [G2Q8.levi2Mat_y1, Matrix.det_fin_two_of]
      ring
    refine ⟨⟨_, hY2 (hU hmem), hdet⟩, hU hmem, Subtype.ext ?_⟩
    change G2Q8.levi2Mat (g2Y ![0, s, 0]) = _
    rw [G2Q8.levi2Mat_y1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11]
  have hB : ∀ y ∈ Y, ∀ hy : y ∈ G2Q8.stabQ2Det F, G2Q8.levi2Mat y 1 0 = 0 := fun y hy hy2 =>
    le_borel_of_utri_le hUJ (ne_top_of_isSolvable h4 hJs) (Subgroup.mem_map_of_mem (levi2D F)
      (show (⟨y, hy2⟩ : ↥(G2Q8.stabQ2Det F)) ∈ Y.subgroupOf (G2Q8.stabQ2Det F) from hy))
  have key : ∀ x ∈ Y, g2Act x (G2Q8.eu 0 1) ∈ G2Q8.stdF F 1 := by
    intro x hx
    have hx2 := hY2 hx
    have hxi2 := hY2 (Y.inv_mem hx)
    have hnU : g2Y ![(0 : F), 1, 0] ∈ G2Q8.U0 F := G2Q8.g2Y_mem_U0 1 0
    have hn2 := hY2 (hU hnU)
    have hM : G2Q8.levi2Mat (x * g2Y ![0, 1, 0] * x⁻¹) =
        G2Q8.levi2Mat x * (!![1, 1; 0, 1] * G2Q8.levi2Mat x⁻¹) := by
      rw [mul_assoc, G2Q8.levi2Mat_mul ((G2Q8.stabQ _).mul_mem hn2 hxi2),
        G2Q8.levi2Mat_mul hxi2, G2Q8.levi2Mat_y1]
    have hAA : G2Q8.levi2Mat x * G2Q8.levi2Mat x⁻¹ = 1 := by
      rw [← G2Q8.levi2Mat_mul hxi2, mul_inv_cancel, G2Q8.levi2Mat_one]
    have hA'A : G2Q8.levi2Mat x⁻¹ * G2Q8.levi2Mat x = 1 := by
      rw [← G2Q8.levi2Mat_mul hx2, inv_mul_cancel, G2Q8.levi2Mat_one]
    have hdet : (G2Q8.levi2Mat (x * g2Y ![0, 1, 0] * x⁻¹)).det = 1 := by
      have hN : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [Matrix.det_fin_two_of]
        ring
      rw [hM, Matrix.det_mul, Matrix.det_mul, hN, one_mul, ← Matrix.det_mul, hAA, Matrix.det_one]
    have h10 := hB _ (Y.mul_mem (Y.mul_mem hx (hU hnU)) (Y.inv_mem hx))
      ⟨(G2Q8.stabQ _).mul_mem ((G2Q8.stabQ _).mul_mem hx2 hn2) hxi2, hdet⟩
    rw [hM] at h10
    set A := G2Q8.levi2Mat x with hA
    set A' := G2Q8.levi2Mat x⁻¹ with hA'
    have e1 : A 1 0 * A' 0 0 + A 1 1 * A' 1 0 = 0 := by
      have := congrFun (congrFun hAA 1) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have e2 : A' 1 0 * A 0 0 + A' 1 1 * A 1 0 = 0 := by
      have := congrFun (congrFun hA'A 1) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have e3 : A' 1 0 * A 0 1 + A' 1 1 * A 1 1 = 1 := by
      have := congrFun (congrFun hA'A 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h10' : A 1 0 * (A' 0 0 + A' 1 0) + A 1 1 * A' 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using h10
    have hsq : A 1 0 ^ 2 = 0 := by
      linear_combination (A 0 1 * A 1 0 - A 0 0 * A 1 1) * (h10' - e1) + A 1 0 * A 1 1 * e2 -
        A 1 0 ^ 2 * e3
    have h0 : A 1 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
    have hw2 : g2Act x (G2Q8.eu 0 1) ∈ G2Q8.stdF F 2 :=
      (G2Q8.mem_stabQ.mp hx2 _).mp (G2Q8.stdF_mono (by norm_num)
        (G2Q8.mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩))
    obtain ⟨w1, w2, w3, w4⟩ := G2Q8.mem_stdF_two.mp hw2
    have w5 : g2Act x (G2Q8.eu 0 1) (.inr 2) = 0 := by
      rw [G2Q8.eu_eq_q6]
      simpa [hA, G2Q8.levi2Mat_apply, G2Q8.upart] using h0
    refine G2Q8.mem_stdF.mpr fun k hk => ?_
    rcases k with k | k <;> fin_cases k
    · simp [G2Q8.ht] at hk
    · exact w1
    · exact w2
    · exact w3
    · exact w4
    · exact w5
  have key1 : ∀ x ∈ Y, ∀ w ∈ G2Q8.stdF F 1, g2Act x w ∈ G2Q8.stdF F 1 := by
    intro x hx w hw
    obtain ⟨c, rfl⟩ := G2Q8.mem_stdF_one_iff.mp hw
    rw [G2Q8.g2Act_smul]
    exact (G2Q8.stdF F 1).smul_mem c (key x hx)
  intro x hx
  refine G2Q8.mem_stabQ.mpr fun w => ⟨key1 x hx w, fun hw => ?_⟩
  have := key1 x⁻¹ (Y.inv_mem hx) _ hw
  rwa [G2Q8.g2Act_inv_apply] at this

theorem eq_bot_of_odd_of_le_normalizer [Finite F] {n : ℕ} (hK : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) {Y N : Subgroup ↥(cayleyGroup F)} (hY : Group.IsSolvable Y)
    (hU : G2Q8.U0 F ≤ Y) (hNY : N ≤ Y) (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hNodd : Odd (Nat.card N))
    (hUN : G2Q8.U0 F ≤ Subgroup.normalizer (N : Set ↥(cayleyGroup F))) : N = ⊥ := by
  have h4 := four_le_of_card hK hn
  have hpowN : ∀ c ∈ N, c ^ Nat.card N = 1 := fun c hc => by
    have h1 := congrArg Subtype.val (pow_card_eq_one' (G := ↥N) (x := ⟨c, hc⟩))
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
    exact h1
  have hC : ∀ s : F, s ≠ 0 → ∀ c ∈ N, G2Q8.tL s * c * (G2Q8.tL s)⁻¹ = c → c = 1 := by
    intro s hs c hcN hcs
    set C := N ⊓ Subgroup.centralizer {G2Q8.tL s} with hCdef
    have hXY : C ⊔ G2Q8.U0 F ≤ Y := sup_le (inf_le_left.trans hNY) hU
    have hX : Group.IsSolvable ↥(C ⊔ G2Q8.U0 F) := by
      have := hY
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXY)
    have hX2 : C ⊔ G2Q8.U0 F ≤ G2Q8.stabQ (G2Q8.stdF F 2) :=
      sup_le (fun c hc => mem_stabQ_two_of_comm hs (Subgroup.mem_centralizer_singleton_iff.mp
        hc.2)) (U0_le_stabQ 2)
    have hXN := le_normalizer_of_le_stabQ_one h4 hK hX le_sup_right
      (le_stabQ_one_of_le_stabQ_two h4 hX le_sup_right hX2)
    have hcC : c ∈ C := ⟨hcN, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc c * G2Q8.tL s = G2Q8.tL s * c * (G2Q8.tL s)⁻¹ * G2Q8.tL s := by rw [hcs]
        _ = G2Q8.tL s * c := by group)⟩
    have hcU : ∀ u ∈ G2Q8.U0 F, c * u = u * c := by
      intro u hu
      have h1 : c * u * c⁻¹ ∈ G2Q8.U0 F :=
        (Subgroup.mem_normalizer_iff.mp (hXN (le_sup_left (b := G2Q8.U0 F) hcC)) u).mp hu
      have h2 : u * c⁻¹ * u⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hUN hu) c⁻¹).mp (N.inv_mem hcN)
      have h3 : c * u * c⁻¹ * u⁻¹ ∈ G2Q8.U0 F ⊓ N := by
        refine ⟨(G2Q8.U0 F).mul_mem h1 ((G2Q8.U0 F).inv_mem hu), ?_⟩
        rw [show c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) by group]
        exact N.mul_mem hcN h2
      rw [G2Q8.U0_inf_eq_bot_of_odd hNodd, Subgroup.mem_bot] at h3
      calc c * u = c * u * c⁻¹ * u⁻¹ * (u * c) := by group
        _ = u * c := by rw [h3, one_mul]
    exact eq_one_of_comm_U0 hNodd (hpowN c hcN) hcU
  obtain ⟨θ, hθ0, hθ1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  have h1θ : (1 : F) + θ ≠ 0 := by
    intro h
    apply hθ1
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h - h2
  have hca : G2Q8.tL (1 + θ) * G2Q8.tL 1 = G2Q8.tL θ := by
    rw [G2Q8.tL_mul, show (1 : F) + θ + 1 = θ by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h2]
  have hcb : G2Q8.tL (1 + θ) * G2Q8.tL θ = G2Q8.tL 1 := by
    rw [G2Q8.tL_mul, show (1 : F) + θ + θ = 1 by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination θ * h2]
  have hsq : ∀ s : F, G2Q8.tL s * G2Q8.tL s = 1 := fun s => by
    rw [G2Q8.tL_mul, CharTwo.add_self_eq_zero]
    exact G2Q8.cayley_eq_one fun w => by rw [q6_eta w, G2Q8.g2Act_tL]; simp
  have hconj : ∀ s : F, ∀ y ∈ N, G2Q8.tL s * y * (G2Q8.tL s)⁻¹ ∈ N := fun s y hy =>
    (Subgroup.mem_normalizer_iff.mp (hUN (tL_mem_U0 s)) y).mp hy
  have hfix : ∀ s : F, s ≠ 0 → ∀ x ∈ N, x * (G2Q8.tL s * x * (G2Q8.tL s)⁻¹) = 1 := by
    intro s hs x hx
    refine hC s hs _ (N.mul_mem hx (hconj s x hx)) ?_
    calc G2Q8.tL s * (x * (G2Q8.tL s * x * (G2Q8.tL s)⁻¹)) * (G2Q8.tL s)⁻¹ =
          G2Q8.tL s * x * (G2Q8.tL s)⁻¹ * ((G2Q8.tL s * G2Q8.tL s) * x *
            (G2Q8.tL s * G2Q8.tL s)⁻¹) := by group
      _ = G2Q8.tL s * x * (G2Q8.tL s)⁻¹ * x := by rw [hsq]; group
      _ = x * (G2Q8.tL s * x * (G2Q8.tL s)⁻¹) := hNc _ (hconj s x hx) _ hx
  refine eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr ?_
  have e1 := eq_inv_of_mul_eq_one_right (hfix 1 one_ne_zero x hx)
  have e2 := eq_inv_of_mul_eq_one_right (hfix θ hθ0 x hx)
  have hxa := hconj 1 x hx
  have hxb := hconj θ x hx
  have e3 : G2Q8.tL 1 * x * (G2Q8.tL 1)⁻¹ * (G2Q8.tL θ * x * (G2Q8.tL θ)⁻¹) = 1 := by
    refine hC (1 + θ) h1θ _ (N.mul_mem hxa hxb) ?_
    calc G2Q8.tL (1 + θ) * (G2Q8.tL 1 * x * (G2Q8.tL 1)⁻¹ * (G2Q8.tL θ * x * (G2Q8.tL θ)⁻¹)) *
          (G2Q8.tL (1 + θ))⁻¹ = (G2Q8.tL (1 + θ) * G2Q8.tL 1) * x *
            (G2Q8.tL (1 + θ) * G2Q8.tL 1)⁻¹ * ((G2Q8.tL (1 + θ) * G2Q8.tL θ) * x *
              (G2Q8.tL (1 + θ) * G2Q8.tL θ)⁻¹) := by group
      _ = G2Q8.tL θ * x * (G2Q8.tL θ)⁻¹ * (G2Q8.tL 1 * x * (G2Q8.tL 1)⁻¹) := by rw [hca, hcb]
      _ = _ := hNc _ hxb _ hxa
  rw [e1, e2] at e3
  have hx2 : x ^ 2 = 1 := by
    rw [sq, ← inv_eq_one, mul_inv_rev]
    exact e3
  exact eq_one_of_sq_of_pow hNodd hx2 (hpowN x hx)

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
