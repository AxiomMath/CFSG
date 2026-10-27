module

public import CFSG.Walter.ReeOrder.WardLocal.XiOuter

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct
open CFSG.BlockSectionOrthogonality.Helpers

theorem xi5_arith {q m d a : ℤ} (hq : q = 3 * m ^ 2) (hm : 3 ≤ m)
    (hd : 2 * d = (q - 1) * m * (q + 1 + 3 * m)) (hdvd : q ^ 2 ∣ d - a) (hb : 2 * a ^ 2 ≤ q ^ 3) :
    2 * a = -(q + m) := by
  obtain ⟨t, ht⟩ := hdvd
  subst hq
  set s := m + 1 - 2 * t with hs
  have h2a : 2 * a = 9 * m ^ 4 * s - 3 * m ^ 2 - m := by
    rw [hs]; linear_combination hd - 2 * ht
  have hb' : (2 * a) ^ 2 ≤ 54 * m ^ 6 := by nlinarith
  have h9 : 9 ≤ m ^ 2 := by nlinarith
  have hm4 : 3 * m ^ 2 + m ≤ m ^ 4 := by nlinarith
  rcases lt_trichotomy s 0 with h | h | h
  · exfalso
    have hs1 : s ≤ -1 := by omega
    have : 2 * a ≤ -(8 * m ^ 4) := by nlinarith
    have : 64 * m ^ 8 ≤ (2 * a) ^ 2 := by nlinarith
    nlinarith
  · rw [h2a, h]; ring
  · exfalso
    have hs1 : 1 ≤ s := by omega
    have : 8 * m ^ 4 ≤ 2 * a := by nlinarith
    have : 64 * m ^ 8 ≤ (2 * a) ^ 2 := by nlinarith
    nlinarith

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

omit [CharP K 3] in
theorem sum_S2 {M : Type*} [AddCommMonoid M] (f : (G → ℂ) → M) :
    ∑ χ ∈ S.S2, f χ = f B.ξ₃ + f B.ξ₄ + f B.ξ₅ + f B.ξ₆ :=
  sum_four B.hS2 B.n34 B.n35 B.n36 B.n45 B.n46 B.n56 f

omit [CharP K 3] in
theorem irr_5 : B.ξ₅ ∈ BlocksIrr G := (mem_supp.mp (show B.ξ₅ ∈ S.S2 by rw [B.hS2]; simp)).1
omit [CharP K 3] in
theorem irr_6 : B.ξ₆ ∈ BlocksIrr G := (mem_supp.mp (show B.ξ₆ ∈ S.S2 by rw [B.hS2]; simp)).1

omit [CharP K 3] in
theorem d2_3 : S.d2 B.ξ₃ = 1 := by
  rw [← S.agree12 (show B.ξ₃ ∈ S.S1 by rw [B.hS1]; simp) (show B.ξ₃ ∈ S.S2 by rw [B.hS2]; simp),
    B.d1_3]

omit [CharP K 3] in
theorem d2_4 : S.d2 B.ξ₄ = -1 := by
  rw [← S.agree12 (show B.ξ₄ ∈ S.S1 by rw [B.hS1]; simp) (show B.ξ₄ ∈ S.S2 by rw [B.hS2]; simp),
    B.d1_4]

omit [CharP K 3] in
theorem col_d2 {x : G} (hx : Odd (orderOf x)) :
    B.ξ₃ x - B.ξ₄ x - B.ξ₅ x + B.ξ₆ x = 0 := by
  have h := S.orth S.d2 (fun χ hχ => S.inner_Φ2 hχ) hx
  rw [sum_irr_eq_sum_of_vanish (supp_sub S.d2) _ (fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ
    rw [S.van2 hχ hnot]; simp)] at h
  rw [show supp S.d2 = S.S2 from rfl, B.sum_S2, B.d2_3, B.d2_4, B.d2_5, B.d2_6] at h
  have h' := congrArg (starRingEnd ℂ) h
  simp only [map_add, map_mul, map_neg, map_one, map_zero, Int.cast_one, Int.cast_neg,
    RCLike.conj_conj] at h'
  linear_combination h'

include B hq hK hG hP1P hPc hPn in
theorem sum_PP1 (f : G → ℂ) :
    ∑ a ∈ Finset.univ.filter (· ∈ PP1 S), f a =
      ∑ c ∈ Finset.univ.filter (· ∈ zcen P), ∑ b ∈ Finset.univ.filter (· ∈ FF S), f (c * b) := by
  have hcT := B.hcT hq hK hG
  have hZ := zcen_eq_CC hq hK hcT hG (B.card_AA hq hK hG) hP1P hPc hPn
  have hZP1 := B.zcen_le_PP1 hq hK hG hP1P hPc hPn
  have hFP1 := FF_le_PP1 (S := S) hq hcT
  set s := (Finset.univ.filter (· ∈ zcen P)) ×ˢ (Finset.univ.filter (· ∈ FF S)) with hs
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2) (s : Set (G × G)) := by
    rintro ⟨c, b⟩ hcb ⟨c', b'⟩ hcb' h
    simp only [hs, Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_ofPred_eq] at hcb hcb'
    simp only at h
    have h1 : c'⁻¹ * c = b' * b⁻¹ := by
      calc c'⁻¹ * c = c'⁻¹ * (c * b) * b⁻¹ := by group
        _ = c'⁻¹ * (c' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    have hC : c'⁻¹ * c ∈ CC S hq hK hcT hG := by
      rw [← hZ]; exact (zcen P).mul_mem ((zcen P).inv_mem hcb'.1) hcb.1
    have hF : c'⁻¹ * c ∈ FF S := h1 ▸ (FF S).mul_mem hcb'.2 ((FF S).inv_mem hcb.2)
    have he := CC_inf_FF hq hK hcT hG hC hF
    have hcc : c = c' := by
      have := congrArg (fun t => c' * t) he
      simpa using this
    subst hcc
    rw [mul_left_cancel h]
  have himg : s.image (fun p : G × G => p.1 * p.2) = Finset.univ.filter (· ∈ PP1 S) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨⟨c, b⟩, hcb, rfl⟩ := Finset.mem_image.mp hx
      simp only [hs, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hcb ⊢
      exact (PP1 S).mul_mem (hZP1 hcb.1) (hFP1 hcb.2)
    · rw [Finset.card_image_of_injOn hinj, hs, Finset.card_product, card_filter_eq, card_filter_eq,
        card_filter_eq, card_PP1 hq hK hcT hG, B.card_zcen hq hK hG hP1P hPc hPn, card_FF, hK]
      ring_nf; rfl
  rw [← himg, Finset.sum_image hinj, hs, Finset.sum_product]

include B hq hK hG hP1P hPc hPn in
theorem zcen_congr {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {X : G} (hX : X ∈ zcen P) (hX1 : X ≠ 1) :
    ∃ a : ℤ, χ X = a ∧ (q : ℤ) ^ 2 ∣ deg χ - a := by
  have hcT := B.hcT hq hK hG
  have hZ := zcen_eq_CC hq hK hcT hG (B.card_AA hq hK hG) hP1P hPc hPn
  have hZP1 := B.zcen_le_PP1 hq hK hG hP1P hPc hPn
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq1 : (q : ℂ) - 1 ≠ 0 := by
    have : ((q : ℤ) - 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hmult : ∀ H : Subgroup G, ∃ n : ℕ,
      ∑ g ∈ Finset.univ.filter (· ∈ H), χ g = (Nat.card H : ℂ) * n := by
    intro H
    obtain ⟨n, hn⟩ := exists_natCast_restrict H.subtype hχ (one_mem_blocksIrr H)
    refine ⟨n, ?_⟩
    rw [BlocksInnerProduct] at hn
    simp only [Function.comp_apply, Pi.one_apply, map_one, mul_one] at hn
    have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [Finset.sum_subtype (Finset.univ.filter (· ∈ H)) (p := fun x => x ∈ H) (by simp) χ, ← hn]
    field_simp
    rfl
  obtain ⟨nC, hnC⟩ := hmult (zcen P)
  obtain ⟨n₁, hn₁⟩ := hmult (PP1 S)
  obtain ⟨nF, hnF⟩ := hmult (FF S)
  rw [B.sum_zcen hq hK hG hP1P hPc hPn hχ hX hX1, B.card_zcen hq hK hG hP1P hPc hPn] at hnC
  rw [card_PP1 hq hK hcT hG] at hn₁
  rw [card_FF, hK] at hnF
  have hdeg := deg_eq hχ
  obtain ⟨a, ha⟩ := exists_int_of_isIntegral (isIntegral_irr hχ X)
    (r := ((q : ℚ) * nC - deg χ) / (q - 1)) (by
      push_cast
      rw [hdeg]
      field_simp
      linear_combination hnC)
  refine ⟨a, ha, ?_⟩
  have hF1 : ∀ b ∈ Finset.univ.filter (· ∈ FF S), b ≠ 1 → ∀ c ∈ zcen P, χ (c * b) = χ b := by
    intro b hb hb1 c hc
    have hbF := (Finset.mem_filter.mp hb).2
    have hbP1 : b ∈ PP1 S := FF_le_PP1 hq hcT hbF
    have hbZ : b ∉ zcen P := fun h => hb1 (CC_inf_FF hq hK hcT hG (hZ ▸ h) hbF)
    obtain ⟨g, -, hg⟩ := B.exists_conj_PP1 hq hK hG hP1P hPc hPn hbP1 hbZ hc
    rw [(mem_zcen.mp hc).2 b (hP1P hbP1), ← hg, irr_class hχ]
  have h1F : (1 : G) ∈ Finset.univ.filter (· ∈ FF S) := by simp [(FF S).one_mem]
  have hsplit : ∀ c ∈ Finset.univ.filter (· ∈ zcen P),
      ∑ b ∈ Finset.univ.filter (· ∈ FF S), χ (c * b) =
        χ c + (∑ b ∈ Finset.univ.filter (· ∈ FF S), χ b - χ 1) := by
    intro c hc
    have hc' := (Finset.mem_filter.mp hc).2
    rw [← Finset.add_sum_erase _ _ h1F, ← Finset.add_sum_erase _ _ h1F, mul_one,
      Finset.sum_congr rfl fun b hb => hF1 b (Finset.mem_of_mem_erase hb)
        (Finset.ne_of_mem_erase hb) c hc']
    ring
  have hP1sum := B.sum_PP1 hq hK hG hP1P hPc hPn χ
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, card_filter_eq,
    B.card_zcen hq hK hG hP1P hPc hPn, B.sum_zcen hq hK hG hP1P hPc hPn hχ hX hX1, hnF, hn₁,
    nsmul_eq_mul] at hP1sum
  push_cast at hP1sum
  have hkey : ((q : ℤ) - 1) * (a - deg χ) = (q : ℤ) ^ 2 * (n₁ - nF) := by
    have : ((((q : ℤ) - 1) * (a - deg χ) : ℤ) : ℂ) = (((q : ℤ) ^ 2 * (n₁ - nF) : ℤ) : ℂ) := by
      push_cast
      rw [← ha, hdeg]
      linear_combination -hP1sum
    exact_mod_cast this
  have hcop : IsCoprime ((q : ℤ) ^ 2) ((q : ℤ) - 1) :=
    IsCoprime.pow_left ⟨1, -1, by ring⟩
  have h2 : (q : ℤ) ^ 2 ∣ ((q : ℤ) - 1) * (a - deg χ) := ⟨n₁ - nF, hkey⟩
  have h3 := hcop.dvd_of_dvd_mul_left h2
  have : deg χ - a = -(a - deg χ) := by ring
  rw [this]
  exact (dvd_neg).mpr h3

include B hq hK hG hP1P hPc hPn in
theorem xi56_zcen (hm : q = 3 * m ^ 2) {X : G} (hX : X ∈ zcen P) (hX1 : X ≠ 1) :
    2 * B.ξ₅ X = -((q : ℂ) + m) ∧ 2 * B.ξ₆ X = (q : ℂ) - m := by
  have hcT := B.hcT hq hK hG
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hm3 : 3 ≤ m := by
    by_contra h
    have : m ≤ 2 := by omega
    have : q ≤ 12 := by rw [hm]; nlinarith
    have := S.q_ge
    omega
  obtain ⟨a, ha, hdvd⟩ := B.zcen_congr hq hK hG hP1P hPc hPn B.irr_5 hX hX1
  have hconj : starRingEnd ℂ ∘ B.ξ₅ ≠ B.ξ₅ := by
    intro h
    apply B.ξ₅_S3
    have hd3 := S.conj_d3 B.irr_5
    simp only [↓reduceIte] at hd3
    rw [h, B.d2_5] at hd3
    exact mem_supp.mpr ⟨B.irr_5, by rw [hd3]; norm_num⟩
  have hXset : ({B.ξ₅, starRingEnd ℂ ∘ B.ξ₅} : Finset (G → ℂ)) ⊆
      (irreducibles_finite G).toFinset := by
    intro χ hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rw [Set.Finite.mem_toFinset]
    rcases hχ with rfl | rfl
    · exact B.irr_5
    · exact irr_conj B.irr_5
  have hbound := sum_normSq_le X hXset
  rw [Finset.sum_pair hconj.symm] at hbound
  have hXA := B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hX hX1
  rw [(centralizer_AA hq hK hcT hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hXA).2] at hbound
  simp only [Function.comp_apply, ha, Complex.normSq_conj, Complex.normSq_intCast] at hbound
  have hb : 2 * a ^ 2 ≤ (q : ℤ) ^ 3 := by
    have : ((2 * a ^ 2 : ℤ) : ℝ) ≤ ((q ^ 3 : ℤ) : ℝ) := by push_cast at hbound ⊢; linarith
    exact_mod_cast this
  have h2a := xi5_arith (q := (q : ℤ)) (m := (m : ℤ)) (d := deg B.ξ₅) (a := a)
    (by rw [hm]; push_cast; ring) (by exact_mod_cast hm3) B.deg_5 hdvd hb
  have h5 : 2 * B.ξ₅ X = -((q : ℂ) + m) := by
    rw [ha]
    have : ((2 * a : ℤ) : ℂ) = ((-((q : ℤ) + m) : ℤ) : ℂ) := by rw [h2a]
    push_cast at this
    exact this
  refine ⟨h5, ?_⟩
  have hX3 : 3 ∣ orderOf X := three_dvd_of_mem (isPGroup_P hq hPc) (mem_zcen.mp hX).1 hX1
  have hXodd : Odd (orderOf X) := by
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨X, (mem_zcen.mp hX).1⟩
    rw [Subgroup.orderOf_mk] at hN
    rw [hN]; exact Odd.pow (by decide)
  have hc2 := B.col_d2 hXodd
  have h24 := (B.eta_eq_one hq hG hXodd hX3 S.i₀).2.2
  have hξ2 : B.ξ₂ X = 1 - q := by
    rw [B.xi2_PP1 hq hK hG (B.zcen_le_PP1 hq hK hG hP1P hPc hPn hX) hX1]; simp [hXA]
  rw [B.xi3_eq_zero hq hG hX3] at hc2
  linear_combination 2 * hc2 + h5 + 2 * h24 - 2 * hξ2

end Block

end CFSG.Walter.WardLocal
