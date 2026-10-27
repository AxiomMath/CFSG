module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KNorm
public import CFSG.RankThree.PartTwo.Sec21.Hering2119KCheck

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def blkX (c0 c1 c2 : F3) : M4 :=
  !![1, 0, 0, 0; 0, 1, 0, 0; c0, c1, 1, 0; c1, c2, 0, 1]

@[expose] def blkT (d0 d1 d2 : F3) : M4 :=
  !![1, 0, 0, 0; 0, 1, 0, 0; d0, d1, -1, 0; d1, d2, 0, -1]

theorem finrank_ker_comp_le {V : Type} [AddCommGroup V] [Module F3 V] [FiniteDimensional F3 V]
    (f g : V →ₗ[F3] V) :
    finrank F3 (LinearMap.ker (f ∘ₗ g)) ≤
      finrank F3 (LinearMap.ker f) + finrank F3 (LinearMap.ker g) := by
  have h := LinearMap.lift_rank_comap_le (f := g) (LinearMap.ker f)
  rw [Cardinal.lift_id, Cardinal.lift_id, Cardinal.lift_id, ← LinearMap.ker_comp,
    ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem mem_ker_sub_one {X : M4} {v : V4} :
    v ∈ LinearMap.ker (Matrix.toLin' (X - 1)) ↔ X *ᵥ v = v := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem sub_one_cube {X : M4} (h : X * X * X = 1) : (X - 1) * (X - 1) * (X - 1) = 0 := by
  have h3 : (3 : M4) = 0 := by exact_mod_cast CharP.cast_eq_zero M4 3
  have e : (X - 1) * (X - 1) * (X - 1) = X * X * X - 1 + 3 * (X - X * X) := by noncomm_ring
  rw [e, h3, zero_mul, add_zero, h, sub_self]

theorem two_le_finrank_fix {X : M4} (h : X * X * X = 1) :
    2 ≤ finrank F3 (LinearMap.ker (Matrix.toLin' (X - 1))) := by
  have h0 : (Matrix.toLin' ((X - 1) * ((X - 1) * (X - 1))) : V4 →ₗ[F3] V4) = 0 := by
    rw [← mul_assoc, sub_one_cube h, map_zero]
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at h0
  have h1 := finrank_ker_comp_le (Matrix.toLin' (X - 1) : V4 →ₗ[F3] V4)
    ((Matrix.toLin' (X - 1) : V4 →ₗ[F3] V4) ∘ₗ Matrix.toLin' (X - 1))
  have h2 := finrank_ker_comp_le (Matrix.toLin' (X - 1) : V4 →ₗ[F3] V4) (Matrix.toLin' (X - 1))
  rw [h0, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun] at h1
  omega

def projF : V4 →ₗ[F3] (Fin 2 → F3) where
  toFun v := ![v 2, v 3]
  map_add' x y := by
    ext i
    fin_cases i <;> rfl
  map_smul' c x := by
    ext i
    fin_cases i <;> rfl

theorem exists_fix {X : M4} (hcube : X * X * X = 1)
    (hnoFix : ∀ v, inA v → v ≠ 0 → X.mulVec v ≠ v) (w : Fin 2 → F3) :
    ∃ n : V4, X *ᵥ n = n ∧ n 2 = w 0 ∧ n 3 = w 1 := by
  have hinj : Function.Injective (projF.domRestrict (LinearMap.ker (Matrix.toLin' (X - 1)))) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hx' := mem_ker_sub_one.mp hx
    have hy' := mem_ker_sub_one.mp hy
    have h2 : x 2 = y 2 := congrFun hxy 0
    have h3 : x 3 = y 3 := congrFun hxy 1
    by_contra hne
    have hA : inA (x - y) := ⟨by simp [h2], by simp [h3]⟩
    have hne0 : x - y ≠ 0 := fun h0 => hne (Subtype.ext (sub_eq_zero.mp h0))
    have hfix : X *ᵥ (x - y) = x - y := by rw [Matrix.mulVec_sub, hx', hy']
    exact hnoFix (x - y) hA hne0 hfix
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun] at hle
  have heq : finrank F3 (LinearMap.ker (Matrix.toLin' (X - 1))) = finrank F3 (Fin 2 → F3) := by
    rw [Module.finrank_fin_fun]
    exact le_antisymm hle (two_le_finrank_fix hcube)
  obtain ⟨⟨n, hn⟩, hpn⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := projF.domRestrict (LinearMap.ker (Matrix.toLin' (X - 1)))) heq).mp hinj w
  exact ⟨n, mem_ker_sub_one.mp hn, congrFun hpn 0, congrFun hpn 1⟩

theorem F3.eq_zero_of_eq_neg : ∀ x : F3, x = -x → x = 0 := by decide

theorem IsItem.omega_fix {a : V4} {X T : M4} (hI : IsItem a X T) {v w : V4}
    (hv : X *ᵥ v = v) (hw : X *ᵥ w = w) : omega4 v w = 0 := by
  have h : omega4 (-v) (-w) = -omega4 v w := by
    have h0 := hI.mult v w
    rw [hI.neg v hv, hI.neg w hw] at h0
    exact h0
  have e : omega4 (-v) (-w) = omega4 v w := by
    simp [omega4]
  rw [e] at h
  exact F3.eq_zero_of_eq_neg _ h

theorem umat_neg_mul (s0 s1 s2 : F3) : umat (-s0) (-s1) (-s2) * umat s0 s1 s2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [umat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem umat_mul_neg (s0 s1 s2 : F3) : umat s0 s1 s2 * umat (-s0) (-s1) (-s2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [umat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem umat_normEl (s0 s1 s2 : F3) : NormEl (umat (-s0) (-s1) (-s2)) (umat s0 s1 s2) :=
  ⟨umat_neg_mul s0 s1 s2, umat_mul_neg s0 s1 s2, umat_symp _ _ _, umat_fixA _ _ _⟩

theorem blk_of_cols {Y : M4} {μ : F3} (hμ : μ * μ = 1)
    (hs : ∀ x y, omega4 (Y *ᵥ x) (Y *ᵥ y) = μ * omega4 x y)
    (h2 : Y *ᵥ ev 2 = μ • ev 2) (h3 : Y *ᵥ ev 3 = μ • ev 3) :
    Y = !![1, 0, 0, 0; 0, 1, 0, 0; Y 2 0, Y 3 0, μ, 0; Y 3 0, Y 3 1, 0, μ] := by
  rw [mulVec_ev] at h2 h3
  have y02 : Y 0 2 = 0 := by simpa [ev] using congrFun h2 0
  have y12 : Y 1 2 = 0 := by simpa [ev] using congrFun h2 1
  have y22 : Y 2 2 = μ := by simpa [ev] using congrFun h2 2
  have y32 : Y 3 2 = 0 := by simpa [ev] using congrFun h2 3
  have y03 : Y 0 3 = 0 := by simpa [ev] using congrFun h3 0
  have y13 : Y 1 3 = 0 := by simpa [ev] using congrFun h3 1
  have y23 : Y 2 3 = 0 := by simpa [ev] using congrFun h3 2
  have y33 : Y 3 3 = μ := by simpa [ev] using congrFun h3 3
  obtain ⟨o02, o13, o01, o03, o12, -⟩ := omega4_ev
  have k : ∀ i j, omega4 (fun r => Y r i) (fun r => Y r j) = μ * omega4 (ev i) (ev j) := by
    intro i j
    have := hs (ev i) (ev j)
    rwa [mulVec_ev, mulVec_ev] at this
  have k02 := k 0 2
  have k03 := k 0 3
  have k12 := k 1 2
  have k13 := k 1 3
  have k01 := k 0 1
  rw [o02] at k02
  rw [o03] at k03
  rw [o12] at k12
  rw [o13] at k13
  rw [o01] at k01
  simp only [omega4, ev, y02, y12, y22, y32, y03, y13, y23, y33] at k02 k03 k12 k13 k01
  have y00 : Y 0 0 = 1 := by linear_combination μ * k02 - (Y 0 0 - 1) * hμ
  have y10 : Y 1 0 = 0 := by linear_combination μ * k03 - Y 1 0 * hμ
  have y01 : Y 0 1 = 0 := by linear_combination μ * k12 - Y 0 1 * hμ
  have y11 : Y 1 1 = 1 := by linear_combination μ * k13 - (Y 1 1 - 1) * hμ
  rw [y00, y01, y10, y11] at k01
  have y21 : Y 2 1 = Y 3 0 := by linear_combination k01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [y00, y01, y10, y11, y21, y02, y12, y22, y32, y03, y13, y23, y33]

theorem sing_ker : ∀ c0 c1 c2 : F3, c0 * c2 - c1 * c1 = 0 →
    ∃ u0 u1 : F3, ¬ (u0 = 0 ∧ u1 = 0) ∧ c0 * u0 + c1 * u1 = 0 ∧ c1 * u0 + c2 * u1 = 0 := by
  decide

theorem det_ne_zero_of_noFix {c0 c1 c2 : F3}
    (h : ∀ v, inA v → v ≠ 0 → (blkX c0 c1 c2) *ᵥ v ≠ v) : c0 * c2 - c1 * c1 ≠ 0 := by
  intro hd
  obtain ⟨u0, u1, hne, h0, h1⟩ := sing_ker c0 c1 c2 hd
  have hA : inA ![u0, u1, 0, 0] := ⟨rfl, rfl⟩
  have hne0 : (![u0, u1, 0, 0] : V4) ≠ 0 := fun h' => hne ⟨congrFun h' 0, congrFun h' 1⟩
  apply h _ hA hne0
  ext r
  fin_cases r <;> simp [blkX, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    first | linear_combination h0 | linear_combination h1

theorem item_normal {a : V4} (ha : inA a) {X T : M4} (hI : IsItem a X T) :
    ∃ s0 s1 s2 c0 c1 c2 d0 d1 d2 : F3,
      umat (-s0) (-s1) (-s2) * X * umat s0 s1 s2 = blkX c0 c1 c2 ∧
      umat (-s0) (-s1) (-s2) * T * umat s0 s1 s2 = blkT d0 d1 d2 ∧
      c0 * c2 - c1 * c1 ≠ 0 ∧ d0 * a 0 + d1 * a 1 = 0 ∧ d1 * a 0 + d2 * a 1 = 0 := by
  obtain ⟨n, hn, hn2, hn3⟩ := exists_fix hI.cube hI.noFix ![1, 0]
  obtain ⟨m, hm, hm2, hm3⟩ := exists_fix hI.cube hI.noFix ![0, 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hn2 hn3 hm2 hm3
  have hiso := hI.omega_fix hn hm
  simp only [omega4, hn2, hn3, hm2, hm3] at hiso
  have hs1 : m 0 = n 1 := by linear_combination -hiso
  have hgn : umat (n 0) (n 1) (m 1) *ᵥ ev 2 = n := by
    rw [mulVec_ev]
    ext r
    fin_cases r <;> simp [umat, hn2, hn3]
  have hgm : umat (n 0) (n 1) (m 1) *ᵥ ev 3 = m := by
    rw [mulVec_ev]
    ext r
    fin_cases r <;> simp [umat, hm2, hm3, hs1]
  have hN := umat_normEl (n 0) (n 1) (m 1)
  have hI' := hN.isItem ha hI
  have key : ∀ v, umat (-n 0) (-n 1) (-m 1) *ᵥ (umat (n 0) (n 1) (m 1) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, umat_neg_mul, Matrix.one_mulVec]
  have hY2 : (umat (-n 0) (-n 1) (-m 1) * X * umat (n 0) (n 1) (m 1)) *ᵥ ev 2 = ev 2 := by
    rw [NormEl.conj_apply, hgn, hn, ← key (ev 2), hgn]
  have hY3 : (umat (-n 0) (-n 1) (-m 1) * X * umat (n 0) (n 1) (m 1)) *ᵥ ev 3 = ev 3 := by
    rw [NormEl.conj_apply, hgm, hm, ← key (ev 3), hgm]
  refine ⟨n 0, n 1, m 1, ?_⟩
  generalize umat (-n 0) (-n 1) (-m 1) * X * umat (n 0) (n 1) (m 1) = Y at hI' hY2 hY3 ⊢
  generalize umat (-n 0) (-n 1) (-m 1) * T * umat (n 0) (n 1) (m 1) = Z at hI' ⊢
  have hYf := blk_of_cols (Y := Y) (μ := 1) (one_mul 1)
    (fun x y => by rw [one_mul]; exact hI'.symp x y)
    (by rw [one_smul]; exact hY2) (by rw [one_smul]; exact hY3)
  have hZf := blk_of_cols (Y := Z) (μ := -1) (by decide)
    (fun x y => by
      have h : omega4 (Z *ᵥ x) (Z *ᵥ y) = -omega4 x y := hI'.mult x y
      simpa using h)
    (by
      have h : Z *ᵥ ev 2 = -ev 2 := hI'.neg _ hY2
      simpa using h)
    (by
      have h : Z *ᵥ ev 3 = -ev 3 := hI'.neg _ hY3
      simpa using h)
  refine ⟨Y 2 0, Y 3 0, Y 3 1, Z 2 0, Z 3 0, Z 3 1, hYf, hZf, ?_, ?_, ?_⟩
  · apply det_ne_zero_of_noFix
    have := hI'.noFix
    rw [hYf] at this
    exact this
  · have hf := congrFun hI'.fixa 2
    rw [hZf] at hf
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, ha.1, ha.2] at hf
    linear_combination hf
  · have hf := congrFun hI'.fixa 3
    rw [hZf] at hf
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, ha.1, ha.2] at hf
    linear_combination hf

theorem item_normal_conj {a : V4} (ha : inA a) {X T : M4} (hI : IsItem a X T) :
    ∃ s0 s1 s2 c0 c1 c2 d0 d1 d2 : F3,
      X = umat s0 s1 s2 * blkX c0 c1 c2 * umat (-s0) (-s1) (-s2) ∧
      T = umat s0 s1 s2 * blkT d0 d1 d2 * umat (-s0) (-s1) (-s2) ∧
      IsItem a (blkX c0 c1 c2) (blkT d0 d1 d2) ∧
      c0 * c2 - c1 * c1 ≠ 0 ∧ d0 * a 0 + d1 * a 1 = 0 ∧ d1 * a 0 + d2 * a 1 = 0 := by
  obtain ⟨s0, s1, s2, c0, c1, c2, d0, d1, d2, hX, hT, hc, hd0, hd1⟩ := item_normal ha hI
  have hN := umat_normEl s0 s1 s2
  have hI' := hN.isItem ha hI
  rw [hX, hT] at hI'
  refine ⟨s0, s1, s2, c0, c1, c2, d0, d1, d2, ?_, ?_, hI', hc, hd0, hd1⟩
  · rw [← hX]
    exact (hN.conj_conj X).symm
  · rw [← hT]
    exact (hN.conj_conj T).symm

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
