module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd

public section

open scoped Matrix

namespace CFSG.StandardType.TableBExc.E6Three

open CFSG.Blueprint.Chevalley

@[expose] def radE6 : Fin Tag.E6.rank → ZMod 3 := ![1, 0, 2, 0, 1, 2]

@[expose] def vInn : AddSubgroup (Fin Tag.E6.rank → ZMod 3) :=
  (AddMonoidHom.mk' (fun v : Fin Tag.E6.rank → ZMod 3 => v ⬝ᵥ radE6)
    (fun a b => add_dotProduct a b radE6)).ker

theorem mem_vInn_iff (v : Fin Tag.E6.rank → ZMod 3) : v ∈ vInn ↔ v ⬝ᵥ radE6 = 0 := by
  simp [vInn, AddMonoidHom.mem_ker]

theorem cartan_mulVec_radE6 (i : Fin Tag.E6.rank) :
    ∑ j, ((Tag.E6.cartan i j : ℤ) : ZMod 3) * radE6 j = 0 := by
  revert i
  decide

theorem cartan_diag (i : Fin Tag.E6.rank) : Tag.E6.cartan i i = 2 := by
  revert i
  decide

private def row (i : Fin Tag.E6.rank) : Fin Tag.E6.rank → ZMod 3 :=
  fun k => ((Tag.E6.cartan i k : ℤ) : ZMod 3)

private def coef (v : Fin Tag.E6.rank → ZMod 3) : Fin Tag.E6.rank → ZMod 3 :=
  ![v (0:Fin 6) + 2 * v (1:Fin 6) + v (2:Fin 6) + v (3:Fin 6) + 2 * v (4:Fin 6),
    2 * v (0:Fin 6) + 2 * v (1:Fin 6) + v (2:Fin 6),
    v (0:Fin 6) + v (1:Fin 6) + 2 * v (2:Fin 6) + 2 * v (3:Fin 6) + v (4:Fin 6),
    v (0:Fin 6) + 2 * v (2:Fin 6),
    2 * v (0:Fin 6) + v (2:Fin 6) + 2 * v (4:Fin 6),
    0]

private def row6 (i : Fin 6) : Fin 6 → ZMod 3 := fun k => ((Tag.E6.cartan i k : ℤ) : ZMod 3)

private def coef6 (v : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![v 0 + 2 * v 1 + v 2 + v 3 + 2 * v 4,
    2 * v 0 + 2 * v 1 + v 2,
    v 0 + v 1 + 2 * v 2 + 2 * v 3 + v 4,
    v 0 + 2 * v 2,
    2 * v 0 + v 2 + 2 * v 4,
    0]

private lemma cartan_symm (i j : Fin Tag.E6.rank) : Tag.E6.cartan i j = Tag.E6.cartan j i := by
  fin_cases i <;> fin_cases j <;> decide

private lemma adRefl_eq (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ZMod 3) :
    adRefl Tag.E6 3 i v = v - v i • row i := rfl

private lemma row_mem_vInn (i : Fin Tag.E6.rank) : row i ∈ vInn := by
  rw [mem_vInn_iff, dotProduct]
  exact cartan_mulVec_radE6 i

private lemma key5 : ∀ a b c d e f : ZMod 3, a + c * 2 + e + f * 2 = 0 →
    f = -(a * 2) - c - e * 2 := by decide

private lemma vInn_eq_sum_fin6 (w : Fin 6 → ZMod 3) (hw : w ⬝ᵥ radE6 = 0) :
    w = ∑ j : Fin 6, coef6 w j • row6 j := by
  have hw' : w 0 + w 2 * 2 + w 4 + w 5 * 2 = 0 := by
    have h := hw
    change (∑ i : Fin 6, w i * ![1, 0, 2, 0, 1, 2] i) = 0 at h
    simpa [Fin.sum_univ_six] using h
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h4 : (4 : ZMod 3) = 1 := by decide
  have h2' : (2 : ZMod 3) = -1 := by decide
  funext k
  rw [Finset.sum_apply]
  fin_cases k
  · simp [coef6, row6, Fin.sum_univ_six, Tag.cartan, Tag.cartanE]; ring_nf; simp [h3, h4, h2']
  · simp [coef6, row6, Fin.sum_univ_six, Tag.cartan, Tag.cartanE]; ring_nf; simp [h3, h4, h2']
  · simp [coef6, row6, Fin.sum_univ_six, Tag.cartan, Tag.cartanE]; ring_nf; simp [h3, h4, h2']
  · simp [coef6, row6, Fin.sum_univ_six, Tag.cartan, Tag.cartanE]
    ring_nf
    linear_combination (w 0 + w 1 + w 3 + w 4) * h3
  · simp [coef6, row6, Fin.sum_univ_six, Tag.cartan, Tag.cartanE]; ring_nf; simp [h3, h4, h2']
  · simp [coef6, row6, Fin.sum_univ_six, Tag.cartan, Tag.cartanE]
    ring_nf
    exact key5 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) hw'

private lemma vInn_eq_sum (v : Fin Tag.E6.rank → ZMod 3) (hv : v ⬝ᵥ radE6 = 0) :
    v = ∑ j : Fin Tag.E6.rank, coef v j • row j := by
  change (fun k : Fin 6 => v k) = ∑ j : Fin 6, coef (fun k : Fin 6 => v k) j • row6 j
  exact vInn_eq_sum_fin6 (fun k : Fin 6 => v k) hv

private lemma zmod_smul_mem {G : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ G) (c : ZMod 3) : c • x ∈ G := by
  have h1 : c • x = (c.val : ZMod 3) • x := by rw [ZMod.natCast_zmod_val]
  rw [h1, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem G hx c.val

private lemma vInn_le_of_rows {G : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    (h : ∀ j, row j ∈ G) : vInn ≤ G := by
  intro v hv
  rw [mem_vInn_iff] at hv
  rw [vInn_eq_sum v hv]
  exact AddSubgroup.sum_mem G (fun j _ => zmod_smul_mem (h j) (coef v j))

private lemma adRefl_row_self_apply (i k : Fin Tag.E6.rank) :
    adRefl Tag.E6 3 i (row i) k = (-row i) k := by
  fin_cases i <;> fin_cases k <;> decide

private lemma adRefl_row_self (i : Fin Tag.E6.rank) : adRefl Tag.E6 3 i (row i) = -row i :=
  funext (adRefl_row_self_apply i)

private lemma adRefl_row_edge_apply (i j k : Fin Tag.E6.rank) (hij : Tag.E6.cartan i j = -1) :
    adRefl Tag.E6 3 i (row j) k = (row j + row i) k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    (first | decide | (exfalso; exact absurd hij (by decide)))

private lemma adRefl_row_of_cartan_eq_neg_one (i j : Fin Tag.E6.rank)
    (hij : Tag.E6.cartan i j = -1) : adRefl Tag.E6 3 i (row j) = row j + row i :=
  funext fun k => adRefl_row_edge_apply i j k hij

private lemma e02 : Tag.E6.cartan (0:Fin 6) (2:Fin 6) = -1 := by decide
private lemma e13 : Tag.E6.cartan (1:Fin 6) (3:Fin 6) = -1 := by decide
private lemma e23 : Tag.E6.cartan (2:Fin 6) (3:Fin 6) = -1 := by decide
private lemma e32 : Tag.E6.cartan (3:Fin 6) (2:Fin 6) = -1 := by decide
private lemma e20 : Tag.E6.cartan (2:Fin 6) (0:Fin 6) = -1 := by decide
private lemma e31 : Tag.E6.cartan (3:Fin 6) (1:Fin 6) = -1 := by decide
private lemma e34 : Tag.E6.cartan (3:Fin 6) (4:Fin 6) = -1 := by decide
private lemma e43 : Tag.E6.cartan (4:Fin 6) (3:Fin 6) = -1 := by decide
private lemma e45 : Tag.E6.cartan (4:Fin 6) (5:Fin 6) = -1 := by decide
private lemma e54 : Tag.E6.cartan (5:Fin 6) (4:Fin 6) = -1 := by decide

private lemma row_mem_of_edge {G : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    (hG : ∀ i, ∀ v ∈ G, adRefl Tag.E6 3 i v ∈ G)
    (i j : Fin 6) (hij : Tag.E6.cartan i j = -1) (hi : row i ∈ G) : row j ∈ G := by
  have hsymm : Tag.E6.cartan j i = -1 := by
    rw [show Tag.E6.cartan j i = Tag.E6.cartan i j from by
      fin_cases i <;> fin_cases j <;> decide]
    exact hij
  have h1 : adRefl Tag.E6 3 j (row i) ∈ G := hG j (row i) hi
  have h2 : adRefl Tag.E6 3 j (row i) - row i = row j := by
    rw [adRefl_row_of_cartan_eq_neg_one j i hsymm]
    abel
  rw [← h2]
  exact G.sub_mem h1 hi

private lemma row_zero_mem_of_row_mem {G : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    (hG : ∀ i, ∀ v ∈ G, adRefl Tag.E6 3 i v ∈ G) {i : Fin Tag.E6.rank}
    (hi : row i ∈ G) : row (0:Fin 6) ∈ G := by
  fin_cases i
  · exact hi
  · exact row_mem_of_edge hG 2 0 e20 (row_mem_of_edge hG 3 2 e32 (row_mem_of_edge hG 1 3 e13 hi))
  · exact row_mem_of_edge hG 2 0 e20 hi
  · exact row_mem_of_edge hG 2 0 e20 (row_mem_of_edge hG 3 2 e32 hi)
  · exact row_mem_of_edge hG 2 0 e20 (row_mem_of_edge hG 3 2 e32 (row_mem_of_edge hG 4 3 e43 hi))
  · exact row_mem_of_edge hG 2 0 e20 (row_mem_of_edge hG 3 2 e32 (row_mem_of_edge hG 4 3 e43 (row_mem_of_edge hG 5 4 e54 hi)))

private lemma row_mem_of_row_zero {G : AddSubgroup (Fin Tag.E6.rank → ZMod 3)}
    (hG : ∀ i, ∀ v ∈ G, adRefl Tag.E6 3 i v ∈ G) (h0 : row (0:Fin 6) ∈ G) :
    ∀ j, row j ∈ G := by
  intro j
  fin_cases j
  · exact h0
  · exact row_mem_of_edge hG 3 1 e31 (row_mem_of_edge hG 2 3 e23 (row_mem_of_edge hG 0 2 e02 h0))
  · exact row_mem_of_edge hG 0 2 e02 h0
  · exact row_mem_of_edge hG 2 3 e23 (row_mem_of_edge hG 0 2 e02 h0)
  · exact row_mem_of_edge hG 3 4 e34 (row_mem_of_edge hG 2 3 e23 (row_mem_of_edge hG 0 2 e02 h0))
  · exact row_mem_of_edge hG 4 5 e45 (row_mem_of_edge hG 3 4 e34 (row_mem_of_edge hG 2 3 e23 (row_mem_of_edge hG 0 2 e02 h0)))

private lemma hstepB_scalar : ∀ x y : ZMod 3,
    x * -1 + y * 2 = x * -1 - x * -1 * 2 → y * 2 = x * 2 := by decide

private def cfunOf (f : (Fin Tag.E6.rank → ZMod 3) →+ (Fin Tag.E6.rank → ZMod 3)) :
    Fin Tag.E6.rank → ZMod 3 := fun i => 2 * (f (row i)) i

private lemma map_zmod_smul (f : (Fin Tag.E6.rank → ZMod 3) →+ (Fin Tag.E6.rank → ZMod 3))
    (c : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3) : f (c • x) = c • f x := by
  have h1 : c • x = c.val • x := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul]
  have h2 : c • f x = c.val • f x := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul]
  rw [h1, map_nsmul, ← h2]

theorem adRefl_dot_radE6 (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ZMod 3) :
    adRefl Tag.E6 3 i v ⬝ᵥ radE6 = v ⬝ᵥ radE6 := by
  rw [adRefl_eq, sub_eq_add_neg, add_dotProduct, neg_dotProduct, smul_dotProduct]
  have hrow : row i ⬝ᵥ radE6 = 0 := by
    rw [dotProduct]
    exact cartan_mulVec_radE6 i
  rw [hrow, smul_zero]
  abel

theorem adRefl_mem_vInn {i : Fin Tag.E6.rank} {v : Fin Tag.E6.rank → ZMod 3} (hv : v ∈ vInn) :
    adRefl Tag.E6 3 i v ∈ vInn := by
  rw [mem_vInn_iff] at hv ⊢
  rw [adRefl_dot_radE6, hv]

theorem adRefl_adRefl (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ZMod 3) :
    adRefl Tag.E6 3 i (adRefl Tag.E6 3 i v) = v := by
  funext k
  simp only [adRefl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, row]
  rw [cartan_diag i]
  norm_num
  ring

theorem eq_zero_of_forall_adRefl_eq {v : Fin Tag.E6.rank → ZMod 3}
    (h : ∀ i, adRefl Tag.E6 3 i v = v) : v = 0 := by
  funext i
  have h2 : v i • row i = 0 := by
    have hi := h i
    rw [adRefl_eq] at hi
    exact sub_eq_self.mp hi
  have h3 : (v i • row i) i = 0 := by rw [h2]; rfl
  simp only [Pi.smul_apply, smul_eq_mul, row] at h3
  rw [cartan_diag i, Int.cast_ofNat] at h3
  rcases mul_eq_zero.mp h3 with h0 | h0
  · exact h0
  · exact absurd h0 (by decide)

theorem vInn_le_of_invariant (G : AddSubgroup (Fin Tag.E6.rank → ZMod 3))
    (hG : ∀ i, ∀ v ∈ G, adRefl Tag.E6 3 i v ∈ G) (hne : G ≠ ⊥) : vInn ≤ G := by
  have hex : ∃ v ∈ G, v ≠ 0 := by
    by_contra h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  obtain ⟨v, hvG, hv0⟩ := hex
  have hcoord : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv0
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hcoord
  have hrowi : row i ∈ G := by
    have hpi : (v i) • row i ∈ G := by
      have h1 : v - adRefl Tag.E6 3 i v ∈ G := G.sub_mem hvG (hG i v hvG)
      have h2 : v - adRefl Tag.E6 3 i v = (v i) • row i := by
        rw [adRefl_eq]; abel
      rwa [h2] at h1
    have hd : (v i) ≠ 0 := hi
    have hrow_eq : row i = ((v i)⁻¹) • ((v i) • row i) := by
      rw [← mul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [hrow_eq]
    exact zmod_smul_mem hpi ((v i)⁻¹)
  have h0 := row_zero_mem_of_row_mem hG hrowi
  exact vInn_le_of_rows (row_mem_of_row_zero hG h0)

theorem exists_smul_of_commute_adRefl (f : (Fin Tag.E6.rank → ZMod 3) →+ (Fin Tag.E6.rank → ZMod 3))
    (hf : ∀ v ∈ vInn, f v ∈ vInn)
    (hc : ∀ i, ∀ v ∈ vInn, f (adRefl Tag.E6 3 i v) = adRefl Tag.E6 3 i (f v)) :
    ∃ c : ZMod 3, ∀ v ∈ vInn, f v = c • v := by
  have hstepA : ∀ i, f (row i) = cfunOf f i • row i := by
    intro i
    have hri : row i ∈ vInn := row_mem_vInn i
    have hcomm := hc i (row i) hri
    rw [adRefl_row_self] at hcomm
    rw [show f (-row i) = -f (row i) from map_neg f (row i)] at hcomm
    rw [adRefl_eq] at hcomm
    have h2 : (f (row i)) i • row i = (2 : ZMod 3) • f (row i) := by
      have hh : -f (row i) + (f (row i)) i • row i = f (row i) := by
        rw [hcomm]; abel
      calc (f (row i)) i • row i = -f (row i) + (f (row i)) i • row i + f (row i) := by abel
        _ = f (row i) + f (row i) := by rw [hh]
        _ = (2 : ZMod 3) • f (row i) := by rw [two_smul]
    have h3 : f (row i) = (2 : ZMod 3) • ((f (row i)) i • row i) := by
      calc f (row i) = (1 : ZMod 3) • f (row i) := (one_smul _ _).symm
        _ = ((2 : ZMod 3) * 2) • f (row i) := by rw [show (2 : ZMod 3) * 2 = 1 by decide]
        _ = (2 : ZMod 3) • ((2 : ZMod 3) • f (row i)) := by rw [mul_smul]
        _ = (2 : ZMod 3) • ((f (row i)) i • row i) := by rw [← h2]
    rw [h3, ← mul_smul]
    rfl
  have hstepB : ∀ i j, Tag.E6.cartan i j = -1 → cfunOf f i = cfunOf f j := by
    intro i j hij
    have hsymm : Tag.E6.cartan j i = -1 := by
      rw [cartan_symm j i]; exact hij
    have hri : row j ∈ vInn := row_mem_vInn j
    have hcomm := hc i (row j) hri
    rw [adRefl_row_of_cartan_eq_neg_one i j hij, map_add, hstepA i, hstepA j] at hcomm
    have hji' : ((Tag.E6.cartan j i : ℤ) : ZMod 3) = -1 := by
      rw [cartan_symm j i, hij]
      decide +kernel
    have hii' : ((Tag.E6.cartan i i : ℤ) : ZMod 3) = 2 := by
      rw [cartan_diag i]
      decide +kernel
    have hcoord := congrFun hcomm i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, adRefl, Pi.sub_apply, row] at hcoord
    rw [hji', hii'] at hcoord
    have h2 : cfunOf f i * 2 = cfunOf f j * 2 :=
      hstepB_scalar (cfunOf f j) (cfunOf f i) hcoord
    exact mul_right_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) h2
  have e02 : cfunOf f (0:Fin 6) = cfunOf f (2:Fin 6) := hstepB (0:Fin 6) (2:Fin 6) (by decide)
  have e23 : cfunOf f (2:Fin 6) = cfunOf f (3:Fin 6) := hstepB (2:Fin 6) (3:Fin 6) (by decide)
  have e34 : cfunOf f (3:Fin 6) = cfunOf f (4:Fin 6) := hstepB (3:Fin 6) (4:Fin 6) (by decide)
  have e13 : cfunOf f (1:Fin 6) = cfunOf f (3:Fin 6) := hstepB (1:Fin 6) (3:Fin 6) (by decide)
  have e45 : cfunOf f (4:Fin 6) = cfunOf f (5:Fin 6) := hstepB (4:Fin 6) (5:Fin 6) (by decide)
  have hcfun : ∀ i : Fin 6, cfunOf f i = cfunOf f (0:Fin 6) := by
    intro i
    fin_cases i
    · rfl
    · change cfunOf f (1:Fin 6) = cfunOf f (0:Fin 6)
      exact e13.trans (e23.symm.trans e02.symm)
    · change cfunOf f (2:Fin 6) = cfunOf f (0:Fin 6)
      exact e02.symm
    · change cfunOf f (3:Fin 6) = cfunOf f (0:Fin 6)
      exact e23.symm.trans e02.symm
    · change cfunOf f (4:Fin 6) = cfunOf f (0:Fin 6)
      exact e34.symm.trans (e23.symm.trans e02.symm)
    · change cfunOf f (5:Fin 6) = cfunOf f (0:Fin 6)
      exact e45.symm.trans (e34.symm.trans (e23.symm.trans e02.symm))
  refine ⟨cfunOf f (0:Fin 6), fun v hv => ?_⟩
  have hvsum := vInn_eq_sum v hv
  calc f v = f (∑ j, coef v j • row j) := congrArg f hvsum
    _ = ∑ j, f (coef v j • row j) := map_sum f _ _
    _ = ∑ j, coef v j • f (row j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact map_zmod_smul f (coef v j) (row j)
    _ = ∑ j, coef v j • (cfunOf f (0:Fin 6) • row j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hstepA j, hcfun j]
    _ = cfunOf f (0:Fin 6) • ∑ j, coef v j • row j := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm]
    _ = cfunOf f (0:Fin 6) • v := by
        conv_rhs => rw [hvsum]

end CFSG.StandardType.TableBExc.E6Three

end 