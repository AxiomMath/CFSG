module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KCentSL
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K

section Class
open scoped MatrixGroups Matrix
open Matrix
open CFSG.LargeExtraspecial

public def star' {K : Type} [Field K] (bar : K →+* K) (u : Fin 3 → K) : Fin 3 → K :=
  fun i => bar (u i)

public def herm {K : Type} [Field K] (bar : K →+* K) (u v : Fin 3 → K) : K := u ⬝ᵥ star' bar v

public theorem star'_star' {K : Type} [Field K] (bar : K →+* K) (hbar : ∀ x, bar (bar x) = x)
    (v : Fin 3 → K) : star' bar (star' bar v) = v := by
  funext i
  simp [star', hbar]

public theorem star'_smul {K : Type} [Field K] (bar : K →+* K) (a : K) (v : Fin 3 → K) :
    star' bar (a • v) = bar a • star' bar v := by
  funext i
  simp [star']

public theorem star'_zero {K : Type} [Field K] (bar : K →+* K) :
    star' bar (0 : Fin 3 → K) = 0 := by
  funext i
  simp [star']

public theorem vecMulVec_mulVec' {K : Type} [Field K] (v w x : Fin 3 → K) :
    vecMulVec v w *ᵥ x = (w ⬝ᵥ x) • v := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

public theorem conjT_one_add_vecMulVec {K : Type} [Field K] (bar : K →+* K) (u φ : Fin 3 → K) :
    ((1 + vecMulVec u φ).map bar)ᵀ = 1 + vecMulVec (star' bar φ) (star' bar u) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [star', vecMulVec, Matrix.one_apply] <;> ring
  · simp [star', vecMulVec, Matrix.one_apply, hij, Ne.symm hij] <;> ring

public theorem tv_unitary {K : Type} [Field K] [CharP K 2] (bar : K →+* K)
    (hbar : ∀ x, bar (bar x) = x) {u : Fin 3 → K} {c : K}
    (hc : bar c = c) (hu : herm bar u u = 0) :
    ((c • star' bar u) ⬝ᵥ u = 0) ∧
    ((((A2Mod.tv u (c • star' bar u) : SL(3,K)) : Matrix (Fin 3) (Fin 3) K).map bar)ᵀ *
      ((A2Mod.tv u (c • star' bar u) : SL(3,K)) : Matrix (Fin 3) (Fin 3) K) = 1) := by
  have hQ : star' bar u ⬝ᵥ u = 0 := by
    rw [dotProduct_comm]
    exact hu
  have hdot : (c • star' bar u) ⬝ᵥ u = 0 := by
    rw [smul_dotProduct, hQ, smul_zero]
  refine ⟨hdot, ?_⟩
  have hφbar : star' bar (c • star' bar u) = c • u := by
    rw [star'_smul, star'_star' bar hbar, hc]
  rw [A2Mod.coe_tv hdot, conjT_one_add_vecMulVec, hφbar]
  have key : (1 + vecMulVec (c • u) (star' bar u)) * (1 + vecMulVec u (c • star' bar u))
      = 1 + (vecMulVec (c • u) (star' bar u) + vecMulVec u (c • star' bar u)) := by
    simp only [add_mul, mul_add, one_mul, mul_one, vecMulVec_mul_vecMulVec, hQ, zero_smul,
      vecMulVec_zero, add_zero]
    abel
  have hsum : vecMulVec (c • u) (star' bar u) + vecMulVec u (c • star' bar u) = 0 := by
    rw [smul_vecMulVec, vecMulVec_smul, ← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  rw [key, hsum, add_zero]

public theorem unitary_involution_tv {K : Type} [Field K] [CharP K 2] (bar : K →+* K)
    (hbar : ∀ x, bar (bar x) = x) {ξ : SL(3,K)} (hξ : ξ * ξ = 1) (hξ1 : ξ ≠ 1)
    (hU : (((ξ : Matrix (Fin 3) (Fin 3) K).map bar)ᵀ * (ξ : Matrix (Fin 3) (Fin 3) K) = 1)) :
    ∃ (u : Fin 3 → K) (c : K), u ≠ 0 ∧ c ≠ 0 ∧ bar c = c ∧ herm bar u u = 0 ∧
      ξ = A2Mod.tv u (c • star' bar u) := by
  obtain ⟨u, φ, hu0, hφ0, hφu, hξeq⟩ := exists_tv_of_involution' hξ hξ1
  have hA : (ξ : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec u φ := by
    rw [hξeq, A2Mod.coe_tv hφu]
  rw [hA, conjT_one_add_vecMulVec] at hU
  have hX : vecMulVec u φ + vecMulVec (star' bar φ) (star' bar u)
      + (star' bar u ⬝ᵥ u) • vecMulVec (star' bar φ) φ = 0 := by
    have key : (1 + vecMulVec (star' bar φ) (star' bar u)) * (1 + vecMulVec u φ)
        = 1 + (vecMulVec u φ + vecMulVec (star' bar φ) (star' bar u)
            + (star' bar u ⬝ᵥ u) • vecMulVec (star' bar φ) φ) := by
      simp only [add_mul, mul_add, one_mul, mul_one, vecMulVec_mul_vecMulVec, vecMulVec_smul]
      abel
    rw [key] at hU
    have h1 : (1 : Matrix (Fin 3) (Fin 3) K) + (vecMulVec u φ
        + vecMulVec (star' bar φ) (star' bar u)
        + (star' bar u ⬝ᵥ u) • vecMulVec (star' bar φ) φ) = 1 + 0 := by
      rw [add_zero]
      exact hU
    exact add_left_cancel h1
  obtain ⟨j, hj⟩ : ∃ j, φ j ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hφ0 (funext h)
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → K, φ ⬝ᵥ x = 1 :=
    ⟨Pi.single j (φ j)⁻¹, by rw [dotProduct_single, mul_inv_cancel₀ hj]⟩
  have hXx : (vecMulVec u φ + vecMulVec (star' bar φ) (star' bar u)
      + (star' bar u ⬝ᵥ u) • vecMulVec (star' bar φ) φ) *ᵥ x = 0 := by
    rw [hX, zero_mulVec]
  rw [add_mulVec, add_mulVec, smul_mulVec, vecMulVec_mulVec', vecMulVec_mulVec',
    vecMulVec_mulVec', hx] at hXx
  simp only [one_smul] at hXx
  have hv : u + (star' bar u ⬝ᵥ x + star' bar u ⬝ᵥ u) • star' bar φ = 0 := by
    rw [add_smul, ← add_assoc]
    exact hXx
  obtain ⟨κ, hκ⟩ : ∃ κ : K, κ = star' bar u ⬝ᵥ x + star' bar u ⬝ᵥ u := ⟨_, rfl⟩
  rw [← hκ] at hv
  have hu_eq : u = κ • star' bar φ := by
    have h1 := eq_neg_of_add_eq_zero_left hv
    rw [← neg_smul, CharTwo.neg_eq] at h1
    exact h1
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hu0
    rw [hu_eq, h0, zero_smul]
  have hφbar : star' bar φ = κ⁻¹ • u := by
    rw [hu_eq, inv_smul_smul₀ hκ0]
  obtain ⟨c, hc⟩ : ∃ c : K, c = bar κ⁻¹ := ⟨_, rfl⟩
  have hφeq : φ = c • star' bar u := by
    rw [hc, ← star'_star' bar hbar φ, hφbar, star'_smul]
  have hc0 : c ≠ 0 := by
    intro h0
    apply hφ0
    rw [hφeq, h0, zero_smul]
  have hφbar2 : star' bar φ = bar c • u := by
    rw [hφeq, star'_smul, star'_star' bar hbar]
  have hQ0 : star' bar u ⬝ᵥ u = 0 := by
    rw [hφeq, smul_dotProduct] at hφu
    exact (smul_eq_zero.mp hφu).resolve_left hc0
  have hsum : (c + bar c) • vecMulVec u (star' bar u) = 0 := by
    have h := hX
    rw [hφbar2, hφeq, hQ0, zero_smul, add_zero, vecMulVec_smul, smul_vecMulVec,
      ← add_smul] at h
    exact h
  have hū : star' bar u ≠ 0 := by
    intro h
    apply hu0
    rw [← star'_star' bar hbar u, h, star'_zero]
  have hM : vecMulVec u (star' bar u) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hu0 (funext h)
    obtain ⟨k, hk⟩ : ∃ k, star' bar u k ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hū (funext h)
    intro h0
    have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i k) h0
    have h1 : u i * star' bar u k = 0 := by
      simpa [vecMulVec] using h2
    exact mul_ne_zero hi hk h1
  have hcsum : c + bar c = 0 := by
    rcases smul_eq_zero.mp hsum with h | h
    · exact h
    · exact absurd h hM
  have hbarc : bar c = c := by
    have h2 : c + c = 0 := CharTwo.add_self_eq_zero c
    calc bar c = bar c + (c + c) := by rw [h2, add_zero]
      _ = (c + bar c) + c := by abel
      _ = c := by rw [hcsum, zero_add]
  have hherm : herm bar u u = 0 := by
    show u ⬝ᵥ star' bar u = 0
    rw [dotProduct_comm]
    exact hQ0
  refine ⟨u, c, hu0, hc0, hbarc, hherm, ?_⟩
  rw [hξeq, hφeq]


end Class

section Count
open Matrix

section Aux

variable {K : Type} [Field K]

lemma two_eq_zero_of_charP [CharP K 2] : (2 : K) = 0 := by
  rw [← Nat.cast_two, CharP.cast_eq_zero]

lemma herm_add_left (bar : K →+* K) (u u' v : Fin 3 → K) :
    herm bar (u + u') v = herm bar u v + herm bar u' v := by
  simp [herm, add_dotProduct]

lemma herm_add_right (bar : K →+* K) (u v v' : Fin 3 → K) :
    herm bar u (v + v') = herm bar u v + herm bar u v' := by
  have h : star' bar (v + v') = star' bar v + star' bar v' := by
    funext i
    simp [star']
  simp [herm, h, dotProduct_add]

lemma herm_smul_left (bar : K →+* K) (a : K) (u v : Fin 3 → K) :
    herm bar (a • u) v = a * herm bar u v := by
  simp [herm, smul_dotProduct]

lemma herm_smul_right (bar : K →+* K) (a : K) (u v : Fin 3 → K) :
    herm bar u (a • v) = bar a * herm bar u v := by
  have h : star' bar (a • v) = bar a • star' bar v := by
    funext i
    simp [star', map_mul]
  simp [herm, h, dotProduct_smul]

lemma herm_comm (bar : K →+* K) (hbar : ∀ x, bar (bar x) = x) (u v : Fin 3 → K) :
    herm bar v u = bar (herm bar u v) := by
  simp only [herm, star', dotProduct, map_sum, map_mul, hbar]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma herm_self_fixed (bar : K →+* K) (hbar : ∀ x, bar (bar x) = x) (u : Fin 3 → K) :
    bar (herm bar u u) = herm bar u u :=
  (herm_comm bar hbar u u).symm

lemma herm_zero_left (bar : K →+* K) (u : Fin 3 → K) : herm bar 0 u = 0 := by
  simp [herm]

lemma herm_comb_v (bar : K →+* K) {v w z : Fin 3 → K}
    (hvv : herm bar v v = 0) (hwv : herm bar w v = 1) (hzv : herm bar z v = 0) (a b c : K) :
    herm bar (a • v + b • w + c • z) v = b := by
  simp only [herm_add_left, herm_smul_left, hvv, hwv, hzv, mul_zero, mul_one, zero_add, add_zero]

lemma herm_comb_w (bar : K →+* K) {v w z : Fin 3 → K}
    (hvw : herm bar v w = 1) (hww : herm bar w w = 0) (hzw : herm bar z w = 0) (a b c : K) :
    herm bar (a • v + b • w + c • z) w = a := by
  simp only [herm_add_left, herm_smul_left, hvw, hww, hzw, mul_zero, mul_one, zero_add, add_zero]

lemma herm_comb_vv (bar : K →+* K) {v w z : Fin 3 → K}
    (hvv : herm bar v v = 0) (hvw : herm bar v w = 1) (hvz : herm bar v z = 0)
    (hwv : herm bar w v = 1) (hww : herm bar w w = 0) (hwz : herm bar w z = 0)
    (hzv : herm bar z v = 0) (hzw : herm bar z w = 0) (a b c : K) :
    herm bar (a • v + b • w + c • z) (a • v + b • w + c • z)
      = a * bar b + b * bar a + c * bar c * herm bar z z := by
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hvv, hvw, hvz,
    hwv, hww, hwz, hzv, hzw]
  ring

lemma exists_herm_eq_one (bar : K →+* K) (hbar : ∀ x, bar (bar x) = x) {v : Fin 3 → K}
    (hv : v ≠ 0) : ∃ u : Fin 3 → K, herm bar u v = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  have hbi : bar (v i) ≠ 0 := by
    intro h
    have h' := congrArg bar h
    rw [hbar, map_zero] at h'
    exact hi h'
  refine ⟨Pi.single i (bar (v i))⁻¹, ?_⟩
  simp [herm, star', single_dotProduct, hbi]

lemma exists_isotropic_partner (bar : K →+* K) (hbar : ∀ x, bar (bar x) = x) [CharP K 2]
    (htr : ∀ c : K, bar c = c → ∃ a : K, a + bar a = c) {v : Fin 3 → K} (hv : v ≠ 0)
    (hvv : herm bar v v = 0) :
    ∃ w : Fin 3 → K, herm bar w v = 1 ∧ herm bar w w = 0 := by
  obtain ⟨u0, hu0⟩ := exists_herm_eq_one bar hbar hv
  obtain ⟨a, ha⟩ := htr (herm bar u0 u0) (herm_self_fixed bar hbar u0)
  have hvu0 : herm bar v u0 = 1 := by
    rw [herm_comm bar hbar, hu0, map_one]
  refine ⟨u0 + a • v, ?_, ?_⟩
  · simp only [herm_add_left, herm_smul_left, hvv, hu0, mul_zero, add_zero]
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hvv, hu0, hvu0,
      mul_zero, mul_one]
    linear_combination ha + (herm bar u0 u0) * two_eq_zero_of_charP (K := K)

lemma exists_common_kernel (bar : K →+* K) (v w : Fin 3 → K) :
    ∃ z : Fin 3 → K, z ≠ 0 ∧ herm bar z v = 0 ∧ herm bar z w = 0 := by
  let M : Matrix (Fin 3) (Fin 3) K := Matrix.of ![star' bar v, star' bar w, 0]
  have hdet : M.det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (2 : Fin 3)
    intro j
    fin_cases j <;> first | rfl | simp [M]
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨z, hz0, ?_, ?_⟩
  · have h0 : star' bar v ⬝ᵥ z = 0 := by
      first
        | exact congrFun hz 0
        | simpa [M, Matrix.mulVec, dotProduct] using congrFun hz 0
    rw [herm, dotProduct_comm]
    exact h0
  · have h1 : star' bar w ⬝ᵥ z = 0 := by
      first
        | exact congrFun hz 1
        | simpa [M, Matrix.mulVec, dotProduct] using congrFun hz 1
    rw [herm, dotProduct_comm]
    exact h1

lemma lin_aux (bar : K →+* K) (hbar : ∀ x, bar (bar x) = x) {v w z : Fin 3 → K}
    (hvv : herm bar v v = 0) (hwv : herm bar w v = 1) (hww : herm bar w w = 0)
    (hzv : herm bar z v = 0) (hzw : herm bar z w = 0) (hz0 : z ≠ 0)
    (x0 x1 x2 : K) (h : x0 • v + x1 • w + x2 • z = 0) : x0 = 0 ∧ x1 = 0 ∧ x2 = 0 := by
  have hvw : herm bar v w = 1 := by
    rw [herm_comm bar hbar, hwv, map_one]
  have hherm0 : ∀ u : Fin 3 → K, herm bar 0 u = 0 := fun u => herm_zero_left bar u
  have hx1 : x1 = 0 := by
    have e := herm_comb_v bar hvv hwv hzv x0 x1 x2
    rw [h, hherm0] at e
    exact e.symm
  have hx0 : x0 = 0 := by
    have e := herm_comb_w bar hvw hww hzw x0 x1 x2
    rw [h, hherm0] at e
    exact e.symm
  have hx2 : x2 = 0 := by
    have hx2z : x2 • z = 0 := by
      rw [hx0, hx1] at h
      simpa using h
    exact (smul_eq_zero.mp hx2z).resolve_right hz0
  exact ⟨hx0, hx1, hx2⟩

lemma span_aux (v w z : Fin 3 → K)
    (hlin : ∀ x0 x1 x2 : K, x0 • v + x1 • w + x2 • z = 0 → x0 = 0 ∧ x1 = 0 ∧ x2 = 0) :
    ∀ u : Fin 3 → K, ∃ x0 x1 x2 : K, x0 • v + x1 • w + x2 • z = u := by
  have hli : LinearIndependent K ![v, w, z] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • v + g 1 • w + g 2 • z = 0 := by
      simpa [Fin.sum_univ_three] using hg
    obtain ⟨h0, h1, h2⟩ := hlin (g 0) (g 1) (g 2) hg'
    intro i
    fin_cases i <;> simp [h0, h1, h2]
  have htop : Submodule.span K (Set.range ![v, w, z]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  intro u
  have hu : u ∈ Submodule.span K (Set.range ![v, w, z]) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
  refine ⟨c 0, c 1, c 2, ?_⟩
  rw [← hc, Fin.sum_univ_three]
  simp

def trc (bar : K →+* K) : K →+ K where
  toFun x := x + bar x
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; ring

lemma add_bar_eq_zero_iff [CharP K 2] (bar : K →+* K) (x : K) :
    x + bar x = 0 ↔ bar x = x := by
  constructor
  · intro h
    linear_combination h - x * two_eq_zero_of_charP (K := K)
  · intro h
    rw [h]
    linear_combination x * two_eq_zero_of_charP (K := K)

lemma mem_ker_trc_iff [CharP K 2] (bar : K →+* K) (x : K) :
    x ∈ (trc bar).ker ↔ bar x = x := by
  rw [AddMonoidHom.mem_ker]
  exact add_bar_eq_zero_iff bar x

lemma card_ker_trc [CharP K 2] (bar : K →+* K) :
    Nat.card (trc bar).ker = Nat.card {x : K // bar x = x} :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun x => mem_ker_trc_iff bar x))

lemma card_range_mul_ker_trc (bar : K →+* K) :
    Nat.card (trc bar).range * Nat.card (trc bar).ker = Nat.card K := by
  rw [← AddSubgroup.index_ker, mul_comm]
  exact AddSubgroup.card_mul_index (H := (trc bar).ker)

lemma exists_trc_eq [Finite K] [CharP K 2] (bar : K →+* K) (hbar : ∀ x, bar (bar x) = x)
    (hfix : Nat.card {x : K // bar x = x} ^ 2 = Nat.card K) (c : K) (hc : bar c = c) :
    ∃ a : K, a + bar a = c := by
  haveI : Nonempty {x : K // bar x = x} := ⟨⟨0, map_zero bar⟩⟩
  have hq : 0 < Nat.card {x : K // bar x = x} := Nat.card_pos
  have hrange : Nat.card (trc bar).range = Nat.card {x : K // bar x = x} := by
    have h1 := card_range_mul_ker_trc bar
    rw [card_ker_trc bar, ← hfix] at h1
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [h1, sq]
  have hsub : ((trc bar).range : Set K) ⊆ {x : K | bar x = x} := by
    intro x hx
    rw [SetLike.mem_coe, AddMonoidHom.mem_range] at hx
    obtain ⟨α, rfl⟩ := hx
    show bar (α + bar α) = α + bar α
    rw [map_add, hbar, add_comm]
  have hF : ({x : K | bar x = x} : Set K).ncard = Nat.card {x : K // bar x = x} :=
    (Nat.card_coe_set_eq _).symm
  have hR : ((trc bar).range : Set K).ncard = Nat.card (trc bar).range :=
    (Nat.card_coe_set_eq _).symm
  have hset : ((trc bar).range : Set K) = {x : K | bar x = x} :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hF, hR, hrange]))
  have hmem : c ∈ ((trc bar).range : Set K) := by
    rw [hset]
    exact hc
  rw [SetLike.mem_coe, AddMonoidHom.mem_range] at hmem
  obtain ⟨α, hα⟩ := hmem
  exact ⟨α, hα⟩

lemma fiber_to_ker_aux (bar : K →+* K) {α c a : K} (hα : α + bar α = c)
    (ha : a + bar a = c) : (a - α) + bar (a - α) = 0 := by
  rw [map_sub]
  linear_combination ha - hα

lemma ker_to_fiber_aux (bar : K →+* K) {α c k : K} (hα : α + bar α = c)
    (hk : k + bar k = 0) : (k + α) + bar (k + α) = c := by
  rw [map_add]
  linear_combination hk + hα

lemma card_fiber_trc [Finite K] [CharP K 2] (bar : K →+* K) (hbar : ∀ x, bar (bar x) = x)
    (hfix : Nat.card {x : K // bar x = x} ^ 2 = Nat.card K) (c : K) (hc : bar c = c) :
    Nat.card {a : K // a + bar a = c} = Nat.card {x : K // bar x = x} := by
  obtain ⟨α, hα⟩ := exists_trc_eq bar hbar hfix c hc
  have e1 : Nat.card {a : K // a + bar a = c} = Nat.card {k : K // k + bar k = 0} :=
    Nat.card_congr
      { toFun := fun a => ⟨a.1 - α, fiber_to_ker_aux bar hα a.2⟩
        invFun := fun k => ⟨k.1 + α, ker_to_fiber_aux bar hα k.2⟩
        left_inv := fun a => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  have e2 : Nat.card {k : K // k + bar k = 0} = Nat.card {x : K // bar x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun k => add_bar_eq_zero_iff bar k))
  exact e1.trans e2

lemma image_mem [CharP K 2] (bar : K →+* K) {v w z : Fin 3 → K}
    (hvv : herm bar v v = 0) (hvw : herm bar v w = 1) (hvz : herm bar v z = 0)
    (hwv : herm bar w v = 1) (hww : herm bar w w = 0) (hwz : herm bar w z = 0)
    (hzv : herm bar z v = 0) (hzw : herm bar z w = 0) {γ α : K}
    (hp : α + bar α = (γ * bar γ) * herm bar z z) :
    herm bar (α • v + w + γ • z) (α • v + w + γ • z) = 0 ∧
      herm bar (α • v + w + γ • z) v = 1 := by
  have e : α • v + w + γ • z = α • v + (1 : K) • w + γ • z := by rw [one_smul]
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [herm_comb_vv bar hvv hvw hvz hwv hww hwz hzv hzw]
    simp only [map_one, one_mul, mul_one]
    linear_combination hp + ((γ * bar γ) * herm bar z z) * two_eq_zero_of_charP (K := K)
  · rw [herm_comb_v bar hvv hwv hzv]

end Aux

public theorem card_isotropic_affine {K : Type} [Field K] [Finite K] [CharP K 2] (bar : K →+* K)
    (hbar : ∀ x, bar (bar x) = x) (hfix : Nat.card {x : K // bar x = x} ^ 2 = Nat.card K)
    {v : Fin 3 → K} (hv : v ≠ 0) (hvv : herm bar v v = 0) :
    Nat.card {u : Fin 3 → K // herm bar u u = 0 ∧ herm bar u v = 1} =
      Nat.card {x : K // bar x = x} ^ 3 := by
  haveI : Fintype K := Fintype.ofFinite K
  have htr : ∀ c : K, bar c = c → ∃ a : K, a + bar a = c :=
    fun c hc => exists_trc_eq bar hbar hfix c hc
  obtain ⟨w, hwv, hww⟩ := exists_isotropic_partner bar hbar htr hv hvv
  obtain ⟨z, hz0, hzv, hzw⟩ := exists_common_kernel bar v w
  have hvw : herm bar v w = 1 := by
    rw [herm_comm bar hbar, hwv, map_one]
  have hvz : herm bar v z = 0 := by
    rw [herm_comm bar hbar, hzv, map_zero]
  have hwz : herm bar w z = 0 := by
    rw [herm_comm bar hbar, hzw, map_zero]
  have hlin : ∀ x0 x1 x2 : K, x0 • v + x1 • w + x2 • z = 0 → x0 = 0 ∧ x1 = 0 ∧ x2 = 0 :=
    fun x0 x1 x2 h => lin_aux bar hbar hvv hwv hww hzv hzw hz0 x0 x1 x2 h
  have hspan := span_aux v w z hlin
  have hfixed : ∀ γ : K, bar ((γ * bar γ) * herm bar z z) = (γ * bar γ) * herm bar z z := by
    intro γ
    rw [map_mul, map_mul, hbar, herm_self_fixed bar hbar z]
    ring
  let f : {c : K × K // c.2 + bar c.2 = (c.1 * bar c.1) * herm bar z z} →
      {u : Fin 3 → K // herm bar u u = 0 ∧ herm bar u v = 1} :=
    fun c => ⟨c.1.2 • v + w + c.1.1 • z,
      image_mem bar hvv hvw hvz hwv hww hwz hzv hzw c.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨γ, α⟩, hp⟩ ⟨⟨γ', α'⟩, hp'⟩ h
    have h' : α • v + w + γ • z = α' • v + w + γ' • z := congrArg Subtype.val h
    have key : (α - α') • v + (0 : K) • w + (γ - γ') • z = 0 := by
      have e : (α - α') • v + (0 : K) • w + (γ - γ') • z
          = (α • v + w + γ • z) - (α' • v + w + γ' • z) := by
        module
      rw [e, h', sub_self]
    obtain ⟨h0, -, h2⟩ := hlin _ _ _ key
    have hγ : γ = γ' := sub_eq_zero.mp h2
    have hα : α = α' := sub_eq_zero.mp h0
    subst hγ
    subst hα
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨u, hu1, hu2⟩
    obtain ⟨x0, x1, x2, hx⟩ := hspan u
    subst hx
    have hx1 : x1 = 1 := by
      have e := herm_comb_v bar hvv hwv hzv x0 x1 x2
      exact e.symm.trans hu2
    subst hx1
    have hp : x0 + bar x0 = (x2 * bar x2) * herm bar z z := by
      have e := hu1
      rw [herm_comb_vv bar hvv hvw hvz hwv hww hwz hzv hzw] at e
      simp only [map_one, one_mul, mul_one] at e
      linear_combination e - ((x2 * bar x2) * herm bar z z) * two_eq_zero_of_charP (K := K)
    refine ⟨⟨(x2, x0), hp⟩, ?_⟩
    apply Subtype.ext
    simp only [f, one_smul]
  have hcount : Nat.card {u : Fin 3 → K // herm bar u u = 0 ∧ herm bar u v = 1} =
      Nat.card {c : K × K // c.2 + bar c.2 = (c.1 * bar c.1) * herm bar z z} :=
    (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm
  rw [hcount]
  have hsig : Nat.card {c : K × K // c.2 + bar c.2 = (c.1 * bar c.1) * herm bar z z} =
      Nat.card (Σ γ : K, {α : K // α + bar α = (γ * bar γ) * herm bar z z}) :=
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (γ α : K) => α + bar α = (γ * bar γ) * herm bar z z))
  rw [hsig, Nat.card_sigma]
  have hfib : ∀ γ : K, Nat.card {α : K // α + bar α = (γ * bar γ) * herm bar z z} =
      Nat.card {x : K // bar x = x} :=
    fun γ => card_fiber_trc bar hbar hfix _ (hfixed γ)
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, ← hfix]
  ring


end Count

section HermExtra

variable {K : Type} [Field K] (bar : K →+* K)

theorem star'_dotProduct (u w : Fin 3 → K) : star' bar u ⬝ᵥ w = herm bar w u := by
  rw [herm, dotProduct_comm]

end HermExtra

abbrev KK (f : ℕ) := GaloisField 2 (2 * f)

section Cover
open scoped MatrixGroups Matrix

@[expose] noncomputable def SUsl (f : ℕ) : Subgroup SL(3, GaloisField 2 (2 * f)) :=
  (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f (GaloisField 2 (2 * f)) 3).comap
    (Matrix.SpecialLinearGroup.toGL)

theorem mem_SUsl_iff (f : ℕ) (hf : 1 ≤ f) {A : SL(3, GaloisField 2 (2 * f))} :
    A ∈ SUsl f ↔
      ((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))).map
          (CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField 2 f hf).bar)ᵀ *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) = 1 := by
  have h := CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField 2 f hf
  have hA : (Matrix.SpecialLinearGroup.toGL A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) =
      (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) := rfl
  unfold SUsl
  rw [Subgroup.mem_comap, CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, hA]
  exact ⟨fun hh => hh.2, fun hh => ⟨A.2, hh⟩⟩

theorem projSU_eq_range (f : ℕ) (hf : 1 ≤ f) :
    CFSG.PGLModel.projSU 3 2 f =
      ((Matrix.SpecialLinearGroup.toPGL : SL(3, GaloisField 2 (2 * f)) →*
        PGL(3, GaloisField 2 (2 * f))).comp (SUsl f).subtype).range := by
  have h := CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField 2 f hf
  rw [← CFSG.PGLModel.projImage_statedSU 3 2 f]
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    have hg' : g ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f (GaloisField 2 (2 * f)) 3 := hg
    obtain ⟨hdet, hmat⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 hg'
    have hsmem : ∀ s : SL(3, GaloisField 2 (2 * f)),
        (s : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) =
          (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) → s ∈ SUsl f := by
      intro s hs
      rw [mem_SUsl_iff f hf, hs]
      exact hmat
    refine MonoidHom.mem_range.2
      ⟨⟨⟨(g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))), hdet⟩,
        hsmem ⟨(g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))), hdet⟩ rfl⟩, ?_⟩
    have hgeq : Matrix.SpecialLinearGroup.toGL
        (⟨(g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))), hdet⟩ :
          SL(3, GaloisField 2 (2 * f))) = g :=
      Units.ext rfl
    show Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
        (⟨(g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))), hdet⟩ :
          SL(3, GaloisField 2 (2 * f)))) = Matrix.ProjGenLinGroup.mk g
    rw [hgeq]
  · intro hx
    obtain ⟨⟨s, hs⟩, rfl⟩ := MonoidHom.mem_range.1 hx
    exact Subgroup.mem_map.2 ⟨Matrix.SpecialLinearGroup.toGL s, Subgroup.mem_comap.1 hs, rfl⟩

@[expose] noncomputable def piSU (f : ℕ) (hf : 1 ≤ f) : ↥(SUsl f) →* ↥(CFSG.PGLModel.projSU 3 2 f) :=
  ((Matrix.SpecialLinearGroup.toPGL : SL(3, GaloisField 2 (2 * f)) →*
      PGL(3, GaloisField 2 (2 * f))).comp (SUsl f).subtype).codRestrict
    (CFSG.PGLModel.projSU 3 2 f) (fun s => by
      rw [projSU_eq_range f hf]
      exact MonoidHom.mem_range.2 ⟨s, rfl⟩)

theorem piSU_surjective (f : ℕ) (hf : 1 ≤ f) : Function.Surjective (piSU f hf) := by
  rintro ⟨x, hx⟩
  rw [projSU_eq_range f hf] at hx
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hx
  exact ⟨s, rfl⟩

theorem val_mem_center_of_mem_ker_piSU (f : ℕ) (hf : 1 ≤ f) {x : ↥(SUsl f)}
    (hx : x ∈ (piSU f hf).ker) :
    (x : SL(3, GaloisField 2 (2 * f))) ∈ Subgroup.center SL(3, GaloisField 2 (2 * f)) := by
  have h0 : piSU f hf x = 1 := MonoidHom.mem_ker.1 hx
  have h3 := congrArg Subtype.val h0
  have h1 : Matrix.SpecialLinearGroup.toPGL (x : SL(3, GaloisField 2 (2 * f))) = 1 := h3
  have h2 : (x : SL(3, GaloisField 2 (2 * f))) ∈
      (Matrix.SpecialLinearGroup.toPGL : SL(3, GaloisField 2 (2 * f)) →*
        PGL(3, GaloisField 2 (2 * f))).ker :=
    MonoidHom.mem_ker.2 h1
  rwa [Matrix.SpecialLinearGroup.toPGL_ker] at h2

theorem ker_piSU_le_center (f : ℕ) (hf : 1 ≤ f) :
    (piSU f hf).ker ≤ Subgroup.center ↥(SUsl f) := by
  intro x hx
  have hz := val_mem_center_of_mem_ker_piSU f hf hx
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hc := Subgroup.mem_center_iff.mp hz (g : SL(3, GaloisField 2 (2 * f)))
  simp only [Subgroup.coe_mul]
  exact hc

theorem odd_card_ker_piSU (f : ℕ) (hf : 1 ≤ f) : Odd (Nat.card (piSU f hf).ker) := by
  haveI : Finite (GaloisField 2 (2 * f)) :=
    (CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField 2 f hf).finite
  by_contra hodd
  have h2 : 2 ∣ Nat.card (piSU f hf).ker := by
    rcases Nat.even_or_odd (Nat.card (piSU f hf).ker) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := (piSU f hf).ker) 2 h2
  have h3 : ((g : ↥(SUsl f)) : SL(3, GaloisField 2 (2 * f))) ^ 3 = 1 :=
    pow_three_eq_one_of_mem_center (val_mem_center_of_mem_ker_piSU f hf g.2)
  have h4 : orderOf ((g : ↥(SUsl f)) : SL(3, GaloisField 2 (2 * f))) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one h3
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg] at h4
  omega


theorem coe_piSU (f : ℕ) (hf : 1 ≤ f) (x : ↥(SUsl f)) :
    ((piSU f hf x : ↥(CFSG.PGLModel.projSU 3 2 f)) : PGL(3, KK f)) =
      Matrix.SpecialLinearGroup.toPGL (x : SL(3, KK f)) := rfl

end Cover

section Glue
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Matrix
open CFSG.LargeExtraspecial

section Partners

variable (f : ℕ)

theorem card_partners_su (hf : 1 ≤ f) (τ : ↥(SUsl f)) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) :
    Nat.card {ξ : ↥(SUsl f) // ξ * ξ = 1 ∧
      (((τ : SL(3, KK f)) * (ξ : SL(3, KK f))) ^ 3 = 1 ∧ (ξ : SL(3, KK f)) ≠ (τ : SL(3, KK f)))}
      = 2 ^ (3 * f) := by
  classical
  have hU : UnitaryFieldData 2 f (KK f) :=
    CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField 2 f hf
  haveI : CharP (KK f) 2 := hU.charP
  haveI : Finite (KK f) := hU.finite
  set bar : KK f →+* KK f := hU.bar with hbar_def
  have hbb : ∀ x, bar (bar x) = x := hU.bar_bar
  have hτ' : (τ : SL(3, KK f)) * (τ : SL(3, KK f)) = 1 := by
    simpa using congrArg Subtype.val hτ
  have hτ1' : (τ : SL(3, KK f)) ≠ 1 := fun h => hτ1 (Subtype.ext (by rw [Subgroup.coe_one]; exact h))
  obtain ⟨v, d, hv, hd, hdbar, hvv, hτeq⟩ :=
    unitary_involution_tv bar hbb hτ' hτ1' ((mem_SUsl_iff f hf).1 τ.2)
  have hψv : (d • star' bar v) ⬝ᵥ v = 0 := (tv_unitary bar hbb hdbar hvv).1
  have hc : bar d⁻¹ = d⁻¹ := by rw [map_inv₀, hdbar]
  have hc0 : d⁻¹ ≠ 0 := inv_ne_zero hd
  have hF : Nat.card {x : KK f // bar x = x} = 2 ^ f := by
    rw [← hU.card_fixedField]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hU.mem_fixedField).symm)
  have hfix : Nat.card {x : KK f // bar x = x} ^ 2 = Nat.card (KK f) := by
    rw [hF, hU.card, ← pow_mul, mul_comm]
  have hA := card_isotropic_affine bar hbb hfix hv hvv
  have hcount : Nat.card {u : Fin 3 → KK f // herm bar u u = 0 ∧ herm bar u v = 1} = 2 ^ (3 * f) := by
    rw [hA, hF, ← pow_mul, Nat.mul_comm]
  rw [← hcount]
  have hdot1 : ∀ u : Fin 3 → KK f, herm bar u v = 1 → (d • star' bar v) ⬝ᵥ u = d := by
    intro u hu
    rw [smul_dotProduct, star'_dotProduct, hu, smul_eq_mul, mul_one]
  have hdot2 : ∀ u : Fin 3 → KK f, herm bar u v = 1 → (d⁻¹ • star' bar u) ⬝ᵥ v = d⁻¹ := by
    intro u hu
    rw [smul_dotProduct, star'_dotProduct, herm_comm bar hbb u v, hu, map_one, smul_eq_mul,
      mul_one]
  let Φ : {u : Fin 3 → KK f // herm bar u u = 0 ∧ herm bar u v = 1} →
      {ξ : ↥(SUsl f) // ξ * ξ = 1 ∧ (((τ : SL(3, KK f)) * (ξ : SL(3, KK f))) ^ 3 = 1 ∧
        (ξ : SL(3, KK f)) ≠ (τ : SL(3, KK f)))} := fun u =>
    ⟨⟨A2Mod.tv u.1 (d⁻¹ • star' bar u.1), (mem_SUsl_iff f hf).2 (tv_unitary bar hbb hc u.2.1).2⟩,
      Subtype.ext (by simpa using tv_involution (tv_unitary bar hbb hc u.2.1).1),
      by
        have key : ((d • star' bar v) ⬝ᵥ u.1) * ((d⁻¹ • star' bar u.1) ⬝ᵥ v) = 1 := by
          rw [hdot1 u.1 u.2.2, hdot2 u.1 u.2.2, mul_inv_cancel₀ hd]
        have h := (cube_iff_of_tv (tv_unitary bar hbb hc u.2.1).1 hψv).2 key
        rw [hτeq]
        exact h⟩
  have hinj : Function.Injective Φ := by
    intro u₁ u₂ h
    have h' : A2Mod.tv u₁.1 (d⁻¹ • star' bar u₁.1) = A2Mod.tv u₂.1 (d⁻¹ • star' bar u₂.1) :=
      congrArg (fun ξ : {ξ : ↥(SUsl f) // ξ * ξ = 1 ∧ (((τ : SL(3, KK f)) * (ξ : SL(3, KK f))) ^ 3 = 1 ∧
        (ξ : SL(3, KK f)) ≠ (τ : SL(3, KK f)))} => (ξ.1 : SL(3, KK f))) h
    have hx := congrArg (fun g : SL(3, KK f) => (g : Matrix (Fin 3) (Fin 3) (KK f)) *ᵥ v) h'
    simp only [A2Mod.tv_mulVec (tv_unitary bar hbb hc u₁.2.1).1,
      A2Mod.tv_mulVec (tv_unitary bar hbb hc u₂.2.1).1, hdot2 u₁.1 u₁.2.2,
      hdot2 u₂.1 u₂.2.2] at hx
    have := add_left_cancel hx
    exact Subtype.ext (smul_right_injective _ hc0 this)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨⟨ξ, hξS⟩, hξsq, hξP⟩
    obtain ⟨hξc, hξne⟩ : ((τ : SL(3, KK f)) * ξ) ^ 3 = 1 ∧ ξ ≠ (τ : SL(3, KK f)) := hξP
    have hξsq' : ξ * ξ = 1 := by simpa using congrArg Subtype.val hξsq
    have hξ1 : ξ ≠ 1 := by
      intro h1
      rw [h1, mul_one, pow_succ, pow_two, hτ', one_mul] at hξc
      exact hτ1' hξc
    obtain ⟨u₀, c₀, hu₀, hc₀, hc₀bar, hQ₀, hξeq⟩ :=
      unitary_involution_tv bar hbb hξsq' hξ1 ((mem_SUsl_iff f hf).1 hξS)
    have hφ₀ := (tv_unitary bar hbb hc₀bar hQ₀).1
    have hcube := (cube_iff_of_tv hφ₀ hψv).1 (by rw [← hξeq, ← hτeq]; exact ⟨hξc, hξne⟩)
    have e1 : (d • star' bar v) ⬝ᵥ u₀ = d * herm bar u₀ v := by
      rw [smul_dotProduct, star'_dotProduct, smul_eq_mul]
    have e2 : (c₀ • star' bar u₀) ⬝ᵥ v = c₀ * bar (herm bar u₀ v) := by
      rw [smul_dotProduct, star'_dotProduct, herm_comm bar hbb u₀ v, smul_eq_mul]
    rw [e1, e2] at hcube
    have hh0 : herm bar u₀ v ≠ 0 := by
      intro h
      rw [h] at hcube
      simp at hcube
    have hlam : bar (herm bar u₀ v)⁻¹ = (bar (herm bar u₀ v))⁻¹ := map_inv₀ bar _
    refine ⟨⟨(herm bar u₀ v)⁻¹ • u₀, ?_, ?_⟩, ?_⟩
    · rw [herm_smul_left, herm_smul_right, hQ₀, mul_zero, mul_zero]
    · rw [herm_smul_left]
      exact inv_mul_cancel₀ hh0
    · apply Subtype.ext
      apply Subtype.ext
      show A2Mod.tv ((herm bar u₀ v)⁻¹ • u₀) (d⁻¹ • star' bar ((herm bar u₀ v)⁻¹ • u₀)) = ξ
      rw [hξeq, A2Mod.tv_smul_left, star'_smul, hlam, smul_smul, smul_smul]
      congr 1
      congr 1
      have hbh : bar (herm bar u₀ v) ≠ 0 := by simpa using hh0
      field_simp
      linear_combination -hcube
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

end Partners

theorem card_s3Partners_projSU (f : ℕ) (hf : 1 ≤ f) (t : ↥(CFSG.PGLModel.projSU 3 2 f))
    (ht : orderOf t = 2) :
    Nat.card {x : ↥(CFSG.PGLModel.projSU 3 2 f) // orderOf x = 2 ∧ orderOf (t * x) = 3} =
      2 ^ (3 * f) := by
  haveI : CharP (KK f) 2 := (CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField 2 f hf).charP
  obtain ⟨τ, hτ, rfl⟩ := exists_involution_lift_of_cover (piSU f hf) (piSU_surjective f hf)
    (ker_piSU_le_center f hf) (odd_card_ker_piSU f hf) ht
  have hτ1' : piSU f hf τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hτ1 : τ ≠ 1 := fun h => hτ1' (by rw [h, map_one])
  have hτSL : (τ : SL(3, KK f)) * (τ : SL(3, KK f)) = 1 := by
    simpa using congrArg Subtype.val hτ
  have hτSL1 : (τ : SL(3, KK f)) ≠ 1 := fun h =>
    hτ1 (Subtype.ext (by rw [Subgroup.coe_one]; exact h))
  rw [card_partners_of_cover (piSU f hf) (piSU_surjective f hf) (ker_piSU_le_center f hf)
    (odd_card_ker_piSU f hf) τ hτ hτ1' (fun ξ => ((τ : SL(3, KK f)) * (ξ : SL(3, KK f))) ^ 3 = 1 ∧
      (ξ : SL(3, KK f)) ≠ (τ : SL(3, KK f))) ?_]
  · exact (Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _)
      (fun ξ => by constructor <;> rintro ⟨h1, h2, h3⟩ <;> tauto))).trans
      (card_partners_su f hf τ hτ hτ1)
  · intro ξ hξ
    have hξSL : (ξ : SL(3, KK f)) * (ξ : SL(3, KK f)) = 1 := by
      simpa using congrArg Subtype.val hξ
    by_cases hξ1 : (ξ : SL(3, KK f)) = 1
    · have hξ1' : ξ = 1 := Subtype.ext (by rw [Subgroup.coe_one]; exact hξ1)
      subst hξ1'
      have h3 : ((τ : SL(3, KK f)) * ((1 : ↥(SUsl f)) : SL(3, KK f))) ^ 3 ≠ 1 := by
        have : ((τ : SL(3, KK f)) * ((1 : ↥(SUsl f)) : SL(3, KK f))) ^ 3 = (τ : SL(3, KK f)) := by
          rw [Subgroup.coe_one, mul_one, pow_succ, pow_two, hτSL, one_mul]
        rw [this]
        exact hτSL1
      constructor
      · intro h
        rw [map_one, mul_one, ht] at h
        omega
      · rintro ⟨h, -⟩
        exact absurd h h3
    · obtain ⟨u, φ, hu, hφ, hφu, hξeq⟩ := exists_tv_of_involution' hξSL hξ1
      obtain ⟨v, ψ, hv, hψ, hψv, hτeq⟩ := exists_tv_of_involution' hτSL hτSL1
      have hcoe : ((piSU f hf τ * piSU f hf ξ : ↥(CFSG.PGLModel.projSU 3 2 f)) : PGL(3, KK f)) =
          Matrix.SpecialLinearGroup.toPGL (τ : SL(3, KK f)) *
            Matrix.SpecialLinearGroup.toPGL (ξ : SL(3, KK f)) := by
        rw [Subgroup.coe_mul, coe_piSU, coe_piSU]
      rw [← Subgroup.orderOf_coe, hcoe]
      have key := orderOf_toPGL_mul_eq_three_iff hφu hψv
      rw [← hξeq, ← hτeq] at key
      exact key

end Glue

theorem s3CountOK_projSU (f : ℕ) (hf : 1 ≤ f) : S3CountOK ↥(CFSG.PGLModel.projSU 3 2 f) := by
  intro t ht
  rw [card_s3Partners_projSU f hf t ht]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem s3CountOK_of_isLThreeEpsAt {T : Type} [Group T] (f : ℕ) (hf : 1 ≤ f)
    (hT : letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      CFSG.RankThree.PartTwo.Sec14.IsLThreeEpsAt T 2 f) : S3CountOK T := by
  have hT' : Nonempty (T ≃* ↥(CFSG.PGLModel.projSL 3 (GaloisField 2 f))) ∨
      (2 < 2 ^ f ∧ Nonempty (T ≃* ↥(CFSG.PGLModel.projSU 3 2 f))) := hT
  rcases hT' with h1 | ⟨-, h2⟩
  · obtain ⟨e⟩ := h1
    exact s3CountOK_of_mulEquiv e (s3CountOK_projSL f hf)
  · obtain ⟨e⟩ := h2
    exact s3CountOK_of_mulEquiv e (s3CountOK_projSU f hf)

end CFSG.RankThree.PartTwo.Sec15.F153L3K
