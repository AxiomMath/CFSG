module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace KF11a

section Basic

variable {K : Type} [Field K] [CharP K 2]

lemma exists_sqrt [Finite K] (c : K) : ∃ t : K, t * t = c := by
  have hinj : Function.Injective (fun t : K => t * t) := by
    intro s t hst
    have hst' : s * s = t * t := hst
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h : (s - t) * (s - t) = 0 := by
      linear_combination hst' + (t * t - s * t) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
  exact Finite.surjective_of_injective hinj c

lemma mat_add_self {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι K) :
    X + X = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero _

lemma mat_neg_eq {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι K) :
    -X = X :=
  (eq_neg_of_add_eq_zero_left (mat_add_self X)).symm

lemma dot_transpose_left {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι K)
    (v X : ι → K) : (H *ᵥ v) ⬝ᵥ X = v ⬝ᵥ (Matrix.transpose H *ᵥ X) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

lemma dot_alt (v : Fin 2 ⊕ Fin 2 → K) :
    v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ v) = 0 := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks]
  ring

end Basic

section Core

variable {K : Type} [Field K] [CharP K 2]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma core_iso [Finite K] (Q T : Matrix ι ι K) (hQ : Matrix.transpose Q = Q)
    (hcard : Fintype.card ι = 4)
    (hL : Module.finrank K (LinearMap.ker Q.mulVecLin) = 2)
    (hnon : ∃ v : ι → K, v ⬝ᵥ (Q *ᵥ v) ≠ 0)
    (hT : ∀ v w : ι → K, (T *ᵥ v) ⬝ᵥ (Q *ᵥ (T *ᵥ w)) = v ⬝ᵥ (Q *ᵥ w))
    (hTL : ∀ v : ι → K, Q *ᵥ v = 0 → Q *ᵥ (T *ᵥ v) = 0) :
    ∀ v : ι → K, Q *ᵥ (((T * T) - 1) *ᵥ v) = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hvv : ∀ w : ι → K, w + w = 0 := fun w => funext fun i => CharTwo.add_self_eq_zero (w i)
  have hfin : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  set L : Submodule K (ι → K) := LinearMap.ker Q.mulVecLin with hLdef
  have memL : ∀ v : ι → K, v ∈ L ↔ Q *ᵥ v = 0 := fun v => by
    rw [hLdef, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hsym : ∀ v w : ι → K, v ⬝ᵥ (Q *ᵥ w) = w ⬝ᵥ (Q *ᵥ v) := by
    intro v w
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ, dotProduct_comm]
  have hradL : ∀ l : ι → K, Q *ᵥ l = 0 → ∀ w : ι → K, l ⬝ᵥ (Q *ᵥ w) = 0 := by
    intro l hl w
    rw [hsym, hl, dotProduct_zero]
  have hnonc := hnon
  have hnonrad : ∀ x : ι → K, Q *ᵥ x ≠ 0 → ∃ y : ι → K, x ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
    intro x hx
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hx
    funext i
    have h1 : ∀ y : ι → K, (Q *ᵥ x) ⬝ᵥ y = 0 := by
      intro y
      rw [dotProduct_comm, hsym]
      exact hcon y
    have h3 := h1 (Pi.single i 1)
    rw [dotProduct_single, mul_one] at h3
    simpa using h3
  obtain ⟨w1, hw1⟩ := hnon
  have hw1L : Q *ᵥ w1 ≠ 0 := by
    intro h
    apply hw1
    rw [h, dotProduct_zero]
  have hw1ne : w1 ≠ 0 := by
    rintro rfl
    exact hw1L (Matrix.mulVec_zero _)
  set S : Submodule K (ι → K) := L ⊔ Submodule.span K {w1} with hSdef
  have hSfin : Module.finrank K S < 4 := by
    have h1 : Module.finrank K S ≤
        Module.finrank K L + Module.finrank K (Submodule.span K {w1}) :=
      Submodule.finrank_add_le_finrank_add_finrank L (Submodule.span K {w1})
    rw [finrank_span_singleton hw1ne, hL] at h1
    omega
  have hSne : S ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hfin] at hSfin
    omega
  obtain ⟨w2, -, hw2S⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hSne)
  have hw2L : w2 ∉ L := fun h => hw2S (Submodule.mem_sup_left h)
  obtain ⟨x0, hx0q, hx0L⟩ : ∃ x0 : ι → K, x0 ⬝ᵥ (Q *ᵥ x0) = 0 ∧ Q *ᵥ x0 ≠ 0 := by
    by_cases hb : w2 ⬝ᵥ (Q *ᵥ w2) = 0
    · exact ⟨w2, hb, fun h => hw2L ((memL w2).mpr h)⟩
    · obtain ⟨t, ht⟩ := exists_sqrt ((w1 ⬝ᵥ (Q *ᵥ w1)) * (w2 ⬝ᵥ (Q *ᵥ w2))⁻¹)
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_mul] at ht
        exact mul_ne_zero hw1 (inv_ne_zero hb) ht.symm
      refine ⟨w1 + t • w2, ?_, ?_⟩
      · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
          dotProduct_smul, smul_dotProduct, smul_eq_mul]
        have hcross := hsym w1 w2
        have hb1 : (w2 ⬝ᵥ (Q *ᵥ w2)) * (w2 ⬝ᵥ (Q *ᵥ w2))⁻¹ = 1 := mul_inv_cancel₀ hb
        linear_combination (w2 ⬝ᵥ (Q *ᵥ w2)) * ht + (w1 ⬝ᵥ (Q *ᵥ w1)) * hb1
          + t * hcross + ((w1 ⬝ᵥ (Q *ᵥ w1)) + t * (w2 ⬝ᵥ (Q *ᵥ w1))) * h2
      · intro h
        have hmem : w1 + t • w2 ∈ S := Submodule.mem_sup_left ((memL _).mpr h)
        have hw1S : w1 ∈ S := Submodule.mem_sup_right (Submodule.mem_span_singleton_self w1)
        have htw2 : t • w2 ∈ S := by simpa using S.sub_mem hmem hw1S
        have hw2mem : w2 ∈ S := by
          simpa [smul_smul, inv_mul_cancel₀ ht0] using S.smul_mem t⁻¹ htw2
        exact hw2S hw2mem
  obtain ⟨y1, hy1⟩ := hnonrad x0 hx0L
  obtain ⟨y, hxy⟩ : ∃ y : ι → K, x0 ⬝ᵥ (Q *ᵥ y) = 1 :=
    ⟨(x0 ⬝ᵥ (Q *ᵥ y1))⁻¹ • y1, by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hy1]⟩
  have hli : LinearIndependent K ![x0, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : x0 ⬝ᵥ (Q *ᵥ (s • x0 + t • y)) = 0 := by
      rw [hst, Matrix.mulVec_zero, dotProduct_zero]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, hx0q, hxy,
      smul_eq_mul, mul_zero, mul_one, zero_add] at h1
    subst h1
    have hs : s • x0 = 0 := by simpa using hst
    rcases smul_eq_zero.mp hs with hs | hs
    · exact ⟨hs, rfl⟩
    · exact (hx0L (by rw [hs, Matrix.mulVec_zero])).elim
  have hPfin : Module.finrank K (Submodule.span K {x0, y}) = 2 := by
    have hrange : Set.range ![x0, y] = {x0, y} := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have h := finrank_span_eq_card hli
    rw [hrange] at h
    simpa using h
  have hPL : Submodule.span K {x0, y} ⊓ L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hzP, hzL⟩ := Submodule.mem_inf.mp hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hzP
    rw [memL] at hzL
    have h1 : x0 ⬝ᵥ (Q *ᵥ (s • x0 + t • y)) = 0 := by
      rw [hzL, dotProduct_zero]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, hx0q, hxy,
      smul_eq_mul, mul_zero, mul_one, zero_add] at h1
    subst h1
    simp only [zero_smul, add_zero] at hzL ⊢
    rw [Matrix.mulVec_smul] at hzL
    rcases smul_eq_zero.mp hzL with hs | hs
    · rw [hs, zero_smul]
    · exact (hx0L hs).elim
  have htop : Submodule.span K {x0, y} ⊔ L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {x0, y}) L
    rw [hPL, finrank_bot, hPfin, hL] at h
    rw [hfin]
    omega
  have hdec : ∀ v : ι → K, ∃ α β : K, ∃ l : ι → K, Q *ᵥ l = 0 ∧
      v = α • x0 + β • y + l := by
    intro v
    have hv : v ∈ Submodule.span K {x0, y} ⊔ L := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hp
    exact ⟨α, β, l, (memL l).mp hl, rfl⟩
  have hyx : y ⬝ᵥ (Q *ᵥ x0) = 1 := by
    rw [hsym]
    exact hxy
  have hform : ∀ α β α' β' : K, ∀ l l' : ι → K, Q *ᵥ l = 0 → Q *ᵥ l' = 0 →
      (α • x0 + β • y + l) ⬝ᵥ (Q *ᵥ (α' • x0 + β' • y + l')) =
        α * β' + β * α' + β * β' * (y ⬝ᵥ (Q *ᵥ y)) := by
    intro α β α' β' l l' hl hl'
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, hl', Matrix.mulVec_zero, dotProduct_zero, add_zero,
      smul_eq_mul, hx0q, hxy, hyx, hradL l hl x0, hradL l hl y]
    ring
  have hc : y ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
    obtain ⟨v, hv⟩ := hnonc
    obtain ⟨α, β, l, hl, rfl⟩ := hdec v
    rw [hform α β α β l l hl hl] at hv
    intro hc0
    apply hv
    linear_combination (α * β) * h2 + (β * β) * hc0
  have hiso : ∀ u : ι → K, u ⬝ᵥ (Q *ᵥ u) = 0 →
      ∃ α : K, ∃ l : ι → K, Q *ᵥ l = 0 ∧ u = α • x0 + l := by
    intro u hu
    obtain ⟨α, β, l, hl, rfl⟩ := hdec u
    rw [hform α β α β l l hl hl] at hu
    have hβ : β * β * (y ⬝ᵥ (Q *ᵥ y)) = 0 := by
      linear_combination hu - (α * β) * h2
    have hβ0 : β = 0 := by
      rcases mul_eq_zero.mp hβ with h | h
      · exact mul_self_eq_zero.mp h
      · exact absurd h hc
    exact ⟨α, l, hl, by rw [hβ0, zero_smul, add_zero]⟩
  have hDiso : ∀ v : ι → K, (T *ᵥ v - v) ⬝ᵥ (Q *ᵥ (T *ᵥ v - v)) = 0 := by
    intro v
    have h1 := hT v v
    have h3 := hsym v (T *ᵥ v)
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
    linear_combination h1 - h3 + ((v ⬝ᵥ (Q *ᵥ v)) - ((T *ᵥ v) ⬝ᵥ (Q *ᵥ v))) * h2
  have hDform : ∀ v : ι → K, ∃ α : K, ∃ l : ι → K, Q *ᵥ l = 0 ∧
      T *ᵥ v - v = α • x0 + l :=
    fun v => hiso _ (hDiso v)
  obtain ⟨s, l0, hl0, hTx0⟩ := hDform x0
  obtain ⟨s', l1, hl1, hTy⟩ := hDform y
  have eTx0 : T *ᵥ x0 = (1 + s) • x0 + (0 : K) • y + l0 := by
    linear_combination (norm := module) hTx0
  have eTy : T *ᵥ y = s' • x0 + (1 : K) • y + l1 := by
    linear_combination (norm := module) hTy
  have hs : s = 0 := by
    have h := hT x0 y
    rw [hxy, eTx0, eTy, hform (1 + s) 0 s' 1 l0 l1 hl0 hl1] at h
    linear_combination h
  have hTxL : Q *ᵥ (T *ᵥ x0 - x0) = 0 := by
    rw [hTx0, hs, zero_smul, zero_add]
    exact hl0
  have hTm : ∀ m : ι → K, Q *ᵥ m = 0 → Q *ᵥ (T *ᵥ m - m) = 0 := by
    intro m hm
    rw [Matrix.mulVec_sub, hTL m hm, hm, sub_zero]
  intro v
  obtain ⟨γ, m, hm, hu⟩ := hDform v
  have hkey : ((T * T) - 1) *ᵥ v = T *ᵥ (T *ᵥ v - v) - (T *ᵥ v - v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    have key : T *ᵥ (T *ᵥ v) - v - (T *ᵥ (T *ᵥ v) - T *ᵥ v - (T *ᵥ v - v)) =
        (T *ᵥ v + T *ᵥ v) - (v + v) := by
      abel
    rw [hvv (T *ᵥ v), hvv v, sub_zero] at key
    exact sub_eq_zero.mp key
  have hTu : T *ᵥ (T *ᵥ v - v) - (T *ᵥ v - v) = γ • (T *ᵥ x0 - x0) + (T *ᵥ m - m) := by
    rw [hu, Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
    abel
  rw [hkey, hTu, Matrix.mulVec_add, Matrix.mulVec_smul, hTxL, smul_zero, zero_add, hTm m hm]

end Core

section Sp

lemma range_eq_of_sq_zero {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (N : Matrix ι ι K) (hNN : N * N = 0) (hr : N.rank = 2) (hcard : Fintype.card ι = 4)
    (w : ι → K) (hw : N *ᵥ w = 0) : ∃ u : ι → K, N *ᵥ u = w := by
  have hfin : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  have hle : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    rintro _ ⟨u, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hNN,
      Matrix.zero_mulVec]
  have hrk := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have hr' : Module.finrank K (LinearMap.range N.mulVecLin) = 2 := hr
  have heq : LinearMap.range N.mulVecLin = LinearMap.ker N.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hwk : w ∈ LinearMap.ker N.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hw
  rw [← heq] at hwk
  obtain ⟨u, hu⟩ := hwk
  exact ⟨u, by simpa [Matrix.mulVecLin_apply] using hu⟩

end Sp

section Application

variable {K : Type} [Field K] [CharP K 2]

lemma c2_pow_four [Finite K] (G H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hG : Matrix.transpose G * Matrix.fromBlocks 0 1 (-1) 0 * G =
      Matrix.fromBlocks 0 1 (-1) 0)
    (hGG : G * G = 1) (hrank : (G - 1).rank = 2)
    (hnon : ∃ v : Fin 2 ⊕ Fin 2 → K,
      v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ (G *ᵥ v)) ≠ 0)
    (hH : Matrix.transpose H * Matrix.fromBlocks 0 1 (-1) 0 * H =
      Matrix.fromBlocks 0 1 (-1) 0)
    (hHG : H * G = G * H) : H ^ 4 = 1 := by
  classical
  have hcard : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
  set J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := Matrix.fromBlocks 0 1 (-1) 0 with hJdef
  set N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := G - 1 with hNdef
  have hNN : N * N = 0 := by
    have h1 : N * N = G * G - G - G + 1 := by
      rw [hNdef]
      noncomm_ring
    rw [h1, hGG]
    have h3 : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - G - G + 1 =
        (1 + 1) - (G + G) := by
      abel
    rw [h3, mat_add_self (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), mat_add_self G,
      sub_zero]
  have hGtJ : Matrix.transpose G * J = J * G := by
    calc Matrix.transpose G * J = Matrix.transpose G * J * (G * G) := by rw [hGG, mul_one]
      _ = (Matrix.transpose G * J * G) * G := by simp only [Matrix.mul_assoc]
      _ = J * G := by rw [hG]
  have hNtJ : Matrix.transpose N * J = J * N := by
    rw [hNdef, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul, hGtJ,
      Matrix.mul_sub, Matrix.mul_one]
  have hJT : Matrix.transpose J = -J := by
    rw [hJdef]
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  have hJT' : Matrix.transpose J = J := hJT.trans (mat_neg_eq J)
  have hJJ : J * J = 1 := by
    have h : J * J = -1 := by
      rw [hJdef, Matrix.fromBlocks_multiply]
      simp [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    rw [h, mat_neg_eq]
  set Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := J * N with hQdef
  have hQsymm : Matrix.transpose Q = Q := by
    rw [hQdef, Matrix.transpose_mul, hJT', hNtJ]
  have hHN : H * N = N * H := by
    rw [hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hHG]
  have hiff : ∀ v : Fin 2 ⊕ Fin 2 → K, Q *ᵥ v = 0 ↔ N *ᵥ v = 0 := by
    intro v
    have hJinv : ∀ w : Fin 2 ⊕ Fin 2 → K, J *ᵥ w = 0 → w = 0 := by
      intro w hw
      have e : w = J *ᵥ (J *ᵥ w) := by rw [Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
      rw [e, hw, Matrix.mulVec_zero]
    rw [hQdef, ← Matrix.mulVec_mulVec]
    constructor
    · exact hJinv _
    · intro h
      rw [h, Matrix.mulVec_zero]
  have hkerEq : LinearMap.ker Q.mulVecLin = LinearMap.ker N.mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hiff v
  have hkerN : Module.finrank K (LinearMap.ker N.mulVecLin) = 2 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    have hr' : Module.finrank K (LinearMap.range N.mulVecLin) = 2 := hrank
    have hfin : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card, hcard]
    omega
  have hL : Module.finrank K (LinearMap.ker Q.mulVecLin) = 2 := by
    rw [hkerEq]
    exact hkerN
  have hnonQ : ∃ v : Fin 2 ⊕ Fin 2 → K, v ⬝ᵥ (Q *ᵥ v) ≠ 0 := by
    obtain ⟨v, hv⟩ := hnon
    refine ⟨v, ?_⟩
    have hGv : G *ᵥ v = N *ᵥ v + v := by
      rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    have hQv : Q *ᵥ v = J *ᵥ (N *ᵥ v) := by rw [hQdef, Matrix.mulVec_mulVec]
    have hJv : v ⬝ᵥ (J *ᵥ v) = 0 := dot_alt v
    have hv' : v ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ (J *ᵥ (G *ᵥ v)) := by
      rw [hGv, Matrix.mulVec_add, dotProduct_add, hQv, hJv, add_zero]
    rw [hv']
    exact hv
  have hT : ∀ v w : Fin 2 ⊕ Fin 2 → K, (H *ᵥ v) ⬝ᵥ (Q *ᵥ (H *ᵥ w)) = v ⬝ᵥ (Q *ᵥ w) := by
    intro v w
    have e1 : Q *ᵥ (H *ᵥ w) = J *ᵥ (H *ᵥ (N *ᵥ w)) := by
      rw [hQdef]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [hHN]
    have e2 : ∀ z : Fin 2 ⊕ Fin 2 → K, Matrix.transpose H *ᵥ (J *ᵥ (H *ᵥ z)) = J *ᵥ z := by
      intro z
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
      rw [hH]
    have e3 : Q *ᵥ w = J *ᵥ (N *ᵥ w) := by rw [hQdef, Matrix.mulVec_mulVec]
    rw [e1, dot_transpose_left, e2, e3]
  have hTL : ∀ v : Fin 2 ⊕ Fin 2 → K, Q *ᵥ v = 0 → Q *ᵥ (H *ᵥ v) = 0 := by
    intro v hv
    apply (hiff _).mpr
    have hv' := (hiff v).mp hv
    rw [Matrix.mulVec_mulVec, ← hHN, ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero]
  have hcore := core_iso Q H hQsymm hcard hL hnonQ hT hTL
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := H * H - 1 with hMdef
  have hNM : ∀ v : Fin 2 ⊕ Fin 2 → K, N *ᵥ (M *ᵥ v) = 0 := fun v => (hiff _).mp (hcore v)
  have hHHN : (H * H) * N = N * (H * H) := by
    calc (H * H) * N = H * (H * N) := Matrix.mul_assoc _ _ _
      _ = H * (N * H) := by rw [hHN]
      _ = (H * N) * H := (Matrix.mul_assoc _ _ _).symm
      _ = (N * H) * H := by rw [hHN]
      _ = N * (H * H) := Matrix.mul_assoc _ _ _
  have hMN : M * N = N * M := by
    have e1 : M * N = (H * H) * N - N := by rw [hMdef, Matrix.sub_mul, Matrix.one_mul]
    have e2 : N * M = N * (H * H) - N := by rw [hMdef, Matrix.mul_sub, Matrix.mul_one]
    rw [e1, e2, hHHN]
  have MM : ∀ v : Fin 2 ⊕ Fin 2 → K, M *ᵥ (M *ᵥ v) = 0 := by
    intro v
    obtain ⟨u, hu⟩ := range_eq_of_sq_zero N hNN hrank hcard (M *ᵥ v) (hNM v)
    rw [← hu, Matrix.mulVec_mulVec, hMN, ← Matrix.mulVec_mulVec, hNM u]
  have hMM0 : M * M = 0 := by
    ext i j
    have h := MM (Pi.single j 1)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    simpa [Matrix.col] using congrFun h i
  have hsq : (H * H) * (H * H) + 1 = 0 := by
    have e : M * M = (H * H) * (H * H) + 1 := by
      rw [hMdef]
      calc (H * H - 1) * (H * H - 1) = (H * H) * (H * H) + 1 + (-((H * H) + (H * H))) := by
            noncomm_ring
        _ = (H * H) * (H * H) + 1 := by rw [mat_add_self (H * H), neg_zero, add_zero]
    rw [← e]
    exact hMM0
  have hPP : (H * H) * (H * H) = 1 := by
    have h := eq_neg_of_add_eq_zero_left hsq
    rw [h, mat_neg_eq]
  have hH4 : H ^ 4 = (H * H) * (H * H) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [hH4, hPP]

theorem sp4_c2_main (K : Type) [Field K] [Finite K] [CharP K 2]
    (g : ↥(CFSG.Open.StatedSp 2 K)) (hgg : g * g = 1)
    (hrk : (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1).rank = 2)
    (hnon : ∃ v : Fin 2 ⊕ Fin 2 → K,
      v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ
        (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)) ≠ 0) :
    IsPGroup 2 ↥(Subgroup.centralizer ({g} : Set ↥(CFSG.Open.StatedSp 2 K))) := by
  intro x
  refine ⟨2, ?_⟩
  have hx : (x : ↥(CFSG.Open.StatedSp 2 K)) * g = g * (x : ↥(CFSG.Open.StatedSp 2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mp x.2
  have hGG := congrArg (fun y : ↥(CFSG.Open.StatedSp 2 K) =>
    ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hgg
  have hHG := congrArg (fun y : ↥(CFSG.Open.StatedSp 2 K) =>
    ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hx
  simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at hGG hHG
  have hpow := c2_pow_four
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (((x : ↥(CFSG.Open.StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (CFSG.Open.StatedAPI.mem_statedSp_iff.mp g.2) hGG hrk hnon
    (CFSG.Open.StatedAPI.mem_statedSp_iff.mp (x : ↥(CFSG.Open.StatedSp 2 K)).2) hHG
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
  exact hpow

end Application

end KF11a

theorem sp4Involution_holds : Sp4InvolutionStatement := by
  intro K _ _ _ _ g hgg hrk hnon
  exact KF11a.sp4_c2_main K g hgg hrk hnon

end CFSG.RankThree.GF2n.Smith81.Smith23E1
