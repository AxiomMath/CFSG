module

public import CFSG.LocalAnalysis.StandardType.GGKGPosSUTorus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
public import CFSG.LieType.Universal.Unitary.Extras.RankOne
public import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.StandardType.KGPosSU

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

section SL2

variable {K : Type*} [Field K]

theorem exists_sl2_decomp (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) :
    ∃ e₁ e₂ e₃ e₄ : K, (∀ τ : K →+* K, (∀ i j, τ (A i j) = A i j) →
        τ e₁ = e₁ ∧ τ e₂ = e₂ ∧ τ e₃ = e₃ ∧ τ e₄ = e₄) ∧
      A = !![1, 0; e₁, 1] * !![1, e₂; 0, 1] * !![1, 0; e₃, 1] * !![1, e₄; 0, 1] := by
  rw [Matrix.det_fin_two] at hA
  by_cases hc : A 1 0 = 0
  · have ha : A 0 0 ≠ 0 := by
      intro h
      rw [h, hc] at hA
      simp at hA
    refine ⟨-1, (A 0 0 - 1) / A 0 0, A 0 0, (A 0 1 + A 1 1 - 1) / A 0 0, fun τ hτ => ?_, ?_⟩
    · simp only [map_neg, map_one, map_div₀, map_sub, map_add, hτ, and_self]
    · have hd : A 1 1 = (A 0 0)⁻¹ := by
        rw [hc, mul_zero, sub_zero] at hA
        exact eq_inv_of_mul_eq_one_right hA
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd] <;> field_simp <;> ring
  · refine ⟨0, (A 0 0 - 1) / A 1 0, A 1 0, (A 1 1 - 1) / A 1 0, fun τ hτ => ?_, ?_⟩
    · simp only [map_zero, map_one, map_div₀, map_sub, hτ, and_self]
    · ext i j
      have hb : A 0 1 = (A 0 0 * A 1 1 - 1) / A 1 0 := by
        rw [eq_div_iff hc]
        linear_combination -hA
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try rw [hb]) <;> field_simp <;> ring

end SL2

section Short

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ} (hσ : ∀ c, σ (σ c) = c)
  {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)

include hk in
theorem eq_one_of_isBlk_short {Q : SU σ n} (hblk : IsBlk (blkShort k hk) (mat σ n Q))
    (hb : toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n Q) = 1) : Q = 1 := by
  set p : Fin n := lowIdx k with hp
  set q : Fin n := lowIdx ⟨k.val + 1, hk⟩ with hq
  have hpq : p ≠ q := lowIdx_ne_succ hk
  have hpp : mat σ n Q p p = 1 := by simpa [toBlock] using congrFun (congrFun hb 0) 0
  have hpq' : mat σ n Q p q = 0 := by simpa [toBlock] using congrFun (congrFun hb 0) 1
  have hqp' : mat σ n Q q p = 0 := by simpa [toBlock] using congrFun (congrFun hb 1) 0
  have hqq : mat σ n Q q q = 1 := by simpa [toBlock] using congrFun (congrFun hb 1) 1
  have hblock : ∀ a b, (a = p ∨ a = q) → (b = p ∨ b = q) →
      mat σ n Q a b = (1 : Matrix (Fin n) (Fin n) F) a b := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · rw [hpp, Matrix.one_apply_eq]
    · rw [hpq', Matrix.one_apply_ne hpq]
    · rw [hqp', Matrix.one_apply_ne hpq.symm]
    · rw [hqq, Matrix.one_apply_eq]
  have hcol : ∀ s, (s = p ∨ s = q) → ∀ a, mat σ n Q a s = (1 : Matrix (Fin n) (Fin n) F) a s := by
    intro s hs a
    by_cases ha : a = p ∨ a = q
    · exact hblock a s ha hs
    · apply hblk a s
      rintro ⟨h1, -⟩
      rw [(blkShort_eq_one_iff hk s).mpr hs, blkShort_eq_one_iff] at h1
      exact ha h1
  apply mat_injective
  rw [map_one]
  ext a b
  by_cases hab : blkShort k hk a = blkShort k hk b ∧ blkShort k hk a ≠ 0
  · obtain ⟨h1, h2⟩ := hab
    by_cases ha1 : blkShort k hk a = 1
    · exact hblock a b ((blkShort_eq_one_iff hk a).mp ha1)
        ((blkShort_eq_one_iff hk b).mp (h1 ▸ ha1))
    · have ha2 : blkShort k hk a = 2 := by
        unfold blkShort at ha1 h2 ⊢
        split_ifs at ha1 h2 ⊢ <;> simp_all
      rcases (blkShort_eq_two_iff hk a).mp ha2 with rfl | rfl
      · exact mat_rev_apply_of_col (hcol p (Or.inl rfl)) b
      · exact mat_rev_apply_of_col (hcol q (Or.inr rfl)) b
  · exact hblk a b hab

include hk in
theorem mem_rankOne_of_isBlk_short {g : SU σ n} (hblk : IsBlk (blkShort k hk) (mat σ n g))
    (hdet : (toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g)).det = 1) :
    g ∈ rankOne (rootGroup σ hσ n) k := by
  obtain ⟨e₁, e₂, e₃, e₄, -, hA⟩ := exists_sl2_decomp _ hdet
  have hpq := lowIdx_ne_succ (n := n) hk
  let x : F → SU σ n := fun c =>
    rootHom σ hσ hpq (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (Multiplicative.ofAdd c)
  let y : F → SU σ n := fun c =>
    rootHom σ hσ hpq.symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev k k) (Multiplicative.ofAdd c)
  have hx : ∀ c, x c ∈ rootGroup σ hσ n (Pi.single k 1) := fun c =>
    rootHom_mem hσ _ _ _ (lowIdx_ne_rev _ _) (toStd_short hk).symm _
  have hy : ∀ c, y c ∈ rootGroup σ hσ n (-Pi.single k 1) := fun c =>
    rootHom_mem hσ _ _ _ (lowIdx_ne_rev _ _) (toStd_short_neg hk).symm _
  have hxL : ∀ c, x c ∈ rankOne (rootGroup σ hσ n) k := fun c => Subgroup.mem_sup_left (hx c)
  have hyL : ∀ c, y c ∈ rankOne (rootGroup σ hσ n) k := fun c => Subgroup.mem_sup_right (hy c)
  have hbx : ∀ c, toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n (x c)) = !![1, c; 0, 1] :=
    fun c => by
      have h : mat σ n (x c) (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) = c :=
        rootMatrix_apply_pq hpq (lowIdx_ne_rev _ _) c
      rw [toBlock_of_mem_pos hk (hx c), h]
  have hby : ∀ c, toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n (y c)) = !![1, 0; c, 1] :=
    fun c => by
      have h : mat σ n (y c) (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k) = c :=
        rootMatrix_apply_pq hpq.symm (lowIdx_ne_rev _ _) c
      rw [toBlock_of_mem_neg hk (hy c), h]
  have hTB : ∀ {u v : SU σ n}, u ∈ rankOne (rootGroup σ hσ n) k →
      toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n (u * v)) =
        toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n u) *
          toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n v) := fun hu => by
    rw [map_mul]
    exact toBlock_mul hpq (blkShort_hblk hk) (blkShort_succ_eq hk) (isBlk_short_of_mem hk hu).1
  let l := y e₁ * x e₂ * y e₃ * x e₄
  have hl1 : y e₁ * x e₂ ∈ rankOne (rootGroup σ hσ n) k := mul_mem (hyL _) (hxL _)
  have hl2 : y e₁ * x e₂ * y e₃ ∈ rankOne (rootGroup σ hσ n) k := mul_mem hl1 (hyL _)
  have hl : l ∈ rankOne (rootGroup σ hσ n) k := mul_mem hl2 (hxL _)
  have hbl : toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n l) =
      toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g) := by
    rw [hTB hl2, hTB hl1, hTB (hyL _), hbx, hby, hbx, hby, ← hA]
  have hQ : l⁻¹ * g = 1 := by
    apply eq_one_of_isBlk_short hk
    · rw [map_mul]
      exact (isBlk_short_of_mem hk (inv_mem hl)).1.mul hblk
    · rw [hTB (inv_mem hl), ← hbl, ← hTB (inv_mem hl), inv_mul_cancel, map_one,
        toBlock_one hpq]
  rw [← inv_mul_eq_one.mp hQ]
  exact hl

end Short

section Last

variable {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F} {n : ℕ} (hσ : ∀ c, σ (σ c) = c)
  {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) (he : Even n)

omit [CharP F 2] in
include he in
theorem eq_one_of_isBlk_last {Q : SU σ n} (hblk : IsBlk (blkLast k) (mat σ n Q))
    (hb : toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n Q) = 1) : Q = 1 := by
  have hpp := lowIdx_ne_rev (n := n) k k
  have hblock : ∀ a b, (a = lowIdx k ∨ a = Fin.rev (lowIdx k)) →
      (b = lowIdx k ∨ b = Fin.rev (lowIdx k)) →
      mat σ n Q a b = (1 : Matrix (Fin n) (Fin n) F) a b := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · simpa [toBlock] using congrFun (congrFun hb 0) 0
    · simpa [toBlock, Matrix.one_apply_ne hpp] using congrFun (congrFun hb 0) 1
    · simpa [toBlock, Matrix.one_apply_ne hpp.symm] using congrFun (congrFun hb 1) 0
    · simpa [toBlock] using congrFun (congrFun hb 1) 1
  apply mat_injective
  rw [map_one]
  ext a b
  by_cases hab : blkLast k a = blkLast k b ∧ blkLast k a ≠ 0
  · have ha := blkLast_eq_one_of_ne_zero hab.2
    have hb' : blkLast k b = 1 := hab.1 ▸ ha
    have hk1 : blkLast k (lowIdx k) = 1 := blkLast_mem (Or.inl rfl)
    exact hblock a b (blkLast_hblk_even he a (ha.trans hk1.symm))
      (blkLast_hblk_even he b (hb'.trans hk1.symm))
  · exact hblk a b hab

include he in
theorem toBlock_last_fixed {g : SU σ n} (hblk : IsBlk (blkLast k) (mat σ n g))
    (hdet : (toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n g)).det = 1) (i j : Fin 2) :
    σ (toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n g) i j) =
      toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n g) i j := by
  set p : Fin n := lowIdx k with hp
  have hpp : p ≠ Fin.rev p := lowIdx_ne_rev k k
  have hrr : Fin.rev (Fin.rev p) = p := Fin.rev_rev p
  have hout : ∀ t a, (a = p ∨ a = Fin.rev p) → ¬(t = p ∨ t = Fin.rev p) → mat σ n g t a = 0 := by
    intro t a ha ht
    have hta : t ≠ a := fun h => ht (h ▸ ha)
    rw [hblk t a (fun h => ?_), Matrix.one_apply_ne hta]
    have h1 := blkLast_eq_one_of_ne_zero h.2
    have hk1 : blkLast k (lowIdx k) = 1 := blkLast_mem (Or.inl rfl)
    exact ht (blkLast_hblk_even he t (h1.trans hk1.symm))
  have hsum : ∀ a b, (a = p ∨ a = Fin.rev p) →
      σ (mat σ n g p a) * mat σ n g (Fin.rev p) b +
        σ (mat σ n g (Fin.rev p) a) * mat σ n g p b = if b = Fin.rev a then 1 else 0 := by
    intro a b ha
    have h := sum_mat_mul_mat g a b
    rw [Finset.sum_eq_add p (Fin.rev p) hpp] at h
    · rw [hrr] at h
      exact h
    · intro t _ ht
      rw [hout t a ha (by tauto), map_zero, zero_mul]
    · simp
    · simp
  have e1 := hsum p p (Or.inl rfl)
  have e2 := hsum p (Fin.rev p) (Or.inl rfl)
  have e3 := hsum (Fin.rev p) p (Or.inr rfl)
  have e4 := hsum (Fin.rev p) (Fin.rev p) (Or.inr rfl)
  rw [if_neg hpp] at e1
  rw [if_pos rfl] at e2
  rw [hrr, if_pos rfl] at e3
  rw [hrr, if_neg hpp.symm] at e4
  rw [toBlock, Matrix.det_fin_two_of] at hdet
  set α := mat σ n g p p
  set β := mat σ n g p (Fin.rev p)
  set γ := mat σ n g (Fin.rev p) p
  set δ := mat σ n g (Fin.rev p) (Fin.rev p)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hα : σ α = α := by linear_combination (-σ α) * hdet + α * e2 - β * e1
  have hβ : σ β = β := by
    linear_combination (-σ β) * hdet - α * e4 + β * e3 + σ β * (α * δ - β * γ) * h2
  have hγ : σ γ = γ := by
    linear_combination (-σ γ) * hdet - δ * e1 + γ * e2 + σ γ * (α * δ - β * γ) * h2
  have hδ : σ δ = δ := by linear_combination (-σ δ) * hdet + δ * e3 - γ * e4
  fin_cases i <;> fin_cases j
  · exact hα
  · exact hβ
  · exact hγ
  · exact hδ

include hσ hk he in
theorem mem_rankOne_of_isBlk_last {g : SU σ n} (hblk : IsBlk (blkLast k) (mat σ n g))
    (hdet : (toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n g)).det = 1) :
    g ∈ rankOne (rootGroup σ hσ n) k := by
  obtain ⟨e₁, e₂, e₃, e₄, hfix, hA⟩ := exists_sl2_decomp _ hdet
  obtain ⟨f₁, f₂, f₃, f₄⟩ := hfix σ.toRingHom (toBlock_last_fixed he hblk hdet)
  have hpp := lowIdx_ne_rev (n := n) k k
  have hpp' : Fin.rev (lowIdx (n := n) k) ≠ Fin.rev (Fin.rev (lowIdx k)) := rev_ne_rev_rev hpp
  have htz : ∀ {e : F}, σ.toRingHom e = e → e ∈ traceZero σ := fun he' => by
    rw [mem_traceZero]
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at he'
    rw [he', CharTwo.add_self_eq_zero]
  let x : traceZero σ → SU σ n := fun c => longRootHom σ hpp (Multiplicative.ofAdd c)
  let y : traceZero σ → SU σ n := fun c => longRootHom σ hpp' (Multiplicative.ofAdd c)
  have hx : ∀ c, x c ∈ rootGroup σ hσ n (Pi.single k 1) := fun c =>
    longRootHom_mem hσ hpp (toStd_last_even hk he).symm _
  have hy : ∀ c, y c ∈ rootGroup σ hσ n (-Pi.single k 1) := fun c =>
    longRootHom_mem hσ hpp' (toStd_neg_last_even hk he).symm _
  have hxL : ∀ c, x c ∈ rankOne (rootGroup σ hσ n) k := fun c => Subgroup.mem_sup_left (hx c)
  have hyL : ∀ c, y c ∈ rankOne (rootGroup σ hσ n) k := fun c => Subgroup.mem_sup_right (hy c)
  have hbx : ∀ c, toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n (x c)) =
      !![1, (c : F); 0, 1] := fun c => by
    rw [mat_apply, coe_longRootHom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toBlock, longRootMatrix, hpp, hpp.symm]
  have hby : ∀ c, toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n (y c)) =
      !![1, 0; (c : F), 1] := fun c => by
    rw [mat_apply, coe_longRootHom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toBlock, longRootMatrix, hpp, hpp.symm]
  have hTB : ∀ {u v : SU σ n}, u ∈ rankOne (rootGroup σ hσ n) k →
      toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n (u * v)) =
        toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n u) *
          toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n v) := fun hu => by
    rw [map_mul]
    exact toBlock_mul hpp (blkLast_hblk_even he) (by
      rw [blkLast_mem (Or.inl rfl), blkLast_mem (Or.inr (Or.inl rfl))]) (isBlk_last_of_mem hk hu)
  let l := y ⟨e₁, htz f₁⟩ * x ⟨e₂, htz f₂⟩ * y ⟨e₃, htz f₃⟩ * x ⟨e₄, htz f₄⟩
  have hl1 : y ⟨e₁, htz f₁⟩ * x ⟨e₂, htz f₂⟩ ∈ rankOne (rootGroup σ hσ n) k :=
    mul_mem (hyL _) (hxL _)
  have hl2 : y ⟨e₁, htz f₁⟩ * x ⟨e₂, htz f₂⟩ * y ⟨e₃, htz f₃⟩ ∈ rankOne (rootGroup σ hσ n) k :=
    mul_mem hl1 (hyL _)
  have hl : l ∈ rankOne (rootGroup σ hσ n) k := mul_mem hl2 (hxL _)
  have hbl : toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n l) =
      toBlock (lowIdx k) (Fin.rev (lowIdx k)) (mat σ n g) := by
    rw [hTB hl2, hTB hl1, hTB (hyL _), hbx, hby, hbx, hby, ← hA]
  have hQ : l⁻¹ * g = 1 := by
    apply eq_one_of_isBlk_last he
    · rw [map_mul]
      exact (isBlk_last_of_mem hk (inv_mem hl)).mul hblk
    · rw [hTB (inv_mem hl), ← hbl, ← hTB (inv_mem hl), inv_mul_cancel, map_one,
        toBlock_one hpp]
  rw [← inv_mul_eq_one.mp hQ]
  exact hl

end Last

end CFSG.StandardType.KGPosSU

end
