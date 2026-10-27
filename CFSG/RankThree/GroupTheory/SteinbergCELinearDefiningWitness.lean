module

public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.RankThree.Classical.SteinbergBJRectangularUnipotent

public section

namespace CFSG.RankThree.GroupTheory

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical CFSG.RankThree.CentralCover

variable {n : ℕ}

@[expose] def blockRows (h m c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i : ℕ) < h ∨ (m ≤ (i : ℕ) ∧ (i : ℕ) < c)

@[expose] def blockCols (h m c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (h ≤ (i : ℕ) ∧ (i : ℕ) < m) ∨ c ≤ (i : ℕ)

@[expose] def twoBlockRect (h m c : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij => ((ij.1 : ℕ) < h ∧ h ≤ (ij.2 : ℕ) ∧ (ij.2 : ℕ) < m) ∨
    (m ≤ (ij.1 : ℕ) ∧ (ij.1 : ℕ) < c ∧ c ≤ (ij.2 : ℕ))

theorem disjoint_blockRows_blockCols {h m c : ℕ} (hhm : h ≤ m) (hmc : m ≤ c) :
    Disjoint (blockRows (n := n) h m c) (blockCols h m c) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  simp only [blockRows, blockCols, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  omega

theorem twoBlockRect_subset (h m c : ℕ) :
    twoBlockRect (n := n) h m c ⊆ blockRows h m c ×ˢ blockCols h m c := by
  intro ij hij
  simp only [twoBlockRect, blockRows, blockCols, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product] at hij ⊢
  omega

theorem card_filter_fin_Ico {a b : ℕ} (hb : b ≤ n) :
    (Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b).card = b - a := by
  have h : (Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ) ∧ (i : ℕ) < b).map Fin.valEmbedding =
      Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Nat.card_Ico]

theorem card_twoBlockRect {h m c : ℕ} (hhm : h ≤ m) (hmc : m ≤ c) (hcn : c ≤ n) :
    (twoBlockRect (n := n) h m c).card = h * (m - h) + (c - m) * (n - c) := by
  classical
  have hsplit : twoBlockRect (n := n) h m c =
      ((Finset.univ.filter fun i : Fin n => 0 ≤ (i : ℕ) ∧ (i : ℕ) < h) ×ˢ
        (Finset.univ.filter fun i : Fin n => h ≤ (i : ℕ) ∧ (i : ℕ) < m)) ∪
      ((Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < c) ×ˢ
        (Finset.univ.filter fun i : Fin n => c ≤ (i : ℕ) ∧ (i : ℕ) < n)) := by
    ext ij
    simp only [twoBlockRect, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product]
    have := ij.2.2
    omega
  have hdisj : Disjoint
      ((Finset.univ.filter fun i : Fin n => 0 ≤ (i : ℕ) ∧ (i : ℕ) < h) ×ˢ
        (Finset.univ.filter fun i : Fin n => h ≤ (i : ℕ) ∧ (i : ℕ) < m))
      ((Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < c) ×ˢ
        (Finset.univ.filter fun i : Fin n => c ≤ (i : ℕ) ∧ (i : ℕ) < n)) := by
    rw [Finset.disjoint_left]
    intro ij h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h1 h2
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    card_filter_fin_Ico (by omega), card_filter_fin_Ico (by omega), card_filter_fin_Ico hcn,
    card_filter_fin_Ico le_rfl, Nat.sub_zero]

theorem half_mul_sub_half (s : ℕ) : s / 2 * (s - s / 2) = s ^ 2 / 4 := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' s
  · have h1 : 2 * t / 2 = t := by omega
    have h2 : (2 * t) ^ 2 = 4 * (t * t) := by ring
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num), show 2 * t - t = t by omega]
  · have h1 : (2 * t + 1) / 2 = t := by omega
    have h2 : (2 * t + 1) ^ 2 = 4 * (t * t + t) + 1 := by ring
    rw [h1, h2, show 2 * t + 1 - t = t + 1 by omega, show t * (t + 1) = t * t + t by ring]
    generalize t * t + t = q
    omega

variable {k : Type*} [Field k]

@[expose] def blockSign (n m : ℕ) (k : Type*) [Field k] : Matrix (Fin n) (Fin n) k :=
  Matrix.diagonal fun i => if (i : ℕ) < m then -1 else 1

theorem blockSign_mul_self (m : ℕ) : blockSign n m k * blockSign n m k = 1 := by
  rw [blockSign, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem det_blockSign {m : ℕ} (hm : Even m) (hmn : m ≤ n) : (blockSign n m k).det = 1 := by
  classical
  rw [blockSign, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
    mul_one]
  have hcard : (Finset.univ.filter fun i : Fin n => (i : ℕ) < m).card = m := by
    have h := card_filter_fin_Ico (n := n) (a := 0) hmn
    simp only [Nat.zero_le, true_and, Nat.sub_zero] at h
    exact h
  rw [hcard, hm.neg_one_pow]

theorem blockSign_mul_rect {m : ℕ} {R : Finset (Fin n × Fin n)}
    (hR : ∀ ij ∈ R, ((ij.1 : ℕ) < m ↔ (ij.2 : ℕ) < m)) (c : R → k) :
    blockSign n m k * (1 + rectSum R c) = (1 + rectSum R c) * blockSign n m k := by
  have hd : ∀ x : Fin n, (if (x : ℕ) < m then (-1 : k) else 1) ≠ 0 := fun x => by
    split_ifs <;> simp
  have hfun : (fun α : R => (if ((α : Fin n × Fin n).1 : ℕ) < m then (-1 : k) else 1) * c α *
      (if ((α : Fin n × Fin n).2 : ℕ) < m then (-1 : k) else 1)⁻¹) = c := by
    funext α
    have h := hR α.1 α.2
    by_cases h1 : ((α : Fin n × Fin n).1 : ℕ) < m
    · have h2 : ((α : Fin n × Fin n).2 : ℕ) < m := h.mp h1
      simp [h1, h2]
    · have h2 : ¬((α : Fin n × Fin n).2 : ℕ) < m := fun h2 => h1 (h.mpr h2)
      simp [h1, h2]
  rw [mul_add, add_mul, mul_one, one_mul, blockSign, diagonal_mul_rectSum _ hd, hfun]

theorem linear_defining_prime_central_cover_two_local_rank_witness {G : Type*} [Group G]
    [Finite G] (K : Subgroup G) {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) [Finite k]
    (hk : Nat.card k = p ^ f) (φ : K →* LinearFlag.projectiveSL n k)
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center K) {m : ℕ} (hm : Even m)
    (hm2 : 2 ≤ m) (hmn : m < n) :
    ∃ u : G, u ∈ K ∧ orderOf u = 2 ∧ ∃ V : Subgroup G,
      V ≤ K ⊓ Subgroup.centralizer ({u} : Set G) ∧ IsElemAbelian p V ∧
        Nat.card V = p ^ (f * (m ^ 2 / 4 + (n - m) ^ 2 / 4)) ∧
        f * (m ^ 2 / 4 + (n - m) ^ 2 / 4) ≤ localRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite k
  have : CharP k p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  have hp2 : p ≠ 2 := by omega
  set h := m / 2 with hh
  set c := m + (n - m) / 2 with hc
  have hhm : h ≤ m := Nat.div_le_self m 2
  have hmc : m ≤ c := Nat.le_add_right m _
  have hcn : c ≤ n := by omega
  set R := twoBlockRect (n := n) h m c
  have hIJ := disjoint_blockRows_blockCols (n := n) hhm hmc
  have hR := twoBlockRect_subset (n := n) h m c
  have hRcard : R.card = m ^ 2 / 4 + (n - m) ^ 2 / 4 := by
    rw [card_twoBlockRect hhm hmc hcn]
    obtain ⟨j, rfl⟩ := hm
    have h1 : (j + j) / 2 = j := by omega
    have h2 : (j + j) ^ 2 / 4 = j * j := by
      rw [show (j + j) ^ 2 = 4 * (j * j) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h1] at hh
    rw [hh, h2, show j + j - j = j by omega, show c - (j + j) = (n - (j + j)) / 2 by omega,
      show n - c = n - (j + j) - (n - (j + j)) / 2 by omega, half_mul_sub_half]
  obtain ⟨hUel, hUcard, hUcomm⟩ :=
    linear_rectangular_unipotent_central_preimage_abelian (k := k) hp hp3 hk hIJ hR
  have hdet := det_blockSign (k := k) hm hmn.le
  set z₀ : Matrix.SpecialLinearGroup (Fin n) k := ⟨blockSign n m k, hdet⟩
  set z := LinearFlag.proj n k z₀
  have hneg : (-1 : k) ≠ 1 := by
    intro h1
    have h2 : (2 : k) = 0 := by linear_combination -h1
    have h3 : ((2 : ℕ) : k) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff k p] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at h1
    obtain ⟨u, -, hu⟩ := h1
    have h0 := congrFun (congrFun hu ⟨0, by omega⟩) ⟨0, by omega⟩
    have hl := congrFun (congrFun hu ⟨n - 1, by omega⟩) ⟨n - 1, by omega⟩
    simp only [z₀, blockSign, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h0 hl
    rw [ite_eq_left (show (0 : ℕ) < m by omega)] at h0
    rw [ite_eq_right (show ¬(n - 1 < m) by omega)] at hl
    exact hneg (h0.trans hl.symm)
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have : z₀ * z₀ = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact blockSign_mul_self m)
    rw [this, map_one]
  have hz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzD : ∀ x ∈ rectUnipotent k hIJ hR, Commute z x := by
    rintro _ ⟨c', rfl⟩
    have hcomm : z₀ * rectHom k hIJ hR c' = rectHom k hIJ hR c' * z₀ := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      change blockSign n m k * (1 + rectSum R c'.toAdd) = (1 + rectSum R c'.toAdd) * _
      refine blockSign_mul_rect (fun ij hij => ?_) _
      simp only [R, twoBlockRect, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      omega
    change z * LinearFlag.proj n k (rectHom k hIJ hR c') =
      LinearFlag.proj n k (rectHom k hIJ hR c') * z
    rw [← map_mul, ← map_mul, hcomm]
  obtain ⟨u, huK, hu, V, hV, hVel, hVcard, -, -, hrank⟩ :=
    central_cover_involution_witness K hφ hZ hp hp2 (D := rectUnipotent k hIJ hR)
      (fun x hx => hUel.2 x hx) (fun x hx y hy => hUcomm φ hφ hZ x hx y hy)
      (r := f * R.card) hUcard.ge hz hzD
  rw [hRcard] at hVcard hrank
  exact ⟨u, huK, hu, V, hV, hVel, hVcard, hrank⟩

end CFSG.RankThree.GroupTheory
