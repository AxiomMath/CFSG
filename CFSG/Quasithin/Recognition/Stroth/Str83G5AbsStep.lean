module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5AbsConj
public import CFSG.Quasithin.Recognition.Stroth.Str83G5Pattern


public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

namespace Conf

variable {G : Type} [Group G] {n : ℕ}

private theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
    inv_inv]
  group

private theorem map_list_conj_mul (l : List (Subgroup G)) (a b : G) :
    (l.map fun T => T.map (MulAut.conj a).toMonoidHom).map
        (fun T => T.map (MulAut.conj b).toMonoidHom) =
      l.map fun T => T.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [List.map_map]
  exact List.map_congr_left fun T _ => map_conj_map_conj T a b

variable [Finite G] (c : Conf G n)

private theorem series_map_conj_x₁_inv {C D : Subgroup G} {l : List (Subgroup G)}
    {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H C l D) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ) :
    IsYSeries c.H (C.map (MulAut.conj c.x₁⁻¹).toMonoidHom)
        (l.map fun T => T.map (MulAut.conj c.x₁⁻¹).toMonoidHom)
        (D.map (MulAut.conj c.x₁⁻¹).toMonoidHom) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂)
          (l.map fun T => T.map (MulAut.conj c.x₁⁻¹).toMonoidHom)
          (D.map (MulAut.conj c.x₁⁻¹).toMonoidHom) = clsSets (μ.map (sigma1 c.m₀)) := by
  have hn : n ≠ 0 := by
    have := c.three_le
    omega
  have hN : 1 < 2 ^ n - 1 := by
    have := seven_le c.three_le
    omega
  have h1 : (c.x₁⁻¹)⁻¹ * c.d₁ * c.x₁⁻¹ =
      c.d₁ ^ (-1 : ZMod (2 ^ n - 1)).val * c.d₂ ^ (0 : ZMod (2 ^ n - 1)).val := by
    rw [inv_inv, c.conj₁₁, pow_val_neg_one (d := c.d₁) c.orderOf₁ hN, ZMod.val_zero,
      pow_zero, mul_one]
  have h2 : (c.x₁⁻¹)⁻¹ * c.d₂ * c.x₁⁻¹ =
      c.d₁ ^ (-2 * c.m₀).val * c.d₂ ^ (1 : ZMod (2 ^ n - 1)).val := by
    rw [inv_inv, c.conj₁₂, pow_val_one (d := c.d₂) hN]
  refine ⟨isYSeries_map_conj (inv_mem c.track.x₁_norm) hl, ?_⟩
  rw [facMultiset_chiLab_map_conj (a := -1) (b := 0) (a' := -2 * c.m₀) (b' := 1)
    hl c.d₁_mem_H c.d₂_mem_H hn c.orderOf_ζ h1 h2 hμ]
  congr 1
  refine Multiset.map_congr rfl fun φ _ => ?_
  ext <;> simp [sigma1] <;> ring

private theorem series_map_conj_x₂_inv {C D : Subgroup G} {l : List (Subgroup G)}
    {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H C l D) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ) :
    IsYSeries c.H (C.map (MulAut.conj c.x₂⁻¹).toMonoidHom)
        (l.map fun T => T.map (MulAut.conj c.x₂⁻¹).toMonoidHom)
        (D.map (MulAut.conj c.x₂⁻¹).toMonoidHom) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂)
          (l.map fun T => T.map (MulAut.conj c.x₂⁻¹).toMonoidHom)
          (D.map (MulAut.conj c.x₂⁻¹).toMonoidHom) = clsSets (μ.map (sigma2 c.k₀)) := by
  have hn : n ≠ 0 := by
    have := c.three_le
    omega
  have hN : 1 < 2 ^ n - 1 := by
    have := seven_le c.three_le
    omega
  have h1 : (c.x₂⁻¹)⁻¹ * c.d₁ * c.x₂⁻¹ =
      c.d₁ ^ (1 : ZMod (2 ^ n - 1)).val * c.d₂ ^ (-2 * c.k₀).val := by
    rw [inv_inv, c.conj₂₁, ← (c.commute.pow_right (-2 * c.k₀).val).eq,
      pow_val_one (d := c.d₁) hN]
  have h2 : (c.x₂⁻¹)⁻¹ * c.d₂ * c.x₂⁻¹ =
      c.d₁ ^ (0 : ZMod (2 ^ n - 1)).val * c.d₂ ^ (-1 : ZMod (2 ^ n - 1)).val := by
    rw [inv_inv, c.conj₂₂, ZMod.val_zero, pow_zero, one_mul,
      pow_val_neg_one (d := c.d₂) c.orderOf₂ hN]
  refine ⟨isYSeries_map_conj (inv_mem c.track.x₂_norm) hl, ?_⟩
  rw [facMultiset_chiLab_map_conj (a := 1) (b := -2 * c.k₀) (a' := 0) (b' := -1)
    hl c.d₁_mem_H c.d₂_mem_H hn c.orderOf_ζ h1 h2 hμ]
  congr 1
  refine Multiset.map_congr rfl fun φ _ => ?_
  ext <;> simp [sigma2] <;> ring

private theorem series_map_conj_tau_one {C D : Subgroup G} {l : List (Subgroup G)}
    {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H C l D) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ) :
    IsYSeries c.H (C.map (MulAut.conj (c.x₂ * c.x₁)).toMonoidHom)
        (l.map fun T => T.map (MulAut.conj (c.x₂ * c.x₁)).toMonoidHom)
        (D.map (MulAut.conj (c.x₂ * c.x₁)).toMonoidHom) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂)
          (l.map fun T => T.map (MulAut.conj (c.x₂ * c.x₁)).toMonoidHom)
          (D.map (MulAut.conj (c.x₂ * c.x₁)).toMonoidHom) =
        clsSets (μ.map (mPow c.k₀ c.m₀ 1)) := by
  obtain ⟨hl1, hμ1⟩ := c.series_map_conj_x₁ hl hμ
  obtain ⟨hl2, hμ2⟩ := c.series_map_conj_x₂ hl1 hμ1
  refine ⟨?_, ?_⟩
  · have hD := map_conj_map_conj D c.x₁ c.x₂
    rw [hD, map_conj_map_conj, map_list_conj_mul] at hl2
    exact hl2
  · have hD := map_conj_map_conj D c.x₁ c.x₂
    rw [hD, map_list_conj_mul] at hμ2
    rw [hμ2, Multiset.map_map]
    congr 1

private theorem series_map_conj_tau_neg_one {C D : Subgroup G} {l : List (Subgroup G)}
    {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H C l D) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ) :
    IsYSeries c.H (C.map (MulAut.conj ((c.x₂ * c.x₁) ^ (-1 : ℤ))).toMonoidHom)
        (l.map fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ (-1 : ℤ))).toMonoidHom)
        (D.map (MulAut.conj ((c.x₂ * c.x₁) ^ (-1 : ℤ))).toMonoidHom) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂)
          (l.map fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ (-1 : ℤ))).toMonoidHom)
          (D.map (MulAut.conj ((c.x₂ * c.x₁) ^ (-1 : ℤ))).toMonoidHom) =
        clsSets (μ.map (mPow c.k₀ c.m₀ (-1))) := by
  have hτ : (c.x₂ * c.x₁) ^ (-1 : ℤ) = c.x₁⁻¹ * c.x₂⁻¹ := by
    rw [zpow_neg_one, mul_inv_rev]
  rw [hτ]
  obtain ⟨hl1, hμ1⟩ := c.series_map_conj_x₂_inv hl hμ
  obtain ⟨hl2, hμ2⟩ := c.series_map_conj_x₁_inv hl1 hμ1
  refine ⟨?_, ?_⟩
  · have hD := map_conj_map_conj D c.x₂⁻¹ c.x₁⁻¹
    rw [hD, map_conj_map_conj, map_list_conj_mul] at hl2
    exact hl2
  · have hD := map_conj_map_conj D c.x₂⁻¹ c.x₁⁻¹
    rw [hD, map_list_conj_mul] at hμ2
    rw [hμ2, Multiset.map_map]
    congr 1

private theorem series_map_conj_tau (t : ℤ) {C D : Subgroup G} {l : List (Subgroup G)}
    {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H C l D) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ) :
    IsYSeries c.H (C.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom)
        (l.map fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom)
        (D.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂)
          (l.map fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom)
          (D.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom) =
        clsSets (μ.map (mPow c.k₀ c.m₀ t)) := by
  induction t using Int.induction_on generalizing C D l μ with
  | zero =>
    have hmap : ∀ K : Subgroup G,
        K.map (MulAut.conj ((c.x₂ * c.x₁) ^ (0 : ℤ))).toMonoidHom = K := by
      intro K
      rw [zpow_zero, map_one MulAut.conj, MulAut.one_def]
      exact Subgroup.map_id K
    have hlist : (l.map fun T => T.map
        (MulAut.conj ((c.x₂ * c.x₁) ^ (0 : ℤ))).toMonoidHom) = l := by
      rw [show (fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ (0 : ℤ))).toMonoidHom) = id
        from funext fun T => hmap T, List.map_id]
    refine ⟨?_, ?_⟩
    · rw [hmap C, hlist, hmap D]
      exact hl
    · rw [hlist, hmap D, hμ]
      rw [show μ.map (mPow c.k₀ c.m₀ (0 : ℤ)) = μ from by
        rw [show mPow c.k₀ c.m₀ (0 : ℤ) = id from funext fun _ => rfl,
          Multiset.map_id]]
  | succ k ih =>
    obtain ⟨hl1, hμ1⟩ := c.series_map_conj_tau_one hl hμ
    obtain ⟨hl2, hμ2⟩ := ih hl1 hμ1
    rw [zpow_add_one]
    refine ⟨?_, ?_⟩
    · have hD := map_conj_map_conj D (c.x₂ * c.x₁) ((c.x₂ * c.x₁) ^ (k : ℤ))
      rw [hD, map_conj_map_conj, map_list_conj_mul] at hl2
      exact hl2
    · have hD := map_conj_map_conj D (c.x₂ * c.x₁) ((c.x₂ * c.x₁) ^ (k : ℤ))
      rw [hD, map_list_conj_mul] at hμ2
      simpa [Multiset.map_map, mPow_add] using hμ2
  | pred k ih =>
    obtain ⟨hl1, hμ1⟩ := c.series_map_conj_tau_neg_one hl hμ
    obtain ⟨hl2, hμ2⟩ := ih hl1 hμ1
    rw [show -(k : ℤ) - 1 = -(k : ℤ) + (-1) by ring, zpow_add]
    refine ⟨?_, ?_⟩
    · have hD := map_conj_map_conj D ((c.x₂ * c.x₁) ^ (-1 : ℤ))
          ((c.x₂ * c.x₁) ^ (-(k : ℤ)))
      rw [hD, map_conj_map_conj, map_list_conj_mul] at hl2
      exact hl2
    · have hD := map_conj_map_conj D ((c.x₂ * c.x₁) ^ (-1 : ℤ))
          ((c.x₂ * c.x₁) ^ (-(k : ℤ)))
      rw [hD, map_list_conj_mul] at hμ2
      simpa [Multiset.map_map, mPow_add] using hμ2

private theorem contrib_map_mPow_even (s : ZMod (2 ^ n - 1)) (t : ℤ) (d : ℕ) :
    (Pattern.contrib c.k₀ c.m₀ s 0 d).map (mPow c.k₀ c.m₀ t) =
      Pattern.contrib c.k₀ c.m₀ s (2 * t) d := by
  have h0 : Even (0 : ℤ) := ⟨0, rfl⟩
  have h2 : Even (2 * t : ℤ) := ⟨t, by ring⟩
  have hdiv : (2 * t : ℤ) / 2 = t := Int.mul_ediv_cancel_left t (by norm_num)
  rcases eq_or_ne d 2 with rfl | hd2
  · simp [Pattern.contrib, h0, h2, hdiv, mPow_smul]
  rcases eq_or_ne d 1 with rfl | hd1
  · simp [Pattern.contrib, h0, h2, hdiv, hd2, mPow_smul]
  · simp [Pattern.contrib, h0, h2, hdiv, hd2, hd1]

private theorem contrib_map_mPow_odd (s : ZMod (2 ^ n - 1)) (t : ℤ) (d : ℕ) :
    (Pattern.contrib c.k₀ c.m₀ s 1 d).map (mPow c.k₀ c.m₀ t) =
      Pattern.contrib c.k₀ c.m₀ s (2 * t + 1) d := by
  have h1 : ¬ Even (1 : ℤ) := by decide
  have h2 : ¬ Even (2 * t + 1 : ℤ) := by
    intro h
    obtain ⟨k, hk⟩ := h
    omega
  have hdiv : (2 * t + 1 - 1 : ℤ) / 2 = t := by
    rw [show (2 * t + 1 - 1 : ℤ) = 2 * t by ring]
    exact Int.mul_ediv_cancel_left t (by norm_num)
  rcases eq_or_ne d 1 with rfl | hd1
  · simp [Pattern.contrib, h1, h2, hdiv, mPow_smul]
  · simp [Pattern.contrib, h1, h2, hdiv, hd1]

private theorem contrib_map_sigma1_mPow (t : ℤ) (d : ℕ) :
    (Pattern.contrib c.k₀ c.m₀ (-1) 0 d).map ((mPow c.k₀ c.m₀ t) ∘ sigma1 c.m₀) =
      Pattern.contrib c.k₀ c.m₀ 1 (2 * t) d := by
  have h0 : Even (0 : ℤ) := ⟨0, rfl⟩
  have h2 : Even (2 * t : ℤ) := ⟨t, by ring⟩
  have hdiv : (2 * t : ℤ) / 2 = t := Int.mul_ediv_cancel_left t (by norm_num)
  rcases eq_or_ne d 2 with rfl | hd2
  · simp [Pattern.contrib, h0, h2, hdiv, sigma1_smul, sigma1_neg, sigma1_psi,
      mPow_smul, mPow_neg_vec]
  rcases eq_or_ne d 1 with rfl | hd1
  · simp [Pattern.contrib, h0, h2, hdiv, hd2, sigma1_smul, sigma1_neg, sigma1_psi,
      mPow_smul, mPow_neg_vec]
  · simp [Pattern.contrib, h0, h2, hdiv, hd2, hd1]

private theorem contrib_map_sigma2_mPow (t : ℤ) (d : ℕ) :
    (Pattern.contrib c.k₀ c.m₀ 1 1 d).map ((mPow c.k₀ c.m₀ t) ∘ sigma2 c.k₀) =
      Pattern.contrib c.k₀ c.m₀ (-1) (2 * t + 1) d := by
  have h1 : ¬ Even (1 : ℤ) := by decide
  have h2 : ¬ Even (2 * t + 1 : ℤ) := by
    intro h
    obtain ⟨k, hk⟩ := h
    omega
  have hdiv : (2 * t + 1 - 1 : ℤ) / 2 = t := by
    rw [show (2 * t + 1 - 1 : ℤ) = 2 * t by ring]
    exact Int.mul_ediv_cancel_left t (by norm_num)
  rcases eq_or_ne d 1 with rfl | hd1
  · simp [Pattern.contrib, h1, h2, hdiv, sigma2_smul, sigma2_neg, sigma2_chi, mPow_smul,
      mPow_neg_vec]
  · simp [Pattern.contrib, h1, h2, hdiv, hd1]

theorem exists_ySeries_right {i j : ℤ} (hij : i ≤ j) :
    ∃ l, IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ i (j + 1)) l
        (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) =
        clsSets (Pattern.contrib c.k₀ c.m₀ 1 (j + 1)
          (c.pattern.dropAt (j + 1) (j + 1 - i).toNat)) := by
  have hmcast : (((j + 1 - i).toNat : ℕ) : ℤ) = j + 1 - i :=
    Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ (j + 1 - i).toNat := by omega
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' (j + 1)
  ·
    obtain ⟨l, hl, hfac⟩ := c.exists_ySeries_baseS (m := (j + 1 - i).toNat) hm1
    obtain ⟨hl1, hfac1⟩ := c.series_map_conj_x₁ hl hfac
    obtain ⟨hl2, hfac2⟩ := c.series_map_conj_tau t hl1 hfac1
    have hC : ((win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 ((j + 1 - i).toNat : ℤ)).map
          (MulAut.conj c.x₁).toMonoidHom).map
          (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ i (j + 1) := by
      rw [c.track.map_win_x₁ c.le_normalizer₁ c.le_normalizer₂, map_win_tau_pow]
      congr 1 <;> omega
    have hD : ((win c.Q₁ c.Q₂ c.x₁ c.x₂ 1 ((j + 1 - i).toNat : ℤ)).map
          (MulAut.conj c.x₁).toMonoidHom).map
          (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ i j := by
      rw [c.track.map_win_x₁ c.le_normalizer₁ c.le_normalizer₂, map_win_tau_pow]
      congr 1 <;> omega
    refine ⟨(l.map fun T => T.map (MulAut.conj c.x₁).toMonoidHom).map
      (fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom), ?_, ?_⟩
    · rw [hC, hD] at hl2
      exact hl2
    · rw [hD] at hfac2
      rw [Multiset.map_map, contrib_map_sigma1_mPow, ← ht] at hfac2
      have hdrop : c.pattern.dropAt (j + 1) (j + 1 - i).toNat =
          c.pattern.dS (j + 1 - i).toNat := by
        rw [Pattern.dropAt, if_pos (show Even (j + 1 : ℤ) from ht ▸ ⟨t, by ring⟩)]
      rw [hdrop]
      exact hfac2
  ·
    obtain ⟨l, hl, hfac⟩ := c.exists_ySeries_baseL (m := (j + 1 - i).toNat) hm1
    obtain ⟨hl1, hfac1⟩ := c.series_map_conj_tau t hl hfac
    have hC : (win c.Q₁ c.Q₂ c.x₁ c.x₂ (1 - ((j + 1 - i).toNat : ℤ)) 1).map
          (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ i (j + 1) := by
      rw [map_win_tau_pow]
      congr 1 <;> omega
    have hD : (win c.Q₁ c.Q₂ c.x₁ c.x₂ (1 - ((j + 1 - i).toNat : ℤ)) 0).map
          (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ i j := by
      rw [map_win_tau_pow]
      congr 1 <;> omega
    refine ⟨l.map fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom, ?_, ?_⟩
    · rw [hC, hD] at hl1
      exact hl1
    · rw [hD] at hfac1
      rw [contrib_map_mPow_odd, ← ht] at hfac1
      have hdrop : c.pattern.dropAt (j + 1) (j + 1 - i).toNat =
          c.pattern.dL (j + 1 - i).toNat := by
        rw [Pattern.dropAt, if_neg (by
          rw [ht]
          intro h
          obtain ⟨k, hk⟩ := h
          omega)]
      rw [hdrop]
      exact hfac1

theorem exists_ySeries_left {i j : ℤ} (hij : i ≤ j) :
    ∃ l, IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ (i - 1) j) l
        (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) =
        clsSets (Pattern.contrib c.k₀ c.m₀ (-1) (i - 1)
          (c.pattern.dropAt (i - 1) (j - (i - 1)).toNat)) := by
  have hmcast : (((j - (i - 1)).toNat : ℕ) : ℤ) = j - (i - 1) :=
    Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ (j - (i - 1)).toNat := by omega
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' (i - 1)
  ·
    obtain ⟨l, hl, hfac⟩ := c.exists_ySeries_baseS (m := (j - (i - 1)).toNat) hm1
    obtain ⟨hl1, hfac1⟩ := c.series_map_conj_tau t hl hfac
    have hC : (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 ((j - (i - 1)).toNat : ℤ)).map
          (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ (i - 1) j := by
      rw [map_win_tau_pow]
      congr 1 <;> omega
    have hD : (win c.Q₁ c.Q₂ c.x₁ c.x₂ 1 ((j - (i - 1)).toNat : ℤ)).map
          (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ i j := by
      rw [map_win_tau_pow]
      congr 1 <;> omega
    refine ⟨l.map fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom, ?_, ?_⟩
    · rw [hC, hD] at hl1
      exact hl1
    · rw [hD] at hfac1
      rw [contrib_map_mPow_even, ← ht] at hfac1
      have hdrop : c.pattern.dropAt (i - 1) (j - (i - 1)).toNat =
          c.pattern.dS (j - (i - 1)).toNat := by
        rw [Pattern.dropAt, if_pos (show Even (i - 1 : ℤ) from ht ▸ ⟨t, by ring⟩)]
      rw [hdrop]
      exact hfac1
  ·
    obtain ⟨l, hl, hfac⟩ := c.exists_ySeries_baseL (m := (j - (i - 1)).toNat) hm1
    obtain ⟨hl1, hfac1⟩ := c.series_map_conj_x₂ hl hfac
    obtain ⟨hl2, hfac2⟩ := c.series_map_conj_tau t hl1 hfac1
    have hC : ((win c.Q₁ c.Q₂ c.x₁ c.x₂ (1 - ((j - (i - 1)).toNat : ℤ)) 1).map
          (MulAut.conj c.x₂).toMonoidHom).map
          (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ (i - 1) j := by
      rw [c.track.map_win_x₂ c.le_normalizer₁ c.le_normalizer₂, map_win_tau_pow]
      congr 1 <;> omega
    have hD : ((win c.Q₁ c.Q₂ c.x₁ c.x₂ (1 - ((j - (i - 1)).toNat : ℤ)) 0).map
          (MulAut.conj c.x₂).toMonoidHom).map
          (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ i j := by
      rw [c.track.map_win_x₂ c.le_normalizer₁ c.le_normalizer₂, map_win_tau_pow]
      congr 1 <;> omega
    refine ⟨(l.map fun T => T.map (MulAut.conj c.x₂).toMonoidHom).map
      (fun T => T.map (MulAut.conj ((c.x₂ * c.x₁) ^ t)).toMonoidHom), ?_, ?_⟩
    · rw [hC, hD] at hl2
      exact hl2
    · rw [hD] at hfac2
      rw [Multiset.map_map, contrib_map_sigma2_mPow, ← ht] at hfac2
      have hdrop : c.pattern.dropAt (i - 1) (j - (i - 1)).toNat =
          c.pattern.dL (j - (i - 1)).toNat := by
        rw [Pattern.dropAt, if_neg (by
          rw [ht]
          intro h
          obtain ⟨k, hk⟩ := h
          omega)]
      rw [hdrop]
      exact hfac2

private theorem chainR_succ (i : ℤ) {j : ℤ} (hj : j ≤ i + (c.pattern.J : ℤ)) :
    c.pattern.chainR c.k₀ c.m₀ i (j - 1) =
      Pattern.contrib c.k₀ c.m₀ 1 j (c.pattern.dropAt j (j - i).toNat) +
        c.pattern.chainR c.k₀ c.m₀ i j := by
  unfold Pattern.chainR
  have hIoc : Finset.Ioc (j - 1) (i + (c.pattern.J : ℤ)) =
      insert j (Finset.Ioc j (i + (c.pattern.J : ℤ))) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hIoc, Finset.sum_insert (by simp [Finset.mem_Ioc])]

private theorem chainL_succ {j : ℤ} (i : ℤ) (hi : j - (c.pattern.J : ℤ) ≤ i) :
    c.pattern.chainL c.k₀ c.m₀ (i + 1) j =
      Pattern.contrib c.k₀ c.m₀ (-1) i (c.pattern.dropAt i (j - i).toNat) +
        c.pattern.chainL c.k₀ c.m₀ i j := by
  unfold Pattern.chainL
  have hIco : Finset.Ico (j - (c.pattern.J : ℤ)) (i + 1) =
      insert i (Finset.Ico (j - (c.pattern.J : ℤ)) i) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [hIco, Finset.sum_insert (by simp [Finset.mem_Ico])]

private theorem exists_ySeries_chainR_aux (i : ℤ) :
    ∀ k : ℕ, k ≤ c.pattern.J →
      ∃ l, IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) l
          (win c.Q₁ c.Q₂ c.x₁ c.x₂ i (i + ((c.pattern.J - k : ℕ) : ℤ))) ∧
        facMultiset (chiLab c.ζ c.d₁ c.d₂) l
            (win c.Q₁ c.Q₂ c.x₁ c.x₂ i (i + ((c.pattern.J - k : ℕ) : ℤ))) =
          clsSets (c.pattern.chainR c.k₀ c.m₀ i (i + ((c.pattern.J - k : ℕ) : ℤ))) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hwin : win c.Q₁ c.Q₂ c.x₁ c.x₂ i (i + ((c.pattern.J - 0 : ℕ) : ℤ)) =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J := by
      simpa using c.win_eq_of_le (a := i) (b := i + (c.pattern.J : ℤ)) (by omega)
    refine ⟨[], ?_, ?_⟩
    · rw [hwin]
      rfl
    · rw [hwin]
      simp [Pattern.chainR, facMultiset, clsSets]
  | succ k ih =>
    intro hk
    have hkJ : k ≤ c.pattern.J := by omega
    obtain ⟨l, hl, hfac⟩ := ih hkJ
    have hstep : i + ((c.pattern.J - (k + 1) : ℕ) : ℤ) =
        i + ((c.pattern.J - k : ℕ) : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : k + 1 ≤ c.pattern.J), Nat.cast_sub hkJ]
      push_cast
      ring
    have hip : i ≤ i + ((c.pattern.J - k : ℕ) : ℤ) - 1 := by
      have : 1 ≤ c.pattern.J - k := by omega
      omega
    obtain ⟨l', hl', hfac'⟩ := c.exists_ySeries_right (i := i)
      (j := i + ((c.pattern.J - k : ℕ) : ℤ) - 1) hip
    have hfac'' : facMultiset (chiLab c.ζ c.d₁ c.d₂) l'
        (win c.Q₁ c.Q₂ c.x₁ c.x₂ i (i + ((c.pattern.J - k : ℕ) : ℤ) - 1)) =
        clsSets (Pattern.contrib c.k₀ c.m₀ 1 (i + ((c.pattern.J - k : ℕ) : ℤ))
          (c.pattern.dropAt (i + ((c.pattern.J - k : ℕ) : ℤ))
            (i + ((c.pattern.J - k : ℕ) : ℤ) - i).toNat)) := by
      simpa using hfac'
    have hchain := c.chainR_succ i (j := i + ((c.pattern.J - k : ℕ) : ℤ)) (by omega)
    have hl'' : IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ i (i + ((c.pattern.J - k : ℕ) : ℤ)))
        l' (win c.Q₁ c.Q₂ c.x₁ c.x₂ i (i + ((c.pattern.J - k : ℕ) : ℤ) - 1)) := by
      simpa using hl'
    rw [hstep]
    refine ⟨l' ++ l, hl''.append hl, ?_⟩
    rw [facMultiset_append (chiLab c.ζ c.d₁ c.d₂) hl'', hfac'', hfac, hchain]
    simp [clsSets]

private theorem exists_ySeries_chainL_aux (j : ℤ) :
    ∀ k : ℕ, k ≤ c.pattern.J →
      ∃ l, IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) l
          (win c.Q₁ c.Q₂ c.x₁ c.x₂ (j - (c.pattern.J : ℤ) + k) j) ∧
        facMultiset (chiLab c.ζ c.d₁ c.d₂) l
            (win c.Q₁ c.Q₂ c.x₁ c.x₂ (j - (c.pattern.J : ℤ) + k) j) =
          clsSets (c.pattern.chainL c.k₀ c.m₀ (j - (c.pattern.J : ℤ) + k) j) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hwin : win c.Q₁ c.Q₂ c.x₁ c.x₂ (j - (c.pattern.J : ℤ) + ((0 : ℕ) : ℤ)) j =
        win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J := by
      simpa using c.win_eq_of_le (a := j - (c.pattern.J : ℤ)) (b := j) (by omega)
    refine ⟨[], ?_, ?_⟩
    · rw [hwin]
      rfl
    · rw [hwin]
      simp [Pattern.chainL, facMultiset, clsSets]
  | succ k ih =>
    intro hk
    have hkJ : k ≤ c.pattern.J := by omega
    obtain ⟨l, hl, hfac⟩ := ih hkJ
    have hstep : j - (c.pattern.J : ℤ) + ((k + 1 : ℕ) : ℤ) =
        j - (c.pattern.J : ℤ) + (k : ℤ) + 1 := by
      push_cast
      ring
    have hip : j - (c.pattern.J : ℤ) + (k : ℤ) + 1 ≤ j := by omega
    obtain ⟨l', hl', hfac'⟩ := c.exists_ySeries_left
      (i := j - (c.pattern.J : ℤ) + (k : ℤ) + 1) (j := j) hip
    have hfac'' : facMultiset (chiLab c.ζ c.d₁ c.d₂) l'
        (win c.Q₁ c.Q₂ c.x₁ c.x₂ (j - (c.pattern.J : ℤ) + (k : ℤ) + 1) j) =
        clsSets (Pattern.contrib c.k₀ c.m₀ (-1) (j - (c.pattern.J : ℤ) + (k : ℤ))
          (c.pattern.dropAt (j - (c.pattern.J : ℤ) + (k : ℤ))
            (j - (j - (c.pattern.J : ℤ) + (k : ℤ))).toNat)) := by
      simpa using hfac'
    have hchain := c.chainL_succ (j := j) (j - (c.pattern.J : ℤ) + (k : ℤ)) (by omega)
    have hl'' : IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ (j - (c.pattern.J : ℤ) + (k : ℤ)) j)
        l' (win c.Q₁ c.Q₂ c.x₁ c.x₂ (j - (c.pattern.J : ℤ) + (k : ℤ) + 1) j) := by
      simpa using hl'
    rw [hstep]
    refine ⟨l' ++ l, hl''.append hl, ?_⟩
    rw [facMultiset_append (chiLab c.ζ c.d₁ c.d₂) hl'', hfac'', hfac, hchain]
    simp [clsSets]

theorem exists_ySeries_chainR {i j : ℤ} (hij : i ≤ j) (hj : j ≤ i + c.pattern.J) :
    ∃ l, IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) l
        (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) =
        clsSets (c.pattern.chainR c.k₀ c.m₀ i j) := by
  have hnonneg : 0 ≤ i + (c.pattern.J : ℤ) - j := by omega
  have hk : (i + (c.pattern.J : ℤ) - j).toNat ≤ c.pattern.J := by
    have hcast : (((i + (c.pattern.J : ℤ) - j).toNat : ℕ) : ℤ) = i + (c.pattern.J : ℤ) - j :=
      Int.toNat_of_nonneg hnonneg
    omega
  obtain ⟨l, hl, hfac⟩ := c.exists_ySeries_chainR_aux i ((i + (c.pattern.J : ℤ) - j).toNat) hk
  have hji : i + ((c.pattern.J - (i + (c.pattern.J : ℤ) - j).toNat : ℕ) : ℤ) = j := by
    rw [Nat.cast_sub hk]
    have hcast : (((i + (c.pattern.J : ℤ) - j).toNat : ℕ) : ℤ) = i + (c.pattern.J : ℤ) - j :=
      Int.toNat_of_nonneg hnonneg
    omega
  rw [hji] at hl hfac
  exact ⟨l, hl, hfac⟩

theorem exists_ySeries_chainL {i j : ℤ} (hij : i ≤ j) (hj : j ≤ i + c.pattern.J) :
    ∃ l, IsYSeries c.H (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) l
        (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) =
        clsSets (c.pattern.chainL c.k₀ c.m₀ i j) := by
  have hnonneg : 0 ≤ i - (j - (c.pattern.J : ℤ)) := by omega
  have hk : (i - (j - (c.pattern.J : ℤ))).toNat ≤ c.pattern.J := by
    have hcast : (((i - (j - (c.pattern.J : ℤ))).toNat : ℕ) : ℤ) =
        i - (j - (c.pattern.J : ℤ)) := Int.toNat_of_nonneg hnonneg
    omega
  obtain ⟨l, hl, hfac⟩ := c.exists_ySeries_chainL_aux j ((i - (j - (c.pattern.J : ℤ))).toNat) hk
  have hji : j - (c.pattern.J : ℤ) + (((i - (j - (c.pattern.J : ℤ))).toNat : ℕ) : ℤ) = i := by
    have hcast : (((i - (j - (c.pattern.J : ℤ))).toNat : ℕ) : ℤ) =
        i - (j - (c.pattern.J : ℤ)) := Int.toNat_of_nonneg hnonneg
    omega
  rw [hji] at hl hfac
  exact ⟨l, hl, hfac⟩

theorem exists_ySeries_Q₁ {μT : Multiset (Coord n)}
    (hμT : ∃ l, IsYSeries c.H ⊥ l (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) =
        clsSets μT) :
    ∃ l, IsYSeries c.H ⊥ l c.Q₁ ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) l c.Q₁ =
        clsSets (c.pattern.chainR c.k₀ c.m₀ 0 0 + μT) := by
  obtain ⟨lT, hlT, hfacT⟩ := hμT
  obtain ⟨lR, hlR, hfacR⟩ := c.exists_ySeries_chainR (i := 0) (j := 0) le_rfl
    (by omega : (0 : ℤ) ≤ 0 + (c.pattern.J : ℤ))
  have hQ : win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 0 = c.Q₁ := win_zero_zero c.Q₁ c.Q₂ c.x₁ c.x₂
  rw [hQ] at hlR hfacR
  refine ⟨lR ++ lT, hlR.append hlT, ?_⟩
  rw [facMultiset_append (chiLab c.ζ c.d₁ c.d₂) hlR, hfacR, hfacT]
  simp [clsSets, Multiset.map_add]

end Conf

end CFSG.Quasithin.Stroth.G5

end
