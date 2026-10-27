module

public import CFSG.Quasithin.EmptyFaithful.E22PD1A
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.E22L2

open DihedralGroup
open scoped commutatorElement

theorem e22pd1_rot_mem_normalizer_iff {k : ℕ} {j i : ZMod (2 ^ (k + 2))} :
    r i ∈ Subgroup.normalizer (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2)))) ↔
      2 * i = 0 ∨ 2 * i = 2 ^ (k + 1) := by
  have hh := e22pd1_h_add_h k
  constructor
  · intro hx
    have hj : sr j ∈ e22pd1_kf k j := e22pd1_mem_kf.mpr (Or.inr (Or.inr (Or.inl rfl)))
    have h1 := (Subgroup.mem_normalizer_iff.mp hx (sr j)).mp hj
    rw [inv_r, r_mul_sr, sr_mul_r, e22pd1_mem_kf] at h1
    rcases h1 with h | h | h | h
    · exact absurd h (e22pd1_sr_ne_one _)
    · exact absurd h (e22pd1_sr_ne_r _ _)
    · left
      have := DihedralGroup.sr.inj h
      linear_combination -this
    · right
      have := DihedralGroup.sr.inj h
      linear_combination (-1 : ZMod (2 ^ (k + 2))) * this - hh
  · intro h
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [SetLike.mem_coe, e22pd1_mem_kf] at hn ⊢
    rcases hn with rfl | rfl | rfl | rfl
    · left; simp
    · right; left
      rw [inv_r, r_mul_r, r_mul_r]; congr 1; ring
    · rcases h with h | h
      · right; right; left
        rw [inv_r, r_mul_sr, sr_mul_r]; congr 1; linear_combination -h
      · right; right; right
        rw [inv_r, r_mul_sr, sr_mul_r]; congr 1; linear_combination -h - hh
    · rcases h with h | h
      · right; right; right
        rw [inv_r, r_mul_sr, sr_mul_r]; congr 1; linear_combination -h
      · right; right; left
        rw [inv_r, r_mul_sr, sr_mul_r]; congr 1; linear_combination -h

theorem e22pd1_ref_mem_normalizer_iff {k : ℕ} {j i : ZMod (2 ^ (k + 2))} :
    sr i ∈ Subgroup.normalizer (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2)))) ↔
      2 * (i - j) = 0 ∨ 2 * (i - j) = 2 ^ (k + 1) := by
  have hh := e22pd1_h_add_h k
  constructor
  · intro hx
    have hj : sr j ∈ e22pd1_kf k j := e22pd1_mem_kf.mpr (Or.inr (Or.inr (Or.inl rfl)))
    have h1 := (Subgroup.mem_normalizer_iff.mp hx (sr j)).mp hj
    rw [inv_sr, sr_mul_sr, r_mul_sr, e22pd1_mem_kf] at h1
    rcases h1 with h | h | h | h
    · exact absurd h (e22pd1_sr_ne_one _)
    · exact absurd h (e22pd1_sr_ne_r _ _)
    · left
      have := DihedralGroup.sr.inj h
      linear_combination this
    · right
      have := DihedralGroup.sr.inj h
      linear_combination this
  · intro h
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [SetLike.mem_coe, e22pd1_mem_kf] at hn ⊢
    rcases hn with rfl | rfl | rfl | rfl
    · left; simp
    · right; left
      rw [inv_sr, sr_mul_r, sr_mul_sr]; congr 1; linear_combination -hh
    · rcases h with h | h
      · right; right; left
        rw [inv_sr, sr_mul_sr, r_mul_sr]; congr 1; linear_combination h
      · right; right; right
        rw [inv_sr, sr_mul_sr, r_mul_sr]; congr 1; linear_combination h
    · rcases h with h | h
      · right; right; right
        rw [inv_sr, sr_mul_sr, r_mul_sr]; congr 1; linear_combination h - hh
      · right; right; left
        rw [inv_sr, sr_mul_sr, r_mul_sr]; congr 1; linear_combination h

theorem e22pd1_r_mem_kf {k : ℕ} {j θ : ZMod (2 ^ (k + 2))}
    (h : θ = 0 ∨ θ = 2 ^ (k + 1)) : r θ ∈ e22pd1_kf k j := by
  rw [e22pd1_mem_kf]
  rcases h with rfl | rfl
  · left; simp
  · right; left; rfl

theorem e22pd1_comm_mem_kf {k : ℕ} {j : ZMod (2 ^ (k + 2))} {x y : DihedralGroup (2 ^ (k + 2))}
    (hx : x ∈ Subgroup.normalizer (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2)))))
    (hy : y ∈ Subgroup.normalizer (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2))))) :
    ⁅x, y⁆ ∈ e22pd1_kf k j := by
  have hh := e22pd1_h_add_h k
  rw [commutatorElement_def]
  rcases x with a | a <;> rcases y with b | b
  · simp only [inv_r, r_mul_r]
    refine e22pd1_r_mem_kf (Or.inl ?_)
    ring
  · have ha := e22pd1_rot_mem_normalizer_iff.mp hx
    rw [inv_r, inv_sr, r_mul_sr, sr_mul_r, sr_mul_sr]
    refine e22pd1_r_mem_kf ?_
    rcases ha with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · have hb := e22pd1_rot_mem_normalizer_iff.mp hy
    rw [inv_r, inv_sr, sr_mul_r, sr_mul_sr, r_mul_r]
    refine e22pd1_r_mem_kf ?_
    rcases hb with h | h
    · exact Or.inl (by linear_combination -h)
    · exact Or.inr (by linear_combination -h - hh)
  · have ha := e22pd1_ref_mem_normalizer_iff.mp hx
    have hb := e22pd1_ref_mem_normalizer_iff.mp hy
    rw [inv_sr, inv_sr, sr_mul_sr, r_mul_sr, sr_mul_sr]
    refine e22pd1_r_mem_kf ?_
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (by linear_combination hb - ha)
    · exact Or.inr (by linear_combination hb - ha)
    · exact Or.inr (by linear_combination hb - ha - hh)
    · exact Or.inl (by linear_combination hb - ha)

theorem e22pd1_normalizer_cases {k : ℕ} {j : ZMod (2 ^ (k + 2))}
    {x : DihedralGroup (2 ^ (k + 2))}
    (hx : x ∈ Subgroup.normalizer (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2))))) :
    x = r 0 ∨ x = r (2 ^ k) ∨ x = r (2 * 2 ^ k) ∨ x = r (3 * 2 ^ k) ∨
      x = sr j ∨ x = sr (j + 2 ^ k) ∨ x = sr (j + 2 * 2 ^ k) ∨ x = sr (j + 3 * 2 ^ k) := by
  have hh := e22pd1_h_add_h k
  rcases x with i | i
  · have h4 : 4 * i = 0 := by
      rcases e22pd1_rot_mem_normalizer_iff.mp hx with h | h
      · linear_combination 2 * h
      · linear_combination 2 * h + hh
    rcases e22pd1_four_mul_eq_zero h4 with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · have h4 : 4 * (i - j) = 0 := by
      rcases e22pd1_ref_mem_normalizer_iff.mp hx with h | h
      · linear_combination 2 * h
      · linear_combination 2 * h + hh
    rcases e22pd1_four_mul_eq_zero h4 with h | h | h | h
    · obtain rfl : i = j := by linear_combination h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · obtain rfl : i = j + 2 ^ k := by linear_combination h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · obtain rfl : i = j + 2 * 2 ^ k := by linear_combination h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · obtain rfl : i = j + 3 * 2 ^ k := by linear_combination h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem e22pd1_kf_add_h (k : ℕ) (j : ZMod (2 ^ (k + 2))) :
    e22pd1_kf k (j + 2 ^ (k + 1)) = e22pd1_kf k j := by
  have hh := e22pd1_h_add_h k
  ext x
  rw [e22pd1_mem_kf, e22pd1_mem_kf]
  have : j + 2 ^ (k + 1) + 2 ^ (k + 1) = j := by linear_combination hh
  rw [this]
  tauto

theorem e22pd1_partner_le_normalizer (k : ℕ) (j : ZMod (2 ^ (k + 2))) :
    e22pd1_kf k (j + 2 ^ k) ≤
      Subgroup.normalizer (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2)))) := by
  have hh := e22pd1_h_add_h k
  intro x hx
  rw [e22pd1_mem_kf] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact e22pd1_rot_mem_normalizer_iff.mpr (Or.inl (by linear_combination hh))
  · exact e22pd1_ref_mem_normalizer_iff.mpr (Or.inr (by ring))
  · exact e22pd1_ref_mem_normalizer_iff.mpr (Or.inr (by linear_combination hh))

theorem e22pd1_card_normalizer_kf (k : ℕ) (j : ZMod (2 ^ (k + 2))) :
    Nat.card ↥(Subgroup.normalizer
      (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2))))) = 8 := by
  classical
  set N := Subgroup.normalizer (e22pd1_kf k j : Set (DihedralGroup (2 ^ (k + 2)))) with hN
  have hle : e22pd1_kf k j ≤ N := Subgroup.le_normalizer
  have hdvd : 4 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hle
    rwa [e22pd1_kf_card] at this
  have hup : Nat.card N ≤ 8 := by
    let L : List (DihedralGroup (2 ^ (k + 2))) :=
      [r 0, r (2 ^ k), r (2 * 2 ^ k), r (3 * 2 ^ k), sr j, sr (j + 2 ^ k), sr (j + 2 * 2 ^ k),
        sr (j + 3 * 2 ^ k)]
    have hsub : (N : Set (DihedralGroup (2 ^ (k + 2)))) ⊆ (L.toFinset : Set _) := by
      intro x hx
      have := e22pd1_normalizer_cases hx
      simp only [Finset.mem_coe, List.mem_toFinset, L, List.mem_cons, List.not_mem_nil, or_false]
      exact this
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : Nat.card N = (N : Set (DihedralGroup (2 ^ (k + 2)))).ncard :=
      Nat.card_coe_set_eq _
    have h3 : L.toFinset.card ≤ L.length := List.toFinset_card_le L
    have h4 : L.length = 8 := rfl
    omega
  have hq0 : (2 ^ k : ZMod (2 ^ (k + 2))) ≠ 0 := e22pd1_two_pow_ne_zero (by omega)
  have hrN : r (2 ^ k : ZMod (2 ^ (k + 2))) ∈ N :=
    e22pd1_rot_mem_normalizer_iff.mpr (Or.inr (by ring))
  have hrK : r (2 ^ k : ZMod (2 ^ (k + 2))) ∉ e22pd1_kf k j := by
    intro h
    rw [e22pd1_mem_kf] at h
    rcases h with h | h | h | h
    · rw [← r_zero] at h
      exact hq0 (DihedralGroup.r.inj h)
    · have := DihedralGroup.r.inj h
      exact hq0 (by linear_combination -this)
    · exact e22pd1_sr_ne_r _ _ h.symm
    · exact e22pd1_sr_ne_r _ _ h.symm
  have hne4 : Nat.card N ≠ 4 := by
    intro h4
    have := Subgroup.eq_of_le_of_card_ge hle (by rw [e22pd1_kf_card, h4])
    exact hrK (this ▸ hrN)
  have hpos : 0 < Nat.card N := Nat.card_pos
  omega

theorem e22pd1_partner_D {k : ℕ} {W : Subgroup (DihedralGroup (2 ^ (k + 2)))}
    (hW : IsKleinFour ↥W) :
    ∃ W' : Subgroup (DihedralGroup (2 ^ (k + 2))), IsKleinFour ↥W' ∧ W' ≠ W ∧
      W' ≤ Subgroup.normalizer (W : Set (DihedralGroup (2 ^ (k + 2)))) ∧
      W ≤ Subgroup.normalizer (W' : Set (DihedralGroup (2 ^ (k + 2)))) ∧
      Nat.card ↥(Subgroup.normalizer (W' : Set (DihedralGroup (2 ^ (k + 2))))) = 8 ∧
      Subgroup.centralizer (W : Set (DihedralGroup (2 ^ (k + 2)))) ≤
        Subgroup.normalizer (W' : Set (DihedralGroup (2 ^ (k + 2)))) ∧
      ⁅Subgroup.normalizer (W' : Set (DihedralGroup (2 ^ (k + 2)))), W⁆ ≤ W' := by
  obtain ⟨j, rfl⟩ := e22pd1_exists_kf_eq_of_isKleinFour hW
  have hq0 : (2 ^ k : ZMod (2 ^ (k + 2))) ≠ 0 := e22pd1_two_pow_ne_zero (by omega)
  have hWN' : e22pd1_kf k j ≤
      Subgroup.normalizer (e22pd1_kf k (j + 2 ^ k) : Set (DihedralGroup (2 ^ (k + 2)))) := by
    have h1 := e22pd1_partner_le_normalizer k (j + 2 ^ k)
    have heq : e22pd1_kf k (j + 2 ^ k + 2 ^ k) = e22pd1_kf k j := by
      rw [show j + 2 ^ k + 2 ^ k = j + 2 ^ (k + 1) by ring]
      exact e22pd1_kf_add_h k j
    rwa [heq] at h1
  refine ⟨e22pd1_kf k (j + 2 ^ k), e22pd1_isKleinFour_kf k _, ?_,
    e22pd1_partner_le_normalizer k j, hWN', e22pd1_card_normalizer_kf k _, ?_, ?_⟩
  · intro h
    have hmem : sr (j + 2 ^ k) ∈ e22pd1_kf k (j + 2 ^ k) :=
      e22pd1_mem_kf.mpr (Or.inr (Or.inr (Or.inl rfl)))
    rw [h, e22pd1_mem_kf] at hmem
    rcases hmem with h1 | h1 | h1 | h1
    · exact e22pd1_sr_ne_one _ h1
    · exact e22pd1_sr_ne_r _ _ h1
    · have := DihedralGroup.sr.inj h1
      exact hq0 (by linear_combination this)
    · have := DihedralGroup.sr.inj h1
      exact hq0 (by linear_combination -this)
  · refine le_trans ?_ hWN'
    exact CFSG.GorensteinWalter.centralizer_kleinFour_le_of_dihedral_mulEquiv
      (by omega) (MulEquiv.refl _) _ (e22pd1_isKleinFour_kf k j)
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact e22pd1_comm_mem_kf hx (hWN' hy)

theorem e22pd1_normalizer_le_D {k : ℕ} (hk : 1 ≤ k) {X : Subgroup (DihedralGroup (2 ^ (k + 2)))}
    (hsq : ∀ x : DihedralGroup (2 ^ (k + 2)), x * x ∈ X)
    {W W' : Subgroup (DihedralGroup (2 ^ (k + 2)))} (hW : IsKleinFour ↥W)
    (hW' : IsKleinFour ↥W') (hWX : W ≤ X)
    (hW'N : W' ≤ Subgroup.normalizer (W : Set (DihedralGroup (2 ^ (k + 2))))) :
    Subgroup.normalizer (W' : Set (DihedralGroup (2 ^ (k + 2)))) ≤ X := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, rfl⟩ := e22pd1_exists_kf_eq_of_isKleinFour hW
  obtain ⟨j', rfl⟩ := e22pd1_exists_kf_eq_of_isKleinFour hW'
  have hr2 : r 2 ∈ X := by
    have := hsq (r 1)
    rwa [r_mul_r, one_add_one_eq_two] at this
  have hmul : ∀ c : ℕ, r ((c : ZMod (2 ^ (k' + 1 + 2))) * 2 ^ (k' + 1)) ∈ X := by
    intro c
    have h := X.pow_mem hr2 (c * 2 ^ k')
    rw [r_pow] at h
    convert h using 2
    push_cast
    ring
  have hsj : sr j ∈ X := hWX (e22pd1_mem_kf.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hj' : sr j' ∈ Subgroup.normalizer
      (e22pd1_kf (k' + 1) j : Set (DihedralGroup (2 ^ (k' + 1 + 2)))) :=
    hW'N (e22pd1_mem_kf.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hh := e22pd1_h_add_h (k' + 1)
  have h4 : 4 * (j' - j) = 0 := by
    rcases e22pd1_ref_mem_normalizer_iff.mp hj' with h | h
    · linear_combination 2 * h
    · linear_combination 2 * h + hh
  have hc : ∃ c : ℕ, j' = j + (c : ZMod (2 ^ (k' + 1 + 2))) * 2 ^ (k' + 1) := by
    rcases e22pd1_four_mul_eq_zero h4 with h | h | h | h
    · exact ⟨0, by simp; linear_combination h⟩
    · exact ⟨1, by simp; linear_combination h⟩
    · exact ⟨2, by simp; linear_combination h⟩
    · exact ⟨3, by simp; linear_combination h⟩
  obtain ⟨c, hc⟩ := hc
  have hsr : ∀ a : ℕ, sr (j' + (a : ZMod (2 ^ (k' + 1 + 2))) * 2 ^ (k' + 1)) ∈ X := by
    intro a
    have h := X.mul_mem hsj (hmul (c + a))
    rw [sr_mul_r] at h
    convert h using 2
    rw [hc]
    push_cast
    ring
  intro x hx
  rcases e22pd1_normalizer_cases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simpa using hmul 1
  · simpa using hmul 2
  · simpa using hmul 3
  · simpa using hsr 0
  · simpa using hsr 1
  · simpa using hsr 2
  · simpa using hsr 3

end CFSG.Quasithin.E22L2
