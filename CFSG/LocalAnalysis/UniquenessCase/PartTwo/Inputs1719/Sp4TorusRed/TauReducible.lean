module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.TauTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.PRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4Plane
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4Weyl
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93TorusLift
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93AC1
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TMain
public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F3D

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauPair)
open scoped Matrix

variable {K : Type} [Field K]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem isTorusReducible_of_pattern {H : Subgroup (StatedSp 2 K)} {s : Fin 2 ⊕ Fin 2 → Prop}
    (hs : ∀ h ∈ H, ∀ k j : Fin 2 ⊕ Fin 2, s j → ¬ s k → (spMat h) k j = 0)
    (hex : ∃ j, s j) (hne : ∃ k, ¬ s k) : IsTorusReducible H := by
  classical
  let W : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    { carrier := {w | ∀ k, ¬ s k → w k = 0}
      add_mem' := by
        intro a b ha hb k hk
        simp [ha k hk, hb k hk]
      zero_mem' := by
        intro k hk
        simp
      smul_mem' := by
        intro c a ha k hk
        simp [ha k hk] }
  have hW0 : W ≠ ⊥ := by
    obtain ⟨j, hj⟩ := hex
    have hmem : Pi.single j (1 : K) ∈ W := by
      intro k hk
      by_cases hjk : j = k
      · subst hjk
        exact absurd hj hk
      · exact Pi.single_eq_of_ne' (M := fun _ => K) hjk 1
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    have h := congrFun hmem j
    simp only [Pi.single_eq_same, Pi.zero_apply] at h
    exact one_ne_zero h
  have hW1 : W ≠ ⊤ := by
    obtain ⟨k, hk⟩ := hne
    intro htop
    have hmem : Pi.single k (1 : K) ∈ W := by
      rw [htop]
      exact Submodule.mem_top
    have h := hmem k hk
    simp only [Pi.single_eq_same] at h
    exact one_ne_zero h
  refine ⟨W, hW0, hW1, ?_, ?_⟩
  · rintro d hd w hw k hk
    obtain ⟨t, rfl⟩ := hd
    rw [coe_torusHom, Matrix.mulVec_diagonal]
    rw [hw k hk, mul_zero]
  · intro h hh w hw k hk
    change (∑ j : Fin 2 ⊕ Fin 2, (spMat h) k j * w j) = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : s j
    · rw [hs h hh k j hj hk, zero_mul]
    · rw [hw j hj, mul_zero]

variable [Finite K] [CharP K 2]

theorem isTorusReducible_of_tau_fixes {H : Subgroup (StatedSp 2 K)} {x : Fin 2 ⊕ Fin 2}
    (hx : ∀ g ∈ H.map tauSp, ∀ k : Fin 2 ⊕ Fin 2, k ≠ x → (spMat g) k x = 0) :
    IsTorusReducible H := by
  let s : Fin 2 ⊕ Fin 2 → Prop := fun r => x = (tauPair r).1 ∨ x = (tauPair r).2
  have hs : ∀ h ∈ H, ∀ k j, s j → ¬ s k → (spMat h) k j = 0 := by
    intro h hh k j hj hk
    have h2 : (spMat h) k j ^ 2 = 0 := by
      rw [← tauSp_tauSp_apply h k j]
      exact tauSp_apply_eq_zero_of_fixes (g := tauSp h)
        (hx (tauSp h) (Subgroup.mem_map_of_mem tauSp hh)) hj hk
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hex : ∃ j, s j := by
    rcases x with x | x <;> fin_cases x
    · exact ⟨Sum.inl 0, Or.inl rfl⟩
    · exact ⟨Sum.inl 0, Or.inr rfl⟩
    · exact ⟨Sum.inr 0, Or.inl rfl⟩
    · exact ⟨Sum.inr 0, Or.inr rfl⟩
  have hne : ∃ k, ¬ s k := by
    rcases x with x | x <;> fin_cases x
    · exact ⟨Sum.inr 0, by rintro (h | h) <;> exact Sum.inl_ne_inr h⟩
    · exact ⟨Sum.inr 0, by rintro (h | h) <;> exact Sum.inl_ne_inr h⟩
    · exact ⟨Sum.inl 0, by rintro (h | h) <;> exact Sum.inr_ne_inl h⟩
    · exact ⟨Sum.inl 0, by rintro (h | h) <;> exact Sum.inr_ne_inl h⟩
  exact isTorusReducible_of_pattern hs hex hne

theorem isTorusReducible_of_tau_stab_pair {H : Subgroup (StatedSp 2 K)} {r : Fin 2 ⊕ Fin 2}
    (hr : ∀ g ∈ H.map tauSp, ∀ j k : Fin 2 ⊕ Fin 2, (j = (tauPair r).1 ∨ j = (tauPair r).2) →
      ¬ (k = (tauPair r).1 ∨ k = (tauPair r).2) → (spMat g) k j = 0) :
    IsTorusReducible H := by
  let s : Fin 2 ⊕ Fin 2 → Prop := fun j => j = r
  have hs : ∀ h ∈ H, ∀ k j, s j → ¬ s k → (spMat h) k j = 0 := by
    intro h hh k j hj hk
    rw [hj]
    have h2 : (spMat h) k r ^ 2 = 0 := by
      rw [← tauSp_tauSp_apply h k r]
      exact tauSp_apply_eq_zero_of_stab_pair (g := tauSp h)
        (hr (tauSp h) (Subgroup.mem_map_of_mem tauSp hh)) hk
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  refine isTorusReducible_of_pattern (s := s) hs ⟨r, rfl⟩ ⟨r.swap, ?_⟩
  rcases r with r | r
  · exact Sum.inr_ne_inl
  · exact Sum.inl_ne_inr

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS in
theorem isTorusReducible_or_two_le_pRank_of_stab_plane (hK : 8 ≤ Nat.card K) {n p : ℕ}
    (hq : Nat.card K = 2 ^ n) (hp : p.Prime) (hpd : p ∣ 2 ^ n + 1)
    {H : Subgroup (StatedSp 2 K)} (hHH : ⁅H, H⁆ = H)
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hW : ∀ h ∈ H.map tauSp, ∀ i j : Fin 2 ⊕ Fin 2,
      (i = Sum.inl 1 ∨ i = Sum.inr 1) → (j = Sum.inl 0 ∨ j = Sum.inr 0) →
      (spMat h) i j = 0) :
    IsTorusReducible H ∨ 2 ≤ CFSG.Open.pRank p H := by
  have hHH' : ⁅H.map tauSp, H.map tauSp⁆ = H.map tauSp := by
    rw [← Subgroup.map_commutator, hHH]
  have hT' := torus_le_normalizer_map_tauSp hT
  rcases eq_of_stab_plane hK hHH' hT' hW with h | h | h | h
  · left
    apply isTorusReducible_of_tau_fixes (x := Sum.inl 0)
    intro g hg k hk
    rw [h, Subgroup.mem_bot] at hg
    subst hg
    change (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) k (Sum.inl 0) = 0
    exact Matrix.one_apply_ne hk
  · left
    apply isTorusReducible_of_tau_fixes (x := Sum.inl 1)
    intro g hg k hk
    rw [h] at hg
    obtain ⟨A, rfl⟩ := hg
    rw [coe_lam]
    rw [pairMat_apply_of_ne' (y := Sum.inl 1) (by decide) (by decide)
      (A : Matrix (Fin 2) (Fin 2) K) k]
    exact Matrix.one_apply_ne hk
  · left
    apply isTorusReducible_of_tau_fixes (x := Sum.inl 0)
    intro g hg k hk
    rw [h] at hg
    obtain ⟨A, rfl⟩ := hg
    rw [coe_lam]
    rw [pairMat_apply_of_ne' (y := Sum.inl 0) (by decide) (by decide)
      (A : Matrix (Fin 2) (Fin 2) K) k]
    exact Matrix.one_apply_ne hk
  · right
    have h2 : 2 ≤ CFSG.Open.pRank p (H.map tauSp) := by
      rw [h]
      exact two_le_pRank_of_lam_range_le hq hp hpd le_sup_left le_sup_right
    rwa [pRank_map_tauSp hp] at h2

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS in
theorem isTorusReducible_or_two_le_pRank_of_tau (hK : 8 ≤ Nat.card K) {n p : ℕ}
    (hq : Nat.card K = 2 ^ n) (hp : p.Prime) (hpd : p ∣ 2 ^ n + 1) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hτ : IsTorusReducible (H.map tauSp)) :
    IsTorusReducible H ∨ 2 ≤ CFSG.Open.pRank p H := by
  obtain ⟨W, hW0, hW1, hWt, hWH⟩ := hτ
  let s : Fin 2 ⊕ Fin 2 → Prop := fun j => Pi.single j (1 : K) ∈ W
  have hent : ∀ g ∈ H.map tauSp, ∀ j k, s j → ¬ s k → (spMat g) k j = 0 := by
    intro g hg j k hj hk
    exact entry_eq_zero_of_invariant hK hWt (hWH g hg) hj hk
  have hex : ∃ j, s j := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
    exact ⟨j, single_mem_of_torus_invariant hK hWt hw hj⟩
  have hne : ∃ k, ¬ s k := by
    by_contra hall
    have hall' : ∀ k, s k := fun k => by_contra fun hk => hall ⟨k, hk⟩
    apply hW1
    rw [eq_top_iff, ← (Pi.basisFun K (Fin 2 ⊕ Fin 2)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simpa using hall' j
  have hfix : ∀ x : Fin 2 ⊕ Fin 2, s x → (∀ k, k ≠ x → ¬ s k) → IsTorusReducible H := by
    intro x hx hk
    refine isTorusReducible_of_tau_fixes (x := x) ?_
    intro g hg k hkx
    exact hent g hg x k hx (hk k hkx)
  have htriple : ∀ y : Fin 2 ⊕ Fin 2, ¬ s y → (∀ j, j ≠ y → s j) → IsTorusReducible H := by
    intro y hy hys
    refine isTorusReducible_of_tau_fixes (x := y.swap) ?_
    intro g hg k hk
    exact line_of_triple (H := H.map tauSp) (y := y)
      (fun h hh j hj => hent h hh j y (hys j hj) hy) g hg k hk
  have hpair : ∀ r : Fin 2 ⊕ Fin 2,
      (∀ j, (j = (tauPair r).1 ∨ j = (tauPair r).2) → s j) →
      (∀ k, ¬ (k = (tauPair r).1 ∨ k = (tauPair r).2) → ¬ s k) →
      IsTorusReducible H := by
    intro r hj hk
    refine isTorusReducible_of_tau_stab_pair (r := r) ?_
    intro g hg j k hjr hkr
    exact hent g hg j k (hj j hjr) (hk k hkr)
  by_cases h0 : s (Sum.inl 0) <;> by_cases h1 : s (Sum.inl 1) <;>
    by_cases h2 : s (Sum.inr 0) <;> by_cases h3 : s (Sum.inr 1)
  · obtain ⟨k, hk⟩ := hne
    rcases k with k | k <;> fin_cases k
    · exact absurd h0 hk
    · exact absurd h1 hk
    · exact absurd h2 hk
    · exact absurd h3 hk
  · left
    exact htriple (Sum.inr 1) h3 (by
      intro j hj
      rcases j with j | j <;> fin_cases j
      · exact h0
      · exact h1
      · exact h2
      · exact absurd rfl hj)
  · left
    exact htriple (Sum.inr 0) h2 (by
      intro j hj
      rcases j with j | j <;> fin_cases j
      · exact h0
      · exact h1
      · exact absurd rfl hj
      · exact h3)
  · left
    exact hpair (Sum.inl 0)
      (by
        intro j hj
        rcases hj with rfl | rfl
        · exact h0
        · exact h1)
      (by
        intro k hk
        rcases k with k | k <;> fin_cases k
        · exact absurd (Or.inl rfl) hk
        · exact absurd (Or.inr rfl) hk
        · exact h2
        · exact h3)
  · left
    exact htriple (Sum.inl 1) h1 (by
      intro j hj
      rcases j with j | j <;> fin_cases j
      · exact h0
      · exact absurd rfl hj
      · exact h2
      · exact h3)
  · exact isTorusReducible_or_two_le_pRank_of_stab_plane (K := K) hK hq hp hpd hHH hT (by
      intro g hg i j hi hj
      exact hent g hg j i
        (by
          rcases hj with rfl | rfl
          · exact h0
          · exact h2)
        (by
          rcases hi with rfl | rfl
          · exact h1
          · exact h3))
  · left
    exact hpair (Sum.inl 1)
      (by
        intro j hj
        rcases hj with rfl | rfl
        · exact h0
        · exact h3)
      (by
        intro k hk
        rcases k with k | k <;> fin_cases k
        · exact absurd (Or.inl rfl) hk
        · exact h1
        · exact h2
        · exact absurd (Or.inr rfl) hk)
  · left
    exact hfix (Sum.inl 0) h0 (by
      intro k hk
      rcases k with k | k <;> fin_cases k
      · exact absurd rfl hk
      · exact h1
      · exact h2
      · exact h3)
  · left
    exact htriple (Sum.inl 0) h0 (by
      intro j hj
      rcases j with j | j <;> fin_cases j
      · exact absurd rfl hj
      · exact h1
      · exact h2
      · exact h3)
  · left
    exact hpair (Sum.inr 1)
      (by
        intro j hj
        rcases hj with rfl | rfl
        · exact h1
        · exact h2)
      (by
        intro k hk
        rcases k with k | k <;> fin_cases k
        · exact h0
        · exact absurd (Or.inl rfl) hk
        · exact absurd (Or.inr rfl) hk
        · exact h3)
  · exact isTorusReducible_or_two_le_pRank_of_stab_plane (K := K) hK hq hp hpd hHH hT (by
      intro g hg i j hi hj
      have hi' : s i.swap := by
        rcases hi with rfl | rfl
        · simpa using h3
        · simpa using h1
      have hj' : ¬ s j.swap := by
        rcases hj with rfl | rfl
        · simpa using h2
        · simpa using h0
      have hzero := hent g⁻¹ ((H.map tauSp).inv_mem hg) i.swap j.swap hi' hj'
      have hgij : (spMat g) i j = (spMat g⁻¹) j.swap i.swap := by
        simpa only [inv_inv] using spMat_inv_apply (g⁻¹) i j
      rw [hgij]
      exact hzero)
  · left
    exact hfix (Sum.inl 1) h1 (by
      intro k hk
      rcases k with k | k <;> fin_cases k
      · exact h0
      · exact absurd rfl hk
      · exact h2
      · exact h3)
  · left
    exact hpair (Sum.inr 0)
      (by
        intro j hj
        rcases hj with rfl | rfl
        · exact h2
        · exact h3)
      (by
        intro k hk
        rcases k with k | k <;> fin_cases k
        · exact h0
        · exact h1
        · exact absurd (Or.inl rfl) hk
        · exact absurd (Or.inr rfl) hk)
  · left
    exact hfix (Sum.inr 0) h2 (by
      intro k hk
      rcases k with k | k <;> fin_cases k
      · exact h0
      · exact h1
      · exact absurd rfl hk
      · exact h3)
  · left
    exact hfix (Sum.inr 1) h3 (by
      intro k hk
      rcases k with k | k <;> fin_cases k
      · exact h0
      · exact h1
      · exact h2
      · exact absurd rfl hk)
  · obtain ⟨j, hj⟩ := hex
    rcases j with j | j <;> fin_cases j
    · exact absurd hj h0
    · exact absurd hj h1
    · exact absurd hj h2
    · exact absurd hj h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
