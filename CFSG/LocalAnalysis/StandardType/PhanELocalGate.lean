module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag
public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2] {n : ℕ}

private theorem plh_finrank_sup_of_disjoint {A B : Submodule K (Fin n → K)}
    (h : Disjoint A B) : finrank K ↥(A ⊔ B) = finrank K A + finrank K B := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [h.eq_bot, finrank_bot, add_zero] at hsum
  exact hsum

private theorem plh_hermLin_apply (lo hi : ℕ) (u v : Fin n → K) :
    hermLin K f n lo hi u v =
      ∑ i : Fin n, if lo ≤ i.val ∧ i.val < hi then sg K f (u i) * v i else 0 := by
  rw [hermLin, LinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : lo ≤ i.val ∧ i.val < hi <;> simp [h]

private theorem plh_hermLin_apply_eq_zero_of_mem_Vsub {lo hi : ℕ} {v : Fin n → K}
    (hv : v ∈ Vsub (K := K) n lo) (u : Fin n → K) : hermLin K f n lo hi u v = 0 := by
  rw [plh_hermLin_apply]
  refine Finset.sum_eq_zero ?_
  intro i _
  by_cases h : lo ≤ i.val ∧ i.val < hi
  · simp [h, hv i h.1]
  · simp [h]

private theorem plh_le_perpB_of_Vsub {lo hi : ℕ} (U : Submodule K (Fin n → K)) :
    Vsub (K := K) n lo ≤ perpB K f n lo hi U := by
  intro v hv
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u _
  exact plh_hermLin_apply_eq_zero_of_mem_Vsub (f := f) hv u

private theorem plh_hermLin_single_apply {lo hi : ℕ} {j : Fin n}
    (hlj : lo ≤ j.val) (hjh : j.val < hi) (v : Fin n → K) :
    hermLin K f n lo hi (Pi.single j (1 : K)) v = v j := by
  rw [plh_hermLin_apply]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp [hlj, hjh]
  · intro i _ hij
    by_cases h : lo ≤ i.val ∧ i.val < hi
    · rw [if_pos h]
      rw [Pi.single_eq_of_ne' hij.symm]
      simp
    · simp [h]

private theorem plh_perpB_Vsub_inf {lo hi : ℕ} (hlh : lo ≤ hi) :
    Vsub (K := K) n hi ⊓ perpB K f n lo hi (Vsub (K := K) n hi) = Vsub (K := K) n lo := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvh, hperp⟩ := hv
    simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker] at hperp
    intro j hj
    by_cases hjh : j.val < hi
    · have hmem : (Pi.single j (1 : K) : Fin n → K) ∈ Vsub (K := K) n hi := by
        intro k hk
        rw [Pi.single_eq_of_ne' (show j ≠ k by rintro rfl; omega)]
      have h := hperp (Pi.single j (1 : K)) hmem
      rw [plh_hermLin_single_apply (f := f) hj hjh v] at h
      exact h
    · exact hvh j (le_of_not_gt hjh)
  · intro v hv
    rw [Submodule.mem_inf]
    exact ⟨Vsub_mono (K := K) hlh hv, plh_le_perpB_of_Vsub (f := f) _ hv⟩

theorem blockU_zero {d : List ℕ} (hle : ∀ i, i < d.length → d.getD i 0 ≤ n)
    (hmono : ∀ i, i + 1 < d.length → d.getD i 0 ≤ d.getD (i + 1) 0) {x : FlagK K n}
    (hx : x ∈ farSet n d) {i : ℕ} (hi : i + 1 < d.length) :
    blockU K n d x.E i 0 = Vsub n (d.getD i 0) := by
  have hb : d.getD (i + 1) 0 ≤ n := hle (i + 1) hi
  have hbot : x.E (n - d.getD (i + 1) 0) ⊓ Vsub n (d.getD (i + 1) 0) = ⊥ := by
    have h := (mem_farSet_iff (K := K) hle).mp hx (i + 1) hi (n - d.getD (i + 1) 0)
      (by omega)
    exact h.1 (by omega)
  show (x.E (n - d.getD (i + 1) 0 + 0) ⊓ Vsub n (d.getD (i + 1) 0)) ⊔ Vsub n (d.getD i 0) =
    Vsub n (d.getD i 0)
  rw [Nat.add_zero, hbot, bot_sup_eq]

theorem blockU_last {d : List ℕ} (hle : ∀ i, i < d.length → d.getD i 0 ≤ n)
    (hmono : ∀ i, i + 1 < d.length → d.getD i 0 ≤ d.getD (i + 1) 0) {x : FlagK K n}
    (hx : x ∈ farSet n d) {i : ℕ} (hi : i + 1 < d.length) :
    blockU K n d x.E i (d.getD (i + 1) 0 - d.getD i 0) = Vsub n (d.getD (i + 1) 0) := by
  have ha : d.getD i 0 ≤ n := hle i (by omega)
  have hb : d.getD (i + 1) 0 ≤ n := hle (i + 1) hi
  have hab : d.getD i 0 ≤ d.getD (i + 1) 0 := hmono i hi
  have hxf := hx
  simp only [farSet, Set.mem_setOf_eq] at hxf
  have hfinA : finrank K ↥(x.E (n - d.getD i 0) ⊓ Vsub n (d.getD (i + 1) 0)) =
      d.getD (i + 1) 0 - d.getD i 0 := by
    rw [hxf (i + 1) hi (n - d.getD i 0) (by omega)]
    omega
  have hfinB : finrank K ↥(Vsub (K := K) n (d.getD i 0)) = d.getD i 0 :=
    finrank_Vsub ha
  have hbot : x.E (n - d.getD i 0) ⊓ Vsub n (d.getD i 0) = ⊥ := by
    have h0 : finrank K ↥(x.E (n - d.getD i 0) ⊓ Vsub n (d.getD i 0)) = 0 := by
      rw [hxf i (by omega) (n - d.getD i 0) (by omega)]
      omega
    exact (Submodule.finrank_eq_zero).mp h0
  have hdisj : Disjoint (x.E (n - d.getD i 0) ⊓ Vsub n (d.getD (i + 1) 0))
      (Vsub (K := K) n (d.getD i 0)) := by
    rw [disjoint_iff]
    have hle : (x.E (n - d.getD i 0) ⊓ Vsub n (d.getD (i + 1) 0)) ⊓ Vsub n (d.getD i 0) ≤
        x.E (n - d.getD i 0) ⊓ Vsub n (d.getD i 0) := by
      intro v hv
      exact ⟨hv.1.1, hv.2⟩
    exact le_bot_iff.mp (hle.trans (le_of_eq hbot))
  have hsup : finrank K ↥((x.E (n - d.getD i 0) ⊓ Vsub n (d.getD (i + 1) 0)) ⊔
      Vsub (K := K) n (d.getD i 0)) = d.getD (i + 1) 0 := by
    rw [plh_finrank_sup_of_disjoint hdisj, hfinA, hfinB]
    omega
  have hleV : (x.E (n - d.getD i 0) ⊓ Vsub n (d.getD (i + 1) 0)) ⊔
      Vsub (K := K) n (d.getD i 0) ≤ Vsub n (d.getD (i + 1) 0) :=
    sup_le inf_le_right (Vsub_mono (K := K) hab)
  have hgoal : (x.E (n - d.getD i 0) ⊓ Vsub n (d.getD (i + 1) 0)) ⊔
      Vsub (K := K) n (d.getD i 0) = Vsub n (d.getD (i + 1) 0) :=
    Submodule.eq_of_le_of_finrank_eq hleV (by rw [hsup, finrank_Vsub hb])
  show (x.E (n - d.getD (i + 1) 0 + (d.getD (i + 1) 0 - d.getD i 0)) ⊓
      Vsub n (d.getD (i + 1) 0)) ⊔ Vsub n (d.getD i 0) = Vsub n (d.getD (i + 1) 0)
  rw [show n - d.getD (i + 1) 0 + (d.getD (i + 1) 0 - d.getD i 0) = n - d.getD i 0
    by omega]
  exact hgoal

theorem blockOK_iff_of_far {d : List ℕ} {pol : List Bool}
    (hle : ∀ i, i < d.length → d.getD i 0 ≤ n)
    (hmono : ∀ i, i + 1 < d.length → d.getD i 0 ≤ d.getD (i + 1) 0) {x : FlagK K n}
    (hx : x ∈ farSet n d) {i : ℕ} (hi : i + 1 < d.length) :
    blockOK K f n d pol x.E i ↔
      ∀ r, 0 < r → r < d.getD (i + 1) 0 - d.getD i 0 →
        if pol.getD i false then
          blockU K n d x.E i r ⊓
            perpB K f n (d.getD i 0) (d.getD (i + 1) 0) (blockU K n d x.E i r) =
            Vsub n (d.getD i 0)
        else
          blockU K n d x.E i r ⊓ sgS K f n
            (blockU K n d x.E i (d.getD (i + 1) 0 - d.getD i 0 - r)) = Vsub n (d.getD i 0) := by
  have hab : d.getD i 0 ≤ d.getD (i + 1) 0 := hmono i hi
  have hU0 := blockU_zero hle hmono hx hi
  have hUm := blockU_last hle hmono hx hi
  constructor
  · intro h r hr0 hrm
    exact h r (by omega)
  · intro h r hr
    by_cases hp : pol.getD i false = true
    · rw [if_pos hp]
      by_cases hr0 : r = 0
      · subst hr0
        rw [hU0]
        exact inf_eq_left.mpr (plh_le_perpB_of_Vsub (f := f) _)
      · by_cases hrm : r = d.getD (i + 1) 0 - d.getD i 0
        · subst hrm
          rw [hUm]
          exact plh_perpB_Vsub_inf (f := f) hab
        · have h1 : 0 < r := by omega
          have h2 : r < d.getD (i + 1) 0 - d.getD i 0 := by omega
          simpa only [if_pos hp] using h r h1 h2
    · rw [if_neg hp]
      by_cases hr0 : r = 0
      · subst hr0
        rw [hU0, Nat.sub_zero, hUm, sgS_Vsub]
        exact inf_eq_left.mpr (Vsub_mono (K := K) hab)
      · by_cases hrm : r = d.getD (i + 1) 0 - d.getD i 0
        · subst hrm
          rw [hUm, show d.getD (i + 1) 0 - d.getD i 0 - (d.getD (i + 1) 0 - d.getD i 0) = 0
            by omega, hU0, sgS_Vsub]
          exact inf_eq_right.mpr (Vsub_mono (K := K) hab)
        · have h1 : 0 < r := by omega
          have h2 : r < d.getD (i + 1) 0 - d.getD i 0 := by omega
          simpa only [if_neg hp] using h r h1 h2

theorem blockOK_of_size_one {d : List ℕ} {pol : List Bool}
    (hle : ∀ i, i < d.length → d.getD i 0 ≤ n)
    (hmono : ∀ i, i + 1 < d.length → d.getD i 0 ≤ d.getD (i + 1) 0) {x : FlagK K n}
    (hx : x ∈ farSet n d) {i : ℕ} (hi : i + 1 < d.length)
    (h1 : d.getD (i + 1) 0 = d.getD i 0 + 1) : blockOK K f n d pol x.E i := by
  rw [blockOK_iff_of_far f hle hmono hx hi]
  intro r hr0 hrm
  exfalso
  omega

end CFSG.ClassicalInvolution.Phan.PhanE

end
