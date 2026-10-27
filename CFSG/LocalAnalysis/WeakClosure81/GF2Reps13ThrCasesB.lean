module

public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem w16g_commSub_eq_of_commSub_le (hW : ∀ w : W, w * w = 1) {t : MulAut W}
    (htt : t * t = 1) {P : Subgroup (MulAut W)} (hP3 : IsPGroup 3 ↥P)
    (hc : ⁅P, Subgroup.zpowers t⁆ = P) {V₀ : Subgroup W} (hVP : StableUnder P V₀)
    (hVt : ∀ v ∈ V₀, t v ∈ V₀) (hle : commSub ⊤ (Subgroup.zpowers t) ≤ V₀) :
    ∀ Q : Subgroup (MulAut W), Q ≤ P → commSub ⊤ Q = commSub V₀ Q := by
  classical
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let K : Subgroup (MulAut W) :=
    { carrier := {x | (∀ v ∈ V₀, x v ∈ V₀) ∧ (∀ v ∈ V₀, x⁻¹ v ∈ V₀) ∧
        ∀ w : W, x w * w⁻¹ ∈ V₀}
      one_mem' := by
        refine ⟨?_, ?_, ?_⟩
        · intro v hv; simpa using hv
        · intro v hv; simpa using hv
        · intro w; simp
      mul_mem' := by
        rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
        refine ⟨?_, ?_, ?_⟩
        · intro v hv
          rw [MulAut.mul_apply]
          exact hx1 (y v) (hy1 v hv)
        · intro v hv
          rw [mul_inv_rev, MulAut.mul_apply]
          exact hy2 (x⁻¹ v) (hx2 v hv)
        · intro w
          rw [MulAut.mul_apply]
          rw [show x (y w) * w⁻¹ = (x (y w) * (y w)⁻¹) * (y w * w⁻¹) by group]
          exact V₀.mul_mem (hx3 (y w)) (hy3 w)
      inv_mem' := by
        rintro x ⟨hx1, hx2, hx3⟩
        refine ⟨hx2, ?_, ?_⟩
        · intro v hv
          rw [inv_inv]
          exact hx1 v hv
        · intro w
          have h := hx3 (x⁻¹ w)
          rw [MulAut.apply_inv_self (M := W) x w] at h
          simpa only [mul_inv_rev, inv_inv] using V₀.inv_mem h }
  have hzpow : ∀ g ∈ Subgroup.zpowers t, g = 1 ∨ g = t := by
    intro g hg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hn]
    have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htt
    rw [zpow_eq_zpow_emod n ht2]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left; rw [h0]; simp
    · right; rw [h1]; simp
  have hgen : ∀ b : W, t b * b⁻¹ ∈ commSub ⊤ (Subgroup.zpowers t) := fun b =>
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, b, Subgroup.mem_top b, rfl⟩
  have hcommK : ⁅P, Subgroup.zpowers t⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro y hy g hg
    rcases hzpow g hg with hg1 | hgt
    · rw [hg1]
      rw [show ⁅y, (1 : MulAut W)⁆ = 1 by simp [commutatorElement_def]]
      exact K.one_mem
    · rw [hgt]
      have hy1 : ∀ v ∈ V₀, y v ∈ V₀ := fun v hv => hVP y hy v hv
      have hy2 : ∀ v ∈ V₀, y⁻¹ v ∈ V₀ := fun v hv => hVP y⁻¹ (P.inv_mem hy) v hv
      have ht1 : ∀ v ∈ V₀, t v ∈ V₀ := hVt
      have ht2 : ∀ v ∈ V₀, t⁻¹ v ∈ V₀ := by rw [htinv]; exact hVt
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        rw [commutatorElement_def]
        simp only [MulAut.mul_apply]
        exact hy1 (t (y⁻¹ (t⁻¹ v)))
          (ht1 (y⁻¹ (t⁻¹ v)) (hy2 (t⁻¹ v) (ht2 v hv)))
      · intro v hv
        have hinv : ⁅y, t⁆⁻¹ = t * y * t⁻¹ * y⁻¹ := by
          rw [commutatorElement_def]; group
        rw [hinv]
        simp only [MulAut.mul_apply]
        exact ht1 (y (t⁻¹ (y⁻¹ v)))
          (hy1 (t⁻¹ (y⁻¹ v)) (ht2 (y⁻¹ v) (hy2 v hv)))
      · intro w
        rw [commutatorElement_def]
        simp only [MulAut.mul_apply, htinv]
        have hA : t w * w⁻¹ ∈ V₀ := hle (hgen w)
        have hB : y⁻¹ (t w) * (y⁻¹ w)⁻¹ ∈ V₀ := by
          simpa only [map_mul, map_inv] using
            hVP y⁻¹ (P.inv_mem hy) (t w * w⁻¹) hA
        have hC : t (y⁻¹ (t w)) * (y⁻¹ (t w))⁻¹ ∈ V₀ := hle (hgen (y⁻¹ (t w)))
        have hD : y (t (y⁻¹ (t w))) * (t w)⁻¹ ∈ V₀ := by
          have := hVP y hy (t (y⁻¹ (t w)) * (y⁻¹ (t w))⁻¹) hC
          simpa only [map_mul, map_inv, MulAut.apply_inv_self] using this
        rw [show y (t (y⁻¹ (t w))) * w⁻¹
            = (y (t (y⁻¹ (t w))) * (t w)⁻¹) * (t w * w⁻¹) by group]
        exact V₀.mul_mem hD hA
  have hPK : P ≤ K := by
    rw [← hc]
    exact hcommK
  have hcommSub_le : commSub ⊤ P ≤ V₀ := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    exact (hPK hx).2.2 w
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).mp hP3
    rw [hn]
    exact (Nat.Prime.odd_of_ne_two Nat.prime_three (by norm_num)).pow
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  intro Q hQ
  refine le_antisymm ?_ (commSub_mono le_top le_rfl)
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, w, -, rfl⟩
  have hxP : x ∈ P := hQ hx
  have htop : fixV P ⊔ commSub ⊤ P = ⊤ := Asc81c.fixV_sup_commSub_eq_top' hW2 hPodd
  have hw : w ∈ fixV P ⊔ commSub ⊤ P := by rw [htop]; exact Subgroup.mem_top w
  obtain ⟨c, hcf, v, hv, rfl⟩ := Subgroup.mem_sup.1 hw
  have hxc : x c = c := hcf x hxP
  have h1 : x (c * v) * (c * v)⁻¹ = x v * v⁻¹ := by
    rw [map_mul, hxc, mul_inv_rev, mul_comm c (x v), mul_assoc, ← mul_assoc c,
      mul_comm c v⁻¹, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1]
  exact Subgroup.subset_closure ⟨x, hx, v, hcommSub_le hv, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81
