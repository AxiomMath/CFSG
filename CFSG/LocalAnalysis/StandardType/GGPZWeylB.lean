module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Center
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CoxeterSystem
  CFSG.LieType.Universal.Symplectic

theorem ggCoxeterB_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (CoxeterMatrix.B n).Group = 2 ^ n * n.factorial :=
  le_antisymm (card_coxeterB_le n) (SpFrame.card_coxeterB_ge n hn)

private theorem pnb_exists_perm {r : ℕ} (σ : Equiv.Perm (Fin (r + 1))) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group,
      SpRealizes (r + 1) w σ 1 := by
  have hmem_gen : σ ∈ Submonoid.closure
      (Set.range fun i : Fin r => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ r]
    exact Submonoid.mem_top σ
  refine Submonoid.closure_induction (motive := fun σ _ =>
      ∃ w : (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group,
        SpRealizes (r + 1) w σ 1) ?_ ?_ ?_ hmem_gen
  · rintro x ⟨i, rfl⟩
    have hlt : i.castSucc.val + 1 < r + 1 := by simp only [Fin.val_castSucc]; omega
    have he : (⟨i.castSucc.val + 1, hlt⟩ : Fin (r + 1)) = i.succ := Fin.ext (by simp)
    exact ⟨(coxeterMatrix (isFiniteType_cartanC (r + 1))).toCoxeterSystem.simple i.castSucc,
      (spRealizes_simple_of_lt (m := r + 1) hlt).congr (by rw [he]) rfl⟩
  · exact ⟨1, spRealizes_one⟩
  · rintro x y _ _ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    exact ⟨w₁ * w₂, h₁.mul_one h₂⟩

private theorem pnb_exists_sgn {r : ℕ} (hr : 1 ≤ r) (a : Fin (r + 1)) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group,
      SpRealizes (r + 1) w 1 (spSgn a) := by
  obtain ⟨ε, hε, -⟩ := SpFrame.exists_sign_family r hr
  exact ⟨ε a, hε a⟩

private theorem pnb_spSgnOn_insert {r : ℕ} {a : Fin (r + 1)} {T : Finset (Fin (r + 1))}
    (ha : a ∉ T) :
    (fun c => spSgnOn T c * spSgn a c) = spSgnOn (insert a T) := by
  funext c
  unfold spSgnOn spSgn
  by_cases hc : c = a
  · subst hc
    simp [ha]
  · by_cases hT : c ∈ T
    · simp [hc, hT]
    · simp [hc, hT, Finset.mem_insert]

private theorem pnb_exists_sgnOn {r : ℕ} (hr : 1 ≤ r) (T : Finset (Fin (r + 1))) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group,
      SpRealizes (r + 1) w 1 (spSgnOn T) := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, spRealizes_one.congr rfl (by funext c; simp [spSgnOn])⟩
  | insert a T ha ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨z, hz⟩ := pnb_exists_sgn hr a
    refine ⟨z * w, (hz.mul hw).congr (by rw [mul_one]) ?_⟩
    simpa only [Equiv.Perm.one_apply] using pnb_spSgnOn_insert ha

private theorem pnb_exists_neg {r : ℕ} (hr : 1 ≤ r) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group,
      SpRealizes (r + 1) w 1 (fun _ => -1) := by
  obtain ⟨w, hw⟩ := pnb_exists_sgnOn (r := r) hr Finset.univ
  refine ⟨w, hw.congr rfl ?_⟩
  funext c
  simp [spSgnOn]

private theorem pnb_neg_mem_center {r : ℕ}
    {w₀ : (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group}
    (hw₀ : SpRealizes (r + 1) w₀ 1 (fun _ => -1)) :
    w₀ ∈ Subgroup.center (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group := by
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨π, s, _hs, hw⟩ := exists_spRealizes w
  have h1 : SpRealizes (r + 1) (w₀ * w) π (fun c => - s c) := by
    refine (hw₀.mul hw).congr (by rw [one_mul]) ?_
    funext c
    simp
  have h2 : SpRealizes (r + 1) (w * w₀) π (fun c => - s c) := by
    refine (hw.mul hw₀).congr (by rw [mul_one]) ?_
    funext c
    simp
  exact SpRealizes.inj h2 h1

private theorem pnb_center_eq_one_or_neg {r : ℕ} (hr : 1 ≤ r)
    {w : (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group}
    (hwc : w ∈ Subgroup.center (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group)
    {w₀ : (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group}
    (hw₀ : SpRealizes (r + 1) w₀ 1 (fun _ => -1)) :
    w = 1 ∨ w = w₀ := by
  obtain ⟨π, s, hs, hw⟩ := exists_spRealizes w
  have hsinv : ∀ σ : Equiv.Perm (Fin (r + 1)), (fun c => s (σ c)) = s := by
    intro σ
    obtain ⟨u, hu⟩ := pnb_exists_perm σ
    have hcomm : u * w = w * u := (Subgroup.mem_center_iff.mp hwc) u
    have hA : SpRealizes (r + 1) (w * u) (π * σ) (fun c => s (σ c)) := by
      refine (hw.mul hu).congr rfl ?_
      funext c
      simp
    have hB : SpRealizes (r + 1) (w * u) (σ * π) s := by
      have h' : SpRealizes (r + 1) (u * w) (σ * π) s := by
        refine (hu.mul hw).congr rfl ?_
        funext c
        simp
      exact hcomm ▸ h'
    exact (SpRealizes.unique (fun c => hs (σ c)) hs hA hB).2
  have hconst : ∀ c : Fin (r + 1), s c = s 0 := by
    intro c
    by_cases hc : c = 0
    · rw [hc]
    · have h := congrFun (hsinv (Equiv.swap c 0)) c
      rw [Equiv.swap_apply_left] at h
      exact h.symm
  have hπ : π = 1 := by
    ext a
    obtain ⟨z, hz⟩ := pnb_exists_sgn hr a
    have hcomm : z * w = w * z := (Subgroup.mem_center_iff.mp hwc) z
    have hA : SpRealizes (r + 1) (w * z) π (fun c => spSgn a c * s c) := by
      refine (hw.mul hz).congr (by rw [mul_one]) ?_
      funext c
      simp
    have hB : SpRealizes (r + 1) (w * z) π (fun c => s c * spSgn a (π c)) := by
      have h' : SpRealizes (r + 1) (z * w) π (fun c => s c * spSgn a (π c)) :=
        (hz.mul hw).congr (by rw [one_mul]) rfl
      exact hcomm ▸ h'
    have hsign := (SpRealizes.unique ((spIsSign_spSgn a).mul hs 1)
      (hs.mul (spIsSign_spSgn a) π) hA hB).2
    have hval := congrFun hsign a
    simp only [Equiv.Perm.one_apply] at hval
    have hsaa : spSgn a a = -1 := by simp [spSgn]
    rw [hsaa] at hval
    have key : spSgn a (π a) = -1 := by
      rcases hs a with h | h
      · rw [h] at hval
        linarith
      · rw [h] at hval
        linarith
    by_contra hne
    have hne' : ¬ π a = a := fun h => hne (congrArg Fin.val h)
    have h1 : spSgn a (π a) = 1 := by simp only [spSgn, if_neg hne']
    rw [h1] at key
    norm_num at key
  have hs1 : s = 1 ∨ s = (fun _ => -1) := by
    rcases hs 0 with h0 | h0
    · left
      funext c
      exact (hconst c).trans h0
    · right
      funext c
      exact (hconst c).trans h0
  have hw1 : SpRealizes (r + 1) w 1 s := hπ ▸ hw
  rcases hs1 with hs1 | hs1
  · exact Or.inl (SpRealizes.inj (hs1 ▸ hw1) spRealizes_one)
  · exact Or.inr (SpRealizes.inj (hs1 ▸ hw1) hw₀)

theorem ggCoxeterB_center (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥(Subgroup.center (CoxeterMatrix.B n).Group) = 2 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, (Nat.sub_add_cancel hn1).symm⟩
  have hr : 1 ≤ r := by omega
  rw [← coxeterMatrix_cartanC_eq_B (r + 1)]
  classical
  let W := (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group
  change Nat.card ↥(Subgroup.center W) = 2
  have hcardW : Nat.card W = 2 ^ (r + 1) * (r + 1).factorial := by
    change Nat.card (coxeterMatrix (isFiniteType_cartanC (r + 1))).Group = _
    rw [coxeterMatrix_cartanC_eq_B (r + 1)]
    exact ggCoxeterB_card (r + 1) (by omega)
  have hpos : 0 < Nat.card W := by
    rw [hcardW]
    positivity
  have hfin : Finite W := (Nat.card_pos_iff.mp hpos).2
  obtain ⟨w₀, hw₀⟩ := pnb_exists_neg hr
  have hw₀c : w₀ ∈ Subgroup.center W := pnb_neg_mem_center hw₀
  have hcenter : Subgroup.center W = Subgroup.zpowers w₀ := by
    apply le_antisymm
    · intro w hw
      rcases pnb_center_eq_one_or_neg hr hw hw₀ with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers w₀
    · exact Subgroup.zpowers_le.mpr hw₀c
  have hw₀sq : w₀ ^ 2 = 1 := by
    rw [pow_two]
    have hmul : SpRealizes (r + 1) (w₀ * w₀) 1 1 := by
      refine (hw₀.mul hw₀).congr (by rw [mul_one]) ?_
      funext c
      simp
    exact SpRealizes.inj hmul spRealizes_one
  have hw₀ne : w₀ ≠ 1 := by
    intro h
    have h1 : SpRealizes (r + 1) (1 : W) 1 (fun _ => -1) := h ▸ hw₀
    have hsign : (fun _ : Fin (r + 1) => (-1 : ℤ)) = (1 : Fin (r + 1) → ℤ) :=
      (SpRealizes.unique (fun _ => Or.inr rfl) spIsSign_one h1 spRealizes_one).2
    have hval := congrFun hsign ⟨0, Nat.succ_pos r⟩
    norm_num at hval
  have horder : orderOf w₀ = 2 := orderOf_eq_prime (p := 2) hw₀sq hw₀ne
  let _ : Fintype W := Fintype.ofFinite W
  calc Nat.card ↥(Subgroup.center W)
      = Nat.card ↥(Subgroup.zpowers w₀) := by rw [hcenter]
    _ = Fintype.card ↥(Subgroup.zpowers w₀) := Nat.card_eq_fintype_card
    _ = orderOf w₀ := Fintype.card_zpowers
    _ = 2 := horder

end CFSG.StandardType

end
