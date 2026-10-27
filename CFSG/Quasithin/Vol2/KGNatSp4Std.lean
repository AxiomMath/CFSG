module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K]

@[expose] def vec4 (a₀ a₁ b₀ b₁ : K) : Fin 2 ⊕ Fin 2 → K := Sum.elim ![a₀, a₁] ![b₀, b₁]

omit [Field K] in
theorem vec4_eq {x y : Fin 2 ⊕ Fin 2 → K} (h0 : x (.inl 0) = y (.inl 0))
    (h1 : x (.inl 1) = y (.inl 1)) (h2 : x (.inr 0) = y (.inr 0)) (h3 : x (.inr 1) = y (.inr 1)) :
    x = y := by
  funext k
  rcases k with i | i <;> fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem qSp_mulVec (x y z : K) (v : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (qSp x y z) *ᵥ v = vec4 (v (.inl 0) + x * v (.inr 0) + y * v (.inr 1))
      (v (.inl 1) + y * v (.inr 0) + z * v (.inr 1)) (v (.inr 0)) (v (.inr 1)) := by
  rw [mat_qSp]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [qMat, symm3, vec4, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.one_apply] <;> ring

theorem nSp_mulVec (r : K) (v : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (nSp r) *ᵥ v = vec4 (v (.inl 0) + r * v (.inl 1)) (v (.inl 1)) (v (.inr 0))
      (v (.inr 1) - r * v (.inr 0)) := by
  have hinv : ((uGL r)⁻¹ : GL (Fin 2) K) = uGL (-r) := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← uGL_add, add_neg_cancel, uGL_zero]
  rw [nSp, mat_lSp, hinv, coe_uGL, coe_uGL]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [vec4, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qSp_mem_Usp (x y z : K) : qSp x y z ∈ Usp K := ⟨x, y, z, 0, by rw [nSp_zero, mul_one]⟩

theorem nSp_mem_Usp (r : K) : nSp r ∈ Usp K := ⟨0, 0, 0, r, by rw [qSp_zero, one_mul]⟩

variable (K) in
@[expose] def spLine : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {x | x (.inl 1) = 0 ∧ x (.inr 0) = 0 ∧ x (.inr 1) = 0}
  add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2.1, hy.2.1],
    by simp [hx.2.2, hy.2.2]⟩
  zero_mem' := ⟨rfl, rfl, rfl⟩
  smul_mem' := fun c x hx => ⟨by simp [hx.1], by simp [hx.2.1], by simp [hx.2.2]⟩

variable (K) in
@[expose] def spPlane : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {x | x (.inr 0) = 0 ∧ x (.inr 1) = 0}
  add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c x hx => ⟨by simp [hx.1], by simp [hx.2]⟩

variable (K) in
@[expose] def spHyp : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {x | x (.inr 0) = 0}
  add_mem' := fun {x y} hx hy => by
    change (x + y) (.inr 0) = 0
    rw [Pi.add_apply, show x (.inr 0) = 0 from hx, show y (.inr 0) = 0 from hy, add_zero]
  zero_mem' := rfl
  smul_mem' := fun c x hx => by
    change (c • x) (.inr 0) = 0
    rw [Pi.smul_apply, show x (.inr 0) = 0 from hx, smul_zero]

theorem mem_spLine {x : Fin 2 ⊕ Fin 2 → K} :
    x ∈ spLine K ↔ x (.inl 1) = 0 ∧ x (.inr 0) = 0 ∧ x (.inr 1) = 0 := Iff.rfl

theorem mem_spPlane {x : Fin 2 ⊕ Fin 2 → K} :
    x ∈ spPlane K ↔ x (.inr 0) = 0 ∧ x (.inr 1) = 0 := Iff.rfl

theorem mem_spHyp {x : Fin 2 ⊕ Fin 2 → K} : x ∈ spHyp K ↔ x (.inr 0) = 0 := Iff.rfl

theorem spLine_le_spPlane : spLine K ≤ spPlane K := fun _ hx => hx.2

theorem spPlane_le_spHyp : spPlane K ≤ spHyp K := fun _ hx => hx.1

@[expose] def UStableSp (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) : Prop :=
  ∀ u ∈ Usp K, ∀ x ∈ S, mat 2 K u *ᵥ x ∈ S

omit [Field K] in
theorem vec4_apply_inl0 (a b c d : K) : vec4 a b c d (.inl 0) = a := rfl
omit [Field K] in
theorem vec4_apply_inl1 (a b c d : K) : vec4 a b c d (.inl 1) = b := rfl
omit [Field K] in
theorem vec4_apply_inr0 (a b c d : K) : vec4 a b c d (.inr 0) = c := rfl
omit [Field K] in
theorem vec4_apply_inr1 (a b c d : K) : vec4 a b c d (.inr 1) = d := rfl

theorem spPlane_le_of_stable {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hS : UStableSp S)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ S) (h2 : v (.inr 0) = 0) (h3 : v (.inr 1) = 0)
    (h1 : v (.inl 1) ≠ 0) : spPlane K ≤ S := by
  have e0 : vec4 (v (.inl 1)) 0 0 0 ∈ S := by
    have h := S.sub_mem (hS _ (nSp_mem_Usp 1) v hv) hv
    rw [nSp_mulVec] at h
    convert h using 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1, h2]
  intro w hw
  have hw' : w = ((w (.inl 0) - w (.inl 1) / v (.inl 1) * v (.inl 0)) / v (.inl 1)) •
      vec4 (v (.inl 1)) 0 0 0 + (w (.inl 1) / v (.inl 1)) • v := by
    refine vec4_eq ?_ ?_ ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl0]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl1]
      field_simp
      ring
    · simp [vec4_apply_inr0, hw.1, h2]
    · simp [vec4_apply_inr1, hw.2, h3]
  rw [hw']
  exact S.add_mem (S.smul_mem _ e0) (S.smul_mem _ hv)

theorem spHyp_le_of_stable {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hS : UStableSp S)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ S) (h2 : v (.inr 0) = 0) (h3 : v (.inr 1) ≠ 0) :
    spHyp K ≤ S := by
  have e0 : vec4 (v (.inr 1)) 0 0 0 ∈ S := by
    have h := S.sub_mem (hS _ (qSp_mem_Usp 0 1 0) v hv) hv
    rw [qSp_mulVec] at h
    convert h using 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1, h2]
  have e1 : vec4 0 (v (.inr 1)) 0 0 ∈ S := by
    have h := S.sub_mem (hS _ (qSp_mem_Usp 0 0 1) v hv) hv
    rw [qSp_mulVec] at h
    convert h using 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1, h2]
  intro w hw
  have hw2 : w (.inr 0) = 0 := hw
  have hw' : w = ((w (.inl 0) - w (.inr 1) / v (.inr 1) * v (.inl 0)) / v (.inr 1)) •
      vec4 (v (.inr 1)) 0 0 0 + ((w (.inl 1) - w (.inr 1) / v (.inr 1) * v (.inl 1)) / v (.inr 1))
      • vec4 0 (v (.inr 1)) 0 0 + (w (.inr 1) / v (.inr 1)) • v := by
    refine vec4_eq ?_ ?_ ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl0]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl1]
      field_simp
      ring
    · simp [vec4_apply_inr0, hw2, h2]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inr1]
      field_simp
      ring
  rw [hw']
  exact S.add_mem (S.add_mem (S.smul_mem _ e0) (S.smul_mem _ e1)) (S.smul_mem _ hv)

theorem eq_top_of_stable_sp {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hS : UStableSp S)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ S) (h2 : v (.inr 0) ≠ 0) : S = ⊤ := by
  have e0 : vec4 (v (.inr 0)) 0 0 0 ∈ S := by
    have h := S.sub_mem (hS _ (qSp_mem_Usp 1 0 0) v hv) hv
    rw [qSp_mulVec] at h
    convert h using 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1]
  have e1 : vec4 (v (.inr 1)) (v (.inr 0)) 0 0 ∈ S := by
    have h := S.sub_mem (hS _ (qSp_mem_Usp 0 1 0) v hv) hv
    rw [qSp_mulVec] at h
    convert h using 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1]
  have e3 : vec4 (v (.inl 1)) 0 0 (-v (.inr 0)) ∈ S := by
    have h := S.sub_mem (hS _ (nSp_mem_Usp 1) v hv) hv
    rw [nSp_mulVec] at h
    convert h using 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1]
  refine eq_top_iff.mpr fun w _ => ?_
  set c2 := w (.inr 0) / v (.inr 0) with hc2
  set c3 := (c2 * v (.inr 1) - w (.inr 1)) / v (.inr 0) with hc3
  set c1 := (w (.inl 1) - c2 * v (.inl 1)) / v (.inr 0) with hc1
  set c0 := (w (.inl 0) - c1 * v (.inr 1) - c3 * v (.inl 1) - c2 * v (.inl 0)) / v (.inr 0)
    with hc0
  have hw' : w = c0 • vec4 (v (.inr 0)) 0 0 0 + c1 • vec4 (v (.inr 1)) (v (.inr 0)) 0 0 +
      c3 • vec4 (v (.inl 1)) 0 0 (-v (.inr 0)) + c2 • v := by
    refine vec4_eq ?_ ?_ ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl0]
      rw [hc0]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl1]
      rw [hc1]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inr0]
      rw [hc2]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inr1]
      rw [hc3]
      field_simp
      ring
  rw [hw']
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ e0) (S.smul_mem _ e1))
    (S.smul_mem _ e3)) (S.smul_mem _ hv)

section Card

variable [Finite K]

omit [Finite K] in
theorem card_spLine : Nat.card (spLine K) = Nat.card K :=
  (Nat.card_congr
    { toFun := fun x => (x : Fin 2 ⊕ Fin 2 → K) (.inl 0)
      invFun := fun c => ⟨vec4 c 0 0 0, rfl, rfl, rfl⟩
      left_inv := fun x => Subtype.ext (vec4_eq rfl x.2.1.symm x.2.2.1.symm x.2.2.2.symm)
      right_inv := fun _ => rfl })

omit [Finite K] in
theorem card_spPlane : Nat.card (spPlane K) = Nat.card K ^ 2 := by
  rw [sq, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => ((x : Fin 2 ⊕ Fin 2 → K) (.inl 0), (x : Fin 2 ⊕ Fin 2 → K) (.inl 1))
      invFun := fun c => ⟨vec4 c.1 c.2 0 0, rfl, rfl⟩
      left_inv := fun x => Subtype.ext (vec4_eq rfl rfl x.2.1.symm x.2.2.symm)
      right_inv := fun c => rfl }

omit [Finite K] in
theorem card_spHyp : Nat.card (spHyp K) = Nat.card K ^ 3 := by
  rw [pow_succ, sq, ← Nat.card_prod, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => (((x : Fin 2 ⊕ Fin 2 → K) (.inl 0), (x : Fin 2 ⊕ Fin 2 → K) (.inl 1)),
        (x : Fin 2 ⊕ Fin 2 → K) (.inr 1))
      invFun := fun c => ⟨vec4 c.1.1 c.1.2 0 c.2, rfl⟩
      left_inv := fun x => Subtype.ext (vec4_eq rfl rfl
        (show (x : Fin 2 ⊕ Fin 2 → K) (.inr 0) = 0 from x.2).symm rfl)
      right_inv := fun c => rfl }

omit [Finite K] in
theorem card_top4 : Nat.card (⊤ : Submodule K (Fin 2 ⊕ Fin 2 → K)) = Nat.card K ^ 4 := by
  rw [Nat.card_congr (Submodule.topEquiv (R := K) (M := Fin 2 ⊕ Fin 2 → K)).toEquiv, Nat.card_fun]
  simp

theorem eq_of_le_of_card_le_sp {S T : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hle : S ≤ T)
    (hc : Nat.card T ≤ Nat.card S) : S = T := by
  apply Submodule.toAddSubgroup_injective
  exact AddSubgroup.eq_of_le_of_card_ge hle hc

theorem eq_std_of_stable_sp {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hS : UStableSp S) :
    (Nat.card S = Nat.card K → S = spLine K) ∧
      (Nat.card S = Nat.card K ^ 2 → S = spPlane K) ∧
      (Nat.card S = Nat.card K ^ 3 → S = spHyp K) := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hlt : ∀ i j : ℕ, i < j → Nat.card K ^ i < Nat.card K ^ j := fun i j h =>
    Nat.pow_lt_pow_right hq h
  have h1 := hlt 1 2 (by norm_num)
  have h2 := hlt 2 3 (by norm_num)
  have h3 := hlt 3 4 (by norm_num)
  rw [pow_one] at h1
  have hle3 : Nat.card S < Nat.card K ^ 4 → S ≤ spHyp K := by
    intro hc v hv
    by_contra hv2
    rw [eq_top_of_stable_sp hS hv hv2, card_top4] at hc
    exact lt_irrefl _ hc
  have hle2 : Nat.card S < Nat.card K ^ 3 → S ≤ spPlane K := by
    intro hc v hv
    have hv2 : v (.inr 0) = 0 := hle3 (by omega) hv
    refine ⟨hv2, ?_⟩
    by_contra hv3
    have h : Nat.card (spHyp K) ≤ Nat.card S :=
      Nat.card_mono (Set.toFinite _) (spHyp_le_of_stable hS hv hv2 hv3)
    rw [card_spHyp] at h
    omega
  have hle1 : Nat.card S < Nat.card K ^ 2 → S ≤ spLine K := by
    intro hc v hv
    obtain ⟨hv2, hv3⟩ := hle2 (by omega) hv
    refine ⟨?_, hv2, hv3⟩
    by_contra hv1
    have h : Nat.card (spPlane K) ≤ Nat.card S :=
      Nat.card_mono (Set.toFinite _) (spPlane_le_of_stable hS hv hv2 hv3 hv1)
    rw [card_spPlane] at h
    omega
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · exact eq_of_le_of_card_le_sp (hle1 (by omega)) (by rw [card_spLine, hc])
  · exact eq_of_le_of_card_le_sp (hle2 (by omega)) (by rw [card_spPlane, hc])
  · exact eq_of_le_of_card_le_sp (hle3 (by omega)) (by rw [card_spHyp, hc])

end Card

theorem usp_mulVec {u : StatedSp 2 K} (hu : u ∈ Usp K) :
    ∃ x y z r : K, ∀ v, mat 2 K u *ᵥ v = mat 2 K (qSp x y z) *ᵥ (mat 2 K (nSp r) *ᵥ v) := by
  obtain ⟨x, y, z, r, rfl⟩ := hu
  exact ⟨x, y, z, r, fun v => by rw [map_mul, Matrix.mulVec_mulVec]⟩

theorem spLine_stable : UStableSp (spLine K) := by
  intro u hu v hv
  obtain ⟨x, y, z, r, h⟩ := usp_mulVec hu
  obtain ⟨h1, h2, h3⟩ := hv
  rw [h, nSp_mulVec, qSp_mulVec]
  refine ⟨?_, ?_, ?_⟩ <;> simp [vec4_apply_inl1, vec4_apply_inr0, vec4_apply_inr1, h1, h2, h3]

theorem spPlane_stable : UStableSp (spPlane K) := by
  intro u hu v hv
  obtain ⟨x, y, z, r, h⟩ := usp_mulVec hu
  obtain ⟨h2, h3⟩ := hv
  rw [h, nSp_mulVec, qSp_mulVec]
  refine ⟨?_, ?_⟩ <;> simp [vec4_apply_inr0, vec4_apply_inr1, h2, h3]

theorem spHyp_stable : UStableSp (spHyp K) := by
  intro u hu v hv
  obtain ⟨x, y, z, r, h⟩ := usp_mulVec hu
  have h2 : v (.inr 0) = 0 := hv
  rw [h, nSp_mulVec, qSp_mulVec]
  change vec4 _ _ _ _ (.inr 0) = 0
  simp [vec4_apply_inr0, h2]

end CFSG.Quasithin.Vol2.KGNat
