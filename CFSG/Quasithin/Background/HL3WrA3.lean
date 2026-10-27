module

public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open Matrix
open scoped Matrix

abbrev uMat (x y w : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, x, y; 0, 1, w; 0, 0, 1]

theorem exists_uMat {u : ↥SL32} (hu : u ∈ U3) : ∃ x y w : ZMod 2, mat u = uMat x y w := by
  obtain ⟨h1, h2⟩ := hu
  obtain ⟨a10, a20, a00⟩ := (mulVec_e0_iff (mat u)).1 h1
  obtain ⟨-, b21, b22⟩ := (e2_vecMul_iff (mat u)).1 h2
  have hdet : (mat u).det = 1 := SL3Pair.mem_statedSL_iff.mp u.2
  simp [Matrix.det_fin_three, a10, a20, a00, b21, b22] at hdet
  have a11 : mat u 1 1 = 1 := by linear_combination hdet
  refine ⟨mat u 0 1, mat u 0 2, mat u 1 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a10, a20, a00, b21, b22, a11]

theorem uMat_E10 (x y w x' y' w' : ZMod 2) :
    uMat x y w * Matrix.single 1 0 1 * (uMat x' y' w')ᵀ =
      Matrix.single 1 0 1 + Matrix.single 0 0 x := by
  revert x y w x' y' w'
  decide

theorem uMat_E01 (x y w x' y' w' : ZMod 2) :
    uMat x y w * Matrix.single 0 1 1 * (uMat x' y' w')ᵀ =
      Matrix.single 0 1 1 + Matrix.single 0 0 x' := by
  revert x y w x' y' w'
  decide

theorem uMat_E20 (y w y' w' : ZMod 2) :
    uMat 0 y w * Matrix.single 2 0 1 * (uMat 0 y' w')ᵀ =
      Matrix.single 2 0 1 + (Matrix.single 1 0 w + Matrix.single 0 0 y) := by
  revert y w y' w'
  decide

theorem uMat_E02 (y w y' w' : ZMod 2) :
    uMat 0 y w * Matrix.single 0 2 1 * (uMat 0 y' w')ᵀ =
      Matrix.single 0 2 1 + (Matrix.single 0 1 w' + Matrix.single 0 0 y') := by
  revert y w y' w'
  decide

@[expose] noncomputable def T0 : Subgroup (MulAut WMod) :=
  (U3.prod U3).map rho ⊔ Subgroup.zpowers tau

theorem T0_le_norm : T0 ≤ norm :=
  sup_le ((Subgroup.map_le_range _ _).trans img_le_norm) (Subgroup.zpowers_le.mpr tau_mem_norm)

theorem T0_inf_img : T0 ⊓ img = (U3.prod U3).map rho :=
  sup_tau_inf_img (Subgroup.map_le_range _ _) (tau_mem_map_prod U3)

theorem mem_T0_cases {x : MulAut WMod} (hx : x ∈ T0) :
    (∃ u ∈ U3, ∃ v ∈ U3, x = rho (u, v)) ∨ (∃ u ∈ U3, ∃ v ∈ U3, x = rho (u, v) * tau) := by
  obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.1 (T0_le_norm hx)
  · left
    have h : rho g ∈ T0 ⊓ img := ⟨hx, rho_mem_img g⟩
    rw [T0_inf_img] at h
    obtain ⟨g', ⟨hu, hv⟩, hg'⟩ := h
    obtain rfl := rho_injective hg'
    exact ⟨g'.1, hu, g'.2, hv, rfl⟩
  · right
    have h : rho g ∈ T0 ⊓ img := by
      refine ⟨?_, rho_mem_img g⟩
      have e : rho g * tau * tau = rho g := by rw [mul_assoc, tau_mul_self, mul_one]
      rw [← e]
      exact T0.mul_mem hx (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau))
    rw [T0_inf_img] at h
    obtain ⟨g', ⟨hu, hv⟩, hg'⟩ := h
    obtain rfl := rho_injective hg'
    exact ⟨g'.1, hu, g'.2, hv, rfl⟩

abbrev eSym : WMod := Multiplicative.ofAdd (Matrix.single 1 0 1 + Matrix.single 0 1 1)

theorem T0_E10 {x : MulAut WMod} (hx : x ∈ T0) :
    x (eW 1 0) = eW 1 0 ∨ x (eW 1 0) = eW 1 0 * eW 0 0 ∨ x (eW 1 0) = eW 1 0 * eSym ∨
      x (eW 1 0) = eW 1 0 * (eW 0 0 * eSym) := by
  rcases mem_T0_cases hx with ⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩
  · obtain ⟨a, b, c, ha⟩ := exists_uMat hu
    obtain ⟨a', b', c', hb⟩ := exists_uMat hv
    have e : Multiplicative.toAdd (rho (u, v) (eW 1 0)) =
        Matrix.single 1 0 1 + Matrix.single 0 0 a := by
      change mat u * Matrix.single 1 0 1 * (mat v)ᵀ = _
      rw [ha, hb, uMat_E10]
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) a with h | h
    · left
      apply Multiplicative.toAdd.injective
      rw [e, h, Matrix.single_zero, add_zero]
      rfl
    · right; left
      apply Multiplicative.toAdd.injective
      rw [e, h]
      rfl
  · obtain ⟨a, b, c, ha⟩ := exists_uMat hu
    obtain ⟨a', b', c', hb⟩ := exists_uMat hv
    have e : Multiplicative.toAdd ((rho (u, v) * tau) (eW 1 0)) =
        Matrix.single 0 1 1 + Matrix.single 0 0 a' := by
      change mat u * (Matrix.single 1 0 (1 : ZMod 2))ᵀ * (mat v)ᵀ = _
      rw [Matrix.transpose_single, ha, hb, uMat_E01]
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) a' with h | h
    · right; right; left
      apply Multiplicative.toAdd.injective
      rw [e, h, Matrix.single_zero, add_zero]
      exact (by decide : (Matrix.single 0 1 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        Matrix.single 1 0 1 + (Matrix.single 1 0 1 + Matrix.single 0 1 1))
    · right; right; right
      apply Multiplicative.toAdd.injective
      rw [e, h]
      exact (by decide : (Matrix.single 0 1 1 + Matrix.single 0 0 1 :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        Matrix.single 1 0 1 + (Matrix.single 0 0 1 + (Matrix.single 1 0 1 + Matrix.single 0 1 1)))

theorem uMat_sym (x y w x' y' w' : ZMod 2) :
    uMat x y w * (Matrix.single 1 0 1 + Matrix.single 0 1 1) * (uMat x' y' w')ᵀ =
      Matrix.single 1 0 1 + Matrix.single 0 1 1 + Matrix.single 0 0 (x + x') := by
  revert x y w x' y' w'
  decide

theorem T0_eSym {x : MulAut WMod} (hx : x ∈ T0) :
    x eSym = eSym ∨ x eSym = eSym * eW 0 0 := by
  have key : ∀ u ∈ U3, ∀ v ∈ U3, rho (u, v) eSym = eSym ∨ rho (u, v) eSym = eSym * eW 0 0 := by
    intro u hu v hv
    obtain ⟨a, b, c, ha⟩ := exists_uMat hu
    obtain ⟨a', b', c', hb⟩ := exists_uMat hv
    have e : Multiplicative.toAdd (rho (u, v) eSym) =
        Matrix.single 1 0 1 + Matrix.single 0 1 1 + Matrix.single 0 0 (a + a') := by
      change mat u * (Matrix.single 1 0 1 + Matrix.single 0 1 1) * (mat v)ᵀ = _
      rw [ha, hb, uMat_sym]
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (a + a') with h | h
    · left
      apply Multiplicative.toAdd.injective
      rw [e, h, Matrix.single_zero, add_zero]
      rfl
    · right
      apply Multiplicative.toAdd.injective
      rw [e, h]
      rfl
  rcases mem_T0_cases hx with ⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩
  · exact key u hu v hv
  · have ht : tau eSym = eSym := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_tau]
      exact (by decide : (Matrix.single 1 0 1 + Matrix.single 0 1 1 :
        Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = Matrix.single 1 0 1 + Matrix.single 0 1 1)
    change rho (u, v) (tau eSym) = eSym ∨ rho (u, v) (tau eSym) = eSym * eW 0 0
    rw [ht]
    exact key u hu v hv

theorem mem_R1R1_of_fix {x : MulAut WMod} (hx : x ∈ T0) (h1 : x (eW 1 0) = eW 1 0)
    (h2 : x eSym = eSym) : x ∈ (R1.prod R1).map rho := by
  rcases mem_T0_cases hx with ⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩
  · obtain ⟨a, b, c, ha⟩ := exists_uMat hu
    obtain ⟨a', b', c', hb⟩ := exists_uMat hv
    have e1 : Matrix.single 1 0 1 + Matrix.single 0 0 a =
        (Matrix.single 1 0 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      have h := congrArg Multiplicative.toAdd h1
      change mat u * Matrix.single 1 0 1 * (mat v)ᵀ = _ at h
      rw [ha, hb, uMat_E10] at h
      exact h
    have e2 : Matrix.single 1 0 1 + Matrix.single 0 1 1 + Matrix.single 0 0 (a + a') =
        (Matrix.single 1 0 1 + Matrix.single 0 1 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      have h := congrArg Multiplicative.toAdd h2
      change mat u * (Matrix.single 1 0 1 + Matrix.single 0 1 1) * (mat v)ᵀ = _ at h
      rw [ha, hb, uMat_sym] at h
      exact h
    have ha0 : a = 0 := by
      have h := congrFun (congrFun e1 0) 0
      simpa using h
    have ha0' : a + a' = 0 := by
      have h := congrFun (congrFun e2 0) 0
      simpa using h
    have ha'0 : a' = 0 := by rw [ha0, zero_add] at ha0'; exact ha0'
    refine ⟨(u, v), ⟨⟨b, c, ?_⟩, ⟨b', c', ?_⟩⟩, rfl⟩
    · rw [ha, ha0]
    · rw [hb, ha'0]
  · exfalso
    obtain ⟨a, b, c, ha⟩ := exists_uMat hu
    obtain ⟨a', b', c', hb⟩ := exists_uMat hv
    have h := congrArg Multiplicative.toAdd h1
    change mat u * (Matrix.single 1 0 (1 : ZMod 2))ᵀ * (mat v)ᵀ = _ at h
    rw [Matrix.transpose_single, ha, hb, uMat_E01] at h
    have h' := congrFun (congrFun h 0) 1
    simp at h'

theorem R1R1_E20_E02 {x : MulAut WMod} (hx : x ∈ (R1.prod R1).map rho) :
    (x (eW 2 0) = eW 2 0 ∨ x (eW 2 0) = eW 2 0 * eW 1 0 ∨ x (eW 2 0) = eW 2 0 * eW 0 0 ∨
      x (eW 2 0) = eW 2 0 * (eW 1 0 * eW 0 0)) ∧
    (x (eW 0 2) = eW 0 2 ∨ x (eW 0 2) = eW 0 2 * eW 0 1 ∨ x (eW 0 2) = eW 0 2 * eW 0 0 ∨
      x (eW 0 2) = eW 0 2 * (eW 0 1 * eW 0 0)) := by
  obtain ⟨⟨u, v⟩, ⟨⟨y, w, hu⟩, ⟨y', w', hv⟩⟩, rfl⟩ := hx
  have hu' : mat u = uMat 0 y w := hu
  have hv' : mat v = uMat 0 y' w' := hv
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  constructor
  · have e : Multiplicative.toAdd (rho (u, v) (eW 2 0)) =
        Matrix.single 2 0 1 + (Matrix.single 1 0 w + Matrix.single 0 0 y) := by
      change mat u * Matrix.single 2 0 1 * (mat v)ᵀ = _
      rw [hu', hv', uMat_E20]
    rcases h01 w with hw | hw <;> rcases h01 y with hy | hy
    · left
      apply Multiplicative.toAdd.injective
      rw [e, hw, hy, Matrix.single_zero, Matrix.single_zero, add_zero, add_zero]
      rfl
    · right; right; left
      apply Multiplicative.toAdd.injective
      rw [e, hw, hy, Matrix.single_zero, zero_add]
      rfl
    · right; left
      apply Multiplicative.toAdd.injective
      rw [e, hw, hy, Matrix.single_zero, add_zero]
      rfl
    · right; right; right
      apply Multiplicative.toAdd.injective
      rw [e, hw, hy]
      rfl
  · have e : Multiplicative.toAdd (rho (u, v) (eW 0 2)) =
        Matrix.single 0 2 1 + (Matrix.single 0 1 w' + Matrix.single 0 0 y') := by
      change mat u * Matrix.single 0 2 1 * (mat v)ᵀ = _
      rw [hu', hv', uMat_E02]
    rcases h01 w' with hw | hw <;> rcases h01 y' with hy | hy
    · left
      apply Multiplicative.toAdd.injective
      rw [e, hw, hy, Matrix.single_zero, Matrix.single_zero, add_zero, add_zero]
      rfl
    · right; right; left
      apply Multiplicative.toAdd.injective
      rw [e, hw, hy, Matrix.single_zero, zero_add]
      rfl
    · right; left
      apply Multiplicative.toAdd.injective
      rw [e, hw, hy, Matrix.single_zero, add_zero]
      rfl
    · right; right; right
      apply Multiplicative.toAdd.injective
      rw [e, hw, hy]
      rfl

theorem eq_one_of_R1R1_fix {x : MulAut WMod} (hx : x ∈ (R1.prod R1).map rho)
    (h1 : x (eW 2 0) = eW 2 0) (h2 : x (eW 0 2) = eW 0 2) : x = 1 := by
  obtain ⟨⟨u, v⟩, ⟨⟨y, w, hu⟩, ⟨y', w', hv⟩⟩, rfl⟩ := hx
  have hu' : mat u = uMat 0 y w := hu
  have hv' : mat v = uMat 0 y' w' := hv
  have e1 : Matrix.single 2 0 1 + (Matrix.single 1 0 w + Matrix.single 0 0 y) =
      (Matrix.single 2 0 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    have h := congrArg Multiplicative.toAdd h1
    change mat u * Matrix.single 2 0 1 * (mat v)ᵀ = _ at h
    rw [hu', hv', uMat_E20] at h
    exact h
  have e2 : Matrix.single 0 2 1 + (Matrix.single 0 1 w' + Matrix.single 0 0 y') =
      (Matrix.single 0 2 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    have h := congrArg Multiplicative.toAdd h2
    change mat u * Matrix.single 0 2 1 * (mat v)ᵀ = _ at h
    rw [hu', hv', uMat_E02] at h
    exact h
  have hw : w = 0 := by simpa using congrFun (congrFun e1 1) 0
  have hy : y = 0 := by simpa using congrFun (congrFun e1 0) 0
  have hw' : w' = 0 := by simpa using congrFun (congrFun e2 0) 1
  have hy' : y' = 0 := by simpa using congrFun (congrFun e2 0) 0
  have hu1 : u = 1 := eq_of_mat_eq (by rw [hu', hw, hy, mat_one]; decide)
  have hv1 : v = 1 := eq_of_mat_eq (by rw [hv', hw', hy', mat_one]; decide)
  rw [hu1, hv1]
  exact map_one rho

theorem mQuot_le_of_relIndex_le {X : Type*} [Group X] [Finite X] {A B : Subgroup X}
    (hA : IsPGroup 2 A) {k : ℕ} (h : B.relIndex A ≤ 2 ^ k) : E3.mQuot A B ≤ k := by
  rw [E3.relIndex_eq_two_pow hA] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem relIndex_stabilizer_le_four {W : Type*} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {D e₁ e₂ : W}
    (hAD : ∀ y ∈ A, y D = D ∨ y D = D * e₁ ∨ y D = D * e₂ ∨ y D = D * (e₁ * e₂)) :
    (A ⊓ MulAction.stabilizer (MulAut W) D).relIndex A ≤ 4 := by
  have h1 : (A ⊓ MulAction.stabilizer (MulAut W) D).subgroupOf A =
      MulAction.stabilizer ↥A D := by
    ext c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
  rw [Subgroup.relIndex, h1, MulAction.index_stabilizer]
  calc (MulAction.orbit ↥A D).ncard ≤ ({D, D * e₁, D * e₂, D * (e₁ * e₂)} : Set W).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨c, rfl⟩
        rcases hAD c c.2 with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    _ ≤ 4 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
        refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
        rw [Set.ncard_singleton]

theorem not_mem_aSet_three_of_orbit {W : Type*} [CommGroup W] [Finite W]
    {Y A : Subgroup (MulAut W)} (hA2 : IsPGroup 2 A) {D e₁ e₂ : W}
    (hAD : ∀ y ∈ A, y D = D ∨ y D = D * e₁ ∨ y D = D * e₂ ∨ y D = D * (e₁ * e₂))
    {a : MulAut W} (ha : a ∈ A) (haD : a D ≠ D) : A ∉ E3.aSet 3 Y := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  rintro ⟨-, -, -, hfix⟩
  have hidx := relIndex_stabilizer_le_four hAD
  have hm : E3.mQuot A (A ⊓ MulAction.stabilizer (MulAut W) D) < 3 :=
    lt_of_le_of_lt (mQuot_le_of_relIndex_le hA2 (k := 2) (hidx.trans (by norm_num)))
      (by norm_num)
  have h := hfix _ inf_le_left hm
  have hDB : D ∈ fixV (A ⊓ MulAction.stabilizer (MulAut W) D) := fun y hy => hy.2
  rw [h] at hDB
  exact haD (hDB a ha)

theorem aSet_three_T0_eq_empty : E3.aSet 3 T0 = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  obtain ⟨hAT, hA1, hA2, -⟩ := id hA
  have hAp : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by rw [pow_one]; exact hA2.2 a a.2)⟩
  by_cases h10 : ∃ a ∈ A, a (eW 1 0) ≠ eW 1 0
  · obtain ⟨a, ha, haD⟩ := h10
    exact not_mem_aSet_three_of_orbit hAp (fun y hy => T0_E10 (hAT hy)) ha haD hA
  push Not at h10
  by_cases hs : ∃ a ∈ A, a eSym ≠ eSym
  · obtain ⟨a, ha, haD⟩ := hs
    refine not_mem_aSet_three_of_orbit (e₁ := eW 0 0) (e₂ := 1) hAp (fun y hy => ?_) ha haD hA
    rcases T0_eSym (hAT hy) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  push Not at hs
  have hR : A ≤ (R1.prod R1).map rho := fun a ha => mem_R1R1_of_fix (hAT ha) (h10 a ha) (hs a ha)
  by_cases h20 : ∃ a ∈ A, a (eW 2 0) ≠ eW 2 0
  · obtain ⟨a, ha, haD⟩ := h20
    exact not_mem_aSet_three_of_orbit hAp (fun y hy => (R1R1_E20_E02 (hR hy)).1) ha haD hA
  push Not at h20
  by_cases h02 : ∃ a ∈ A, a (eW 0 2) ≠ eW 0 2
  · obtain ⟨a, ha, haD⟩ := h02
    exact not_mem_aSet_three_of_orbit hAp (fun y hy => (R1R1_E20_E02 (hR hy)).2) ha haD hA
  push Not at h02
  apply hA1
  exact eq_bot_iff.mpr fun a ha =>
    (Subgroup.mem_bot).mpr (eq_one_of_R1R1_fix (hR ha) (h20 a ha) (h02 a ha))

theorem normalizer_U3_matrix : ∀ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g.det ≠ 0 →
    (∀ x y w : ZMod 2, ∃ x' y' w' : ZMod 2, g * uMat x y w = uMat x' y' w' * g) →
    ∃ a b c : ZMod 2, g = uMat a b c := by
  decide +kernel

theorem det_uMat (x y w : ZMod 2) : (uMat x y w).det ≠ 0 := by
  revert x y w
  decide

theorem uMat_mem_U3 (x y w : ZMod 2) : slOfMat (uMat x y w) (det_uMat x y w) ∈ U3 := by
  have h1 : ∀ x y w : ZMod 2, uMat x y w *ᵥ e0 = e0 := by decide
  have h2 : ∀ x y w : ZMod 2, e2 ᵥ* uMat x y w = e2 := by decide
  exact ⟨h1 x y w, h2 x y w⟩

theorem mem_U3_of_normalizes {g : ↥SL32} (hg : ∀ u ∈ U3, g * u * g⁻¹ ∈ U3) : g ∈ U3 := by
  have hdet : (mat g).det ≠ 0 := by
    rw [SL3Pair.mem_statedSL_iff.mp g.2]
    exact one_ne_zero
  have key : ∀ x y w : ZMod 2, ∃ x' y' w' : ZMod 2,
      mat g * uMat x y w = uMat x' y' w' * mat g := by
    intro x y w
    obtain ⟨x', y', w', h⟩ := exists_uMat (hg _ (uMat_mem_U3 x y w))
    refine ⟨x', y', w', ?_⟩
    rw [← h, mat_mul, mat_mul, Matrix.mul_assoc, mat_inv_mul, Matrix.mul_one, mat_slOfMat]
  obtain ⟨a, b, c, h⟩ := normalizer_U3_matrix (mat g) hdet key
  have hg' : g = slOfMat (uMat a b c) (det_uMat a b c) := eq_of_mat_eq (by rw [mat_slOfMat, h])
  rw [hg']
  exact uMat_mem_U3 a b c

theorem le_T0_of_isPGroup {Y : Subgroup (MulAut WMod)} (hYn : Y ≤ norm) (hY2 : IsPGroup 2 Y)
    (hUY : (U3.prod U3).map rho ≤ Y) : Y ≤ T0 := by
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S0 := (U3.prod U3).map rho with hS0
  have hS0img : S0 ≤ img := Subgroup.map_le_range _ _
  have hS0card : Nat.card ↥S0 = 2 ^ 6 := by
    rw [hS0, Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_U3]
    norm_num
  have hYimg : Y ⊓ img = S0 := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (le_inf hUY hS0img) ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hY2.to_le (inf_le_left : Y ⊓ img ≤ Y))
    have hdvd : Nat.card ↥(Y ⊓ img) ∣ 2 ^ 6 * 441 := by
      rw [show (2 ^ 6 * 441 : ℕ) = 168 ^ 2 by norm_num, ← card_img]
      exact Subgroup.card_dvd_of_le inf_le_right
    rw [hk] at hdvd ⊢
    rw [hS0card]
    have hcop : Nat.Coprime (2 ^ k) 441 := Nat.Coprime.pow_left k (by norm_num)
    exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)
  intro y hy
  have hyN : y ∈ Subgroup.normalizer (S0 : Set (MulAut WMod)) := by
    rw [← hYimg]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hYn hy⟩
  have hρ : ∀ g : ↥SL32 × ↥SL32, rho g ∈ Subgroup.normalizer (S0 : Set (MulAut WMod)) →
      rho g ∈ T0 := by
    intro g hg
    have h1 : ∀ u ∈ U3, g.1 * u * g.1⁻¹ ∈ U3 := by
      intro u hu
      have hm : rho g * rho (u, 1) * (rho g)⁻¹ ∈ S0 :=
        (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨(u, 1), ⟨hu, U3.one_mem⟩, rfl⟩
      obtain ⟨g', ⟨hg1, -⟩, hg'⟩ := hm
      rw [← map_inv, ← map_mul, ← map_mul] at hg'
      have he := congrArg Prod.fst (rho_injective hg')
      have e2 : (g * (u, 1) * g⁻¹).1 = g.1 * u * g.1⁻¹ := rfl
      rw [← e2, ← he]
      exact hg1
    have h2 : ∀ u ∈ U3, g.2 * u * g.2⁻¹ ∈ U3 := by
      intro u hu
      have hm : rho g * rho (1, u) * (rho g)⁻¹ ∈ S0 :=
        (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨(1, u), ⟨U3.one_mem, hu⟩, rfl⟩
      obtain ⟨g', ⟨-, hg2⟩, hg'⟩ := hm
      rw [← map_inv, ← map_mul, ← map_mul] at hg'
      have he := congrArg Prod.snd (rho_injective hg')
      have e2 : (g * (1, u) * g⁻¹).2 = g.2 * u * g.2⁻¹ := rfl
      rw [← e2, ← he]
      exact hg2
    have hg1 := mem_U3_of_normalizes h1
    have hg2 := mem_U3_of_normalizes h2
    exact Subgroup.mem_sup_left ⟨g, ⟨hg1, hg2⟩, rfl⟩
  obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.mp (hYn hy)
  · exact hρ g hyN
  · have htN : tau ∈ Subgroup.normalizer (S0 : Set (MulAut WMod)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have := tau_mem_map_prod U3 h hh
        rw [tau_inv]
        exact this
      · intro hh
        have := tau_mem_map_prod U3 _ hh
        have e : tau * (tau * h * tau⁻¹) * tau = h := by
          rw [tau_inv]
          calc tau * (tau * h * tau) * tau = (tau * tau) * h * (tau * tau) := by group
            _ = h := by rw [tau_mul_self, one_mul, mul_one]
        rwa [e] at this
    have hg : rho g ∈ Subgroup.normalizer (S0 : Set (MulAut WMod)) := by
      have e : rho g = rho g * tau * tau⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ htN)
    exact T0.mul_mem (hρ g hg) (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau))

theorem aSet_three_eq_empty_of {Y : Subgroup (MulAut WMod)} (hYn : Y ≤ norm)
    (hY2 : IsPGroup 2 Y) (hUY : (U3.prod U3).map rho ≤ Y) : E3.aSet 3 Y = ∅ := by
  have hYT := le_T0_of_isPGroup hYn hY2 hUY
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  have hA' : A ∈ E3.aSet 3 T0 := ⟨hA.1.trans hYT, hA.2⟩
  rw [aSet_three_T0_eq_empty] at hA'
  exact hA'

end L3Wr

end H

end CFSG.Quasithin
