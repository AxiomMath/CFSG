module

public import CFSG.Quasithin.Background.RonanD35

public section

namespace CFSG.Quasithin.RonanD35

open CFSG.Quasithin CFSG.Open
open scoped Matrix

section Matrices

variable {d : ℕ} {K : Type} [Field K]

@[expose] def slTv (a φ : Fin d → K) : Matrix (Fin d) (Fin d) K :=
  1 + Matrix.vecMulVec a φ

theorem slTv_mulVec (a φ x : Fin d → K) : slTv a φ *ᵥ x = x + (φ ⬝ᵥ x) • a := by
  rw [slTv, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem sl_dot_single (φ : Fin d → K) (i : Fin d) : φ ⬝ᵥ Pi.single i 1 = φ i := by
  rw [dotProduct_single, mul_one]

theorem sl_vecMulVec_mul_eq_zero {a φ b ψ : Fin d → K} (h : φ ⬝ᵥ b = 0) :
    Matrix.vecMulVec a φ * Matrix.vecMulVec b ψ = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]

theorem sl_vecMulVec_mul_eq {a φ b ψ : Fin d → K} (h : φ ⬝ᵥ b = 1) :
    Matrix.vecMulVec a φ * Matrix.vecMulVec b ψ = Matrix.vecMulVec a ψ := by
  rw [Matrix.vecMulVec_mul_vecMulVec, h, one_smul]

theorem slTv_mul_slTv {a φ : Fin d → K} (h : φ ⬝ᵥ a = 0) (ψ : Fin d → K) :
    slTv a φ * slTv a ψ = slTv a (φ + ψ) := by
  rw [slTv, slTv, slTv, add_mul, one_mul, mul_add, mul_one, sl_vecMulVec_mul_eq_zero h, add_zero,
    Matrix.vecMulVec_add]
  abel

theorem sl_add_self [CharP K 2] (M : Matrix (Fin d) (Fin d) K) : M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (M i j)

theorem slTv_mul_self [CharP K 2] {a φ : Fin d → K} (h : φ ⬝ᵥ a = 0) :
    slTv a φ * slTv a φ = 1 := by
  have h2 : φ + φ = 0 := funext fun i => CharTwo.add_self_eq_zero (φ i)
  rw [slTv_mul_slTv h, h2, slTv, Matrix.vecMulVec_zero, add_zero]

theorem slTv_injective {i₀ : Fin d} {φ ψ : Fin d → K}
    (h : slTv (Pi.single i₀ 1) φ = slTv (Pi.single i₀ 1) ψ) : φ = ψ := by
  funext j
  have h1 := congrFun (congrFun h i₀) j
  simpa [slTv, Matrix.vecMulVec_apply] using h1

theorem sl_det_eq_one [CharP K 2] {M : Matrix (Fin d) (Fin d) K} (h : M * M = 1) : M.det = 1 := by
  have h1 : M.det * M.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  have h2 : (M.det + 1) * (M.det + 1) = 0 := by
    calc (M.det + 1) * (M.det + 1) = M.det * M.det + (M.det + M.det) + 1 := by ring
      _ = 0 := by rw [h1, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h3 : M.det + 1 = 0 := mul_self_eq_zero.mp h2
  calc M.det = M.det + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h3, zero_add]

theorem sl_mul_four [CharP K 2] {A B C : Matrix (Fin d) (Fin d) K} (hAA : A * A = 0)
    (hAB : A * B = C) (hBA : B * A = 0) (hBB : B * B = 0) (hCA : C * A = 0) (hCB : C * B = 0) :
    (1 + A) * (1 + B) * (1 + A) * (1 + B) = 1 + C := by
  have h1 : (1 + A) * (1 + B) = 1 + A + B + C := by
    simp only [mul_add, add_mul, one_mul, mul_one, hAB]
    abel
  have h2 : (1 + A + B + C) * (1 + A) = 1 + B + C + (A + A) := by
    simp only [mul_add, add_mul, one_mul, mul_one, hAA, hBA, hCA, add_zero]
    abel
  have h3 : (1 + B + C) * (1 + B) = 1 + C + (B + B) := by
    simp only [mul_add, add_mul, one_mul, mul_one, hBB, hCB, add_zero]
    abel
  rw [h1, h2, sl_add_self A, add_zero, h3, sl_add_self B, add_zero]

theorem sl_tutu [CharP K 2] {i₀ i : Fin d} (hi : i ≠ i₀) {ψ : Fin d → K} (hψ₀ : ψ i₀ = 0)
    (hψ : ψ i = 0) :
    slTv (Pi.single i₀ 1) (Pi.single i 1) * slTv (Pi.single i 1) ψ *
        slTv (Pi.single i₀ 1) (Pi.single i 1) * slTv (Pi.single i 1) ψ =
      slTv (Pi.single i₀ 1) ψ := by
  have hii : Pi.single i (1 : K) ⬝ᵥ Pi.single i 1 = 1 := by
    rw [sl_dot_single, Pi.single_eq_same]
  have hi0 : Pi.single i (1 : K) ⬝ᵥ Pi.single i₀ 1 = 0 := by
    rw [sl_dot_single, Pi.single_eq_of_ne hi.symm]
  have hψ0 : ψ ⬝ᵥ Pi.single i₀ 1 = 0 := by rw [sl_dot_single, hψ₀]
  have hψi : ψ ⬝ᵥ Pi.single i 1 = 0 := by rw [sl_dot_single, hψ]
  exact sl_mul_four (sl_vecMulVec_mul_eq_zero hi0) (sl_vecMulVec_mul_eq hii)
    (sl_vecMulVec_mul_eq_zero hψ0) (sl_vecMulVec_mul_eq_zero hψi) (sl_vecMulVec_mul_eq_zero hψ0)
    (sl_vecMulVec_mul_eq_zero hψi)

end Matrices

section Groups

variable {d : ℕ} {K : Type} [Field K]

theorem sl_ext {g h : ↥(StatedSL d K)}
    (e : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) : g = h :=
  Subtype.ext (Units.ext e)

theorem sl_coe_mul (g h : ↥(StatedSL d K)) :
    (((g * h : ↥(StatedSL d K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  rfl

theorem sl_coe_one :
    (((1 : ↥(StatedSL d K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 :=
  rfl

@[expose] def slG [CharP K 2] (a φ : Fin d → K) (h : φ ⬝ᵥ a = 0) : ↥(StatedSL d K) :=
  ⟨⟨slTv a φ, slTv a φ, slTv_mul_self h, slTv_mul_self h⟩,
    Subgroup.subset_closure (sl_det_eq_one (slTv_mul_self h))⟩

@[expose] def slA [CharP K 2] (i₀ : Fin d) : Subgroup ↥(StatedSL d K) where
  carrier := {g | ∃ φ : Fin d → K, φ i₀ = 0 ∧
    ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = slTv (Pi.single i₀ 1) φ}
  one_mem' := ⟨0, rfl, by rw [sl_coe_one, slTv, Matrix.vecMulVec_zero, add_zero]⟩
  mul_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    refine ⟨φ + ψ, by rw [Pi.add_apply, hφ, hψ, add_zero], ?_⟩
    rw [sl_coe_mul, ha, hb, slTv_mul_slTv (by rw [sl_dot_single, hφ])]
  inv_mem' := by
    rintro a ⟨φ, hφ, ha⟩
    have h2 : a * a = 1 :=
      sl_ext (by rw [sl_coe_mul, ha, slTv_mul_self (by rw [sl_dot_single, hφ]), sl_coe_one])
    rw [inv_eq_of_mul_eq_one_right h2]
    exact ⟨φ, hφ, ha⟩

theorem slA_mem_iff [CharP K 2] {i₀ : Fin d} {g : ↥(StatedSL d K)} :
    g ∈ slA i₀ ↔ ∃ φ : Fin d → K, φ i₀ = 0 ∧
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = slTv (Pi.single i₀ 1) φ :=
  Iff.rfl

theorem slA_comm [CharP K 2] (i₀ : Fin d) :
    ∀ a ∈ slA (K := K) i₀, ∀ b ∈ slA i₀, a * b = b * a := by
  rintro a ⟨φ, hφ, ha⟩ b ⟨ψ, hψ, hb⟩
  apply sl_ext
  rw [sl_coe_mul, sl_coe_mul, ha, hb, slTv_mul_slTv (by rw [sl_dot_single, hφ]),
    slTv_mul_slTv (by rw [sl_dot_single, hψ]), add_comm]

theorem slA_mul_self [CharP K 2] (i₀ : Fin d) : ∀ a ∈ slA (K := K) i₀, a * a = 1 := by
  rintro a ⟨φ, hφ, ha⟩
  apply sl_ext
  rw [sl_coe_mul, ha, slTv_mul_self (by rw [sl_dot_single, hφ]), sl_coe_one]

theorem slA_ne_bot [CharP K 2] {i₀ i₁ : Fin d} (h : i₁ ≠ i₀) : slA (K := K) i₀ ≠ ⊥ := by
  have hT : Pi.single i₁ (1 : K) ⬝ᵥ Pi.single i₀ 1 = 0 := by
    rw [sl_dot_single, Pi.single_eq_of_ne h.symm]
  intro hbot
  have h1 : slG (Pi.single i₀ 1) (Pi.single i₁ (1 : K)) hT ∈ slA i₀ :=
    ⟨Pi.single i₁ 1, Pi.single_eq_of_ne h.symm 1, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : slTv (Pi.single i₀ (1 : K)) (Pi.single i₁ 1) i₀ i₁ =
      (1 : Matrix (Fin d) (Fin d) K) i₀ i₁ :=
    congrArg (fun g : ↥(StatedSL d K) => ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i₀ i₁) h1
  rw [slTv, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_eq_same, Pi.single_eq_same,
    mul_one, Matrix.one_apply_ne h.symm, zero_add] at h2
  exact one_ne_zero h2

@[expose] def slP (i₀ : Fin d) : Subgroup (Multiplicative (Fin d → K)) where
  carrier := {x | ∀ j, j ≠ i₀ → Multiplicative.toAdd x j = 0}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb j hj => by
    rw [toAdd_mul, Pi.add_apply, ha j hj, hb j hj, add_zero]
  inv_mem' := fun {a} ha j hj => by
    rw [toAdd_inv, Pi.neg_apply, ha j hj, neg_zero]

theorem slP_mem_iff {i₀ : Fin d} {x : Multiplicative (Fin d → K)} :
    x ∈ slP i₀ ↔ ∀ j, j ≠ i₀ → Multiplicative.toAdd x j = 0 :=
  Iff.rfl

theorem sl_dot_eq_zero {i₀ : Fin d} {φ : Fin d → K} (hφ : φ i₀ = 0)
    {x : Multiplicative (Fin d → K)} (hx : x ∈ slP i₀) : φ ⬝ᵥ Multiplicative.toAdd x = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j = i₀
  · rw [hj, hφ, zero_mul]
  · rw [slP_mem_iff.mp hx j hj, mul_zero]

theorem sl_natAct_eq_self {g : ↥(StatedSL d K)} {a φ : Fin d → K}
    (hg : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = slTv a φ)
    {x : Multiplicative (Fin d → K)} (hx : φ ⬝ᵥ Multiplicative.toAdd x = 0) :
    natAct (StatedSL d K) g x = x := by
  rw [natAct, hg, slTv_mulVec, hx, zero_smul, add_zero, ofAdd_toAdd]

theorem sl_index_le [CharP K 2] [Finite K] (i₀ : Fin d) :
    (slP (K := K) i₀).index ≤ Nat.card ↥(slA (K := K) i₀) := by
  have hφ : ∀ x : Multiplicative (Fin d → K),
      Function.update (Multiplicative.toAdd x) i₀ 0 ⬝ᵥ Pi.single i₀ 1 = 0 := fun x => by
    rw [sl_dot_single, Function.update_self]
  refine index_le_of_injective (slP i₀)
    (fun x => (⟨slG (Pi.single i₀ 1) (Function.update (Multiplicative.toAdd x) i₀ 0) (hφ x),
      Function.update (Multiplicative.toAdd x) i₀ 0, Function.update_self _ _ _, rfl⟩,
      ⟨Multiplicative.ofAdd (Pi.single i₀ (Multiplicative.toAdd x i₀)),
        fun j hj => Pi.single_eq_of_ne hj _⟩)) ?_
  intro x y hxy
  have h1 : slTv (Pi.single i₀ (1 : K)) (Function.update (Multiplicative.toAdd x) i₀ 0) =
      slTv (Pi.single i₀ 1) (Function.update (Multiplicative.toAdd y) i₀ 0) :=
    congrArg (fun p : ↥(slA (K := K) i₀) × ↥(slP (K := K) i₀) =>
      ((((p.1 : ↥(slA (K := K) i₀)) : ↥(StatedSL d K)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)) hxy
  have h2 : (Pi.single i₀ (Multiplicative.toAdd x i₀) : Fin d → K) i₀ =
      (Pi.single i₀ (Multiplicative.toAdd y i₀) : Fin d → K) i₀ :=
    congrArg (fun p : ↥(slA (K := K) i₀) × ↥(slP (K := K) i₀) =>
      Multiplicative.toAdd ((p.2 : ↥(slP (K := K) i₀)) : Multiplicative (Fin d → K)) i₀) hxy
  rw [Pi.single_eq_same, Pi.single_eq_same] at h2
  have h3 := slTv_injective h1
  apply Multiplicative.toAdd.injective
  funext j
  by_cases hj : j = i₀
  · rw [hj]
    exact h2
  · have h4 := congrFun h3 j
    rwa [Function.update_of_ne hj, Function.update_of_ne hj] at h4

end Groups

section Covering

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V Z : Subgroup W} {d : ℕ} {K : Type}
  [Field K] [CharP K 2] {π : ↥(StatedSL d K) →* ↥L}

theorem sl_apply_eq_of_tv (hW : ∀ w : W, w * w = 1) (hLs : L ≤ stabSub V)
    (hZ : ∀ g ∈ L, ∀ z ∈ Z, g z = z) (β : ↥V →* Multiplicative (Fin d → K))
    (hβk : ∀ u : ↥V, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : ↥(StatedSL d K)) (u : ↥V) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ V),
      β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = natAct (StatedSL d K) γ (β u))
    {i₀ i : Fin d} (hi : i ≠ i₀) {ψ : Fin d → K} (hψ₀ : ψ i₀ = 0) (hψ : ψ i = 0)
    {g : ↥(StatedSL d K)}
    (hg : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = slTv (Pi.single i₀ 1) ψ)
    {v : ↥V} (hv : β v ∈ slP i₀) : ((π g : ↥L) : MulAut W) (v : W) = v := by
  have hT : Pi.single i (1 : K) ⬝ᵥ Pi.single i₀ 1 = 0 := by
    rw [sl_dot_single, Pi.single_eq_of_ne hi.symm]
  have hU : ψ ⬝ᵥ Pi.single i 1 = 0 := by rw [sl_dot_single, hψ]
  have hV : ∀ γ : ↥(StatedSL d K), ∀ x ∈ V, ((π γ : ↥L) : MulAut W) x ∈ V := fun γ x hx =>
    (mem_stabSub.mp (hLs (π γ).2) x).mpr hx
  have hfix : ∀ (γ : ↥(StatedSL d K)) (a φ : Fin d → K),
      ((γ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = slTv a φ → φ i₀ = 0 →
        β ⟨((π γ : ↥L) : MulAut W) (v : W), hV γ v v.2⟩ = β v := fun γ a φ hγ hφ =>
    (hβe γ v (hV γ v v.2)).trans (sl_natAct_eq_self hγ (sl_dot_eq_zero hφ hv))
  obtain ⟨T, hTm⟩ : ∃ T : ↥(StatedSL d K), ((T : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      slTv (Pi.single i₀ 1) (Pi.single i 1) :=
    ⟨slG (Pi.single i₀ 1) (Pi.single i 1) hT, rfl⟩
  obtain ⟨U, hUm⟩ : ∃ U : ↥(StatedSL d K), ((U : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      slTv (Pi.single i 1) ψ :=
    ⟨slG (Pi.single i 1) ψ hU, rfl⟩
  have hUU : U * U = 1 := sl_ext (by rw [sl_coe_mul, hUm, slTv_mul_self hU, sl_coe_one])
  have hg' : g = T * U * T * U⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hUU]
    apply sl_ext
    rw [hg, sl_coe_mul, sl_coe_mul, sl_coe_mul, hTm, hUm, sl_tutu hi hψ₀ hψ]
  have key := conj_pair_apply_eq_of_lift hW (hZ _ (π T).2) (hZ _ (π U).2) (hV T) (hV U) β hβk
    (hfix T _ _ hTm (Pi.single_eq_of_ne hi.symm 1)) (hfix U _ _ hUm hψ₀)
  rw [hg', map_mul, map_mul, map_mul, map_inv]
  exact key

theorem sl_apply_eq_of_mem_slA (hW : ∀ w : W, w * w = 1) (hLs : L ≤ stabSub V)
    (hZ : ∀ g ∈ L, ∀ z ∈ Z, g z = z) (β : ↥V →* Multiplicative (Fin d → K))
    (hβk : ∀ u : ↥V, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : ↥(StatedSL d K)) (u : ↥V) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ V),
      β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = natAct (StatedSL d K) γ (β u))
    {i₀ i₁ i₂ : Fin d} (h10 : i₁ ≠ i₀) (h20 : i₂ ≠ i₀) (h21 : i₂ ≠ i₁)
    {a : ↥(StatedSL d K)} (ha : a ∈ slA i₀) {v : ↥V} (hv : β v ∈ slP i₀) :
    ((π a : ↥L) : MulAut W) (v : W) = v := by
  obtain ⟨φ, hφ, hac⟩ := slA_mem_iff.mp ha
  have h1 : Function.update φ i₁ 0 i₀ = 0 := by rw [Function.update_of_ne h10.symm, hφ]
  have h2 : (Pi.single i₁ (φ i₁) : Fin d → K) i₀ = 0 := Pi.single_eq_of_ne h10.symm _
  have h1' : Function.update φ i₁ 0 ⬝ᵥ Pi.single i₀ 1 = 0 := by rw [sl_dot_single, h1]
  have h2' : (Pi.single i₁ (φ i₁) : Fin d → K) ⬝ᵥ Pi.single i₀ 1 = 0 := by
    rw [sl_dot_single, h2]
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ↥(StatedSL d K), ((a₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      slTv (Pi.single i₀ 1) (Function.update φ i₁ 0) :=
    ⟨slG (Pi.single i₀ 1) (Function.update φ i₁ 0) h1', rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : ↥(StatedSL d K), ((a₂ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      slTv (Pi.single i₀ 1) (Pi.single i₁ (φ i₁)) :=
    ⟨slG (Pi.single i₀ 1) (Pi.single i₁ (φ i₁)) h2', rfl⟩
  have hsplit : a = a₁ * a₂ := by
    apply sl_ext
    rw [sl_coe_mul, hac, ha₁, ha₂, slTv_mul_slTv h1']
    congr 1
    funext j
    by_cases hj : j = i₁
    · rw [hj, Pi.add_apply, Function.update_self, Pi.single_eq_same, zero_add]
    · rw [Pi.add_apply, Function.update_of_ne hj, Pi.single_eq_of_ne hj, add_zero]
  rw [hsplit, map_mul, Subgroup.coe_mul, MulAut.mul_apply,
    sl_apply_eq_of_tv hW hLs hZ β hβk hβe h20 h2 (Pi.single_eq_of_ne h21 _) ha₂ hv]
  exact sl_apply_eq_of_tv hW hLs hZ β hβk hβe h10 h1 (Function.update_self _ _ _) ha₁ hv

end Covering

theorem isFFModule_of_natSL {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} {V Z : Subgroup W} (hLs : L ≤ stabSub V)
    (hZ : ∀ g ∈ L, ∀ z ∈ Z, g z = z) {d : ℕ} (hd : 3 ≤ d) {K : Type} [Field K] [Finite K]
    [CharP K 2] {π : ↥(StatedSL d K) →* ↥L}
    (hπ : (FFModel.nat (StatedSL d K)).RealizesVia L V Z π) : IsFFModule (autSub L V) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_ambMap (D := FFModel.nat (StatedSL d K)) rfl hπ
  have hβs' : Function.Surjective β := fun m => hβs m (Subgroup.mem_top m)
  obtain ⟨i₀, i₁, i₂, h10, h20, h21⟩ : ∃ i₀ i₁ i₂ : Fin d, i₁ ≠ i₀ ∧ i₂ ≠ i₀ ∧ i₂ ≠ i₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp, by simp, by simp⟩
  refine isFFModule_of_realizesVia (FFModel.nat_faithful _) hLs hπ β hβs' (slA i₀)
    (slA_comm i₀) (slA_mul_self i₀) (slA_ne_bot h10) (slP i₀) (sl_index_le i₀) ?_
  intro v hv a ha
  exact sl_apply_eq_of_mem_slA hW hLs hZ β hβk hβe h10 h20 h21 ha hv

end CFSG.Quasithin.RonanD35
