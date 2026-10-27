module

public import CFSG.LocalAnalysis.WeakClosure81.TransvectionCenterCard

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Matrix

private theorem exists_ne_zero_dotProduct_eq_zero_pair {m : ℕ} {F : Type} [Field F]
    (hm : 3 ≤ m) (a a' : Fin m → F) :
    ∃ f : Fin m → F, f ≠ 0 ∧ f ⬝ᵥ a = 0 ∧ f ⬝ᵥ a' = 0 := by
  let L : (Fin m → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun f => ![f ⬝ᵥ a, f ⬝ᵥ a']
      map_add' := fun f g => by
        ext i; fin_cases i <;> simp [add_dotProduct]
      map_smul' := fun c f => by
        ext i; fin_cases i <;> simp [smul_dotProduct] }
  have hlt : Module.finrank F (Fin 2 → F) < Module.finrank F (Fin m → F) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  have hker : LinearMap.ker L ≠ ⊥ := L.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have h := LinearMap.mem_ker.mp hf
  refine ⟨f, hf0, ?_, ?_⟩
  · simpa [L] using congrFun h 0
  · simpa [L] using congrFun h 1

private theorem mk_transvectionCenterSL_ne_one {m : ℕ} {F : Type} [Field F] {a f : Fin m → F}
    (ha : a ≠ 0) (hf : f ≠ 0) (hfa : f ⬝ᵥ a = 0) :
    (QuotientGroup.mk (transvectionCenterSL a f hfa) : StatedProj (StatedSL m F)) ≠ 1 := by
  intro h
  have h1 : (QuotientGroup.mk (transvectionCenterSL a f hfa) : StatedProj (StatedSL m F)) =
      QuotientGroup.mk (1 : ↥(StatedSL m F)) := by
    rw [h]; rfl
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSL m F)
    (transvectionCenterSL a f hfa) 1).mp h1
  have hu' : (1 : Matrix (Fin m) (Fin m) F) =
      (1 + vecMulVec a f) * ((u : F) • (1 : Matrix (Fin m) (Fin m) F)) := by
    simpa [transvectionCenterSL_coe] using hu
  have hscal : (u : F) • a = a := by
    have h2 := congrArg (fun M : Matrix (Fin m) (Fin m) F => M *ᵥ a) hu'
    simp only [one_mulVec] at h2
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, one_mulVec] at h2
    rw [Matrix.mulVec_smul, transvectionCenterMatrix_mulVec a f hfa] at h2
    exact h2.symm
  have hu1 : (u : F) = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have := congrFun hscal i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have hi' : a i ≠ 0 := by simpa using hi
    exact mul_right_cancel₀ hi' (by simpa using this)
  rw [hu1, one_smul, Matrix.mul_one] at hu'
  have hz : vecMulVec a f = 0 := by
    have := hu'
    exact (add_eq_left.mp this.symm)
  exact CFSG.CGT.Timmesfeld75.vecMulVec_ne_zero_of ha hf hz

private theorem mem_transvectionCenterSet_iff_exists_mk {m : ℕ} {F : Type} [Field F]
    {a : Fin m → F} {x : StatedProj (StatedSL m F)} :
    x ∈ transvectionCenterSet m F a ↔
      ∃ (f : Fin m → F) (hf : f ⬝ᵥ a = 0),
        x = QuotientGroup.mk (transvectionCenterSL a f hf) := by
  constructor
  · rintro ⟨g, hgx, f, hf, hg⟩
    refine ⟨f, hf, ?_⟩
    have : g = transvectionCenterSL a f hf := by
      apply Subtype.ext
      apply Units.ext
      rw [hg, transvectionCenterSL_coe]
    rw [← hgx, this]
  · rintro ⟨f, hf, rfl⟩
    exact ⟨transvectionCenterSL a f hf, rfl, f, hf, transvectionCenterSL_coe a f hf⟩

private theorem mk_mul_mk_mul_mk_inv {m : ℕ} {F : Type} [Field F]
    (g : ↥(StatedSL m F)) {a f : Fin m → F} (hf : f ⬝ᵥ a = 0) :
    ∃ hf' : Matrix.vecMul f (((g⁻¹ : ↥(StatedSL m F)) : GL (Fin m) F) :
          Matrix (Fin m) (Fin m) F) ⬝ᵥ
        Matrix.mulVec ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) a = 0,
      (QuotientGroup.mk g : StatedProj (StatedSL m F)) *
          QuotientGroup.mk (transvectionCenterSL a f hf) *
          (QuotientGroup.mk g : StatedProj (StatedSL m F))⁻¹ =
        QuotientGroup.mk (transvectionCenterSL
          (Matrix.mulVec ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) a)
          (Matrix.vecMul f (((g⁻¹ : ↥(StatedSL m F)) : GL (Fin m) F) :
            Matrix (Fin m) (Fin m) F)) hf') := by
  set G : Matrix (Fin m) (Fin m) F := ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) with hG
  set G' : Matrix (Fin m) (Fin m) F :=
    (((g⁻¹ : ↥(StatedSL m F)) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) with hG'
  have hGG' : G * G' = 1 := by
    rw [hG, hG', ← Units.val_mul]
    simp
  have hG'G : G' * G = 1 := by
    rw [hG, hG', ← Units.val_mul]
    simp
  have hf' : Matrix.vecMul f G' ⬝ᵥ Matrix.mulVec G a = 0 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hG'G, Matrix.one_mulVec]
    exact hf
  refine ⟨hf', ?_⟩
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, transvectionCenterSL_coe]
  rw [← hG, ← hG', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hGG',
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private theorem mk_mul_mk_mul_mk_inv_mem {m : ℕ} {F : Type} [Field F]
    {a a' f g : Fin m → F} (hfa : f ⬝ᵥ a = 0) (hfa' : f ⬝ᵥ a' = 0) (hga' : g ⬝ᵥ a' = 0) :
    (QuotientGroup.mk (transvectionCenterSL a f hfa) : StatedProj (StatedSL m F)) *
        QuotientGroup.mk (transvectionCenterSL a' g hga') *
        (QuotientGroup.mk (transvectionCenterSL a f hfa) : StatedProj (StatedSL m F))⁻¹ ∈
      transvectionCenterSet m F a' := by
  have hg' : (g - (g ⬝ᵥ a) • f) ⬝ᵥ a' = 0 := by
    rw [sub_dotProduct, smul_dotProduct, hfa', hga']
    simp
  rw [mem_transvectionCenterSet_iff_exists_mk]
  refine ⟨g - (g ⬝ᵥ a) • f, hg', ?_⟩
  rw [mul_inv_eq_iff_eq_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, transvectionCenterSL_coe]
  have hga : (g - (g ⬝ᵥ a) • f) ⬝ᵥ a = g ⬝ᵥ a := by
    rw [sub_dotProduct, smul_dotProduct, hfa]
    simp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.vecMulVec_mul_vecMulVec, hfa, hfa', hga, Matrix.vecMulVec_sub, Matrix.vecMulVec_smul,
    Matrix.sub_mul, Matrix.smul_mul, Matrix.vecMulVec_zero, zero_smul, smul_zero, add_zero,
    sub_zero]
  abel

theorem kFacts_transvection_normalizer :
    ∀ (m : ℕ) (F : Type) [Field F] [Finite F] (a a' : Fin m → F),
      3 ≤ m → a ≠ 0 → a' ≠ 0 → (∀ c : F, a' ≠ c • a) →
        ∃ x ∈ transvectionCenterSet m F a, x ≠ 1 ∧
          ∀ y ∈ transvectionCenterSet m F a', x * y * x⁻¹ ∈ transvectionCenterSet m F a' := by
  intro m F _ _ a a' hm ha _ _
  obtain ⟨f, hf0, hfa, hfa'⟩ := exists_ne_zero_dotProduct_eq_zero_pair hm a a'
  refine ⟨QuotientGroup.mk (transvectionCenterSL a f hfa),
    (mem_transvectionCenterSet_iff_exists_mk).mpr ⟨f, hfa, rfl⟩,
    mk_transvectionCenterSL_ne_one ha hf0 hfa, ?_⟩
  intro y hy
  obtain ⟨g, hga', rfl⟩ := (mem_transvectionCenterSet_iff_exists_mk).mp hy
  exact mk_mul_mk_mul_mk_inv_mem hfa hfa' hga'

theorem kFacts_transvection_conj :
    ∀ (m : ℕ) (F : Type) [Field F] [Finite F] (a : Fin m → F)
        (γ : StatedProj (StatedSL m F)), 3 ≤ m → a ≠ 0 → ∃ a' : Fin m → F, a' ≠ 0 ∧
      {x | ∃ y ∈ transvectionCenterSet m F a, x = γ * y * γ⁻¹} = transvectionCenterSet m F a' := by
  intro m F _ _ a γ hm ha
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  set G : Matrix (Fin m) (Fin m) F := ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) with hG
  set G' : Matrix (Fin m) (Fin m) F :=
    (((g⁻¹ : ↥(StatedSL m F)) : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) with hG'
  have hGG' : G * G' = 1 := by
    rw [hG, hG', ← Units.val_mul]
    simp
  have hG'G : G' * G = 1 := by
    rw [hG, hG', ← Units.val_mul]
    simp
  refine ⟨Matrix.mulVec G a, ?_, ?_⟩
  · intro h0
    apply ha
    have := congrArg (fun v => Matrix.mulVec G' v) h0
    simpa [Matrix.mulVec_mulVec, hG'G] using this
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨f, hfa, rfl⟩ := (mem_transvectionCenterSet_iff_exists_mk).mp hy
      obtain ⟨hf', h⟩ := mk_mul_mk_mul_mk_inv g hfa
      rw [h]
      exact (mem_transvectionCenterSet_iff_exists_mk).mpr ⟨_, hf', rfl⟩
    · intro hx
      obtain ⟨f', hf'a, rfl⟩ := (mem_transvectionCenterSet_iff_exists_mk).mp hx
      have hfa : Matrix.vecMul f' G ⬝ᵥ a = 0 := by
        rw [← Matrix.dotProduct_mulVec]
        exact hf'a
      refine ⟨QuotientGroup.mk (transvectionCenterSL a (Matrix.vecMul f' G) hfa),
        (mem_transvectionCenterSet_iff_exists_mk).mpr ⟨_, hfa, rfl⟩, ?_⟩
      obtain ⟨hf'', h⟩ := mk_mul_mk_mul_mk_inv g hfa
      rw [h]
      congr 1
      apply Subtype.ext
      apply Units.ext
      simp only [transvectionCenterSL_coe]
      rw [← hG', Matrix.vecMul_vecMul, hGG', Matrix.vecMul_one]

end CFSG.LocalAnalysis.WeakClosure81
