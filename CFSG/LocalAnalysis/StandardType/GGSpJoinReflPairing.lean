module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra

public section

namespace CFSG.StandardType.SpJoinRefl



section Pairing

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

private theorem pr_ggCoxA_two (R : Type*) [CommRing R] (t : R) :
    ggCoxA R ((2 : ℕ) : ℤ) t = 1 := by
  simp only [ggCoxA]
  norm_num

private theorem pr_ggCoxA_three (R : Type*) [CommRing R] (t : R) :
    ggCoxA R ((3 : ℕ) : ℤ) t = t + 1 := by
  simp only [ggCoxA]
  norm_num

private theorem pr_cartan_off_diag {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) (hsl : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1)
    {i j : Γ} (hij : i ≠ j) :
    (M i j = 2 ∧ C i j = 0) ∨ (M i j = 3 ∧ C i j = -1) := by
  rcases hC.entries hij with ⟨hM, h1, -⟩ | ⟨hM, h1, -⟩ | ⟨hM, h1⟩ | ⟨hM, h1⟩
  · exact Or.inl ⟨hM, h1⟩
  · exact Or.inr ⟨hM, h1⟩
  · exfalso
    rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩
    · rcases hsl j i hij.symm with h0 | h0 <;> rw [h0] at h1b <;> norm_num at h1b
    · rcases hsl i j hij with h0 | h0 <;> rw [h0] at h1a <;> norm_num at h1a
  · exfalso
    rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩
    · rcases hsl j i hij.symm with h0 | h0 <;> rw [h0] at h1b <;> norm_num at h1b
    · rcases hsl i j hij with h0 | h0 <;> rw [h0] at h1a <;> norm_num at h1a

theorem exists_pairing_of_weylOfType [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {ι : Type} {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType p M A)
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) :
    ∃ (e : M.Group ≃* ↥A) (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
      (hα : ∀ i, α i (h i) = 2),
      (∀ i, ggLin (p := p) ιV ((e (M.simple i) : ↥A) : MulAut ↥Bs) = Module.reflection (hα i)) ∧
      (∀ i j, i ≠ j → M i j = 2 → α i (h j) = 0 ∧ α j (h i) = 0) ∧
      (∀ i j, i ≠ j → M i j = 3 → α i (h j) * α j (h i) = 1) := by
  classical
  obtain ⟨e, he⟩ := hW
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  let φ : ι → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  let Φ : M.Group →* MulAut ↥Bs := (Subgroup.subtype A).comp e.toMonoidHom
  have hφeq : ∀ i, φ i = Φ (M.simple i) := fun _ => rfl
  have hφind : ∀ i, φ i ∈ ggInduced ⊤ Bs := fun i => hind _ (SetLike.coe_mem _)
  choose x f hfx hlinapply using fun i => exists_of_ggIsReflection ιV (he i)
  have hlin : ∀ i, ggLin (p := p) ιV (φ i) = Module.reflection (hfx i) :=
    fun i => ggLin_eq_reflection ιV (hfx i) (hlinapply i)
  have hΦinj : Function.Injective Φ :=
    fun a b h => e.injective (Subtype.coe_injective h)
  have hφinj : Function.Injective φ := by
    intro i j hij
    have h1 : e (M.simple i) = e (M.simple j) := Subtype.ext hij
    have h2 : M.simple i = M.simple j := e.injective h1
    exact CoxeterSystem.simple_injective M.toCoxeterSystem (by
      rw [CoxeterMatrix.toCoxeterSystem_simple]; exact h2)
  have horder : ∀ i j, orderOf (M.simple i * M.simple j) = M i j := by
    intro i j
    have h := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
    rwa [CoxeterMatrix.toCoxeterSystem_simple] at h
  have hpow : ∀ i j, (φ i * φ j) ^ (M i j) = 1 := by
    intro i j
    have hm : (M.simple i * M.simple j) ^ (M i j) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [horder i j])
    have h1 : φ i * φ j = Φ (M.simple i * M.simple j) := by
      rw [map_mul, hφeq i, hφeq j]
    rw [h1, ← map_pow, hm, map_one]
  refine ⟨e, x, f, hfx, hlin, ?_, ?_⟩
  · intro i j hij hM2
    have hpow2 : (φ i * φ j) ^ 2 = 1 := by rw [← hM2]; exact hpow i j
    have hcross : f i (x j) = 0 → f j (x i) = 0 := fun h =>
      ggCross_eq_zero_of_noTransvection hp2 hNT ιV (hφind i) (hφind j)
        (hfx i) (hfx j) (hlin i) (hlin j) h
    have hcross' : f j (x i) = 0 → f i (x j) = 0 := fun h =>
      ggCross_eq_zero_of_noTransvection hp2 hNT ιV (hφind j) (hφind i)
        (hfx j) (hfx i) (hlin j) (hlin i) h
    by_cases hu : f i (x j) = 0
    · exact ⟨hu, hcross hu⟩
    · by_cases hv : f j (x i) = 0
      · exact ⟨hcross' hv, hv⟩
      · exfalso
        have hcrit := (ggReflection_mul_pow_eq_one_iff hp2 hNT ιV (hφind i) (hφind j)
          (hφinj.ne hij) (hfx i) (hfx j) (hlin i) (hlin j) hu hv 2).mp hpow2
        have h0 := hcrit.1
        rw [pr_ggCoxA_two] at h0
        exact one_ne_zero h0
  · intro i j hij hM3
    have hpow3 : (φ i * φ j) ^ 3 = 1 := by rw [← hM3]; exact hpow i j
    have hpow2_of : f i (x j) = 0 → f j (x i) = 0 → (φ i * φ j) ^ 2 = 1 := by
      intro h0 hv0
      apply ggLin_injective (p := p) ιV
      rw [map_pow, map_mul, hlin i, hlin j, map_one]
      exact reflection_mul_reflection_pow_two (hfx i) (hfx j) h0 hv0
    have hneq : φ i * φ j ≠ 1 := by
      intro h1
      have h2 : M.simple i * M.simple j = 1 := by
        apply hΦinj
        rw [map_mul, map_one]
        simpa [hφeq] using h1
      have h3 := horder i j
      rw [h2, orderOf_one] at h3
      omega
    have hne_of_two : (φ i * φ j) ^ 2 = 1 → False := by
      intro h2
      apply hneq
      have h := hpow3
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, h2, one_mul] at h
      exact h
    have hcross : f i (x j) = 0 → f j (x i) = 0 := fun h =>
      ggCross_eq_zero_of_noTransvection hp2 hNT ιV (hφind i) (hφind j)
        (hfx i) (hfx j) (hlin i) (hlin j) h
    have hcross' : f j (x i) = 0 → f i (x j) = 0 := fun h =>
      ggCross_eq_zero_of_noTransvection hp2 hNT ιV (hφind j) (hφind i)
        (hfx j) (hfx i) (hlin j) (hlin i) h
    have hu : f i (x j) ≠ 0 := fun h => hne_of_two (hpow2_of h (hcross h))
    have hv : f j (x i) ≠ 0 := fun h => hne_of_two (hpow2_of (hcross' h) h)
    have hcrit := (ggReflection_mul_pow_eq_one_iff hp2 hNT ιV (hφind i) (hφind j)
      (hφinj.ne hij) (hfx i) (hfx j) (hlin i) (hlin j) hu hv 3).mp hpow3
    have h0 := hcrit.1
    rw [pr_ggCoxA_three] at h0
    linear_combination h0

theorem exists_cartan_pairing_of_weylOfType [Finite G] (hp2 : p ≠ 2)
    (hNT : GGNoTransvection p Bs) {ι : Type} [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hC : GGIntCartan M C) (hsl : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1)
    (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hpar : ∀ i j, i ≠ j → (C i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType p M A) (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) :
    ∃ (e : M.Group ≃* ↥A) (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
      (hα : ∀ i, α i (h i) = 2),
      (∀ i, ggLin (p := p) ιV ((e (M.simple i) : ↥A) : MulAut ↥Bs) = Module.reflection (hα i)) ∧
      ∀ i j, α i (h j) = (C i j : ZMod p) := by
  classical
  obtain ⟨e, h, α, hα, hrefl, h2, h3⟩ :=
    exists_pairing_of_weylOfType (p := p) hp2 hNT hW hind ιV
  let P : ι → ι → ZMod p := fun i j => α i (h j)
  have hP0 : ∀ i j, i ≠ j → C i j = 0 → P i j = 0 := by
    intro i j hij hCij
    rcases pr_cartan_off_diag hC hsl hij with ⟨hM, -⟩ | ⟨hM, hCij'⟩
    · exact (h2 i j hij hM).1
    · rw [hCij] at hCij'; norm_num at hCij'
  have hP1 : ∀ i j, C i j = -1 → P i j * P j i = 1 := by
    intro i j hCij
    by_cases hij : i = j
    · subst hij
      rw [hC.1] at hCij
      norm_num at hCij
    · rcases pr_cartan_off_diag hC hsl hij with ⟨hM, hCij'⟩ | ⟨hM, -⟩
      · rw [hCij] at hCij'; norm_num at hCij'
      · exact h3 i j hij hM
  obtain ⟨c, hc0, hc⟩ :=
    exists_unit_gauge_of_tree (K := ZMod p) (fun i j => C i j) P par root depth hsl hP0 hP1 hpar
      hdepth
  have hα' : ∀ i, ((c i)⁻¹ • α i) (c i • h i) = 2 := by
    intro i
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (hc0 i), one_mul]
    exact hα i
  have hrefl' : ∀ i, ggLin (p := p) ιV ((e (M.simple i) : ↥A) : MulAut ↥Bs) =
      Module.reflection (hα' i) := by
    intro i
    rw [hrefl i]
    ext v
    rw [Module.reflection_apply, Module.reflection_apply]
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [smul_smul]
    congr 1
    rw [mul_assoc, mul_comm ((α i) v) (c i), ← mul_assoc, inv_mul_cancel₀ (hc0 i), one_mul]
  refine ⟨e, fun j => c j • h j, fun i => (c i)⁻¹ • α i, hα', hrefl', ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst hij
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (hc0 i), one_mul, hα i, hC.1]
      norm_num
    · have hcij := hc i j hij
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
      simpa only [P, mul_assoc] using hcij

private def pr_A_par (r : ℕ) (i : Fin r) : Fin r :=
  ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

private theorem pr_A_par_eq (r : ℕ) (i j : Fin r) (hi : i.val ≠ 0) :
    pr_A_par r i = j ↔ i.val = j.val + 1 := by
  rw [Fin.ext_iff]
  simp only [pr_A_par]
  omega

private theorem pr_A_neg_one (r : ℕ) (i j : Fin r) :
    CartanMatrix.A r i j = -1 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  rw [CartanMatrix.A, Matrix.of_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    by_cases h2 : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [if_pos h2]; exact iff_of_true rfl h2
    · rw [if_neg h2]; exact iff_of_false (by norm_num) h2

private theorem pr_A_hsl (r : ℕ) (i j : Fin r) (hij : i ≠ j) :
    CartanMatrix.A r i j = 0 ∨ CartanMatrix.A r i j = -1 := by
  rw [CartanMatrix.A, Matrix.of_apply, if_neg hij]
  by_cases h2 : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [if_pos h2]; exact Or.inr rfl
  · rw [if_neg h2]; exact Or.inl rfl

private theorem pr_A_hpar (r : ℕ) (hr : 1 ≤ r) (i j : Fin r) (hij : i ≠ j) :
    (CartanMatrix.A r i j = -1 ↔
      ((i ≠ (⟨0, hr⟩ : Fin r) ∧ pr_A_par r i = j) ∨
        (j ≠ (⟨0, hr⟩ : Fin r) ∧ pr_A_par r j = i))) := by
  rw [pr_A_neg_one]
  have hroot : ∀ i : Fin r, (i ≠ (⟨0, hr⟩ : Fin r)) ↔ i.val ≠ 0 := by
    intro i
    simp [Fin.ext_iff]
  constructor
  · intro h
    rcases h with h | h
    · right
      refine ⟨(hroot j).mpr (by omega), ?_⟩
      rw [pr_A_par_eq r j i (by omega)]
      omega
    · left
      refine ⟨(hroot i).mpr (by omega), ?_⟩
      rw [pr_A_par_eq r i j (by omega)]
      omega
  · rintro (⟨hi, hpi⟩ | ⟨hj, hpj⟩)
    · rw [pr_A_par_eq r i j ((hroot i).mp hi)] at hpi
      omega
    · rw [pr_A_par_eq r j i ((hroot j).mp hj)] at hpj
      omega

private theorem pr_A_hdepth (r : ℕ) (hr : 1 ≤ r) (i : Fin r)
    (hi : i ≠ (⟨0, hr⟩ : Fin r)) : (pr_A_par r i).val < i.val := by
  have hroot : i.val ≠ 0 := by
    intro h0; exact hi (Fin.ext h0)
  simp only [pr_A_par, Fin.val_mk]
  omega

private theorem pr_D_neg_one (r : ℕ) (hr : 4 ≤ r) (i j : Fin r) :
    CartanMatrix.D r i j = -1 ↔
      (i.val + 1 = j.val ∧ j.val + 2 < r) ∨ (j.val + 1 = i.val ∧ i.val + 2 < r) ∨
      (i.val + 3 = r ∧ (j.val + 2 = r ∨ j.val + 1 = r)) ∨
      (j.val + 3 = r ∧ (i.val + 2 = r ∨ i.val + 1 = r)) := by
  rw [CartanMatrix.D, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    constructor
    · intro h; norm_num at h
    · intro h; omega
  · rw [if_neg hij]
    rw [if_neg (by omega : ¬ r ≤ 2)]
    by_cases c1 : i.val + 1 = j.val ∧ j.val + 2 < r
    · rw [if_pos c1]; exact iff_of_true rfl (Or.inl c1)
    · rw [if_neg c1]
      by_cases c2 : j.val + 1 = i.val ∧ i.val + 2 < r
      · rw [if_pos c2]; exact iff_of_true rfl (Or.inr (Or.inl c2))
      · rw [if_neg c2]
        by_cases c3 : i.val + 3 = r ∧ (j.val + 2 = r ∨ j.val + 1 = r)
        · rw [if_pos c3]; exact iff_of_true rfl (Or.inr (Or.inr (Or.inl c3)))
        · rw [if_neg c3]
          by_cases c4 : j.val + 3 = r ∧ (i.val + 2 = r ∨ i.val + 1 = r)
          · rw [if_pos c4]; exact iff_of_true rfl (Or.inr (Or.inr (Or.inr c4)))
          · rw [if_neg c4]
            exact iff_of_false (by norm_num) (by
              rintro (h | h | h | h)
              · exact c1 h
              · exact c2 h
              · exact c3 h
              · exact c4 h)

private theorem pr_D_hsl (r : ℕ) (i j : Fin r) (hij : i ≠ j) :
    CartanMatrix.D r i j = 0 ∨ CartanMatrix.D r i j = -1 := by
  rcases cartanMatrix_D_pair r hij with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

private def pr_D_par (r : ℕ) (hr : 4 ≤ r) (i : Fin r) : Fin r :=
  if i.val = r - 1 then ⟨r - 3, by omega⟩
  else ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

private theorem pr_D_par_eq (r : ℕ) (hr : 4 ≤ r) (i j : Fin r) (hi : i.val ≠ 0) :
    pr_D_par r hr i = j ↔
      (i.val = r - 1 ∧ j.val = r - 3) ∨ (i.val ≠ r - 1 ∧ i.val = j.val + 1) := by
  rw [Fin.ext_iff]
  by_cases h1 : i.val = r - 1
  · rw [pr_D_par, if_pos h1]
    simp only [Fin.val_mk]
    constructor
    · intro h; exact Or.inl ⟨h1, h.symm⟩
    · rintro (⟨-, h⟩ | ⟨hne, -⟩)
      · exact h.symm
      · exact absurd h1 hne
  · rw [pr_D_par, if_neg h1]
    simp only [Fin.val_mk]
    constructor
    · intro h; exact Or.inr ⟨h1, by omega⟩
    · rintro (⟨hv, -⟩ | ⟨-, h⟩)
      · exact absurd hv h1
      · omega

private theorem pr_D_hpar (r : ℕ) (hr : 4 ≤ r) (i j : Fin r) (hij : i ≠ j) :
    (CartanMatrix.D r i j = -1 ↔
      ((i ≠ (⟨0, by omega⟩ : Fin r) ∧ pr_D_par r hr i = j) ∨
        (j ≠ (⟨0, by omega⟩ : Fin r) ∧ pr_D_par r hr j = i))) := by
  rw [pr_D_neg_one r hr]
  have hroot : ∀ i : Fin r, (i ≠ (⟨0, by omega⟩ : Fin r)) ↔ i.val ≠ 0 := by
    intro i; simp [Fin.ext_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right
      refine ⟨(hroot j).mpr (by omega), ?_⟩
      rw [pr_D_par_eq r hr j i (by omega)]
      exact Or.inr ⟨by omega, by omega⟩
    · left
      refine ⟨(hroot i).mpr (by omega), ?_⟩
      rw [pr_D_par_eq r hr i j (by omega)]
      exact Or.inr ⟨by omega, by omega⟩
    · rcases h2 with h2 | h2
      · right
        refine ⟨(hroot j).mpr (by omega), ?_⟩
        rw [pr_D_par_eq r hr j i (by omega)]
        exact Or.inr ⟨by omega, by omega⟩
      · right
        refine ⟨(hroot j).mpr (by omega), ?_⟩
        rw [pr_D_par_eq r hr j i (by omega)]
        exact Or.inl ⟨by omega, by omega⟩
    · rcases h2 with h2 | h2
      · left
        refine ⟨(hroot i).mpr (by omega), ?_⟩
        rw [pr_D_par_eq r hr i j (by omega)]
        exact Or.inr ⟨by omega, by omega⟩
      · left
        refine ⟨(hroot i).mpr (by omega), ?_⟩
        rw [pr_D_par_eq r hr i j (by omega)]
        exact Or.inl ⟨by omega, by omega⟩
  · rintro (⟨hi, hpi⟩ | ⟨hj, hpj⟩)
    · rw [pr_D_par_eq r hr i j ((hroot i).mp hi)] at hpi
      rcases hpi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
      · by_cases hle : i.val + 2 < r
        · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · rw [pr_D_par_eq r hr j i ((hroot j).mp hj)] at hpj
      rcases hpj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
      · by_cases hle : j.val + 2 < r
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))

private def pr_D_depth (r : ℕ) (i : Fin r) : ℕ :=
  if i.val = r - 1 then r - 2 else i.val

private theorem pr_D_depth_par (r : ℕ) (hr : 4 ≤ r) (i : Fin r) :
    pr_D_depth r (pr_D_par r hr i) = if i.val = r - 1 then r - 3 else i.val - 1 := by
  rw [pr_D_depth, pr_D_par]
  by_cases h1 : i.val = r - 1
  · rw [if_pos h1]
    simp only [Fin.val_mk]
    rw [if_neg (by omega : ¬ r - 3 = r - 1), if_pos h1]
  · rw [if_neg h1]
    simp only [Fin.val_mk]
    rw [if_neg (by omega : ¬ i.val - 1 = r - 1), if_neg h1]

private theorem pr_D_hdepth (r : ℕ) (hr : 4 ≤ r) (i : Fin r)
    (hi : i ≠ (⟨0, by omega⟩ : Fin r)) :
    pr_D_depth r (pr_D_par r hr i) < pr_D_depth r i := by
  have hroot : i.val ≠ 0 := by
    intro h0; exact hi (Fin.ext h0)
  rw [pr_D_depth_par, pr_D_depth]
  by_cases h1 : i.val = r - 1
  · rw [if_pos h1, if_pos h1]; omega
  · rw [if_neg h1, if_neg h1]; omega

theorem exists_cartan_pairing_A [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) {r : ℕ}
    (hr : 1 ≤ r) {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType p (CoxeterMatrix.A r) A)
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) :
    ∃ (h : Fin r → V) (α : Fin r → Module.Dual (ZMod p) V),
      ∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p) := by
  obtain ⟨-, h, α, -, -, hP⟩ :=
    exists_cartan_pairing_of_weylOfType (M := CoxeterMatrix.A r) (C := CartanMatrix.A r)
      hp2 hNT (ggIntCartan_A r) (pr_A_hsl r) (pr_A_par r) (⟨0, hr⟩) (fun i => i.val)
      (pr_A_hpar r hr) (fun i hi => pr_A_hdepth r hr i hi) hW hind ιV
  exact ⟨h, α, hP⟩

theorem exists_cartan_reflections_D [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {r : ℕ} (hr : 4 ≤ r) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType p (ggCoxeterMatrixD r) A) (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) :
    ∃ (e : (ggCoxeterMatrixD r).Group ≃* ↥A) (h : Fin r → V)
      (α : Fin r → Module.Dual (ZMod p) V) (hα : ∀ i, α i (h i) = 2),
      (∀ i, ggLin (p := p) ιV
          ((e ((ggCoxeterMatrixD r).simple i) : ↥A) : MulAut ↥Bs) = Module.reflection (hα i)) ∧
        ∀ i j, α i (h j) = (CartanMatrix.D r i j : ZMod p) :=
  exists_cartan_pairing_of_weylOfType (M := ggCoxeterMatrixD r) (C := CartanMatrix.D r)
    hp2 hNT (ggIntCartan_D r) (pr_D_hsl r) (pr_D_par r hr) (⟨0, by omega⟩)
    (pr_D_depth r) (pr_D_hpar r hr) (fun i hi => pr_D_hdepth r hr i hi) hW hind ιV

theorem exists_cartan_pairing_D [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) {r : ℕ}
    (hr : 4 ≤ r) {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType p (ggCoxeterMatrixD r) A)
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) :
    ∃ (h : Fin r → V) (α : Fin r → Module.Dual (ZMod p) V),
      ∀ i j, α i (h j) = (CartanMatrix.D r i j : ZMod p) := by
  obtain ⟨-, h, α, -, -, hP⟩ := exists_cartan_reflections_D hp2 hNT hr hW hind ιV
  exact ⟨h, α, hP⟩

end Pairing

end CFSG.StandardType.SpJoinRefl
