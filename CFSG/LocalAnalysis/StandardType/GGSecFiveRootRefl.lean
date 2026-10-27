module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
public import CFSG.LocalAnalysis.StandardType.GGWeylReflection
public import CFSG.LocalAnalysis.StandardType.GGReflModule
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed

public section

namespace CFSG.StandardType.SecFiveRootRefl

open CFSG CFSG.Assembly Module CFSG.LieType.RootSystem CFSG.StandardType.SpJoinRefl


noncomputable def treeGauge {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] (A : ι → ι → ℤ) (P : ι → ι → K)
    (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) : ι → K
  | i => if _ : i = root then 1
      else treeGauge A P par root depth hdepth (par i) * P i (par i) * ((A i (par i) : K))⁻¹
termination_by i => depth i
decreasing_by exact hdepth i ‹i ≠ root›

theorem treeGauge_of_ne_root {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] (A : ι → ι → ℤ) (P : ι → ι → K)
    (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) {i : ι} (hi : i ≠ root) :
    treeGauge A P par root depth hdepth i =
      treeGauge A P par root depth hdepth (par i) * P i (par i) * ((A i (par i) : K))⁻¹ := by
  rw [treeGauge.eq_1, dif_neg hi]

theorem exists_gauge_of_tree {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (A : ι → ι → ℤ) (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hP0 : ∀ i j, i ≠ j → A i j = 0 → P i j = 0)
    (hPP : ∀ i j, i ≠ j → A i j ≠ 0 → P i j * P j i = (A i j : K) * (A j i : K))
    (hAK : ∀ i j, i ≠ j → A i j ≠ 0 → (A i j : K) ≠ 0)
    (hpar : ∀ i j, i ≠ j → (A i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) :
    ∃ c : ι → K, (∀ i, c i ≠ 0) ∧ ∀ i j, i ≠ j → (c i)⁻¹ * c j * P i j = (A i j : K) := by
  set c := treeGauge A P par root depth hdepth with hcdef
  have hsym : ∀ i j, i ≠ j → A i j ≠ 0 → A j i ≠ 0 := by
    intro i j hij h
    exact (hpar j i (Ne.symm hij)).mpr (((hpar i j hij).mp h).symm)
  have hPne : ∀ i j, i ≠ j → A i j ≠ 0 → P i j ≠ 0 := by
    intro i j hij h h0
    have := hPP i j hij h
    rw [h0, zero_mul] at this
    exact mul_ne_zero (hAK i j hij h) (hAK j i (Ne.symm hij) (hsym i j hij h)) this.symm
  have hparne : ∀ i, i ≠ root → i ≠ par i := by
    intro i hi heq
    have h1 := hdepth i hi
    rw [← heq] at h1
    exact lt_irrefl _ h1
  have hedge : ∀ i, i ≠ root → A i (par i) ≠ 0 := fun i hi =>
    (hpar i (par i) (hparne i hi)).mpr (Or.inl ⟨hi, rfl⟩)
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i
    induction hd : depth i using Nat.strong_induction_on generalizing i with
    | _ n ih =>
      by_cases hi : i = root
      · rw [hcdef, treeGauge.eq_1, dif_pos hi]; exact one_ne_zero
      · rw [hcdef, treeGauge_of_ne_root A P par root depth hdepth hi]
        have hlt : depth (par i) < n := hd ▸ hdepth i hi
        refine mul_ne_zero (mul_ne_zero (ih _ hlt (par i) rfl)
          (hPne i (par i) (hparne i hi) (hedge i hi))) (inv_ne_zero ?_)
        exact hAK i (par i) (hparne i hi) (hedge i hi)
  refine ⟨c, hc0, fun i j hij => ?_⟩
  by_cases hA : A i j = 0
  · rw [hP0 i j hij hA, hA]; simp
  · rcases (hpar i j hij).mp hA with ⟨hir, hpi⟩ | ⟨hjr, hpj⟩
    · have hci : c i = c j * P i j * ((A i j : K))⁻¹ := by
        rw [hcdef, treeGauge_of_ne_root A P par root depth hdepth hir, hpi]
      have h1 := hc0 j
      have h2 := hPne i j hij hA
      have h3 := hAK i j hij hA
      rw [hci]
      field_simp
    · have hcj : c j = c i * P j i * ((A j i : K))⁻¹ := by
        rw [hcdef, treeGauge_of_ne_root A P par root depth hdepth hjr, hpj]
      have h1 := hc0 i
      have h3 := hAK j i (Ne.symm hij) (hsym i j hij hA)
      have hpp := hPP i j hij hA
      rw [hcj]
      field_simp
      linear_combination hpp

section Pairing

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

theorem ggCoxA_four (R : Type*) [CommRing R] (t : R) :
    ggCoxA R ((4 : ℕ) : ℤ) t = t * (t + 1) := by
  simp only [ggCoxA]
  norm_num

theorem ggCoxB_four (R : Type*) [CommRing R] (t : R) :
    ggCoxB R ((4 : ℕ) : ℤ) t = t * (t * t - 1 + t) := by
  simp only [ggCoxB]
  norm_num [Polynomial.Chebyshev.S_two]
  ring

theorem pairing_mul_eq_two_of_four [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {ι : Type} {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A)
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
    (hα : ∀ i, α i (h i) = 2)
    (hrefl : ∀ i, ggLin (p := p) ιV ((e (M.simple i) : ↥A) : MulAut ↥Bs) =
      Module.reflection (hα i))
    {i j : ι} (hij : i ≠ j) (hM4 : M i j = 4) : α i (h j) * α j (h i) = 2 := by
  let φ : ι → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  let Φ : M.Group →* MulAut ↥Bs := (Subgroup.subtype A).comp e.toMonoidHom
  have hφeq : ∀ i, φ i = Φ (M.simple i) := fun _ => rfl
  have hφind : ∀ i, φ i ∈ ggInduced ⊤ Bs := fun i => hind _ (SetLike.coe_mem _)
  have hΦinj : Function.Injective Φ := fun a b hab => e.injective (Subtype.coe_injective hab)
  have hφinj : Function.Injective φ := by
    intro i j hij
    have h1 : e (M.simple i) = e (M.simple j) := Subtype.ext hij
    exact CoxeterSystem.simple_injective M.toCoxeterSystem (by
      rw [CoxeterMatrix.toCoxeterSystem_simple]; exact e.injective h1)
  have horder : orderOf (M.simple i * M.simple j) = 4 := by
    have h := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h
    rw [h, hM4]
  have hmul : φ i * φ j = Φ (M.simple i * M.simple j) := by rw [map_mul, hφeq i, hφeq j]
  have hpow4 : (φ i * φ j) ^ 4 = 1 := by
    rw [hmul, ← map_pow, ← horder, pow_orderOf_eq_one, map_one]
  have hpow2 : (φ i * φ j) ^ 2 ≠ 1 := by
    intro h2
    rw [hmul, ← map_pow] at h2
    have h3 : (M.simple i * M.simple j) ^ 2 = 1 := hΦinj (by rw [h2, map_one])
    have h4 := orderOf_le_of_pow_eq_one (by norm_num) h3
    rw [horder] at h4
    omega
  have hpow2_of : α i (h j) = 0 → α j (h i) = 0 → (φ i * φ j) ^ 2 = 1 := by
    intro h0 hv0
    apply ggLin_injective (p := p) ιV
    rw [map_pow, map_mul, hrefl i, hrefl j, map_one]
    exact reflection_mul_reflection_pow_two (hα i) (hα j) h0 hv0
  have hcross : α i (h j) = 0 → α j (h i) = 0 := fun h0 =>
    ggCross_eq_zero_of_noTransvection hp2 hNT ιV (hφind i) (hφind j)
      (hα i) (hα j) (hrefl i) (hrefl j) h0
  have hcross' : α j (h i) = 0 → α i (h j) = 0 := fun h0 =>
    ggCross_eq_zero_of_noTransvection hp2 hNT ιV (hφind j) (hφind i)
      (hα j) (hα i) (hrefl j) (hrefl i) h0
  have hu : α i (h j) ≠ 0 := fun h0 => hpow2 (hpow2_of h0 (hcross h0))
  have hv : α j (h i) ≠ 0 := fun h0 => hpow2 (hpow2_of (hcross' h0) h0)
  have hcrit := (ggReflection_mul_pow_eq_one_iff hp2 hNT ιV (hφind i) (hφind j)
    (hφinj.ne hij) (hα i) (hα j) (hrefl i) (hrefl j) hu hv 4).mp hpow4
  obtain ⟨hA, hB⟩ := hcrit
  rw [ggCoxA_four] at hA
  rw [ggCoxB_four] at hB
  linear_combination (α i (h j) * α j (h i) - 2) * hA - hB

theorem exists_cartan_pairing_of_weylOfType' [Finite G] (hp2 : p ≠ 2)
    (hNT : GGNoTransvection p Bs) {ι : Type} [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hC : GGIntCartan M C) (hno6 : ∀ i j, M i j ≠ 6)
    (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hpar : ∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
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
  have htwo : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hP0 : ∀ i j, i ≠ j → C i j = 0 → P i j = 0 := by
    intro i j hij hCij
    rcases hC.entries hij with ⟨hM, -, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨hM, -⟩
    · exact (h2 i j hij hM).1
    · rw [hCij] at h1; norm_num at h1
    · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hCij] at h1 <;> norm_num at h1
    · exact absurd hM (hno6 i j)
  have hPP : ∀ i j, i ≠ j → C i j ≠ 0 → P i j * P j i = (C i j : ZMod p) * (C j i : ZMod p) := by
    intro i j hij hCij
    rcases hC.entries hij with ⟨-, h1, -⟩ | ⟨hM, h1, h1'⟩ | ⟨hM, h1⟩ | ⟨hM, -⟩
    · exact absurd h1 hCij
    · rw [h3 i j hij hM, h1, h1']; norm_num
    · rw [pairing_mul_eq_two_of_four hp2 hNT e hind ιV h α hα hrefl hij hM]
      rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rw [h1, h1'] <;> norm_num
    · exact absurd hM (hno6 i j)
  have hAK : ∀ i j, i ≠ j → C i j ≠ 0 → ((C i j : ℤ) : ZMod p) ≠ 0 := by
    intro i j hij hCij
    rcases hC.entries hij with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨hM, -⟩
    · exact absurd h1 hCij
    · rw [h1]; norm_num
    · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · norm_num
      · push_cast; exact neg_ne_zero.mpr htwo
    · exact absurd hM (hno6 i j)
  obtain ⟨c, hc0, hc⟩ :=
    exists_gauge_of_tree (K := ZMod p) (fun i j => C i j) P par root depth hP0 hPP hAK hpar hdepth
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
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (hc0 i), one_mul, hα i, hC.1]
    norm_num
  · have hcij := hc i j hij
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
    simpa only [P, mul_assoc] using hcij

end Pairing



section Pairing

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

theorem ggCoxA_two' (R : Type*) [CommRing R] (t : R) : ggCoxA R ((2 : ℕ) : ℤ) t = 1 := by
  simp only [ggCoxA]
  norm_num

theorem ggCoxA_three' (R : Type*) [CommRing R] (t : R) :
    ggCoxA R ((3 : ℕ) : ℤ) t = t + 1 := by
  simp only [ggCoxA]
  norm_num

theorem exists_pairing_of_iso [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {ι : Type} {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A)
    (he : ∀ i : ι, GGIsReflection p ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) :
    ∃ (h : ι → V) (α : ι → Module.Dual (ZMod p) V) (hα : ∀ i, α i (h i) = 2),
      (∀ i, ggLin (p := p) ιV ((e (M.simple i) : ↥A) : MulAut ↥Bs) = Module.reflection (hα i)) ∧
      (∀ i j, i ≠ j → M i j = 2 → α i (h j) = 0 ∧ α j (h i) = 0) ∧
      (∀ i j, i ≠ j → M i j = 3 → α i (h j) * α j (h i) = 1) ∧
      (∀ i j, i ≠ j → M i j = 4 → α i (h j) * α j (h i) = 2) := by
  classical
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
  refine ⟨x, f, hfx, hlin, ?_, ?_, ?_⟩
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
        rw [ggCoxA_two'] at h0
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
    rw [ggCoxA_three'] at h0
    linear_combination h0
  · intro i j hij hM4
    exact pairing_mul_eq_two_of_four hp2 hNT e hind ιV x f hfx hlin hij hM4

@[expose] def CartanTree {ι : Type} (C : Matrix ι ι ℤ) : Prop :=
  ∃ (par : ι → ι) (root : ι) (depth : ι → ℕ),
    (∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i)))) ∧
      ∀ i, i ≠ root → depth (par i) < depth i

theorem exists_cartan_pairing_of_iso [Finite G] (hp2 : p ≠ 2)
    (hNT : GGNoTransvection p Bs) {ι : Type} [DecidableEq ι] {M : CoxeterMatrix ι}
    {C : Matrix ι ι ℤ} (hC : GGIntCartan M C)
    (hent : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1 ∨ C i j = -2) (hT : CartanTree C)
    {A : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A)
    (he : ∀ i : ι, GGIsReflection p ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) :
    ∃ (h : ι → V) (α : ι → Module.Dual (ZMod p) V) (hα : ∀ i, α i (h i) = 2),
      (∀ i, ggLin (p := p) ιV ((e (M.simple i) : ↥A) : MulAut ↥Bs) = Module.reflection (hα i)) ∧
      ∀ i j, α i (h j) = (C i j : ZMod p) := by
  classical
  obtain ⟨par, root, depth, hpar, hdepth⟩ := hT
  obtain ⟨h, α, hα, hrefl, h2, h3, h4⟩ := exists_pairing_of_iso hp2 hNT e he hind ιV
  let P : ι → ι → ZMod p := fun i j => α i (h j)
  have htwo : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hno6 : ∀ i j, i ≠ j → M i j ≠ 6 := by
    intro i j hij hM
    rcases hC.entries hij with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩
    · omega
    · omega
    · omega
    · rcases h1 with ⟨-, h1⟩ | ⟨h1, -⟩
      · rcases hent j i (Ne.symm hij) with h0 | h0 | h0 <;> omega
      · rcases hent i j hij with h0 | h0 | h0 <;> omega
  have hP0 : ∀ i j, i ≠ j → C i j = 0 → P i j = 0 := by
    intro i j hij hCij
    rcases hC.entries hij with ⟨hM, -, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1⟩ | ⟨hM, -⟩
    · exact (h2 i j hij hM).1
    · rw [hCij] at h1; norm_num at h1
    · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hCij] at h1 <;> norm_num at h1
    · exact absurd hM (hno6 i j hij)
  have hPP : ∀ i j, i ≠ j → C i j ≠ 0 →
      P i j * P j i = (C i j : ZMod p) * (C j i : ZMod p) := by
    intro i j hij hCij
    rcases hC.entries hij with ⟨-, h1, -⟩ | ⟨hM, h1, h1'⟩ | ⟨hM, h1⟩ | ⟨hM, -⟩
    · exact absurd h1 hCij
    · rw [h3 i j hij hM, h1, h1']; norm_num
    · rw [h4 i j hij hM]
      rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rw [h1, h1'] <;> norm_num
    · exact absurd hM (hno6 i j hij)
  have hAK : ∀ i j, i ≠ j → C i j ≠ 0 → ((C i j : ℤ) : ZMod p) ≠ 0 := by
    intro i j hij hCij
    rcases hent i j hij with h1 | h1 | h1
    · exact absurd h1 hCij
    · rw [h1]; norm_num
    · rw [h1]; push_cast; exact neg_ne_zero.mpr htwo
  obtain ⟨c, hc0, hc⟩ :=
    exists_gauge_of_tree (K := ZMod p) (fun i j => C i j) P par root depth hP0 hPP hAK hpar hdepth
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
  refine ⟨fun j => c j • h j, fun i => (c i)⁻¹ • α i, hα', hrefl', ?_⟩
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (hc0 i), one_mul, hα i, hC.1]
    norm_num
  · have hcij := hc i j hij
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
    simpa only [P, mul_assoc] using hcij

theorem rootRefl_of_cartan [Finite G] (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) (hFT : TauCeti.IsFiniteType C)
    (hent : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1 ∨ C i j = -2) (hT : CartanTree C)
    {A : Subgroup (MulAut ↥Bs)} (hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) (f : M.Group ≃* ↥A)
    (hf : ∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V)
    (a : ↥A) (ha : GGIsReflection p (a : MulAut ↥Bs)) :
    ∃ (i : ι) (g : M.Group), a = f (g * M.simple i * g⁻¹) := by
  obtain ⟨h, α, hα, hrefl, hP⟩ := exists_cartan_pairing_of_iso hp2 hNT hC hent hT f hf hind ιV
  have hMeq : coxeterMatrix hFT = M := coxeterMatrix_eq_of_ggIntCartan hFT hC
  subst hMeq
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  let ρ : (coxeterMatrix hFT).Group →* (V ≃ₗ[ZMod p] V) :=
    (ggLin (p := p) ιV).comp ((Subgroup.subtype A).comp f.toMonoidHom)
  have hρapp : ∀ w, ρ w = ggLin (p := p) ιV ((f w : ↥A) : MulAut ↥Bs) := fun _ => rfl
  have hρ : ∀ i v, ρ ((coxeterMatrix hFT).toCoxeterSystem.simple i) v = v - α i v • h i := by
    intro i v
    rw [hρapp, CoxeterMatrix.toCoxeterSystem_simple, hrefl i, Module.reflection_apply]
  set t := f.symm a with htdef
  have hft : f t = a := by rw [htdef, MulEquiv.apply_symm_apply]
  have ha2 : a * a = 1 := by
    apply Subtype.ext
    have := ha.1
    rw [pow_two] at this
    simpa using this
  have ht : t * t = 1 := by
    apply f.injective
    rw [map_mul, hft, ha2, map_one]
  have hminus := ggRefl_minus_finrank hFT hp2 h α hP ρ hρ t ht
  have hT2 : (ρ t) ^ 2 = 1 := by rw [← map_pow, pow_two, ht, map_one]
  have hfix : Nat.card {v : V // ρ t v = v} * p = Nat.card V := by
    rw [hρapp, hft]
    exact ((ggIsReflection_iff ιV _).mp ha).2
  have hker := ggFinrank_minus_eq_one hp2 (ρ t) hT2 hfix
  have hle : LinearMap.ker ((ρ t).toLinearMap + 1) ≤ Submodule.span (ZMod p) (Set.range h) := by
    intro v hv
    have hv' : ρ t v = -v := by
      rw [LinearMap.mem_ker, LinearMap.add_apply, LinearEquiv.coe_coe, Module.End.one_apply,
        add_eq_zero_iff_eq_neg] at hv
      exact hv
    have hmem := ggRefl_sub_mem hFT h α ρ hρ t v
    rw [hv'] at hmem
    have h2v : (2 : ZMod p) • v ∈ Submodule.span (ZMod p) (Set.range h) := by
      have := Submodule.neg_mem _ hmem
      rwa [neg_sub, sub_neg_eq_add, ← two_smul (ZMod p)] at this
    have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
    have := Submodule.smul_mem _ (2 : ZMod p)⁻¹ h2v
    rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at this
  rw [inf_eq_left.mpr hle, hker] at hminus
  obtain ⟨g, i, hgi⟩ := ggWeyl_isReflection_of_finrank hFT t ht hminus.symm
  refine ⟨i, g, ?_⟩
  rw [← hft, hgi, CoxeterMatrix.toCoxeterSystem_simple]

end Pairing

section Types

theorem CartanTree.reindex {n : ℕ} {ι : Type} (e : Fin n ≃ ι) {C : Matrix (Fin n) (Fin n) ℤ}
    (hT : CartanTree C) : CartanTree (Matrix.reindex e e C) := by
  obtain ⟨par, root, depth, hpar, hdepth⟩ := hT
  refine ⟨fun i => e (par (e.symm i)), e root, fun i => depth (e.symm i), ?_, ?_⟩
  · intro i j hij
    have hij' : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    have key : ∀ a b : ι, (a ≠ e root ∧ e (par (e.symm a)) = b) ↔
        (e.symm a ≠ root ∧ par (e.symm a) = e.symm b) := by
      intro a b
      rw [Equiv.apply_eq_iff_eq_symm_apply]
      have : (a ≠ e root) ↔ (e.symm a ≠ root) := not_congr (Equiv.symm_apply_eq e).symm
      rw [this]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hpar _ _ hij', key, key]
  · intro i hi
    have hi' : e.symm i ≠ root := fun h => hi (by rw [← h, Equiv.apply_symm_apply])
    simpa using hdepth (e.symm i) hi'

theorem entries_reindex {n : ℕ} {ι : Type} (e : Fin n ≃ ι) {C : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1 ∨ C i j = -2) :
    ∀ i j, i ≠ j → Matrix.reindex e e C i j = 0 ∨ Matrix.reindex e e C i j = -1 ∨
      Matrix.reindex e e C i j = -2 := by
  intro i j hij
  simpa [Matrix.reindex_apply] using h (e.symm i) (e.symm j) (fun h' => hij (e.symm.injective h'))

theorem cartanTree_chain {n : ℕ} (hn : 1 ≤ n) (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : ∀ i j : Fin n, i ≠ j → (C i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    CartanTree C := by
  refine ⟨fun i => ⟨i.val - 1, by omega⟩, ⟨0, hn⟩, fun i => i.val, ?_, ?_⟩
  · intro i j hij
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rw [hC i j hij]
    simp only [ne_eq, Fin.ext_iff]
    omega
  · intro i hi
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp only
    omega

theorem cartanTree_A (n : ℕ) (hn : 1 ≤ n) : CartanTree (CartanMatrix.A n) :=
  cartanTree_chain hn _ fun i j hij => by
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij]
    split_ifs with h <;> simp_all

theorem cartanTree_B (n : ℕ) (hn : 1 ≤ n) : CartanTree (CartanMatrix.B n) :=
  cartanTree_chain hn _ fun i j hij => by
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [CartanMatrix.B, Matrix.of_apply, if_neg hij]
    split_ifs <;> simp_all <;> omega

theorem cartanTree_F₄ : CartanTree CartanMatrix.F₄ :=
  cartanTree_chain (by norm_num) _ fun i j => by fin_cases i <;> fin_cases j <;> decide

theorem cartanTree_D (n : ℕ) (hn : 4 ≤ n) : CartanTree (CartanMatrix.D n) := by
  refine ⟨fun i => if i.val = n - 1 then ⟨n - 3, by omega⟩ else ⟨i.val - 1, by omega⟩,
    ⟨0, by omega⟩, fun i => i.val, ?_, ?_⟩
  · intro i j hij
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    simp only [CartanMatrix.D, Matrix.of_apply, if_neg hij, if_neg (show ¬ n ≤ 2 by omega),
      ne_eq, Fin.ext_iff]
    split_ifs <;> simp_all <;> omega
  · intro i hi
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have := i.isLt
    beta_reduce
    split_ifs <;> simp only <;> omega

theorem cartanTree_E (n : ℕ) (hn : 4 ≤ n) : CartanTree (CartanMatrix.E n) := by
  refine ⟨fun i => if i.val = 1 then ⟨3, by omega⟩ else if i.val = 2 then ⟨0, by omega⟩
      else ⟨i.val - 1, by omega⟩, ⟨0, by omega⟩,
    fun i => if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 0 then 0 else i.val - 1,
    ?_, ?_⟩
  · intro i j hij
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    simp only [CartanMatrix.E, Matrix.of_apply, if_neg hij, ne_eq, Fin.ext_iff]
    split_ifs <;> simp_all <;> omega
  · intro i hi
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have := i.isLt
    beta_reduce
    split_ifs <;> simp_all <;> omega

theorem entries_A (n : ℕ) : ∀ i j : Fin n, i ≠ j →
    CartanMatrix.A n i j = 0 ∨ CartanMatrix.A n i j = -1 ∨ CartanMatrix.A n i j = -2 := by
  intro i j hij
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij]
  split_ifs <;> simp

theorem entries_B (n : ℕ) : ∀ i j : Fin n, i ≠ j →
    CartanMatrix.B n i j = 0 ∨ CartanMatrix.B n i j = -1 ∨ CartanMatrix.B n i j = -2 := by
  intro i j hij
  simp only [CartanMatrix.B, Matrix.of_apply, if_neg hij]
  split_ifs <;> simp

theorem entries_D (n : ℕ) : ∀ i j : Fin n, i ≠ j →
    CartanMatrix.D n i j = 0 ∨ CartanMatrix.D n i j = -1 ∨ CartanMatrix.D n i j = -2 := by
  intro i j hij
  simp only [CartanMatrix.D, Matrix.of_apply, if_neg hij]
  split_ifs <;> simp

theorem entries_E (n : ℕ) : ∀ i j : Fin n, i ≠ j →
    CartanMatrix.E n i j = 0 ∨ CartanMatrix.E n i j = -1 ∨ CartanMatrix.E n i j = -2 := by
  intro i j hij
  simp only [CartanMatrix.E, Matrix.of_apply, if_neg hij]
  split_ifs <;> simp

theorem entries_F₄ : ∀ i j : Fin 4, i ≠ j →
    CartanMatrix.F₄ i j = 0 ∨ CartanMatrix.F₄ i j = -1 ∨ CartanMatrix.F₄ i j = -2 := by
  intro i j; fin_cases i <;> fin_cases j <;> decide

end Types

theorem ggSecFiveRootReflInput_holds : GGSecFiveRootReflInput := by
  intro G _ _ p Bs hp hp2 hEl hNT A hAind ι M hM hG2 f hf a ha
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hEl
  have hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs := fun φ h => hAind h
  have key : ∀ {n : ℕ} (e : Fin n ≃ ι) (M₀ : CoxeterMatrix (Fin n))
      (C₀ : Matrix (Fin n) (Fin n) ℤ), M = M₀.reindex e → GGIntCartan M₀ C₀ →
      TauCeti.IsFiniteType C₀ → (∀ i j, i ≠ j → C₀ i j = 0 ∨ C₀ i j = -1 ∨ C₀ i j = -2) →
      CartanTree C₀ → ∃ (i : ι) (g : M.Group), a = f (g * M.simple i * g⁻¹) := by
    intro n e M₀ C₀ hMe hC₀ hFT₀ hent hT
    haveI : Fintype ι := Fintype.ofEquiv _ e
    have hC : GGIntCartan M (Matrix.reindex e e C₀) := hMe ▸ hC₀.reindex e
    have hFT : TauCeti.IsFiniteType (Matrix.reindex e e C₀) := by
      rw [Matrix.reindex_apply]
      exact hFT₀.submatrix e.symm.injective
    exact rootRefl_of_cartan hp2 hNT hC hFT (entries_reindex e hent) (hT.reindex e) hind f hf ιV
      a ha
  rcases hM with ⟨n, e, hn, hMA | ⟨hn2, hMB⟩ | ⟨hn4, hMD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4⟩ | ⟨e, hMG⟩
  · exact key e _ _ hMA (ggIntCartan_A n) (TauCeti.isFiniteType_cartanMatrix_A n) (entries_A n)
      (cartanTree_A n hn)
  · exact key e _ _ hMB (ggIntCartan_B n) (TauCeti.isFiniteType_cartanMatrix_B n) (entries_B n)
      (cartanTree_B n hn)
  · exact key e _ _ hMD (ggIntCartan_D n) (TauCeti.isFiniteType_cartanMatrix_D n) (entries_D n)
      (cartanTree_D n hn4)
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
    rw [TauCeti.DynkinType.cartanMatrix_E6] at h
    exact key e _ _ hE6 ggIntCartan_E₆ h (entries_E 6) (cartanTree_E 6 (by norm_num))
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
    rw [TauCeti.DynkinType.cartanMatrix_E7] at h
    exact key e _ _ hE7 ggIntCartan_E₇ h (entries_E 7) (cartanTree_E 7 (by norm_num))
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E8
    rw [TauCeti.DynkinType.cartanMatrix_E8] at h
    exact key e _ _ hE8 ggIntCartan_E₈ h (entries_E 8) (cartanTree_E 8 (by norm_num))
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_F4
    rw [TauCeti.DynkinType.cartanMatrix_F4] at h
    exact key e _ _ hF4 ggIntCartan_F₄ h entries_F₄ cartanTree_F₄
  · exact absurd ⟨e, hMG⟩ hG2

end CFSG.StandardType.SecFiveRootRefl
