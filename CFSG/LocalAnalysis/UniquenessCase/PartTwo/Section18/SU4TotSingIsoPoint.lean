module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Unitary CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LieType.Universal.Unitary (SUid)
open scoped Matrix

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {n p : ℕ}

private def isoVec_T1J3 (a b : Fˣ) : Fin 4 → F :=
  ![(a : F), (a : F), (b : F), ((((a * a * b)⁻¹ : Fˣ)) : F)]

private theorem isoVec_det_T1J3 (a b : Fˣ) : ∏ i, isoVec_T1J3 a b i = 1 := by
  rw [Fin.prod_univ_four]
  have h : (((a * a * b) * (a * a * b)⁻¹ : Fˣ) : F) = 1 := by simp
  simpa [isoVec_T1J3, mul_assoc] using h

private theorem isoVec_norm_T1J3 {Z : Subgroup Fˣ} (hZ : ∀ a ∈ Z, σ (a : F) * a = 1)
    {a b : Fˣ} (ha : a ∈ Z) (hb : b ∈ Z) (i : Fin 4) :
    σ (isoVec_T1J3 a b i) * isoVec_T1J3 a b i = 1 := by
  fin_cases i
  · simpa [isoVec_T1J3] using hZ a ha
  · simpa [isoVec_T1J3] using hZ a ha
  · simpa [isoVec_T1J3] using hZ b hb
  · exact hZ _ (Z.inv_mem (Z.mul_mem (Z.mul_mem ha ha) hb))

private theorem isoVec_mul_T1J3 (a a' b b' : Fˣ) (i : Fin 4) :
    isoVec_T1J3 (a * a') (b * b') i = isoVec_T1J3 a b i * isoVec_T1J3 a' b' i := by
  fin_cases i
  · simp [isoVec_T1J3]
  · simp [isoVec_T1J3]
  · simp [isoVec_T1J3]
  · have h : ((a * a') * (a * a') * (b * b'))⁻¹ =
        (a * a * b)⁻¹ * (a' * a' * b')⁻¹ := by
      rw [← mul_inv]
      congr 1
      ac_rfl
    simp [isoVec_T1J3, h]

private noncomputable def isoSU_T1J3 (Z : Subgroup Fˣ)
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) : ↥Z × ↥Z →* ↥(SUid σ 4) where
  toFun x := diagSU σ (isoVec_T1J3 (x.1 : Fˣ) (x.2 : Fˣ))
    (isoVec_norm_T1J3 hZ x.1.2 x.2.2) (isoVec_det_T1J3 _ _)
  map_one' := by
    apply ext_smul
    intro v
    rw [diagSU_smul, one_smul]
    funext i
    fin_cases i <;> simp [isoVec_T1J3]
  map_mul' x y := by
    apply ext_smul
    intro v
    rw [mul_smul, diagSU_smul, diagSU_smul, diagSU_smul]
    funext i
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [isoVec_mul_T1J3, mul_assoc]

private theorem isoSU_smul_T1J3 (Z : Subgroup Fˣ)
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) (x : ↥Z × ↥Z) (v : Fin 4 → F) :
    isoSU_T1J3 Z hZ x • v = fun i => isoVec_T1J3 (x.1 : Fˣ) (x.2 : Fˣ) i * v i :=
  diagSU_smul σ _ _ _ v

private theorem isoSU_smul_eq_smul_T1J3 {Z : Subgroup Fˣ}
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) {s : Fin 4 → F} (h0 : s 0 = 1) (h2 : s 2 = 0)
    (h3 : s 3 = 0) (x : ↥Z × ↥Z) :
    isoSU_T1J3 Z hZ x • s = ((x.1 : Fˣ) : F) • s := by
  rw [isoSU_smul_T1J3]
  funext i
  fin_cases i <;> simp [isoVec_T1J3, h0, h2, h3]

private theorem isoSU_injective_T1J3 (Z : Subgroup Fˣ)
    (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) : Function.Injective (isoSU_T1J3 Z hZ) := by
  intro x y h
  have h1 := congrArg (fun g => g • (Pi.single 0 1 : Fin 4 → F)) h
  have h2 := congrArg (fun g => g • (Pi.single 2 1 : Fin 4 → F)) h
  simp only [isoSU_smul_T1J3] at h1 h2
  have e1 := congrFun h1 0
  have e2 := congrFun h2 2
  simp [isoVec_T1J3] at e1 e2
  exact Prod.ext (Subtype.ext (Units.ext e1)) (Subtype.ext (Units.ext e2))

private theorem span_stab_T1J3 {E : Subgroup (GL (Fin 4) F)} {v : Fin 4 → F}
    (hscale : ∀ g ∈ E, ∃ d : F, d ≠ 0 ∧
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ v = d • v)
    (g : GL (Fin 4) F) (hg : g ∈ E) (x : Fin 4 → F) :
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ Submodule.span F {v} ↔
      x ∈ Submodule.span F {v} := by
  obtain ⟨d, -, hdv⟩ := hscale g hg
  obtain ⟨d', -, hd'v⟩ := hscale g⁻¹ (E.inv_mem hg)
  have h1 : ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
      (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [Submodule.mem_span_singleton]
    refine ⟨c * d', ?_⟩
    rw [← h1, ← hc, Matrix.mulVec_smul, hd'v, smul_smul]
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [Submodule.mem_span_singleton]
    refine ⟨c * d, ?_⟩
    rw [← hc, Matrix.mulVec_smul, hdv, smul_smul]

private theorem exists_scale_range_T1J3 (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hnorm : ∀ c : F, σ c * c = c ^ (2 ^ n + 1))
    {v s : Fin 4 → F} (t : ↥(SUid σ 4)) (h0 : s 0 = 1) (h2 : s 2 = 0) (h3 : s 3 = 0)
    (ht : t • s = v) :
    ∃ P : Subgroup (GL (Fin 4) F), P ≤ SUid σ 4 ∧ IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
      ∀ g ∈ P, ∃ d : F, d ≠ 0 ∧
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ v = d • v := by
  obtain ⟨Z, hZp, hZcard, hZ⟩ := exists_torus_data hp hpq hF hnorm
  set Θ : ↥Z × ↥Z →* ↥(SUid σ 4) := isoSU_T1J3 Z hZ with hΘdef
  set Ψ : ↥Z × ↥Z →* GL (Fin 4) F :=
    (SUid σ 4).subtype.comp ((MulAut.conj t).toMonoidHom.comp Θ) with hΨdef
  have hΨa : ∀ a, Ψ a = ((t * Θ a * t⁻¹ : ↥(SUid σ 4)) : GL (Fin 4) F) := fun a => rfl
  have hinj : Function.Injective Ψ :=
    (SUid σ 4).subtype_injective.comp
      ((MulAut.conj t).injective.comp (isoSU_injective_T1J3 Z hZ))
  have hA : ∀ x : ↥Z × ↥Z, x ^ p = 1 := fun x => by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using hZp _ x.1.2
    · simpa using hZp _ x.2.2
  have hcard : Nat.card (↥Z × ↥Z) = p ^ 2 := by rw [Nat.card_prod, hZcard, sq]
  have hscale_phi : ∀ a : ↥Z × ↥Z,
      (t * Θ a * t⁻¹ : ↥(SUid σ 4)) • v = ((a.1 : Fˣ) : F) • v := by
    intro a
    have htinv : t⁻¹ • v = s := by rw [← ht, inv_smul_smul]
    calc (t * Θ a * t⁻¹) • v = t • (Θ a • (t⁻¹ • v)) := by rw [mul_smul, mul_smul]
      _ = t • (Θ a • s) := by rw [htinv]
      _ = t • (((a.1 : Fˣ) : F) • s) := by
        rw [isoSU_smul_eq_smul_T1J3 hZ h0 h2 h3 a]
      _ = ((a.1 : Fˣ) : F) • (t • s) := by rw [smul_comm]
      _ = ((a.1 : Fˣ) : F) • v := by rw [ht]
  have hscale : ∀ g ∈ Ψ.range, ∃ d : F, d ≠ 0 ∧
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ v = d • v := by
    rintro _ ⟨a, rfl⟩
    refine ⟨((a.1 : Fˣ) : F), (a.1 : Fˣ).ne_zero, ?_⟩
    rw [hΨa]
    exact (smul_def σ _ _).symm.trans (hscale_phi a)
  refine ⟨Ψ.range, ?_, ?_, ?_, hscale⟩
  · rintro _ ⟨a, rfl⟩
    rw [hΨa]
    exact (t * Θ a * t⁻¹).2
  · exact isElemAbelian_range Ψ hA
  · rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_stab_isotropicLine (hσ : IsUnitaryInvolution σ)
    (hσpow : ∀ c, σ c = c ^ 2 ^ n) (hF : Nat.card F = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) {v : Fin 4 → F} (hv0 : v ≠ 0) (hv : herm σ v v = 0) :
    ∃ P : Subgroup (GL (Fin 4) F), P ≤ SUid σ 4 ∧ IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
      ∀ g ∈ P, ∀ x : Fin 4 → F,
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ Submodule.span F {v} ↔
          x ∈ Submodule.span F {v} := by
  have hnorm : ∀ c : F, σ c * c = c ^ (2 ^ n + 1) := fun c => by
    rw [hσpow c, ← pow_succ]
  obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
  set s : Fin 4 → F := ![1, u, 0, 0] with hsdef
  have hs0 : s ≠ 0 := fun h => by simpa [hsdef] using congrFun h 0
  have hss : herm σ s s = 0 := by
    simp only [herm, hsdef, Fin.sum_univ_four]
    simp
    linear_combination hu
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ (by norm_num) hs0 hss hv0 hv
  have h0s : s 0 = 1 := by simp [hsdef]
  have h2s : s 2 = 0 := by simp [hsdef]
  have h3s : s 3 = 0 := by simp [hsdef]
  obtain ⟨P, hPle, hPab, hPcard, hPscale⟩ :=
    exists_scale_range_T1J3 hp hpq hF hnorm t h0s h2s h3s ht
  exact ⟨P, hPle, hPab, hPcard, fun g hg x => span_stab_T1J3 hPscale g hg x⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
