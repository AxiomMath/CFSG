module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg

namespace PsiDiagChar

section SL2

variable {k : Type*} [Field k]

@[expose] noncomputable def sl2Diag (s : kˣ) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)], by simp [Matrix.det_fin_two]⟩

theorem coe_sl2Diag (s : kˣ) :
    ((sl2Diag s : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)] :=
  rfl

theorem sl2Diag_mul_upper (s : kˣ) (c : k) :
    sl2Diag s * sl2Upper c = sl2Upper ((s : k) ^ 2 * c) * sl2Diag s := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag, CFSG.LieType.Steinberg.coe_sl2Upper,
    Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp
  field_simp

theorem sl2Diag_mul_lower (s : kˣ) (c : k) :
    sl2Diag s * sl2Lower c = sl2Lower (((s⁻¹ : kˣ) : k) ^ 2 * c) * sl2Diag s := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag, CFSG.LieType.Steinberg.coe_sl2Lower,
    Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp
  field_simp

theorem exists_sq_eq [Finite k] [CharP k 2] (e : kˣ) : ∃ s : kˣ, s ^ 2 = e := by
  have hsurj : Function.Surjective fun t : kˣ => t ^ (2 ^ 1) :=
    Finite.injective_iff_surjective.mp (PsiDiag.pow_two_pow_injective (k := k) 1)
  obtain ⟨s, hs⟩ := hsurj e
  exact ⟨s, by simpa using hs⟩

theorem mul_eq_one_of_conj_sl2 [Finite k] [CharP k 2] {G : Type*} [Group G]
    (Φ : Matrix.SpecialLinearGroup (Fin 2) k →* G) (hΦ : Function.Injective Φ) {d : G} (χ : kˣ)
    {χ' : k} (hu : ∀ c, d⁻¹ * Φ (sl2Upper c) * d = Φ (sl2Upper ((χ : k) * c)))
    (hl : ∀ c, d⁻¹ * Φ (sl2Lower c) * d = Φ (sl2Lower (χ' * c))) : (χ : k) * χ' = 1 := by
  obtain ⟨s, hs⟩ := exists_sq_eq χ
  have hs' : ((s : k)) ^ 2 = χ := by rw [← Units.val_pow_eq_pow_val, hs]
  have hsi : (((s⁻¹ : kˣ) : k)) ^ 2 * χ = 1 := by
    rw [← hs', Units.val_inv_eq_inv_val, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 s.ne_zero)]
  have hconj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) k,
      (d * Φ (sl2Diag s))⁻¹ * Φ M * (d * Φ (sl2Diag s)) =
        (Φ (sl2Diag s))⁻¹ * (d⁻¹ * Φ M * d) * Φ (sl2Diag s) := fun M => by group
  refine PsiDiag.eq_one_of_conj_sl2 Φ hΦ (d := d * Φ (sl2Diag s)) (fun c => ?_) (fun c => ?_)
  · rw [hconj, hu, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_assoc, inv_mul_eq_iff_eq_mul, sl2Diag_mul_upper, hs']
  · rw [hconj, hl, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_assoc, inv_mul_eq_iff_eq_mul, sl2Diag_mul_lower]
    congr 2
    calc χ' * c = ((((s⁻¹ : kˣ) : k)) ^ 2 * χ) * χ' * c := by rw [hsi, one_mul]
      _ = (((s⁻¹ : kˣ) : k)) ^ 2 * ((χ : k) * χ' * c) := by ring

end SL2

section Char

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_char_of_ggPsiInnerDiag (hE : ChevalleyExtras D k x C O) [Finite k] [CharP k 2]
    (hlin : ∀ γ ∈ D.roots, ∀ h ∈ ggTorus D, ∃ χ : k, ∀ c, h * x γ c * h⁻¹ = x γ (χ * c))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {c : G}
    (hc : GGPsiInnerDiag D ψ c) :
    ∃ g ∈ ψ.range, ∃ a : Fin D.rank → kˣ, ∀ i t,
      (c * g)⁻¹ * ψ (x (Pi.single i 1) t) * (c * g) =
          ψ (x (Pi.single i 1) ((a i : k) * t)) ∧
        (c * g)⁻¹ * ψ (x (-Pi.single i 1) t) * (c * g) =
          ψ (x (-Pi.single i 1) (((a i)⁻¹ : kˣ) * t)) := by
  obtain ⟨g, hg, hγ⟩ := hc
  have key : ∀ γ ∈ D.roots, ∃ χ : k, ∀ t,
      (c * g)⁻¹ * ψ (x γ t) * (c * g) = ψ (x γ (χ * t)) := by
    intro γ hγr
    obtain ⟨h, hh, hz⟩ := hγ γ hγr
    obtain ⟨χ, hχ⟩ := hlin γ hγr h hh
    exact ⟨χ, fun t => by rw [hz _ (((hE.param γ hγr).1 _).mpr ⟨t, rfl⟩), hχ]⟩
  choose! χ hχ using key
  choose φ hφinj hφu hφl using hE.rankOne
  have hΦ : ∀ i, Function.Injective (ψ.comp (φ i)) := fun i =>
    PsiDiag.injective_comp_of_ker_le_center (φ i) (hφinj i) ψ hker
  have hx0 : ∀ γ ∈ D.roots, x γ 0 = 1 := by
    intro γ hγr
    have h := (hE.param γ hγr).2.1 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hχ0 : ∀ i, χ (Pi.single i 1) ≠ 0 := by
    intro i h0
    have h := hχ _ (single_mem_roots i) 1
    rw [h0, zero_mul, hx0 _ (single_mem_roots i), map_one] at h
    have h' : ψ (x (Pi.single i 1) 1) = 1 := by
      calc ψ (x (Pi.single i 1) 1) =
            (c * g) * ((c * g)⁻¹ * ψ (x (Pi.single i 1) 1) * (c * g)) * (c * g)⁻¹ := by group
        _ = 1 := by rw [h]; group
    have h'' : (ψ.comp (φ i)) (sl2Upper 1) = (ψ.comp (φ i)) 1 := by
      rw [MonoidHom.comp_apply, hφu, h', map_one]
    have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 0 1) (hΦ i h'')
    simp [sl2Upper] at h3
  refine ⟨g, hg, fun i => Units.mk0 (χ (Pi.single i 1)) (hχ0 i), fun i t => ⟨?_, ?_⟩⟩
  · exact hχ _ (single_mem_roots i) t
  · have hm := mul_eq_one_of_conj_sl2 (ψ.comp (φ i)) (hΦ i) (d := c * g)
      (Units.mk0 _ (hχ0 i)) (χ' := χ (-Pi.single i 1))
      (fun c' => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφu, hφu]
        exact hχ _ (single_mem_roots i) c')
      (fun c' => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφl, hφl]
        exact hχ _ (neg_single_mem_roots i) c')
    rw [hχ _ (neg_single_mem_roots i) t, eq_inv_of_mul_eq_one_right hm,
      Units.val_inv_eq_inv_val]

end Char

section E6

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


theorem exists_char_E6 {k : Type} [Field k] [Finite k] [CharP k 2] {G : Type*} [Group G]
    (ψ : ↥(e6Data_valid.minGroup k) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k)) {c : G}
    (hc : GGPsiInnerDiag (e6Datum k) ψ c) :
    ∃ g ∈ ψ.range, ∃ a : Fin (e6Datum k).rank → kˣ, ∀ i t,
      (c * g)⁻¹ * ψ (e6Data_valid.xm k (Pi.single i 1) t) * (c * g) =
          ψ (e6Data_valid.xm k (Pi.single i 1) ((a i : k) * t)) ∧
        (c * g)⁻¹ * ψ (e6Data_valid.xm k (-Pi.single i 1) t) * (c * g) =
          ψ (e6Data_valid.xm k (-Pi.single i 1) (((a i)⁻¹ : kˣ) * t)) := by
  obtain ⟨O⟩ := e6_nonempty_commOrder k
  have hE := (e6Data_valid.minDatum_chevalleyExtras_commC isFiniteType_cartan_E6 k
    posDef_cartan_E6 neighbour_E6 O).2
  refine exists_char_of_ggPsiInnerDiag hE (fun γ hγ h hh => ?_) ψ hker hc
  refine PsiDiag.Minu.conj_xm_eq_of_mem_normalizer e6Data_valid k ?_
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  exact hh γ hγ

end E6

end PsiDiagChar

end CFSG.StandardType
