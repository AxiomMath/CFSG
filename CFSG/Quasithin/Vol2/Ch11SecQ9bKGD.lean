module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open Matrix CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.Vol2.Ch11.SecS CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace C11P9B

variable {K : Type} [Field K]

theorem ringHom_eq_id_or_sq [Finite K] (hK : Nat.card K = 4) (σ : K →+* K) :
    (∀ c, σ c = c) ∨ ∀ c, σ c = c ^ 2 := by
  have h3 : ∀ s : Kˣ, s ^ 3 = 1 := fun s => by
    have h := pow_card_eq_one' (G := Kˣ) (x := s)
    rw [Nat.card_units, hK] at h
    exact h
  have hc3 : ∀ c : K, c ≠ 0 → c ^ 3 = 1 := fun c hc0 => by
    have h := congrArg Units.val (h3 (Units.mk0 c hc0))
    simpa using h
  have hdich : ∀ c : K, c ≠ 0 → c ≠ 1 → σ c = c ∨ σ c = c ^ 2 := by
    intro c hc0 hc1
    have hq : c ^ 2 + c + 1 = 0 := by
      have : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc3 c hc0
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
    have hy : σ c ^ 2 + σ c + 1 = 0 := by
      have := congrArg σ hq
      simpa using this
    have : (σ c - c) * (σ c - c ^ 2) = 0 := by
      linear_combination hy - σ c * hq + hc3 c hc0
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  by_cases hex : ∃ c : K, c ≠ 0 ∧ c ≠ 1 ∧ σ c = c
  · obtain ⟨c₀, h0, h1, hσ0⟩ := hex
    left
    intro c
    by_cases hc : c = 0
    · rw [hc, map_zero]
    have hord : orderOf (Units.mk0 c₀ h0) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp
          (orderOf_dvd_of_pow_eq_one (h3 (Units.mk0 c₀ h0))) with h | h
      · exfalso
        have := congrArg Units.val (orderOf_eq_one_iff.mp h)
        exact h1 (by simpa using this)
      · exact h
    have htop : Subgroup.zpowers (Units.mk0 c₀ h0) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, Nat.card_units, hK])
    have hmem : Units.mk0 c hc ∈ Submonoid.powers (Units.mk0 c₀ h0) :=
      mem_powers_iff_mem_zpowers.mpr (htop ▸ Subgroup.mem_top _)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
    have hck : c = c₀ ^ k := by
      have := congrArg Units.val hk
      simpa using this.symm
    rw [hck, map_pow, hσ0]
  · right
    intro c
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, zero_pow two_ne_zero]
    by_cases hc1 : c = 1
    · rw [hc1, map_one, one_pow]
    exact (hdich c hc0 hc1).resolve_left fun h => hex ⟨c, hc0, hc1, h⟩

theorem matrix_eq_of_mulVec {A B : Matrix (Fin 3) (Fin 3) K} (h : ∀ x, A *ᵥ x = B *ᵥ x) :
    A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h])

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem eq_one_of_act_eq (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) {h : MulAut W}
    (hh : h ∈ H) (hfix : ∀ w, f (h w) = f w) : h = 1 := by
  obtain ⟨A, hA⟩ := (rho3_bijective hf).2 ⟨h, hh⟩
  have hA1 : A = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have hmat : (A : Matrix (Fin 3) (Fin 3) K) = 1 := matrix_eq_of_mulVec fun x => by
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [Matrix.one_mulVec, ← hf.act3, hA]
      exact hfix w
    rw [hmat, Matrix.SpecialLinearGroup.coe_one]
  have := congrArg Subtype.val hA
  rw [hA1, map_one] at this
  exact this.symm

theorem conj_inv_mem_of_conj_mem [Finite W] {τ : MulAut W}
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) : ∀ h ∈ H, τ⁻¹ * h * τ ∈ H := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hmap : H.map (MulAut.conj τ).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj τ).injective).ge
    rintro _ ⟨h, hh, rfl⟩
    exact hτH h hh
  intro h hh
  rw [← hmap] at hh
  obtain ⟨h', hh', rfl⟩ := hh
  have he : τ⁻¹ * (MulAut.conj τ).toMonoidHom h' * τ = h' := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [he]
  exact hh'

theorem exists_mat_conj (T : (Fin 3 → K) →+ (Fin 3 → K)) (hT : ∀ (c : K) x, T (c • x) = c • T x)
    (g : SpecialLinearGroup (Fin 3) K) :
    ∃ Mg : Matrix (Fin 3) (Fin 3) K, ∀ u, Mg *ᵥ u =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u) := by
  let L : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := fun u => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u)
      map_add' := fun u v => by simp only [Matrix.mulVec_add, map_add]
      map_smul' := fun c u => by simp only [Matrix.mulVec_smul, hT, RingHom.id_apply] }
  exact ⟨LinearMap.toMatrix' L, fun u => LinearMap.toMatrix'_mulVec L u⟩

theorem col_mulVec_e0 {X : Matrix (Fin 3) (Fin 3) K} (x10 : X 1 0 = 0) (x20 : X 2 0 = 0) :
    X *ᵥ ![1, 0, 0] = X 0 0 • ![1, 0, 0] :=
  vec3_eq (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three])
    (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, x10])
    (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, x20])

theorem col_zero_of_stab (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) {τ : MulAut W} {T : (Fin 3 → K) →+ (Fin 3 → K)}
    (hTf : ∀ w, T (f w) = f (τ w))
    (hU : τ ∈ stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))
    {Mg : Matrix (Fin 3) (Fin 3) K}
    (hMg : ∀ u, Mg *ᵥ u = ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u)) : Mg 1 0 = 0 ∧ Mg 2 0 = 0 := by
  obtain ⟨w, hw⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  have hw1 : w ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
    show f w ∈ gmap g (flagSpace 3 K 1)
    rw [mem_gmap, hw, ginv_g_mulVec, ← stdLine_eq_flagSpace]
    exact ⟨rfl, rfl⟩
  have h2 : f (τ w) ∈ gmap g (flagSpace 3 K 1) := (hU w).mp hw1
  rw [mem_gmap, ← hTf, hw, ← hMg, ← stdLine_eq_flagSpace] at h2
  obtain ⟨h1, h2⟩ := h2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  exact ⟨h1, h2⟩

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
