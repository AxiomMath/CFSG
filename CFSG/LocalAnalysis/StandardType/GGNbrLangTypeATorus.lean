module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeANorm
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.StandardType

namespace NbrLangTypeA

open Matrix CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

variable {d : ℕ} {F : Type} [Field F]

@[expose] def torusVec (i j : Fin d) (u : Fˣ) : Fin d → Fˣ :=
  Pi.mulSingle i u * Pi.mulSingle j u⁻¹

theorem prod_torusVec (i j : Fin d) (u : Fˣ) : ∏ k, torusVec i j u k = 1 := by
  simp [torusVec, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle']

theorem torusVec_apply (i j : Fin d) (u : Fˣ) (k : Fin d) :
    torusVec i j u k = (if k = i then u else 1) * (if k = j then u⁻¹ else 1) := by
  simp only [torusVec, Pi.mul_apply, Pi.mulSingle_apply]

theorem torusVec_mul (i j : Fin d) (u v : Fˣ) :
    torusVec i j (u * v) = torusVec i j u * torusVec i j v := by
  simp only [torusVec, mul_inv, Pi.mulSingle_mul]
  exact mul_mul_mul_comm (Pi.mulSingle i u : Fin d → Fˣ) (Pi.mulSingle i v)
    (Pi.mulSingle j u⁻¹) (Pi.mulSingle j v⁻¹)

theorem torusVec_one (i j : Fin d) : torusVec i j (1 : Fˣ) = 1 := by
  simp [torusVec]

@[expose] def torusElt (i j : Fin d) (u : Fˣ) : SpecialLinearGroup (Fin d) F :=
  ⟨diagonal fun k => (torusVec i j u k : F), by
    rw [det_diagonal, ← Units.coe_prod, prod_torusVec, Units.val_one]⟩

theorem coe_torusElt (i j : Fin d) (u : Fˣ) :
    (torusElt i j u : Matrix (Fin d) (Fin d) F) = diagonal fun k => (torusVec i j u k : F) :=
  rfl

@[expose] def torusHom (i j : Fin d) : Fˣ →* SpecialLinearGroup (Fin d) F where
  toFun := torusElt i j
  map_one' := by
    apply Subtype.ext
    rw [coe_torusElt, Matrix.SpecialLinearGroup.coe_one, torusVec_one]
    simp
  map_mul' u v := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_torusElt, coe_torusElt, coe_torusElt,
      diagonal_mul_diagonal, torusVec_mul]
    rfl

theorem torusHom_apply (i j : Fin d) (u : Fˣ) :
    (torusHom i j u : Matrix.SpecialLinearGroup (Fin d) F) = torusElt i j u :=
  rfl

theorem slConjugation_torusElt {D : GL (Fin d) F} (hD : (D : Matrix (Fin d) (Fin d) F).IsDiag)
    (i j : Fin d) (u : Fˣ) :
    CatalogueBHigherLinearAction.slConjugation d F D (torusElt i j u) = torusElt i j u := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, coe_torusElt]
  have h1 : diagonal (diag (D : Matrix (Fin d) (Fin d) F)) = D :=
    (isDiag_iff_diagonal_diag _).mp hD
  have hcomm : (D : Matrix (Fin d) (Fin d) F) * diagonal (fun k => (torusVec i j u k : F)) =
      diagonal (fun k => (torusVec i j u k : F)) * D := by
    rw [← h1, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  rw [hcomm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem map_torusElt (σ : F ≃+* F) (i j : Fin d) (u : Fˣ) :
    SpecialLinearGroup.map σ.toRingHom (torusElt i j u) =
      torusElt i j (Units.map (σ : F →* F) u) := by
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_torusElt, coe_torusElt,
    Matrix.map_apply]
  by_cases hab : a = b
  · subst hab
    rw [diagonal_apply_eq, diagonal_apply_eq, torusVec_apply, torusVec_apply]
    split_ifs <;> simp
  · rw [diagonal_apply_ne _ hab, diagonal_apply_ne _ hab, map_zero]

theorem eq_one_of_torusElt_mem_center {i j l : Fin d} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {u : Fˣ} (h : torusElt i j u ∈ Subgroup.center (SpecialLinearGroup (Fin d) F)) : u = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have hl := congrFun (congrFun hr l) l
  have hi := congrFun (congrFun hr i) i
  rw [coe_torusElt, diagonal_apply_eq, scalar_apply, diagonal_apply_eq, torusVec_apply] at hl hi
  rw [ite_eq_right hil.symm, ite_eq_right hjl.symm, mul_one, Units.val_one] at hl
  rw [ite_eq_left rfl, ite_eq_right hij, mul_one] at hi
  exact Units.ext (hi.symm.trans hl)

theorem list_prod_map_range {M : Type*} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).prod = ∏ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
    simp

theorem pow_conj_torusElt {G : Type*} [Group G] (φ : Matrix.SpecialLinearGroup (Fin d) F →* G)
    {σ : F ≃+* F} {b₀ : G} {D₀ : GL (Fin d) F} (hD₀ : (D₀ : Matrix (Fin d) (Fin d) F).IsDiag)
    (hb₀ : ∀ h, b₀ * φ h * b₀⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F D₀
      (Matrix.SpecialLinearGroup.map σ.toRingHom h)))
    (i j : Fin d) (n : ℕ) (v : Fˣ) :
    b₀ ^ n * φ (torusElt i j v) * (b₀ ^ n)⁻¹ =
      φ (torusElt i j (Units.map ((σ ^ n : F ≃+* F) : F →* F) v)) := by
  induction n generalizing v with
  | zero =>
    have h1 : Units.map ((σ ^ 0 : F ≃+* F) : F →* F) v = v := Units.ext rfl
    rw [h1, pow_zero, one_mul, inv_one, mul_one]
  | succ n ih =>
    have h1 : b₀ ^ (n + 1) * φ (torusElt i j v) * (b₀ ^ (n + 1))⁻¹ =
        b₀ * (b₀ ^ n * φ (torusElt i j v) * (b₀ ^ n)⁻¹) * b₀⁻¹ := by group
    have h2 : Units.map (σ : F →* F) (Units.map ((σ ^ n : F ≃+* F) : F →* F) v) =
        Units.map ((σ ^ (n + 1) : F ≃+* F) : F →* F) v := Units.ext (by
      rw [pow_succ']
      rfl)
    rw [h1, ih, hb₀, map_torusElt, slConjugation_torusElt hD₀, h2]

theorem exists_lang_torus {G : Type*} [Group G] [Finite G] [Finite F] {p : ℕ} (hp : p.Prime)
    {i j l : Fin d} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (φ : Matrix.SpecialLinearGroup (Fin d) F →* G)
    (hφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F))
    {σ : F ≃+* F} (hσ : orderOf σ = p) {b₀ : G} {D₀ : GL (Fin d) F}
    (hD₀ : (D₀ : Matrix (Fin d) (Fin d) F).IsDiag)
    (hb₀ : ∀ h, b₀ * φ h * b₀⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F D₀
      (Matrix.SpecialLinearGroup.map σ.toRingHom h)))
    {B₀ : Subgroup G}
    (hB₀ : ∀ b ∈ B₀, ∃ D : GL (Fin d) F, (D : Matrix (Fin d) (Fin d) F).IsDiag ∧
      ∀ h, b * φ h * b⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F D h))
    {ω : Fˣ} (hωσ : σ ω = ω) (hωp : ω ^ p = 1) (hω1 : ω ≠ 1) :
    ∃ T : Subgroup G, T ≤ φ.range ∧ T ≤ Subgroup.centralizer (B₀ : Set G) ∧
      (∀ a ∈ T, ∀ c ∈ T, a * c = c * a) ∧ b₀ ∈ Subgroup.normalizer (T : Set G) ∧
      (∀ t ∈ T, b₀ * t * b₀⁻¹ = t → ∃ s ∈ T,
        t = ((List.range p).map fun i => b₀ ^ i * s * (b₀ ^ i)⁻¹).prod) ∧
      ∃ e ∈ T, e ≠ 1 ∧ b₀ * e * b₀⁻¹ = e ∧ e ^ p = 1 := by
  have hconj : ∀ v : Fˣ, b₀ * φ (torusElt i j v) * b₀⁻¹ =
      φ (torusElt i j (Units.map (σ : F →* F) v)) := fun v => by
    rw [hb₀, map_torusElt, slConjugation_torusElt hD₀]
  refine ⟨(φ.comp (torusHom i j)).range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨D, hD, hbD⟩ := hB₀ b hb
    have h1 := hbD (torusElt i j u)
    rw [slConjugation_torusElt hD] at h1
    change b * φ (torusElt i j u) = φ (torusElt i j u) * b
    calc b * φ (torusElt i j u) = b * φ (torusElt i j u) * b⁻¹ * b := by group
      _ = φ (torusElt i j u) * b := by rw [h1]
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm u v]
  · refine NbrLang.mem_normalizer_of_conj_mem ?_
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map (σ : F →* F) u, (hconj u).symm⟩
  · rintro _ ⟨u, rfl⟩ hfix
    change b₀ * φ (torusElt i j u) * b₀⁻¹ = φ (torusElt i j u) at hfix
    rw [hconj] at hfix
    have hσu : σ (u : F) = u := by
      have h1 : torusElt i j (Units.map (σ : F →* F) u * u⁻¹) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
        apply hφ
        rw [MonoidHom.mem_ker, ← torusHom_apply, map_mul, map_inv, map_mul, map_inv,
          torusHom_apply, torusHom_apply, hfix, mul_inv_cancel]
      have h3 : Units.map (σ : F →* F) u = u :=
        mul_inv_eq_one.mp (eq_one_of_torusElt_mem_center hij hil hjl h1)
      exact congrArg Units.val h3
    obtain ⟨s, hs0, hs⟩ := exists_prod_pow_eq hp hσ hσu u.ne_zero
    refine ⟨φ (torusElt i j (Units.mk0 s hs0)), ⟨Units.mk0 s hs0, rfl⟩, ?_⟩
    have h1 : ∀ n : ℕ, b₀ ^ n * φ (torusElt i j (Units.mk0 s hs0)) * (b₀ ^ n)⁻¹ =
        (φ.comp (torusHom i j)) (Units.map ((σ ^ n : F ≃+* F) : F →* F) (Units.mk0 s hs0)) :=
      fun n => pow_conj_torusElt φ hD₀ hb₀ i j n _
    simp_rw [h1]
    set g : ℕ → Fˣ := fun n => Units.map ((σ ^ n : F ≃+* F) : F →* F) (Units.mk0 s hs0) with hg
    have h2 : ((List.range p).map fun n => (φ.comp (torusHom i j)) (g n)).prod =
        (φ.comp (torusHom i j)) (((List.range p).map g).prod) := by
      rw [map_list_prod, List.map_map]
      rfl
    rw [h2, list_prod_map_range]
    change φ (torusElt i j u) = φ (torusElt i j _)
    congr 2
    apply Units.ext
    rw [Units.coe_prod, ← hs]
    rfl
  · refine ⟨φ (torusElt i j ω), ⟨ω, rfl⟩, fun he => ?_, ?_, ?_⟩
    · exact hω1 (eq_one_of_torusElt_mem_center hij hil hjl (hφ he))
    · rw [hconj]
      congr 2
      exact Units.ext hωσ
    · rw [← torusHom_apply, ← map_pow, ← map_pow, hωp, map_one, map_one]

end NbrLangTypeA

end CFSG.StandardType

end
