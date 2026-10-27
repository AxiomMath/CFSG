module

public import CFSG.LocalAnalysis.StandardType.KGLangTorALinLift
import CFSG.LocalAnalysis.StandardType.KGLangTorALangElt
import CFSG.LocalAnalysis.StandardType.GGPGLToralityMain
import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeATorus
import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeAFrame
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem kgLangTorALinCoreAux_toGL_map {d : ℕ} {F F' : Type} [Field F] [Field F']
    (f : F →+* F') (g : Matrix.SpecialLinearGroup (Fin d) F) :
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map f g) : GL (Fin d) F') =
      Matrix.GeneralLinearGroup.map f (Matrix.SpecialLinearGroup.toGL g) := Units.ext rfl

private theorem kgLangTorALinCoreAux_map_slConjugation {d : ℕ} {F : Type} [Field F]
    (σ : F ≃+* F) (A : GL (Fin d) F) (g : Matrix.SpecialLinearGroup (Fin d) F) :
    Matrix.SpecialLinearGroup.map σ.toRingHom
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F A g) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F
        (Matrix.GeneralLinearGroup.map (σ : F →+* F) A)
        (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  conv_lhs =>
    rw [kgLangTorALinCoreAux_toGL_map,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      map_mul, map_mul, map_inv]
  conv_rhs =>
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      kgLangTorALinCoreAux_toGL_map]
  rfl

private theorem kgLangTorALinCoreAux_isDiag_map {d : ℕ} {F F' : Type} [Field F] [Field F']
    (f : F →+* F') {M : Matrix (Fin d) (Fin d) F} (hM : M.IsDiag) :
    (f.mapMatrix M).IsDiag := by
  intro i j hij
  change M.map (⇑f) i j = 0
  rw [Matrix.map_apply, hM hij, map_zero]

theorem kgLangTorA_lin_core_split {d n p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hd : 3 ≤ d)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LinearFlag.projectiveSL d F))} (hX : IsElemAbelian p X)
    (hXc : ∀ x ∈ X, x ∈ Set.range (LinearFlag.conjAut d F))
    (hXσ : ∀ x ∈ X, LinearFlag.fieldAut d F σ * x = x * LinearFlag.fieldAut d F σ)
    (hsplit : p ∣ 2 ^ n - 1) (hcard : p ^ (d / p + 2) ≤ Nat.card X) :
    ∃ e s : Matrix.SpecialLinearGroup (Fin d) F,
      Matrix.SpecialLinearGroup.map σ.toRingHom e = e ∧ e ^ p = 1 ∧
      e ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) ∧
      Matrix.SpecialLinearGroup.map σ.toRingHom s = s * e ∧
      ∀ B : GL (Fin d) F, LinearFlag.conjAut d F B ∈ X →
        B * Matrix.SpecialLinearGroup.toGL e = Matrix.SpecialLinearGroup.toGL e * B ∧
        B * Matrix.SpecialLinearGroup.toGL s = Matrix.SpecialLinearGroup.toGL s * B := by
  classical
  have hd0 : 0 < d := by omega
  obtain ⟨hpdvdn, hF0⟩ := kgLangTorA_card_fixed_linear hn hF hσ
  set q₀ : ℕ := 2 ^ (n / p) with hq₀
  have hF0q : Nat.card (semilinearFixedSubfield σ) = q₀ := by rw [hF0, hq₀]
  have hnpad : 1 ≤ n / p := by
    obtain ⟨k, hk⟩ := hpdvdn
    have hk1 : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      omega
    rw [hk, Nat.mul_div_right k hp.pos]
    exact hk1
  have hq₀2 : 2 ≤ q₀ := by
    rw [hq₀]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n / p) := Nat.pow_le_pow_right (by norm_num) hnpad
  have hq₀1 : 1 ≤ q₀ := by omega
  have hq₀pos : 0 < q₀ - 1 := by omega
  have h2np : 2 ^ n = q₀ ^ p := by
    obtain ⟨k, hk⟩ := hpdvdn
    rw [hq₀, hk, Nat.mul_div_right k hp.pos, ← pow_mul, mul_comm]
  have hpq0 : p ∣ q₀ - 1 := by
    apply NbrLangTypeA.dvd_sub_one_of_dvd_pow_sub_one hp hq₀1
    rwa [← h2np]
  have hpF₀ : p ∣ Nat.card (semilinearFixedSubfield σ) - 1 := by
    rw [hF0q]
    exact hpq0
  obtain ⟨hproj, hcardG⟩ := kgLangTorA_lin_fixed_group hp hd0 hσ hX hXc hXσ
  let G : Subgroup (GL (Fin d) (semilinearFixedSubfield σ)) :=
    X.comap ((LinearFlag.conjAut d F).comp
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype))
  have hprojG : TypeA.PGLTor.IsProjElem p G := hproj
  have hcardG' : Nat.card G = Nat.card X * (q₀ - 1) := by rw [hcardG, hF0q]
  have htor : TypeA.PGLTor.IsToral G := by
    rcases TypeA.PGLTor.toral_or_card_le (K := semilinearFixedSubfield σ) hp hp2 hpF₀ hprojG
      with h | h
    · exact h
    · exfalso
      rw [hF0q, Fintype.card_fin] at h
      have hle2 : Nat.card X * (q₀ - 1) ≤ p ^ (d / p + 1) * (q₀ - 1) := by
        rw [← hcardG']
        exact h
      have hXle : Nat.card X ≤ p ^ (d / p + 1) := Nat.le_of_mul_le_mul_right hle2 hq₀pos
      have hlt : p ^ (d / p + 1) < p ^ (d / p + 2) :=
        Nat.pow_lt_pow_right hp.one_lt (by omega)
      exact (not_le.mpr hlt) (le_trans hcard hXle)
  obtain ⟨A, hA⟩ := htor
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let i2 : Fin d := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have h' := congrArg Fin.val h
    simp only [i0, i1] at h'
    omega
  have h02 : i0 ≠ i2 := by
    intro h
    have h' := congrArg Fin.val h
    simp only [i0, i2] at h'
    omega
  have h12 : i1 ≠ i2 := by
    intro h
    have h' := congrArg Fin.val h
    simp only [i1, i2] at h'
    omega
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := semilinearFixedSubfield σ) hp hpF₀
  let ω' : Fˣ := Units.mk0 ((ζ : semilinearFixedSubfield σ) : F)
    (fun h => hζ.ne_zero hp.ne_zero
      ((semilinearFixedSubfield σ).subtype_injective (by rw [map_zero]; exact h)))
  have hω'σ : σ (ω' : F) = (ω' : F) := by
    have hfix := RingHom.mem_eqLocusField.mp (ζ : semilinearFixedSubfield σ).2
    simpa [ω'] using hfix
  have hω'p : ω' ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (semilinearFixedSubfield σ).subtype ζ ^ p = 1
    rw [← map_pow (semilinearFixedSubfield σ).subtype, hζ.pow_eq_one, map_one]
  have hω'pF : (ω' : F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω'p, Units.val_one]
  have hω'1 : ω' ≠ 1 := by
    intro h
    have hval := congrArg Units.val h
    have hζ1 : ζ = 1 := (semilinearFixedSubfield σ).subtype_injective (by
      simpa [ω'] using hval)
    exact hζ.ne_one hp.one_lt hζ1
  obtain ⟨u, hu⟩ := kgLangTorA_hilbert90 hp hσ hω'σ hω'pF
  let Â : GL (Fin d) F :=
    Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype A
  have hσÂ : Matrix.GeneralLinearGroup.map (σ : F →+* F) Â = Â := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F)
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype A) = _
    simpa using NbrLangTypeA.map_pow_map_subtype (σ := σ) A 1
  let e : Matrix.SpecialLinearGroup (Fin d) F :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹ (NbrLangTypeA.torusElt i0 i1 ω')
  let s : Matrix.SpecialLinearGroup (Fin d) F :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹ (NbrLangTypeA.torusElt i0 i1 u)
  have htoGLe : (Matrix.SpecialLinearGroup.toGL e : GL (Fin d) F) =
      Â⁻¹ * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 ω') * Â := by
    show (Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
        (NbrLangTypeA.torusElt i0 i1 ω')) : GL (Fin d) F) = _
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, inv_inv]
  have htoGLs : (Matrix.SpecialLinearGroup.toGL s : GL (Fin d) F) =
      Â⁻¹ * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 u) * Â := by
    show (Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
        (NbrLangTypeA.torusElt i0 i1 u)) : GL (Fin d) F) = _
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, inv_inv]
  have htωp : NbrLangTypeA.torusElt i0 i1 ω' ^ p = 1 := by
    rw [← NbrLangTypeA.torusHom_apply, ← map_pow, hω'p, map_one]
  have hep_e : e ^ p = 1 := by
    show (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
      (NbrLangTypeA.torusElt i0 i1 ω')) ^ p = 1
    rw [← map_pow (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹), htωp, map_one]
  have he_fixed : Matrix.SpecialLinearGroup.map σ.toRingHom e = e := by
    show Matrix.SpecialLinearGroup.map σ.toRingHom
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
        (NbrLangTypeA.torusElt i0 i1 ω')) = e
    rw [kgLangTorALinCoreAux_map_slConjugation]
    rw [map_inv, hσÂ]
    rw [NbrLangTypeA.map_torusElt]
    have hσu : Units.map (σ : F →* F) ω' = ω' := Units.ext hω'σ
    rw [hσu]
  have hes : s * e = e * s := by
    show (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
        (NbrLangTypeA.torusElt i0 i1 u)) *
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
          (NbrLangTypeA.torusElt i0 i1 ω')) =
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
          (NbrLangTypeA.torusElt i0 i1 ω')) *
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
          (NbrLangTypeA.torusElt i0 i1 u))
    change (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
        (NbrLangTypeA.torusHom i0 i1 u)) *
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
          (NbrLangTypeA.torusHom i0 i1 ω')) =
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
          (NbrLangTypeA.torusHom i0 i1 ω')) *
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
          (NbrLangTypeA.torusHom i0 i1 u))
    simp only [← map_mul]
    exact congrArg (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹)
      (congrArg (NbrLangTypeA.torusHom i0 i1) (mul_comm u ω'))
  have hsσ' : Matrix.SpecialLinearGroup.map σ.toRingHom s = s * e := by
    show Matrix.SpecialLinearGroup.map σ.toRingHom
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
        (NbrLangTypeA.torusElt i0 i1 u)) = s * e
    rw [kgLangTorALinCoreAux_map_slConjugation]
    rw [map_inv, hσÂ]
    rw [NbrLangTypeA.map_torusElt]
    have hσu : Units.map (σ : F →* F) u = ω' * u := Units.ext hu
    rw [hσu]
    change (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹)
        (NbrLangTypeA.torusHom i0 i1 (ω' * u)) = s * e
    rw [map_mul]
    rw [map_mul]
    exact hes.symm
  have he_notcenter : e ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    intro hec
    have h1 : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â) e ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) :=
      (Subgroup.map_center_eq (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â)).symm ▸
        Subgroup.mem_map_of_mem _ hec
    have h2 : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â) e =
        NbrLangTypeA.torusElt i0 i1 ω' := by
      show (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â)
        ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹)
          (NbrLangTypeA.torusElt i0 i1 ω')) = _
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [h2] at h1
    exact hω'1 (NbrLangTypeA.eq_one_of_torusElt_mem_center h01 h02 h12 h1)
  refine ⟨e, s, he_fixed, hep_e, he_notcenter, hsσ', ?_⟩
  intro B' hB'
  obtain ⟨c, M, hM⟩ := kgLangTorA_lin_descend_lift hp hd0 hσ B' (hXσ _ hB')
  have hconjMgl : LinearFlag.conjAut d F
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M) =
      LinearFlag.conjAut d F B' := by
    have h := congrArg (LinearFlag.conjAut d F) hM
    rw [map_mul, LinearFlag.conjAut_scalar, one_mul] at h
    exact h.symm
  have hMG : M ∈ G := by
    show M ∈ X.comap ((LinearFlag.conjAut d F).comp
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype))
    rw [Subgroup.mem_comap]
    show LinearFlag.conjAut d F
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M) ∈ X
    rw [hconjMgl]
    exact hB'
  let Mgl : GL (Fin d) F :=
    Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M
  let D : GL (Fin d) F :=
    Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype (A * M * A⁻¹)
  have hD_eq : D = Â * Mgl * Â⁻¹ := by
    show Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype (A * M * A⁻¹) =
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype A *
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype M *
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype A)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hDdiag : (D : Matrix (Fin d) (Fin d) F).IsDiag := by
    show (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
      (A * M * A⁻¹) : Matrix (Fin d) (Fin d) F).IsDiag
    exact kgLangTorALinCoreAux_isDiag_map (semilinearFixedSubfield σ).subtype (hA M hMG)
  have hMglD : Mgl = Â⁻¹ * D * Â := by rw [hD_eq]; group
  have hcomm_torus : ∀ x : Fˣ, Mgl * Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
        (NbrLangTypeA.torusElt i0 i1 x)) =
      Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
          (NbrLangTypeA.torusElt i0 i1 x)) * Mgl := by
    intro x
    have hDx : D * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) =
        Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) * D := by
      have h1 := NbrLangTypeA.slConjugation_torusElt hDdiag i0 i1 x
      have h2 : Matrix.SpecialLinearGroup.toGL
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F D
            (NbrLangTypeA.torusElt i0 i1 x)) =
          D * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) * D⁻¹ :=
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation d F D
          (NbrLangTypeA.torusElt i0 i1 x)
      rw [h1] at h2
      calc D * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) =
            (D * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) * D⁻¹) * D :=
              by group
        _ = Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) * D := by
              rw [← h2]
    have hto : (Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
          (NbrLangTypeA.torusElt i0 i1 x)) : GL (Fin d) F) =
        Â⁻¹ * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) * Â := by
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, inv_inv]
    rw [hto, hMglD]
    calc Â⁻¹ * D * Â * (Â⁻¹ * Matrix.SpecialLinearGroup.toGL
          (NbrLangTypeA.torusElt i0 i1 x) * Â) =
          Â⁻¹ * (D * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x)) * Â :=
            by group
      _ = Â⁻¹ * (Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) * D) * Â := by
            rw [hDx]
      _ = (Â⁻¹ * Matrix.SpecialLinearGroup.toGL (NbrLangTypeA.torusElt i0 i1 x) * Â) *
          (Â⁻¹ * D * Â) := by group
  have hMgl_e := hcomm_torus ω'
  have hMgl_s := hcomm_torus u
  refine ⟨?_, ?_⟩
  · rw [hM]
    calc Matrix.GeneralLinearGroup.scalar (Fin d) c * Mgl *
          Matrix.SpecialLinearGroup.toGL e =
          Matrix.GeneralLinearGroup.scalar (Fin d) c *
            (Mgl * Matrix.SpecialLinearGroup.toGL e) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) c *
            (Matrix.SpecialLinearGroup.toGL e * Mgl) := by rw [hMgl_e]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c *
            Matrix.SpecialLinearGroup.toGL e) * Mgl := by group
      _ = (Matrix.SpecialLinearGroup.toGL e *
            Matrix.GeneralLinearGroup.scalar (Fin d) c) * Mgl := by
            rw [(TypeA.commute_scalar_GL c (Matrix.SpecialLinearGroup.toGL e)).eq]
      _ = Matrix.SpecialLinearGroup.toGL e *
            (Matrix.GeneralLinearGroup.scalar (Fin d) c * Mgl) := by group
  · rw [hM]
    calc Matrix.GeneralLinearGroup.scalar (Fin d) c * Mgl *
          Matrix.SpecialLinearGroup.toGL s =
          Matrix.GeneralLinearGroup.scalar (Fin d) c *
            (Mgl * Matrix.SpecialLinearGroup.toGL s) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) c *
            (Matrix.SpecialLinearGroup.toGL s * Mgl) := by rw [hMgl_s]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c *
            Matrix.SpecialLinearGroup.toGL s) * Mgl := by group
      _ = (Matrix.SpecialLinearGroup.toGL s *
            Matrix.GeneralLinearGroup.scalar (Fin d) c) * Mgl := by
            rw [(TypeA.commute_scalar_GL c (Matrix.SpecialLinearGroup.toGL s)).eq]
      _ = Matrix.SpecialLinearGroup.toGL s *
            (Matrix.GeneralLinearGroup.scalar (Fin d) c * Mgl) := by group

private theorem kgLangTorALinCoreAux_units_pow_dvd {F : Type} [Field F] [Finite F]
    (u : Fˣ) {m N : ℕ} (hm : Nat.card F - 1 = m) (hN : m ∣ N) : u ^ N = 1 := by
  have h : u ^ Nat.card Fˣ = 1 := pow_card_eq_one'
  rw [Nat.card_units F, hm] at h
  obtain ⟨k, rfl⟩ := hN
  rw [pow_mul, h, one_pow]

private theorem kgLangTorALinCoreAux_commute_lift {d p m : ℕ} {F : Type} [Field F] [Finite F]
    {X : Subgroup (MulAut (LinearFlag.projectiveSL d F))} (hX : IsElemAbelian p X)
    (hd : 0 < d) (hp : p.Prime) (hcop : Nat.Coprime p m)
    (hpow : ∀ u : Fˣ, u ^ m = 1)
    {eB : GL (Fin d) F} (hep : eB ^ p = 1)
    {x : MulAut (LinearFlag.projectiveSL d F)} (heBx : LinearFlag.conjAut d F eB = x)
    (hxX : x ∈ X) :
    ∀ B : GL (Fin d) F, LinearFlag.conjAut d F B ∈ X → B * eB = eB * B := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro B hBX
  have hcommx : LinearFlag.conjAut d F B * x = x * LinearFlag.conjAut d F B :=
    congrArg Subtype.val (hX.1.is_comm.comm ⟨LinearFlag.conjAut d F B, hBX⟩ ⟨x, hxX⟩)
  have hconj1 : LinearFlag.conjAut d F (B * eB * B⁻¹ * eB⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [heBx, hcommx]
    group
  obtain ⟨r, hrmat⟩ := TypeA.exists_scalar_of_conjAut_eq_one hconj1
  obtain ⟨ζ, hζ⟩ := TypeA.exists_unit_of_scalar hd hrmat
  have hBe : B * eB * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * eB := by
    rw [← hζ]
    group
  have hzp : ζ ^ p = 1 := by
    have h1 : (B * eB * B⁻¹) ^ p = 1 := by
      rw [conj_pow, hep, mul_one, mul_inv_cancel]
    have h2 : (Matrix.GeneralLinearGroup.scalar (Fin d) ζ * eB) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ p) := by
      rw [(TypeA.commute_scalar_GL ζ eB).mul_pow, ← map_pow, hep, mul_one]
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ p) = 1 := by
      rw [← h2, ← hBe]
      exact h1
    exact TypeA.PGLTor.scalar_injective (by rw [h3, map_one])
  have hzm : ζ ^ m = 1 := hpow ζ
  have hζ1 : ζ = 1 := by
    have hg : ζ ^ Nat.gcd p m = 1 := (pow_gcd_eq_one).mpr ⟨hzp, hzm⟩
    rw [Nat.coprime_iff_gcd_eq_one.mpr hcop, pow_one] at hg
    exact hg
  calc B * eB = (B * eB * B⁻¹) * B := by group
    _ = (Matrix.GeneralLinearGroup.scalar (Fin d) ζ * eB) * B := by rw [hBe]
    _ = eB * B := by rw [hζ1, map_one, one_mul]

theorem kgLangTorA_lin_core_nonsplit {d n p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hd : 3 ≤ d)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LinearFlag.projectiveSL d F))} (hX : IsElemAbelian p X)
    (hXc : ∀ x ∈ X, x ∈ Set.range (LinearFlag.conjAut d F))
    (hXσ : ∀ x ∈ X, LinearFlag.fieldAut d F σ * x = x * LinearFlag.fieldAut d F σ)
    (hns : ¬ p ∣ 2 ^ n - 1) (hcard : 1 < Nat.card X) :
    ∃ e s : Matrix.SpecialLinearGroup (Fin d) F,
      Matrix.SpecialLinearGroup.map σ.toRingHom e = e ∧ e ^ p = 1 ∧
      e ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) ∧
      Matrix.SpecialLinearGroup.map σ.toRingHom s = s * e ∧
      ∀ B : GL (Fin d) F, LinearFlag.conjAut d F B ∈ X →
        B * Matrix.SpecialLinearGroup.toGL e = Matrix.SpecialLinearGroup.toGL e * B ∧
        B * Matrix.SpecialLinearGroup.toGL s = Matrix.SpecialLinearGroup.toGL s * B := by
  classical
  have hd0 : 0 < d := by omega
  have hp2le : 2 ≤ p := hp.two_le
  have hm2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set m : ℕ := 2 ^ n - 1 with hm
  have hmpos : 0 < m := by rw [hm]; omega
  have hmcard : Nat.card F - 1 = m := by rw [hF, hm]
  have hmnot : ¬ p ∣ m := by rw [hm]; exact hns
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hmnot
  set N : ℕ := m ^ (p - 1) with hN
  have hNm : m ∣ N := by
    rw [hN]
    simpa using pow_dvd_pow m (show 1 ≤ p - 1 by omega)
  have hfermat : m ^ (p - 1) ≡ 1 [MOD p] := by
    simpa [Nat.totient_prime hp] using Nat.ModEq.pow_totient hcop.symm
  have hNmod : N % p = 1 := by
    rw [hN]
    have h := hfermat
    rw [Nat.ModEq] at h
    rwa [Nat.mod_eq_of_lt hp.one_lt] at h
  have hpowe : ∀ u : Fˣ, u ^ m = 1 := by
    intro u
    have h : u ^ Nat.card Fˣ = 1 := pow_card_eq_one'
    rwa [Nat.card_units F, hmcard] at h
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨x, hxX⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hXne
  have hxne : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨B, hBx⟩ := hXc x hxX
  have hσB : LinearFlag.fieldAut d F σ * LinearFlag.conjAut d F B =
      LinearFlag.conjAut d F B * LinearFlag.fieldAut d F σ := by
    rw [hBx]
    exact hXσ x hxX
  obtain ⟨c, hc⟩ := kgLangTorA_lin_semifixed hd0 σ B hσB
  have hxpow : x ^ p = 1 := hX.2 x hxX
  have hBp : LinearFlag.conjAut d F (B ^ p) = 1 := by rw [map_pow, hBx, hxpow]
  obtain ⟨lamc, hlamc⟩ := TypeA.exists_scalar_of_conjAut_eq_one hBp
  obtain ⟨lam, hlam⟩ := TypeA.exists_unit_of_scalar hd0 hlamc
  have hcn : c ^ N = 1 := kgLangTorALinCoreAux_units_pow_dvd c hmcard hNm
  have hlamn : lam ^ N = 1 := kgLangTorALinCoreAux_units_pow_dvd lam hmcard hNm
  let eB : GL (Fin d) F := B ^ N
  have hep : eB ^ p = 1 := by
    show (B ^ N) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hlam, ← map_pow, hlamn, map_one]
  have hσe : Matrix.GeneralLinearGroup.map (σ : F →+* F) eB = eB := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F) (B ^ N) = B ^ N
    rw [map_pow, hc, (TypeA.commute_scalar_GL c B).mul_pow, ← map_pow, hcn, map_one, one_mul]
  have hconje : LinearFlag.conjAut d F eB = x := by
    show LinearFlag.conjAut d F (B ^ N) = x
    rw [map_pow, hBx, pow_eq_pow_mod N hxpow, hNmod, pow_one]
  have hdeteB : Matrix.GeneralLinearGroup.det eB = 1 := by
    show Matrix.GeneralLinearGroup.det (B ^ N) = 1
    rw [map_pow]
    exact kgLangTorALinCoreAux_units_pow_dvd (Matrix.GeneralLinearGroup.det B) hmcard hNm
  have hdeteB' : (eB : Matrix (Fin d) (Fin d) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdeteB, Units.val_one]
  let e : Matrix.SpecialLinearGroup (Fin d) F := ⟨(eB : Matrix (Fin d) (Fin d) F), hdeteB'⟩
  have htoGLe : Matrix.SpecialLinearGroup.toGL e = eB := Units.ext rfl
  have hep_e : e ^ p = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, htoGLe, hep, map_one]
  have he_fixed : Matrix.SpecialLinearGroup.map σ.toRingHom e = e := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hmap : (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map σ.toRingHom e) : GL (Fin d) F) =
        Matrix.GeneralLinearGroup.map (σ : F →+* F) (Matrix.SpecialLinearGroup.toGL e) :=
      Units.ext rfl
    rw [hmap, htoGLe, hσe]
  have he_notcenter : e ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    intro hec
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hec
    have heBmat : (eB : Matrix (Fin d) (Fin d) F) = Matrix.scalar (Fin d) r := by
      have h1 : (↑e : Matrix (Fin d) (Fin d) F) = (eB : Matrix (Fin d) (Fin d) F) := rfl
      rw [h1] at hr
      exact hr.symm
    obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar hd0 heBmat
    have h1 : LinearFlag.conjAut d F eB = 1 := by rw [hu, LinearFlag.conjAut_scalar]
    rw [hconje] at h1
    exact hxne h1
  have hcommE : ∀ B' : GL (Fin d) F, LinearFlag.conjAut d F B' ∈ X → B' * eB = eB * B' :=
    kgLangTorALinCoreAux_commute_lift hX hd0 hp hcop hpowe hep hconje hxX
  obtain ⟨s₀, P, hs₀P, hs₀σ⟩ := kgLangTorA_lang_poly hp hσ hσe hep
  have hs₀P' : (s₀ : Matrix (Fin d) (Fin d) F) = P.smeval (eB : Matrix (Fin d) (Fin d) F) := by
    rw [hs₀P, Polynomial.aeval_eq_smeval]
  have hs₀e_mat : (s₀ : Matrix (Fin d) (Fin d) F) * (eB : Matrix (Fin d) (Fin d) F) =
      (eB : Matrix (Fin d) (Fin d) F) * (s₀ : Matrix (Fin d) (Fin d) F) := by
    rw [hs₀P']
    exact (Polynomial.smeval_commute_left F P
      (Commute.refl (eB : Matrix (Fin d) (Fin d) F))).eq
  have hs₀e : s₀ * eB = eB * s₀ := Units.ext hs₀e_mat
  have hsσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) (s₀ ^ N) = s₀ ^ N * eB :=
    kgLangTorA_pow_lang hs₀e hep hs₀σ hNmod
  let sGL : GL (Fin d) F := s₀ ^ N
  have hdets : Matrix.GeneralLinearGroup.det sGL = 1 := by
    show Matrix.GeneralLinearGroup.det (s₀ ^ N) = 1
    rw [map_pow]
    exact kgLangTorALinCoreAux_units_pow_dvd (Matrix.GeneralLinearGroup.det s₀) hmcard hNm
  have hdets' : (sGL : Matrix (Fin d) (Fin d) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdets, Units.val_one]
  let s : Matrix.SpecialLinearGroup (Fin d) F := ⟨(sGL : Matrix (Fin d) (Fin d) F), hdets'⟩
  have htoGLs : Matrix.SpecialLinearGroup.toGL s = sGL := Units.ext rfl
  have hsσ'' : Matrix.SpecialLinearGroup.map σ.toRingHom s = s * e := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hmap : (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map σ.toRingHom s) : GL (Fin d) F) =
        Matrix.GeneralLinearGroup.map (σ : F →+* F) (Matrix.SpecialLinearGroup.toGL s) :=
      Units.ext rfl
    rw [hmap, map_mul, htoGLs, htoGLe, hsσ]
  have hcommS : ∀ B' : GL (Fin d) F, LinearFlag.conjAut d F B' ∈ X → sGL * B' = B' * sGL := by
    intro B' hB'
    have hB'e : B' * eB = eB * B' := hcommE B' hB'
    have hcemat_eq : (B' : Matrix (Fin d) (Fin d) F) * (eB : Matrix (Fin d) (Fin d) F) =
        (eB : Matrix (Fin d) (Fin d) F) * (B' : Matrix (Fin d) (Fin d) F) := by
      have h := congrArg (fun z : GL (Fin d) F => (z : Matrix (Fin d) (Fin d) F)) hB'e
      simpa only [Units.val_mul] using h
    have hcemat : Commute (B' : Matrix (Fin d) (Fin d) F) (eB : Matrix (Fin d) (Fin d) F) :=
      (commute_iff_eq _ _).mpr hcemat_eq
    have hs₀B_mat : Commute (s₀ : Matrix (Fin d) (Fin d) F) (B' : Matrix (Fin d) (Fin d) F) := by
      rw [hs₀P']
      exact Polynomial.smeval_commute_left F P hcemat.symm
    have hsGL_mat : Commute (sGL : Matrix (Fin d) (Fin d) F) (B' : Matrix (Fin d) (Fin d) F) := by
      have hpow : Commute ((s₀ : Matrix (Fin d) (Fin d) F) ^ N)
          (B' : Matrix (Fin d) (Fin d) F) := hs₀B_mat.pow_left N
      have hv : (sGL : Matrix (Fin d) (Fin d) F) = (s₀ : Matrix (Fin d) (Fin d) F) ^ N := by
        show (↑(s₀ ^ N) : Matrix (Fin d) (Fin d) F) = _
        rw [Units.val_pow_eq_pow_val]
      rwa [hv]
    exact Units.ext hsGL_mat.eq
  refine ⟨e, s, he_fixed, hep_e, he_notcenter, hsσ'', ?_⟩
  intro B' hB'
  refine ⟨?_, ?_⟩
  · have h := hcommE B' hB'
    rwa [← htoGLe] at h
  · have h := hcommS B' hB'
    rw [← htoGLs] at h
    exact h.symm

theorem kgLangTorA_lin_core {d n p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hd : 3 ≤ d)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LinearFlag.projectiveSL d F))} (hX : IsElemAbelian p X)
    (hXc : ∀ x ∈ X, x ∈ Set.range (LinearFlag.conjAut d F))
    (hXσ : ∀ x ∈ X, LinearFlag.fieldAut d F σ * x = x * LinearFlag.fieldAut d F σ)
    (hcard : 1 < Nat.card X) (hsplit : p ∣ 2 ^ n - 1 → p ^ (d / p + 2) ≤ Nat.card X) :
    ∃ e s : Matrix.SpecialLinearGroup (Fin d) F,
      Matrix.SpecialLinearGroup.map σ.toRingHom e = e ∧ e ^ p = 1 ∧
      e ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) ∧
      Matrix.SpecialLinearGroup.map σ.toRingHom s = s * e ∧
      ∀ B : GL (Fin d) F, LinearFlag.conjAut d F B ∈ X →
        B * Matrix.SpecialLinearGroup.toGL e = Matrix.SpecialLinearGroup.toGL e * B ∧
        B * Matrix.SpecialLinearGroup.toGL s = Matrix.SpecialLinearGroup.toGL s * B := by
  by_cases h : p ∣ 2 ^ n - 1
  · exact kgLangTorA_lin_core_split hp hp2 hn hF hd hσ hX hXc hXσ h (hsplit h)
  · exact kgLangTorA_lin_core_nonsplit hp hp2 hn hF hd hσ hX hXc hXσ h hcard

end CFSG.StandardType
