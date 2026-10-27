module

public import CFSG.LocalAnalysis.StandardType.KGLangTorALinLift
import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeAFrame
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinWeight

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem kgLangS1ALinCoreAux_toGL_map {d : ℕ} {F F' : Type} [Field F] [Field F']
    (f : F →+* F') (g : Matrix.SpecialLinearGroup (Fin d) F) :
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map f g) : GL (Fin d) F') =
      Matrix.GeneralLinearGroup.map f (Matrix.SpecialLinearGroup.toGL g) := Units.ext rfl

private theorem kgLangS1ALinCoreAux_map_slConjugation {d : ℕ} {F : Type} [Field F]
    (σ : F ≃+* F) (A : GL (Fin d) F) (g : Matrix.SpecialLinearGroup (Fin d) F) :
    Matrix.SpecialLinearGroup.map σ.toRingHom
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F A g) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F
        (Matrix.GeneralLinearGroup.map (σ : F →+* F) A)
        (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  conv_lhs =>
    rw [kgLangS1ALinCoreAux_toGL_map,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      map_mul, map_mul, map_inv]
  conv_rhs =>
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      kgLangS1ALinCoreAux_toGL_map]
  rfl

private theorem kgLangS1ALinCoreAux_prod_zpow_eq_zpow_sum {ι G : Type*} [CommGroup G]
    (s : Finset ι) (y : G) (e : ι → ℤ) :
    s.prod (fun i => y ^ e i) = y ^ s.sum e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← zpow_add]

private theorem kgLangS1ALinCoreAux_zpow_pow_eq_one {G : Type*} [Group G] (u : G) {p : ℕ}
    (hp : u ^ p = 1) (n : ℤ) : (u ^ n) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp, one_zpow]

private def kgLangS1ALinCoreAux_diagElt {d : ℕ} {F : Type} [Field F]
    (w : Fin d → Fˣ) (hw : ∏ i, w i = 1) : Matrix.SpecialLinearGroup (Fin d) F :=
  ⟨Matrix.diagonal fun i => (w i : F), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, hw, Units.val_one]⟩

private theorem kgLangS1ALinCoreAux_coe_diagElt {d : ℕ} {F : Type} [Field F]
    (w : Fin d → Fˣ) (hw : ∏ i, w i = 1) :
    (kgLangS1ALinCoreAux_diagElt w hw : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal fun i => (w i : F) := rfl

private theorem kgLangS1ALinCoreAux_diagElt_pow {d : ℕ} {F : Type} [Field F]
    (w : Fin d → Fˣ) (hw : ∏ i, w i = 1) {p : ℕ} (hp : ∀ i, w i ^ p = 1) :
    kgLangS1ALinCoreAux_diagElt w hw ^ p = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_pow, kgLangS1ALinCoreAux_coe_diagElt,
    Matrix.diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.pow_apply,
      ← Units.val_pow_eq_pow_val, hp i, Units.val_one]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

private theorem kgLangS1ALinCoreAux_map_diagElt_of_fixed {d : ℕ} {F : Type} [Field F]
    (σ : F ≃+* F) (w : Fin d → Fˣ) (hw : ∏ i, w i = 1)
    (hfix : ∀ i, σ (w i : F) = (w i : F)) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (kgLangS1ALinCoreAux_diagElt w hw) =
      kgLangS1ALinCoreAux_diagElt w hw := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  change σ ((Matrix.diagonal fun i => (w i : F)) i j) =
    (Matrix.diagonal fun i => (w i : F)) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, hfix]
  · rw [Matrix.diagonal_apply_ne _ hij, map_zero]

private theorem kgLangS1ALinCoreAux_map_diagElt_mul {d : ℕ} {F : Type} [Field F]
    (σ : F ≃+* F) (w v : Fin d → Fˣ) (hw : ∏ i, w i = 1) (hv : ∏ i, v i = 1)
    (hrel : ∀ i, Units.map (σ : F →* F) (w i) = v i * w i) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (kgLangS1ALinCoreAux_diagElt w hw) =
      kgLangS1ALinCoreAux_diagElt w hw * kgLangS1ALinCoreAux_diagElt v hv := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  change σ ((Matrix.diagonal fun i => (w i : F)) i j) =
    ((Matrix.diagonal fun i => (w i : F)) * (Matrix.diagonal fun i => (v i : F))) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      mul_comm]
    simpa using congrArg Units.val (hrel i)
  · rw [Matrix.diagonal_apply_ne _ hij, map_zero, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_ne _ hij]

private theorem kgLangS1ALinCoreAux_blockScalar_commute {d : ℕ} {F : Type} [Field F]
    {a : Fin d → ℤ} {w : Fin d → F} {D E : GL (Fin d) F}
    (hD : ∀ i j, a i ≠ a j → (D : Matrix (Fin d) (Fin d) F) i j = 0)
    (hE : (E : Matrix (Fin d) (Fin d) F) = Matrix.diagonal w)
    (hw : ∀ i j, a i = a j → w i = w j) :
    D * E = E * D := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hE]
  ext i j
  have h1 : ((D : Matrix (Fin d) (Fin d) F) * Matrix.diagonal w) i j =
      (D : Matrix (Fin d) (Fin d) F) i j * w j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [Matrix.diagonal_apply_eq]
    · intro k _ hk; rw [Matrix.diagonal_apply_ne _ hk, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have h2 : (Matrix.diagonal w * (D : Matrix (Fin d) (Fin d) F)) i j =
      w i * (D : Matrix (Fin d) (Fin d) F) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
    · intro k _ hk; rw [Matrix.diagonal_apply_ne _ (Ne.symm hk), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [h1, h2]
  by_cases hij : a i = a j
  · rw [hw i j hij, mul_comm]
  · rw [hD i j hij, zero_mul, mul_zero]

theorem kgLangS1A_lin_core {d n p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hd : d = p ∨ d = 2 * p)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    {X : Subgroup (MulAut (LinearFlag.projectiveSL d F))} (hX : IsElemAbelian p X)
    (hXc : ∀ x ∈ X, x ∈ Set.range (LinearFlag.conjAut d F))
    (hXσ : ∀ x ∈ X, LinearFlag.fieldAut d F σ * x = x * LinearFlag.fieldAut d F σ)
    (hsplit : p ∣ 2 ^ n - 1) (hcard : p ^ 2 ≤ Nat.card X)
    (hab : ∀ M ∈ X.comap ((LinearFlag.conjAut d F).comp
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype)),
      ∀ N ∈ X.comap ((LinearFlag.conjAut d F).comp
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype)), M * N = N * M) :
    ∃ e s : Matrix.SpecialLinearGroup (Fin d) F,
      Matrix.SpecialLinearGroup.map σ.toRingHom e = e ∧ e ^ p = 1 ∧
      e ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) ∧
      Matrix.SpecialLinearGroup.map σ.toRingHom s = s * e ∧
      ∀ B : GL (Fin d) F, LinearFlag.conjAut d F B ∈ X →
        B * Matrix.SpecialLinearGroup.toGL e = Matrix.SpecialLinearGroup.toGL e * B ∧
        B * Matrix.SpecialLinearGroup.toGL s = Matrix.SpecialLinearGroup.toGL s * B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2le : 2 ≤ p := hp.two_le
  have hd0 : 0 < d := by rcases hd with h | h <;> omega
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
  have hcardw : p ^ 2 * (Nat.card (semilinearFixedSubfield σ) - 1) ≤ Nat.card G := by
    rw [hF0q, hcardG']
    exact Nat.mul_le_mul_right _ hcard
  obtain ⟨A, a, hAdiag, hsum, hnotcong⟩ :=
    kgLangS1A_lin_weight hp hp2 hpF₀ hd hprojG hab hcardw
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := semilinearFixedSubfield σ) hp hpF₀
  let ωF : Fˣ := Units.mk0 ((ζ : semilinearFixedSubfield σ) : F)
    (fun h => hζ.ne_zero hp.ne_zero
      ((semilinearFixedSubfield σ).subtype_injective (by rw [map_zero]; exact h)))
  have hωFσ : σ (ωF : F) = (ωF : F) := by
    have hfix := RingHom.mem_eqLocusField.mp (ζ : semilinearFixedSubfield σ).2
    simpa [ωF] using hfix
  have hωFp : ωF ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (semilinearFixedSubfield σ).subtype ζ ^ p = 1
    rw [← map_pow (semilinearFixedSubfield σ).subtype, hζ.pow_eq_one, map_one]
  have hωFpF : (ωF : F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hωFp, Units.val_one]
  have hωF1 : ωF ≠ 1 := by
    intro h
    have hval := congrArg Units.val h
    have hζ1 : ζ = 1 := (semilinearFixedSubfield σ).subtype_injective (by
      simpa [ωF] using hval)
    exact hζ.ne_one hp.one_lt hζ1
  have hωForder : orderOf ωF = p := orderOf_eq_prime hωFp hωF1
  obtain ⟨u, hu⟩ := kgLangTorA_hilbert90 hp hσ hωFσ hωFpF
  let Â : GL (Fin d) F :=
    Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype A
  have hσÂ : Matrix.GeneralLinearGroup.map (σ : F →+* F) Â = Â := by
    show Matrix.GeneralLinearGroup.map (σ : F →+* F)
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype A) = _
    simpa using NbrLangTypeA.map_pow_map_subtype (σ := σ) A 1
  let we : Fin d → Fˣ := fun i => ωF ^ (a i)
  have hwe : ∏ i, we i = 1 := by
    change Finset.univ.prod (fun i => ωF ^ (a i)) = 1
    rw [kgLangS1ALinCoreAux_prod_zpow_eq_zpow_sum Finset.univ ωF a, hsum, zpow_zero]
  have hwe_pow : ∀ i, we i ^ p = 1 :=
    fun i => kgLangS1ALinCoreAux_zpow_pow_eq_one ωF hωFp (a i)
  have hwe_fixed : ∀ i, σ (we i : F) = (we i : F) := by
    intro i
    have h1 : Units.map (σ : F →* F) (we i) = we i := by
      change Units.map (σ : F →* F) (ωF ^ (a i)) = ωF ^ (a i)
      rw [map_zpow, show Units.map (σ : F →* F) ωF = ωF from Units.ext hωFσ]
    simpa using congrArg Units.val h1
  let D_e : Matrix.SpecialLinearGroup (Fin d) F := kgLangS1ALinCoreAux_diagElt we hwe
  let e : Matrix.SpecialLinearGroup (Fin d) F :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹ D_e
  have hep_e : e ^ p = 1 := by
    show (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹
      D_e) ^ p = 1
    rw [← map_pow (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹),
      kgLangS1ALinCoreAux_diagElt_pow we hwe hwe_pow, map_one]
  have he_fixed : Matrix.SpecialLinearGroup.map σ.toRingHom e = e := by
    show Matrix.SpecialLinearGroup.map σ.toRingHom
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹ D_e) = e
    rw [kgLangS1ALinCoreAux_map_slConjugation]
    rw [map_inv, hσÂ]
    rw [kgLangS1ALinCoreAux_map_diagElt_of_fixed σ we hwe hwe_fixed]
  have he_notcenter : e ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    intro hec
    have h1 : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â) e ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) :=
      (Subgroup.map_center_eq (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â)).symm ▸
        Subgroup.mem_map_of_mem _ hec
    have h2 : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â) e =
        D_e := by
      show (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â)
        ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹) D_e) = _
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [h2] at h1
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
    obtain ⟨i, j, hij⟩ := hnotcong
    have hentry : (we i : F) = (we j : F) := by
      have hi : (D_e : Matrix (Fin d) (Fin d) F) i i = r := by
        rw [← hr]; simp [Matrix.scalar_apply]
      have hj : (D_e : Matrix (Fin d) (Fin d) F) j j = r := by
        rw [← hr]; simp [Matrix.scalar_apply]
      rw [kgLangS1ALinCoreAux_coe_diagElt, Matrix.diagonal_apply_eq] at hi
      rw [kgLangS1ALinCoreAux_coe_diagElt, Matrix.diagonal_apply_eq] at hj
      rw [hi, hj]
    have hdiff : we i ≠ we j := by
      intro h
      have h3 : ωF ^ (a i) = ωF ^ (a j) := by simpa [we] using h
      have hmod : a i ≡ a j [ZMOD (p : ℤ)] := by
        have h4 := zpow_eq_zpow_iff_modEq.mp h3
        rwa [hωForder] at h4
      exact hij (by
        have h6 := Int.modEq_iff_dvd.mp hmod
        have := dvd_neg.mpr h6
        simpa only [neg_sub] using this)
    exact hdiff (Units.ext hentry)
  let ws : Fin d → Fˣ := fun i => u ^ (a i)
  have hws : ∏ i, ws i = 1 := by
    change Finset.univ.prod (fun i => u ^ (a i)) = 1
    rw [kgLangS1ALinCoreAux_prod_zpow_eq_zpow_sum Finset.univ u a, hsum, zpow_zero]
  let D_s : Matrix.SpecialLinearGroup (Fin d) F := kgLangS1ALinCoreAux_diagElt ws hws
  let s : Matrix.SpecialLinearGroup (Fin d) F :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹ D_s
  have hσu_units : Units.map (σ : F →* F) u = ωF * u := Units.ext hu
  have hrel : ∀ i, Units.map (σ : F →* F) (ws i) = we i * ws i := by
    intro i
    change Units.map (σ : F →* F) (u ^ (a i)) = ωF ^ (a i) * u ^ (a i)
    rw [map_zpow, hσu_units, mul_zpow]
  have hσDs : Matrix.SpecialLinearGroup.map σ.toRingHom D_s = D_s * D_e := by
    simpa only [D_s, D_e] using kgLangS1ALinCoreAux_map_diagElt_mul σ ws we hws hwe hrel
  have hsσ' : Matrix.SpecialLinearGroup.map σ.toRingHom s = s * e := by
    show Matrix.SpecialLinearGroup.map σ.toRingHom
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹ D_s) = s * e
    rw [kgLangS1ALinCoreAux_map_slConjugation]
    rw [map_inv, hσÂ]
    rw [hσDs]
    rw [map_mul]
  have htoGLe : (Matrix.SpecialLinearGroup.toGL e : GL (Fin d) F) =
      Â⁻¹ * Matrix.SpecialLinearGroup.toGL D_e * Â := by
    show (Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹ D_e) :
        GL (Fin d) F) = _
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, inv_inv]
  have htoGLs : (Matrix.SpecialLinearGroup.toGL s : GL (Fin d) F) =
      Â⁻¹ * Matrix.SpecialLinearGroup.toGL D_s * Â := by
    show (Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F Â⁻¹ D_s) :
        GL (Fin d) F) = _
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, inv_inv]
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
  have hMglD : Mgl = Â⁻¹ * D * Â := by rw [hD_eq]; group
  have hDcond : ∀ i j, a i ≠ a j → (D : Matrix (Fin d) (Fin d) F) i j = 0 := by
    intro i j hij
    have hAcoe : ((A * M * A⁻¹ : GL (Fin d) (semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) =
        (A : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) *
          (M : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) *
          ((A⁻¹ : GL (Fin d) (semilinearFixedSubfield σ)) :
            Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) := by
      rw [Units.val_mul, Units.val_mul]
    change (semilinearFixedSubfield σ).subtype
      (((A * M * A⁻¹ : GL (Fin d) (semilinearFixedSubfield σ)) :
        Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) i j) = 0
    rw [hAcoe, hAdiag M hMG i j hij, map_zero]
  have hD_e_coe : (Matrix.SpecialLinearGroup.toGL D_e : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => (we i : F)) := rfl
  have hD_s_coe : (Matrix.SpecialLinearGroup.toGL D_s : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun i => (ws i : F)) := rfl
  have hcommDe : D * Matrix.SpecialLinearGroup.toGL D_e =
      Matrix.SpecialLinearGroup.toGL D_e * D :=
    kgLangS1ALinCoreAux_blockScalar_commute hDcond hD_e_coe
      (fun i j hij => by dsimp only [we]; rw [hij])
  have hcommDs : D * Matrix.SpecialLinearGroup.toGL D_s =
      Matrix.SpecialLinearGroup.toGL D_s * D :=
    kgLangS1ALinCoreAux_blockScalar_commute hDcond hD_s_coe
      (fun i j hij => by dsimp only [ws]; rw [hij])
  have hMgl_e : Mgl * Matrix.SpecialLinearGroup.toGL e =
      Matrix.SpecialLinearGroup.toGL e * Mgl := by
    rw [hMglD, htoGLe]
    calc Â⁻¹ * D * Â * (Â⁻¹ * Matrix.SpecialLinearGroup.toGL D_e * Â) =
          Â⁻¹ * (D * Matrix.SpecialLinearGroup.toGL D_e) * Â := by group
      _ = Â⁻¹ * (Matrix.SpecialLinearGroup.toGL D_e * D) * Â := by rw [hcommDe]
      _ = (Â⁻¹ * Matrix.SpecialLinearGroup.toGL D_e * Â) * (Â⁻¹ * D * Â) := by group
  have hMgl_s : Mgl * Matrix.SpecialLinearGroup.toGL s =
      Matrix.SpecialLinearGroup.toGL s * Mgl := by
    rw [hMglD, htoGLs]
    calc Â⁻¹ * D * Â * (Â⁻¹ * Matrix.SpecialLinearGroup.toGL D_s * Â) =
          Â⁻¹ * (D * Matrix.SpecialLinearGroup.toGL D_s) * Â := by group
      _ = Â⁻¹ * (Matrix.SpecialLinearGroup.toGL D_s * D) * Â := by rw [hcommDs]
      _ = (Â⁻¹ * Matrix.SpecialLinearGroup.toGL D_s * Â) * (Â⁻¹ * D * Â) := by group
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

end CFSG.StandardType
