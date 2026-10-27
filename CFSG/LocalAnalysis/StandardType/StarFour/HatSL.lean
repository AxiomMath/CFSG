module

public import CFSG.LocalAnalysis.StandardType.StarFour.PsiInjective
public import CFSG.LocalAnalysis.StandardType.StarFour.InnerDiagTwo

public section

namespace CFSG.StandardType.StarFour

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank Matrix

private lemma conjSL_one {F : Type} [Field F] {m : ℕ}
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (1 : GL (Fin (m + 1)) F) u = u := by
  apply (InnerDiagA.slEquiv m F).injective
  rw [InnerDiagA.slEquiv_conjSL]
  simp

private lemma conjSL_mul {F : Type} [Field F] {m : ℕ}
    (A B : GL (Fin (m + 1)) F) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (A * B) u = InnerDiagA.conjSL A (InnerDiagA.conjSL B u) := by
  apply (InnerDiagA.slEquiv m F).injective
  rw [InnerDiagA.slEquiv_conjSL, InnerDiagA.slEquiv_conjSL, InnerDiagA.slEquiv_conjSL,
    show MulAut.conjNormal (A * B) = MulAut.conjNormal A * MulAut.conjNormal B from
      map_mul MulAut.conjNormal A B]
  rfl

private lemma conjSL_inv_left {F : Type} [Field F] {m : ℕ}
    (A : GL (Fin (m + 1)) F) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL A (InnerDiagA.conjSL A⁻¹ u) = u := by
  rw [← conjSL_mul, mul_inv_cancel, conjSL_one]

theorem exists_conjSL_eq_conj {F : Type} [Field F] [Finite F] {m : ℕ}
    (hcop : Nat.Coprime (m + 1) (Nat.card F - 1)) (A : GL (Fin (m + 1)) F) :
    ∃ s : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      ∀ u, InnerDiagA.conjSL A u = s * u * s⁻¹ := by
  classical
  obtain ⟨μ, hμ⟩ := (pow_bijective_of_coprime hcop).2 (Matrix.GeneralLinearGroup.det A)
  have hμ' : μ ^ (m + 1) = Matrix.GeneralLinearGroup.det A := by simpa using hμ
  let A' : GL (Fin (m + 1)) F := Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹ * A
  have hμi : (μ⁻¹) ^ (m + 1) = (Matrix.GeneralLinearGroup.det A)⁻¹ := by
    rw [inv_pow, hμ']
  have hdetA' : Matrix.GeneralLinearGroup.det A' = 1 := by
    show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹ * A) = 1
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hμi, inv_mul_cancel]
  let s : Matrix.SpecialLinearGroup (Fin (m + 1)) F :=
    (InnerDiagA.slEquiv m F).symm ⟨A', hdetA'⟩
  have hsA : (InnerDiagA.slEquiv m F s : GL (Fin (m + 1)) F) = A' := by
    simp [s]
  have hAs : A = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ * A' := by
    show A = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ *
      (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹ * A)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨s, fun u => ?_⟩
  apply (InnerDiagA.slEquiv m F).injective
  rw [InnerDiagA.slEquiv_conjSL]
  simp only [map_mul, map_inv]
  refine Subtype.ext ?_
  rw [MulAut.conjNormal_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hsA, hAs]
  have hc := Matrix.GeneralLinearGroup.scalar_commute μ
    (A' * (InnerDiagA.slEquiv m F u : GL (Fin (m + 1)) F) * A'⁻¹)
  rw [show (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ * A') *
        (InnerDiagA.slEquiv m F u : GL (Fin (m + 1)) F) *
        (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ * A')⁻¹
      = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ *
        (A' * (InnerDiagA.slEquiv m F u : GL (Fin (m + 1)) F) * A'⁻¹) *
        (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) μ)⁻¹ by group,
    hc]
  group

private lemma exists_conjGL_of_chi {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    {X : Type*} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : Function.Injective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {x : X} {χ : Fin (m + 1) → Fin (m + 1) → F}
    (hχ : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (t : F),
      x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij t) * x =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t))) :
    ∃ D : GL (Fin (m + 1)) F, ∀ u, x⁻¹ * ψ u * x = ψ (InnerDiagA.conjSL D u) := by
  rcases lt_or_ge m 2 with hm | hm
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · refine ⟨1, fun u => ?_⟩
      haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => by
        rw [Fin.eq_zero a, Fin.eq_zero b]⟩
      haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin (0 + 1)) F) :=
        Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
      have hu : u = 1 := Subsingleton.elim u 1
      rw [hu, conjSL_one]
      simp
    · exact exists_conj_eq_conjSL_two ψ hψ hχ
  · exact InnerDiagA.exists_conj_eq_conjSL hm ψ hker hχ

private lemma exists_conjSL_of_ggPsiInnerDiag {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hcop : Nat.Coprime (m + 1) (Nat.card F - 1))
    {X : Type*} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : Function.Injective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {b : X} (hb : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b) :
    ∃ s : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      ∀ u, b * ψ u * b⁻¹ = ψ (s * u * s⁻¹) := by
  obtain ⟨g, hg, χ, hχ⟩ := InnerDiagA.exists_chi_of_ggPsiInnerDiag ψ hb
  obtain ⟨s₀, rfl⟩ := hg
  obtain ⟨D, hD⟩ := exists_conjGL_of_chi ψ hψ hker hχ
  have hx : ∀ w, (b * ψ s₀) * ψ w * (b * ψ s₀)⁻¹ = ψ (InnerDiagA.conjSL D⁻¹ w) := by
    intro w
    have h := hD (InnerDiagA.conjSL D⁻¹ w)
    rw [conjSL_inv_left] at h
    calc (b * ψ s₀) * ψ w * (b * ψ s₀)⁻¹
        = (b * ψ s₀) * ((b * ψ s₀)⁻¹ * ψ (InnerDiagA.conjSL D⁻¹ w) * (b * ψ s₀)) *
            (b * ψ s₀)⁻¹ := by rw [h]
      _ = ψ (InnerDiagA.conjSL D⁻¹ w) := by group
  obtain ⟨s₁, hs₁⟩ := exists_conjSL_eq_conj hcop D⁻¹
  refine ⟨s₁ * s₀⁻¹, fun u => ?_⟩
  have hmid : ψ s₀ * ψ (s₀⁻¹ * u * s₀) * ψ s₀⁻¹ = ψ u := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  calc b * ψ u * b⁻¹
      = b * (ψ s₀ * ψ (s₀⁻¹ * u * s₀) * ψ s₀⁻¹) * b⁻¹ := by rw [hmid]
    _ = (b * ψ s₀) * ψ (s₀⁻¹ * u * s₀) * (b * ψ s₀)⁻¹ := by
        rw [map_inv ψ s₀]; group
    _ = ψ (InnerDiagA.conjSL D⁻¹ (s₀⁻¹ * u * s₀)) := hx _
    _ = ψ ((s₁ * s₀⁻¹) * u * (s₁ * s₀⁻¹)⁻¹) := by
        rw [hs₁ (s₀⁻¹ * u * s₀)]
        congr 1
        group

private lemma eq_of_conjSL_eq {F : Type} [Field F] [Finite F] {m : ℕ}
    {X : Type*} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : Function.Injective ψ)
    (hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) = ⊥)
    {b : X} {s s' : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hs : ∀ u, b * ψ u * b⁻¹ = ψ (s * u * s⁻¹))
    (hs' : ∀ u, b * ψ u * b⁻¹ = ψ (s' * u * s'⁻¹)) : s = s' := by
  have h1 : ∀ u, s * u * s⁻¹ = s' * u * s'⁻¹ := by
    intro u
    apply hψ
    rw [← hs u, ← hs' u]
  have hmem : s'⁻¹ * s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
    rw [Subgroup.mem_center_iff]
    intro u
    have h2 : (s'⁻¹ * s) * u = u * (s'⁻¹ * s) := by
      calc (s'⁻¹ * s) * u
          = s'⁻¹ * (s * u * s⁻¹) * s := by group
        _ = s'⁻¹ * (s' * u * s'⁻¹) * s := by rw [h1 u]
        _ = u * (s'⁻¹ * s) := by group
    exact h2.symm
  have hs1 : s'⁻¹ * s = 1 := by
    have h := hmem
    rw [hcen] at h
    exact Subgroup.mem_bot.mp h
  calc s = s' * (s'⁻¹ * s) := by group
    _ = s' * 1 := by rw [hs1]
    _ = s' := by rw [mul_one]

theorem exists_hat_of_ggPsiInnerDiag {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hcop : Nat.Coprime (m + 1) (Nat.card F - 1)) {X : Type*} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (B : Subgroup X) (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB : ∀ b ∈ B, GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b) :
    ∃ hat : B →* Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      (∀ (b : B) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F),
        (b : X) * ψ u * (b : X)⁻¹ = ψ (hat b * u * (hat b)⁻¹)) ∧
      (∀ b : B, hat b = 1 ↔ (b : X) ∈ Subgroup.centralizer (ψ.range : Set X)) := by
  classical
  have hψ : Function.Injective ψ := psi_injective_of_ker_le_center hcop ψ hker
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) = ⊥ :=
    center_specialLinearGroup_eq_bot_of_coprime hcop
  let good : B → Matrix.SpecialLinearGroup (Fin (m + 1)) F := fun b =>
    Classical.choose (exists_conjSL_of_ggPsiInnerDiag hcop ψ hψ hker (hB b b.2))
  have good_spec : ∀ (b : B) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F),
      (b : X) * ψ u * (b : X)⁻¹ = ψ (good b * u * (good b)⁻¹) := fun b =>
    Classical.choose_spec (exists_conjSL_of_ggPsiInnerDiag hcop ψ hψ hker (hB b b.2))
  have hmap : ∀ b b' : B, good (b * b') = good b * good b' := by
    intro b b'
    refine eq_of_conjSL_eq ψ hψ hcen (b := ((b * b' : B) : X)) (s := good (b * b'))
      (s' := good b * good b') ?_ ?_
    · exact good_spec (b * b')
    · intro u
      calc ((b * b' : B) : X) * ψ u * ((b * b' : B) : X)⁻¹
          = (b : X) * ((b' : X) * ψ u * (b' : X)⁻¹) * (b : X)⁻¹ := by
            simp only [Subgroup.coe_mul]; group
        _ = (b : X) * ψ (good b' * u * (good b')⁻¹) * (b : X)⁻¹ := by
            rw [good_spec b' u]
        _ = ψ (good b * (good b' * u * (good b')⁻¹) * (good b)⁻¹) := by
            rw [good_spec b (good b' * u * (good b')⁻¹)]
        _ = ψ ((good b * good b') * u * (good b * good b')⁻¹) := by
            congr 1; group
  refine ⟨MonoidHom.mk' good hmap, ?_, ?_⟩
  · intro b u
    exact good_spec b u
  · intro b
    constructor
    · intro hb1
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨u, rfl⟩ := hy
      have hb1' : good b = 1 := by simpa using hb1
      have h := good_spec b u
      rw [hb1', one_mul, inv_one, mul_one] at h
      calc ψ u * (b : X) = ((b : X) * ψ u * (b : X)⁻¹) * (b : X) := by rw [h]
        _ = (b : X) * ψ u := by group
    · intro hbcent
      refine eq_of_conjSL_eq ψ hψ hcen (b := (b : X)) (s := good b) (s' := 1) (good_spec b) ?_
      intro u
      rw [one_mul, inv_one, mul_one]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hbcent) (ψ u) ⟨u, rfl⟩
      rw [← hcomm]
      group

end CFSG.StandardType.StarFour
