module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Vol2.KGNatCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat Matrix

variable {W : Type} [CommGroup W]

private lemma s16t3_eq_zero_or_eq_one_of_card_eq_two {K : Type} [Field K]
    (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    rw [hy x hx, hy 1 one_ne_zero]

private theorem s16t3_rep_aux {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (hK : Nat.card K = 2) {X : Subgroup (MulAut W)}
    {U Z : Subgroup W} (f : W → (ι → K))
    (hadd : ∀ u ∈ U, ∀ u' ∈ U, f (u * u') = f u + f u')
    (hker : ∀ u ∈ U, f u = 0 ↔ u ∈ Z) (hsurj : ∀ m : ι → K, ∃ u ∈ U, f u = m)
    (hXU : StableUnder X U) (hXZ : StableUnder X Z) :
    ∃ τ : ↥X →* Matrix.GeneralLinearGroup ι K,
      ∀ (x : ↥X) (u : ↥U), (τ x : Matrix ι ι K) *ᵥ f u = f ((x : MulAut W) u) := by
  classical
  let rep : (ι → K) → W := fun m => Classical.choose (hsurj m)
  have rep_mem : ∀ m : ι → K, rep m ∈ U := fun m => (Classical.choose_spec (hsurj m)).1
  have rep_spec : ∀ m : ι → K, f (rep m) = m := fun m => (Classical.choose_spec (hsurj m)).2
  let A : ↥X → (ι → K) → (ι → K) := fun x m => f ((x : MulAut W) (rep m))
  have well_def (x : ↥X) : ∀ u ∈ U, ∀ u' ∈ U, f u = f u' →
      f ((x : MulAut W) u) = f ((x : MulAut W) u') := by
    intro u hu u' hu' hfu
    have hwU : u * u'⁻¹ ∈ U := U.mul_mem hu (U.inv_mem hu')
    have hgr : (u * u'⁻¹) * u' = u := by group
    have h2 : f (u * u'⁻¹) + f u' = 0 + f u' := by
      rw [zero_add, ← hadd (u * u'⁻¹) hwU u' hu', hgr, hfu]
    have hw0 : f (u * u'⁻¹) = 0 := add_right_cancel h2
    have hz : u * u'⁻¹ ∈ Z := (hker (u * u'⁻¹) hwU).1 hw0
    have hxw0 : f ((x : MulAut W) (u * u'⁻¹)) = 0 :=
      (hker _ (hXU x x.2 (u * u'⁻¹) hwU)).2 (hXZ x x.2 (u * u'⁻¹) hz)
    have h3 : f ((x : MulAut W) (u * u'⁻¹) * (x : MulAut W) u') = f ((x : MulAut W) u') := by
      rw [hadd _ (hXU x x.2 (u * u'⁻¹) hwU) _ (hXU x x.2 u' hu'), hxw0, zero_add]
    have h4 : (x : MulAut W) (u * u'⁻¹) * (x : MulAut W) u' = (x : MulAut W) u := by
      rw [← map_mul, hgr]
    rw [h4] at h3
    exact h3
  have A_apply (x : ↥X) (u : ↥U) : A x (f u) = f ((x : MulAut W) u) := by
    show f ((x : MulAut W) (rep (f u))) = f ((x : MulAut W) u)
    exact well_def x (rep (f u)) (rep_mem (f u)) u.1 u.2 (rep_spec (f u))
  have A_eq (x : ↥X) (m : ι → K) (u : ↥U) (hu : f u = m) :
      A x m = f ((x : MulAut W) u) := by
    rw [← hu]
    exact A_apply x u
  have A_add (x : ↥X) : ∀ m m' : ι → K, A x (m + m') = A x m + A x m' := by
    intro m m'
    obtain ⟨u, huU, hfu⟩ := hsurj m
    obtain ⟨u', hu'U, hfu'⟩ := hsurj m'
    rw [← hfu, ← hfu', ← hadd u huU u' hu'U]
    rw [A_eq x (f (u * u')) ⟨u * u', U.mul_mem huU hu'U⟩ rfl,
      A_eq x (f u) ⟨u, huU⟩ rfl, A_eq x (f u') ⟨u', hu'U⟩ rfl]
    simp only [Subgroup.coe_mk]
    rw [map_mul]
    exact hadd ((x : MulAut W) u) (hXU x x.2 u huU) ((x : MulAut W) u') (hXU x x.2 u' hu'U)
  have A_zero (x : ↥X) : A x 0 = 0 := by
    have hf1 : f 1 = 0 := (hker 1 U.one_mem).2 Z.one_mem
    calc A x 0 = A x (f 1) := by rw [hf1]
      _ = f ((x : MulAut W) 1) := A_apply x ⟨1, U.one_mem⟩
      _ = f 1 := by rw [map_one]
      _ = 0 := hf1
  have A_one : ∀ m : ι → K, A 1 m = m := by
    intro m
    obtain ⟨u, huU, hfu⟩ := hsurj m
    rw [A_eq 1 m ⟨u, huU⟩ hfu]
    simp [hfu]
  have A_mul (x y : ↥X) : A (x * y) = A x ∘ A y := by
    funext m
    obtain ⟨u, huU, hfu⟩ := hsurj m
    have harg : ((x * y : ↥X) : MulAut W) u = (x : MulAut W) ((y : MulAut W) u) := by
      simp only [Subgroup.coe_mul, MulAut.mul_apply]
    rw [Function.comp_apply, A_eq (x * y) m ⟨u, huU⟩ hfu,
      show A y m = f ((y : MulAut W) u) from A_eq y m ⟨u, huU⟩ hfu,
      A_apply x ⟨(y : MulAut W) u, hXU y y.2 u huU⟩, harg]
  have A_smul (x : ↥X) : ∀ (c : K) (m : ι → K), A x (c • m) = c • A x m := by
    intro c m
    rcases s16t3_eq_zero_or_eq_one_of_card_eq_two hK c with hc | hc
    · rw [hc, zero_smul, zero_smul, A_zero x]
    · rw [hc, one_smul, one_smul]
  let Alin : ↥X → ((ι → K) ≃ₗ[K] (ι → K)) := fun x =>
    { toFun := A x
      invFun := A x⁻¹
      left_inv := fun m => by
        have h := congrFun (A_mul x⁻¹ x) m
        simp only [Function.comp_apply] at h
        rw [show x⁻¹ * x = 1 from inv_mul_cancel x, A_one] at h
        exact h.symm
      right_inv := fun m => by
        have h := congrFun (A_mul x x⁻¹) m
        simp only [Function.comp_apply] at h
        rw [show x * x⁻¹ = 1 from mul_inv_cancel x, A_one] at h
        exact h.symm
      map_add' := A_add x
      map_smul' := A_smul x }
  let M : ↥X → Matrix.GeneralLinearGroup ι K := fun x =>
    Matrix.GeneralLinearGroup.toLin.symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).symm (Alin x))
  have hM (x : ↥X) : ∀ v : ι → K, (M x : Matrix ι ι K) *ᵥ v = A x v := by
    intro v
    have h1 := Matrix.GeneralLinearGroup.toLin_apply (M x) v
    rw [Matrix.mulVecLin_apply] at h1
    rw [← h1]
    have h2 : Matrix.GeneralLinearGroup.toLin (M x) =
        (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).symm (Alin x) :=
      MulEquiv.apply_symm_apply _ _
    rw [h2, ← LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, MulEquiv.apply_symm_apply]
    rfl
  have M_mul (x y : ↥X) : M (x * y) = M x * M y := by
    apply Units.ext
    apply Matrix.ext_iff_mulVec.2
    intro v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hM x, hM y, hM (x * y)]
    exact congrFun (A_mul x y) v
  let τ : ↥X →* Matrix.GeneralLinearGroup ι K := MonoidHom.mk' M M_mul
  have hτ (x : ↥X) (v : ι → K) : (τ x : Matrix ι ι K) *ᵥ v = A x v := hM x v
  exact ⟨τ, fun x u => (hτ x (f u)).trans (A_apply x u)⟩

theorem s16t3_exists_rep_of_normalizes {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (hK : Nat.card K = 2) {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H X : Subgroup (MulAut W)} {U Z : Subgroup W} {π : ↥Γ →* ↥H}
    (hπ : (FFModel.nat Γ).RealizesVia H U Z π) (hXU : StableUnder X U)
    (hXZ : StableUnder X Z) (hXH : X ≤ Subgroup.normalizer (H : Set (MulAut W))) :
    ∃ τ : ↥X →* Matrix.GeneralLinearGroup ι K,
      (∀ (x : ↥X) (γ : ↥Γ), ∃ hγ : τ x * (γ : Matrix.GeneralLinearGroup ι K) * (τ x)⁻¹ ∈ Γ,
        ((π ⟨_, hγ⟩ : ↥H) : MulAut W) =
          (x : MulAut W) * ((π γ : ↥H) : MulAut W) * (x : MulAut W)⁻¹) ∧
      ∀ (x : ↥X) (γ : ↥Γ), (x : MulAut W) = ((π γ : ↥H) : MulAut W) →
        τ x = (γ : Matrix.GeneralLinearGroup ι K) := by
  classical
  obtain ⟨f, hadd, hker, hsurj, hcomm⟩ := exists_coord (linModelNat Γ) hπ
  obtain ⟨hπsurj, -, -, hHU, -, -, -, -⟩ := hπ
  obtain ⟨τ, hτf⟩ := s16t3_rep_aux hK f hadd hker hsurj hXU hXZ
  refine ⟨τ, ?_, ?_⟩
  · intro x γ
    have hxN : (x : MulAut W) ∈ Subgroup.normalizer (H : Set (MulAut W)) := hXH x.2
    have hmem : (x : MulAut W) * ((π γ : ↥H) : MulAut W) * (x : MulAut W)⁻¹ ∈ H :=
      ((Subgroup.mem_normalizer_iff).1 hxN ((π γ : ↥H) : MulAut W)).1 (π γ).2
    have hπsurj' : ∀ y : ↥H, ∃ γ : ↥Γ, π γ = y := hπsurj
    obtain ⟨γ', hγ'⟩ := hπsurj' ⟨_, hmem⟩
    have hγ'' : ((π γ' : ↥H) : MulAut W) =
        (x : MulAut W) * ((π γ : ↥H) : MulAut W) * (x : MulAut W)⁻¹ :=
      congrArg Subtype.val hγ'
    have hconj : τ x * (γ : Matrix.GeneralLinearGroup ι K) * (τ x)⁻¹ =
        (γ' : Matrix.GeneralLinearGroup ι K) := by
      apply Units.ext
      apply Matrix.ext_iff_mulVec.2
      intro v
      obtain ⟨u, huU, hfu⟩ := hsurj v
      rw [← hfu]
      have hwU : ((x⁻¹ : ↥X) : MulAut W) u ∈ U := hXU x⁻¹ (x⁻¹).2 u huU
      have hxinv : ((((τ x)⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ f u) =
          f (((x⁻¹ : ↥X) : MulAut W) u) := by
        rw [← map_inv τ x]
        exact hτf x⁻¹ ⟨u, huU⟩
      have hγlin : (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)) *ᵥ
            f (((x⁻¹ : ↥X) : MulAut W) u) =
          f (((π γ : ↥H) : MulAut W) (((x⁻¹ : ↥X) : MulAut W) u)) :=
        ((linModelNat_lin Γ γ (f (((x⁻¹ : ↥X) : MulAut W) u))).symm).trans
          (hcomm γ (((x⁻¹ : ↥X) : MulAut W) u) hwU).symm
      have hxlin : (τ x : Matrix ι ι K) *ᵥ
            f (((π γ : ↥H) : MulAut W) (((x⁻¹ : ↥X) : MulAut W) u)) =
          f ((x : MulAut W) (((π γ : ↥H) : MulAut W)
            (((x⁻¹ : ↥X) : MulAut W) u))) :=
        hτf x ⟨_, hHU (π γ) (((x⁻¹ : ↥X) : MulAut W) u) hwU⟩
      have hxconj : (x : MulAut W) (((π γ : ↥H) : MulAut W)
            (((x⁻¹ : ↥X) : MulAut W) u)) = ((π γ' : ↥H) : MulAut W) u := by
        rw [hγ'']
        simp [MulAut.mul_apply]
      have hγ'lin : f (((π γ' : ↥H) : MulAut W) u) =
          (((γ' : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)) *ᵥ f u :=
        (hcomm γ' u huU).trans (linModelNat_lin Γ γ' (f u))
      calc (((τ x * (γ : Matrix.GeneralLinearGroup ι K) * (τ x)⁻¹ :
                Matrix.GeneralLinearGroup ι K)) : Matrix ι ι K) *ᵥ f u
          = (τ x : Matrix ι ι K) *ᵥ
              (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
                ((((τ x)⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ f u)) := by
            rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        _ = (τ x : Matrix ι ι K) *ᵥ
              (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
                f (((x⁻¹ : ↥X) : MulAut W) u)) := by
            rw [hxinv]
        _ = (τ x : Matrix ι ι K) *ᵥ
              f (((π γ : ↥H) : MulAut W) (((x⁻¹ : ↥X) : MulAut W) u)) := by
            rw [hγlin]
        _ = f ((x : MulAut W) (((π γ : ↥H) : MulAut W)
              (((x⁻¹ : ↥X) : MulAut W) u))) := by
            rw [hxlin]
        _ = f (((π γ' : ↥H) : MulAut W) u) := by
            rw [hxconj]
        _ = (((γ' : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)) *ᵥ f u := hγ'lin
    have hmemA : τ x * (γ : Matrix.GeneralLinearGroup ι K) * (τ x)⁻¹ ∈ Γ := by
      rw [hconj]
      exact γ'.2
    refine ⟨hmemA, ?_⟩
    have hsub : (⟨τ x * (γ : Matrix.GeneralLinearGroup ι K) * (τ x)⁻¹,
        hmemA⟩ : ↥Γ) = γ' := Subtype.ext hconj
    have h3 : ((π ⟨τ x * (γ : Matrix.GeneralLinearGroup ι K) * (τ x)⁻¹,
        hmemA⟩ : ↥H) : MulAut W) = ((π γ' : ↥H) : MulAut W) :=
      congrArg Subtype.val (congrArg π hsub)
    rw [h3]
    simpa using congrArg Subtype.val hγ'
  · intro x γ hx
    apply Units.ext
    apply Matrix.ext_iff_mulVec.2
    intro v
    obtain ⟨u, huU, hfu⟩ := hsurj v
    rw [← hfu, hτf x ⟨u, huU⟩, hx]
    exact (hcomm γ u huU).trans (linModelNat_lin Γ γ (f u))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
