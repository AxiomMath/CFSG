module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Aff
public import CFSG.RankThree.PartOne.SEITZ2.OmegaDickson

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix CFSG.RankThree.PartOne.CTP

section Basic

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_symm_ts {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    eichler Q u w = eichler Q w u := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_ts_apply hu hw huw, eichler_ts_apply hw hu hwu]
  abel

theorem exists_dual_data {x₀ x₁ u w : V} (hx₀ : Q x₀ = 0) (hx₁ : Q x₁ = 0)
    (hx₀₁ : polar Q x₀ x₁ = 0) (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (hδ : polar Q x₀ u * polar Q x₁ w + polar Q x₀ w * polar Q x₁ u ≠ 0) :
    ∃ P P' : HypPair Q, P.Orth P' ∧ P.e = x₀ ∧ P'.e = x₁ ∧
      (∀ v, polar Q v u = 0 → polar Q v w = 0 → polar Q v P.f = 0 ∧ polar Q v P'.f = 0) ∧
      eichler Q u w = eichler Q P.f
        ((polar Q x₀ u * polar Q x₁ w + polar Q x₀ w * polar Q x₁ u) • P'.f) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, ha⟩ : ∃ a, polar Q x₀ u = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, polar Q x₀ w = b := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, polar Q x₁ u = m := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, polar Q x₁ w = n := ⟨_, rfl⟩
  rw [ha, hb, hm, hn] at hδ ⊢
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = a * n + b * m := ⟨_, rfl⟩
  rw [← hδdef] at hδ ⊢
  have hδ' : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : V, c₁ = (δ⁻¹ * n) • u + (δ⁻¹ * m) • w := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : V, c₂ = (δ⁻¹ * b) • u + (δ⁻¹ * a) • w := ⟨_, rfl⟩
  have hQ₁ : Q c₁ = 0 := by rw [hc₁]; exact map_comb_eq_zero hu hw huw _ _
  have hQ₂ : Q c₂ = 0 := by rw [hc₂]; exact map_comb_eq_zero hu hw huw _ _
  have hc₁c₂ : polar Q c₁ c₂ = 0 := by
    rw [hc₁, hc₂]; exact polar_comb_eq_zero hu hw huw _ _ _ _
  have e₁c₁ : polar Q x₀ c₁ = 1 := by
    rw [hc₁, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, ha, hb]
    linear_combination hδ' + (0 : K) * h2 - (δ⁻¹) * hδdef
  have e₂c₁ : polar Q x₁ c₁ = 0 := by
    rw [hc₁, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hm, hn]
    linear_combination (δ⁻¹ * m * n) * h2
  have e₁c₂ : polar Q x₀ c₂ = 0 := by
    rw [hc₂, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, ha, hb]
    linear_combination (δ⁻¹ * a * b) * h2
  have e₂c₂ : polar Q x₁ c₂ = 1 := by
    rw [hc₂, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hm, hn]
    linear_combination hδ' - (δ⁻¹) * hδdef
  have hu_eq : u = a • c₁ + m • c₂ := by
    rw [hc₁, hc₂]
    match_scalars
    · linear_combination (-1 : K) * hδ' + δ⁻¹ * hδdef
    · linear_combination (-(δ⁻¹ * a * m)) * h2
  have hw_eq : w = b • c₁ + n • c₂ := by
    rw [hc₁, hc₂]
    match_scalars
    · linear_combination (-1 : K) * hδ' + δ⁻¹ * hδdef
    · linear_combination (-(δ⁻¹ * b * n)) * h2
  have hOrth : (⟨x₀, c₁, hx₀, hQ₁, e₁c₁⟩ : HypPair Q).Orth ⟨x₁, c₂, hx₁, hQ₂, e₂c₂⟩ :=
    ⟨hx₀₁, e₁c₂, by rw [polar_comm]; exact e₂c₁, hc₁c₂⟩
  refine ⟨_, _, hOrth, rfl, rfl, fun v hvu hvw => ⟨?_, ?_⟩, ?_⟩
  · show polar Q v c₁ = 0
    rw [hc₁, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hvu, hvw]
    ring
  · show polar Q v c₂ = 0
    rw [hc₂, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hvu, hvw]
    ring
  · show eichler Q u w = eichler Q c₁ (δ • c₂)
    have hch := eichler_change_basis hQ₁ hQ₂ hc₁c₂ a m b n
    have h1 : eichler Q u w = eichler Q (a • c₁ + m • c₂) (b • c₁ + n • c₂) := by
      rw [← hu_eq, ← hw_eq]
    rw [h1, hch]
    have : a * n + m * b = δ := by rw [hδdef]; ring
    rw [this]

end Basic

section Plane

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def vecOf (P P' : HypPair Q) (b : Matrix (Fin 2) (Fin 2) K) : V :=
  b 0 0 • P'.e + b 0 1 • P.e + b 1 0 • P.f + b 1 1 • P'.f

variable {P P' : HypPair Q}

theorem vecOf_add (b b' : Matrix (Fin 2) (Fin 2) K) :
    vecOf P P' (b + b') = vecOf P P' b + vecOf P P' b' := by
  simp only [vecOf, Matrix.add_apply, add_smul]
  abel

theorem vecOf_zero : vecOf P P' (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  simp [vecOf]

theorem planeLin_e (h : P.Orth P') (g : SpecialLinearGroup (Fin 2) K) :
    planeLin P P' g P.e = (g : Matrix (Fin 2) (Fin 2) K) 0 0 • P.e +
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 • P'.f := by
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  rw [planeLin_apply]
  simp only [planeA₁, planeA₂, planeC₁, planeC₂, ee, ee', ef, ef']
  module

theorem planeLin_e' (h : P.Orth P') (g : SpecialLinearGroup (Fin 2) K) :
    planeLin P P' g P'.e = (g : Matrix (Fin 2) (Fin 2) K) 0 0 • P'.e +
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 • P.f := by
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  rw [planeLin_apply]
  simp only [planeA₁, planeA₂, planeC₁, planeC₂, e'e, e'f, e'e', e'f']
  module

theorem planeLin_f (h : P.Orth P') (g : SpecialLinearGroup (Fin 2) K) :
    planeLin P P' g P.f = (g : Matrix (Fin 2) (Fin 2) K) 1 1 • P.f +
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 • P'.e := by
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  rw [planeLin_apply]
  simp only [planeA₁, planeA₂, planeC₁, planeC₂, fe, ff, fe', ff']
  module

theorem planeLin_f' (h : P.Orth P') (g : SpecialLinearGroup (Fin 2) K) :
    planeLin P P' g P'.f = (g : Matrix (Fin 2) (Fin 2) K) 1 1 • P'.f +
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 • P.e := by
  obtain ⟨ee, ee', ef, ef', fe, ff, fe', ff', e'e, e'f, e'e', e'f', f'e, f'f, f'e', f'f'⟩ :=
    polar_facts P P' h
  rw [planeLin_apply]
  simp only [planeA₁, planeA₂, planeC₁, planeC₂, f'e, f'f, f'e', f'f']
  module

theorem planeHom_vecOf (h : P.Orth P') (g : SpecialLinearGroup (Fin 2) K)
    (b : Matrix (Fin 2) (Fin 2) K) :
    planeHom h g (vecOf P P' b) = vecOf P P' ((g : Matrix (Fin 2) (Fin 2) K) * b) := by
  rw [planeHom_apply]
  simp only [vecOf, map_add, map_smul, planeLin_e h, planeLin_e' h, planeLin_f h, planeLin_f' h,
    Matrix.mul_apply, Fin.sum_univ_two]
  module

theorem planeHom_fix (h : P.Orth P') (g : SpecialLinearGroup (Fin 2) K) {z : V}
    (hze : polar Q z P.e = 0) (hzf : polar Q z P.f = 0) (hze' : polar Q z P'.e = 0)
    (hzf' : polar Q z P'.f = 0) : planeHom h g z = z := by
  rw [planeHom_apply, planeLin_apply]
  simp [planeA₁, planeA₂, planeC₁, planeC₂, hze, hzf, hze', hzf']

theorem polar_vecOf_right {z : V} (hze : polar Q z P.e = 0) (hzf : polar Q z P.f = 0)
    (hze' : polar Q z P'.e = 0) (hzf' : polar Q z P'.f = 0) (b : Matrix (Fin 2) (Fin 2) K) :
    polar Q z (vecOf P P' b) = 0 := by
  simp [vecOf, polar_add_right, hze, hzf, hze', hzf']

end Plane

section Siegel

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P P' : HypPair Q}

theorem planeHom_conj_siegel (h : P.Orth P') (g : SpecialLinearGroup (Fin 2) K) {z : V}
    (hze : polar Q z P.e = 0) (hzf : polar Q z P.f = 0) (hze' : polar Q z P'.e = 0)
    (hzf' : polar Q z P'.f = 0) (b : Matrix (Fin 2) (Fin 2) K) :
    planeHom h g * eichler Q z (vecOf P P' b) * (planeHom h g)⁻¹ =
      eichler Q z (vecOf P P' ((g : Matrix (Fin 2) (Fin 2) K) * b)) := by
  rw [eichler_conj (planeHom_mem_orthogonalGroup g h), planeHom_fix h g hze hzf hze' hzf',
    planeHom_vecOf h g b]

@[expose] noncomputable def psi (h : P.Orth P') (z : V) (hze : polar Q z P.e = 0)
    (hzf : polar Q z P.f = 0) (hze' : polar Q z P'.e = 0) (hzf' : polar Q z P'.f = 0) :
    Aff K →* (V ≃ₗ[K] V) :=
  MonoidHom.mk' (fun x => eichler Q z (vecOf P P' x.b) * planeHom h x.m) (by
    intro x y
    have hcomm : planeHom h x.m * eichler Q z (vecOf P P' y.b) =
        eichler Q z (vecOf P P' ((x.m : Matrix (Fin 2) (Fin 2) K) * y.b)) * planeHom h x.m := by
      rw [← planeHom_conj_siegel h x.m hze hzf hze' hzf' y.b]
      group
    have hadd : eichler Q z (vecOf P P' (x.b + (x.m : Matrix (Fin 2) (Fin 2) K) * y.b)) =
        eichler Q z (vecOf P P' x.b) *
          eichler Q z (vecOf P P' ((x.m : Matrix (Fin 2) (Fin 2) K) * y.b)) := by
      rw [vecOf_add, eichler_mul (polar_vecOf_right hze hzf hze' hzf' _)
        (polar_vecOf_right hze hzf hze' hzf' _)]
    show eichler Q z (vecOf P P' (x.b + (x.m : Matrix (Fin 2) (Fin 2) K) * y.b)) *
        planeHom h (x.m * y.m) = _
    rw [hadd, map_mul]
    calc _ = eichler Q z (vecOf P P' x.b) * (eichler Q z (vecOf P P'
            ((x.m : Matrix (Fin 2) (Fin 2) K) * y.b)) * planeHom h x.m) * planeHom h y.m := by
          group
      _ = eichler Q z (vecOf P P' x.b) * (planeHom h x.m * eichler Q z (vecOf P P' y.b)) *
            planeHom h y.m := by rw [hcomm]
      _ = _ := by group)

end Siegel

end CFSG.RankThree.PartOne.SEITZ2
