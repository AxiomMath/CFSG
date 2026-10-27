module

public import CFSG.Quasithin.Background.P4SL34Core
public import CFSG.Quasithin.Background.G116IIInputs

public section

namespace CFSG.Quasithin.G11.P4SL34

open CFSG.Assembly.LowTwoRank

theorem outer_general {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {U : Type} [AddCommGroup U] [Module (ZMod 2) U] (K : Subgroup (GLV U))
    (hnat : IsNaturalMatrixModule K (StatedSL 3 F))
    (α : ↥K ≃* ↥K) (P : Sylow 2 ↥K) (hαP : ∀ s ∈ P, α s ∈ P) (hα2 : ∀ s, α (α s) = s)
    (hnot : ¬ ∃ c : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = c * (k : GLV U) * c⁻¹) :
    ∃ s ∈ P, ∃ t ∈ P,
      ¬ ((s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
        (s⁻¹ * α s) * (s⁻¹ * α s) = 1) := by
  obtain ⟨φ, ψ, hψ⟩ := hnat
  let Φ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    φ.trans (specialLinearGroupEquivStatedSL 3 F).symm
  have hΦ : ∀ k : ↥K, ((Φ k : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((φ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro k
    have h := specialLinearGroupEquivStatedSL_coe 3 F (Φ k)
    rw [← h]
    simp [Φ]
  have : Finite ↥K := Finite.of_equiv _ Φ.symm.toEquiv
  let α₁ : MulAut (Matrix.SpecialLinearGroup (Fin 3) F) := (Φ.symm.trans α).trans Φ
  have hα₁ : ∀ x, α₁ x = Φ (α (Φ.symm x)) := fun x => rfl
  have hinv : ∀ x, α₁ (α₁ x) = x := by
    intro x
    rw [hα₁, hα₁, Φ.symm_apply_apply, hα2, Φ.apply_symm_apply]
  let P₁ : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) F) :=
    P.mapSurjective (f := Φ.toMonoidHom) Φ.surjective
  have hmemP₁ : ∀ x, x ∈ (P₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ↔
      ∃ y ∈ P, Φ y = x := by
    intro x
    change x ∈ Subgroup.map Φ.toMonoidHom (P : Subgroup ↥K) ↔ _
    exact Subgroup.mem_map
  have hP₁ : ∀ x ∈ P₁, α₁ x ∈ P₁ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmemP₁ x).mp hx
    rw [hα₁, Φ.symm_apply_apply]
    exact (hmemP₁ _).mpr ⟨α y, hαP y hy, rfl⟩
  have hnotLin : ¬ P4SL34.LinInd α₁ := by
    rintro ⟨Θ, hΘ⟩
    apply hnot
    let E : U ≃+ U := ψ.toAddEquiv.trans (Θ.trans ψ.toAddEquiv.symm)
    let c : GLV U := LinearEquiv.ofBijective (E.toAddMonoidHom.toZModLinearMap 2) E.bijective
    have hc : ∀ u, ψ (c u) = Θ (ψ u) := by
      intro u
      show ψ (E u) = Θ (ψ u)
      simp [E]
    have key : ∀ (k : ↥K) (u : U), ((α k : ↥K) : GLV U) (c u) = c ((k : GLV U) u) := by
      intro k u
      apply ψ.injective
      rw [hψ (α k) (c u), hc, hc, hψ k u, ← hΦ k, hΘ (Φ k) (ψ u), hα₁, Φ.symm_apply_apply, hΦ]
    refine ⟨c, fun k => ?_⟩
    refine LinearEquiv.ext fun u => ?_
    show ((α k : ↥K) : GLV U) u = c ((k : GLV U) (c.symm u))
    rw [← key k (c.symm u), LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx, hxsq⟩ := P4SL34.exists_sq_ne_one α₁ P₁ hP₁ hinv hnotLin
  obtain ⟨y, hy, rfl⟩ := (hmemP₁ x).mp hx
  refine ⟨y, hy, y, hy, ?_⟩
  rintro ⟨-, hsq⟩
  apply hxsq
  have h := congrArg Φ hsq
  rw [map_mul, map_mul, map_inv, map_one] at h
  rw [hα₁, Φ.symm_apply_apply]
  exact h

end CFSG.Quasithin.G11.P4SL34

namespace CFSG.Quasithin.G11

theorem outerSL34Input : OuterSL34Input := by
  intro U _ _ _ K hnat α P hαP hα2 hnot
  exact P4SL34.outer_general K hnat α P hαP hα2 hnot

end CFSG.Quasithin.G11
