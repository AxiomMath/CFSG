module

public import CFSG.RankThree.GF2n.Stroth80.Satz5Stroth
public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

section OrthogonalModule

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

@[expose] def OrthogonalModuleRep {R N : Subgroup G}
    (M₀ : Tim79.QuadModel Q Z K γ) : Prop :=
  ∃ φ : R →* GL (Fin 3 ⊕ Fin 3) K,
    φ.range = StatedOmega (StatedQuadPlus 3 K) ∧
    φ.ker = N.subgroupOf R ∧
    ∃ e : M₀.E ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K),
      (∀ v, quadPlus 3 K (e v) = M₀.Qf v) ∧
      ∀ (g : R) (x : G), x ∈ Q →
        e (M₀.π ((g : G) * x * (g : G)⁻¹)) =
          ((φ g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
            e (M₀.π x)

theorem orthogonalModuleRep_inducesOmega {R N : Subgroup G}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : OrthogonalModuleRep (Q := Q) (Z := Z) (K := K) M₀ (R := R) (N := N)) :
    InducesOmega M₀ R := by
  classical
  obtain ⟨φ, hφrange, -, e, he, hact⟩ := h
  let c : (M₀.E ≃ₗ[K] M₀.E) ≃* ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
    { toFun := fun T => e.symm.trans (T.trans e)
      invFun := fun T => e.trans (T.trans e.symm)
      left_inv := fun T => by ext x; simp
      right_inv := fun T => by ext x; simp
      map_mul' := fun T S => by ext x; simp [mul_assoc] }
  have hmap : (TauCeti.QuadraticMap.orthogonalGroup M₀.toQuadraticForm).map c.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) := by
    ext A
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        have hTv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hT (e.symm v)
        have hTv' : M₀.Qf (T (e.symm v)) = M₀.Qf (e.symm v) := hTv
        change quadPlus 3 K (e (T (e.symm v))) = quadPlus 3 K v
        rw [he, hTv', ← he (e.symm v)]
        simp
    · intro hA
      refine ⟨c.symm A, ?_, by simp⟩
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        have hAv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hA (e v)
        change M₀.Qf (e.symm (A (e v))) = M₀.Qf v
        rw [← he (e.symm (A (e v))), LinearEquiv.apply_symm_apply, hAv, he]
  have homega : (Satz5.omegaOf M₀).map c.toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)⁆ := by
    rw [Satz5.omegaOf, Subgroup.map_commutator, hmap]
  intro T hT
  have hcT : c T ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)⁆ := by
    rw [← homega]
    exact Subgroup.mem_map_of_mem c.toMonoidHom hT
  set A : GL (Fin 3 ⊕ Fin 3) K :=
    (toLinEquiv (Fin 3 ⊕ Fin 3) K).symm (c T) with hA
  have hAmem : A ∈ StatedOmega (StatedQuadPlus 3 K) := by
    rw [statedOmega_eq_comap (Q := quadPlus 3 K) (Q₀ := StatedQuadPlus 3 K)
      (coe_quadPlus 3 K), Subgroup.mem_comap]
    change toLinEquiv (Fin 3 ⊕ Fin 3) K A ∈ _
    rw [hA, MulEquiv.apply_symm_apply]
    exact hcT
  have hArange : A ∈ φ.range := by rwa [hφrange]
  obtain ⟨g, hφg⟩ := MonoidHom.mem_range.mp hArange
  refine ⟨(g : G), g.2, ?_⟩
  intro x hx
  have h1 := hact g x hx
  have h2 : ((φ g : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ e (M₀.π x) = e (T (M₀.π x)) := by
    rw [hφg, hA, ← toLinEquiv_apply]
    rw [MulEquiv.apply_symm_apply]
    change e (T (e.symm (e (M₀.π x)))) = e (T (M₀.π x))
    simp
  apply e.injective
  rw [h1, h2]

end OrthogonalModule

section Main

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem l4Orthogonal_case_false (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀)
    {X₁ X₂ : Subgroup G} (hX₂ : X₂ = Q) (hX₁ : X₁ = Z)
    (nat : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) X₂ X₁ (XbarPreCenter M Q Z B))
    (hΩ : InducesOmega M₀ (XbarPre M Q Z B)) : False :=
  BeisiegelSatz5Stroth hc.hyp hD hw hn (XbarPre_le_H0 hc) hΩ

theorem l4Orthogonal_case_false_of_orthogonalModuleRep (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀)
    {X₁ X₂ : Subgroup G} (hX₂ : X₂ = Q) (hX₁ : X₁ = Z)
    (nat : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) X₂ X₁ (XbarPreCenter M Q Z B))
    (hrep : OrthogonalModuleRep (Q := Q) (Z := Z) (K := K) M₀
      (R := XbarPre M Q Z B) (N := XbarPreCenter M Q Z B)) : False :=
  l4Orthogonal_case_false hc hw hn hD hX₂ hX₁ nat (orthogonalModuleRep_inducesOmega hrep)

end Main

end CFSG.RankThree.GF2n.Stroth80

