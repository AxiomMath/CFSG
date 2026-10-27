module

public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3A

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem exists_scalar_of_intertwine {K : Type} [Group K] (α₀ : K →* ↥(StatedSL 2 F))
    (hs : Function.Surjective α₀) (ρK : K → Matrix (Fin 2) (Fin 2) F)
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ (k : K) (v : Fin 2 → F),
      T (ρK k *ᵥ v) = (((α₀ k : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v)
    (a : F) : ∃ μ : F, ∀ w : Fin 2 → F, T (a • w) = μ • T w := by
  let φ : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => T (a • T.symm v)
      map_zero' := by rw [map_zero, smul_zero, map_zero]
      map_add' := fun v w => by rw [map_add, smul_add, map_add] }
  have hφ : ∀ g : ↥(StatedSL 2 F), ∀ v, φ (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ φ v := by
    intro g v
    obtain ⟨k, rfl⟩ := hs g
    have h1 : T.symm ((((α₀ k : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        ρK k *ᵥ T.symm v := by
      apply T.injective
      rw [hT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    show T (a • T.symm _) = _ *ᵥ T (a • T.symm v)
    rw [h1, ← Matrix.mulVec_smul, hT]
  obtain ⟨μ, hμ⟩ := exists_smul_of_comm_sl le_rfl φ hφ
  refine ⟨μ, fun w => ?_⟩
  have := hμ (T w)
  simpa [φ] using this

theorem tScalar_pow (T : (Fin 2 → F) ≃+ (Fin 2 → F)) {a μ : F}
    (h : ∀ w : Fin 2 → F, T (a • w) = μ • T w) (n : ℕ) (w : Fin 2 → F) :
    T (a ^ n • w) = μ ^ n • T w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ih, h, pow_succ, mul_smul]

variable {G : Type} [Group G]

theorem isNatEigSection_of_coords {K : Subgroup G} {y : G} (α₀ : ↥K →* ↥(StatedSL 2 F))
    {C S : Subgroup G} (κ : ↥S →* Multiplicative (Fin 2 → F)) (hκs : Function.Surjective κ)
    (hκk : ∀ c : ↥S, κ c = 1 ↔ (c : G) ∈ C) (ρK : ↥K → Matrix (Fin 2) (Fin 2) F)
    (hκK : ∀ (k : ↥K) (c c' : ↥S), (c' : G) = k * c * (k : G)⁻¹ →
      Multiplicative.toAdd (κ c') = ρK k *ᵥ Multiplicative.toAdd (κ c))
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ (k : ↥K) (v : Fin 2 → F),
      T (ρK k *ᵥ v) = (((α₀ k : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v)
    {a μ : F} (hy : ∀ c c' : ↥S, (c' : G) = y * c * y⁻¹ →
      Multiplicative.toAdd (κ c') = a • Multiplicative.toAdd (κ c))
    (hμ : ∀ w : Fin 2 → F, T (a • w) = μ • T w) :
    IsNatEigSection K y α₀ C S μ := by
  let Tm : Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F) :=
    AddMonoidHom.toMultiplicative T.toAddMonoidHom
  refine ⟨Tm.comp κ, ?_, fun c => ?_, fun k c c' h => ?_, fun c c' h => ?_⟩
  · intro w
    obtain ⟨c, hc⟩ := hκs (Multiplicative.ofAdd (T.symm (Multiplicative.toAdd w)))
    refine ⟨c, ?_⟩
    simp [Tm, hc]
  · rw [← hκk c]
    simp only [Tm, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · intro h
      have h1 : T (Multiplicative.toAdd (κ c)) = 0 := congrArg Multiplicative.toAdd h
      rw [AddEquiv.map_eq_zero_iff] at h1
      exact h1
    · intro h
      rw [h]
      exact map_one _
  · simp only [Tm, MonoidHom.coe_comp, Function.comp_apply]
    show T (Multiplicative.toAdd (κ c')) = _ *ᵥ T (Multiplicative.toAdd (κ c))
    rw [hκK k c c' h, hT]
  · simp only [Tm, MonoidHom.coe_comp, Function.comp_apply]
    show T (Multiplicative.toAdd (κ c')) = μ • T (Multiplicative.toAdd (κ c))
    rw [hy c c' h, hμ]

end CFSG.Quasithin.H13.Ch4.B414.M
