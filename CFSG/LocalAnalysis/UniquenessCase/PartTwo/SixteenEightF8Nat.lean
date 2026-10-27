module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def s16gNatAut (g : GL ι K) : MulAut (Multiplicative (ι → K)) where
  toFun x := Multiplicative.ofAdd ((g : Matrix ι ι K) *ᵥ Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd x)
  left_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel]
    simp
  right_inv x := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  map_mul' x y := by
    simp [Matrix.mulVec_add]

@[expose] def s16gNatHom (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    GL ι K →* MulAut (Multiplicative (ι → K)) where
  toFun := s16gNatAut
  map_one' := by
    ext x
    simp [s16gNatAut]
  map_mul' g h := by
    ext x
    simp [s16gNatAut, Matrix.mulVec_mulVec]

theorem s16gNatHom_apply (g : GL ι K) (x : Multiplicative (ι → K)) :
    s16gNatHom ι K g x =
      Multiplicative.ofAdd ((g : Matrix ι ι K) *ᵥ Multiplicative.toAdd x) := rfl

theorem s16gNatHom_eq_natAct (Γ : Subgroup (GL ι K)) (γ : ↥Γ) (x : Multiplicative (ι → K)) :
    s16gNatHom ι K (γ : GL ι K) x = CFSG.Quasithin.natAct Γ γ x := rfl

theorem s16gNatHom_injective : Function.Injective (s16gNatHom ι K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  ext i j
  have h := congrArg (fun a : MulAut (Multiplicative (ι → K)) =>
    Multiplicative.toAdd (a (Multiplicative.ofAdd (Pi.single j (1 : K))))) hg
  have h' := congrFun h i
  simpa [s16gNatHom_apply, Matrix.one_apply, Matrix.mulVec_single, Pi.single_apply,
    Matrix.mulVec, dotProduct] using h'

@[expose] def s16gLin (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    Subgroup (MulAut (Multiplicative (ι → K))) :=
  (s16gNatHom ι K).range

@[expose] def s16gNorm (Γ : Subgroup (GL ι K)) : Subgroup (MulAut (Multiplicative (ι → K))) :=
  Subgroup.normalizer ((Γ.map (s16gNatHom ι K) : Subgroup (MulAut (Multiplicative (ι → K)))) :
    Set (MulAut (Multiplicative (ι → K))))

theorem s16g_mem_norm_natHom_iff (Γ : Subgroup (GL ι K)) (g : GL ι K) :
    s16gNatHom ι K g ∈ s16gNorm Γ ↔ g ∈ Subgroup.normalizer (Γ : Set (GL ι K)) := by
  rw [s16gNorm, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  have key : ∀ h : GL ι K, s16gNatHom ι K h ∈ Γ.map (s16gNatHom ι K) ↔ h ∈ Γ := fun h =>
    Subgroup.mem_map_iff_mem s16gNatHom_injective
  have conj : ∀ h : GL ι K, s16gNatHom ι K g * s16gNatHom ι K h * (s16gNatHom ι K g)⁻¹ =
      s16gNatHom ι K (g * h * g⁻¹) := fun h => by simp [map_mul, map_inv]
  constructor
  · intro H h
    rw [← key h, H (s16gNatHom ι K h), conj, key]
  · intro H a
    by_cases ha : a ∈ s16gLin ι K
    · obtain ⟨h, rfl⟩ := ha
      rw [key, conj, key, H h]
    · have hmap : Γ.map (s16gNatHom ι K) ≤ s16gLin ι K := fun x hx => by
        obtain ⟨y, -, rfl⟩ := hx
        exact ⟨y, rfl⟩
      have hg : s16gNatHom ι K g ∈ s16gLin ι K := ⟨g, rfl⟩
      have hn : s16gNatHom ι K g * a * (s16gNatHom ι K g)⁻¹ ∉ s16gLin ι K := fun hc => by
        apply ha
        have := (s16gLin ι K).mul_mem ((s16gLin ι K).mul_mem ((s16gLin ι K).inv_mem hg) hc) hg
        simpa [mul_assoc] using this
      exact ⟨fun h => (ha (hmap h)).elim, fun h => (hn (hmap h)).elim⟩

theorem s16g_charP_two [Finite K] (hK : Nat.card K = 8) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

