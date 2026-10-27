module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaPlus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.Isometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaPlusFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.Quasithin.Background.RealizesFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

local notation "ιP" => Fin 2 ⊕ Fin 2

private lemma mulAut_congr_eq_s16gNatHom {W : Type} [CommGroup W] {K : Type} [Field K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {e : W ≃* Multiplicative (ι → K)} {h : MulAut W}
    {A : GL ι K} (he : ∀ w : W, Multiplicative.toAdd (e (h w)) =
      (A : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w)) :
    MulAut.congr e h = s16gNatHom ι K A := by
  refine MulEquiv.ext fun v => ?_
  refine Multiplicative.toAdd.injective ?_
  rw [s16gNatHom_apply, toAdd_ofAdd, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.trans_apply, he, MulEquiv.apply_symm_apply]

theorem exists_plusCoords {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {n : ℕ}
    (hn : 2 ≤ n) (hN : NatOmegaPlus H ⊤ ⊥ 4 n) (S : Sylow 2 ↥H) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ e : W ≃* Multiplicative (ιP → K),
        H.map (MulAut.congr e).toMonoidHom =
            (StatedOmega (StatedQuadPlus 2 K)).map (s16gNatHom ιP K) ∧
        ∀ w : W, w ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) ↔
          ∃ c' : K, Multiplicative.toAdd (e w) = c' • KTabC.e1P K := by
  classical
  obtain ⟨-, K, hK, hKfin, hKcard, hR⟩ := hN
  letI : Field K := hK
  letI : Finite K := hKfin
  haveI hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨K, hK, hKfin, hchar, hKcard, ?_⟩
  let Γ : Subgroup (GL ιP K) := StatedOmega (StatedQuadPlus 2 K)
  have hRΓ : (CFSG.Quasithin.FFModel.nat Γ).Realizes H ⊤ ⊥ := hR
  obtain ⟨π, e₀, he₀⟩ := KTabC.exists_natEquiv (K := K) (ι := ιP) hRΓ
  let S' : Sylow 2 ↥Γ := S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective
  obtain ⟨x, hx⟩ := KTabC.sylowFixedLine_plus K h4 S'
  let X : GL ιP K := (x : GL ιP K)
  let A : GL ιP K := ((x⁻¹ : ↥Γ) : GL ιP K)
  have hA : A = X⁻¹ := Subgroup.coe_inv Γ x
  have hAΓ : A ∈ Γ := (x⁻¹ : ↥Γ).2
  have hXΓ : X ∈ Γ := x.2
  have hXA : X * A = 1 := by rw [hA, mul_inv_cancel]
  have hAX : A * X = 1 := by rw [hA, inv_mul_cancel]
  let e : W ≃* Multiplicative (ιP → K) := e₀.trans (s16gNatHom ιP K A)
  have heA : ∀ w : W, Multiplicative.toAdd (e w) =
      (A : Matrix ιP ιP K) *ᵥ Multiplicative.toAdd (e₀ w) := fun _ => rfl
  have he₀' : ∀ (h : ↥H) (w : W), Multiplicative.toAdd (e₀ ((h : MulAut W) w)) =
      (((π.symm h : ↥Γ) : GL ιP K) : Matrix ιP ιP K) *ᵥ
        Multiplicative.toAdd (e₀ w) := by
    intro h w
    have h1 := he₀ (π.symm h) w
    rwa [MulEquiv.apply_symm_apply] at h1
  have hrow : ∀ h : ↥H, MulAut.congr e (h : MulAut W) =
      s16gNatHom ιP K (A * ((π.symm h : ↥Γ) : GL ιP K) * X) := by
    intro h
    refine mulAut_congr_eq_s16gNatHom (A := A * ((π.symm h : ↥Γ) : GL ιP K) * X) ?_
    intro w
    have hu : Multiplicative.toAdd (e₀ w) =
        (X : Matrix ιP ιP K) *ᵥ Multiplicative.toAdd (e w) := by
      rw [heA w, Matrix.mulVec_mulVec, ← Units.val_mul, hXA, Units.val_one,
        Matrix.one_mulVec]
    rw [heA ((h : MulAut W) w), he₀' h w, hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rfl
  have hmap : H.map (MulAut.congr e).toMonoidHom = Γ.map (s16gNatHom ιP K) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨h, hh, rfl⟩
      refine Subgroup.mem_map.mpr
        ⟨A * ((π.symm ⟨h, hh⟩ : ↥Γ) : GL ιP K) * X, ?_, (hrow ⟨h, hh⟩).symm⟩
      exact Γ.mul_mem (Γ.mul_mem hAΓ (π.symm ⟨h, hh⟩).2) hXΓ
    · rintro y ⟨γ, hγ, rfl⟩
      have hmem : A⁻¹ * γ * A ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hAΓ) hγ) hAΓ
      refine Subgroup.mem_map.mpr
        ⟨((π ⟨A⁻¹ * γ * A, hmem⟩ : ↥H) : MulAut W), (π ⟨A⁻¹ * γ * A, hmem⟩).2, ?_⟩
      change MulAut.congr e ((π ⟨A⁻¹ * γ * A, hmem⟩ : ↥H) : MulAut W) =
        s16gNatHom ιP K γ
      have hkey := hrow (π ⟨A⁻¹ * γ * A, hmem⟩)
      have hsym : ((π.symm (π ⟨A⁻¹ * γ * A, hmem⟩) : ↥Γ) : GL ιP K) = A⁻¹ * γ * A := by
        rw [MulEquiv.symm_apply_apply]
      rw [hsym] at hkey
      rw [hkey]
      have hXeq : X = A⁻¹ := by rw [hA, inv_inv]
      have harg : A * (A⁻¹ * γ * A) * X = γ := by
        rw [hXeq]
        group
      rw [harg]
  refine ⟨e, hmap, ?_⟩
  intro w
  have hfix : w ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) ↔
      ∃ c : K, Multiplicative.toAdd (e₀ w) =
        c • ((X : Matrix ιP ιP K) *ᵥ KTabC.e1P K) := by
    rw [CFSG.Quasithin.mem_fixV]
    have h1 : (∀ x ∈ (S : Subgroup ↥H).map H.subtype, x w = w) ↔
        ∀ s ∈ (S : Subgroup ↥H), (s : MulAut W) w = w := by
      constructor
      · intro hf s hs
        exact hf _ (Subgroup.mem_map_of_mem H.subtype hs)
      · rintro hf x ⟨s, hs, rfl⟩
        exact hf s hs
    rw [h1]
    have h2 : (∀ s ∈ (S : Subgroup ↥H), (s : MulAut W) w = w) ↔
        ∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ιP K) : Matrix ιP ιP K) *ᵥ
          Multiplicative.toAdd (e₀ w) = Multiplicative.toAdd (e₀ w) := by
      constructor
      · intro hf s hs
        have h3 := he₀' s w
        rw [hf s hs] at h3
        exact h3.symm
      · intro hf s hs
        apply e₀.injective
        apply Multiplicative.toAdd.injective
        rw [he₀' s w, hf s hs]
    rw [h2]
    exact (KTabC.fixed_iff_fixed_sylowMap π S (Multiplicative.toAdd (e₀ w))).trans
      (hx (Multiplicative.toAdd (e₀ w)))
  rw [hfix]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [heA w, hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, hAX,
      Units.val_one, Matrix.one_mulVec]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hv' : Multiplicative.toAdd (e₀ w) =
        (X : Matrix ιP ιP K) *ᵥ Multiplicative.toAdd (e w) := by
      rw [heA w, Matrix.mulVec_mulVec, ← Units.val_mul, hXA, Units.val_one,
        Matrix.one_mulVec]
    rw [hv', hc, Matrix.mulVec_smul]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
