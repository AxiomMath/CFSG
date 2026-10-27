module

public import CFSG.Quasithin.Vol2.Ch9Setup
public import CFSG.Quasithin.Background.HOm4Norm
public import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem conjAct_mul_mul_inv {V : Subgroup G} (x y : Subgroup.normalizer (V : Set G)) :
    conjAct V (x * y * x⁻¹) = conjAct V x * conjAct V y * (conjAct V x)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

omit [Finite G] in
theorem autOn_le_normalizer {V X Z : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) :
    autOn X V ≤ Subgroup.normalizer (autOn Z V : Set (MulAut V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hXZ

namespace Setup

variable (S : Setup T L I n)
include S

theorem autOn_M_le_normalizer : autOn (fsuM T L) (fsuV T I) ≤
    Subgroup.normalizer (autOn (fsuL0 T L) (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
  autOn_le_normalizer S.hMN le_rfl

theorem exists_coord : ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
    Fintype.card K = 2 ^ n ∧ ∃ e : ↥(fsuV T I) ≃* Om4.VM K,
      (autOn (fsuL0 T L) (fsuV T I)).map (MulAut.congr e).toMonoidHom =
        (Om4.rho (K := K)).range := by
  have := S.comm
  obtain ⟨-, -, K, _, _, hK, π, hπ⟩ := S.row
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hK'
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv rfl hπ
  let e : ↥(fsuV T I) ≃* Om4.VM K := E.trans Subgroup.topEquiv
  have key : ∀ γ : (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).Gam,
      MulAut.congr e ((π γ : ↥(autOn (fsuL0 T L) (fsuV T I))) : MulAut ↥(fsuV T I)) =
        Om4.lr ((γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)).1 : GL (Fin 2) K)
          ((γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)).2 : GL (Fin 2) K) := by
    intro γ
    refine MulEquiv.ext fun X => ?_
    show ((E (((π γ : ↥(autOn (fsuL0 T L) (fsuV T I))) : MulAut ↥(fsuV T I)) (e.symm X)) :
      ↥(tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).sec) :
        (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).Amb) = _
    rw [hE γ (e.symm X)]
    show (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).act γ (e (e.symm X)) = _
    rw [e.apply_symm_apply]
    rfl
  have hcoe : ∀ g : ↥(StatedSL 2 K), Matrix.SpecialLinearGroup.toGL
      ((specialLinearGroupEquivStatedSL 2 K).symm g) = (g : GL (Fin 2) K) := fun g =>
    congrArg Subtype.val ((specialLinearGroupEquivStatedSL 2 K).apply_symm_apply g)
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK', e, ?_⟩
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨γ, hγ⟩ := hπ.1 ⟨ψ, hψ⟩
    refine ⟨((specialLinearGroupEquivStatedSL 2 K).symm γ.1,
      (specialLinearGroupEquivStatedSL 2 K).symm γ.2), ?_⟩
    rw [Om4.rho_apply, hcoe, hcoe]
    have h1 := key γ
    rw [hγ] at h1
    exact h1.symm
  · rintro ⟨⟨g, h⟩, rfl⟩
    let γ₀ : (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).Gam :=
      (specialLinearGroupEquivStatedSL 2 K g, specialLinearGroupEquivStatedSL 2 K h)
    refine ⟨(π γ₀ : MulAut ↥(fsuV T I)), (π γ₀).2, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, key γ₀, Om4.rho_apply]
    rfl

theorem exists_form {K : Type} [Field K] [Fintype K] [CharP K 2] (hK : Fintype.card K = 2 ^ n)
    {e : ↥(fsuV T I) ≃* Om4.VM K}
    (he : (autOn (fsuL0 T L) (fsuV T I)).map (MulAut.congr e).toMonoidHom =
      (Om4.rho (K := K)).range)
    {φ : MulAut ↥(fsuV T I)}
    (hφ : φ ∈ Subgroup.normalizer (autOn (fsuL0 T L) (fsuV T I) : Set (MulAut ↥(fsuV T I)))) :
    ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), MulAut.congr e φ = Om4.lr A B * Om4.frM τ ∨
      MulAut.congr e φ = Om4.lr A B * Om4.frM τ * Om4.trM := by
  have h4 : 4 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) S.two_le
  apply Om4.exists_eq_of_mem_normalizer h4
  rw [← he, ← Subgroup.map_equiv_normalizer_eq]
  exact ⟨φ, hφ, rfl⟩

end Setup

end CFSG.Quasithin.H13.Ch9
