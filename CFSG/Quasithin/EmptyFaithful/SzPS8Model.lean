module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Torus
public import CFSG.Quasithin.Background.P3OrthoOm4

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.G11 CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups Pointwise Matrix

namespace SzPS8

open L28

section Sylow

theorem exists_conj_of_isPGroup {X : Type*} [Group X] [Finite X] {P Q : Subgroup X}
    (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hQ2 : IsPGroup 2 Q) (hQidx : ¬ 2 ∣ Q.index) :
    ∃ g : X, ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SP : Sylow 2 X := hP2.toSylow hPidx
  let SQ : Sylow 2 X := hQ2.toSylow hQidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X SQ SP
  refine ⟨g, fun x => ?_⟩
  have h1 : (SP : Subgroup X) = MulAut.conj g • (SQ : Subgroup X) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hSP : x ∈ (SP : Subgroup X) ↔ x ∈ P := by simp [SP]
  rw [← hSP, h1, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : s ∈ Q := by simpa [SQ] using hs
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
  · intro h
    refine ⟨g⁻¹ * x * g, by simpa [SQ] using h, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]

theorem isPGroup_UU : IsPGroup 2 UU := by
  intro g
  obtain ⟨hg1, hg2⟩ := mem_UU_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨x, hx⟩ := hg1
  obtain ⟨y, hy⟩ := hg2
  have h1 : ((g : Pr).1) ^ 2 = 1 := by
    rw [← hx, pow_two]
    show up (Multiplicative.toAdd x) * up (Multiplicative.toAdd x) = 1
    rw [up_mul, CharTwo.add_self_eq_zero, up_zero]
  have h2 : ((g : Pr).2) ^ 2 = 1 := by
    rw [← hy, pow_two]
    show up (Multiplicative.toAdd y) * up (Multiplicative.toAdd y) = 1
    rw [up_mul, CharTwo.add_self_eq_zero, up_zero]
  show (g : Pr) ^ (2 ^ 1) = 1
  rw [pow_one]
  exact Prod.ext h1 h2

theorem index_UU : ¬ 2 ∣ UU.index := by
  rw [UU, Subgroup.index_prod]
  have h := index_U_gf (n := 2) (by norm_num)
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h1 | h1 <;> exact h h1

end Sylow

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def actEquiv (c : Pr) :
    Matrix (Fin 2) (Fin 2) F4 ≃+ Matrix (Fin 2) (Fin 2) F4 where
  toFun := act c
  invFun := act c⁻¹
  left_inv X := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv X := by rw [← act_mul, mul_inv_cancel, act_one]
  map_add' := act_add c

theorem rho'_apply' (z : Pr) (X : Matrix (Fin 2) (Fin 2) F4) :
    (rho' F4 z) X = act z X := specialRho_apply z X

theorem exists_model {H : Subgroup (GLV V)}
    (h : IsNaturalMatrixModule H (StatedOmega (StatedQuadPlus 2 F4))) :
    ∃ (θ : ↥H ≃* Pr) (e : V ≃+ Matrix (Fin 2) (Fin 2) F4),
      ∀ (x : ↥H) (v : V), e ((x : GLV V) v) = act (θ x) (e v) := by
  obtain ⟨φ, ψ, hφψ⟩ := h
  have h4 : 4 ≤ Nat.card F4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  let e1 := (Ψ F4).subgroupMap (StatedOmega (StatedQuadPlus 2 F4))
  let e2 := MulEquiv.subgroupCongr
    (show (StatedOmega (StatedQuadPlus 2 F4)).map (Ψ F4).toMonoidHom = (rho' F4).range by
      rw [map_statedOmega, commutator_eq_range h4])
  let e3 := (MonoidHom.ofInjective (rho'_injective (K := F4))).symm
  let θ : ↥H ≃* Pr := φ.trans (e1.trans (e2.trans e3))
  let e : V ≃+ Matrix (Fin 2) (Fin 2) F4 := ψ.toAddEquiv.trans (toMat F4).toAddEquiv
  refine ⟨θ, e, fun x v => ?_⟩
  have hθ : rho' F4 (θ x) = Ψ F4 ((φ x : ↥(StatedOmega (StatedQuadPlus 2 F4))) : GL _ _) := by
    show rho' F4 (e3 (e2 (e1 (φ x)))) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  have h1 : e ((x : GLV V) v) = toMat F4 ((((φ x : ↥(StatedOmega (StatedQuadPlus 2 F4))) :
      GL (Fin 2 ⊕ Fin 2) F4) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F4) *ᵥ ψ v) := by
    show toMat F4 (ψ ((x : GLV V) v)) = _
    rw [hφψ]
  rw [h1]
  show _ = act (θ x) (toMat F4 (ψ v))
  rw [← rho'_apply', hθ, Ψ_apply, LinearEquiv.symm_apply_apply]

theorem exists_model_sylow {H : Subgroup (GLV V)}
    (h : IsNaturalMatrixModule H (StatedOmega (StatedQuadPlus 2 F4)))
    {S : Subgroup (GLV V)} (hSH : S ≤ H) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex H) :
    ∃ (θ : ↥H ≃* Pr) (e : V ≃+ Matrix (Fin 2) (Fin 2) F4),
      (∀ (x : ↥H) (v : V), e ((x : GLV V) v) = act (θ x) (e v)) ∧
        ∀ x : ↥H, (x : GLV V) ∈ S ↔ θ x ∈ UU := by
  classical
  obtain ⟨θ₀, e₀, h₀⟩ := exists_model h
  set S₀ : Subgroup Pr := (S.subgroupOf H).map θ₀.toMonoidHom with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := by
    have h1 : IsPGroup 2 ↥(S.subgroupOf H) :=
      hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    exact h1.map θ₀.toMonoidHom
  have hS₀idx : ¬ 2 ∣ S₀.index := by
    have : S₀.index = (S.subgroupOf H).index := Subgroup.index_map_equiv _ θ₀
    rw [this]
    exact hSidx
  obtain ⟨c, hc⟩ := exists_conj_of_isPGroup hS₀2 hS₀idx isPGroup_UU index_UU
  refine ⟨θ₀.trans (MulAut.conj c⁻¹), e₀.trans (actEquiv c⁻¹), ?_, ?_⟩
  · intro x v
    show act c⁻¹ (e₀ ((x : GLV V) v)) = act (c⁻¹ * θ₀ x * c⁻¹⁻¹) (act c⁻¹ (e₀ v))
    rw [h₀, ← act_mul, ← act_mul]
    congr 1
    group
  · intro x
    show (x : GLV V) ∈ S ↔ c⁻¹ * θ₀ x * c⁻¹⁻¹ ∈ UU
    rw [inv_inv, ← hc (θ₀ x), hS₀, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
      Subgroup.mem_subgroupOf]

end Model

end SzPS8

end CFSG.Quasithin
