module

public import CFSG.Quasithin.Vol2.Ch10SecC3L

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def IsSemilin (x : MulAut (WM K)) (σ : K ≃+* K) : Prop :=
  ∀ (c : K) (X : WM K), x (Multiplicative.ofAdd (c • Multiplicative.toAdd X)) =
    Multiplicative.ofAdd (σ c • Multiplicative.toAdd (x X))

theorem isSemilin_one : IsSemilin (1 : MulAut (WM K)) 1 := fun _ _ => rfl

theorem isSemilin_rho (g : SL K × SL K) : IsSemilin (rho K g) 1 := by
  intro c X
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd, toAdd_rho, Matrix.mul_smul, Matrix.smul_mul]
  rfl

theorem isSemilin_sc (y : Kˣ) : IsSemilin (sc y) 1 := by
  intro c X
  apply Multiplicative.toAdd.injective
  rw [toAdd_sc, toAdd_ofAdd, toAdd_ofAdd, toAdd_sc, smul_comm]
  rfl

theorem isSemilin_fa (σ : K ≃+* K) : IsSemilin (fa σ) σ := by
  intro c X
  apply Multiplicative.toAdd.injective
  rw [toAdd_fa, toAdd_ofAdd, toAdd_ofAdd, toAdd_fa]
  ext i j
  simp

theorem isSemilin_tau : IsSemilin (tau K) 1 := by
  intro c X
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau, toAdd_ofAdd, toAdd_ofAdd, toAdd_tau, Matrix.transpose_smul]
  rfl

theorem IsSemilin.mul {x y : MulAut (WM K)} {σ τ : K ≃+* K} (hx : IsSemilin x σ)
    (hy : IsSemilin y τ) : IsSemilin (x * y) (σ * τ) := by
  intro c X
  rw [MulAut.mul_apply, hy, hx]
  rfl

theorem IsSemilin.inv {x : MulAut (WM K)} {σ : K ≃+* K} (hx : IsSemilin x σ) :
    IsSemilin x⁻¹ σ⁻¹ := by
  intro c X
  apply x.injective
  rw [MulAut.apply_inv_self, hx]
  apply Multiplicative.toAdd.injective
  have hc : σ (σ⁻¹ c) = c := σ.apply_symm_apply c
  rw [toAdd_ofAdd, toAdd_ofAdd, MulAut.apply_inv_self, hc]

theorem IsSemilin.unique {x : MulAut (WM K)} {σ σ' : K ≃+* K} (hx : IsSemilin x σ)
    (hx' : IsSemilin x σ') : σ = σ' := by
  set E : WM K := Multiplicative.ofAdd (Matrix.single 0 0 1) with hEdef
  have hE : x E ≠ 1 := by
    intro h
    rw [← map_one x] at h
    have h3 := congrArg Multiplicative.toAdd (x.injective h)
    have h4 := congrFun (congrFun h3 0) 0
    simp [hEdef] at h4
  obtain ⟨i, j, hij⟩ : ∃ i j, Multiplicative.toAdd (x E) i j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hE (Multiplicative.toAdd.injective (Matrix.ext hall))
  refine RingEquiv.ext fun c => ?_
  have h1 := (hx c E).symm.trans (hx' c E)
  have h2 : σ c * Multiplicative.toAdd (x E) i j = σ' c * Multiplicative.toAdd (x E) i j := by
    have := congrArg (fun M : WM K => Multiplicative.toAdd M i j) h1
    simpa using this
  exact mul_right_cancel₀ hij h2

variable (K) in
@[expose] def linSub : Subgroup (MulAut (WM K)) where
  carrier := {x | IsSemilin x 1}
  one_mem' := isSemilin_one
  mul_mem' hx hy := by
    have := IsSemilin.mul hx hy
    rwa [mul_one] at this
  inv_mem' hx := by
    have := IsSemilin.inv hx
    rwa [inv_one] at this

theorem mem_linSub {x : MulAut (WM K)} : x ∈ linSub K ↔ IsSemilin x 1 := Iff.rfl

variable [CharP K 2] [Finite K]

theorem exists_isSemilin (hK : 4 ≤ Nat.card K) {x : MulAut (WM K)} (hx : x ∈ norm K) :
    ∃ σ : K ≃+* K, IsSemilin x σ := by
  obtain ⟨g, y, σ, rfl | rfl⟩ := mem_norm_form hK hx
  · refine ⟨1 * (1 * σ), ?_⟩
    exact (isSemilin_rho g).mul ((isSemilin_sc y).mul (isSemilin_fa σ))
  · refine ⟨1 * (1 * σ) * 1, ?_⟩
    exact ((isSemilin_rho g).mul ((isSemilin_sc y).mul (isSemilin_fa σ))).mul isSemilin_tau

@[expose] noncomputable def semHom (hK : 4 ≤ Nat.card K) {A : Subgroup (MulAut (WM K))}
    (hA : A ≤ norm K) : ↥A →* (K ≃+* K) where
  toFun a := Classical.choose (exists_isSemilin hK (hA a.2))
  map_one' := (Classical.choose_spec (exists_isSemilin hK (hA (A.one_mem)))).unique isSemilin_one
  map_mul' a b := (Classical.choose_spec (exists_isSemilin hK (hA (a * b).2))).unique
    ((Classical.choose_spec (exists_isSemilin hK (hA a.2))).mul
      (Classical.choose_spec (exists_isSemilin hK (hA b.2))))

theorem isSemilin_semHom (hK : 4 ≤ Nat.card K) {A : Subgroup (MulAut (WM K))}
    (hA : A ≤ norm K) (a : ↥A) : IsSemilin (a : MulAut (WM K)) (semHom hK hA a) :=
  Classical.choose_spec (exists_isSemilin hK (hA a.2))

theorem card_le_card_inf_linSub_mul (hK : 4 ≤ Nat.card K) {A : Subgroup (MulAut (WM K))}
    (hA : A ≤ norm K) :
    Nat.card A ≤ Nat.card ↥(A ⊓ linSub K) * Nat.card (K ≃+* K) := by
  have : Finite (WM K) := inferInstanceAs (Finite (Matrix (Fin 2) (Fin 2) K))
  have : Finite (MulAut (WM K)) := MulEquiv.finite_left
  have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    (fun σ τ h => RingEquiv.ext (congrFun h))
  set f := semHom hK hA with hf
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ linSub K) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, a.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
    · have h1 := isSemilin_semHom hK hA a.1
      rw [show f a.1 = 1 from a.2] at h1
      exact h1
    · exact (isSemilin_semHom hK hA ⟨x.1, x.2.1⟩).unique x.2.2
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker] at h1
  rw [← h1]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)

end CFSG.Quasithin.Vol2.Ch10.C3.Om
