module

public import CFSG.Quasithin.Vol2.Ch10SecKGCFd
public import CFSG.Quasithin.Vol2.Ch10SecQ34MK
public import CFSG.Quasithin.Vol2.Ch10SecQ34ML

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2] (a : ℕ) {V : Type} [CommGroup V]
  {H : Subgroup (MulAut V)} {π : ↥(StatedSL 2 K) →* ↥H} {BE : V ≃* ↥(hermSub a (Fin 2) K)}

theorem smH_comm (hπ : Function.Surjective π)
    (hBE : ∀ γ v, hmat a (BE (((π γ : ↥H) : MulAut V) v)) =
      smat γ * hmat a (BE v) * (frobPow a (smat γ))ᵀ)
    (S : Subfield K) (hS : ∀ c, c ∈ S ↔ c ^ 2 ^ a = c) :
    ∀ h ∈ H, ∀ c v, smH a BE S hS c (h v) = h (smH a BE S hS c v) := by
  intro h hh c v
  obtain ⟨γ, hγ⟩ := hπ ⟨h, hh⟩
  rw [show h = ((π γ : ↥H) : MulAut V) from (congrArg Subtype.val hγ).symm]
  apply BE.injective
  apply hmat_injective a
  rw [hmat_smH, hBE, hBE, hmat_smH, Matrix.mul_smul, Matrix.smul_mul]

theorem smH_commutant [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a))
    (hBE : ∀ γ v, hmat a (BE (((π γ : ↥H) : MulAut V) v)) =
      smat γ * hmat a (BE v) * (frobPow a (smat γ))ᵀ)
    (S : Subfield K) (hS : ∀ c, c ∈ S ↔ c ^ 2 ^ a = c) :
    ∀ f : V →* V, (∀ h ∈ H, ∀ v, f (h v) = h (f v)) → ∃ c, ∀ v, f v = smH a BE S hS c v := by
  classical
  intro f hf
  let f' : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K := fun X =>
    if hX : (frobPow a X)ᵀ = X then hmat a (BE (f (BE.symm ⟨Multiplicative.ofAdd X, hX⟩)))
    else 0
  have hf' : ∀ w : ↥(hermSub a (Fin 2) K), f' (hmat a w) = hmat a (BE (f (BE.symm w))) := by
    intro w
    have hw : (frobPow a (hmat a w))ᵀ = hmat a w := w.2
    simp only [f', hw, dite_true]
    rfl
  have hmk : ∀ X (hX : (frobPow a X)ᵀ = X),
      hmat a (⟨Multiplicative.ofAdd X, hX⟩ : ↥(hermSub a (Fin 2) K)) = X := fun _ _ => rfl
  have htw : ∀ (γ : ↥(StatedSL 2 K)) (w : ↥(hermSub a (Fin 2) K)),
      f' (C10P34.tw a (smat γ) (hmat a w)) = C10P34.tw a (smat γ) (f' (hmat a w)) := by
    intro γ w
    have h1 : C10P34.tw a (smat γ) (hmat a w) =
        hmat a (BE (((π γ : ↥H) : MulAut V) (BE.symm w))) := by
      rw [hBE, MulEquiv.apply_symm_apply]
      rfl
    rw [h1, hf', hf', MulEquiv.symm_apply_apply, hf _ (π γ).2, hBE]
    rfl
  obtain ⟨μ, hμq, hμ⟩ := C10P34.eq_smul_of_comm_twist a ha hK f'
    (fun X hX => by
      rw [← hmk X hX, hf']
      exact (BE (f (BE.symm ⟨Multiplicative.ofAdd X, hX⟩))).2)
    (fun X Y hX hY => by
      rw [← hmk X hX, ← hmk Y hY, ← hmat_mul, hf', hf', hf', map_mul, map_mul, map_mul,
        hmat_mul])
    (fun t X hX => by
      rw [← hmk X hX, ← C10P34.coe_uSL t, htw])
    (fun X hX => by
      rw [← hmk X hX, ← C10P34.coe_wSL, htw])
  refine ⟨⟨μ, (hS μ).mpr hμq⟩, fun v => BE.injective (hmat_injective a ?_)⟩
  rw [hmat_smH]
  have h2 := hμ (hmat a (BE v)) (BE v).2
  rw [hf', MulEquiv.symm_apply_apply] at h2
  exact h2

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KG
