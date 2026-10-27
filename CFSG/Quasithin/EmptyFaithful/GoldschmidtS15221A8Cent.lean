module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL42Core
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.S15221

open Equiv Equiv.Perm CFSG.QuasithinUnique.Vol2Native.L239.L42Insp

@[expose] def cent8 : Subgroup (Perm (Fin 8)) :=
  Subgroup.centralizer {tau0} ⊓ alternatingGroup (Fin 8)

theorem tau0_eq : tau0 = swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 := by
  apply pn_inj
  rw [pn_tau0, pn_mul, pn_mul, pn_mul, pn_swap, pn_swap, pn_swap, pn_swap]
  decide +kernel

@[expose] def pairOf (i : Fin 8) : Fin 4 := ⟨i.val / 2, by omega⟩

@[expose] def repOf (k : Fin 4) : Fin 8 := ⟨2 * k.val, by omega⟩

theorem pairOf_repOf : ∀ k : Fin 4, pairOf (repOf k) = k := by decide

theorem pairOf_tau0 : ∀ i : Fin 8, pairOf (tau0 i) = pairOf i := by
  rw [tau0_eq]
  decide +kernel

theorem same_pair : ∀ i j : Fin 8, pairOf i = pairOf j → j = i ∨ j = tau0 i := by
  rw [tau0_eq]
  decide +kernel

theorem pairOf_repOf_pairOf : ∀ i : Fin 8, pairOf (repOf (pairOf i)) = pairOf i := by decide

theorem tau0_involutive : ∀ i : Fin 8, tau0 (tau0 i) = i := fun i => by
  have := congrArg (fun f : Perm (Fin 8) => f i) tau0_sq
  simpa using this

section Pairs

variable {σ : Perm (Fin 8)}

theorem pairOf_eq_of_comm (hσ : tau0 * σ = σ * tau0) {i j : Fin 8} (h : pairOf i = pairOf j) :
    pairOf (σ i) = pairOf (σ j) := by
  rcases same_pair i j h with rfl | rfl
  · rfl
  · have h1 : σ (tau0 i) = tau0 (σ i) := by
      have := congrArg (fun f : Perm (Fin 8) => f i) hσ
      simpa using this.symm
    rw [h1, pairOf_tau0]

@[expose] def prFun (σ : Perm (Fin 8)) (k : Fin 4) : Fin 4 := pairOf (σ (repOf k))

theorem pairOf_apply (hσ : tau0 * σ = σ * tau0) (i : Fin 8) :
    pairOf (σ i) = prFun σ (pairOf i) :=
  pairOf_eq_of_comm hσ (pairOf_repOf_pairOf i).symm

theorem prFun_mul {σ τ : Perm (Fin 8)} (hσ : tau0 * σ = σ * tau0) (k : Fin 4) :
    prFun (σ * τ) k = prFun σ (prFun τ k) := by
  show pairOf ((σ * τ) (repOf k)) = prFun σ (pairOf (τ (repOf k)))
  rw [Perm.mul_apply]
  exact pairOf_apply hσ _

theorem comm_inv (hσ : tau0 * σ = σ * tau0) : tau0 * σ⁻¹ = σ⁻¹ * tau0 :=
  Commute.inv_right (show Commute tau0 σ from hσ)

theorem prFun_one : prFun (1 : Perm (Fin 8)) = id := funext fun k => pairOf_repOf k

@[expose] def prPerm (σ : Perm (Fin 8)) (hσ : tau0 * σ = σ * tau0) : Perm (Fin 4) where
  toFun := prFun σ
  invFun := prFun σ⁻¹
  left_inv := fun k => by
    rw [← prFun_mul (comm_inv hσ), inv_mul_cancel, prFun_one]
    rfl
  right_inv := fun k => by
    have h := comm_inv hσ
    rw [← prFun_mul (σ := σ) hσ, mul_inv_cancel, prFun_one]
    rfl

end Pairs

theorem comm_of_mem_centralizer {σ : Perm (Fin 8)} (h : σ ∈ Subgroup.centralizer {tau0}) :
    tau0 * σ = σ * tau0 := (Subgroup.mem_centralizer_singleton_iff.mp h).symm

@[expose] def prHom : ↥(Subgroup.centralizer {tau0}) →* Perm (Fin 4) where
  toFun σ := prPerm σ.1 (comm_of_mem_centralizer σ.2)
  map_one' := Equiv.ext fun k => congrFun prFun_one k
  map_mul' σ τ := Equiv.ext fun k => prFun_mul (σ := σ.1) (τ := τ.1) (comm_of_mem_centralizer σ.2) k

@[expose] def sigma8 : ↥cent8 →* Perm (Fin 4) := prHom.comp (Subgroup.inclusion inf_le_left)

theorem sigma8_apply (σ : ↥cent8) (k : Fin 4) :
    sigma8 σ k = pairOf ((σ : Perm (Fin 8)) (repOf k)) := rfl

theorem sq_eq_one_of_prFun_eq {σ : Perm (Fin 8)} (hσ : tau0 * σ = σ * tau0)
    (h : ∀ k, prFun σ k = k) : σ * σ = 1 := by
  refine Equiv.ext fun i => ?_
  have hp : pairOf (σ i) = pairOf i := by rw [pairOf_apply hσ, h]
  have hσt : ∀ j, σ (tau0 j) = tau0 (σ j) := fun j => by
    have := congrArg (fun f : Perm (Fin 8) => f j) hσ
    simpa using this.symm
  rcases same_pair i (σ i) hp.symm with h1 | h1
  · show σ (σ i) = i
    rw [h1]
    exact h1
  · show σ (σ i) = i
    rw [h1, hσt, h1, tau0_involutive]

theorem isPGroup_ker_sigma8 : IsPGroup 2 sigma8.ker := by
  intro g
  refine ⟨1, ?_⟩
  have hσ : tau0 * (g.1 : ↥cent8).1 = (g.1 : ↥cent8).1 * tau0 :=
    comm_of_mem_centralizer (g.1 : ↥cent8).2.1
  have hk : ∀ k, prFun (g.1 : ↥cent8).1 k = k := fun k => by
    have := g.2
    rw [MonoidHom.mem_ker] at this
    have h2 := congrArg (fun f : Perm (Fin 4) => f k) this
    exact h2
  apply Subtype.ext
  apply Subtype.ext
  have := sq_eq_one_of_prFun_eq hσ hk
  simpa [pow_two] using this

@[expose] def liftFun (τ : Perm (Fin 4)) (i : Fin 8) : Fin 8 :=
  ⟨2 * (τ ⟨i.val / 2, by omega⟩).val + i.val % 2, by
    have := (τ ⟨i.val / 2, by omega⟩).isLt
    omega⟩

theorem liftFun_left : ∀ (τ : Perm (Fin 4)) (i : Fin 8), liftFun τ⁻¹ (liftFun τ i) = i := by
  decide +kernel

theorem liftFun_right : ∀ (τ : Perm (Fin 4)) (i : Fin 8), liftFun τ (liftFun τ⁻¹ i) = i := by
  decide +kernel

@[expose] def lift8 (τ : Perm (Fin 4)) : Perm (Fin 8) where
  toFun := liftFun τ
  invFun := liftFun τ⁻¹
  left_inv := liftFun_left τ
  right_inv := liftFun_right τ

theorem lift8_comm : ∀ τ : Perm (Fin 4), tau0 * lift8 τ = lift8 τ * tau0 := by
  rw [tau0_eq]
  decide +kernel

theorem lift8_sign : ∀ τ : Perm (Fin 4), sign (lift8 τ) = 1 := by decide +kernel

theorem prFun_lift8 : ∀ (τ : Perm (Fin 4)) (k : Fin 4), prFun (lift8 τ) k = τ k := by
  decide +kernel

theorem sigma8_surjective : Function.Surjective sigma8 := by
  intro τ
  have hc : lift8 τ ∈ cent8 :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (lift8_comm τ).symm,
      Equiv.Perm.mem_alternatingGroup.mpr (lift8_sign τ)⟩
  refine ⟨⟨lift8 τ, hc⟩, Equiv.ext fun k => ?_⟩
  exact (sigma8_apply ⟨lift8 τ, hc⟩ k).trans (prFun_lift8 τ k)

theorem tau0_mem_P0 : tau0 ∈ P0 := by
  rw [mem_P0, pn_tau0]
  decide +kernel

end CFSG.Quasithin.S15221
