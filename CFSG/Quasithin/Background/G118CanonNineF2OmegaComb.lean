module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2Omega

open scoped Matrix

abbrev Ix : Type := Fin 1 ⊕ Fin 1 ⊕ Fin 2

@[expose] def qF (v : Ix → ZMod 2) : ZMod 2 :=
  v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
    v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + v (Sum.inr (Sum.inr 1)) ^ 2

@[expose] def coordV (x y u w : ZMod 2) : Ix → ZMod 2 :=
  Sum.elim (fun _ => x) (Sum.elim (fun _ => y) (fun j => if j = 0 then u else w))

@[expose] def sv : Fin 5 → (Ix → ZMod 2) :=
  ![coordV 1 0 0 0, coordV 0 1 0 0, coordV 1 1 1 0, coordV 1 1 0 1, coordV 1 1 1 1]

theorem qF_sv (j : Fin 5) : qF (sv j) = 0 := by
  revert j
  decide

theorem sv_ne_zero (j : Fin 5) : sv j ≠ 0 := by
  revert j
  decide

theorem sv_injective : Function.Injective sv := by
  decide

theorem sv_char (v : Ix → ZMod 2) (hv : v ≠ 0) (hq : qF v = 0) : ∃ j, sv j = v := by
  revert v
  decide

theorem sv_sum : ∑ j, sv j = 0 := by
  decide

@[expose] def Smat : Matrix Ix (Fin 5) (ZMod 2) := Matrix.of fun i j => sv j i

theorem smat_mulVec (y : Fin 5 → ZMod 2) : Smat *ᵥ y = ∑ j, y j • sv j := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Smat,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem smat_injective_on_permCore :
    ∀ x : Fin 5 → ZMod 2, (∑ i, x i = 0) → Smat *ᵥ x = 0 → x = 0 := by
  decide

theorem smat_permAct (σ : Equiv.Perm (Fin 5)) (M : Matrix Ix Ix (ZMod 2))
    (hM : ∀ j, M *ᵥ sv j = sv (σ j)) (x : Fin 5 → ZMod 2) :
    Smat *ᵥ (fun i => x (σ⁻¹ i)) = M *ᵥ (Smat *ᵥ x) := by
  have h1 : Smat *ᵥ (fun i => x (σ⁻¹ i)) = ∑ k, x k • sv (σ k) := by
    rw [smat_mulVec]
    calc ∑ j, (x (σ⁻¹ j)) • sv j = ∑ k, (x (σ⁻¹ (σ k))) • sv (σ k) :=
          (Equiv.sum_comp σ (fun j => x (σ⁻¹ j) • sv j)).symm
      _ = ∑ k, x k • sv (σ k) := by simp
  have h2 : M *ᵥ (Smat *ᵥ x) = ∑ k, x k • sv (σ k) := by
    simp only [smat_mulVec, Matrix.mulVec_sum, Matrix.mulVec_smul, hM]
  rw [h1, h2]

theorem span_sv : ∀ v : Ix → ZMod 2, ∃ c : Fin 5 → ZMod 2, v = ∑ j, c j • sv j := by
  decide

theorem permAct_mem_permCore (σ : Equiv.Perm (Fin 5)) (x : Fin 5 → ZMod 2)
    (hx : ∑ i, x i = 0) : ∑ i, (fun k => x (σ⁻¹ k)) i = 0 := by
  rw [← hx]
  exact Equiv.sum_comp σ⁻¹ x

@[expose] noncomputable def sIdx (v : Ix → ZMod 2) : Fin 5 :=
  if h : ∃ j, sv j = v then h.choose else 0

theorem sIdx_spec {v : Ix → ZMod 2} {j : Fin 5} (hj : sv j = v) : sv (sIdx v) = v := by
  have h : ∃ k, sv k = v := ⟨j, hj⟩
  unfold sIdx
  rw [dif_pos h]
  exact h.choose_spec

@[expose] noncomputable def permOf (M : Matrix Ix Ix (ZMod 2)) (j : Fin 5) : Fin 5 :=
  sIdx (M *ᵥ sv j)

theorem permOf_spec (M : Matrix Ix Ix (ZMod 2)) (hMQ : ∀ v, qF (M *ᵥ v) = qF v)
    (hMinj : ∀ v, M *ᵥ v = 0 → v = 0) (j : Fin 5) : M *ᵥ sv j = sv (permOf M j) := by
  have hne : M *ᵥ sv j ≠ 0 := fun h => sv_ne_zero j (hMinj _ h)
  have hq : qF (M *ᵥ sv j) = 0 := by rw [hMQ, qF_sv]
  obtain ⟨k, hk⟩ := sv_char _ hne hq
  unfold permOf
  rw [sIdx_spec hk]

theorem permOf_injective (M : Matrix Ix Ix (ZMod 2)) (hMQ : ∀ v, qF (M *ᵥ v) = qF v)
    (hMinj : ∀ v, M *ᵥ v = 0 → v = 0) : Function.Injective (permOf M) := by
  intro i j hij
  have h1 := permOf_spec M hMQ hMinj i
  have h2 := permOf_spec M hMQ hMinj j
  rw [hij] at h1
  have hd : M *ᵥ (sv i - sv j) = 0 := by
    rw [Matrix.mulVec_sub, h1, h2, sub_self]
  have h3 : sv i = sv j := sub_eq_zero.1 (hMinj _ hd)
  exact sv_injective h3

end F2Omega

end Canon

end G11

end CFSG.Quasithin
