module

public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.Ch4.J4NSD

open CFSG.Quasithin.KGC31
open scoped Matrix

variable {Γ : Type*} [Group Γ] {n : ℕ}

theorem mulVec_single_one' (M : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) :
    M *ᵥ Pi.single i 1 = fun r => M r i := by
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem eBasis_of_map {Γ' : Type*} [Group Γ'] {v : Fin n → Γ} {f : Γ →* Γ'}
    (hf : Function.Injective f) (h : EBasis fun i => f (v i)) : EBasis v where
  sq i := hf (by rw [map_mul, h.sq i, map_one])
  comm i j := hf (by rw [map_mul, map_mul]; exact h.comm i j)
  ne_one c hc := h.ne_one c (by rw [← map_eElt, hc, map_one])

theorem exists_eMat_map {Γ' : Type*} [Group Γ'] [Finite Γ'] {v : Fin n → Γ} (hv : EBasis v)
    {f : Γ →* Γ'} (hf : Function.Injective f) (g : Γ) (hg : g ∈ eNorm hv) :
    ∃ hg' : f g ∈ eNorm (hv.map hf), eMat (hv.map hf) ⟨f g, hg'⟩ = eMat hv ⟨g, hg⟩ := by
  have hM : ∀ i, f g * f (v i) * (f g)⁻¹ =
      eElt (fun j => f (v j)) fun r => eMat hv ⟨g, hg⟩ r i := by
    intro i
    rw [← map_eElt, ← mulVec_single_one', ← conj_eq_eElt_mulVec hv ⟨g, hg⟩, eElt_single]
    simp only [map_mul, map_inv]
  exact ⟨mem_eNorm (hv.map hf) _ hM, eMat_eq (hv.map hf) _ _ hM⟩

theorem exists_eMat_comap [Finite Γ] {Γ' : Type*} [Group Γ'] {v : Fin n → Γ} (hv : EBasis v)
    {f : Γ →* Γ'} (hf : Function.Injective f) (g : Γ) (hg : f g ∈ eNorm (hv.map hf)) :
    ∃ hg' : g ∈ eNorm hv, eMat hv ⟨g, hg'⟩ = eMat (hv.map hf) ⟨f g, hg⟩ := by
  have hM : ∀ i, g * v i * g⁻¹ = eElt v fun r => eMat (hv.map hf) ⟨f g, hg⟩ r i := by
    intro i
    apply hf
    rw [map_eElt, ← mulVec_single_one', ← conj_eq_eElt_mulVec (hv.map hf) ⟨f g, hg⟩,
      eElt_single]
    simp only [map_mul, map_inv]
  exact ⟨mem_eNorm hv _ hM, eMat_eq hv _ _ hM⟩

theorem exists_basis_change {v w : Fin n → Γ} (hv : EBasis v) (hw : EBasis w)
    (hvw : eSub hv = eSub hw) :
    ∃ P Q : Matrix (Fin n) (Fin n) (ZMod 2), P * Q = 1 ∧ Q * P = 1 ∧
      ∀ (g : Γ) (hg : g ∈ eNorm hv) (hg' : g ∈ eNorm hw),
        eMat hw ⟨g, hg'⟩ = Q * eMat hv ⟨g, hg⟩ * P := by
  have hwv : ∀ j, ∃ c, eElt v c = w j := fun j =>
    (mem_eSub_iff hv _).mp (hvw ▸ mem_eSub hw j)
  have hvw' : ∀ j, ∃ d, eElt w d = v j := fun j =>
    (mem_eSub_iff hw _).mp (hvw ▸ mem_eSub hv j)
  choose c hc using hwv
  choose d hd using hvw'
  set P : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of fun r j => c j r with hP
  set Q : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of fun r j => d j r with hQ
  have hPw : ∀ x, eElt v (P *ᵥ x) = eElt w x := by
    intro x
    rw [← eElt_mulVec hv P x]
    congr 1
    funext j
    exact hc j
  have hQv : ∀ x, eElt w (Q *ᵥ x) = eElt v x := by
    intro x
    rw [← eElt_mulVec hw Q x]
    congr 1
    funext j
    exact hd j
  have hPQ : P * Q = 1 := matrix_ext_mulVec fun x => eElt_injective hv (by
    rw [← Matrix.mulVec_mulVec, hPw, hQv, Matrix.one_mulVec])
  have hQP : Q * P = 1 := matrix_ext_mulVec fun x => eElt_injective hw (by
    rw [← Matrix.mulVec_mulVec, hQv, hPw, Matrix.one_mulVec])
  refine ⟨P, Q, hPQ, hQP, fun g hg hg' => ?_⟩
  apply eMat_eq hw ⟨g, hg'⟩
  intro i
  rw [← mulVec_single_one', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQv,
    ← conj_eq_eElt_mulVec hv ⟨g, hg⟩, hPw, eElt_single]

theorem trace_eq_of_conj {X Y W : GL (Fin n) (ZMod 2)} (h : X = W * Y * W⁻¹) :
    Matrix.trace (X : Matrix (Fin n) (Fin n) (ZMod 2)) =
      Matrix.trace (Y : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  rw [h, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]

theorem conj_zpow_of_conj_inv {M : Type*} [Group M] {X W : M} (hX : X = W * X⁻¹ * W⁻¹) (h : M)
    (j : ℤ) : h * X ^ j * h⁻¹ =
      (h * W * h⁻¹) * (h * X⁻¹ ^ j * h⁻¹) * (h * W * h⁻¹)⁻¹ := by
  have hj : X ^ j = W * X⁻¹ ^ j * W⁻¹ := by
    conv_lhs => rw [hX]
    rw [conj_zpow]
  rw [hj]
  group

theorem exists_conj_zpow_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : ¬ p ^ 2 ∣ Nat.card G) {g s : G} (hg : orderOf g = p) (hs : orderOf s = p) :
    ∃ (h : G) (j : ℤ), h * g ^ j * h⁻¹ = s := by
  have hcard : ∀ x : G, orderOf x = p → ∀ P : Sylow p G, Subgroup.zpowers x ≤ P →
      (P : Subgroup G) = Subgroup.zpowers x := by
    intro x hx P hP
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hdvd : p ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G)
    have hk1 : k ≤ 1 := by
      by_contra hk1
      exact hp2 ((pow_dvd_pow p (by omega)).trans hdvd)
    refine (Subgroup.eq_of_le_of_card_ge hP ?_).symm
    rw [hk, Nat.card_zpowers, hx]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk1
      _ = p := pow_one p
  have hgp : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hsp : IsPGroup p (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨P, hP⟩ := hgp.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hsp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P Q
  have hs' : s ∈ ((h • P : Sylow p G) : Subgroup G) := by
    rw [hh, hcard s hs Q hQ]
    exact Subgroup.mem_zpowers s
  rw [Sylow.coe_subgroup_smul, hcard g hg P hP, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    at hs'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hs'
  refine ⟨h, j, ?_⟩
  rw [hj, MulAut.smul_def, MulAut.conj_inv_apply]
  group

end CFSG.Quasithin.H13.Ch4.J4NSD
