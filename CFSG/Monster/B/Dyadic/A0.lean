module

public import CFSG.Monster.B.Dyadic.Nodes
public import Certificates.Certificate3107

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Dyadic

open Module CFSG.Monster.B.Binary.Native
open scoped Matrix

section Generic

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℚ V]
  (R : Basis (Fin 4371) ℚ V) (ρ : G →* (V ≃ₗ[ℚ] V))

variable {R} in
theorem acts_mul {φ ψ : V →ₗ[ℚ] V} {A B : Matrix (Fin 4371) (Fin 4371) ℚ}
    (hφ : ∀ t, φ (R t) = ∑ u, A t u • R u) (hψ : ∀ t, ψ (R t) = ∑ u, B t u • R u) (t : Fin 4371) :
    φ (ψ (R t)) = ∑ u, (B * A) t u • R u := by
  rw [hψ t, map_sum]
  simp_rw [map_smul, hφ, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

variable {R} in
theorem ell_image_int {N : V →ₗ[ℚ] V} {num : ℕ → ℕ → ℤ}
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((num t u : ℚ) / 8) • R u) {i : Fin 4371}
    {c : Fin 4371 → ℤ}
    (hc : ∀ u : Fin 4371, ∑ t : Fin 4371, Bz i t * num t u = 8 * ∑ t : Fin 4371, c t * Bz t u) :
    N (ell R i) = ∑ t, (c t : ℚ) • ell R t := by
  have hX : ∀ u : Fin 4371, ∑ s : Fin 4371, Bq i s * ((num s u : ℚ) / 8) =
      ∑ t : Fin 4371, (c t : ℚ) * Bq t u := by
    intro u
    have h1 := congrArg (fun z : ℤ => (z : ℚ)) (hc u)
    push_cast at h1
    simp only [Bq, Bmat_apply]
    calc ∑ s : Fin 4371, (Bz i s : ℚ) / 128 * ((num s u : ℚ) / 8) =
        (∑ s : Fin 4371, (Bz i s : ℚ) * (num s u : ℚ)) / 1024 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ = (∑ t : Fin 4371, (c t : ℚ) * (Bz t u : ℚ)) / 128 := by
          rw [h1]
          ring
      _ = ∑ t : Fin 4371, (c t : ℚ) * ((Bz t u : ℚ) / 128) := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun t _ => by ring
  have hL : N (ell R i) =
      ∑ u : Fin 4371, (∑ s : Fin 4371, Bq i s * ((num s u : ℚ) / 8)) • R u := by
    rw [ell_eq, map_sum]
    simp_rw [map_smul, hN, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  have hR : ∑ t, (c t : ℚ) • ell R t = ∑ u : Fin 4371, (∑ t, (c t : ℚ) * Bq t u) • R u := by
    simp_rw [ell_eq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun u _ => by rw [hX u]

variable {R} in
theorem modTwo_ell_int
    {N : V →ₗ[ℚ] V} {num : ℕ → ℕ → ℤ}
    (hN : ∀ t, N (R t) = ∑ u : Fin 4371, ((num t u : ℚ) / 8) • R u)
    (hm : ∀ x ∈ Lam R, N x ∈ Lam R) {i : Fin 4371} {c : Fin 4371 → ℤ}
    (hc : ∀ u : Fin 4371, ∑ t : Fin 4371, Bz i t * num t u = 8 * ∑ t : Fin 4371, c t * Bz t u) :
    modTwoMap (lamEnd R N hm) (ModN.basis (ellZBasis R) i) =
      ∑ l, (c l : ZMod 2) • ModN.basis (ellZBasis R) l := by
  rw [ModN.basis_apply_eq_mkQ, modTwoMap_mkQ]
  have h' : lamEnd R N hm (ellZBasis R i) = ∑ l, c l • ellZBasis R l := by
    apply Subtype.ext
    rw [Submodule.coe_sum, coe_lamEnd, coe_ellZBasis, ell_image_int hN hc]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Submodule.coe_smul, coe_ellZBasis, Int.cast_smul_eq_zsmul]
  rw [h', map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mkQ_zsmul, ModN.basis_apply_eq_mkQ]

variable (hΛ : ∀ s, ∀ x ∈ Lam R, ρ s x ∈ Lam R)

theorem beta_of_rows
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) {s : G}
    {X : Fin 4370 → Fin 4371 → ZMod 2}
    (h : ∀ j, modRep R ρ hΛ s (bb R (pIdx.succAbove j)) = ∑ l, X j l • bb R l) :
    ((beta R ρ hΛ hf s : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      (Matrix.of fun j t => Pmap (X j) t).transpose := by
  ext i j
  rw [coe_beta, Matrix.transpose_apply, Matrix.of_apply]
  change LinearMap.toMatrix' (betaLin R ρ hΛ hf s) i j = _
  rw [LinearMap.toMatrix'_apply, betaLin, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [coordQ_symm_single]
  change coordQ R (quotEnd R ρ hΛ hf s (Submodule.Quotient.mk (bb R (pIdx.succAbove j)))) i = _
  rw [quotEnd_mk, coordQ_mk, Phi_apply, h, equivFun_sum]

end Generic

attribute [local instance] instAddCommGroupVst

@[expose] noncomputable def a0Elt : Cbar :=
  packetElt ⟨17, by norm_num⟩ * packetElt ⟨10, by norm_num⟩ * packetElt ⟨5, by norm_num⟩ *
    packetElt ⟨4, by norm_num⟩ * packetElt ⟨2, by norm_num⟩ * packetElt ⟨1, by norm_num⟩ *
    packetElt ⟨28, by norm_num⟩

theorem chi_packetElt_mq
    {k : ℕ} (hk : k < 48) (t : Fin 4371) :
    (chi (packetElt ⟨k, hk⟩) : Vst →ₗ[ℚ] Vst) (Rbasis t) =
      ∑ u, MqN (numerAt k) t u • Rbasis u := by
  rw [chi_packetElt_apply]
  exact Finset.sum_congr rfl fun u _ => by
    rw [packetQ_numerAt]
    rfl

theorem chi_a0Elt_apply
    (t : Fin 4371) :
    (chi a0Elt : Vst →ₗ[ℚ] Vst) (Rbasis t) =
      ∑ u : Fin 4371, ((numer26 t u : ℚ) / 8) • Rbasis u := by
  have hm : ∀ (a b : Cbar) (A B : Matrix (Fin 4371) (Fin 4371) ℚ),
      (∀ t, (chi a : Vst →ₗ[ℚ] Vst) (Rbasis t) = ∑ u, A t u • Rbasis u) →
      (∀ t, (chi b : Vst →ₗ[ℚ] Vst) (Rbasis t) = ∑ u, B t u • Rbasis u) →
      ∀ t, (chi (a * b) : Vst →ₗ[ℚ] Vst) (Rbasis t) = ∑ u, (B * A) t u • Rbasis u := by
    intro a b A B ha hb t
    rw [map_mul, LinearEquiv.coe_coe, LinearEquiv.mul_apply]
    exact acts_mul ha hb t
  have h := hm _ _ _ _ (hm _ _ _ _ (hm _ _ _ _ (hm _ _ _ _ (hm _ _ _ _ (hm _ _ _ _
    (chi_packetElt_mq (k := 17) (by norm_num)) (chi_packetElt_mq (k := 10) (by norm_num)))
    (chi_packetElt_mq (k := 5) (by norm_num))) (chi_packetElt_mq (k := 4) (by norm_num)))
    (chi_packetElt_mq (k := 2) (by norm_num))) (chi_packetElt_mq (k := 1) (by norm_num)))
    (chi_packetElt_mq (k := 28) (by norm_num)) t
  rw [a0Elt, h]
  simp only [← Matrix.mul_assoc]
  rw [Certificates.certificate3107.1]
  rfl

theorem betaS_a0 :
    ((betaS a0Elt : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      (Matrix.of F0row).transpose := by
  choose c hc hpar using Certificates.certificate3107.2
  rw [betaS, beta_of_rows Rbasis chi lamS_stable fbarS_fixed (X := fun j l => (c j l : ZMod 2))
    fun j => modTwo_ell_int chi_a0Elt_apply (lamS_stable a0Elt) (hc j)]
  congr 1
  ext j t
  rw [Matrix.of_apply, Matrix.of_apply, Pmap_apply]
  exact hpar j t

end CFSG.Monster.B.Dyadic

end
