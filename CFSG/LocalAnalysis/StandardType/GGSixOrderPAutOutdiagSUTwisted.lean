module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagSUPPD
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSUTorus

public section

namespace CFSG.StandardType

namespace OrdPOutSU

open Polynomial Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

section Transfer

variable {K L V : Type*} [Field K] [Field L] [Algebra K L] [Finite L] [AddCommGroup V]
  [Module K V] [Module L V] [IsScalarTower K L V] {fK fL : ℕ}
  {hK : UnitaryFieldData 2 fK K} {hL : UnitaryFieldData 2 fL L}

theorem trace_bar (hbar : ∀ a : K, hL.bar (algebraMap K L a) = algebraMap K L (hK.bar a))
    (x : L) : Algebra.trace K L (hL.bar x) = hK.bar (Algebra.trace K L x) := by
  apply (algebraMap K L).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow, ← hbar, FiniteField.algebraMap_trace_eq_sum_pow,
    map_sum]
  exact Finset.sum_congr rfl fun i _ => (map_pow hL.bar x _).symm

theorem exists_transfer (hbar : ∀ a : K, hL.bar (algebraMap K L a) = algebraMap K L (hK.bar a))
    (B : V →ₛₗ[hK.bar] V →ₗ[K] K) (hB : B.IsSymm) (hBs : B.SeparatingLeft)
    (hadj : ∀ (l : L) (v w : V), B (l • v) w = B v (hL.bar l • w)) :
    ∃ H : V →ₛₗ[hL.bar] V →ₗ[L] L, H.IsSymm ∧ H.SeparatingLeft ∧
      ∀ v w, Algebra.trace K L (H v w) = B v w := by
  classical
  have : Finite K := Finite.of_injective _ (algebraMap K L).injective
  have hnd := traceForm_nondegenerate K L
  set T := (Algebra.traceForm K L).toDual hnd with hT
  let ℓ : V → V → Module.Dual K L := fun v w =>
    { toFun := fun c => B v (c • w)
      map_add' := fun c c' => by rw [add_smul, map_add]
      map_smul' := fun a c => by
        simp only [smul_assoc, LinearMap.map_smul, smul_eq_mul, RingHom.id_apply] }
  have hℓ : ∀ v w c, ℓ v w c = B v (c • w) := fun _ _ _ => rfl
  set H₀ : V → V → L := fun v w => T.symm (ℓ v w) with hH₀def
  have hH₀ : ∀ v w c, Algebra.trace K L (H₀ v w * c) = B v (c • w) := by
    intro v w c
    have h1 : T (T.symm (ℓ v w)) c = ℓ v w c := by rw [T.apply_symm_apply]
    rw [hT, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
    rw [← hℓ, ← h1]
  have hext : ∀ x y : L, (∀ c, Algebra.trace K L (x * c) = Algebra.trace K L (y * c)) →
      x = y := by
    intro x y hxy
    have h0 := hnd.1 (x - y) fun c => by
      rw [Algebra.traceForm_apply, sub_mul, map_sub, hxy c, sub_self]
    exact sub_eq_zero.mp h0
  refine ⟨LinearMap.mk₂'ₛₗ hL.bar (RingHom.id L) H₀ ?_ ?_ ?_ ?_, ⟨fun x y => ?_⟩,
    fun x hx => ?_, fun v w => ?_⟩
  · intro v v' w
    refine hext _ _ fun c => ?_
    rw [hH₀, add_mul, map_add (Algebra.trace K L), hH₀, hH₀, map_add B, LinearMap.add_apply]
  · intro l v w
    refine hext _ _ fun c => ?_
    have e : hL.bar l • H₀ v w * c = H₀ v w * (hL.bar l * c) := by
      rw [smul_eq_mul]
      ring
    rw [hH₀, hadj, e, hH₀, smul_smul]
  · intro v w w'
    refine hext _ _ fun c => ?_
    rw [hH₀, add_mul, map_add (Algebra.trace K L), hH₀, hH₀, smul_add, map_add (B v)]
  · intro l v w
    refine hext _ _ fun c => ?_
    have e : (RingHom.id L) l • H₀ v w * c = H₀ v w * (c * l) := by
      rw [RingHom.id_apply, smul_eq_mul]
      ring
    rw [hH₀, e, hH₀, smul_smul]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    refine hext _ _ fun c => ?_
    have e1 : hL.bar (H₀ x y) * c = hL.bar (H₀ x y * hL.bar c) := by
      rw [map_mul, UnitaryFieldData.bar_bar]
    rw [e1, trace_bar hbar, hH₀, hH₀, ← hB.eq (c • x) y, hadj]
  · have h1 : ∀ y, B x y = 0 := fun y => by
      have h2 := hH₀ x y 1
      rw [mul_one, one_smul] at h2
      rw [← h2]
      have h3 := hx y
      simp only [LinearMap.mk₂'ₛₗ_apply] at h3
      rw [h3, map_zero]
    exact hBs x h1
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    have h2 := hH₀ v w 1
    rwa [mul_one, one_smul] at h2

end Transfer

section Twisted

variable {f : ℕ} {K : Type} [Field K]

theorem pow_two_pow_mul_odd (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : Odd p) (a : K) :
    a ^ 2 ^ (f * p) = h.bar a := by
  have : Finite K := h.finite
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨k, hk⟩ := hp
  have hcard : Fintype.card K = 2 ^ (2 * f) := by rw [← Nat.card_eq_fintype_card, h.card]
  have e : 2 ^ (f * p) = 2 ^ f * (Fintype.card K) ^ k := by
    rw [hcard, hk, ← pow_mul, ← pow_add]
    ring_nf
  rw [e, pow_mul, FiniteField.pow_card_pow, UnitaryFieldData.bar_apply]

theorem exists_su_comm_of_twisted (h : UnitaryFieldData 2 f K) {n p r : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {A : GL (Fin n) K}
    (hAU : A ∈ primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hc : A ^ p = GeneralLinearGroup.scalar (Fin n) c) (hcμ : ∀ μ : Kˣ, μ ^ p ≠ c)
    (hr : r.Prime) (hrd : ∀ m, p * m = n → (r : ℤ) ∣ ((2 ^ (f * p) : ℕ) : ℤ) ^ m - (-1) ^ m)
    (hrq : ¬ r ∣ 2 ^ f + 1) :
    ∃ g : GL (Fin n) K, g ∈ unitarySU 2 f K n ∧ orderOf g = r ∧ g * A = A * g := by
  classical
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero n := ⟨by omega⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hcN : (c : K) ^ (2 ^ f + 1) = 1 := by
    have hcU : GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n) := by
      rw [← hc]
      exact (primeFormUnitary h (idGram K n)).pow_mem hAU p
    have h1 := (SUTorus.scalar_mem_primeFormUnitary_iff h c).mp hcU
    rw [UnitaryFieldData.bar_apply] at h1
    rw [pow_succ]
    exact h1
  set P : K[X] := X ^ p - C (c : K) with hP
  have hPirr : Irreducible P := X_pow_sub_C_irreducible_of_prime hp fun b hb => by
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hb
      exact c.ne_zero hb.symm
    exact hcμ (Units.mk0 b hb0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hb]))
  have : Fact (Irreducible P) := ⟨hPirr⟩
  have hP0 : P ≠ 0 := hPirr.ne_zero
  set xA : Module.End K (Fin n → K) := Matrix.toLinAlgEquiv' (A : Matrix (Fin n) (Fin n) K)
    with hxA
  have haeval : aeval xA P = 0 := by
    have h1 : xA ^ p = algebraMap K (Module.End K (Fin n → K)) (c : K) := by
      rw [hxA, ← map_pow, ← Units.val_pow_eq_pow_val, hc, GeneralLinearGroup.coe_scalar,
        ← AlgEquiv.commutes Matrix.toLinAlgEquiv' (c : K)]
      rfl
    rw [hP, map_sub, aeval_X_pow, aeval_C, h1, sub_self]
  set φ : AdjoinRoot P →ₐ[K] Module.End K (Fin n → K) :=
    Ideal.Quotient.liftₐ (Ideal.span {P}) (aeval xA) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, haeval, mul_zero]) with hφ
  have hφroot : φ (AdjoinRoot.root P) = xA := by
    rw [← AdjoinRoot.mk_X]
    exact aeval_X xA
  let : Module (AdjoinRoot P) (Fin n → K) := Module.compHom (Fin n → K) φ.toRingHom
  have hsmul : ∀ (l : AdjoinRoot P) (v : Fin n → K), l • v = φ l v := fun _ _ => rfl
  have : IsScalarTower K (AdjoinRoot P) (Fin n → K) := ⟨fun a l v => by
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have : Module.Finite K (AdjoinRoot P) := (AdjoinRoot.powerBasis hP0).finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  have : Module.Finite (AdjoinRoot P) (Fin n → K) :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot P) (Fin n → K)
  have hdimL : Module.finrank K (AdjoinRoot P) = p := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hP0), AdjoinRoot.powerBasis_dim hP0,
      natDegree_X_pow_sub_C]
  set m := Module.finrank (AdjoinRoot P) (Fin n → K) with hm
  have hdim : p * m = n := by
    rw [hm, ← hdimL, Module.finrank_mul_finrank K (AdjoinRoot P) (Fin n → K),
      Module.finrank_fin_fun]
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hdim
      omega
    · exact h0
  have hcardL : Nat.card (AdjoinRoot P) = 2 ^ (2 * (f * p)) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdimL, h.card, ← pow_mul]
    ring_nf
  have hL : UnitaryFieldData 2 (f * p) (AdjoinRoot P) :=
    ⟨Nat.prime_two, Nat.mul_pos h.one_le hp.pos, hcardL⟩
  have hbarK : ∀ a : K, hL.bar (algebraMap K (AdjoinRoot P) a) =
      algebraMap K (AdjoinRoot P) (h.bar a) := by
    intro a
    rw [UnitaryFieldData.bar_apply, ← map_pow, pow_two_pow_mul_odd h hodd]
  have hrootp : AdjoinRoot.root P ^ p = algebraMap K (AdjoinRoot P) (c : K) := by
    have h0 := AdjoinRoot.eval₂_root P
    rw [hP, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
    rw [h0, AdjoinRoot.algebraMap_eq]
  have hbarRoot : hL.bar (AdjoinRoot.root P) * AdjoinRoot.root P = 1 := by
    obtain ⟨t, ht⟩ := mul_dvd_pow_add_one hp hp2 hpq
    rw [UnitaryFieldData.bar_apply, ← pow_succ,
      show 2 ^ (f * p) + 1 = (2 ^ f) ^ p + 1 by rw [pow_mul], ht, pow_mul, pow_mul, hrootp,
      ← map_pow, hcN, map_one, one_pow]
  have hAiso := (gramForm_isometry_iff h 1 (A : Matrix (Fin n) (Fin n) K)).mpr (by
    have h1 := mem_primeFormUnitary.mp hAU
    rwa [idGram, Units.val_one] at h1)
  have hroot_smul : ∀ v : Fin n → K,
      AdjoinRoot.root P • v = (A : Matrix (Fin n) (Fin n) K) *ᵥ v := by
    intro v
    rw [hsmul, hφroot, hxA, Matrix.toLinAlgEquiv'_apply]
  have hadj : ∀ (l : AdjoinRoot P) (v w : Fin n → K),
      gramForm h 1 (l • v) w = gramForm h 1 v (hL.bar l • w) := by
    let S : Subalgebra K (AdjoinRoot P) :=
      { carrier := {l | ∀ v w : Fin n → K, gramForm h (1 : Matrix (Fin n) (Fin n) K) (l • v) w =
          gramForm h (1 : Matrix (Fin n) (Fin n) K) v (hL.bar l • w)}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          intro v w
          rw [mul_smul, ha (b • v) w, hb v (hL.bar a • w), ← mul_smul, map_mul,
            mul_comm (hL.bar b)]
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          intro v w
          rw [add_smul, map_add (gramForm h 1), LinearMap.add_apply, ha v w, hb v w,
            map_add hL.bar, add_smul, map_add (gramForm h 1 v)]
        algebraMap_mem' := by
          intro a
          simp only [Set.mem_ofPred_eq]
          intro v w
          rw [algebraMap_smul, hbarK, algebraMap_smul, LinearMap.map_smulₛₗ₂,
            LinearMap.map_smul] }
    have hroot : AdjoinRoot.root P ∈ S := by
      change ∀ v w, gramForm h 1 (AdjoinRoot.root P • v) w =
        gramForm h 1 v (hL.bar (AdjoinRoot.root P) • w)
      intro v w
      set u := hL.bar (AdjoinRoot.root P) • w with hu
      have hAu : (A : Matrix (Fin n) (Fin n) K) *ᵥ u = w := by
        rw [← hroot_smul, hu, smul_smul, mul_comm, hbarRoot, one_smul]
      rw [hroot_smul, ← hAu, hAiso]
    have htop : S = ⊤ := by
      rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hroot)
    intro l v w
    have hl : l ∈ S := htop ▸ Algebra.mem_top
    exact hl v w
  obtain ⟨H, hHs, hHsep, hHtr⟩ := exists_transfer (hK := h) (hL := hL) hbarK
    (gramForm h (1 : Matrix (Fin n) (Fin n) K)) (gramForm_isSymm h (by simp))
    (gramForm_separatingLeft h (by simp)) hadj
  have hcardU := (CFSG.LinearGroups.unitary_full_group_order hL hHs hHsep hm.symm hm1).1
  have hrU : r ∣ Nat.card (sesqUnitaryGroup H) := by
    have h1 : (r : ℤ) ∣ ∏ i ∈ Finset.Icc 1 m, (((2 ^ (f * p) : ℕ) : ℤ) ^ i - (-1) ^ i) :=
      (hrd m hdim).trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hm1, le_rfl⟩))
    have h2 : (r : ℤ) ∣ (Nat.card (sesqUnitaryGroup H) : ℤ) := by
      rw [hcardU]
      exact dvd_mul_of_dvd_right h1 _
    exact Int.natCast_dvd_natCast.mp h2
  have : Finite ((Fin n → K) →ₗ[AdjoinRoot P] (Fin n → K)) :=
    Finite.of_injective (fun g : (Fin n → K) →ₗ[AdjoinRoot P] (Fin n → K) =>
      (g : (Fin n → K) → (Fin n → K))) DFunLike.coe_injective
  have : Finite (LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → K)) :=
    Finite.of_injective (fun u : LinearMap.GeneralLinearGroup (AdjoinRoot P) (Fin n → K) =>
      (u : (Fin n → K) →ₗ[AdjoinRoot P] (Fin n → K))) fun _ _ e => Units.ext e
  obtain ⟨⟨g₁, hg₁U⟩, hg₀⟩ := exists_prime_orderOf_dvd_card' r hrU
  have hg₁o : orderOf g₁ = r := by
    rw [← hg₀]
    exact Subgroup.orderOf_coe (⟨g₁, hg₁U⟩ : sesqUnitaryGroup H)
  let R : Module.End (AdjoinRoot P) (Fin n → K) →* Module.End K (Fin n → K) :=
    { toFun := fun g => g.restrictScalars K, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hR : Function.Injective R := LinearMap.restrictScalars_injective K
  let e₃ : (Module.End K (Fin n → K))ˣ ≃* GL (Fin n) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv' :
      Module.End K (Fin n → K) ≃ₐ[K] Matrix (Fin n) (Fin n) K).toMulEquiv
  set g₃ : GL (Fin n) K := e₃ (Units.map R g₁) with hg₃def
  have hg₃ : orderOf g₃ = r := by
    rw [hg₃def, MulEquiv.orderOf_eq, orderOf_injective _ (Units.map_injective hR), hg₁o]
  have hg₃v : ∀ v, (g₃ : Matrix (Fin n) (Fin n) K) *ᵥ v =
      (g₁ : Module.End (AdjoinRoot P) (Fin n → K)) v := by
    intro v
    have e : (g₃ : Matrix (Fin n) (Fin n) K) =
        LinearMap.toMatrix' (R (g₁ : Module.End (AdjoinRoot P) (Fin n → K))) := rfl
    rw [e, LinearMap.toMatrix'_mulVec]
    rfl
  have hg₃iso : ∀ x y, gramForm h (1 : Matrix (Fin n) (Fin n) K)
      ((g₃ : Matrix (Fin n) (Fin n) K) *ᵥ x) ((g₃ : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      gramForm h (1 : Matrix (Fin n) (Fin n) K) x y := by
    intro x y
    rw [hg₃v, hg₃v, ← hHtr, ← hHtr, mem_sesqUnitaryGroup.mp hg₁U]
  have hcomm : g₃ * A = A * g₃ := by
    apply Units.ext
    have hA' : (A : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrixAlgEquiv' xA := by
      rw [hxA, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
    rw [Units.val_mul, Units.val_mul, hA']
    change LinearMap.toMatrixAlgEquiv' (R (g₁ : Module.End (AdjoinRoot P) (Fin n → K))) * _ =
      _ * LinearMap.toMatrixAlgEquiv' (R (g₁ : Module.End (AdjoinRoot P) (Fin n → K)))
    rw [← map_mul, ← map_mul]
    congr 1
    refine LinearMap.ext fun v => ?_
    change (g₁ : Module.End (AdjoinRoot P) (Fin n → K)) (xA v) =
      xA ((g₁ : Module.End (AdjoinRoot P) (Fin n → K)) v)
    have hx : ∀ w : Fin n → K, xA w = AdjoinRoot.root P • w := fun w => by
      rw [hsmul, hφroot]
    rw [hx, hx, LinearMap.map_smul]
  have hg₃U : g₃ ∈ primeFormUnitary h (idGram K n) := by
    rw [mem_primeFormUnitary, idGram, Units.val_one]
    exact (gramForm_isometry_iff h 1 _).mp hg₃iso
  have hdet : GeneralLinearGroup.det g₃ = 1 := by
    have h1 : (GeneralLinearGroup.det g₃) ^ r = 1 := by
      rw [← map_pow, ← hg₃, pow_orderOf_eq_one, map_one]
    have h2 : GeneralLinearGroup.det g₃ ^ (2 ^ f + 1) = 1 := UnitModel.det_pow_eq_one_of_mem h hg₃U
    rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one h1) with h5 | h5
    · exact orderOf_eq_one_iff.mp h5
    · exact absurd (h5 ▸ orderOf_dvd_of_pow_eq_one h2) hrq
  refine ⟨g₃, (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩, hg₃, hcomm⟩
  · have := congrArg (fun u : Kˣ => (u : K)) hdet
    simpa only [GeneralLinearGroup.val_det_apply, Units.val_one] using this
  · have h1 := mem_primeFormUnitary.mp hg₃U
    rwa [idGram, Units.val_one, Matrix.mul_one] at h1

end Twisted

end OrdPOutSU

end CFSG.StandardType
