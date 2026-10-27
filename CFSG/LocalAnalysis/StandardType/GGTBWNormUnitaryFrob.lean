module

public import CFSG.LinearAlgebra.FrobeniusIsometryUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBWNormFormFrob
public import CFSG.LocalAnalysis.StandardType.GGL45TGSU
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGK1ScUni
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial Matrix

namespace UnitaryFrob

variable {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K) (d : ℕ)

@[expose] noncomputable def hermForm : (Fin d → K) →ₛₗ[h.bar] (Fin d → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id K) (fun v w => (h.bar ∘ v) ⬝ᵥ w)
    (fun v v' w => by
      rw [show h.bar ∘ (v + v') = h.bar ∘ v + h.bar ∘ v' from funext fun i => by simp,
        add_dotProduct])
    (fun c v w => by
      rw [show h.bar ∘ (c • v) = h.bar c • (h.bar ∘ v) from funext fun i => by simp,
        smul_dotProduct, smul_eq_mul])
    (fun v w w' => by rw [dotProduct_add])
    (fun c v w => by rw [dotProduct_smul, RingHom.id_apply])

variable {h d}

theorem hermForm_apply (v w : Fin d → K) : hermForm h d v w = (h.bar ∘ v) ⬝ᵥ w := rfl

theorem hermForm_mulVec {A : Matrix (Fin d) (Fin d) K} (hA : (A.map h.bar)ᵀ * A = 1)
    (v w : Fin d → K) : hermForm h d (A *ᵥ v) (A *ᵥ w) = hermForm h d v w := by
  rw [hermForm_apply, hermForm_apply]
  have h1 : h.bar ∘ (A *ᵥ v) = A.map h.bar *ᵥ (h.bar ∘ v) := funext fun i =>
    RingHom.map_mulVec h.bar A v i
  rw [h1, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, hA, one_mulVec]

theorem map_transpose_mul_toMatrix'_eq_one (T : (Fin d → K) →ₗ[K] (Fin d → K))
    (hT : ∀ v w, hermForm h d (T v) (T w) = hermForm h d v w) :
    ((LinearMap.toMatrix' T).map h.bar)ᵀ * LinearMap.toMatrix' T = 1 := by
  classical
  ext j k
  have hc : ∀ i, T (Pi.single i 1) = fun r => LinearMap.toMatrix' T r i := fun i => by
    funext r
    rw [LinearMap.toMatrix'_apply]
  have h1 := hT (Pi.single j 1) (Pi.single k 1)
  rw [hc, hc, hermForm_apply, hermForm_apply] at h1
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  rw [show (∑ x, h.bar (LinearMap.toMatrix' T x j) * LinearMap.toMatrix' T x k) =
    (h.bar ∘ fun r => LinearMap.toMatrix' T r j) ⬝ᵥ (fun r => LinearMap.toMatrix' T r k) from rfl,
    h1]
  simp only [dotProduct, Function.comp_apply, Pi.single_apply, apply_ite h.bar, map_one, map_zero,
    ite_mul, one_mul, zero_mul]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, eq_comm]

variable (h) in
theorem hermForm_herm (v w : Fin d → K) : hermForm h d w v = h.bar (hermForm h d v w) := by
  rw [hermForm_apply, hermForm_apply]
  simp only [dotProduct, Function.comp_apply, map_sum, map_mul, h.bar_bar]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

variable (h) in
theorem hermForm_nondeg (v : Fin d → K) (hv : ∀ w, hermForm h d v w = 0) : v = 0 := by
  classical
  funext i
  have h1 := hv (Pi.single i 1)
  rw [hermForm_apply, dotProduct_single, mul_one, Function.comp_apply] at h1
  rw [Pi.zero_apply, ← h.bar_bar (v i), h1, map_zero]

variable (h) in
include h in
theorem exists_conj_eq_pow_card_su [Finite K] (P : Subgroup (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hodd : Odd (Nat.card P)) :
    ∃ g : LargeEvenSUGroup (Fin d) K (2 ^ n), ∀ s ∈ P, g * s * g⁻¹ = s ^ Nat.card K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  let Φ : GL (Fin d) K ≃* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K))
  have hΦ : ∀ (A : GL (Fin d) K) (v : Fin d → K), Φ A v = (A : Matrix (Fin d) (Fin d) K) *ᵥ v :=
    fun _ _ => rfl
  let ψ : LargeEvenSUGroup (Fin d) K (2 ^ n) →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    Φ.toMonoidHom.comp (LargeEvenSUGroup (Fin d) K (2 ^ n)).subtype
  have hψinj : Function.Injective ψ := Φ.injective.comp Subtype.val_injective
  have : Finite P := Subtype.finite
  have : Finite (P.map ψ) := inferInstanceAs (Finite ↥(ψ '' (P : Set _)))
  have hcomm' : ∀ x ∈ P.map ψ, ∀ y ∈ P.map ψ, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hodd' : Odd (Nat.card (P.map ψ)) := by
    rwa [Subgroup.card_map_of_injective hψinj]
  have hiso' : ∀ y ∈ P.map ψ, ∀ v w, hermForm h d (y v) (y w) = hermForm h d v w := by
    rintro _ ⟨s, -, rfl⟩ v w
    exact hermForm_mulVec ((GGL45TG.SU.mem_su_iff h).mp s.2).1 v w
  obtain ⟨T, hT, hTconj, hTdet⟩ := CFSG.LinearAlgebra.exists_hermitian_isometry_conj_eq_pow_card h
    (hermForm h d) (hermForm_herm h) (hermForm_nondeg h) hcomm' hodd' hiso'
  let G : GL (Fin d) K := Φ.symm T
  have hGT : Φ G = T := Φ.apply_symm_apply T
  have hGmat :
      (G : Matrix (Fin d) (Fin d) K) = LinearMap.toMatrix' (T : (Fin d → K) →ₗ[K] _) := by
    rw [← hGT]
    exact (LinearMap.toMatrix'_toLin' _).symm
  have hunit :
      ((G : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (G : Matrix (Fin d) (Fin d) K) = 1 := by
    have hT' : ∀ v w, hermForm h d ((T : (Fin d → K) →ₗ[K] (Fin d → K)) v)
        ((T : (Fin d → K) →ₗ[K] (Fin d → K)) w) = hermForm h d v w := fun v w => hT v w
    rw [hGmat]
    exact map_transpose_mul_toMatrix'_eq_one _ hT'
  have hdet : (G : Matrix (Fin d) (Fin d) K).det = 1 := by
    have h1 := congrArg Matrix.det hunit
    rw [det_mul, det_transpose, show ((G : Matrix (Fin d) (Fin d) K).map h.bar).det =
      h.bar (G : Matrix (Fin d) (Fin d) K).det from (RingHom.map_det h.bar _).symm, det_one] at h1
    have h2 : h.bar (G : Matrix (Fin d) (Fin d) K).det = (G : Matrix (Fin d) (Fin d) K).det := by
      rw [hGmat, LinearMap.det_toMatrix']
      exact hTdet
    rw [h2] at h1
    have h3 : ((G : Matrix (Fin d) (Fin d) K).det - 1) * ((G : Matrix (Fin d) (Fin d) K).det - 1)
        = 0 := by
      linear_combination h1 + (1 - (G : Matrix (Fin d) (Fin d) K).det) *
        (CharTwo.two_eq_zero (R := K))
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  have hGSU : G ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) :=
    (GGL45TG.SU.mem_su_iff h).mpr ⟨hunit, hdet⟩
  refine ⟨⟨G, hGSU⟩, fun s hs => hψinj ?_⟩
  rw [map_mul, map_mul, map_inv, map_pow]
  change Φ G * ψ s * (Φ G)⁻¹ = ψ s ^ Nat.card K
  rw [hGT]
  exact hTconj (ψ s) ⟨s, hs, rfl⟩

end UnitaryFrob

section Row


open LinearFrob FormFrob UnitaryFrob in
theorem ggTorusWNormSC_unitary_frob {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : ¬ p ∣ (2 ^ n) ^ 4 - 1) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hFD := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := hFD.charP
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    simp only [Prod.mk.injEq] at he
    omega
  have hpq2 := not_dvd_sq_sub_one_of_not_dvd_pow_four_sub_one hpq
  have hp1 : ¬ p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpq2
  have hpq1 : ¬ p ∣ 2 ^ n + 1 := fun h1 => hpq2 (by
    rw [show (2 ^ n) ^ 2 - 1 = (2 ^ n) ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact h1.mul_right _)
  obtain ⟨u, hu, hupow⟩ := exists_pow_mem_ggAutomizer_of_innerModel hp
    (TableBUE.center_proj_eq_bot hK (by omega) hdq)
    (NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega) hp hpq1)
    (ggCenterPrime_unitary_gcd hK hn (by omega) hdq hp hp2 fun h1 => hpq1 h1.2)
    ψ hψ hker hperf hA hAI hsc (k := Nat.card K)
    fun E hE _ _ => exists_conj_eq_pow_largeEvenProj hp hp2 hp1
      (fun P hc ho => exists_conj_eq_pow_card_su hFD P hc ho) hE
  have hsq := natCast_sq_eq_one_of_pow_mem hp5 Λ M C V ι φ h α hM hC hpair hlin hgen hu hupow
  apply hpq
  rw [show (2 ^ n) ^ 4 = Nat.card K ^ 2 by rw [hK]; ring]
  exact dvd_sq_sub_one_of_natCast_sq_eq_one hsq

end Row

theorem largeEvenLabelAll_wnorm_unitary_frob
    {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ lab.n)
    (ht : lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) (hr : 3 ≤ lab.rank)
    (hpq : ¬ p ∣ (2 ^ lab.n) ^ 4 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  have hp5 := LinearFrob.five_le_of_not_dvd_four_pow_sub_one hp hp2
    (not_dvd_sq_sub_one_of_not_dvd_pow_four_sub_one hpq)
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hn hpq ⊢
  rcases ht with rfl | ⟨rfl, rfl⟩
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_unitary_frob (d := r + 1) hK hn (by omega) hp hp5 hpq
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_unitary_frob (d := 4) hK hn (by norm_num) hp hp5 hpq

end CFSG.StandardType
