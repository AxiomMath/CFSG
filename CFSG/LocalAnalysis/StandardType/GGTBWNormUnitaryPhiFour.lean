module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryFrob
public import CFSG.LocalAnalysis.StandardType.GGTBWNormOrthPhiFour

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial Matrix

namespace UnitaryPhiFour

@[expose] def expo (p q : ℕ) : ℕ := ((p - 1) * q) ^ ((q + 1) ^ 2)

theorem natCast_expo_sq {p q : ℕ} [Fact p.Prime] (hq : Even q) (hpq : p ∣ q ^ 2 + 1) :
    ((expo p q : ℕ) : ZMod p) ^ 2 = -1 := by
  have hq2 : ((q : ℕ) : ZMod p) ^ 2 = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) p).mpr hpq
    push_cast at h
    linear_combination h
  have hp1 : (((p - 1 : ℕ) : ℕ) : ZMod p) = -1 := by
    have hp := (Fact.out : p.Prime).one_le
    rw [Nat.cast_sub hp, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hodd : Odd ((q + 1) ^ 2) := (hq.add_one).pow
  obtain ⟨r, hr⟩ := hodd
  rw [expo, Nat.cast_pow, Nat.cast_mul, hp1, ← pow_mul, mul_comm ((q + 1) ^ 2) 2, pow_mul,
    neg_one_mul, neg_sq, hq2, hr, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]

variable {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K) (d : ℕ)

include h in
theorem exists_eigen_su [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hpq : p ∣ (2 ^ n) ^ 2 + 1) (P : Subgroup (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hexp : ∀ x ∈ P, x ^ p = 1)
    (hcard : p ^ 2 ≤ Nat.card P) :
    ∃ g : LargeEvenSUGroup (Fin d) K (2 ^ n), (∀ x ∈ P, g * x * g⁻¹ ∈ P) ∧
      (∀ x ∈ P, g * x * g⁻¹ = x → x = 1) ∧
      (∃ x ∈ P, x ≠ 1 ∧ g * x * g⁻¹ = x ^ expo p (2 ^ n)) ∧
      ∀ x ∈ P, (g * x * g⁻¹) ^ expo p (2 ^ n) = x → x = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have hqeven : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
  have hk2 := natCast_expo_sq hqeven hpq
  have h20 : (2 : ZMod p) ≠ 0 := fun h2 => by
    have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2'))
  have hpow_eq : ∀ x ∈ P, ∀ a b : ℕ, x ^ a = x ^ b → x ≠ 1 → ((a : ℕ) : ZMod p) = b := by
    intro x hx a b hab hx1
    have hord : orderOf x = p := orderOf_eq_prime (hexp x hx) hx1
    rw [pow_eq_pow_iff_modEq, hord] at hab
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hab
  have hk1 : ((expo p (2 ^ n) : ℕ) : ZMod p) ≠ 1 := fun h1 => by
    rw [h1, one_pow] at hk2
    exact h20 (by linear_combination hk2)
  have hkk : ((expo p (2 ^ n) * expo p (2 ^ n) : ℕ) : ZMod p) ≠ 1 := fun h1 => by
    rw [Nat.cast_mul, ← sq, hk2] at h1
    exact h20 (by linear_combination -h1)
  let Φ : GL (Fin d) K ≃* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K))
  let ψ : LargeEvenSUGroup (Fin d) K (2 ^ n) →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    Φ.toMonoidHom.comp (LargeEvenSUGroup (Fin d) K (2 ^ n)).subtype
  have hψinj : Function.Injective ψ := Φ.injective.comp Subtype.val_injective
  have : Finite P := Subtype.finite
  have : Finite (P.map ψ) := inferInstanceAs (Finite ↥(ψ '' (P : Set _)))
  have hcomm' : ∀ x ∈ P.map ψ, ∀ y ∈ P.map ψ, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hexp' : ∀ x ∈ P.map ψ, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hodd' : Odd (Nat.card (P.map ψ)) := by
    have hS : IsPGroup p (P.map ψ) := fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, hexp' g g.2, Subgroup.coe_one])⟩
    obtain ⟨m, hm⟩ := hS.exists_card_eq
    rw [hm]
    exact (hp.odd_of_ne_two hp2).pow
  have hiso' : ∀ y ∈ P.map ψ, ∀ v w, UnitaryFrob.hermForm h d (y v) (y w) =
      UnitaryFrob.hermForm h d v w := by
    rintro _ ⟨s, -, rfl⟩ v w
    exact UnitaryFrob.hermForm_mulVec ((GGL45TG.SU.mem_su_iff h).mp s.2).1 v w
  obtain ⟨T, hT, hTconj⟩ := CFSG.LinearAlgebra.exists_hermitian_isometry_conj_eq_inv_pow h
    (UnitaryFrob.hermForm h d) (UnitaryFrob.hermForm_herm h) (UnitaryFrob.hermForm_nondeg h)
    hcomm' hodd' hiso'
  have hTc : ∀ y ∈ P.map ψ, T * y * T⁻¹ = y ^ ((p - 1) * 2 ^ n) := fun y hy => by
    rw [hTconj y hy, pow_mul,
      show y⁻¹ = y ^ (p - 1) from by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hp.one_le,
          hexp' y hy]]
  have hTm := CFSG.LinearAlgebra.FrobeniusIsometryEigen.conj_pow_eq_pow_pow hTc ((2 ^ n + 1) ^ 2)
  let G : GL (Fin d) K := Φ.symm (T ^ (2 ^ n + 1) ^ 2)
  have hGT : Φ G = T ^ (2 ^ n + 1) ^ 2 := Φ.apply_symm_apply _
  have hTmiso : ∀ v w, UnitaryFrob.hermForm h d ((T ^ (2 ^ n + 1) ^ 2) v) ((T ^ (2 ^ n + 1) ^ 2) w) =
      UnitaryFrob.hermForm h d v w := by
    have : ∀ j : ℕ, ∀ v w, UnitaryFrob.hermForm h d ((T ^ j) v) ((T ^ j) w) =
        UnitaryFrob.hermForm h d v w := by
      intro j
      induction j with
      | zero => intro v w; rfl
      | succ j ih => intro v w; rw [pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih, hT]
    exact this _
  have hGmat : (G : Matrix (Fin d) (Fin d) K) =
      LinearMap.toMatrix' ((T ^ (2 ^ n + 1) ^ 2 : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
        (Fin d → K) →ₗ[K] _) := by
    rw [← hGT]
    exact (LinearMap.toMatrix'_toLin' _).symm
  have hunit : ((G : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (G : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hGmat]
    exact UnitaryFrob.map_transpose_mul_toMatrix'_eq_one _ fun v w => hTmiso v w
  let G₁ : GL (Fin d) K := Φ.symm T
  have hG₁T : Φ G₁ = T := Φ.apply_symm_apply _
  have hG₁mat : (G₁ : Matrix (Fin d) (Fin d) K) =
      LinearMap.toMatrix' (T : (Fin d → K) →ₗ[K] _) := by
    rw [← hG₁T]
    exact (LinearMap.toMatrix'_toLin' _).symm
  have hunit₁ : ((G₁ : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (G₁ : Matrix (Fin d) (Fin d) K) =
      1 := by
    rw [hG₁mat]
    exact UnitaryFrob.map_transpose_mul_toMatrix'_eq_one _ fun v w => hT v w
  have hdetT : LinearMap.det (T : (Fin d → K) →ₗ[K] _) ^ (2 ^ n + 1) = 1 := by
    have h1 := congrArg Matrix.det hunit₁
    rw [det_mul, det_transpose, show ((G₁ : Matrix (Fin d) (Fin d) K).map h.bar).det =
      h.bar (G₁ : Matrix (Fin d) (Fin d) K).det from (RingHom.map_det h.bar _).symm, det_one,
      hG₁mat, LinearMap.det_toMatrix', UnitaryFieldData.bar_apply] at h1
    rw [pow_succ]
    exact h1
  have hdet : (G : Matrix (Fin d) (Fin d) K).det = 1 := by
    rw [hGmat, LinearMap.det_toMatrix', ← LinearEquiv.coe_det, map_pow, Units.val_pow_eq_pow_val,
      LinearEquiv.coe_det, sq, pow_mul, hdetT, one_pow]
  have hGSU : G ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) :=
    (GGL45TG.SU.mem_su_iff h).mpr ⟨hunit, hdet⟩
  have hact : ∀ x ∈ P, (⟨G, hGSU⟩ : LargeEvenSUGroup (Fin d) K (2 ^ n)) * x * ⟨G, hGSU⟩⁻¹ =
      x ^ expo p (2 ^ n) :=
    fun x hx => hψinj (by
      rw [map_mul, map_mul, map_inv, map_pow]
      change Φ G * ψ x * (Φ G)⁻¹ = ψ x ^ expo p (2 ^ n)
      rw [hGT, hTm (ψ x) ⟨x, hx, rfl⟩]
      rfl)
  obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot P).mp
      (lt_of_lt_of_le (Nat.one_lt_pow two_ne_zero hp.one_lt) hcard))
  have hx₀1' : x₀ ≠ 1 := fun h1 => hx₀1 (Subtype.ext h1)
  refine ⟨⟨G, hGSU⟩, fun x hx => ?_, fun x hx hxe => ?_, ⟨x₀, hx₀, hx₀1', hact x₀ hx₀⟩,
    fun x hx hxe => ?_⟩
  · rw [hact x hx]
    exact P.pow_mem hx _
  · rw [hact x hx] at hxe
    by_contra hx1
    exact hk1 ((hpow_eq x hx _ 1 (by rw [pow_one]; exact hxe) hx1).trans Nat.cast_one)
  · rw [hact x hx, ← pow_mul] at hxe
    by_contra hx1
    exact hkk ((hpow_eq x hx _ 1 (by rw [pow_one]; exact hxe) hx1).trans Nat.cast_one)

end UnitaryPhiFour

section Row


open LinearFrob FormFrob UnitaryFrob UnitaryPhiFour OrthPhiFour in
theorem ggTorusWNormSC_unitary_phi4 {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ (2 ^ n) ^ 2 + 1) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L _ _ ψ hψ hker hperf A hA hAI hA3 hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hp2 : p ≠ 2 := by omega
  have hFD := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := hFD.charP
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    simp only [Prod.mk.injEq] at he
    omega
  have hpq2 : ¬ p ∣ (2 ^ n) ^ 2 - 1 := fun h1 => by
    have hle : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h2 : (2 ^ n) ^ 2 + 1 = ((2 ^ n) ^ 2 - 1) + 2 := by omega
    rw [h2] at hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((Nat.dvd_add_right h1).mp hpq))
  have hp1 : ¬ p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpq2
  have hpq1 : ¬ p ∣ 2 ^ n + 1 := fun h1 => hpq2 (by
    rw [show (2 ^ n) ^ 2 - 1 = (2 ^ n) ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact h1.mul_right _)
  obtain ⟨u, hu, hufix, huev, huinv⟩ := exists_eigen_mem_ggAutomizer_of_innerModel hp
    (TableBUE.center_proj_eq_bot hK (by omega) hdq)
    (NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega) hp hpq1)
    (ggCenterPrime_unitary_gcd hK hn (by omega) hdq hp hp2 fun h1 => hpq1 h1.2)
    ψ hψ hker hperf hA hAI hsc (k := expo p (2 ^ n))
    fun E hE hEc hEsc => exists_eigen_largeEvenProj hp hp1
      (fun P hc hx _ hcard => exists_eigen_su hFD d hp hp2 hn hpq P hc hx hcard) hE
      (by rw [hEc]; exact (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hA3) hEsc
  exact false_of_eigen_mem_ggAutomizer hp5 Λ M C V ι φ h α hM hC hpair hlin hgen hu hufix huev
    huinv

end Row

theorem largeEvenLabelAll_wnorm_unitary_phi4
    {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ lab.n)
    (ht : lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) (hr : 3 ≤ lab.rank)
    (hpq : ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  by_cases h4 : p ∣ (2 ^ lab.n) ^ 4 - 1
  swap
  · exact largeEvenLabelAll_wnorm_unitary_frob hp hp2 hn ht hr h4
  have hp5 := LinearFrob.five_le_of_not_dvd_four_pow_sub_one hp hp2 hpq
  have hpq' : p ∣ (2 ^ lab.n) ^ 2 + 1 := by
    have hfac : (2 ^ lab.n) ^ 4 - 1 = ((2 ^ lab.n) ^ 2 + 1) * ((2 ^ lab.n) ^ 2 - 1) := by
      rw [show (2 ^ lab.n) ^ 4 - 1 = ((2 ^ lab.n) ^ 2) ^ 2 - 1 ^ 2 by
        rw [one_pow, ← pow_mul (2 ^ lab.n) 2 2], Nat.sq_sub_sq]
    rw [hfac] at h4
    exact (hp.dvd_mul.mp h4).resolve_right hpq
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hr hn hpq' ⊢
  rcases ht with rfl | ⟨rfl, rfl⟩
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_unitary_phi4 (d := r + 1) hK hn (by omega) hp hp5 hpq'
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_unitary_phi4 (d := 4) hK hn (by norm_num) hp hp5 hpq'

end CFSG.StandardType
