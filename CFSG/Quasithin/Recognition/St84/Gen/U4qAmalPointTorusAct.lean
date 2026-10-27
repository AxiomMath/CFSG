module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLineVertex

import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalSchur
import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
import CFSG.Quasithin.H13.L32NLem14324g
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits
open scoped MatrixGroups

section Data

variable {G : Type*} [Group G]

structure U4qTorusData (L1 L2 S H₀ : Subgroup G) (f : ℕ) : Prop where
  le_bigB : H₀ ≤ bigB L1 L2 S
  comm : ∀ a ∈ H₀, ∀ b ∈ H₀, a * b = b * a
  card : Nat.card H₀ = 4 ^ f - 1
  conj_mem : ∀ h ∈ H₀, ∀ x ∈ L1, h * x * h⁻¹ * x⁻¹ ∈ pCoreOf 2 L1

variable {L1 L2 S H₀ : Subgroup G} {f : ℕ}

private theorem U4qTorusData.conj_mem_left (hT : U4qTorusData L1 L2 S H₀ f) {h x : G}
    (hh : h ∈ H₀) (hx : x ∈ L1) : h * x * h⁻¹ ∈ L1 := by
  have e := L1.mul_mem (pCoreOf_le 2 L1 (hT.conj_mem h hh x hx)) hx
  rwa [inv_mul_cancel_right] at e

theorem U4qTorusData.le_normalizer_left (hT : U4qTorusData L1 L2 S H₀ f) :
    H₀ ≤ Subgroup.normalizer (L1 : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hT.conj_mem_left hh hx, fun hx => ?_⟩
  have e := hT.conj_mem_left (H₀.inv_mem hh) hx
  have e' : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [e'] at e

theorem U4qTorusData.le_normalizer_pCoreOf_left (hT : U4qTorusData L1 L2 S H₀ f) :
    H₀ ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
  hT.le_normalizer_left.trans (normalizer_le_normalizer_pCoreOf 2 L1)

private theorem bigB_le_normalizer_right_tor (hH : Hyp111 L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
  rw [bigB]
  exact sup_le (sup_le hH.h2.borel_le ((borelOf_le L2 S).trans Subgroup.le_normalizer))
    hH.h2.normalizes

theorem U4qTorusData.le_normalizer_right (hH : Hyp111 L1 L2 S)
    (hT : U4qTorusData L1 L2 S H₀ f) : H₀ ≤ Subgroup.normalizer (L2 : Set G) :=
  hT.le_bigB.trans (bigB_le_normalizer_right_tor hH)

theorem U4qTorusData.le_normalizer_pCoreOf_right (hH : Hyp111 L1 L2 S)
    (hT : U4qTorusData L1 L2 S H₀ f) : H₀ ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
  (hT.le_normalizer_right hH).trans (normalizer_le_normalizer_pCoreOf 2 L2)

private theorem U4qTorusData.odd_card (hT : U4qTorusData L1 L2 S H₀ f) (hf : 1 ≤ f) :
    Odd (Nat.card H₀) := by
  rw [hT.card]
  have h4 : Even (4 ^ f) := (show Even 4 by norm_num).pow_of_ne_zero (by omega)
  exact Nat.Even.sub_odd (Nat.one_le_pow f 4 (by norm_num)) h4 (by norm_num)

private theorem U4qTorusData.coprime_two_pow (hT : U4qTorusData L1 L2 S H₀ f) (hf : 1 ≤ f)
    (k : ℕ) : Nat.Coprime (Nat.card H₀) (2 ^ k) :=
  Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hT.odd_card hf))

private theorem conj_mem_centerOf_tor {Q : Subgroup G} {p z : G}
    (hp : p ∈ Subgroup.normalizer (Q : Set G)) (hz : z ∈ centerOf Q) :
    p * z * p⁻¹ ∈ centerOf Q := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hp z).mp hz.1,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : p⁻¹ * y * p ∈ Q := by
    have e := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hp) y).mp hy
    rwa [inv_inv] at e
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hy'
  calc y * (p * z * p⁻¹) = p * ((p⁻¹ * y * p) * z) * p⁻¹ := by group
    _ = p * (z * (p⁻¹ * y * p)) * p⁻¹ := by rw [hc]
    _ = p * z * p⁻¹ * y := by group

theorem U4qTorusData.exists_mul_beta (hT : U4qTorusData L1 L2 S H₀ f) {F : Type} [Field F]
    (c₁ : U4qCoordLeft L1 L2 S f F) {h : G} (hh : h ∈ H₀) :
    ∃ M : Matrix (Fin 2) (Fin 2) F, ∀ (u : G) (hu : u ∈ pCoreOf 2 L1)
      (hhu : h * u * h⁻¹ ∈ pCoreOf 2 L1),
      Multiplicative.toAdd (c₁.β ⟨h * u * h⁻¹, hhu⟩) =
        Multiplicative.toAdd (c₁.β ⟨u, hu⟩) * M := by
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; positivity)
  haveI := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  have hN : h ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) := hT.le_normalizer_pCoreOf_left hh
  let ψ : MulAut ↥(pCoreOf 2 L1) := (pCoreOf 2 L1).normalizerMonoidHom ⟨h, hN⟩
  have hψ : ∀ u : ↥(pCoreOf 2 L1), ((ψ u : ↥(pCoreOf 2 L1)) : G) = h * u * h⁻¹ := fun u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (pCoreOf 2 L1) ⟨h, hN⟩ u
  have hker : ∀ u : ↥(pCoreOf 2 L1), c₁.β u = 1 → c₁.β (ψ u) = 1 := by
    intro u hu
    have hu' : u ∈ c₁.β.ker := hu
    rw [c₁.ker_β, Subgroup.mem_subgroupOf] at hu'
    have hψu : ψ u ∈ c₁.β.ker := by
      rw [c₁.ker_β, Subgroup.mem_subgroupOf, hψ]
      exact conj_mem_centerOf_tor hN hu'
    exact hψu
  choose sec hsec using fun X => c₁.surjective_β X
  have hwd : ∀ u : ↥(pCoreOf 2 L1), c₁.β (ψ (sec (c₁.β u))) = c₁.β (ψ u) := by
    intro u
    have h1 : c₁.β ((sec (c₁.β u))⁻¹ * u) = 1 := by rw [map_mul, map_inv, hsec, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at h2
    exact h2
  let T : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F :=
    AddMonoidHom.mk' (fun X => Multiplicative.toAdd (c₁.β (ψ (sec (Multiplicative.ofAdd X)))))
      (by
        intro X Y
        have e : Multiplicative.ofAdd (X + Y) =
            c₁.β (sec (Multiplicative.ofAdd X) * sec (Multiplicative.ofAdd Y)) := by
          rw [map_mul, hsec, hsec, ofAdd_add]
        simp only [e]
        rw [hwd, map_mul, map_mul, toAdd_mul])
  have hTβ : ∀ u : ↥(pCoreOf 2 L1), T (Multiplicative.toAdd (c₁.β u)) =
      Multiplicative.toAdd (c₁.β (ψ u)) := by
    intro u
    change Multiplicative.toAdd (c₁.β (ψ (sec (Multiplicative.ofAdd
      (Multiplicative.toAdd (c₁.β u)))))) = _
    rw [ofAdd_toAdd, hwd]
  have hTcomm : ∀ (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F),
      T ((g : Matrix (Fin 2) (Fin 2) F) * X) = (g : Matrix (Fin 2) (Fin 2) F) * T X := by
    intro g X
    obtain ⟨x, rfl⟩ := c₁.surjective_α g
    obtain ⟨u, rfl⟩ : ∃ u, Multiplicative.toAdd (c₁.β u) = X :=
      ⟨sec (Multiplicative.ofAdd X), by rw [hsec]; rfl⟩
    let w : ↥(pCoreOf 2 L1) := ⟨(x : G) * u * (x : G)⁻¹,
      CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf x.2 u.2⟩
    let y : ↥L1 := ⟨h * (x : G) * h⁻¹, hT.conj_mem_left hh x.2⟩
    have hαy : c₁.α y = c₁.α x := by
      have hq : ((y * x⁻¹ : ↥L1) : G) ∈ pCoreOf 2 L1 := hT.conj_mem h hh x x.2
      have e := (c₁.eq_one_iff (y * x⁻¹)).mpr hq
      rwa [map_mul, map_inv, mul_inv_eq_one] at e
    rw [← c₁.equivariant x u w rfl, hTβ, hTβ, ← hαy]
    refine c₁.equivariant y (ψ u) (ψ w) ?_
    rw [hψ, hψ]
    change h * ((x : G) * u * (x : G)⁻¹) * h⁻¹ =
      h * (x : G) * h⁻¹ * (h * u * h⁻¹) * (h * (x : G) * h⁻¹)⁻¹
    group
  refine ⟨T 1, fun u hu hhu => ?_⟩
  have hψu : ψ ⟨u, hu⟩ = ⟨h * u * h⁻¹, hhu⟩ := Subtype.ext (hψ _)
  rw [← hψu, ← hTβ]
  exact CFSG.Quasithin.H13.L14324.eq_mul_of_comm_left T hTcomm _

theorem U4qTorusData.exists_rowwise_beta (hT : U4qTorusData L1 L2 S H₀ f) {F : Type}
    [Field F] (c₁ : U4qCoordLeft L1 L2 S f F) {h : G} (hh : h ∈ H₀) :
    ∃ τ : (Fin 2 → F) →+ (Fin 2 → F), ∀ (u : G) (hu : u ∈ pCoreOf 2 L1)
      (hhu : h * u * h⁻¹ ∈ pCoreOf 2 L1) (i : Fin 2),
      Multiplicative.toAdd (c₁.β ⟨h * u * h⁻¹, hhu⟩) i =
        τ (Multiplicative.toAdd (c₁.β ⟨u, hu⟩) i) := by
  obtain ⟨M, hM⟩ := hT.exists_mul_beta c₁ hh
  refine ⟨AddMonoidHom.mk' (fun v => v ᵥ* M) (fun v w => Matrix.add_vecMul M v w),
    fun u hu hhu i => ?_⟩
  rw [hM u hu hhu]
  rfl

end Data

section Faithful

variable {m : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 m K)

theorem eq_of_forall_twist_eq {A B : Matrix (Fin 2) (Fin 2) K} (hB : IsUnit B.det)
    (hA : hU.bar A.det = A.det) (hBf : hU.bar B.det = B.det)
    (htw : ∀ X ∈ u4Herm hU, A * X * (A.map hU.bar)ᵀ = B * X * (B.map hU.bar)ᵀ) : A = B := by
  have hBB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBB' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hdet : B.det * (B⁻¹ * A).det = A.det := by
    rw [← Matrix.det_mul, ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  have hfix : hU.bar (B⁻¹ * A).det = (B⁻¹ * A).det := by
    have e := congrArg hU.bar hdet
    rw [map_mul, hBf, hA, ← hdet] at e
    exact mul_left_cancel₀ hB.ne_zero e
  have hσ : (B.map hU.bar)ᵀ * ((B⁻¹).map hU.bar)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hBB,
      Matrix.map_one _ (map_zero hU.bar) (map_one hU.bar), Matrix.transpose_one]
  have h1 : B⁻¹ * A = 1 := by
    refine eq_one_of_forall_twist_eq hU hfix fun X hX => ?_
    calc B⁻¹ * A * X * ((B⁻¹ * A).map hU.bar)ᵀ =
        B⁻¹ * (A * X * (A.map hU.bar)ᵀ) * ((B⁻¹).map hU.bar)ᵀ := by
          simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B⁻¹ * (B * X * (B.map hU.bar)ᵀ) * ((B⁻¹).map hU.bar)ᵀ := by rw [htw X hX]
      _ = X := by
          simp only [Matrix.mul_assoc]
          rw [hσ, Matrix.mul_one, ← Matrix.mul_assoc, hBB, Matrix.one_mul]
  calc A = B * (B⁻¹ * A) := by rw [← Matrix.mul_assoc, hBB', Matrix.one_mul]
    _ = B := by rw [h1, Matrix.mul_one]

private theorem twist_mul_eq_tor (P Q X : Matrix (Fin 2) (Fin 2) K) :
    P * Q * X * ((P * Q).map hU.bar)ᵀ = P * (Q * X * (Q.map hU.bar)ᵀ) * (P.map hU.bar)ᵀ := by
  simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem twist_smul_one_tor (c : K) (X : Matrix (Fin 2) (Fin 2) K) :
    (c • (1 : Matrix (Fin 2) (Fin 2) K)) * X *
        ((c • (1 : Matrix (Fin 2) (Fin 2) K)).map hU.bar)ᵀ = (c * hU.bar c) • X := by
  ext i j
  rw [mul_mul_map_bar_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.one_apply] <;> ring

private theorem twist_mul_self_eq_of_eq_tor {A : Matrix (Fin 2) (Fin 2) K} (h10 : A 1 0 = 0)
    (hd : A 0 0 = A 1 1) (hN : A 1 1 * hU.bar (A 1 1) = 1) (X : Matrix (Fin 2) (Fin 2) K) :
    A * A * X * ((A * A).map hU.bar)ᵀ = X := by
  haveI := hU.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : A * A = (A 1 1 * A 1 1) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hd]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hd]
      linear_combination (A 0 1 * A 1 1) * h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hd]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hd]
  have hc : A 1 1 * A 1 1 * hU.bar (A 1 1 * A 1 1) = 1 := by
    rw [map_mul]
    linear_combination (A 1 1 * hU.bar (A 1 1) + 1) * hN
  rw [hsq, twist_smul_one_tor hU, hc, one_smul]

private theorem exists_fixed_ne_zero_ne_one_tor (hm : 2 ≤ m) :
    ∃ c : K, hU.bar c = c ∧ c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective fun c : hU.fixedField => decide ((c : K) = 0) := by
    intro a b hab
    by_cases ha : (a : K) = 0
    · have hb : (b : K) = 0 := by simpa [ha] using hab.symm
      exact Subtype.ext (ha.trans hb.symm)
    · have hb : (b : K) ≠ 0 := by simpa [ha] using hab.symm
      exact Subtype.ext ((hcon a ((hU.mem_fixedField).mp a.2) ha).trans
        (hcon b ((hU.mem_fixedField).mp b.2) hb).symm)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hU.card_fixedField, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

end Faithful

section Twist

variable {G : Type} [Group G] {L1 L2 S : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (c₂ : U4qCoordRight L1 L2 S f K) (hU : UnitaryFieldData 2 f K)

private theorem U4qCoordRight.equivariant_tor (x : ↥L2) (u v : ↥(pCoreOf 2 L2))
    (hv : (v : G) = x * u * x⁻¹) :
    Multiplicative.toAdd (c₂.β v) = (c₂.α x : Matrix (Fin 2) (Fin 2) K) *
      Multiplicative.toAdd (c₂.β u) * ((c₂.α x : Matrix (Fin 2) (Fin 2) K).map hU.bar)ᵀ := by
  have hpow : (fun y : K => y ^ 2 ^ f) = ⇑hU.bar := funext fun y => (hU.bar_apply y).symm
  have h := c₂.equivariant x u v hv
  rw [hpow] at h
  exact h

private theorem U4qCoordRight.exists_beta_eq_tor {X : Matrix (Fin 2) (Fin 2) K}
    (hX : X ∈ u4Herm hU) : ∃ u, Multiplicative.toAdd (c₂.β u) = X :=
  (c₂.range_iff X).mpr ((mem_u4Herm_iff_pow hU).mp hX)

theorem U4qCoordRight.eq_of_twist_of_mem_normalizer {p : G}
    (hp : p ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G)) {A B : Matrix (Fin 2) (Fin 2) K}
    (hB : IsUnit B.det) (hA : hU.bar A.det = A.det) (hBf : hU.bar B.det = B.det)
    (hpA : ∀ u v : ↥(pCoreOf 2 L2), (v : G) = p * u * p⁻¹ →
      Multiplicative.toAdd (c₂.β v) = A * Multiplicative.toAdd (c₂.β u) * (A.map hU.bar)ᵀ)
    (hpB : ∀ u v : ↥(pCoreOf 2 L2), (v : G) = p * u * p⁻¹ →
      Multiplicative.toAdd (c₂.β v) = B * Multiplicative.toAdd (c₂.β u) * (B.map hU.bar)ᵀ) :
    A = B := by
  refine eq_of_forall_twist_eq hU hB hA hBf fun X hX => ?_
  obtain ⟨u, rfl⟩ := c₂.exists_beta_eq_tor hU hX
  let v : ↥(pCoreOf 2 L2) := ⟨p * u * p⁻¹, (Subgroup.mem_normalizer_iff.mp hp u).mp u.2⟩
  rw [← hpA u v rfl, ← hpB u v rfl]

private theorem U4qCoordRight.twist_mul_tor {p q : G}
    (hq : q ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G)) {A B : Matrix (Fin 2) (Fin 2) K}
    (hpA : ∀ u v : ↥(pCoreOf 2 L2), (v : G) = p * u * p⁻¹ →
      Multiplicative.toAdd (c₂.β v) = A * Multiplicative.toAdd (c₂.β u) * (A.map hU.bar)ᵀ)
    (hqB : ∀ u v : ↥(pCoreOf 2 L2), (v : G) = q * u * q⁻¹ →
      Multiplicative.toAdd (c₂.β v) = B * Multiplicative.toAdd (c₂.β u) * (B.map hU.bar)ᵀ) :
    ∀ u v : ↥(pCoreOf 2 L2), (v : G) = p * q * u * (p * q)⁻¹ →
      Multiplicative.toAdd (c₂.β v) =
        A * B * Multiplicative.toAdd (c₂.β u) * ((A * B).map hU.bar)ᵀ := by
  intro u v hv
  let w : ↥(pCoreOf 2 L2) := ⟨q * u * q⁻¹, (Subgroup.mem_normalizer_iff.mp hq u).mp u.2⟩
  have hvw : (v : G) = p * w * p⁻¹ := by
    rw [hv]
    change p * q * u * (p * q)⁻¹ = p * (q * u * q⁻¹) * p⁻¹
    group
  rw [hpA w v hvw, hqB u w rfl]
  simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

end Twist

section Vertex

variable {G : Type} [Group G] [Finite G] {L1 L2 S H₀ : Subgroup G} {f : ℕ}

private theorem sup_bigB_inf_centralizer_le_tor (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer (pCoreOf 2 L2 : Set G) ≤ pCoreOf 2 L2 := by
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hP : L2 ⊔ bigB L1 L2 S = L2 ⊔ borelOf L1 S := sup_bigB_right_of_le hSL2
  have h := hH.h2.charTwo
  unfold CharTwo at h
  rw [sup_eq_left.mpr hSL2, ← hP, pCoreOf_sup_bigB_right_of_le hH hSL1 hSL2] at h
  exact h

theorem U4qLocalData.exists_twist_of_mem_torus (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) {K : Type} [Field K] (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) {h : G} (hh : h ∈ H₀) :
    ∃ A : GL (Fin 2) K, A ∈ u4DetFixGL hU ∧ (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      hU.norm ((A : Matrix (Fin 2) (Fin 2) K) 1 1) = 1 ∧
      (∀ u v : ↥(pCoreOf 2 L2), (v : G) = h * u * h⁻¹ →
        Multiplicative.toAdd (c₂.β v) = (A : Matrix (Fin 2) (Fin 2) K) *
          Multiplicative.toAdd (c₂.β u) * ((A : Matrix (Fin 2) (Fin 2) K).map hU.bar)ᵀ) ∧
      ∀ (x : G) (hx : x ∈ L2) (hhx : h * x * h⁻¹ ∈ L2),
        (c₂.α ⟨h * x * h⁻¹, hhx⟩ : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
          (A : Matrix (Fin 2) (Fin 2) K) * (c₂.α ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) K) := by
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hN1 : h ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) := hT.le_normalizer_pCoreOf_left hh
  have hN2 : h ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    hT.le_normalizer_pCoreOf_right hH hh
  obtain ⟨A, hA, hhA⟩ := hD.exists_twist_of_mem_sup_bigB hH hS c₂ hU
    (Subgroup.mem_sup_right (hT.le_bigB hh))
  have htw := (c₂.actsByMatrix_coordEquiv_iff hU _ _).mp hhA
  refine ⟨A, hA, ?_⟩
  set Am : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hAm
  obtain ⟨z, hz⟩ := (c₂.range_iff (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K)).mpr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp)
  have hzZ : (z : G) ∈ centerOf (pCoreOf 2 L1) :=
    (c₂.mem_center_iff z).mpr ⟨by rw [hz]; rfl, by rw [hz]; rfl⟩
  let z' : ↥(pCoreOf 2 L2) := ⟨h * z * h⁻¹, (Subgroup.mem_normalizer_iff.mp hN2 z).mp z.2⟩
  have hz' := ((c₂.mem_center_iff z').mp (conj_mem_centerOf_tor hN1 hzZ)).2
  rw [htw z z' rfl, hz, mul_mul_map_bar_transpose_apply] at hz'
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at hz'
  have hA10 : Am 1 0 = 0 := by
    have h0 : Am 1 0 * hU.bar (Am 1 0) = 0 := by linear_combination hz'
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact h0
    · exact (map_eq_zero hU.bar).mp h0
  refine ⟨hA10, ?_, htw, ?_⟩
  ·
    obtain ⟨e, he⟩ := (c₂.range_iff (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K)).mpr (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp)
    let e' : ↥(pCoreOf 2 L2) := ⟨h * e * h⁻¹, (Subgroup.mem_normalizer_iff.mp hN2 e).mp e.2⟩
    have hmem : ((e' * e⁻¹ : ↥(pCoreOf 2 L2)) : G) ∈ pCoreOf 2 L1 :=
      hT.conj_mem h hh e (hSL1 (hH.pCoreOf_le_right e.2))
    have h11 := (c₂.mem_inf_iff (e' * e⁻¹)).mp hmem
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, htw e e' rfl, he, Matrix.add_apply,
      Matrix.neg_apply, mul_mul_map_bar_transpose_apply] at h11
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h11
    rw [UnitaryFieldData.norm]
    linear_combination h11
  ·
    intro x hx hhx
    have hAu : IsUnit Am.det := by
      rw [hAm, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.isUnit _
    have hdet1 : ∀ y : ↥L2, (c₂.α y : Matrix (Fin 2) (Fin 2) K).det = 1 := fun y => (c₂.α y).2
    refine eq_of_forall_twist_eq hU ?_ ?_ ?_ fun X hX => ?_
    · rw [Matrix.det_mul, hdet1, mul_one]
      exact hAu
    · rw [Matrix.det_mul, hdet1, one_mul]
      exact hA
    · rw [Matrix.det_mul, hdet1, mul_one]
      exact hA
    · obtain ⟨u, rfl⟩ := c₂.exists_beta_eq_tor hU hX
      let u' : ↥(pCoreOf 2 L2) := ⟨h * u * h⁻¹, (Subgroup.mem_normalizer_iff.mp hN2 u).mp u.2⟩
      let w : ↥(pCoreOf 2 L2) :=
        ⟨x * u * x⁻¹, CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hx u.2⟩
      let v : ↥(pCoreOf 2 L2) := ⟨h * w * h⁻¹, (Subgroup.mem_normalizer_iff.mp hN2 w).mp w.2⟩
      have hv : (v : G) = (h * x * h⁻¹) * u' * (h * x * h⁻¹)⁻¹ := by
        change h * (x * u * x⁻¹) * h⁻¹ = h * x * h⁻¹ * (h * u * h⁻¹) * (h * x * h⁻¹)⁻¹
        group
      rw [twist_mul_eq_tor hU, twist_mul_eq_tor hU, ← htw u u' rfl,
        ← c₂.equivariant_tor hU ⟨h * x * h⁻¹, hhx⟩ u' v hv,
        ← c₂.equivariant_tor hU ⟨x, hx⟩ u w rfl, ← htw w v rfl]

theorem U4qLocalData.exists_torusTwist (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (hT : U4qTorusData L1 L2 S H₀ f) {K : Type} [Field K]
    (c₂ : U4qCoordRight L1 L2 S f K) (hU : UnitaryFieldData 2 f K) :
    ∃ (A : ↥H₀ →* GL (Fin 2) K) (κ : ↥H₀ ≃* Kˣ),
      (∀ h : ↥H₀, A h ∈ u4DetFixGL hU) ∧
      (∀ h : ↥H₀, (A h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) ∧
      (∀ h : ↥H₀, hU.norm ((A h : Matrix (Fin 2) (Fin 2) K) 1 1) = 1) ∧
      (∀ h : ↥H₀, (κ h : K) =
        (A h : Matrix (Fin 2) (Fin 2) K) 0 0 / (A h : Matrix (Fin 2) (Fin 2) K) 1 1) ∧
      (∀ (h : ↥H₀) (u v : ↥(pCoreOf 2 L2)), (v : G) = (h : G) * u * (h : G)⁻¹ →
        Multiplicative.toAdd (c₂.β v) = (A h : Matrix (Fin 2) (Fin 2) K) *
          Multiplicative.toAdd (c₂.β u) * ((A h : Matrix (Fin 2) (Fin 2) K).map hU.bar)ᵀ) ∧
      ∀ (h : ↥H₀) (x : G) (hx : x ∈ L2) (hhx : (h : G) * x * (h : G)⁻¹ ∈ L2),
        (c₂.α ⟨(h : G) * x * (h : G)⁻¹, hhx⟩ : Matrix (Fin 2) (Fin 2) K) *
            (A h : Matrix (Fin 2) (Fin 2) K) =
          (A h : Matrix (Fin 2) (Fin 2) K) * (c₂.α ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) K) := by
  classical
  haveI : Finite K := hU.finite
  have hf : 1 ≤ f := hD.one_le
  choose Af hAf using fun h : ↥H₀ => hD.exists_twist_of_mem_torus hH hS hT c₂ hU h.2
  have hN2 : ∀ h : ↥H₀, (h : G) ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    fun h => hT.le_normalizer_pCoreOf_right hH h.2
  have huniq : ∀ (h : ↥H₀) (B : GL (Fin 2) K), B ∈ u4DetFixGL hU →
      (∀ u v : ↥(pCoreOf 2 L2), (v : G) = (h : G) * u * (h : G)⁻¹ →
        Multiplicative.toAdd (c₂.β v) = (B : Matrix (Fin 2) (Fin 2) K) *
          Multiplicative.toAdd (c₂.β u) * ((B : Matrix (Fin 2) (Fin 2) K).map hU.bar)ᵀ) →
      Af h = B := by
    intro h B hB hhB
    apply Units.ext
    refine c₂.eq_of_twist_of_mem_normalizer hU (hN2 h) ?_ (hAf h).1 hB (hAf h).2.2.2.1 hhB
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  have hAmul : ∀ h h' : ↥H₀, Af (h * h') = Af h * Af h' := by
    intro h h'
    refine huniq (h * h') _ (Subgroup.mul_mem _ (hAf h).1 (hAf h').1) fun u v hv => ?_
    rw [Units.val_mul]
    exact c₂.twist_mul_tor hU (hN2 h') (hAf h).2.2.2.1 (hAf h').2.2.2.1 u v hv
  have hdiag : ∀ h : ↥H₀, (Af h : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 ∧
      (Af h : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro h
    have hdet : (Af h : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    rw [Matrix.det_fin_two, (hAf h).2.1, mul_zero, sub_zero] at hdet
    exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩
  have hmul00 : ∀ h h' : ↥H₀, (Af (h * h') : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (Af h : Matrix (Fin 2) (Fin 2) K) 0 0 * (Af h' : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    intro h h'
    rw [hAmul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, (hAf h').2.1, mul_zero,
      add_zero]
  have hmul11 : ∀ h h' : ↥H₀, (Af (h * h') : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (Af h : Matrix (Fin 2) (Fin 2) K) 1 1 * (Af h' : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    intro h h'
    rw [hAmul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, (hAf h).2.1, zero_mul,
      zero_add]
  let κf : ↥H₀ → Kˣ := fun h => Units.mk0 ((Af h : Matrix (Fin 2) (Fin 2) K) 0 0 /
    (Af h : Matrix (Fin 2) (Fin 2) K) 1 1) (div_ne_zero (hdiag h).1 (hdiag h).2)
  have hκmul : ∀ h h' : ↥H₀, κf (h * h') = κf h * κf h' := by
    intro h h'
    apply Units.ext
    simp only [κf, Units.val_mk0, Units.val_mul]
    rw [hmul00, hmul11, div_mul_div_comm]
  let κ : ↥H₀ →* Kˣ := MonoidHom.mk' κf hκmul
  have hcent := sup_bigB_inf_centralizer_le_tor hH hD hS
  have hinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro h hh1
    have hk : (Af h : Matrix (Fin 2) (Fin 2) K) 0 0 = (Af h : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      have e : ((κ h : Kˣ) : K) = 1 := by rw [hh1, Units.val_one]
      exact (div_eq_one_iff_eq (hdiag h).2).mp e
    have hsq : ∀ u : ↥(pCoreOf 2 L2), (u : G) * ((h : G) * h) = ((h : G) * h) * u := by
      intro u
      let v : ↥(pCoreOf 2 L2) := ⟨(h : G) * h * u * ((h : G) * h)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.mul_mem _ (hN2 h) (hN2 h)) u).mp u.2⟩
      have e := c₂.twist_mul_tor hU (hN2 h) (hAf h).2.2.2.1 (hAf h).2.2.2.1 u v rfl
      rw [twist_mul_self_eq_of_eq_tor hU (hAf h).2.1 hk (hAf h).2.2.1] at e
      have hvu : (h : G) * h * u * ((h : G) * h)⁻¹ = u :=
        congrArg Subtype.val (c₂.injective_β (Multiplicative.toAdd.injective e))
      calc (u : G) * ((h : G) * h) = ((h : G) * h * u * ((h : G) * h)⁻¹) * ((h : G) * h) := by
            rw [hvu]
        _ = (h : G) * h * u := by group
    have hC : (h : G) * h ∈ Subgroup.centralizer (pCoreOf 2 L2 : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun u hu => hsq ⟨u, hu⟩
    obtain ⟨k, hk⟩ := (hT.odd_card hf).of_dvd_nat (orderOf_dvd_natCard h)
    have hpow : (h : G) = ((h : G) * h) ^ (k + 1) := by
      have e : (h : G) ^ orderOf h = 1 := by
        rw [← Subgroup.orderOf_coe]
        exact pow_orderOf_eq_one _
      rw [hk] at e
      calc (h : G) = (h : G) ^ (2 * k + 1) * h := by rw [e, one_mul]
        _ = ((h : G) * h) ^ (k + 1) := by
          rw [← pow_two, ← pow_mul, ← pow_succ, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    have hhC : (h : G) ∈ Subgroup.centralizer (pCoreOf 2 L2 : Set G) := by
      rw [hpow]
      exact Subgroup.pow_mem _ hC _
    have hhQ : (h : G) ∈ pCoreOf 2 L2 := hcent ⟨Subgroup.mem_sup_right (hT.le_bigB h.2), hhC⟩
    have hbot : H₀ ⊓ pCoreOf 2 L2 = ⊥ := Subgroup.inf_eq_bot_of_coprime (by
      rw [hD.card_right]
      exact hT.coprime_two_pow hf _)
    have hmem : (h : G) ∈ H₀ ⊓ pCoreOf 2 L2 := ⟨h.2, hhQ⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcard : Nat.card Kˣ ≤ Nat.card ↥H₀ := by
    rw [Nat.card_units, c₂.card, hT.card, pow_mul]
    norm_num
  have hbij : Function.Bijective κ := hinj.bijective_of_nat_card_le hcard
  refine ⟨MonoidHom.mk' Af hAmul, MulEquiv.ofBijective κ hbij, fun h => (hAf h).1,
    fun h => (hAf h).2.1, fun h => (hAf h).2.2.1, fun h => rfl, fun h => (hAf h).2.2.2.1,
    fun h => (hAf h).2.2.2.2⟩

theorem U4qLocalData.exists_torusCoord (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (hT : U4qTorusData L1 L2 S H₀ f) {K : Type} [Field K]
    (c₂ : U4qCoordRight L1 L2 S f K) (hU : UnitaryFieldData 2 f K) :
    ∃ κ : ↥H₀ ≃* Kˣ,
      (∀ (h : ↥H₀) (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2)
          (hha : (h : G) * a * (h : G)⁻¹ ∈ L2),
        (c₂.α ⟨(h : G) * a * (h : G)⁻¹, hha⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
          (κ h : K) * (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1) ∧
      (∀ (h : ↥H₀) (x : G) (hx : x ∈ pCoreOf 2 L2)
          (hhx : (h : G) * x * (h : G)⁻¹ ∈ pCoreOf 2 L2), x ∈ pCoreOf 2 L1 →
        Multiplicative.toAdd (c₂.β ⟨(h : G) * x * (h : G)⁻¹, hhx⟩) 0 1 =
          (κ h : K) * Multiplicative.toAdd (c₂.β ⟨x, hx⟩) 0 1) ∧
      (∀ (h : ↥H₀) (z : G) (hz : z ∈ pCoreOf 2 L2)
          (hhz : (h : G) * z * (h : G)⁻¹ ∈ pCoreOf 2 L2), z ∈ centerOf (pCoreOf 2 L1) →
        Multiplicative.toAdd (c₂.β ⟨(h : G) * z * (h : G)⁻¹, hhz⟩) 0 0 =
          hU.norm (κ h : K) * Multiplicative.toAdd (c₂.β ⟨z, hz⟩) 0 0) ∧
      ∀ (h : ↥H₀) (s : G) (hs : s ∈ S) (hs' : s ∈ L2) (hhs : (h : G) * s * (h : G)⁻¹ ∈ L2),
        (c₂.α ⟨(h : G) * s * (h : G)⁻¹, hhs⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
          (κ h : K) * (c₂.α ⟨s, hs'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  obtain ⟨A, κ, -, hA10, hN, hκ, htw, hα⟩ := hD.exists_torusTwist hH hS hT c₂ hU
  have hA11 : ∀ h : ↥H₀, (A h : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro h h0
    have e := hN h
    rw [UnitaryFieldData.norm, h0, zero_mul] at e
    exact zero_ne_one e
  have hA00 : ∀ h : ↥H₀, (A h : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h
    have hdet : (A h : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    rw [Matrix.det_fin_two, hA10 h, mul_zero, sub_zero] at hdet
    exact left_ne_zero_of_mul hdet
  have hSκ : ∀ (h : ↥H₀) (s : G) (hs : s ∈ S) (hs' : s ∈ L2)
      (hhs : (h : G) * s * (h : G)⁻¹ ∈ L2),
      (c₂.α ⟨(h : G) * s * (h : G)⁻¹, hhs⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
        (κ h : K) * (c₂.α ⟨s, hs'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    intro h s hs hs' hhs
    obtain ⟨t, ht⟩ := (c₂.mem_iff ⟨s, hs'⟩).mp hs
    have hc := hα h s hs' hhs
    rw [ht] at hc ⊢
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA10 h, mul_zero, add_zero, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, mul_one] at e00 e01 ⊢
    have hM00 : (c₂.α ⟨(h : G) * s * (h : G)⁻¹, hhs⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 :=
      mul_right_cancel₀ (hA00 h) (e00.trans (one_mul _).symm)
    rw [hκ h, div_mul_eq_mul_div, eq_div_iff (hA11 h)]
    linear_combination e01 - (A h : Matrix (Fin 2) (Fin 2) K) 0 1 * hM00
  refine ⟨κ, fun h a ha ha' hha => hSκ h a (hH.pCoreOf_le_left ha) ha' hha, ?_, ?_, hSκ⟩
  ·
    intro h x hx hhx hx1
    have hX11 : Multiplicative.toAdd (c₂.β ⟨x, hx⟩) 1 1 = 0 := (c₂.mem_inf_iff ⟨x, hx⟩).mp hx1
    have hN' := hN h
    rw [UnitaryFieldData.norm] at hN'
    rw [htw h ⟨x, hx⟩ ⟨_, hhx⟩ rfl, mul_mul_map_bar_transpose_apply, hA10 h, hX11, hκ h]
    simp only [map_zero, mul_zero, zero_mul, add_zero, zero_add]
    rw [div_mul_eq_mul_div, eq_div_iff (hA11 h)]
    linear_combination ((A h : Matrix (Fin 2) (Fin 2) K) 0 0 *
      Multiplicative.toAdd (c₂.β ⟨x, hx⟩) 0 1) * hN'
  ·
    intro h z hz hhz hzZ
    obtain ⟨hX01, hX11⟩ := (c₂.mem_center_iff ⟨z, hz⟩).mp hzZ
    have hX10 : Multiplicative.toAdd (c₂.β ⟨z, hz⟩) 1 0 = 0 := by
      have hH' := congrFun (congrFun ((c₂.range_iff _).mp ⟨⟨z, hz⟩, rfl⟩) 0) 1
      simp only [Matrix.map_apply, Matrix.transpose_apply, hX01] at hH'
      rw [← hH']
      exact zero_pow (pow_ne_zero _ two_ne_zero)
    have hN' := hN h
    rw [UnitaryFieldData.norm] at hN'
    rw [htw h ⟨z, hz⟩ ⟨_, hhz⟩ rfl, mul_mul_map_bar_transpose_apply, hX01, hX10, hX11, hκ h]
    simp only [map_zero, mul_zero, zero_mul, add_zero, zero_add]
    rw [UnitaryFieldData.norm, map_div₀, div_mul_div_comm, hN', div_one]
    ring

theorem U4qLocalData.eq_one_of_torus_fixed (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (hT : U4qTorusData L1 L2 S H₀ f) (hf : 2 ≤ f) {x : G}
    (hx : x ∈ pCoreOf 2 L1) (hfix : ∀ h ∈ H₀, h * x * h⁻¹ = x) : x = 1 := by
  classical
  obtain ⟨K, hK, -, ⟨c₂⟩⟩ := hD.exists_coordRight hH hS
  letI := hK
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hD.one_le, c₂.card⟩
  haveI := hU.charP
  obtain ⟨κ, hQκ, hℓκ, hZκ, -⟩ := hD.exists_torusCoord hH hS hT c₂ hU
  obtain ⟨c, hcf, hc0, hc1⟩ := exists_fixed_ne_zero_ne_one_tor hU hf
  obtain ⟨h, hκh⟩ : ∃ h : ↥H₀, (κ h : K) = c :=
    ⟨κ.symm (Units.mk0 c hc0), by rw [MulEquiv.apply_symm_apply, Units.val_mk0]⟩
  have hfx : (h : G) * x * (h : G)⁻¹ = x := hfix h h.2
  have hxL2 : x ∈ L2 := hD.le_right hH hS (hH.pCoreOf_le_left hx)
  have hα1 := hQκ h x hx hxL2 (by rw [hfx]; exact hxL2)
  have hsubL : ∀ p, (⟨(h : G) * x * (h : G)⁻¹, p⟩ : ↥L2) = ⟨x, hxL2⟩ := fun p => Subtype.ext hfx
  rw [hsubL, hκh] at hα1
  obtain ⟨t, ht⟩ := (c₂.mem_iff ⟨x, hxL2⟩).mp (hH.pCoreOf_le_left hx)
  rw [ht] at hα1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at hα1
  have ht0 : t = 0 := by
    have e : (c - 1) * t = 0 := by linear_combination -hα1
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hc1)
  have hxQ2 : x ∈ pCoreOf 2 L2 := by
    refine (c₂.eq_one_iff ⟨x, hxL2⟩).mp (Subtype.ext ?_)
    rw [ht, ht0]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hX11 := (c₂.mem_inf_iff ⟨x, hxQ2⟩).mp hx
  have hsubQ : ∀ p, (⟨(h : G) * x * (h : G)⁻¹, p⟩ : ↥(pCoreOf 2 L2)) = ⟨x, hxQ2⟩ :=
    fun p => Subtype.ext hfx
  have hℓ := hℓκ h x hxQ2 (by rw [hfx]; exact hxQ2) hx
  rw [hsubQ, hκh] at hℓ
  have hX01 : Multiplicative.toAdd (c₂.β ⟨x, hxQ2⟩) 0 1 = 0 := by
    have e : (c - 1) * Multiplicative.toAdd (c₂.β ⟨x, hxQ2⟩) 0 1 = 0 := by
      linear_combination -hℓ
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hc1)
  have hxZ : x ∈ centerOf (pCoreOf 2 L1) := (c₂.mem_center_iff ⟨x, hxQ2⟩).mpr ⟨hX01, hX11⟩
  have hZ := hZκ h x hxQ2 (by rw [hfx]; exact hxQ2) hxZ
  rw [hsubQ, hκh, UnitaryFieldData.norm, hcf] at hZ
  have hN1 : c * c ≠ 1 := fun e => hc1 (CharTwo.sq_inj.mp (by rw [one_pow, sq]; exact e))
  have hX00 : Multiplicative.toAdd (c₂.β ⟨x, hxQ2⟩) 0 0 = 0 := by
    have e : (c * c - 1) * Multiplicative.toAdd (c₂.β ⟨x, hxQ2⟩) 0 0 = 0 := by
      linear_combination -hZ
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hN1)
  have hX10 : Multiplicative.toAdd (c₂.β ⟨x, hxQ2⟩) 1 0 = 0 := by
    have hH' := congrFun (congrFun ((c₂.range_iff _).mp ⟨⟨x, hxQ2⟩, rfl⟩) 0) 1
    simp only [Matrix.map_apply, Matrix.transpose_apply, hX01] at hH'
    rw [← hH']
    exact zero_pow (pow_ne_zero _ two_ne_zero)
  have hβ : c₂.β ⟨x, hxQ2⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    ext i j
    fin_cases i <;> fin_cases j
    · exact hX00
    · exact hX01
    · exact hX10
    · exact hX11
  exact congrArg Subtype.val (c₂.injective_β (hβ.trans (map_one c₂.β).symm))

theorem U4qLocalData.pCoreOf_inf_centralizer_torus (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) (hf : 2 ≤ f) :
    pCoreOf 2 L1 ⊓ Subgroup.centralizer (H₀ : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxC⟩
  refine hD.eq_one_of_torus_fixed hH hS hT hf hx fun h hh => ?_
  rw [Subgroup.mem_centralizer_iff.mp hxC h hh, mul_inv_cancel_right]

theorem U4qLocalData.phi_conj_of_torus (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (hT : U4qTorusData L1 L2 S H₀ f) {F K : Type} [Field F]
    [Field K] (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K)
    {φ : (Fin 2 → F) → K}
    (hφ : ∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2),
      φ (Multiplicative.toAdd (c₁.β ⟨a, ha⟩) 1) = (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
    {h : G} (hh : h ∈ H₀) {c : K}
    (hc : ∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2) (hha : h * a * h⁻¹ ∈ L2),
      (c₂.α ⟨h * a * h⁻¹, hha⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
        c * (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
    (u : G) (hu : u ∈ pCoreOf 2 L1) (hhu : h * u * h⁻¹ ∈ pCoreOf 2 L1) (i : Fin 2) :
    φ (Multiplicative.toAdd (c₁.β ⟨h * u * h⁻¹, hhu⟩) i) =
      c * φ (Multiplicative.toAdd (c₁.β ⟨u, hu⟩) i) := by
  obtain ⟨M, hM⟩ := hT.exists_mul_beta c₁ hh
  have hQ1L2 : ∀ {a : G}, a ∈ pCoreOf 2 L1 → a ∈ L2 := fun ha =>
    hD.le_right hH hS (hH.pCoreOf_le_left ha)
  have hN : h ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) := hT.le_normalizer_pCoreOf_left hh
  have key : ∀ v : Fin 2 → F, φ (v ᵥ* M) = c * φ v := by
    intro v
    obtain ⟨a, ha⟩ := c₁.surjective_β (Multiplicative.ofAdd (Matrix.of ![0, v]))
    have hrow : Multiplicative.toAdd (c₁.β ⟨(a : G), a.2⟩) 1 = v := by
      change Multiplicative.toAdd (c₁.β a) 1 = v
      rw [ha]
      rfl
    have hha : h * (a : G) * h⁻¹ ∈ pCoreOf 2 L1 := (Subgroup.mem_normalizer_iff.mp hN a).mp a.2
    have e := hφ (h * (a : G) * h⁻¹) hha (hQ1L2 hha)
    rw [hM a a.2 hha, hc a a.2 (hQ1L2 a.2) (hQ1L2 hha), ← hφ a a.2 (hQ1L2 a.2),
      Matrix.mul_apply_eq_vecMul, hrow] at e
    exact e
  rw [hM u hu hhu, Matrix.mul_apply_eq_vecMul, key]

theorem U4qLocalData.sup_inf_centralizer_torus (hD : U4qLocalData L1 L2 S f)
    (hT : U4qTorusData L1 L2 S H₀ f) :
    pCoreOf 2 L1 ⊔ (L1 ⊓ Subgroup.centralizer (H₀ : Set G)) = L1 :=
  sup_inf_centralizer_eq_of_coprime (pCoreOf_le 2 L1) (le_normalizer_pCoreOf 2 L1)
    hT.le_normalizer_pCoreOf_left (by rw [hD.card_left]; exact hT.coprime_two_pow hD.one_le _)
    hT.conj_mem

theorem U4qLocalData.inf_centralizer_torus_inf_eq_bot (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) (hf : 2 ≤ f) :
    L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊓ pCoreOf 2 L1 = ⊥ :=
  inf_centralizer_inf_eq_bot_of_fixed fun _ hx hfix =>
    hD.eq_one_of_torus_fixed hH hS hT hf hx hfix

theorem U4qCoordLeft.bijective_torusCompl {F : Type} [Field F] (c₁ : U4qCoordLeft L1 L2 S f F)
    (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) (hf : 2 ≤ f) :
    Function.Bijective (c₁.α.comp (Subgroup.inclusion
      (inf_le_left : L1 ⊓ Subgroup.centralizer (H₀ : Set G) ≤ L1))) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro k hk
    have hkQ : (k : G) ∈ pCoreOf 2 L1 := (c₁.eq_one_iff _).mp hk
    have hmem : (k : G) ∈ L1 ⊓ Subgroup.centralizer (H₀ : Set G) ⊓ pCoreOf 2 L1 := ⟨k.2, hkQ⟩
    rw [hD.inf_centralizer_torus_inf_eq_bot hH hS hT hf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  · intro M
    obtain ⟨l, rfl⟩ := c₁.surjective_α M
    obtain ⟨q, hq, k, hk, hlqk⟩ := exists_mul_mem_inf_centralizer_of_coprime (pCoreOf_le 2 L1)
      (le_normalizer_pCoreOf 2 L1) hT.le_normalizer_pCoreOf_left
      (by rw [hD.card_left]; exact hT.coprime_two_pow hD.one_le _) hT.conj_mem l.2
    refine ⟨⟨k, hk⟩, ?_⟩
    have hl : l = ⟨q, pCoreOf_le 2 L1 hq⟩ * ⟨k, hk.1⟩ := Subtype.ext hlqk
    rw [hl, map_mul, (c₁.eq_one_iff _).mpr hq, one_mul]
    rfl

@[expose] noncomputable def U4qCoordLeft.torusComplEquiv {F : Type} [Field F]
    (c₁ : U4qCoordLeft L1 L2 S f F) (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (hT : U4qTorusData L1 L2 S H₀ f) (hf : 2 ≤ f) :
    ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G)) ≃* SL(2, F) :=
  MulEquiv.ofBijective _ (c₁.bijective_torusCompl hH hD hS hT hf)

theorem U4qCoordLeft.torusComplEquiv_apply {F : Type} [Field F]
    (c₁ : U4qCoordLeft L1 L2 S f F) (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (hT : U4qTorusData L1 L2 S H₀ f) (hf : 2 ≤ f)
    (k : ↥(L1 ⊓ Subgroup.centralizer (H₀ : Set G))) :
    c₁.torusComplEquiv hH hD hS hT hf k = c₁.α ⟨k, k.2.1⟩ :=
  rfl

theorem U4qLocalData.inf_inf_centralizer_torus_le (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (hT : U4qTorusData L1 L2 S H₀ f) :
    S ⊓ (L1 ⊓ Subgroup.centralizer (H₀ : Set G)) ≤ pCoreOf 2 L2 := by
  classical
  rintro s ⟨hsS, -, hsC⟩
  obtain ⟨K, hK, -, ⟨c₂⟩⟩ := hD.exists_coordRight hH hS
  letI := hK
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hD.one_le, c₂.card⟩
  obtain ⟨κ, -, -, -, hSκ⟩ := hD.exists_torusCoord hH hS hT c₂ hU
  obtain ⟨c, hc⟩ := hU.exists_bar_ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (map_zero _)
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hc (map_one _)
  obtain ⟨h, hκh⟩ : ∃ h : ↥H₀, (κ h : K) = c :=
    ⟨κ.symm (Units.mk0 c hc0), by rw [MulEquiv.apply_symm_apply, Units.val_mk0]⟩
  have hsL2 : s ∈ L2 := hD.le_right hH hS hsS
  have hfix : (h : G) * s * (h : G)⁻¹ = s := by
    rw [(Subgroup.mem_centralizer_iff.mp hsC (h : G) h.2), mul_inv_cancel_right]
  have e := hSκ h s hsS hsL2 (by rw [hfix]; exact hsL2)
  have hsub : ∀ p, (⟨(h : G) * s * (h : G)⁻¹, p⟩ : ↥L2) = ⟨s, hsL2⟩ := fun p => Subtype.ext hfix
  rw [hsub, hκh] at e
  obtain ⟨t, ht⟩ := (c₂.mem_iff ⟨s, hsL2⟩).mp hsS
  rw [ht] at e
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at e
  have ht0 : t = 0 := by
    have e' : (c - 1) * t = 0 := by linear_combination -e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hc1)
  refine (c₂.eq_one_iff ⟨s, hsL2⟩).mp (Subtype.ext ?_)
  rw [ht, ht0]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Vertex

end CFSG.Quasithin.F112R.St84

end
