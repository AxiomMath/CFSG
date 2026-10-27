module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.StandardType.FS81.L3TwoFixedPointFree
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.GroupTheory.ClosurePairInvert
public import Mathlib.Tactic.Group
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open scoped commutatorElement

variable {X : Type} [Group X]

private structure Fs81CentData (X : Type) [Group X] where
  Y : Subgroup X
  H : Subgroup X
  Q : Subgroup X
  S : Subgroup X
  K : Subgroup X
  P : Subgroup X
  t₀ : X
  σ : X
  b : X
  k : X
  b₁ : X
  hQH : Q ≤ H
  hHnorm : H ≤ Subgroup.normalizer (Q : Set X)
  hQ2 : IsPGroup 2 Q
  hHcent : H ⊓ Subgroup.centralizer (Q : Set X) ≤ Q
  ht₀Q : t₀ ∈ Q
  ht₀cent : ∀ h ∈ H, h * t₀ = t₀ * h
  hQQ : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ⁅q₁, q₂⁆ ∈ Subgroup.zpowers t₀
  hσH : σ ∈ H
  hSH : S ≤ H
  hS2 : IsPGroup 2 S
  hSσ : ∀ s ∈ S, s * σ = σ * s
  hSWs : ∀ s ∈ S, ∀ w ∈ fs81CommSet Q σ, ⁅s, w⁆ ∈ Subgroup.zpowers t₀
  hSq : ∀ s ∈ S, ∀ q ∈ Q, ⁅⁅s, q⁆, σ⁆ ∈ Subgroup.zpowers t₀
  hSc : ∀ s ∈ S, ∀ c ∈ Q, ⁅c, σ⁆ ∈ Subgroup.zpowers t₀ →
    ⁅s, c⁆ ∈ fs81SigmaW Q σ t₀
  hKH : K ≤ H
  hKSnorm : K ≤ Subgroup.normalizer (S : Set X)
  hKσ : ∀ x ∈ K, x * σ = σ * x
  hKWs : ∀ x ∈ K, ∀ w ∈ fs81CommSet Q σ, ⁅x, w⁆ ∈ Subgroup.zpowers t₀
  hbK : b ∈ K
  hkK : k ∈ K
  hb3 : orderOf b = 3
  hk2 : orderOf k = 2
  hkb : k * b * k⁻¹ = b⁻¹
  hKcl : K ≤ Subgroup.closure ({b, k} : Set X)
  hPH : P ≤ H
  hPiso : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  hPσ : ∀ p ∈ P, p * σ = σ * p
  hPk : ∀ p ∈ P, p * k = k * p
  hPSnorm : P ≤ Subgroup.normalizer (S : Set X)
  hb₁P : b₁ ∈ P
  hb₁3 : orderOf b₁ = 3
  hbY : Subgroup.centralizer ({b} : Set X) ≤ Y
  hb₁Y : Subgroup.centralizer ({b₁} : Set X) ≤ Y
  hlast : ∀ h ∈ H ⊓ Y, ⁅h, σ⁆ ∈ Q →
    (∀ w ∈ fs81CommSet Q σ, ⁅h, w⁆ ∈ Subgroup.zpowers t₀) → h ∈ Q ⊔ S ⊔ K

private theorem conj_eq_self_of_mem_central {H Z : Subgroup X}
    (hZ : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) {z : X} (hz : z ∈ Z)
    {h : X} (hh : h ∈ H) : h * z * h⁻¹ = z := by
  rw [← hZ z hz h hh]
  group

private theorem commutatorElement_mul_right_mem_of_central {H Z : Subgroup X}
    (hZ : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) {x y₁ y₂ : X}
    (hy₁ : y₁ ∈ H) (hy₂ : y₂ ∈ H) (h₁ : ⁅x, y₁⁆ ∈ Z) (h₂ : ⁅x, y₂⁆ ∈ Z) :
    ⁅x, y₁ * y₂⁆ ∈ Z := by
  have heq : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * ⁅x, y₂⁆ := by
    calc ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
          rw [commutatorElement_mul_right_eq_mul_conj]; group
      _ = ⁅x, y₁⁆ * ⁅x, y₂⁆ := by rw [conj_eq_self_of_mem_central hZ h₂ hy₁]
  rw [heq]
  exact Z.mul_mem h₁ h₂

private theorem commutatorElement_inv_right_mem_of_central {H Z : Subgroup X}
    (hZ : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) {x y : X}
    (hy : y ∈ H) (hxy : ⁅x, y⁆ ∈ Z) : ⁅x, y⁻¹⁆ ∈ Z := by
  have heq : ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
    calc ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
          rw [commutatorElement_inv_right, ← commutatorElement_inv]
      _ = ⁅x, y⁆⁻¹ := by
          simpa using conj_eq_self_of_mem_central hZ (Z.inv_mem hxy) (H.inv_mem hy)
  rw [heq]
  exact Z.inv_mem hxy

private theorem commutatorElement_mem_closure_of_central {H Z : Subgroup X}
    (hZ : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) {Xs : Set X} (hXs : Xs ⊆ H)
    {x : X} (hx : x ∈ H) (hgen : ∀ w ∈ Xs, ⁅x, w⁆ ∈ Z) :
    ∀ w ∈ Subgroup.closure Xs, ⁅x, w⁆ ∈ Z := by
  let K : Subgroup X :=
    { carrier := {w | w ∈ H ∧ ⁅x, w⁆ ∈ Z}
      one_mem' := ⟨H.one_mem, by rw [commutatorElement_one_right]; exact Z.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        exact ⟨H.mul_mem haH hbH,
          commutatorElement_mul_right_mem_of_central hZ haH hbH ha hb⟩
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        exact ⟨H.inv_mem haH,
          commutatorElement_inv_right_mem_of_central hZ haH ha⟩ }
  have hle : Subgroup.closure Xs ≤ K := by
    rw [Subgroup.closure_le]
    intro w hw
    exact ⟨hXs hw, hgen w hw⟩
  intro w hw
  exact (hle hw).2

private theorem commutatorElement_conj_left (c m w : X) :
    ⁅c * m * c⁻¹, w⁆ = c * ⁅m, c⁻¹ * w * c⁆ * c⁻¹ := by
  have h' : c⁻¹ * ⁅c * m * c⁻¹, w⁆ * c = ⁅m, c⁻¹ * w * c⁆ := by
    calc c⁻¹ * ⁅c * m * c⁻¹, w⁆ * c
        = ⁅c⁻¹ * (c * m * c⁻¹) * c, c⁻¹ * w * c⁆ := by
          simpa using (conjugate_commutatorElement (g₁ := c * m * c⁻¹) (g₂ := w)
            (g₃ := c⁻¹))
      _ = ⁅m, c⁻¹ * w * c⁆ := by rw [show c⁻¹ * (c * m * c⁻¹) * c = m by group]
  calc ⁅c * m * c⁻¹, w⁆ = c * (c⁻¹ * ⁅c * m * c⁻¹, w⁆ * c) * c⁻¹ := by group
    _ = c * ⁅m, c⁻¹ * w * c⁆ * c⁻¹ := by rw [h']

private theorem conj_involution_mul_eq {b k : X} (hb3 : orderOf b = 3) (hk2 : orderOf k = 2)
    (hkb : k * b * k⁻¹ = b⁻¹) (m : ℤ) :
    (b ^ m * k) * (b * (b ^ m * k) * b⁻¹) = b := by
  have hkinv : k⁻¹ = k := inv_eq_self_of_orderOf_eq_two hk2
  have hk2pow : k * k = 1 := by
    have := pow_orderOf_eq_one k
    rwa [hk2, pow_two] at this
  have hkb' : k * b * k = b⁻¹ := by rwa [hkinv] at hkb
  have hkbk : k * b⁻¹ = b * k := by
    have h1 : k * b⁻¹ * k = b := by
      calc k * b⁻¹ * k = (k * b * k)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, hkinv]
            group
        _ = (b⁻¹)⁻¹ := by rw [hkb']
        _ = b := by group
    calc k * b⁻¹ = (k * b⁻¹) * 1 := by rw [mul_one]
      _ = (k * b⁻¹) * (k * k) := by rw [hk2pow]
      _ = (k * b⁻¹ * k) * k := by group
      _ = b * k := by rw [h1]
  have hbpow : b * b ^ m = b ^ (m + 1) := by
    calc b * b ^ m = b ^ (1 : ℤ) * b ^ m := by rw [zpow_one]
      _ = b ^ ((1 : ℤ) + m) := (zpow_add b 1 m).symm
      _ = b ^ (m + 1) := by congr 1; ring
  have hbpow2 : b ^ (m + 1) * b = b ^ (m + 2) := by
    calc b ^ (m + 1) * b = b ^ (m + 1) * b ^ (1 : ℤ) := by rw [zpow_one]
      _ = b ^ ((m + 1) + 1) := (zpow_add b (m + 1) 1).symm
      _ = b ^ (m + 2) := by congr 1; ring
  have hstep : b * (b ^ m * k) * b⁻¹ = b ^ (m + 2) * k := by
    calc b * (b ^ m * k) * b⁻¹ = (b * b ^ m) * (k * b⁻¹) := by group
      _ = b ^ (m + 1) * (b * k) := by rw [hbpow, hkbk]
      _ = b ^ (m + 2) * k := by rw [← mul_assoc, hbpow2]
  have hconj : k * b ^ (m + 2) * k = b ^ (-(m + 2)) := by
    calc k * b ^ (m + 2) * k = k * b ^ (m + 2) * k⁻¹ := by rw [hkinv]
      _ = (b ^ (m + 2))⁻¹ := by rw [← conj_zpow, hkb, inv_zpow]
      _ = b ^ (-(m + 2)) := by rw [zpow_neg]
  have hb3z : b ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simpa [hb3] using pow_orderOf_eq_one b
  calc (b ^ m * k) * (b * (b ^ m * k) * b⁻¹)
      = (b ^ m * k) * (b ^ (m + 2) * k) := by rw [hstep]
    _ = b ^ m * (k * b ^ (m + 2) * k) := by group
    _ = b ^ m * b ^ (-(m + 2)) := by rw [hconj]
    _ = b ^ (m + -(m + 2)) := by rw [← zpow_add]
    _ = b := by
        rw [show m + -(m + 2) = (-2 : ℤ) by ring]
        calc b ^ (-2 : ℤ) = b ^ (-2 : ℤ) * b ^ (3 : ℤ) := by rw [hb3z, mul_one]
          _ = b ^ (-2 + 3 : ℤ) := by rw [← zpow_add]
          _ = b := by norm_num

private def fs81C0 (H Q Z : Subgroup X) (σ : X)
    (hQH : Q ≤ H) (hZcent : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) : Subgroup X :=
  { carrier := {c | c ∈ Q ∧ ⁅c, σ⁆ ∈ Z}
    one_mem' := ⟨Q.one_mem, by rw [commutatorElement_one_left]; exact Z.one_mem⟩
    mul_mem' := by
      rintro a b ⟨haQ, ha⟩ ⟨hbQ, hb⟩
      refine ⟨Q.mul_mem haQ hbQ, ?_⟩
      have hconj : a * ⁅b, σ⁆ * a⁻¹ = ⁅b, σ⁆ :=
        conj_eq_self_of_mem_central hZcent hb (hQH haQ)
      rw [commutatorElement_mul_left_eq_conj_mul, hconj]
      exact Z.mul_mem hb ha
    inv_mem' := by
      rintro a ⟨haQ, ha⟩
      refine ⟨Q.inv_mem haQ, ?_⟩
      have hconj : a⁻¹ * ⁅a, σ⁆⁻¹ * a = ⁅a, σ⁆⁻¹ := by
        simpa using conj_eq_self_of_mem_central hZcent (Z.inv_mem ha) (hQH (Q.inv_mem haQ))
      rw [commutatorElement_inv_left, ← commutatorElement_inv, hconj]
      exact Z.inv_mem ha }

private def fs81C (H Q : Subgroup X) (σ : X)
    (hHnorm : H ≤ Subgroup.normalizer (Q : Set X)) : Subgroup X :=
  { carrier := {h | h ∈ H ∧ ⁅h, σ⁆ ∈ Q}
    one_mem' := ⟨H.one_mem, by rw [commutatorElement_one_left]; exact Q.one_mem⟩
    mul_mem' := by
      rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
      refine ⟨H.mul_mem haH hbH, ?_⟩
      have hconj : a * ⁅b, σ⁆ * a⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hHnorm haH) ⁅b, σ⁆).mp hb
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Q.mul_mem hconj ha
    inv_mem' := by
      rintro a ⟨haH, ha⟩
      refine ⟨H.inv_mem haH, ?_⟩
      rw [commutatorElement_inv_left, ← commutatorElement_inv]
      simpa using (Subgroup.mem_normalizer_iff.mp (hHnorm (H.inv_mem haH)) ⁅a, σ⁆⁻¹).mp
        (Q.inv_mem ha) }

private def fs81M (H Q : Subgroup X) (σ : X) (W Z : Subgroup X)
    (hHnorm : H ≤ Subgroup.normalizer (Q : Set X))
    (hZcent : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) : Subgroup X :=
  { carrier := {h | h ∈ H ∧ ⁅h, σ⁆ ∈ Q ∧ ∀ w ∈ W, ⁅h, w⁆ ∈ Z}
    one_mem' := ⟨H.one_mem, by rw [commutatorElement_one_left]; exact Q.one_mem,
      by intro w _; rw [commutatorElement_one_left]; exact Z.one_mem⟩
    mul_mem' := by
      rintro a b ⟨haH, haQ, haW⟩ ⟨hbH, hbQ, hbW⟩
      refine ⟨H.mul_mem haH hbH, ?_, ?_⟩
      · have hconj : a * ⁅b, σ⁆ * a⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hHnorm haH) ⁅b, σ⁆).mp hbQ
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact Q.mul_mem hconj haQ
      · intro w hw
        have hconj : a * ⁅b, w⁆ * a⁻¹ = ⁅b, w⁆ :=
          conj_eq_self_of_mem_central hZcent (hbW w hw) haH
        rw [commutatorElement_mul_left_eq_conj_mul, hconj]
        exact Z.mul_mem (hbW w hw) (haW w hw)
    inv_mem' := by
      rintro a ⟨haH, haQ, haW⟩
      refine ⟨H.inv_mem haH, ?_, ?_⟩
      · rw [commutatorElement_inv_left, ← commutatorElement_inv]
        simpa using (Subgroup.mem_normalizer_iff.mp (hHnorm (H.inv_mem haH)) ⁅a, σ⁆⁻¹).mp
          (Q.inv_mem haQ)
      · intro w hw
        have hconj : a⁻¹ * ⁅a, w⁆⁻¹ * a = ⁅a, w⁆⁻¹ := by
          simpa using conj_eq_self_of_mem_central hZcent (Z.inv_mem (haW w hw)) (H.inv_mem haH)
        rw [commutatorElement_inv_left, ← commutatorElement_inv, hconj]
        exact Z.inv_mem (haW w hw) }

private def fs81N (C C0 M W Q : Subgroup X)
    (hCnormC0 : C ≤ Subgroup.normalizer C0) (hCnormW : C ≤ Subgroup.normalizer W)
    (hMC : M ≤ C) : Subgroup X :=
  { carrier := {h | h ∈ M ∧ (∀ q ∈ Q, ⁅h, q⁆ ∈ C0) ∧ ∀ c ∈ C0, ⁅h, c⁆ ∈ W}
    one_mem' := ⟨M.one_mem, by intro q _; rw [commutatorElement_one_left]; exact C0.one_mem,
      by intro c _; rw [commutatorElement_one_left]; exact W.one_mem⟩
    mul_mem' := by
      rintro a b ⟨haM, haQ, haC⟩ ⟨hbM, hbQ, hbC⟩
      refine ⟨M.mul_mem haM hbM, ?_, ?_⟩
      · intro q hq
        have hconj : a * ⁅b, q⁆ * a⁻¹ ∈ C0 :=
          (Subgroup.le_normalizer_iff.mp hCnormC0) a (hMC haM) ⁅b, q⁆ (hbQ q hq)
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact C0.mul_mem hconj (haQ q hq)
      · intro c hc
        have hconj : a * ⁅b, c⁆ * a⁻¹ ∈ W :=
          (Subgroup.le_normalizer_iff.mp hCnormW) a (hMC haM) ⁅b, c⁆ (hbC c hc)
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact W.mul_mem hconj (haC c hc)
    inv_mem' := by
      rintro a ⟨haM, haQ, haC⟩
      refine ⟨M.inv_mem haM, ?_, ?_⟩
      · intro q hq
        rw [commutatorElement_inv_left, ← commutatorElement_inv]
        simpa using (Subgroup.le_normalizer_iff.mp hCnormC0) a⁻¹ (hMC (M.inv_mem haM))
          ⁅a, q⁆⁻¹ (C0.inv_mem (haQ q hq))
      · intro c hc
        rw [commutatorElement_inv_left, ← commutatorElement_inv]
        simpa using (Subgroup.le_normalizer_iff.mp hCnormW) a⁻¹ (hMC (M.inv_mem haM))
          ⁅a, c⁆⁻¹ (W.inv_mem (haC c hc)) }

namespace Fs81CentData

private theorem k_sq (D : Fs81CentData X) : D.k * D.k = 1 := by
  rw [← pow_two, ← D.hk2]
  exact pow_orderOf_eq_one D.k

private theorem b_sq_ne_one (D : Fs81CentData X) : D.b ^ 2 ≠ 1 := by
  intro h
  have hdvd : orderOf D.b ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rw [D.hb3] at hdvd
  norm_num at hdvd

private def Z (D : Fs81CentData X) : Subgroup X := Subgroup.zpowers D.t₀

private def W (D : Fs81CentData X) : Subgroup X := fs81SigmaW D.Q D.σ D.t₀

private theorem zcentral (D : Fs81CentData X) :
    ∀ z ∈ D.Z, ∀ h ∈ D.H, z * h = h * z := by
  intro z hz h hh
  have hle : Subgroup.zpowers D.t₀ ≤ Subgroup.centralizer (D.H : Set X) :=
    Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh'
      exact D.ht₀cent h' hh')
  have hzc : z ∈ Subgroup.centralizer (D.H : Set X) := hle hz
  rw [Subgroup.mem_centralizer_iff] at hzc
  exact (hzc h hh).symm

private def C0 (D : Fs81CentData X) : Subgroup X :=
  fs81C0 D.H D.Q D.Z D.σ D.hQH D.zcentral

private def C (D : Fs81CentData X) : Subgroup X :=
  fs81C D.H D.Q D.σ D.hHnorm

private def M (D : Fs81CentData X) : Subgroup X :=
  fs81M D.H D.Q D.σ D.W D.Z D.hHnorm D.zcentral

private theorem Z_le_Q (D : Fs81CentData X) : D.Z ≤ D.Q := by
  intro z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact D.Q.zpow_mem D.ht₀Q n

private theorem Q_commutator_mem (D : Fs81CentData X) :
    ∀ q ∈ D.Q, ⁅q, D.σ⁆ ∈ D.Q := by
  intro q hq
  have h := (Subgroup.mem_normalizer_iff.mp (D.hHnorm D.hσH) q).mp hq
  rw [show ⁅q, D.σ⁆ = q * (D.σ * q * D.σ⁻¹)⁻¹ by
    simp only [commutatorElement_def]; group]
  exact D.Q.mul_mem hq (D.Q.inv_mem h)

private theorem Ws_subset_Q (D : Fs81CentData X) :
    fs81CommSet D.Q D.σ ⊆ D.Q := by
  rintro w ⟨q, hq, rfl⟩
  exact D.Q_commutator_mem q hq

private theorem Ws_subset_W (D : Fs81CentData X) :
    fs81CommSet D.Q D.σ ⊆ D.W := by
  intro w hw
  change w ∈ Subgroup.closure (fs81CommSet D.Q D.σ) ⊔ Subgroup.zpowers D.t₀
  exact Subgroup.mem_sup_left (Subgroup.subset_closure hw)

private theorem Z_le_W (D : Fs81CentData X) : D.Z ≤ D.W := by
  intro z hz
  change z ∈ Subgroup.closure (fs81CommSet D.Q D.σ) ⊔ Subgroup.zpowers D.t₀
  exact Subgroup.mem_sup_right hz

private theorem Ws_subset_H (D : Fs81CentData X) :
    fs81CommSet D.Q D.σ ⊆ D.H :=
  fun _ hw => D.hQH (D.Ws_subset_Q hw)

private theorem closure_Ws_le_H (D : Fs81CentData X) :
    Subgroup.closure (fs81CommSet D.Q D.σ) ≤ D.H := by
  rw [Subgroup.closure_le]
  exact D.Ws_subset_H

private theorem Z_le_normalizer_Ws (D : Fs81CentData X) :
    D.Z ≤ Subgroup.normalizer
      (Subgroup.closure (fs81CommSet D.Q D.σ) : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro z hz a ha
  have hconj : z * a * z⁻¹ = a := by
    rw [D.zcentral z hz a (D.closure_Ws_le_H ha)]
    group
  rw [hconj]
  exact ha

private theorem C0_le_Q (D : Fs81CentData X) : D.C0 ≤ D.Q := fun _ hc => hc.1

private theorem Z_le_C0 (D : Fs81CentData X) : D.Z ≤ D.C0 := by
  intro z hz
  refine ⟨D.Z_le_Q hz, ?_⟩
  have hzσ : ⁅z, D.σ⁆ = 1 := by
    rw [commutatorElement_def, D.zcentral z hz D.σ D.hσH]
    group
  rw [hzσ]
  exact D.Z.one_mem

private theorem C_le_H (D : Fs81CentData X) : D.C ≤ D.H := fun _ hc => hc.1

private theorem C_commutator_mem (D : Fs81CentData X) :
    ∀ c ∈ D.C, ⁅c, D.σ⁆ ∈ D.Q := fun _ hc => hc.2

private theorem M_le_H (D : Fs81CentData X) : D.M ≤ D.H := fun _ hm => hm.1

private theorem M_commutator_mem (D : Fs81CentData X) :
    ∀ m ∈ D.M, ⁅m, D.σ⁆ ∈ D.Q := fun _ hm => hm.2.1

private theorem M_commutator_W (D : Fs81CentData X) :
    ∀ m ∈ D.M, ∀ w ∈ D.W, ⁅m, w⁆ ∈ D.Z := fun _ hm => hm.2.2

private theorem M_le_C (D : Fs81CentData X) : D.M ≤ D.C :=
  fun _ hm => ⟨hm.1, hm.2.1⟩

private theorem C_le_normalizer_C0 (D : Fs81CentData X) :
    D.C ≤ Subgroup.normalizer D.C0 := by
  rw [Subgroup.le_normalizer_iff]
  intro c hc x hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp (D.hHnorm (D.C_le_H hc)) x).mp hx.1, ?_⟩
  have huQ : ⁅c⁻¹, D.σ⁆ ∈ D.Q := by
    have h : c⁻¹ * ⁅c, D.σ⁆⁻¹ * c ∈ D.Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (D.hHnorm (D.C.inv_mem hc).1) ⁅c, D.σ⁆⁻¹).mp
        (D.Q.inv_mem (D.C_commutator_mem c hc))
    rwa [commutatorElement_inv_left, ← commutatorElement_inv]
  have hxu : ⁅x, ⁅c⁻¹, D.σ⁆⁆ ∈ D.Z := D.hQQ x hx.1 ⁅c⁻¹, D.σ⁆ huQ
  have hxσ : ⁅x, D.σ⁆ ∈ D.Z := hx.2
  have hmul : ⁅x, ⁅c⁻¹, D.σ⁆ * D.σ⁆ = ⁅x, ⁅c⁻¹, D.σ⁆⁆ * ⁅x, D.σ⁆ := by
    calc ⁅x, ⁅c⁻¹, D.σ⁆ * D.σ⁆ =
        ⁅x, ⁅c⁻¹, D.σ⁆⁆ * ⁅c⁻¹, D.σ⁆ * ⁅x, D.σ⁆ * ⁅c⁻¹, D.σ⁆⁻¹ := by
          rw [commutatorElement_mul_right_eq_mul_conj]
      _ = ⁅x, ⁅c⁻¹, D.σ⁆⁆ * (⁅c⁻¹, D.σ⁆ * ⁅x, D.σ⁆ * ⁅c⁻¹, D.σ⁆⁻¹) := by group
      _ = ⁅x, ⁅c⁻¹, D.σ⁆⁆ * ⁅x, D.σ⁆ := by
          rw [conj_eq_self_of_mem_central D.zcentral hxσ (D.hQH huQ)]
  have hinv : c⁻¹ * D.σ * c = ⁅c⁻¹, D.σ⁆ * D.σ := by
    simpa [MulAut.conj_apply] using
      (conj_eq_commutatorElement_mul (g₁ := c⁻¹) (g₂ := D.σ))
  rw [commutatorElement_conj_left, hinv, hmul]
  rw [conj_eq_self_of_mem_central D.zcentral (D.Z.mul_mem hxu hxσ) (D.C_le_H hc)]
  exact D.Z.mul_mem hxu hxσ

private theorem C_conj_commSet_mem_W (D : Fs81CentData X) :
    ∀ c ∈ D.C, ∀ q ∈ D.Q, c * ⁅q, D.σ⁆ * c⁻¹ ∈ D.W := by
  intro c hc q hq
  have hq' : c * q * c⁻¹ ∈ D.Q :=
    (Subgroup.mem_normalizer_iff.mp (D.hHnorm (D.C_le_H hc)) q).mp hq
  have huQ : ⁅c, D.σ⁆ ∈ D.Q := D.C_commutator_mem c hc
  have hcσ : c * D.σ * c⁻¹ = ⁅c, D.σ⁆ * D.σ := by
    rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
  have hq'σ : ⁅c * q * c⁻¹, D.σ⁆ ∈ fs81CommSet D.Q D.σ := ⟨c * q * c⁻¹, hq', rfl⟩
  have hzu : ⁅c * q * c⁻¹, ⁅c, D.σ⁆⁆ ∈ D.Z := D.hQQ _ hq' _ huQ
  have hzv : ⁅⁅c, D.σ⁆, ⁅c * q * c⁻¹, D.σ⁆⁆ ∈ D.Z :=
    D.hQQ _ huQ _ (D.Ws_subset_Q hq'σ)
  have hinner : ⁅c, D.σ⁆ * ⁅c * q * c⁻¹, D.σ⁆ * ⁅c, D.σ⁆⁻¹ =
      ⁅⁅c, D.σ⁆, ⁅c * q * c⁻¹, D.σ⁆⁆ * ⁅c * q * c⁻¹, D.σ⁆ := by
    rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
  have heq : c * ⁅q, D.σ⁆ * c⁻¹ =
      (⁅c * q * c⁻¹, ⁅c, D.σ⁆⁆ * ⁅⁅c, D.σ⁆, ⁅c * q * c⁻¹, D.σ⁆⁆) *
        ⁅c * q * c⁻¹, D.σ⁆ := by
    calc c * ⁅q, D.σ⁆ * c⁻¹ = ⁅c * q * c⁻¹, c * D.σ * c⁻¹⁆ :=
          conjugate_commutatorElement (g₁ := q) (g₂ := D.σ) (g₃ := c)
      _ = ⁅c * q * c⁻¹, ⁅c, D.σ⁆ * D.σ⁆ := by rw [hcσ]
      _ = ⁅c * q * c⁻¹, ⁅c, D.σ⁆⁆ * ⁅c, D.σ⁆ * ⁅c * q * c⁻¹, D.σ⁆ *
            ⁅c, D.σ⁆⁻¹ := by
            rw [commutatorElement_mul_right_eq_mul_conj]
      _ = ⁅c * q * c⁻¹, ⁅c, D.σ⁆⁆ *
            (⁅c, D.σ⁆ * ⁅c * q * c⁻¹, D.σ⁆ * ⁅c, D.σ⁆⁻¹) := by group
      _ = ⁅c * q * c⁻¹, ⁅c, D.σ⁆⁆ *
            (⁅⁅c, D.σ⁆, ⁅c * q * c⁻¹, D.σ⁆⁆ * ⁅c * q * c⁻¹, D.σ⁆) := by
            rw [hinner]
      _ = (⁅c * q * c⁻¹, ⁅c, D.σ⁆⁆ * ⁅⁅c, D.σ⁆, ⁅c * q * c⁻¹, D.σ⁆⁆) *
            ⁅c * q * c⁻¹, D.σ⁆ := by group
  rw [heq]
  exact D.W.mul_mem (D.Z_le_W (D.Z.mul_mem hzu hzv))
    (Subgroup.mem_sup_left (Subgroup.subset_closure hq'σ))

private theorem C_le_normalizer_W (D : Fs81CentData X) :
    D.C ≤ Subgroup.normalizer D.W := by
  rw [Subgroup.le_normalizer_iff]
  intro c hc w hw
  have hcomap : Subgroup.closure (fs81CommSet D.Q D.σ) ≤
      Subgroup.comap (MulAut.conj c).toMonoidHom D.W := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    change (MulAut.conj c) ⁅q, D.σ⁆ ∈ D.W
    rw [MulAut.conj_apply]
    exact D.C_conj_commSet_mem_W c hc q hq
  change w ∈ Subgroup.closure (fs81CommSet D.Q D.σ) ⊔ Subgroup.zpowers D.t₀ at hw
  obtain ⟨a, ha, z, hz, rfl⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left D.Z_le_normalizer_Ws).mp hw
  have haW : c * a * c⁻¹ ∈ D.W := by
    have h := hcomap ha
    change (MulAut.conj c) a ∈ D.W at h
    rwa [MulAut.conj_apply] at h
  have hzW : c * z * c⁻¹ ∈ D.W := by
    rw [conj_eq_self_of_mem_central D.zcentral hz (D.C_le_H hc)]
    exact D.Z_le_W hz
  rw [show c * (a * z) * c⁻¹ = (c * a * c⁻¹) * (c * z * c⁻¹) by group]
  exact D.W.mul_mem haW hzW

private theorem mem_M (D : Fs81CentData X) {x : X} (hxH : x ∈ D.H)
    (hxQ : ⁅x, D.σ⁆ ∈ D.Q)
    (hxWs : ∀ w ∈ fs81CommSet D.Q D.σ, ⁅x, w⁆ ∈ D.Z) : x ∈ D.M := by
  refine ⟨hxH, hxQ, ?_⟩
  intro w hw
  change w ∈ Subgroup.closure (fs81CommSet D.Q D.σ) ⊔ Subgroup.zpowers D.t₀ at hw
  obtain ⟨a, ha, z, hz, rfl⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left D.Z_le_normalizer_Ws).mp hw
  have haZ : ⁅x, a⁆ ∈ D.Z :=
    commutatorElement_mem_closure_of_central D.zcentral D.Ws_subset_H hxH hxWs a ha
  have hz1 : ⁅x, z⁆ = 1 := by
    rw [commutatorElement_def, ← D.zcentral z hz x hxH]
    group
  rw [commutatorElement_mul_right_eq_mul_conj, hz1]
  simpa using haZ

private theorem C_le_normalizer_M (D : Fs81CentData X) :
    D.C ≤ Subgroup.normalizer D.M := by
  rw [Subgroup.le_normalizer_iff]
  intro c hc m hm
  have huQ : ⁅c⁻¹, D.σ⁆ ∈ D.Q := by
    have h : c⁻¹ * ⁅c, D.σ⁆⁻¹ * c ∈ D.Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (D.hHnorm (D.C.inv_mem hc).1) ⁅c, D.σ⁆⁻¹).mp
        (D.Q.inv_mem (D.C_commutator_mem c hc))
    rwa [commutatorElement_inv_left, ← commutatorElement_inv]
  refine ⟨D.H.mul_mem (D.H.mul_mem (D.C_le_H hc) (D.M_le_H hm))
    (D.H.inv_mem (D.C_le_H hc)), ?_, ?_⟩
  · have hmu : ⁅m, ⁅c⁻¹, D.σ⁆⁆ ∈ D.Q := by
      have h := (Subgroup.mem_normalizer_iff.mp (D.hHnorm (D.M_le_H hm))
        ⁅c⁻¹, D.σ⁆).mp huQ
      rw [commutatorElement_def]
      exact D.Q.mul_mem h (D.Q.inv_mem huQ)
    have hmσ : ⁅m, D.σ⁆ ∈ D.Q := D.M_commutator_mem m hm
    have hmul : ⁅m, ⁅c⁻¹, D.σ⁆ * D.σ⁆ =
        ⁅m, ⁅c⁻¹, D.σ⁆⁆ * (⁅c⁻¹, D.σ⁆ * ⁅m, D.σ⁆ * ⁅c⁻¹, D.σ⁆⁻¹) := by
      calc ⁅m, ⁅c⁻¹, D.σ⁆ * D.σ⁆ =
          ⁅m, ⁅c⁻¹, D.σ⁆⁆ * ⁅c⁻¹, D.σ⁆ * ⁅m, D.σ⁆ * ⁅c⁻¹, D.σ⁆⁻¹ := by
            rw [commutatorElement_mul_right_eq_mul_conj]
        _ = ⁅m, ⁅c⁻¹, D.σ⁆⁆ * (⁅c⁻¹, D.σ⁆ * ⁅m, D.σ⁆ * ⁅c⁻¹, D.σ⁆⁻¹) := by group
    have hinv : c⁻¹ * D.σ * c = ⁅c⁻¹, D.σ⁆ * D.σ := by
      simpa [MulAut.conj_apply] using
        (conj_eq_commutatorElement_mul (g₁ := c⁻¹) (g₂ := D.σ))
    rw [commutatorElement_conj_left, hinv, hmul]
    exact (Subgroup.mem_normalizer_iff.mp (D.hHnorm (D.C_le_H hc)) _).mp
      (D.Q.mul_mem hmu (D.Q.mul_mem (D.Q.mul_mem huQ hmσ) (D.Q.inv_mem huQ)))
  · intro w hw
    have hcw : c⁻¹ * w * c ∈ D.W := by
      have := (Subgroup.le_normalizer_iff.mp D.C_le_normalizer_W) c⁻¹
        (D.C.inv_mem hc) w hw
      simpa using this
    have hmz : ⁅m, c⁻¹ * w * c⁆ ∈ D.Z := D.M_commutator_W m hm _ hcw
    rw [commutatorElement_conj_left]
    rw [conj_eq_self_of_mem_central D.zcentral hmz (D.C_le_H hc)]
    exact hmz

private def N (D : Fs81CentData X) : Subgroup X :=
  fs81N D.C D.C0 D.M D.W D.Q D.C_le_normalizer_C0 D.C_le_normalizer_W D.M_le_C

private theorem N_le_M (D : Fs81CentData X) : D.N ≤ D.M := fun _ hn => hn.1

private theorem N_commutator_Q (D : Fs81CentData X) :
    ∀ n ∈ D.N, ∀ q ∈ D.Q, ⁅n, q⁆ ∈ D.C0 := fun _ hn => hn.2.1

private theorem N_commutator_C0 (D : Fs81CentData X) :
    ∀ n ∈ D.N, ∀ c ∈ D.C0, ⁅n, c⁆ ∈ D.W := fun _ hn => hn.2.2

private theorem C_le_normalizer_N (D : Fs81CentData X) :
    D.C ≤ Subgroup.normalizer D.N := by
  rw [Subgroup.le_normalizer_iff]
  intro c hc n hn
  refine ⟨(Subgroup.le_normalizer_iff.mp D.C_le_normalizer_M) c hc n (D.N_le_M hn), ?_, ?_⟩
  · intro q hq
    have hq' : c⁻¹ * q * c ∈ D.Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (D.hHnorm (D.C_le_H (D.C.inv_mem hc))) q).mp hq
    have hnq : ⁅n, c⁻¹ * q * c⁆ ∈ D.C0 := D.N_commutator_Q n hn _ hq'
    rw [commutatorElement_conj_left]
    exact (Subgroup.le_normalizer_iff.mp D.C_le_normalizer_C0) c hc _ hnq
  · intro c₀ hc₀
    have hc₀' : c⁻¹ * c₀ * c ∈ D.C0 := by
      simpa using (Subgroup.le_normalizer_iff.mp D.C_le_normalizer_C0) c⁻¹
        (D.C.inv_mem hc) c₀ hc₀
    have hnw : ⁅n, c⁻¹ * c₀ * c⁆ ∈ D.W := D.N_commutator_C0 n hn _ hc₀'
    rw [commutatorElement_conj_left]
    exact (Subgroup.le_normalizer_iff.mp D.C_le_normalizer_W) c hc _ hnw

private theorem K_le_M (D : Fs81CentData X) : D.K ≤ D.M := by
  intro x hx
  refine D.mem_M (D.hKH hx) ?_ (D.hKWs x hx)
  have hxσ : ⁅x, D.σ⁆ = 1 := by
    rw [commutatorElement_def, D.hKσ x hx]
    group
  rw [hxσ]
  exact D.Q.one_mem

private theorem S_le_M (D : Fs81CentData X) : D.S ≤ D.M := by
  intro s hs
  refine D.mem_M (D.hSH hs) ?_ (D.hSWs s hs)
  have hsσ : ⁅s, D.σ⁆ = 1 := by
    rw [commutatorElement_def, D.hSσ s hs]
    group
  rw [hsσ]
  exact D.Q.one_mem

private theorem Q_le_M (D : Fs81CentData X) : D.Q ≤ D.M := by
  intro q hq
  refine D.mem_M (D.hQH hq) (D.Q_commutator_mem q hq) ?_
  intro w hw
  rcases hw with ⟨q', hq', rfl⟩
  exact D.hQQ q hq ⁅q', D.σ⁆ (D.Q_commutator_mem q' hq')

private theorem S_commutator_Q (D : Fs81CentData X) :
    ∀ s ∈ D.S, ∀ q ∈ D.Q, ⁅s, q⁆ ∈ D.Q := by
  intro s hs q hq
  have h := (Subgroup.mem_normalizer_iff.mp (D.hHnorm (D.hSH hs)) q).mp hq
  rw [show ⁅s, q⁆ = (s * q * s⁻¹) * q⁻¹ by rw [commutatorElement_def]]
  exact D.Q.mul_mem h (D.Q.inv_mem hq)

private theorem Q_le_N (D : Fs81CentData X) : D.Q ≤ D.N := by
  intro q hq
  refine ⟨D.Q_le_M hq, ?_, ?_⟩
  · intro q' hq'
    exact D.Z_le_C0 (D.hQQ q hq q' hq')
  · intro c hc
    exact D.Z_le_W (D.hQQ q hq c hc.1)

private theorem S_le_N (D : Fs81CentData X) : D.S ≤ D.N := by
  intro s hs
  refine ⟨D.S_le_M hs, ?_, ?_⟩
  · intro q hq
    exact ⟨D.S_commutator_Q s hs q hq, D.hSq s hs q hq⟩
  · intro c hc
    exact D.hSc s hs c hc.1 hc.2

private theorem Q_sup_S_le_N (D : Fs81CentData X) : D.Q ⊔ D.S ≤ D.N :=
  sup_le D.Q_le_N D.S_le_N

private theorem N_isPGroup [Finite X] (D : Fs81CentData X)
    (h₁ : FS81FlagTwoGroup) : IsPGroup 2 D.N :=
  h₁ X D.H D.Q D.C0 (D.W ⊓ D.C0) D.Z D.N D.hQ2 (le_inf D.Z_le_W D.Z_le_C0)
    inf_le_right D.C0_le_Q (D.N_le_M.trans D.M_le_H) D.hHcent
    (fun n hn q hq => D.N_commutator_Q n hn q hq)
    (fun n hn c hc => ⟨D.N_commutator_C0 n hn c hc, D.N_commutator_Q n hn c hc.1⟩)
    (fun n hn w hw => D.M_commutator_W n (D.N_le_M hn) w hw.1)
    (fun n hn z hz => (D.zcentral z hz n (D.M_le_H (D.N_le_M hn))).symm)

private theorem K_le_C (D : Fs81CentData X) : D.K ≤ D.C := by
  intro x hx
  refine ⟨D.hKH hx, ?_⟩
  have hxσ : ⁅x, D.σ⁆ = 1 := by
    rw [commutatorElement_def, D.hKσ x hx]
    group
  rw [hxσ]
  exact D.Q.one_mem

private theorem P_le_C (D : Fs81CentData X) : D.P ≤ D.C := by
  intro p hp
  refine ⟨D.hPH hp, ?_⟩
  have hpσ : ⁅p, D.σ⁆ = 1 := by
    rw [commutatorElement_def, D.hPσ p hp]
    group
  rw [hpσ]
  exact D.Q.one_mem

private def T0 (D : Fs81CentData X) : Subgroup X := D.Q ⊔ D.S

private def T (D : Fs81CentData X) : Subgroup X :=
  D.N ⊓ Subgroup.normalizer (D.T0 : Set X)

private theorem T0_isPGroup (D : Fs81CentData X) : IsPGroup 2 D.T0 := by
  change IsPGroup 2 ↥(D.Q ⊔ D.S)
  exact IsPGroup.to_sup_of_normal_left' D.hQ2 D.hS2 (D.hSH.trans D.hHnorm)

private theorem K_le_normalizer_T0 (D : Fs81CentData X) :
    D.K ≤ Subgroup.normalizer (D.T0 : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hxK y hy
  change y ∈ D.Q ⊔ D.S at hy
  obtain ⟨q, hq, s, hs, rfl⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
      (D.hSH.trans D.hHnorm)).mp hy
  have hq' : x * q * x⁻¹ ∈ D.Q :=
    (Subgroup.mem_normalizer_iff.mp (D.hHnorm (D.hKH hxK)) q).mp hq
  have hs' : x * s * x⁻¹ ∈ D.S :=
    (Subgroup.mem_normalizer_iff.mp (D.hKSnorm hxK) s).mp hs
  rw [show x * (q * s) * x⁻¹ = (x * q * x⁻¹) * (x * s * x⁻¹) by group]
  exact Subgroup.mul_mem_sup hq' hs'

private theorem P_le_normalizer_T0 (D : Fs81CentData X) :
    D.P ≤ Subgroup.normalizer (D.T0 : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hxP y hy
  change y ∈ D.Q ⊔ D.S at hy
  obtain ⟨q, hq, s, hs, rfl⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
      (D.hSH.trans D.hHnorm)).mp hy
  have hq' : x * q * x⁻¹ ∈ D.Q :=
    (Subgroup.mem_normalizer_iff.mp (D.hHnorm (D.hPH hxP)) q).mp hq
  have hs' : x * s * x⁻¹ ∈ D.S :=
    (Subgroup.mem_normalizer_iff.mp (D.hPSnorm hxP) s).mp hs
  rw [show x * (q * s) * x⁻¹ = (x * q * x⁻¹) * (x * s * x⁻¹) by group]
  exact Subgroup.mul_mem_sup hq' hs'

private theorem P_le_normalizer_N (D : Fs81CentData X) :
    D.P ≤ Subgroup.normalizer D.N :=
  D.P_le_C.trans D.C_le_normalizer_N

private theorem P_le_normalizer_M (D : Fs81CentData X) :
    D.P ≤ Subgroup.normalizer D.M :=
  D.P_le_C.trans D.C_le_normalizer_M

private theorem P_le_normalizer_T (D : Fs81CentData X) :
    D.P ≤ Subgroup.normalizer (D.T : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro p hp x hx
  refine ⟨(Subgroup.le_normalizer_iff.mp D.P_le_normalizer_N) p hp x hx.1, ?_⟩
  exact (Subgroup.normalizer (D.T0 : Set X)).mul_mem
    ((Subgroup.normalizer (D.T0 : Set X)).mul_mem (D.P_le_normalizer_T0 hp) hx.2)
    ((Subgroup.normalizer (D.T0 : Set X)).inv_mem (D.P_le_normalizer_T0 hp))

private theorem T_isSolvable [Finite X] (D : Fs81CentData X)
    (hT2 : IsPGroup 2 D.T) : IsSolvable ↥D.T := by
  haveI : Group.IsNilpotent ↥D.T := IsPGroup.isNilpotent hT2
  exact IsNilpotent.to_isSolvable

private theorem b_zpow_eq_one_of_mem_N (D : Fs81CentData X)
    (hN2 : IsPGroup 2 D.N) {m : ℤ} (hmN : D.b ^ m ∈ D.N) : D.b ^ m = 1 := by
  have hdvd : orderOf (D.b ^ m) ∣ 3 := by
    have hmem : D.b ^ m ∈ Subgroup.zpowers D.b := Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers D.b) hmem
    rwa [Nat.card_zpowers, D.hb3] at h
  obtain ⟨j, hj⟩ := IsPGroup.exists_orderOf_eq_pow (p := 2) hN2 ⟨D.b ^ m, hmN⟩
  have hbmord : orderOf (D.b ^ m) = 2 ^ j := by simpa using hj
  have hdvd' : 2 ^ j ∣ 3 := by rwa [hbmord] at hdvd
  have h1 : 2 ^ j = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd' with h | h
    · exact h
    · exfalso
      cases j with
      | zero => norm_num at h
      | succ k =>
          have h2 : 2 ∣ 2 ^ (k + 1) := ⟨2 ^ k, by rw [pow_succ]; ring⟩
          rw [h] at h2
          norm_num at h2
  have hord1 : orderOf (D.b ^ m) = 1 := by rw [hbmord, h1]
  exact orderOf_eq_one_iff.mp hord1

private theorem b_mul_k_not_mem_N (D : Fs81CentData X)
    (hN2 : IsPGroup 2 D.N) (hCnormN : D.C ≤ Subgroup.normalizer D.N) {m : ℤ}
    (hmN : D.b ^ m * D.k ∈ D.N) : False := by
  have hbC : D.b ∈ D.C := D.K_le_C D.hbK
  have hbz : D.b * (D.b ^ m * D.k) * D.b⁻¹ ∈ D.N :=
    (Subgroup.le_normalizer_iff.mp hCnormN) D.b hbC _ hmN
  have hprod : (D.b ^ m * D.k) * (D.b * (D.b ^ m * D.k) * D.b⁻¹) ∈ D.N :=
    D.N.mul_mem hmN hbz
  have heq : (D.b ^ m * D.k) * (D.b * (D.b ^ m * D.k) * D.b⁻¹) = D.b :=
    conj_involution_mul_eq D.hb3 D.hk2 D.hkb m
  have hbN : D.b ∈ D.N := by rwa [heq] at hprod
  obtain ⟨j, hj⟩ := IsPGroup.exists_orderOf_eq_pow (p := 2) hN2 ⟨D.b, hbN⟩
  have hbord : orderOf D.b = 2 ^ j := by simpa using hj
  rw [D.hb3] at hbord
  cases j with
  | zero => norm_num at hbord
  | succ k =>
      have h2 : 2 ∣ 2 ^ (k + 1) := ⟨2 ^ k, by rw [pow_succ]; ring⟩
      rw [← hbord] at h2
      norm_num at h2

private theorem N_inf_K_eq_bot (D : Fs81CentData X) (hN2 : IsPGroup 2 D.N)
    (hCnormN : D.C ≤ Subgroup.normalizer D.N) : D.N ⊓ D.K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzN, hzK⟩ := hz
  rcases CFSG.GroupTheory.mem_closure_pair_of_conj_eq_inv D.k_sq D.hkb (D.hKcl hzK) with
    ⟨m, rfl | rfl⟩
  · exact Subgroup.mem_bot.mpr (D.b_zpow_eq_one_of_mem_N hN2 hzN)
  · exfalso
    exact D.b_mul_k_not_mem_N hN2 hCnormN hzN

private theorem exists_fixed_coset [Finite X] (D : Fs81CentData X)
    (hT0_2 : IsPGroup 2 D.T0)
    (hPnormT0 : D.P ≤ Subgroup.normalizer (D.T0 : Set X))
    {t : X} (ht : t ∈ D.T) (hmem : D.b₁ * t * D.b₁⁻¹ * t⁻¹ ∈ D.T0) :
    ∃ n ∈ D.T0, D.b₁ * (t * n) * D.b₁⁻¹ = t * n := by
  have hNinv : ∀ n ∈ D.T0, D.b₁ * n * D.b₁⁻¹ ∈ D.T0 := fun n hn =>
    (Subgroup.le_normalizer_iff.mp hPnormT0) D.b₁ D.hb₁P n hn
  have hg : t⁻¹ * (D.b₁ * t * D.b₁⁻¹) ∈ D.T0 := by
    have h1 : t⁻¹ * (D.b₁ * t * D.b₁⁻¹) =
        t⁻¹ * (D.b₁ * t * D.b₁⁻¹ * t⁻¹) * t := by group
    rw [h1]
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (D.T0 : Set X)).inv_mem ht.2) _).mp hmem
  have h3T0 : ¬ 3 ∣ Nat.card D.T0 := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT0_2
    rw [hk] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hcop : Nat.Coprime (orderOf D.b₁) (Nat.card D.T0) := by
    rw [D.hb₁3]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3T0
  exact CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime (N := D.T0) hNinv hg hcop

private theorem fpf [Finite X] (D : Fs81CentData X)
    (hT0_2 : IsPGroup 2 D.T0)
    (hKnormT0 : D.K ≤ Subgroup.normalizer (D.T0 : Set X))
    (hPnormT0 : D.P ≤ Subgroup.normalizer (D.T0 : Set X))
    (hNK : D.N ⊓ D.K = ⊥)
    {t : X} (ht : t ∈ D.T) (hmem : D.b₁ * t * D.b₁⁻¹ * t⁻¹ ∈ D.T0) :
    t ∈ D.T0 := by
  obtain ⟨n, hnT0, hfixn⟩ := D.exists_fixed_coset hT0_2 hPnormT0 ht hmem
  have htN : t ∈ D.N := ht.1
  have hnN : n ∈ D.N := D.Q_sup_S_le_N hnT0
  have ht'N : t * n ∈ D.N := D.N.mul_mem htN hnN
  have ht'Y : t * n ∈ D.Y := by
    apply D.hb₁Y
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : D.b₁ * (t * n) = (t * n) * D.b₁ := by
      calc D.b₁ * (t * n) = D.b₁ * (t * n) * D.b₁⁻¹ * D.b₁ := by group
        _ = (t * n) * D.b₁ := by rw [hfixn]
    exact hcomm.symm
  have ht'H : t * n ∈ D.H := D.M_le_H (D.N_le_M ht'N)
  have ht'Q : ⁅t * n, D.σ⁆ ∈ D.Q := D.M_commutator_mem (t * n) (D.N_le_M ht'N)
  have ht'Ws : ∀ w ∈ fs81CommSet D.Q D.σ, ⁅t * n, w⁆ ∈ D.Z :=
    fun w hw => D.M_commutator_W (t * n) (D.N_le_M ht'N) w (D.Ws_subset_W hw)
  have ht'sup : t * n ∈ D.Q ⊔ D.S ⊔ D.K :=
    D.hlast (t * n) ⟨ht'H, ht'Y⟩ ht'Q ht'Ws
  have ht'sup' : t * n ∈ D.T0 ⊔ D.K := ht'sup
  obtain ⟨x, hxT0, κ, hκK, hxκ⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hKnormT0).mp ht'sup'
  have hxN : x ∈ D.N := D.Q_sup_S_le_N hxT0
  have hκN : κ ∈ D.N := by
    have hκ : κ = x⁻¹ * (t * n) := by rw [hxκ]; group
    rw [hκ]
    exact D.N.mul_mem (D.N.inv_mem hxN) ht'N
  have hκbot : κ ∈ (⊥ : Subgroup X) := by
    rw [← hNK]
    exact ⟨hκN, hκK⟩
  have hκ1 : κ = 1 := Subgroup.mem_bot.mp hκbot
  have ht'T0 : t * n ∈ D.T0 := by
    rw [hxκ, hκ1, mul_one]
    exact hxT0
  have htT0 : t ∈ D.T0 := by
    have h : t = (t * n) * n⁻¹ := by group
    rw [h]
    exact D.T0.mul_mem ht'T0 (D.T0.inv_mem hnT0)
  exact htT0

private theorem T0_eq_N [Finite X] (D : Fs81CentData X)
    (hN2 : IsPGroup 2 D.N) (hT0_2 : IsPGroup 2 D.T0)
    (hKnormT0 : D.K ≤ Subgroup.normalizer (D.T0 : Set X))
    (hPnormT0 : D.P ≤ Subgroup.normalizer (D.T0 : Set X))
    (hPnormT : D.P ≤ Subgroup.normalizer (D.T : Set X))
    (hfpf : ∀ t ∈ D.T, D.b₁ * t * D.b₁⁻¹ * t⁻¹ ∈ D.T0 → t ∈ D.T0) :
    D.T0 = D.N := by
  have hT0N : D.T0 ≤ D.N := D.Q_sup_S_le_N
  by_contra hne
  have hlt : D.T0 < D.N := lt_of_le_of_ne hT0N hne
  have hgrowth : D.T0 < D.N ⊓ Subgroup.normalizer (D.T0 : Set X) :=
    pSubgroup_lt_normalizer_intersection 2 Nat.prime_two D.T0 D.N hN2 hlt
  have hT2 : IsPGroup 2 D.T := hN2.to_le inf_le_left
  have hTle : D.T ≤ D.T0 :=
    le_of_l3TwoFixedPointFree (T₀ := D.T0) (T := D.T) (P := D.P)
      (le_inf hT0N Subgroup.le_normalizer) inf_le_right hPnormT hPnormT0 D.hPiso
      D.hb₁P D.hb₁3 (D.T_isSolvable hT2) hfpf
  exact not_le_of_gt hgrowth hTle

private theorem decomp (D : Fs81CentData X)
    (hKnormT0 : D.K ≤ Subgroup.normalizer (D.T0 : Set X))
    (hT0eqN : D.T0 = D.N) {m : X} (hm : m ∈ D.M) (hmY : m ∈ D.Y) :
    ∃ x ∈ D.N, ∃ κ ∈ D.K, m = x * κ := by
  have hmSup : m ∈ D.Q ⊔ D.S ⊔ D.K :=
    D.hlast m ⟨D.M_le_H hm, hmY⟩ (D.M_commutator_mem m hm)
      (fun w hw => D.M_commutator_W m hm w (D.Ws_subset_W hw))
  have hmSup' : m ∈ D.T0 ⊔ D.K := hmSup
  obtain ⟨x, hxT0, κ, hκK, hxκ⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hKnormT0).mp hmSup'
  refine ⟨x, ?_, κ, hκK, hxκ⟩
  rwa [hT0eqN] at hxT0

private theorem centralizer_b_le (D : Fs81CentData X)
    (hKnormT0 : D.K ≤ Subgroup.normalizer (D.T0 : Set X))
    (hT0eqN : D.T0 = D.N) (hNK : D.N ⊓ D.K = ⊥) {m : X}
    (hm : m ∈ D.M) (hcomm : m * D.b = D.b * m) :
    m ∈ D.N ⊔ Subgroup.zpowers D.b := by
  have hmY : m ∈ D.Y := by
    apply D.hbY
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  obtain ⟨x, hxN, κ, hκK, hxκ⟩ := D.decomp hKnormT0 hT0eqN hm hmY
  have hbC : D.b ∈ D.C := D.K_le_C D.hbK
  have hbxb : D.b * x⁻¹ * D.b⁻¹ ∈ D.N :=
    (Subgroup.le_normalizer_iff.mp D.C_le_normalizer_N) D.b hbC x⁻¹ (D.N.inv_mem hxN)
  have hbx : D.b * x⁻¹ * D.b⁻¹ * x ∈ D.N := D.N.mul_mem hbxb hxN
  have heq : ⁅κ, D.b⁆ = (D.b * x⁻¹ * D.b⁻¹ * x)⁻¹ := by
    rw [show κ = x⁻¹ * m by rw [hxκ]; group]
    simp only [commutatorElement_def]
    calc x⁻¹ * m * D.b * (x⁻¹ * m)⁻¹ * D.b⁻¹
        = x⁻¹ * (m * D.b) * ((x⁻¹ * m)⁻¹) * D.b⁻¹ := by group
      _ = x⁻¹ * (D.b * m) * ((x⁻¹ * m)⁻¹) * D.b⁻¹ := by rw [hcomm]
      _ = (D.b * x⁻¹ * D.b⁻¹ * x)⁻¹ := by group
  have hκbN : ⁅κ, D.b⁆ ∈ D.N := by
    rw [heq]
    exact D.N.inv_mem hbx
  have hκbK : ⁅κ, D.b⁆ ∈ D.K := by
    simp only [commutatorElement_def]
    exact D.K.mul_mem (D.K.mul_mem (D.K.mul_mem hκK D.hbK) (D.K.inv_mem hκK))
      (D.K.inv_mem D.hbK)
  have hκb1 : ⁅κ, D.b⁆ = 1 := by
    have hbot : ⁅κ, D.b⁆ ∈ (⊥ : Subgroup X) := by
      rw [← hNK]
      exact ⟨hκbN, hκbK⟩
    exact Subgroup.mem_bot.mp hbot
  have hκcomm : κ * D.b = D.b * κ := by
    have h : κ * D.b * κ⁻¹ * D.b⁻¹ = 1 := by
      simpa only [commutatorElement_def] using hκb1
    calc κ * D.b = (κ * D.b * κ⁻¹ * D.b⁻¹) * (D.b * κ) := by group
      _ = D.b * κ := by rw [h, one_mul]
  have hκzp : κ ∈ Subgroup.zpowers D.b :=
    CFSG.GroupTheory.mem_zpowers_left_of_mem_closure_pair_of_conj_eq_inv D.k_sq D.hkb
      D.b_sq_ne_one (D.hKcl hκK) hκcomm
  rw [hxκ]
  exact Subgroup.mul_mem_sup hxN hκzp

private theorem centralizer_b1_le (D : Fs81CentData X)
    (hKnormT0 : D.K ≤ Subgroup.normalizer (D.T0 : Set X))
    (hT0eqN : D.T0 = D.N) {m : X}
    (hm : m ∈ D.M) (hcomm : m * D.b₁ = D.b₁ * m) :
    m ∈ D.N ⊔ Subgroup.closure ({D.b, D.k} : Set X) := by
  have hmY : m ∈ D.Y := D.hb₁Y (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  obtain ⟨x, hxN, κ, hκK, hxκ⟩ := D.decomp hKnormT0 hT0eqN hm hmY
  have hκcl : κ ∈ Subgroup.closure ({D.b, D.k} : Set X) := D.hKcl hκK
  rw [hxκ]
  exact Subgroup.mul_mem_sup hxN hκcl

private theorem M_le_QSK [Finite X] (D : Fs81CentData X) (h₂ : FS81SixLift)
    (hN2 : IsPGroup 2 D.N) (hCnormN : D.C ≤ Subgroup.normalizer D.N)
    (hPnormM : D.P ≤ Subgroup.normalizer D.M)
    (hKnormT0 : D.K ≤ Subgroup.normalizer (D.T0 : Set X))
    (hT0eqN : D.T0 = D.N)
    (hCb : ∀ m ∈ D.M, m * D.b = D.b * m → m ∈ D.N ⊔ Subgroup.zpowers D.b)
    (hCb₁ : ∀ m ∈ D.M, m * D.b₁ = D.b₁ * m →
      m ∈ D.N ⊔ Subgroup.closure ({D.b, D.k} : Set X)) :
    D.M ≤ D.Q ⊔ D.S ⊔ D.K := by
  have hSix : D.M ≤ D.N ⊔ Subgroup.closure ({D.b, D.k} : Set X) :=
    h₂ X D.C D.M D.N D.P D.b D.k D.b₁ D.N_le_M D.M_le_C hCnormN hN2 D.P_le_C hPnormM
      (D.K_le_M D.hbK) (D.K_le_M D.hkK) D.hb3 D.hk2 D.hkb D.hPiso D.hb₁P D.hb₁3 D.hPk
      hCb hCb₁
  have hclK : Subgroup.closure ({D.b, D.k} : Set X) ≤ D.K := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact D.hbK
    · exact D.hkK
  refine hSix.trans (sup_le ?_ ?_)
  · rw [← hT0eqN]
    exact le_sup_left
  · exact hclK.trans (le_sup_right : D.K ≤ (D.Q ⊔ D.S) ⊔ D.K)

private theorem M_normal (D : Fs81CentData X)
    (hCnormM : D.C ≤ Subgroup.normalizer D.M) :
    ∀ c ∈ D.H, ⁅c, D.σ⁆ ∈ D.Q → ∀ m ∈ D.M, c * m * c⁻¹ ∈ D.M := by
  intro c hcH hcQ m hm
  exact (Subgroup.le_normalizer_iff.mp hCnormM) c ⟨hcH, hcQ⟩ m hm

private theorem fs81CentM_main [Finite X] (D : Fs81CentData X)
    (h₁ : FS81FlagTwoGroup) (h₂ : FS81SixLift) :
    ∃ M : Subgroup X, D.K ≤ M ∧ M ≤ D.Q ⊔ D.S ⊔ D.K ∧
      ∀ c ∈ D.H, ⁅c, D.σ⁆ ∈ D.Q → ∀ m ∈ M, c * m * c⁻¹ ∈ M := by
  have hN2 := D.N_isPGroup h₁
  have hCnormN := D.C_le_normalizer_N
  have hPnormM := D.P_le_normalizer_M
  have hT0_2 := D.T0_isPGroup
  have hKnormT0 := D.K_le_normalizer_T0
  have hPnormT0 := D.P_le_normalizer_T0
  have hPnormT := D.P_le_normalizer_T
  have hNK := D.N_inf_K_eq_bot hN2 hCnormN
  have hfpf : ∀ t ∈ D.T, D.b₁ * t * D.b₁⁻¹ * t⁻¹ ∈ D.T0 → t ∈ D.T0 :=
    fun t => D.fpf (t := t) hT0_2 hKnormT0 hPnormT0 hNK
  have hT0eqN := D.T0_eq_N hN2 hT0_2 hKnormT0 hPnormT0 hPnormT hfpf
  have hCb : ∀ m ∈ D.M, m * D.b = D.b * m → m ∈ D.N ⊔ Subgroup.zpowers D.b :=
    fun m => D.centralizer_b_le (m := m) hKnormT0 hT0eqN hNK
  have hCb₁ : ∀ m ∈ D.M, m * D.b₁ = D.b₁ * m →
      m ∈ D.N ⊔ Subgroup.closure ({D.b, D.k} : Set X) :=
    fun m => D.centralizer_b1_le (m := m) hKnormT0 hT0eqN
  refine ⟨D.M, D.K_le_M,
    D.M_le_QSK h₂ hN2 hCnormN hPnormM hKnormT0 hT0eqN hCb hCb₁, ?_⟩
  exact D.M_normal D.C_le_normalizer_M

end Fs81CentData

theorem fs81CentM_of (h₁ : FS81FlagTwoGroup) (h₂ : FS81SixLift) : FS81CentM := by
  classical
  intro X _ _ Y H Q S K P t₀ σ b k b₁
    hQH hHnorm hQ2 hHcent ht₀Q ht₀cent hQQ hσH
    hSH hS2 hSσ hSWs hSq hSc hKH hKSnorm hKσ hKWs
    hbK hkK hb3 hk2 hkb hKcl hPH hPiso hPσ hPk hPSnorm hb₁P hb₁3 hbY hb₁Y hlast
  exact Fs81CentData.fs81CentM_main
    { Y := Y, H := H, Q := Q, S := S, K := K, P := P, t₀ := t₀, σ := σ, b := b, k := k,
      b₁ := b₁, hQH := hQH, hHnorm := hHnorm, hQ2 := hQ2, hHcent := hHcent, ht₀Q := ht₀Q,
      ht₀cent := ht₀cent, hQQ := hQQ, hσH := hσH, hSH := hSH, hS2 := hS2, hSσ := hSσ,
      hSWs := hSWs, hSq := hSq, hSc := hSc, hKH := hKH, hKSnorm := hKSnorm, hKσ := hKσ,
      hKWs := hKWs, hbK := hbK, hkK := hkK, hb3 := hb3, hk2 := hk2, hkb := hkb,
      hKcl := hKcl, hPH := hPH, hPiso := hPiso, hPσ := hPσ, hPk := hPk, hPSnorm := hPSnorm,
      hb₁P := hb₁P, hb₁3 := hb₁3, hbY := hbY, hb₁Y := hb₁Y, hlast := hlast } h₁ h₂

end CFSG.StandardType.FrameRoute.FS81
