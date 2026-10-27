module

public import CFSG.RankThree.PartTwo.Sec21.FF81SL32FixData
public import Mathlib.GroupTheory.PGroup
import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fixed

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix

open Subgroup

variable {X : Type*} [Group X] {K W M : Subgroup X}

def conjOn (M : Subgroup X) (x : X) (hx : ∀ m ∈ M, x * m * x⁻¹ ∈ M) : M →* M where
  toFun m := ⟨x * m * x⁻¹, hx m m.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

section Action

variable [hN : (W.subgroupOf M).Normal]
  (hKM : ∀ x ∈ K, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hKW : ∀ x ∈ K, ∀ w ∈ W, x * w * x⁻¹ ∈ W)

def actQ (x : K) : (M ⧸ W.subgroupOf M) →* (M ⧸ W.subgroupOf M) :=
  QuotientGroup.map (W.subgroupOf M) (W.subgroupOf M) (conjOn M x (hKM x x.2)) (by
    intro a ha
    exact hKW x x.2 a ha)

include hKM hKW in
theorem actQ_mk (x : K) (m : M) :
    actQ hKM hKW x (m : M ⧸ W.subgroupOf M) =
      ((⟨(x : X) * (m : X) * (x : X)⁻¹, hKM x x.2 m m.2⟩ : M) : M ⧸ W.subgroupOf M) :=
  rfl

include hKM hKW in
theorem actQ_one : actQ hKM hKW 1 = MonoidHom.id (M ⧸ W.subgroupOf M) := by
  refine MonoidHom.ext fun q => QuotientGroup.induction_on q fun m => ?_
  rw [actQ_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext (by simp))

include hKM hKW in
theorem actQ_mul (x x' : K) :
    actQ hKM hKW (x * x') = (actQ hKM hKW x).comp (actQ hKM hKW x') := by
  refine MonoidHom.ext fun q => QuotientGroup.induction_on q fun m => ?_
  rw [actQ_mk, MonoidHom.comp_apply, actQ_mk, actQ_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext (by simp only [Subgroup.coe_mul]; group))

def rho : K →* MulAut (M ⧸ W.subgroupOf M) where
  toFun x := MonoidHom.toMulEquiv (actQ hKM hKW x) (actQ hKM hKW x⁻¹)
    (by rw [← actQ_mul, inv_mul_cancel, actQ_one])
    (by rw [← actQ_mul, mul_inv_cancel, actQ_one])
  map_one' := MulEquiv.ext fun q => congrArg (fun f => f q) (actQ_one hKM hKW)
  map_mul' x x' := MulEquiv.ext fun q => congrArg (fun f => f q) (actQ_mul hKM hKW x x')

def fixQ (x : K) : Subgroup (M ⧸ W.subgroupOf M) :=
  (actQ hKM hKW x).eqLocus (MonoidHom.id _)

end Action

section Count

variable [hN : (W.subgroupOf M).Normal]
  (hKM : ∀ x ∈ K, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hKW : ∀ x ∈ K, ∀ w ∈ W, x * w * x⁻¹ ∈ W)

include hKM hKW in
theorem card_fix_mul [Finite X] (hWM : W ≤ M) {y : X} (hy : y ∈ K) (hy3 : y ^ 3 = 1)
    (h3 : ¬ 3 ∣ Nat.card W) :
    Nat.card ↥(W ⊓ centralizer ({y} : Set X)) * Nat.card ↥(fixQ hKM hKW ⟨y, hy⟩) =
      Nat.card ↥(M ⊓ centralizer ({y} : Set X)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup X := M ⊓ centralizer ({y} : Set X) with hH
  let π₀ : ↥H →* (M ⧸ W.subgroupOf M) :=
    (QuotientGroup.mk' (W.subgroupOf M)).comp (Subgroup.inclusion inf_le_left)
  have hπ₀v : ∀ h : ↥H, π₀ h = ((⟨(h : X), h.2.1⟩ : M) : M ⧸ W.subgroupOf M) := fun h => rfl
  have hπ₀ : ∀ h : ↥H, π₀ h ∈ fixQ hKM hKW ⟨y, hy⟩ := by
    intro h
    show actQ hKM hKW ⟨y, hy⟩ (π₀ h) = π₀ h
    rw [hπ₀v, actQ_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    have hc : (h : X) * y = y * h := mem_centralizer_singleton_iff.1 h.2.2
    show y * (h : X) * y⁻¹ = h
    rw [← hc]
    group
  let π : ↥H →* ↥(fixQ hKM hKW ⟨y, hy⟩) := π₀.codRestrict _ hπ₀
  have hπv : ∀ h : ↥H, ((π h : ↥(fixQ hKM hKW ⟨y, hy⟩)) : M ⧸ W.subgroupOf M) = π₀ h :=
    fun h => rfl
  have hker : π.ker = (W ⊓ centralizer ({y} : Set X)).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hc : (h : X) ∈ centralizer ({y} : Set X) := h.2.2
    constructor
    · intro hh
      have h1 : π₀ h = 1 := by rw [← hπv, hh]; rfl
      rw [hπ₀v, QuotientGroup.eq_one_iff] at h1
      exact ⟨h1, hc⟩
    · rintro ⟨hw, -⟩
      apply Subtype.ext
      rw [hπv, hπ₀v]
      exact (QuotientGroup.eq_one_iff _).2 hw
  have hsurj : Function.Surjective π := by
    rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | _ m =>
      have hq' : actQ hKM hKW ⟨y, hy⟩ (m : M ⧸ W.subgroupOf M) = m := hq
      rw [actQ_mk] at hq'
      have hmem : (m : X)⁻¹ * (y * m * y⁻¹) ∈ W := by
        have h := QuotientGroup.eq.1 hq'.symm
        rw [Subgroup.mem_subgroupOf] at h
        simpa using h
      obtain ⟨n, hn, hfix⟩ := CFSG.GH74.GLS.Stage1.Thm6.Sec13.fixed_in_coset (p := 3) W y m 1
        (by simpa using hy3) (fun n hn => hKW y hy n hn) hmem h3
      have hmn : (m : X) * n ∈ M := M.mul_mem m.2 (hWM hn)
      refine ⟨⟨(m : X) * n, hmn, ?_⟩, ?_⟩
      · show (m : X) * n ∈ centralizer ({y} : Set X)
        rw [mem_centralizer_singleton_iff]
        have : y * ((m : X) * n) = (m * n) * y := by
          calc y * ((m : X) * n) = y * (m * n) * y⁻¹ * y := by group
            _ = (m * n) * y := by rw [hfix]
        exact this.symm
      · apply Subtype.ext
        rw [hπv, hπ₀v]
        refine QuotientGroup.eq.2 ?_
        rw [Subgroup.mem_subgroupOf]
        show ((m : X) * n)⁻¹ * m ∈ W
        have e : ((m : X) * n)⁻¹ * m = n⁻¹ := by group
        rw [e]
        exact W.inv_mem hn
  have key := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker] at key
  have e : Nat.card ↥((W ⊓ centralizer ({y} : Set X)).subgroupOf H) =
      Nat.card ↥(W ⊓ centralizer ({y} : Set X)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_inf_right _ hWM)).toEquiv
  rw [e] at key
  exact key

end Count

theorem layer_bound [Finite X] (hWM : W ≤ M) [hN : (W.subgroupOf M).Normal]
    (hKM : ∀ x ∈ K, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hKW : ∀ x ∈ K, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ W) (hsq : ∀ a ∈ M, a * a ∈ W)
    (hW : IsPGroup 2 W) (ψ : GL3 →* K) {y : X} (hy : y ∈ K) (hy3 : orderOf y = 3)
    (hψ : ψ y0 = ⟨y, hy⟩) :
    Nat.card M * Nat.card ↥(W ⊓ centralizer ({y} : Set X)) ^ 4 ≤
      Nat.card W * Nat.card ↥(M ⊓ centralizer ({y} : Set X)) ^ 4 := by
  classical
  have hQc : ∀ a b : M ⧸ W.subgroupOf M, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have h := hcomm (b⁻¹ : M) (b⁻¹ : M).2 (a⁻¹ : M) (a⁻¹ : M).2
        have e : ((a * b)⁻¹ * (b * a) : M) = (b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ : M) := by group
        rw [e]
        simpa using h
  have hQ2 : ∀ q : M ⧸ W.subgroupOf M, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | _ a =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hsq a a.2
  have h1 := card_le_pow_four_GL hQc hQ2 ((rho hKM hKW).comp ψ)
  have e1 : Nat.card {q : M ⧸ W.subgroupOf M // ((rho hKM hKW).comp ψ) y0 q = q} =
      Nat.card ↥(fixQ hKM hKW ⟨y, hy⟩) := by
    rw [MonoidHom.comp_apply, hψ]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun q => Iff.rfl)
  rw [e1] at h1
  have hy3' : y ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy3] at h
  have h3 : ¬ 3 ∣ Nat.card W := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hW
    rw [hn]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hc := card_fix_mul hKM hKW hWM hy hy3' h3
  have hM : Nat.card M = Nat.card (M ⧸ W.subgroupOf M) * Nat.card W := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (W.subgroupOf M)]
    exact congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv)
  rw [hM]
  calc Nat.card (M ⧸ W.subgroupOf M) * Nat.card W * Nat.card ↥(W ⊓ centralizer ({y} : Set X)) ^ 4
      ≤ Nat.card ↥(fixQ hKM hKW ⟨y, hy⟩) ^ 4 * Nat.card W *
        Nat.card ↥(W ⊓ centralizer ({y} : Set X)) ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ = Nat.card W * (Nat.card ↥(W ⊓ centralizer ({y} : Set X)) *
        Nat.card ↥(fixQ hKM hKW ⟨y, hy⟩)) ^ 4 := by ring
    _ = Nat.card W * Nat.card ↥(M ⊓ centralizer ({y} : Set X)) ^ 4 := by rw [hc]

end CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix
