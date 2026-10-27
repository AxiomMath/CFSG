module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.TheoremA
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Hyp11Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.DihedralStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma22
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Section 4, equation (10): the PSL₂ data package

This module constructs the `BenderGlauberman.Hyp11` structure for the linear
(PSL₂) branch from the `CentralizerSetup` bridge, identifies its centralizer
`H = C_G(t) = c.H`, and derives the two structural identities consumed by
`secondCase_equation10_of_theorem_A`:

* the index-tower factorization
  `(bg.H.index : ℚ) * (u * p0) = q * k' * (w.M.index : ℚ)`, obtained from
  the equation-(8) datum `|U : U ∩ M| = u · p0` together with the
  equation-(9) datum `S ≤ M` (the source's `S ⊆ E ⊆ M`) and the preamble
  `H = U · S`; and
* the parameter identification `bg.k = k * u * p0`, obtained from the
  dihedral counting `2·|H : C_H(r)| = |S0|·|U : C_U(r)|` for every
  reflection `r ∈ S \ S0` (equation (5): `C_U(r) = B`), the equation-(2)
  decomposition `U ∩ M = K · B` with `K ∩ B = 1`, the equation-(8) datum
  `|U : U ∩ M| = u · p0`, and the equation-(9) datum
  `k = |K| · |S0|`.

The exported rational inequality
`q * k' * (w.M.index : ℚ) ≤ 6 * k ^ 2 * u ^ 3 * p0 ^ 3` is then obtained by
applying the existing `secondCase_equation10_of_theorem_A`; equation (10)
is never assumed.

The `K`, `B`, `s` inputs are the equation-(1)--(3) data supplied by
`secondCase_fitting_involution_decomposition`; the explicit hypotheses
`hUInter`, `hSleM`, `hMInter`, `hk` are the natural subgroup/index data of
equations (8) and (9).
-/

noncomputable section

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

namespace CFSG.GorensteinWalter

universe u

section DihedralInfra

variable {G : Type u} [Group G] [Finite G]
variable (c : BenderGlauberman.Hyp11 G)

/-- `U ≤ H` (`U = O(H)`). -/
private lemma U_le_H_local (c : BenderGlauberman.Hyp11 G) : c.U ≤ c.H := by
  intro x hx
  have huU : x ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [BenderGlauberman.Hyp11.U, oddCoreOf] using hx
  exact SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU

/-- `U ∩ S = 1`: the odd core of `H` meets the Sylow 2-subgroup trivially. -/
private lemma U_inter_S_eq_bot_local (c : BenderGlauberman.Hyp11 G) {x : G}
    (hxU : x ∈ c.U) (hxS : x ∈ (c.S : Subgroup G)) : x = 1 := by
  classical
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [BenderGlauberman.Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  by_contra hx1
  have hordU : orderOf x ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨x, hxU⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨x, hxU⟩ : ↥c.U)]
    have hxU' : orderOf (⟨x, hxU⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨x, hxU⟩)
    rwa [← Nat.card_eq_fintype_card] at hxU'
  have hordS : orderOf x ∣ Nat.card (c.S : Subgroup G) := by
    change orderOf ((c.S : Subgroup G).subtype (⟨x, hxS⟩ : ↥(c.S : Subgroup G))) ∣
      Nat.card (c.S : Subgroup G)
    rw [orderOf_injective (c.S : Subgroup G).subtype
      (Subgroup.subtype_injective (c.S : Subgroup G)) (⟨x, hxS⟩ : ↥(c.S : Subgroup G))]
    have hxS' : orderOf (⟨x, hxS⟩ : ↥(c.S : Subgroup G)) ∣
        Fintype.card ↥(c.S : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S : Subgroup G)) (x := ⟨x, hxS⟩)
    rwa [← Nat.card_eq_fintype_card] at hxS'
  have hpow : orderOf x ∣ 2 * 2 ^ c.m := by
    rw [← BenderGlauberman.S_nat_card c]
    exact hordS
  have hpow' : orderOf x ∣ 2 ^ (c.m + 1) := by
    rw [pow_succ]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpow
  have hcop' : Nat.Coprime (2 ^ (c.m + 1)) (Nat.card ↥c.U) := hcop.pow_left _
  have h1' : orderOf x = 1 := by
    have hdvd : orderOf x ∣ 1 := by
      rw [← hcop'.gcd_eq_one]
      exact Nat.dvd_gcd hpow' hordU
    exact Nat.dvd_one.mp hdvd
  exact hx1 (orderOf_eq_one_iff.mp h1')

/-- Every element of `S` normalizes `U = O(H)` (from `U ⊴ H` and `S ≤ H`). -/
private lemma S_le_normalizer_U_local (c : BenderGlauberman.Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact BenderGlauberman.U_normal_in_H c (BenderGlauberman.S_le_H c hs) hu
  · intro hsu
    have hs' : s⁻¹ ∈ c.H := c.H.inv_mem (BenderGlauberman.S_le_H c hs)
    have h1 := BenderGlauberman.U_normal_in_H c hs' hsu
    have h2 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [h2] at h1

/-- `H = U·S` (set product, from `H_eq_US` and `S ≤ N_G(U)`). -/
private lemma H_eq_U_mul_S_local (c : BenderGlauberman.Hyp11 G) :
    (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
  rw [← c.H_eq_US]
  exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
    (S_le_normalizer_U_local c)

/-- Uniqueness of the `U·K`-decomposition (`U ∩ K = 1`). -/
private lemma U_mul_K_decomp_unique_local (c : BenderGlauberman.Hyp11 G) (K : Subgroup G)
    (hK : ∀ {x : G}, x ∈ c.U → x ∈ K → x = 1)
    {u₁ u₂ : ↥c.U} {s₁ s₂ : ↥K}
    (h : (u₁ : G) * (s₁ : G) = (u₂ : G) * (s₂ : G)) :
    u₁ = u₂ ∧ s₁ = s₂ := by
  have h1 : (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ = 1 := by
    calc
      (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ =
          (u₂ : G)⁻¹ * ((u₁ : G) * (s₁ : G)) * (s₂ : G)⁻¹ := by group
      _ = (u₂ : G)⁻¹ * ((u₂ : G) * (s₂ : G)) * (s₂ : G)⁻¹ := by rw [h]
      _ = 1 := by group
  have hU : (u₂ : G)⁻¹ * (u₁ : G) ∈ c.U := c.U.mul_mem (c.U.inv_mem u₂.2) u₁.2
  have hS : (s₂ : G) * (s₁ : G)⁻¹ ∈ K := K.mul_mem s₂.2 (K.inv_mem s₁.2)
  have hEq2 : (u₂ : G)⁻¹ * (u₁ : G) = (s₂ : G) * (s₁ : G)⁻¹ := by
    calc
      (u₂ : G)⁻¹ * (u₁ : G) =
          (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ * (s₂ : G) * (s₁ : G)⁻¹ := by group
      _ = 1 * (s₂ : G) * (s₁ : G)⁻¹ := by rw [h1]
      _ = (s₂ : G) * (s₁ : G)⁻¹ := by simp
  have hU2 : (u₂ : G)⁻¹ * (u₁ : G) ∈ K := by
    rw [hEq2]
    exact hS
  have h1' : (u₂ : G)⁻¹ * (u₁ : G) = 1 := hK hU hU2
  have hu12 : (u₁ : G) = (u₂ : G) := by
    calc
      (u₁ : G) = (u₂ : G) * ((u₂ : G)⁻¹ * (u₁ : G)) := by group
      _ = (u₂ : G) := by rw [h1']; simp
  constructor
  · apply Subtype.ext
    exact hu12
  · apply Subtype.ext
    calc
      (s₁ : G) = (u₁ : G)⁻¹ * ((u₁ : G) * (s₁ : G)) := by group
      _ = (u₂ : G)⁻¹ * ((u₂ : G) * (s₂ : G)) := by rw [h, hu12]
      _ = (s₂ : G) := by group

/-- The bijection `U × S ≃ H` (`H = U·S`, `U ∩ S = 1`). -/
private noncomputable def H_equiv_U_mul_S_local (c : BenderGlauberman.Hyp11 G) :
    ↥c.U × ↥(c.S : Subgroup G) ≃ ↥c.H := by
  classical
  refine Equiv.ofBijective (fun p : ↥c.U × ↥(c.S : Subgroup G) =>
    ⟨(p.1 : G) * (p.2 : G), c.H.mul_mem (U_le_H_local c p.1.2) (BenderGlauberman.S_le_H c p.2.2)⟩) ⟨?_, ?_⟩
  · intro p₁ p₂ h
    rcases U_mul_K_decomp_unique_local c (c.S : Subgroup G)
      (fun hxU hxK => U_inter_S_eq_bot_local c hxU hxK)
      (by exact congrArg (fun z : ↥c.H => (z : G)) h) with ⟨hu, hs⟩
    ext
    · exact congrArg (fun z : ↥c.U => (z : G)) hu
    · exact congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hs
  · intro x
    have hx : (x : G) ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
      rw [← H_eq_U_mul_S_local c]
      exact x.2
    rcases hx with ⟨u, hu, s, hs, hxeq⟩
    refine ⟨(⟨u, hu⟩, ⟨s, hs⟩), ?_⟩
    apply Subtype.ext
    exact hxeq

/-- `|H| = |U|·|S|`. -/
private lemma H_card_eq_local (c : BenderGlauberman.Hyp11 G) :
    Nat.card (↥c.H) = Nat.card ↥c.U * Nat.card (c.S : Subgroup G) := by
  simpa [Nat.card_prod] using (Nat.card_congr (H_equiv_U_mul_S_local c).symm)

/-- Membership in the centralizer inside a subgroup. -/
private lemma mem_centralizerIn_iff_local {G : Type u} [Group G] {X : Subgroup G} {s x : G} :
    x ∈ centralizerIn X s ↔ x ∈ X ∧ x * s = s * x := by
  unfold centralizerIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  simp [eq_comm]

/-- `C_H(t) = C_U(t)·C_S(t)` for `t ∈ S` (from `H = U·S` and `U ∩ S = 1`). -/
private lemma centralizer_H_eq_U_mul_S_local (c : BenderGlauberman.Hyp11 G) {ti : G}
    (htiS : ti ∈ (c.S : Subgroup G)) :
    (centralizerIn c.H ti : Set G) =
      (centralizerIn c.U ti : Set G) * (centralizerIn (c.S : Subgroup G) ti : Set G) := by
  ext x
  constructor
  · intro hx
    have hxH : x ∈ c.H := ((mem_centralizerIn_iff_local (X := c.H) (s := ti)).1 hx).1
    have hxU : (x : G) ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
      rw [← H_eq_U_mul_S_local c]
      exact hxH
    rcases hxU with ⟨u, huU, s', hsS, hxs⟩
    have hxcomm : (x : G) * ti = ti * (x : G) :=
      ((mem_centralizerIn_iff_local (X := c.H) (s := ti)).1 hx).2
    have h1 : (u : G) * (s' * ti) = ti * (u : G) * s' := by
      calc
        (u : G) * (s' * ti) = ((u : G) * s') * ti := by group
        _ = (x : G) * ti := by rw [← hxs]
        _ = ti * (x : G) := hxcomm
        _ = ti * ((u : G) * s') := by rw [← hxs]
        _ = ti * (u : G) * s' := by group
    have h2 : (u : G) * (s' * ti * s'⁻¹) * (u : G)⁻¹ = ti := by
      calc
        (u : G) * (s' * ti * s'⁻¹) * (u : G)⁻¹ =
            ((u : G) * (s' * ti) * s'⁻¹) * (u : G)⁻¹ := by group
        _ = ((ti * (u : G) * s') * s'⁻¹) * (u : G)⁻¹ := by rw [h1]
        _ = ti := by group
    let a : G := s' * ti * s'⁻¹
    have haS : a ∈ (c.S : Subgroup G) := by
      dsimp [a]
      simpa [mul_assoc] using
        ((c.S : Subgroup G).mul_mem hsS
          ((c.S : Subgroup G).mul_mem htiS ((c.S : Subgroup G).inv_mem hsS)))
    have h3 : (u : G) * a * (u : G)⁻¹ * a⁻¹ ∈ c.U := by
      have h1' : a * (u : G)⁻¹ * a⁻¹ ∈ c.U :=
        BenderGlauberman.U_normal_in_H c (BenderGlauberman.S_le_H c haS) (c.U.inv_mem huU)
      have hEq : (u : G) * a * (u : G)⁻¹ * a⁻¹ =
          (u : G) * (a * (u : G)⁻¹ * a⁻¹) := by group
      rw [hEq]
      exact c.U.mul_mem huU h1'
    have hts : ti * a⁻¹ ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem htiS ((c.S : Subgroup G).inv_mem haS)
    have htsU : ti * a⁻¹ ∈ c.U := by
      rw [← h2]
      exact h3
    have hta : ti * a⁻¹ = 1 := U_inter_S_eq_bot_local c htsU hts
    have haeq : a = ti := by
      have ha1 : a⁻¹ = ti⁻¹ := by
        calc
          a⁻¹ = ti⁻¹ * (ti * a⁻¹) := by group
          _ = ti⁻¹ := by rw [hta]; simp
      calc
        a = (a⁻¹)⁻¹ := by simp
        _ = (ti⁻¹)⁻¹ := by rw [ha1]
        _ = ti := by simp
    have hs'comm : s' * ti = ti * s' := by
      have ha' : s' * ti * s'⁻¹ = ti := haeq
      calc
        s' * ti = s' * ti * s'⁻¹ * s' := by group
        _ = ti * s' := by rw [ha']
    have hucomm : (u : G) * ti = ti * (u : G) := by
      have h2' : (u : G) * ti * (u : G)⁻¹ = ti := by
        change (u : G) * a * (u : G)⁻¹ = ti at h2
        rwa [haeq] at h2
      calc
        (u : G) * ti = (u : G) * ti * (u : G)⁻¹ * (u : G) := by group
        _ = ti * (u : G) := by rw [h2']
    refine ⟨u, ?_, s', ?_, hxs⟩
    · exact (mem_centralizerIn_iff_local (X := c.U) (s := ti)).mpr ⟨huU, hucomm⟩
    · exact (mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).mpr
        ⟨hsS, hs'comm⟩
  · intro hx
    rcases hx with ⟨u, huC, s', hsC, hxs⟩
    have huU : (u : G) ∈ c.U := ((mem_centralizerIn_iff_local (X := c.U) (s := ti)).1 huC).1
    have hsS : (s' : G) ∈ (c.S : Subgroup G) :=
      ((mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).1 hsC).1
    have hxH : (x : G) ∈ c.H := by
      simpa [hxs] using c.H.mul_mem (U_le_H_local c huU) (BenderGlauberman.S_le_H c hsS)
    have hxcomm : (x : G) * ti = ti * (x : G) := by
      have hucomm := ((mem_centralizerIn_iff_local (X := c.U) (s := ti)).1 huC).2
      have hscomm := ((mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).1 hsC).2
      have hmain : (u : G) * s' * ti = ti * ((u : G) * s') := by
        calc
          (u : G) * s' * ti = (u : G) * (s' * ti) := by group
          _ = (u : G) * (ti * s') := by rw [hscomm]
          _ = (u : G) * ti * s' := by group
          _ = ti * (u : G) * s' := by rw [hucomm]
          _ = ti * ((u : G) * s') := by group
      simpa [hxs] using hmain
    exact (mem_centralizerIn_iff_local (X := c.H) (s := ti)).mpr ⟨hxH, hxcomm⟩

/-- The bijection `C_U(t) × C_S(t) ≃ C_H(t)`. -/
private noncomputable def centralizer_H_equiv_local (c : BenderGlauberman.Hyp11 G) {ti : G}
    (htiS : ti ∈ (c.S : Subgroup G)) :
    ↥(centralizerIn c.U ti) × ↥(centralizerIn (c.S : Subgroup G) ti) ≃
      ↥(centralizerIn c.H ti) := by
  classical
  refine Equiv.ofBijective
    (fun p : ↥(centralizerIn c.U ti) × ↥(centralizerIn (c.S : Subgroup G) ti) =>
      ⟨(p.1 : G) * (p.2 : G), ?_⟩) ⟨?_, ?_⟩
  · have huU : (p.1 : G) ∈ c.U :=
      ((mem_centralizerIn_iff_local (X := c.U) (s := ti)).1 p.1.2).1
    have hsS : (p.2 : G) ∈ (c.S : Subgroup G) :=
      ((mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).1 p.2.2).1
    have hucomm := ((mem_centralizerIn_iff_local (X := c.U) (s := ti)).1 p.1.2).2
    have hscomm := ((mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).1 p.2.2).2
    refine (mem_centralizerIn_iff_local (X := c.H) (s := ti)).mpr ⟨?_, ?_⟩
    · exact c.H.mul_mem (U_le_H_local c huU) (BenderGlauberman.S_le_H c hsS)
    · calc
        (p.1 : G) * (p.2 : G) * ti = (p.1 : G) * ((p.2 : G) * ti) := by group
        _ = (p.1 : G) * (ti * (p.2 : G)) := by rw [hscomm]
        _ = (p.1 : G) * ti * (p.2 : G) := by group
        _ = ti * (p.1 : G) * (p.2 : G) := by rw [hucomm]
        _ = ti * ((p.1 : G) * (p.2 : G)) := by group
  · intro p₁ p₂ h
    have hu₁ : (p₁.1 : G) ∈ c.U :=
      ((mem_centralizerIn_iff_local (X := c.U) (s := ti)).1 p₁.1.2).1
    have hu₂ : (p₂.1 : G) ∈ c.U :=
      ((mem_centralizerIn_iff_local (X := c.U) (s := ti)).1 p₂.1.2).1
    have hs₁ : (p₁.2 : G) ∈ (c.S : Subgroup G) :=
      ((mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).1 p₁.2.2).1
    have hs₂ : (p₂.2 : G) ∈ (c.S : Subgroup G) :=
      ((mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).1 p₂.2.2).1
    rcases U_mul_K_decomp_unique_local c (c.S : Subgroup G)
      (fun hxU hxK => U_inter_S_eq_bot_local c hxU hxK)
      (u₁ := ⟨(p₁.1 : G), hu₁⟩) (u₂ := ⟨(p₂.1 : G), hu₂⟩)
      (s₁ := ⟨(p₁.2 : G), hs₁⟩) (s₂ := ⟨(p₂.2 : G), hs₂⟩) (by
        simpa using congrArg (fun z : ↥(centralizerIn c.H ti) => (z : G)) h) with ⟨hu, hs⟩
    ext
    · exact congrArg (fun z : ↥c.U => (z : G)) hu
    · exact congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hs
  · intro x
    have hx : (x : G) ∈ (centralizerIn c.U ti : Set G) *
        (centralizerIn (c.S : Subgroup G) ti : Set G) := by
      rw [← centralizer_H_eq_U_mul_S_local c htiS]
      exact x.2
    rcases hx with ⟨u, huC, s, hsC, hxeq⟩
    refine ⟨(⟨u, huC⟩, ⟨s, hsC⟩), ?_⟩
    apply Subtype.ext
    exact hxeq

/-- `|C_H(t)| = |C_U(t)|·|C_S(t)|`. -/
private lemma centralizer_H_card_local (c : BenderGlauberman.Hyp11 G) {ti : G}
    (htiS : ti ∈ (c.S : Subgroup G)) :
    Nat.card (↥(centralizerIn c.H ti)) =
      Nat.card (↥(centralizerIn c.U ti)) *
        Nat.card (↥(centralizerIn (c.S : Subgroup G) ti)) := by
  simpa [Nat.card_prod] using (Nat.card_congr (centralizer_H_equiv_local c htiS).symm)

/-- Any element of `S \ S0` inverts every element of `S0` (dihedral structure). -/
private lemma reflection_inverts_S0_local (c : BenderGlauberman.Hyp11 G) {r : G}
    (hrS : r ∈ (c.S : Subgroup G)) (hrS0 : r ∉ (c.S0 : Subgroup G))
    {x : G} (hx : x ∈ (c.S0 : Subgroup G)) :
    r * x * r⁻¹ = x⁻¹ := by
  classical
  let K : Subgroup (↥(c.S : Subgroup G)) := (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hwK : (⟨r * c.s, c.S.mul_mem hrS c.s_mem_S⟩ : ↥(c.S : Subgroup G)) ∈ K := by
    have hiff := Subgroup.mul_mem_iff_of_index_two (BenderGlauberman.S0_index c)
      (G := ↥(c.S : Subgroup G)) (H := K) (a := ⟨r, hrS⟩) (b := ⟨c.s, c.s_mem_S⟩)
    change (⟨r, hrS⟩ * ⟨c.s, c.s_mem_S⟩ : ↥(c.S : Subgroup G)) ∈ K
    rw [hiff]
    dsimp [K]
    simp [Subgroup.mem_subgroupOf, hrS0, c.s_not_mem_S0]
  have hw : r * c.s ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp hwK
  let w : ↥(c.S0 : Subgroup G) := ⟨r * c.s, hw⟩
  have hrs : r = (w : G) * c.s := by
    calc
      r = r * (c.s * c.s) := by
        have hs2 : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
        rw [hs2]
        simp
      _ = (r * c.s) * c.s := by group
      _ = (w : G) * c.s := rfl
  have hxs : (c.s * x * c.s⁻¹) = x⁻¹ := BenderGlauberman.s_inverts_S0 c hx
  have hxw : (w : G) * x * (w : G)⁻¹ = x := by
    let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
    let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
    have hcomm : w * ⟨x, hx⟩ = ⟨x, hx⟩ * w := mul_comm w ⟨x, hx⟩
    have hval : (w : G) * x = x * (w : G) :=
      congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hcomm
    calc
      (w : G) * x * (w : G)⁻¹ = (x * (w : G)) * (w : G)⁻¹ := by rw [hval]
      _ = x := by group
  calc
    r * x * r⁻¹ = ((w : G) * c.s) * x * ((w : G) * c.s)⁻¹ := by rw [hrs]
    _ = (w : G) * (c.s * x * c.s⁻¹) * (w : G)⁻¹ := by group
    _ = (w : G) * x⁻¹ * (w : G)⁻¹ := by rw [hxs]
    _ = x⁻¹ := by
      let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
      let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
      have hcomm : w * ⟨x⁻¹, (c.S0 : Subgroup G).inv_mem hx⟩ =
          ⟨x⁻¹, (c.S0 : Subgroup G).inv_mem hx⟩ * w := mul_comm w _
      have hval : (w : G) * x⁻¹ = x⁻¹ * (w : G) :=
        congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hcomm
      rw [hval]
      group

/-- The centralizer of `ti ∈ S \ S0` in `S` has exactly four elements:
`{1, t, ti, t·ti}`. -/
private lemma C_S_card_eq_four_local (c : BenderGlauberman.Hyp11 G) {ti : G}
    (htiS : ti ∈ (c.S : Subgroup G)) (htiS0 : ti ∉ (c.S0 : Subgroup G))
    (hti_ne : ti ≠ 1) (hti2 : ti * ti = 1) :
    Nat.card (↥(centralizerIn (c.S : Subgroup G) ti)) = 4 := by
  classical
  let Kf : Finset (↥(c.S : Subgroup G)) :=
    {1, ⟨c.t, c.S0_le_S c.t_mem_S0⟩, ⟨ti, htiS⟩,
      ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩}
  let K0 : Subgroup (↥(c.S : Subgroup G)) := (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hmem : ∀ y : ↥(c.S : Subgroup G),
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti ↔
        y = 1 ∨ y = ⟨c.t, c.S0_le_S c.t_mem_S0⟩ ∨ y = ⟨ti, htiS⟩ ∨
          y = ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩ := by
    intro y
    constructor
    · intro hy
      have hxcomm : (y : G) * ti = ti * (y : G) :=
        ((mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).1 hy).2
      by_cases hyS0 : (y : G) ∈ (c.S0 : Subgroup G)
      · have hyinv : (y : G) = (y : G)⁻¹ := by
          have hti_eq_inv : ti = ti⁻¹ := eq_inv_iff_mul_eq_one.mpr hti2
          have hri : ti * (y : G) * ti⁻¹ = (y : G)⁻¹ :=
            reflection_inverts_S0_local c htiS htiS0 hyS0
          calc
            (y : G) = (y : G) * 1 := by simp
            _ = (y : G) * (ti * ti) := by rw [← hti2]
            _ = (y : G) * ti * ti := by group
            _ = ti * (y : G) * ti := by rw [hxcomm]
            _ = ti * (y : G) * ti⁻¹ := by rw [← hti_eq_inv]
            _ = (y : G)⁻¹ := hri
        have hy2 : (y : G) * (y : G) = 1 := by
          calc
            (y : G) * (y : G) = (y : G) * (y : G)⁻¹ := by rw [← hyinv]
            _ = 1 := by simp
        have hy2' : (⟨(y : G), hyS0⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
          apply Subtype.ext
          simpa [Subgroup.coe_pow, pow_two] using hy2
        rcases (BenderGlauberman.S0_sq_eq_one_iff c (x := ⟨(y : G), hyS0⟩)).1 hy2' with h1 | ht
        · left
          exact Subtype.ext_iff.2 (congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) h1)
        · right
          left
          exact Subtype.ext_iff.2 (congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) ht)
      · have hytiK0 : (⟨(y : G) * ti, c.S.mul_mem y.2 htiS⟩ : ↥(c.S : Subgroup G)) ∈ K0 := by
          have hiff := Subgroup.mul_mem_iff_of_index_two (BenderGlauberman.S0_index c)
            (G := ↥(c.S : Subgroup G)) (H := K0) (a := ⟨(y : G), y.2⟩) (b := ⟨ti, htiS⟩)
          change (⟨(y : G), y.2⟩ * ⟨ti, htiS⟩ : ↥(c.S : Subgroup G)) ∈ K0
          rw [hiff]
          dsimp [K0]
          simp [Subgroup.mem_subgroupOf, hyS0, htiS0]
        have hyti : (y : G) * ti ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp hytiK0
        let r : ↥(c.S0 : Subgroup G) := ⟨(y : G) * ti, hyti⟩
        have hyr : (y : G) = (r : G) * ti := by
          calc
            (y : G) = (y : G) * 1 := by simp
            _ = (y : G) * (ti * ti) := by rw [← hti2]
            _ = (y : G) * ti * ti := by group
            _ = (r : G) * ti := rfl
        have hr2 : (r : G) * (r : G) = 1 := by
          have hri : ti * (r : G) * ti⁻¹ = (r : G)⁻¹ :=
            reflection_inverts_S0_local c htiS htiS0 r.2
          have hr_eq : (r : G) = (r : G)⁻¹ := by
            have hti_eq_inv : ti = ti⁻¹ := eq_inv_iff_mul_eq_one.mpr hti2
            calc
              (r : G) = (y : G) * ti := rfl
              _ = ti * (y : G) := hxcomm
              _ = ti * ((r : G) * ti) := by rw [hyr]
              _ = ti * (r : G) * ti := by group
              _ = ti * (r : G) * ti⁻¹ := by rw [← hti_eq_inv]
              _ = (r : G)⁻¹ := hri
          calc
            (r : G) * (r : G) = (r : G) * (r : G)⁻¹ := by rw [← hr_eq]
            _ = 1 := by simp
        have hr2' : (⟨(r : G), r.2⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
          apply Subtype.ext
          simpa [Subgroup.coe_pow, pow_two] using hr2
        rcases (BenderGlauberman.S0_sq_eq_one_iff c (x := ⟨(r : G), r.2⟩)).1 hr2' with hr1 | hrt
        · right
          right
          left
          exact Subtype.ext_iff.2 (by
          calc
            (y : G) = (r : G) * ti := hyr
            _ = 1 * ti := by
              rw [congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hr1]
              simp
            _ = ti := by simp)
        · right
          right
          right
          exact Subtype.ext_iff.2 (by
          calc
            (y : G) = (r : G) * ti := hyr
            _ = c.t * ti := by
              rw [congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hrt])
    · intro hy
      rcases hy with hy1 | hy2
      · subst hy1
        exact (mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).mpr
          ⟨by simp, by simp⟩
      · rcases hy2 with hy2a | hy2b
        · subst hy2a
          exact (mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).mpr ⟨
            c.S0_le_S c.t_mem_S0, by
              have h := BenderGlauberman.S_conj_t c htiS
              calc
                c.t * ti = (ti * c.t * ti⁻¹) * ti := by rw [h]
                _ = ti * c.t := by group⟩
        · rcases hy2b with hy2c | hy2d
          · subst hy2c
            exact (mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).mpr ⟨htiS, by
              simp [hti2]⟩
          · subst hy2d
            exact (mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).mpr ⟨
              c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS, by
                calc
                  (c.t * ti) * ti = c.t * (ti * ti) := by group
                  _ = c.t := by rw [hti2]; simp
                  _ = ti * (c.t * ti) := by
                    have h := BenderGlauberman.S_conj_t c htiS
                    calc
                      c.t = ti * c.t * ti⁻¹ := by rw [h]
                      _ = ti * c.t * ti := by
                        have hti_eq_inv : ti = ti⁻¹ := eq_inv_iff_mul_eq_one.mpr hti2
                        rw [← hti_eq_inv]
                      _ = ti * (c.t * ti) := by group⟩
  have hKf : Kf = Finset.univ.filter (fun y : ↥(c.S : Subgroup G) =>
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti) := by
    ext y
    simp [Kf, hmem y]
  have hKcard : Kf.card = 4 := by
    -- pairwise distinctness of the four elements
    have htS : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : ↥(c.S : Subgroup G)) ≠ 1 := by
      intro h
      exact c.t_involution.1 (by simpa using congrArg Subtype.val h)
    have htiS1 : (⟨ti, htiS⟩ : ↥(c.S : Subgroup G)) ≠ 1 := by
      intro h
      exact hti_ne (by simpa using congrArg Subtype.val h)
    have htt1 : (⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩ : ↥(c.S : Subgroup G)) ≠ 1 := by
      intro h
      have hval : c.t * ti = 1 := by simpa using congrArg Subtype.val h
      have hti_t : ti = c.t := by
        calc
          ti = c.t⁻¹ * (c.t * ti) := by group
          _ = c.t⁻¹ := by rw [hval]; simp
          _ = c.t := by
            have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
            exact (eq_inv_iff_mul_eq_one.mpr ht2).symm
      apply htiS0
      rw [hti_t]
      exact c.t_mem_S0
    have ht_ne_ti : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : ↥(c.S : Subgroup G)) ≠ ⟨ti, htiS⟩ := by
      intro h
      have hval : c.t = ti := by simpa using congrArg Subtype.val h
      exact htiS0 (by simpa [← hval] using c.t_mem_S0)
    have ht_ne_tti : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : ↥(c.S : Subgroup G)) ≠
        ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩ := by
      intro h
      have hval : c.t = c.t * ti := by simpa using congrArg Subtype.val h
      have hti1 : ti = 1 := by
        calc
          ti = c.t⁻¹ * (c.t * ti) := by group
          _ = c.t⁻¹ * c.t := by rw [← hval]
          _ = 1 := by simp
      exact hti_ne hti1
    have hti_ne_tti : (⟨ti, htiS⟩ : ↥(c.S : Subgroup G)) ≠
        ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩ := by
      intro h
      have hval : ti = c.t * ti := by simpa using congrArg Subtype.val h
      have ht1 : c.t = 1 := by
        have hval' : ti * ti = (c.t * ti) * ti := by rw [← hval]
        have hR : (c.t * ti) * ti = c.t := by
          calc
            (c.t * ti) * ti = c.t * (ti * ti) := by group
            _ = c.t := by rw [hti2]; simp
        calc
          c.t = (c.t * ti) * ti := hR.symm
          _ = ti * ti := by rw [← hval']
          _ = 1 := hti2
      exact c.t_involution.1 ht1
    change ({1, ⟨c.t, c.S0_le_S c.t_mem_S0⟩, ⟨ti, htiS⟩,
      ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩} :
      Finset (↥(c.S : Subgroup G))).card = 4
    have h1 : (1 : ↥(c.S : Subgroup G)) ∉
        ({⟨c.t, c.S0_le_S c.t_mem_S0⟩, ⟨ti, htiS⟩,
          ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩} :
      Finset (↥(c.S : Subgroup G))) := by
      simp [Ne.symm htS, Ne.symm htiS1, Ne.symm htt1]
    rw [Finset.card_insert_of_notMem h1]
    have h2 : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : ↥(c.S : Subgroup G)) ∉
        ({⟨ti, htiS⟩, ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩} :
          Finset (↥(c.S : Subgroup G))) := by
      simp [ht_ne_ti, ht_ne_tti]
    rw [Finset.card_insert_of_notMem h2]
    have h3 : (⟨ti, htiS⟩ : ↥(c.S : Subgroup G)) ∉
        ({⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩} :
          Finset (↥(c.S : Subgroup G))) := by
      simp [hti_ne_tti]
    rw [Finset.card_insert_of_notMem h3]
    simp
  have hcardF : (Finset.univ.filter (fun y : ↥(c.S : Subgroup G) =>
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti)).card = 4 := by
    rw [← hKf]
    exact hKcard
  have hcardSub : Fintype.card {y : ↥(c.S : Subgroup G) //
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti} = 4 := by
    simpa [Fintype.card_subtype] using hcardF
  have heq : {y : ↥(c.S : Subgroup G) //
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti} ≃
      ↥(centralizerIn (c.S : Subgroup G) ti) := by
    refine (Equiv.subtypeSubtypeEquivSubtype
      (p := fun x : G => x ∈ (c.S : Subgroup G))
      (q := fun x : G => x ∈ centralizerIn (c.S : Subgroup G) ti) ?_)
    intro x hx
    exact ((mem_centralizerIn_iff_local (X := (c.S : Subgroup G)) (s := ti)).1 hx).1
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr heq).symm.trans hcardSub

/-- `2·|H : C_H(r)| = |S0|·|U : C_U(r)|` for every reflection `r ∈ S \ S0`
(the paper's `k₁ = |H : C_H(t₁)| = ½|S0|·|U : B₁|`). -/
private lemma two_mul_reflection_index (c : BenderGlauberman.Hyp11 G) {r : G}
    (hrS : r ∈ (c.S : Subgroup G)) (hrS0 : r ∉ (c.S0 : Subgroup G))
    (hri : IsInvolution r) :
    2 * ((centralizerIn c.H r).subgroupOf c.H).index =
      Nat.card (c.S0 : Subgroup G) *
        ((centralizerIn c.U r).subgroupOf c.U).index := by
  classical
  have hCH : Nat.card (↥(centralizerIn c.H r)) =
      4 * Nat.card (↥(centralizerIn c.U r)) := by
    rw [centralizer_H_card_local c hrS]
    rw [C_S_card_eq_four_local c hrS hrS0 hri.1 (by simpa [pow_two] using hri.2)]
    ring
  have hCHcard : Nat.card ↥((centralizerIn c.H r).subgroupOf c.H) =
      Nat.card ↥(centralizerIn c.H r) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := centralizerIn c.H r) (K := c.H) inf_le_left).toEquiv
  have hk1m : ((centralizerIn c.H r).subgroupOf c.H).index *
      Nat.card (↥(centralizerIn c.H r)) = Nat.card (↥c.H) := by
    have h := Subgroup.index_mul_card (H := (centralizerIn c.H r).subgroupOf c.H)
    rw [hCHcard] at h
    change ((centralizerIn c.H r).subgroupOf c.H).index *
      Nat.card (↥(centralizerIn c.H r)) = Nat.card (↥c.H)
    exact h
  have hB1card : Nat.card ↥((centralizerIn c.U r).subgroupOf c.U) =
      Nat.card ↥(centralizerIn c.U r) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := centralizerIn c.U r) (K := c.U) inf_le_left).toEquiv
  have hU : Nat.card ↥c.U =
      ((centralizerIn c.U r).subgroupOf c.U).index *
        Nat.card (↥(centralizerIn c.U r)) := by
    have h := Subgroup.index_mul_card (H := (centralizerIn c.U r).subgroupOf c.U)
    rw [hB1card] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hMain : ((centralizerIn c.H r).subgroupOf c.H).index *
      (4 * Nat.card (↥(centralizerIn c.U r))) =
      Nat.card ↥c.U * (2 * Nat.card (c.S0 : Subgroup G)) := by
    calc
      ((centralizerIn c.H r).subgroupOf c.H).index *
          (4 * Nat.card (↥(centralizerIn c.U r)))
          = ((centralizerIn c.H r).subgroupOf c.H).index *
              Nat.card (↥(centralizerIn c.H r)) := by rw [hCH]
      _ = Nat.card (↥c.H) := hk1m
      _ = Nat.card ↥c.U * Nat.card (c.S : Subgroup G) := H_card_eq_local c
      _ = Nat.card ↥c.U * (2 * Nat.card (c.S0 : Subgroup G)) := by
        rw [BenderGlauberman.S_nat_card c, BenderGlauberman.S0_nat_card c]
  have hMain' : ((centralizerIn c.H r).subgroupOf c.H).index *
      (4 * Nat.card (↥(centralizerIn c.U r))) =
      ((centralizerIn c.U r).subgroupOf c.U).index *
        Nat.card (↥(centralizerIn c.U r)) *
        (2 * Nat.card (c.S0 : Subgroup G)) := by
    rwa [hU] at hMain
  have hcancel : ((centralizerIn c.H r).subgroupOf c.H).index * 4 =
      ((centralizerIn c.U r).subgroupOf c.U).index * 2 *
        Nat.card (c.S0 : Subgroup G) := by
    have hb : Nat.card (↥(centralizerIn c.U r)) ≠ 0 := Nat.card_pos.ne'
    exact mul_left_cancel₀ hb (by
      calc
        Nat.card (↥(centralizerIn c.U r)) *
            (((centralizerIn c.H r).subgroupOf c.H).index * 4)
            = ((centralizerIn c.H r).subgroupOf c.H).index *
                (4 * Nat.card (↥(centralizerIn c.U r))) := by ring
        _ = ((centralizerIn c.U r).subgroupOf c.U).index *
              Nat.card (↥(centralizerIn c.U r)) *
              (2 * Nat.card (c.S0 : Subgroup G)) := hMain'
        _ = Nat.card (↥(centralizerIn c.U r)) *
              (((centralizerIn c.U r).subgroupOf c.U).index * 2 *
                Nat.card (c.S0 : Subgroup G)) := by ring)
  have h2 : 2 * (2 * ((centralizerIn c.H r).subgroupOf c.H).index) =
      2 * (Nat.card (c.S0 : Subgroup G) *
        ((centralizerIn c.U r).subgroupOf c.U).index) := by
    calc
      2 * (2 * ((centralizerIn c.H r).subgroupOf c.H).index)
          = ((centralizerIn c.H r).subgroupOf c.H).index * 4 := by ring
      _ = ((centralizerIn c.U r).subgroupOf c.U).index * 2 *
            Nat.card (c.S0 : Subgroup G) := hcancel
      _ = 2 * (Nat.card (c.S0 : Subgroup G) *
            ((centralizerIn c.U r).subgroupOf c.U).index) := by ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) h2

end DihedralInfra

/-! ## Product cardinality of a join of disjoint subgroups -/

/-- `|K ⊔ B| = |K|·|B|` when `B` normalizes `K` and `K ∩ B = 1`
(bijection `K × B ≃ K ⊔ B` via the product map). -/
private lemma natCard_sup_of_disjoint {G : Type u} [Group G] [Finite G]
    (K B : Subgroup G)
    (hBleN : B ≤ Subgroup.normalizer (K : Set G))
    (hKB : K ⊓ B = ⊥) :
    Nat.card (↥(K ⊔ B)) = Nat.card (↥K) * Nat.card (↥B) := by
  classical
  let f : ↥K × ↥B → ↥(K ⊔ B) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), by
      have hcoe : (↑(K ⊔ B) : Set G) = (K : Set G) * (B : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left K B hBleN
      change (p.1 : G) * (p.2 : G) ∈ (↑(K ⊔ B) : Set G)
      rw [hcoe]
      exact ⟨(p.1 : G), p.1.2, (p.2 : G), p.2.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro p q h
    have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val h
    have hK : (q.1 : G)⁻¹ * (p.1 : G) ∈ K := K.mul_mem (K.inv_mem q.1.2) p.1.2
    have hB : (q.2 : G) * (p.2 : G)⁻¹ ∈ B := B.mul_mem q.2.2 (B.inv_mem p.2.2)
    have hEq : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G)
            = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hval]
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hbot : (q.1 : G)⁻¹ * (p.1 : G) = 1 := by
      have hmem : (q.1 : G)⁻¹ * (p.1 : G) ∈ K ⊓ B := ⟨hK, by rwa [hEq]⟩
      rw [hKB] at hmem
      exact Subgroup.mem_bot.mp hmem
    apply Prod.ext
    · apply Subtype.ext
      calc
        (p.1 : G) = (q.1 : G) * ((q.1 : G)⁻¹ * (p.1 : G)) := by group
        _ = (q.1 : G) := by rw [hbot]; simp
    · apply Subtype.ext
      calc
        (p.2 : G) = ((q.2 : G) * (p.2 : G)⁻¹)⁻¹ * (q.2 : G) := by group
        _ = ((q.1 : G)⁻¹ * (p.1 : G))⁻¹ * (q.2 : G) := by rw [hEq]
        _ = (q.2 : G) := by rw [hbot]; simp
  have hsurj : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ (K : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K B hBleN]
      exact x.2
    rcases hx with ⟨a, haK, b, hbB, hxab⟩
    refine ⟨(⟨a, haK⟩, ⟨b, hbB⟩), ?_⟩
    apply Subtype.ext
    exact hxab
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  have hc : Nat.card (↥K × ↥B) = Nat.card (↥(K ⊔ B)) :=
    Nat.card_congr (Equiv.ofBijective f hbij)
  calc
    Nat.card (↥(K ⊔ B)) = Nat.card (↥K × ↥B) := hc.symm
    _ = Nat.card (↥K) * Nat.card (↥B) := by simp

/-- `|K ⊔ B : B| = |K|` when `B` normalizes `K` and `K ∩ B = 1`. -/
private lemma relIndex_of_sup_of_disjoint {G : Type u} [Group G] [Finite G]
    (K B : Subgroup G)
    (hBleN : B ≤ Subgroup.normalizer (K : Set G))
    (hKB : K ⊓ B = ⊥) :
    B.relIndex (K ⊔ B) = Nat.card (↥K) := by
  classical
  have hBsubJ : B ≤ K ⊔ B := le_sup_right
  have hJcard : Nat.card (↥(K ⊔ B)) = Nat.card (↥K) * Nat.card (↥B) :=
    natCard_sup_of_disjoint K B hBleN hKB
  have hcB : Nat.card (↥(B.subgroupOf (K ⊔ B))) = Nat.card (↥B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := B) (K := K ⊔ B) hBsubJ).toEquiv
  have hind : (B.subgroupOf (K ⊔ B)).index * Nat.card (↥B) =
      Nat.card (↥K) * Nat.card (↥B) := by
    calc
      (B.subgroupOf (K ⊔ B)).index * Nat.card (↥B)
          = (B.subgroupOf (K ⊔ B)).index * Nat.card (↥(B.subgroupOf (K ⊔ B))) := by
            rw [hcB]
      _ = Nat.card (↥(K ⊔ B)) := Subgroup.index_mul_card (H := B.subgroupOf (K ⊔ B))
      _ = Nat.card (↥K) * Nat.card (↥B) := hJcard
  have h' : (B.subgroupOf (K ⊔ B)).index = Nat.card (↥K) :=
    mul_right_cancel₀ (Nat.card_pos.ne') hind
  simpa [Subgroup.relIndex] using h'

/-! ## The exported data package -/

/-- Section 4 equation (10): the constructed Bender--Glauberman data for the
linear (PSL₂) branch.

`bg` is the `BenderGlauberman.Hyp11` structure supplied by the
`CentralizerSetup` bridge (`GorensteinWalter.Section2.Hyp11Bridge`), so
`bg.H = c.H` is the involution centralizer.  The two structural identities
are:

* `indexTower`: the index-tower factorization
  `(bg.H.index : ℚ) * (u * p0) = q * k' * (w.M.index : ℚ)`, and
* `bgK`: the identification `bg.k = k * u * p0`.

`equation10` is the rational inequality
`q * k' * (w.M.index : ℚ) ≤ 6 * k ^ 2 * u ^ 3 * p0 ^ 3` obtained by
applying `secondCase_equation10_of_theorem_A`; it is never assumed. -/
public structure SecondCaseLinearEquationTenData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (q k k' u p0 : ℚ) where
  bg : BenderGlauberman.Hyp11 G
  bg_H_eq : bg.H = c.H
  indexTower : (bg.H.index : ℚ) * (u * p0) = q * k' * (w.M.index : ℚ)
  bgK : (bg.k : ℚ) = k * u * p0
  hu : 0 < u
  hp0 : 0 < p0
  equation10 : q * k' * (w.M.index : ℚ) ≤ 6 * k ^ 2 * u ^ 3 * p0 ^ 3

/-- Constructor of the equation-(10) data package for the linear branch.

The `K`, `B`, `s` inputs are the equation-(1)--(3) data of
`secondCase_fitting_involution_decomposition`; the remaining hypotheses are
the natural subgroup/index data of equations (8) and (9):

* `hCU` is equation (5) in its reflection-uniform form: `C_U(r) = B` for
  every reflection `r ∈ S \ S0`;
* `hUInter` is the equation-(8) datum `|U : U ∩ M| = u · p0`;
* `hSleM` is the equation-(9) datum `S ⊆ E ⊆ M`;
* `hMInter` is the equation-(9) datum `|M : H ∩ M| = q · k'`;
* `hk` is the equation-(9) datum `k = |K| · |S0|`.
-/
public noncomputable def secondCase_linearEquationTenData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K B : Subgroup G) (s : d.E)
    {u p0 q k' k : ℕ}
    (hK_eq : (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hB_eq : B = centralizerIn (c.U ⊓ w.M) (s : G))
    (hjoin : K ⊔ B = c.U ⊓ w.M)
    (hsI : IsInvolution s)
    (hsH : (s : G) ∈ c.H)
    (hCU : ∀ r : G, r ∈ (c.S : Subgroup G) → r ∉ c.S0 →
      centralizerIn c.U r = B)
    (hUInter : (c.U ⊓ w.M).relIndex c.U = u * p0)
    (hSleM : (c.S : Subgroup G) ≤ w.M)
    (hMInter : (c.H ⊓ w.M).relIndex w.M = q * k')
    (hk : k = Nat.card K * Nat.card c.S0)
    (hu : 0 < u) (hp0 : 0 < p0) :
    SecondCaseLinearEquationTenData c w (q : ℚ) (k : ℚ) (k' : ℚ) (u : ℚ) (p0 : ℚ) := by
  classical
  -- the Bender--Glauberman structure from the Section 2 bridge
  let hbgExists := exists_benderGlaubermanHyp11_of_centralizerSetup_full c
    (fact_2_preamble_involutions_conjugate_proved hmin)
    (fact_2_preamble_H_eq_SU_proved hmin c)
  let bg : BenderGlauberman.Hyp11 G := Classical.choose hbgExists
  have hbgSpec := Classical.choose_spec hbgExists
  have hbgH : bg.H = c.H := hbgSpec.1
  have hSbg : (bg.S : Subgroup G) = (c.S : Subgroup G) := hbgSpec.2.1
  have hS0bg : bg.S0 = c.S0 := hbgSpec.2.2.1
  have hUeq : bg.U = c.U := by
    simpa [BenderGlauberman.Hyp11.U, CentralizerSetup.U] using congrArg oddCoreOf hbgH
  have hSleH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  have hUleH : c.U ≤ c.H := by
    intro x hx
    simpa [CentralizerSetup.U, oddCoreOf] using
      (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H) hx)
  -- `U` is normal in `H`
  have hUnormal : IsNormalIn c.U c.H := by
    refine ⟨hUleH, ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈ pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem p hp (⟨h, hh⟩ : c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  have hSleNU : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
    intro σ hσ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hUnormal.2 σ (hSleH hσ) x hx
    · intro hx'
      have h1 := hUnormal.2 σ⁻¹ (c.H.inv_mem (hSleH hσ)) (σ * x * σ⁻¹) hx'
      have h2 : σ⁻¹ * (σ * x * σ⁻¹) * (σ⁻¹)⁻¹ = x := by group
      rwa [h2] at h1
  -- `U ∩ S = 1`
  have hUdisS : c.U ⊓ (c.S : Subgroup G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxUbg : x ∈ bg.U := by
      rw [hUeq]
      exact hx.1
    exact U_inter_S_eq_bot_local bg hxUbg (by rw [hSbg]; exact hx.2)
  -- the oddness of `|U|` (used for `K ∩ B = 1`)
  have hcopU : Nat.Coprime 2 (Nat.card (↥c.U)) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [CentralizerSetup.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hUodd : Odd (Nat.card (↥c.U)) := Nat.coprime_two_left.mp hcopU
  have hXleU : c.U ⊓ w.M ≤ c.U := inf_le_left
  have hXodd : Odd (Nat.card (↥(c.U ⊓ w.M))) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hXleU)
  have hcopX : Nat.Coprime 2 (Nat.card (↥(c.U ⊓ w.M))) := Nat.coprime_two_left.mpr hXodd
  -- the equation-(2) data: `K ≤ X`, `B ≤ X`, `s` normalizes `X`
  have hKleX : K ≤ c.U ⊓ w.M := by
    intro x hx
    have hx' : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hK_eq]
      exact hx
    exact hx'.1
  have hBleX : B ≤ c.U ⊓ w.M := by
    rw [hB_eq]
    exact inf_le_left
  have hBleU : B ≤ c.U := hBleX.trans hXleU
  have hsIG : IsInvolution (s : G) := by
    constructor
    · intro h1
      apply hsI.1
      apply Subtype.ext
      exact h1
    · simpa [pow_two] using congrArg Subtype.val hsI.2
  have hsM : (s : G) ∈ w.M := d.E_component.1 s.2
  have hsXnorm : ∀ x : G, x ∈ c.U ⊓ w.M → (s : G) * x * (s : G)⁻¹ ∈ c.U ⊓ w.M := by
    intro x hx
    refine ⟨hUnormal.2 (s : G) hsH x hx.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)
  -- `K` is normal in `X` (Fact 1.5(iii): inverted subgroups are normal)
  have hKnormal : IsNormalIn K (c.U ⊓ w.M) :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal (s := (s : G)) hsIG hcopX hsXnorm
      (I := K) hK_eq).2.1
  have hBleNK : B ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hKnormal.2 x (hBleX hx) y hy
    · intro hy
      have hxinv : x⁻¹ ∈ c.U ⊓ w.M := (c.U ⊓ w.M).inv_mem (hBleX hx)
      have h := hKnormal.2 x⁻¹ hxinv (x * y * x⁻¹) hy
      simpa [mul_assoc] using h
  -- `K ∩ B = 1` (elements of `K` are inverted by `s`, elements of `B` fixed)
  have hKB : K ⊓ B = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxK : x ∈ K := hx.1
    have hxB : x ∈ B := hx.2
    have hxinv : (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
      have hx' : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
        rw [← hK_eq]
        exact hxK
      exact hx'.2
    have hxfix : (s : G) * x * (s : G)⁻¹ = x := by
      have hxs : x * (s : G) = (s : G) * x :=
        (mem_centralizerIn_iff_local (X := c.U ⊓ w.M) (s := (s : G)) (x := x)).mp
          (by rwa [hB_eq] at hxB) |>.2
      calc
        (s : G) * x * (s : G)⁻¹ = (x * (s : G)) * (s : G)⁻¹ := by rw [hxs]
        _ = x := by group
    have hx2 : x ^ 2 = 1 := by
      have hxeq : x⁻¹ = x := hxinv.symm.trans hxfix
      rw [pow_two]
      calc
        x * x = x * x⁻¹ := by rw [hxeq]
        _ = 1 := by simp
    have hxU : x ∈ c.U := (hKleX hxK).1
    let xU : ↥c.U := ⟨x, hxU⟩
    have hxU2 : xU ^ 2 = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow, pow_two] using hx2
    have hxU1 := eq_one_of_sq_eq_one_of_coprime_two (G := ↥c.U) hcopU hxU2
    exact congrArg Subtype.val hxU1
  -- `|X : B| = |K|` (from `X = K ⊔ B`, `K ∩ B = 1`)
  have hXBindex : B.relIndex (c.U ⊓ w.M) = Nat.card (↥K) := by
    have h' := relIndex_of_sup_of_disjoint K B hBleNK hKB
    rw [hjoin] at h'
    exact h'
  -- `|U : B| = (u · p0) · |K|` (tower through `X = U ∩ M`)
  have htower : B.relIndex (c.U ⊓ w.M) * (c.U ⊓ w.M).relIndex c.U = B.relIndex c.U :=
    Subgroup.relIndex_mul_relIndex B (c.U ⊓ w.M) c.U hBleX hXleU
  have hU_B : B.relIndex c.U = (u * p0) * Nat.card (↥K) := by
    calc
      B.relIndex c.U = B.relIndex (c.U ⊓ w.M) * (c.U ⊓ w.M).relIndex c.U := htower.symm
      _ = Nat.card (↥K) * (u * p0) := by rw [hXBindex, hUInter]
      _ = (u * p0) * Nat.card (↥K) := by ring
  -- the dihedral counting: `2·kᵢ = |S0|·|U : C_U(tᵢ)|`, with `C_U(tᵢ) = B`
  have h2k1 : 2 * bg.k1 = Nat.card (bg.S0 : Subgroup G) *
      ((centralizerIn bg.U bg.t1).subgroupOf bg.U).index :=
    two_mul_reflection_index bg bg.t1_mem_S bg.t1_not_mem_S0 bg.t1_involution
  have h2k2 : 2 * bg.k2 = Nat.card (bg.S0 : Subgroup G) *
      ((centralizerIn bg.U bg.t2).subgroupOf bg.U).index :=
    two_mul_reflection_index bg bg.t2_mem_S bg.t2_not_mem_S0 bg.t2_involution
  have hC1 : centralizerIn bg.U bg.t1 = B := by
    rw [hUeq]
    exact hCU bg.t1 (by simpa [hSbg] using bg.t1_mem_S)
      (by simpa [hS0bg] using bg.t1_not_mem_S0)
  have hC2 : centralizerIn bg.U bg.t2 = B := by
    rw [hUeq]
    exact hCU bg.t2 (by simpa [hSbg] using bg.t2_mem_S)
      (by simpa [hS0bg] using bg.t2_not_mem_S0)
  have h2k1B : 2 * bg.k1 = Nat.card (bg.S0 : Subgroup G) *
      ((B.subgroupOf bg.U).index) := by
    rw [hC1] at h2k1
    exact h2k1
  have h2k2B : 2 * bg.k2 = Nat.card (bg.S0 : Subgroup G) *
      ((B.subgroupOf bg.U).index) := by
    rw [hC2] at h2k2
    exact h2k2
  have hboth : 2 * bg.k = 2 * (Nat.card (bg.S0 : Subgroup G) *
      ((B.subgroupOf bg.U).index)) := by
    dsimp [BenderGlauberman.Hyp11.k]
    rw [mul_add, h2k1B, h2k2B]
    ring
  have hbgk1 : bg.k = Nat.card (bg.S0 : Subgroup G) *
      ((B.subgroupOf bg.U).index) :=
    mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hboth
  have hBrelU : (B.subgroupOf bg.U).index = B.relIndex c.U := by
    change B.relIndex bg.U = B.relIndex c.U
    rw [hUeq]
  have hbgk2 : bg.k = Nat.card c.S0 * B.relIndex c.U := by
    rw [hbgk1, hS0bg, hBrelU]
  -- `bg.k = k · u · p0` (equations (8) and (9))
  have hbgk3 : bg.k = k * u * p0 := by
    rw [hbgk2, hU_B, hk]
    ring
  have hbgkQ : (bg.k : ℚ) = (k : ℚ) * (u : ℚ) * (p0 : ℚ) := by
    exact_mod_cast hbgk3
  -- `|H : H ∩ M| = |U : U ∩ M|` (from `H = U·S`, `S ≤ M`)
  have hHUS_c : (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
    have h := H_eq_U_mul_S_local bg
    rw [hbgH, hUeq, hSbg] at h
    exact h
  have hSleNX : (c.S : Subgroup G) ≤ Subgroup.normalizer ((c.U ⊓ w.M : Subgroup G) : Set G) := by
    intro σ hσ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨hUnormal.2 σ (hSleH hσ) x hx.1,
        w.M.mul_mem (w.M.mul_mem (hSleM hσ) hx.2) (w.M.inv_mem (hSleM hσ))⟩
    · intro hx'
      have h1 := hUnormal.2 σ⁻¹ (c.H.inv_mem (hSleH hσ)) (σ * x * σ⁻¹) hx'.1
      have h2 : σ⁻¹ * (σ * x * σ⁻¹) * (σ⁻¹)⁻¹ = x := by group
      have hxU : x ∈ c.U := by
        rwa [h2] at h1
      have hxM : x ∈ w.M := by
        have h4 : σ⁻¹ * (σ * x * σ⁻¹) ∈ w.M :=
          w.M.mul_mem (w.M.inv_mem (hSleM hσ)) hx'.2
        have h5 : σ⁻¹ * (σ * x * σ⁻¹) * σ ∈ w.M := w.M.mul_mem h4 (hSleM hσ)
        have h6 : σ⁻¹ * (σ * x * σ⁻¹) * σ = x := by group
        rwa [h6] at h5
      exact ⟨hxU, hxM⟩
  have hXdisS : (c.U ⊓ w.M) ⊓ (c.S : Subgroup G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxUbg : x ∈ bg.U := by
      rw [hUeq]
      exact hx.1.1
    exact U_inter_S_eq_bot_local bg hxUbg (by rw [hSbg]; exact hx.2)
  have hHcapM_eq : (c.U ⊓ w.M) ⊔ (c.S : Subgroup G) = c.H ⊓ w.M := by
    apply le_antisymm
    · exact sup_le (inf_le_inf hUleH (le_refl w.M)) (le_inf hSleH hSleM)
    · intro x hx
      have hxH : x ∈ c.H := hx.1
      have hxM : x ∈ w.M := hx.2
      have hxUS : x ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
        rw [← hHUS_c]
        exact hxH
      rcases hxUS with ⟨u, huU, σ, hσS, hxus⟩
      have hσM : σ ∈ w.M := hSleM hσS
      have huM : u ∈ w.M := by
        have h1 : x * σ⁻¹ ∈ w.M := w.M.mul_mem hxM (w.M.inv_mem hσM)
        have h2 : u = x * σ⁻¹ := by
          calc
            u = (u * σ) * σ⁻¹ := by group
            _ = x * σ⁻¹ := congrArg (fun z : G => z * σ⁻¹) hxus
        rwa [← h2] at h1
      have huXM : u ∈ c.U ⊓ w.M := ⟨huU, huM⟩
      have hxprod : x ∈ ((c.U ⊓ w.M) : Set G) * ((c.S : Subgroup G) : Set G) :=
        ⟨u, huXM, σ, hσS, hxus⟩
      have hxjoin : x ∈ (c.U ⊓ w.M) ⊔ (c.S : Subgroup G) := by
        change x ∈ (↑((c.U ⊓ w.M) ⊔ (c.S : Subgroup G)) : Set G)
        rw [Subgroup.coe_mul_of_right_le_normalizer_left
          (c.U ⊓ w.M) (c.S : Subgroup G) hSleNX]
        exact hxprod
      exact hxjoin
  have hHcard : Nat.card (↥c.H) = Nat.card (↥c.U) * Nat.card (↥(c.S : Subgroup G)) := by
    calc
      Nat.card (↥c.H) = Nat.card (↥((c.S : Subgroup G) ⊔ c.U)) := by
        rw [fact_2_preamble_H_eq_SU_proved hmin c]
      _ = Nat.card (↥(c.U ⊔ (c.S : Subgroup G))) := by rw [sup_comm]
      _ = Nat.card (↥c.U) * Nat.card (↥(c.S : Subgroup G)) :=
        natCard_sup_of_disjoint c.U (c.S : Subgroup G) hSleNU hUdisS
  have hHMc : Nat.card (↥(c.H ⊓ w.M)) =
      Nat.card (↥(c.U ⊓ w.M)) * Nat.card (↥(c.S : Subgroup G)) := by
    calc
      Nat.card (↥(c.H ⊓ w.M)) = Nat.card (↥((c.U ⊓ w.M) ⊔ (c.S : Subgroup G))) := by
        rw [← hHcapM_eq]
      _ = Nat.card (↥(c.U ⊓ w.M)) * Nat.card (↥(c.S : Subgroup G)) :=
        natCard_sup_of_disjoint (c.U ⊓ w.M) (c.S : Subgroup G) hSleNX hXdisS
  have hIdx : (c.H ⊓ w.M).relIndex c.H = (c.U ⊓ w.M).relIndex c.U := by
    have hA : (c.H ⊓ w.M).relIndex c.H * Nat.card (↥(c.U ⊓ w.M)) = Nat.card (↥c.U) := by
      have h1 : ((c.H ⊓ w.M).subgroupOf c.H).index *
          Nat.card (↥(c.H ⊓ w.M)) = Nat.card (↥c.H) := by
        have h := Subgroup.index_mul_card (H := (c.H ⊓ w.M).subgroupOf c.H)
        have hc : Nat.card (↥((c.H ⊓ w.M).subgroupOf c.H)) = Nat.card (↥(c.H ⊓ w.M)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := c.H ⊓ w.M) (K := c.H)
            inf_le_left).toEquiv
        rwa [hc] at h
      have h1' := h1
      rw [hHcard, hHMc] at h1'
      have hcancelS : ((c.H ⊓ w.M).subgroupOf c.H).index *
          Nat.card (↥(c.U ⊓ w.M)) = Nat.card (↥c.U) :=
        mul_right_cancel₀ (Nat.card_pos.ne') (by
          calc
            ((c.H ⊓ w.M).subgroupOf c.H).index *
                Nat.card (↥(c.U ⊓ w.M)) * Nat.card (↥(c.S : Subgroup G))
                = ((c.H ⊓ w.M).subgroupOf c.H).index *
                    (Nat.card (↥(c.U ⊓ w.M)) * Nat.card (↥(c.S : Subgroup G))) := by ring
            _ = Nat.card (↥c.U) * Nat.card (↥(c.S : Subgroup G)) := h1')
      simpa [Subgroup.relIndex] using hcancelS
    have hB : (c.U ⊓ w.M).relIndex c.U * Nat.card (↥(c.U ⊓ w.M)) = Nat.card (↥c.U) := by
      have h := Subgroup.index_mul_card (H := (c.U ⊓ w.M).subgroupOf c.U)
      have hc : Nat.card (↥((c.U ⊓ w.M).subgroupOf c.U)) = Nat.card (↥(c.U ⊓ w.M)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := c.U ⊓ w.M) (K := c.U)
          hXleU).toEquiv
      rwa [hc] at h
    exact mul_right_cancel₀ (Nat.card_pos.ne') (by
      calc
        (c.H ⊓ w.M).relIndex c.H * Nat.card (↥(c.U ⊓ w.M))
            = Nat.card (↥c.U) := hA
        _ = (c.U ⊓ w.M).relIndex c.U * Nat.card (↥(c.U ⊓ w.M)) := hB.symm)
  have hHInter' : (c.H ⊓ w.M).relIndex c.H = u * p0 := by
    calc
      (c.H ⊓ w.M).relIndex c.H = (c.U ⊓ w.M).relIndex c.U := hIdx
      _ = u * p0 := hUInter
  -- the index-tower factorization
  have hfactor' : (c.H.index : ℚ) * ((u : ℚ) * (p0 : ℚ)) =
      (q : ℚ) * (k' : ℚ) * (w.M.index : ℚ) := by
    exact secondCase_inf_index_tower_factor_eq10 c.H w.M
      hHInter' hMInter
      (by exact Nat.cast_mul u p0)
      (by exact Nat.cast_mul q k')
      rfl
  have hfactor : (bg.H.index : ℚ) * ((u : ℚ) * (p0 : ℚ)) =
      (q : ℚ) * (k' : ℚ) * (w.M.index : ℚ) := by
    rw [hbgH]
    exact hfactor'
  -- the rational equation-(10) inequality (Theorem A transport)
  have huQ : 0 < (u : ℚ) := by exact_mod_cast hu
  have hp0Q : 0 < (p0 : ℚ) := by exact_mod_cast hp0
  have h10 := secondCase_equation10_of_theorem_A bg hfactor hbgkQ huQ hp0Q
  exact {
    bg := bg
    bg_H_eq := hbgH
    indexTower := hfactor
    bgK := hbgkQ
    hu := huQ
    hp0 := hp0Q
    equation10 := h10
  }

end CFSG.GorensteinWalter
