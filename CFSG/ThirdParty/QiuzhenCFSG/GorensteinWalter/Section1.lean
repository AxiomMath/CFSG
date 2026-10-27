module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index

namespace CFSG
end CFSG
open CFSG

/-!
# Section 1: general facts (Bender, pp. 216-218)

The paper lists elementary general facts 1.1-1.10.  This file formalizes the
ones whose statements and proofs are self-contained: Fact 1.2 (already in the
repository, bridged to the ambient notation), Fact 1.4 (involution arithmetic),
and Fact 1.5 (an involution acting on a `2'`-group).  Facts 1.6-1.10 are
structure theorems for `D`-groups taken from Gorenstein-Walter and are not
provable from the paper alone.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## Fact 1.2: `C_H(F(H)) ≤ F(H)` for solvable `H` -/

/-- Fact 1.2: if `H` is solvable, then `C_H(F(H)) ≤ F(H)`, written with the
ambient centralizer. -/
public theorem fact_1_2_centralizer_fitting_le_fitting
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (hsolv : IsSolvable (↥H)) :
    H ⊓ Subgroup.centralizer (fittingSubgroupOf (G := G) H : Set G) ≤
      fittingSubgroupOf (G := G) H := by
  intro c hc
  have hcH : c ∈ H := hc.1
  have hcC : c ∈ Subgroup.centralizer (fittingSubgroupOf (G := G) H : Set G) := hc.2
  let c' : ↥H := ⟨c, hcH⟩
  have hc'_cent : c' ∈ Subgroup.centralizer (fittingSubgroup (↥H) : Set (↥H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfF : (f : G) ∈ fittingSubgroupOf (G := G) H := by
      simpa [fittingSubgroupOf] using (Subgroup.mem_map_of_mem H.subtype hf)
    have hcomm := (Subgroup.mem_centralizer_iff (g := c) (s := (fittingSubgroupOf (G := G) H : Set G))).1
      hcC (f : G) hfF
    apply Subtype.ext
    simpa using hcomm
  have hle := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := ↥H) hsolv
  have hc'_fit : c' ∈ fittingSubgroup (↥H) := hle hc'_cent
  exact Subgroup.mem_map.mpr ⟨c', hc'_fit, rfl⟩

/-! ## Fact 1.4: involution arithmetic -/

/-- Membership in `I_G(y)`, unfolded for an involution `y`. -/
public theorem mem_invertedElements_top_iff
    {G : Type u} [Group G] {y g : G} (hy : IsInvolution y) :
    g ∈ invertedElements (⊤ : Subgroup G) y ↔ y * g * y = g⁻¹ := by
  have hyy : y * y = 1 := by simpa [pow_two] using hy.2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  constructor
  · intro hg
    simpa [invertedElements, hyinv] using hg.2
  · intro hgy
    refine ⟨by simp, ?_⟩
    simpa [hyinv] using hgy

/-- Fact 1.4: for an involution `y` and `g ∈ G`, `g * y` is an involution
iff `g ≠ y` and `g ∈ I_G(y)`. -/
public theorem fact_1_4_involution_mul
    {G : Type u} [Group G] {y g : G} (hy : IsInvolution y) :
    IsInvolution (g * y) ↔ g ≠ y ∧ y * g * y = g⁻¹ := by
  have hyy : y * y = 1 := by simpa [pow_two] using hy.2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  constructor
  · intro h
    constructor
    · intro hgy
      apply h.1
      calc
        g * y = y * y := by rw [hgy]
        _ = 1 := hyy
    · -- `(g * y) ^ 2 = 1` gives `y * g * y = g⁻¹`
      have h1 : g * y * g * y = 1 := by simpa [pow_two, mul_assoc] using h.2
      have h2 : g * y * g = y := by
        calc
          g * y * g = (g * y * g) * (y * y) := by rw [hyy]; simp
          _ = (g * y * g * y) * y := by group
          _ = 1 * y := by rw [h1]
          _ = y := by simp
      have h3 : y * g * y * g = 1 := by
        calc
          y * g * y * g = y * (g * y * g) := by group
          _ = y * y := by rw [h2]
          _ = 1 := hyy
      calc
        y * g * y = (y * g * y * g) * g⁻¹ := by group
        _ = 1 * g⁻¹ := by rw [h3]
        _ = g⁻¹ := by simp
  · intro h
    constructor
    · intro hgy
      exact h.1 (by
        calc
          g = y⁻¹ := eq_inv_of_mul_eq_one_left hgy
          _ = y := hyinv)
    · -- `y * g * y = g⁻¹` gives `(g * y) ^ 2 = 1`
      have h3 : y * g * y * g = 1 := by
        calc
          y * g * y * g = g⁻¹ * g := by rw [h.2]
          _ = 1 := by simp
      have h2 : g * y * g = y := by
        calc
          g * y * g = (y * y) * (g * y * g) := by rw [hyy]; simp
          _ = y * (y * g * y * g) := by group
          _ = y * 1 := by rw [h3]
          _ = y := by simp
      have h1 : g * y * g * y = 1 := by
        calc
          g * y * g * y = y * y := by rw [h2]
          _ = 1 := hyy
      simpa [pow_two, mul_assoc] using h1

/-- Fact 1.4: if `f, g ∈ I_G(y)`, then `f * g⁻¹ ∈ I_G(g * y)`. -/
public theorem fact_1_4_inverted_mul_inv
    {G : Type u} [Group G] {y f g : G} (hy : IsInvolution y)
    (hf : f ∈ invertedElements (⊤ : Subgroup G) y)
    (hg : g ∈ invertedElements (⊤ : Subgroup G) y) :
    f * g⁻¹ ∈ invertedElements (⊤ : Subgroup G) (g * y) := by
  have hfy : y * f * y = f⁻¹ := (mem_invertedElements_top_iff hy).1 hf
  have hgy : y * g * y = g⁻¹ := (mem_invertedElements_top_iff hy).1 hg
  have hyy : y * y = 1 := by simpa [pow_two] using hy.2
  -- `g⁻¹ * y * g⁻¹ = y`, from `y * g * y = g⁻¹`
  have hgy' : g⁻¹ * y * g⁻¹ = y := by
    calc
      g⁻¹ * y * g⁻¹ = (y * g * y) * y * (y * g * y) := by rw [← hgy]
      _ = y * g * (y * y) * (y * g * y) := by group
      _ = y * g * (y * g * y) := by rw [hyy]; simp
      _ = (y * g * y) * (g * y) := by group
      _ = g⁻¹ * (g * y) := by rw [← hgy]
      _ = y := by group
  rw [invertedElements]
  refine ⟨by simp, ?_⟩
  calc
    (g * y) * (f * g⁻¹) * (g * y)⁻¹ = g * y * f * (g⁻¹ * y * g⁻¹) := by
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
      rw [mul_inv_rev, hyinv]
      group
    _ = g * y * f * y := by rw [hgy']
    _ = g * (y * f * y) := by group
    _ = g * f⁻¹ := by rw [hfy]
    _ = (f * g⁻¹)⁻¹ := by group

/-! ## Fact 1.5: an involution acting on a `2'`-group -/

/-- In a group whose order is coprime to `2` the squaring map is bijective. -/
public theorem sq_bijective_of_coprime_two
    {G : Type u} [Group G] [Finite G] (hcop : Nat.Coprime 2 (Nat.card G)) :
    Function.Bijective (fun x : G => x ^ 2) := by
  simpa [Nat.Coprime, pow_two] using (hcop.symm.pow_left_bijective (G := G) (n := 2))

/-- The square root in a finite `2'`-group is unique. -/
public theorem sq_eq_sq_of_coprime_two
    {G : Type u} [Group G] [Finite G] (hcop : Nat.Coprime 2 (Nat.card G))
    {a b : G} (h : a ^ 2 = b ^ 2) : a = b :=
  (sq_bijective_of_coprime_two (G := G) hcop).1 h

/-- In a `2'`-group, an element of order dividing two is trivial. -/
public theorem eq_one_of_sq_eq_one_of_coprime_two
    {G : Type u} [Group G] [Finite G] (hcop : Nat.Coprime 2 (Nat.card G))
    {x : G} (h : x ^ 2 = 1) : x = 1 := by
  have hord2 : orderOf x ∣ 2 := (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).2 h
  have hordn : orderOf x ∣ Nat.card G := by
    let : Fintype G := Fintype.ofFinite G
    simpa using (orderOf_dvd_card (G := G) (x := x))
  have hdvd_gcd : orderOf x ∣ (2 : ℕ).gcd (Nat.card G) := Nat.dvd_gcd hord2 hordn
  have hgcd : (2 : ℕ).gcd (Nat.card G) = 1 := hcop.gcd_eq_one
  have hord1 : orderOf x = 1 := Nat.dvd_one.mp (by simpa [hgcd] using hdvd_gcd)
  exact (orderOf_eq_one_iff (x := x)).1 hord1

private theorem involution_inv {G : Type u} [Group G] {s : G} (hs : IsInvolution s) :
    s⁻¹ = s :=
  inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs.2)

private theorem involution_sq_one {G : Type u} [Group G] {s : G} (hs : IsInvolution s) :
    s * s = 1 := by
  simpa [pow_two] using hs.2

/-- `(x^s)^s = x` for an involution `s`. -/
private theorem conj_conj_of_involution {G : Type u} [Group G] {s a : G}
    (hs : IsInvolution s) : s * (s * a * s⁻¹) * s⁻¹ = a := by
  have hs_inv : s⁻¹ = s := involution_inv hs
  have hss : s * s = 1 := involution_sq_one hs
  calc
    s * (s * a * s⁻¹) * s⁻¹ = (s * s) * a * (s⁻¹ * s⁻¹) := by group
    _ = 1 * a * 1 := by
      have hss' : s⁻¹ * s⁻¹ = 1 := by
        calc s⁻¹ * s⁻¹ = (s * s)⁻¹ := by group
          _ = 1 := by rw [hss]; simp
      rw [hss, hss']
    _ = a := by simp

/-- `(x^s)^2 = (x^2)^s` for an involution `s`. -/
private theorem conj_sq_of_involution {G : Type u} [Group G] {s a : G}
    (_hs : IsInvolution s) : (s * a * s⁻¹) ^ 2 = s * (a ^ 2) * s⁻¹ := by
  calc
    (s * a * s⁻¹) ^ 2 = (s * a * s⁻¹) * (s * a * s⁻¹) := by rw [pow_two]
    _ = s * (a * a) * s⁻¹ := by group
    _ = s * (a ^ 2) * s⁻¹ := by rw [← pow_two]

/-- The centralizer of `s` inside `X`. -/
@[expose]
public def centralizerIn {G : Type u} [Group G] (X : Subgroup G) (s : G) : Subgroup G :=
  X ⊓ Subgroup.centralizer ({s} : Set G)

private theorem mem_centralizerIn_iff {G : Type u} [Group G] (X : Subgroup G) (s : G) (c : G) :
    c ∈ centralizerIn X s ↔ c ∈ X ∧ s * c * s⁻¹ = c := by
  constructor
  · intro hc
    refine ⟨hc.1, ?_⟩
    have hcs : s * c = c * s :=
      (Subgroup.mem_centralizer_iff (g := c) (s := ({s} : Set G))).1 hc.2 s (by simp)
    calc
      s * c * s⁻¹ = c * s * s⁻¹ := by rw [hcs]
      _ = c := by simp
  · intro hc
    refine ⟨hc.1, ?_⟩
    change c ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzs : z = s := by simpa using hz
    rw [hzs]
    have hcs : s * c = c * s := by
      calc
        s * c = (s * c * s⁻¹) * s := by group
        _ = c * s := by rw [hc.2]
    exact hcs

/-- A square root of `y` in a finite `2'`-group. -/
private noncomputable def sqrtOf {G : Type u} [Group G] [Finite G]
    (hcop : Nat.Coprime 2 (Nat.card G)) (y : G) : G :=
  Classical.choose ((sq_bijective_of_coprime_two (G := G) hcop).2 y)

private theorem sqrtOf_sq {G : Type u} [Group G] [Finite G]
    (hcop : Nat.Coprime 2 (Nat.card G)) (y : G) :
    sqrtOf hcop y ^ 2 = y :=
  Classical.choose_spec ((sq_bijective_of_coprime_two (G := G) hcop).2 y)

/-- Fact 1.5(i): `I_X(s) = {x⁻¹ * x^s | x ∈ X}`. -/
public theorem fact_1_5_i_invertedElements_eq_image
    {G : Type u} [Group G] [Finite G] {X : Subgroup G} {s : G}
    (hs : IsInvolution s) (hcop : Nat.Coprime 2 (Nat.card (↥X)))
    (hsX : ∀ x : G, x ∈ X → s * x * s⁻¹ ∈ X) :
    invertedElements X s =
      {x : G | ∃ a : ↥X, x = (a : G)⁻¹ * (s * (a : G) * s⁻¹)} := by
  classical
  let S : Set G := {x : G | ∃ a : ↥X, x = (a : G)⁻¹ * (s * (a : G) * s⁻¹)}
  -- the image is closed under inversion: `(a⁻¹ * a^s)⁻¹ = (a^s)⁻¹ * (a^s)^s`
  have hS_inv : ∀ x : G, x ∈ S → x⁻¹ ∈ S := by
    intro x hx
    rcases hx with ⟨a, ha⟩
    refine ⟨⟨s * (a : G) * s⁻¹, hsX (a : G) a.2⟩, ?_⟩
    calc
      x⁻¹ = (a⁻¹ * (s * a * s⁻¹))⁻¹ := by
        rw [ha]
        simp
      _ = (s * (a : G) * s⁻¹)⁻¹ * (s * (s * (a : G) * s⁻¹) * s⁻¹) := by
        calc
          (a⁻¹ * (s * a * s⁻¹))⁻¹ = (s * (a : G) * s⁻¹)⁻¹ * (a : G) := by
            change ((a : G)⁻¹ * (s * (a : G) * s⁻¹))⁻¹ = (s * (a : G) * s⁻¹)⁻¹ * (a : G)
            group
          _ = (s * (a : G) * s⁻¹)⁻¹ * (s * (s * (a : G) * s⁻¹) * s⁻¹) := by
            exact congrArg (fun z : G => (s * (a : G) * s⁻¹)⁻¹ * z)
              ((conj_conj_of_involution (G := G) hs).symm)
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxX, hxs⟩
    -- `j₀ := sqrt(x⁻¹)` lies in `I(s)`.
    let j₀ : ↥X := sqrtOf hcop (⟨x⁻¹, X.inv_mem hxX⟩ : ↥X)
    have hsq_j₀ : j₀ ^ 2 = ⟨x⁻¹, X.inv_mem hxX⟩ := by
      change sqrtOf hcop (⟨x⁻¹, X.inv_mem hxX⟩ : ↥X) ^ 2 = ⟨x⁻¹, X.inv_mem hxX⟩
      exact sqrtOf_sq hcop (⟨x⁻¹, X.inv_mem hxX⟩ : ↥X)
    have h' : (j₀ : G) ^ 2 = x⁻¹ := by
      simpa using congrArg (fun z : ↥X => (z : G)) hsq_j₀
    have hj₀I : (j₀ : G) ∈ invertedElements X s := by
      rw [invertedElements]
      refine ⟨j₀.2, ?_⟩
      have hsq : (s * (j₀ : G) * s⁻¹) ^ 2 = ((j₀ : G)⁻¹) ^ 2 := by
        calc
          (s * (j₀ : G) * s⁻¹) ^ 2 = s * ((j₀ : G) ^ 2) * s⁻¹ := by
            exact conj_sq_of_involution (G := G) hs
          _ = s * (x⁻¹) * s⁻¹ := by rw [h']
          _ = x := by
            calc
              s * (x⁻¹) * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
              _ = ((x : G)⁻¹)⁻¹ := by rw [hxs]
              _ = x := by simp
          _ = ((j₀ : G)⁻¹) ^ 2 := by
            have hx' : x = ((j₀ : G) ^ 2)⁻¹ := by
              calc
                x = (x⁻¹)⁻¹ := by simp
                _ = ((j₀ : G) ^ 2)⁻¹ := by rw [h']
            calc
              x = ((j₀ : G) ^ 2)⁻¹ := hx'
              _ = ((j₀ : G)⁻¹) ^ 2 := by
                rw [pow_two]
                group
      have hin : s * (j₀ : G) * s⁻¹ ∈ X := hsX (j₀ : G) j₀.2
      have hsq' : (⟨s * (j₀ : G) * s⁻¹, hin⟩ : ↥X) ^ 2 =
          (⟨(j₀ : G)⁻¹, X.inv_mem j₀.2⟩ : ↥X) ^ 2 := by
        apply Subtype.ext
        simpa using hsq
      have heq := (sq_bijective_of_coprime_two (G := ↥X) hcop).1 hsq'
      simpa using congrArg Subtype.val heq
    -- `x⁻¹ = j₀ ^ 2 = (j₀⁻¹)⁻¹ * (j₀⁻¹)^s`, so `x⁻¹ ∈ S`; the image is closed under inverses.
    have hx_inv_S : x⁻¹ ∈ S := by
      refine ⟨⟨(j₀ : G)⁻¹, X.inv_mem j₀.2⟩, ?_⟩
      calc
        x⁻¹ = (j₀ : G) ^ 2 := by
          simpa using (congrArg (fun z : ↥X => (z : G)) hsq_j₀).symm
        _ = ((j₀ : G)⁻¹)⁻¹ * (s * (j₀ : G)⁻¹ * s⁻¹) := by
          have hj₀_inv : s * (j₀ : G)⁻¹ * s⁻¹ = (j₀ : G) := by
            have : s * (j₀ : G) * s⁻¹ = (j₀ : G)⁻¹ := hj₀I.2
            calc
              s * (j₀ : G)⁻¹ * s⁻¹ = (s * (j₀ : G) * s⁻¹)⁻¹ := by group
              _ = ((j₀ : G)⁻¹)⁻¹ := by rw [this]
              _ = (j₀ : G) := by simp
          calc
            (j₀ : G) ^ 2 = (j₀ : G) * (j₀ : G) := by simp [pow_two]
            _ = ((j₀ : G)⁻¹)⁻¹ * (s * (j₀ : G)⁻¹ * s⁻¹) := by rw [hj₀_inv]; simp
    change x ∈ S
    simpa using hS_inv (x⁻¹) hx_inv_S
  · intro hx
    rcases hx with ⟨a, ha⟩
    rw [invertedElements]
    refine ⟨?_, ?_⟩
    · -- `a⁻¹ * (s * a * s⁻¹) ∈ X`
      rw [ha]
      exact X.mul_mem (X.inv_mem a.2) (hsX (a : G) a.2)
    · -- it is inverted by `s`
      rw [ha]
      calc
        s * ((a : G)⁻¹ * (s * (a : G) * s⁻¹)) * s⁻¹ =
            ((a : G)⁻¹ * (s * (a : G) * s⁻¹))⁻¹ := by
          calc
            s * ((a : G)⁻¹ * (s * (a : G) * s⁻¹)) * s⁻¹ =
                (s * (a : G)⁻¹ * s⁻¹) * (s * (s * (a : G) * s⁻¹) * s⁻¹) := by group
            _ = (s * (a : G) * s⁻¹)⁻¹ * (a : G) := by
              have h1 : s * (a : G)⁻¹ * s⁻¹ = (s * (a : G) * s⁻¹)⁻¹ := by group
              rw [h1, conj_conj_of_involution (G := G) hs]
            _ = ((a : G)⁻¹ * (s * (a : G) * s⁻¹))⁻¹ := by group

/-- Fact 1.5(ii): every `x ∈ X` decomposes uniquely as `x = c * i` with
`c ∈ C_X(s)` and `i ∈ I_X(s)`. -/
public theorem fact_1_5_ii_decomposition
    {G : Type u} [Group G] [Finite G] {X : Subgroup G} {s : G}
    (hs : IsInvolution s) (hcop : Nat.Coprime 2 (Nat.card (↥X)))
    (hsX : ∀ x : G, x ∈ X → s * x * s⁻¹ ∈ X) :
    ∀ x : G, x ∈ X →
      ∃ c : G, c ∈ centralizerIn X s ∧
        ∃ i : G, i ∈ invertedElements X s ∧ x = c * i := by
  classical
  intro x hx
  let C : Subgroup G := centralizerIn X s
  let I : Set G := invertedElements X s
  let u : ↥X := ⟨(s * x * s⁻¹)⁻¹ * x, X.mul_mem (X.inv_mem (hsX x hx)) hx⟩
  let i : ↥X := sqrtOf hcop u
  have hsq_i : i ^ 2 = u := sqrtOf_sq hcop u
  have hi_sq : (i : G) ^ 2 = (u : G) := by
    simpa using congrArg (fun z : ↥X => (z : G)) hsq_i
  have hx_u : x⁻¹ * (s * x * s⁻¹) = (u : G)⁻¹ := by
    calc
      x⁻¹ * (s * x * s⁻¹) = ((s * x * s⁻¹)⁻¹ * x)⁻¹ := by group
      _ = (u : G)⁻¹ := by rfl
  have hu_eq : s * (u : G) * s⁻¹ = (u : G)⁻¹ := by
    calc
      s * (u : G) * s⁻¹ = s * ((s * x * s⁻¹)⁻¹ * x) * s⁻¹ := by rfl
      _ = x⁻¹ * (s * x * s⁻¹) := by
        calc
          s * ((s * x * s⁻¹)⁻¹ * x) * s⁻¹ = (s * (s * x * s⁻¹)⁻¹ * s⁻¹) * (s * x * s⁻¹) := by group
          _ = x⁻¹ * (s * x * s⁻¹) := by
            have h1 : s * (s * x * s⁻¹)⁻¹ * s⁻¹ = x⁻¹ := by
              calc
                s * (s * x * s⁻¹)⁻¹ * s⁻¹ = s * (s * x⁻¹ * s⁻¹) * s⁻¹ := by
                  have hstep : (s * x * s⁻¹)⁻¹ = s * x⁻¹ * s⁻¹ := by group
                  exact congrArg (fun z : G => s * z * s⁻¹) hstep
                _ = x⁻¹ := conj_conj_of_involution (G := G) (a := x⁻¹) hs
            rw [h1]
      _ = (u : G)⁻¹ := hx_u
  have hiI : (i : G) ∈ I := by
    change (i : G) ∈ invertedElements X s
    rw [invertedElements]
    refine ⟨i.2, ?_⟩
    have hsq : (s * (i : G) * s⁻¹) ^ 2 = ((i : G)⁻¹) ^ 2 := by
      calc
        (s * (i : G) * s⁻¹) ^ 2 = s * ((i : G) ^ 2) * s⁻¹ := by
          exact conj_sq_of_involution (G := G) hs
        _ = s * (u : G) * s⁻¹ := by rw [hi_sq]
        _ = (u : G)⁻¹ := hu_eq
        _ = ((i : G)⁻¹) ^ 2 := by
          calc
            (u : G)⁻¹ = ((i : G) ^ 2)⁻¹ := by rw [hi_sq]
            _ = ((i : G)⁻¹) ^ 2 := by
              rw [pow_two]
              group
    have hin : s * (i : G) * s⁻¹ ∈ X := hsX (i : G) i.2
    have hsq' : (⟨s * (i : G) * s⁻¹, hin⟩ : ↥X) ^ 2 =
        (⟨(i : G)⁻¹, X.inv_mem i.2⟩ : ↥X) ^ 2 := by
      apply Subtype.ext
      simpa using hsq
    have heq := (sq_bijective_of_coprime_two (G := ↥X) hcop).1 hsq'
    simpa using congrArg Subtype.val heq
  let c : G := x * (i : G)⁻¹
  have hcC : c ∈ C := by
    rw [mem_centralizerIn_iff]
    constructor
    · exact X.mul_mem hx (X.inv_mem i.2)
    · have hi_inv : s * (i : G)⁻¹ * s⁻¹ = (i : G) := by
        have : s * (i : G) * s⁻¹ = (i : G)⁻¹ := hiI.2
        calc
          s * (i : G)⁻¹ * s⁻¹ = (s * (i : G) * s⁻¹)⁻¹ := by group
          _ = ((i : G)⁻¹)⁻¹ := by rw [this]
          _ = (i : G) := by simp
      have hu'_inv : (u : G)⁻¹ = ((i : G)⁻¹) ^ 2 := by
        calc
          (u : G)⁻¹ = ((i : G) ^ 2)⁻¹ := by rw [hi_sq]
          _ = ((i : G)⁻¹) ^ 2 := by
            rw [pow_two]
            group
      have hx_u' : x⁻¹ * (s * x * s⁻¹) = ((i : G)⁻¹) ^ 2 := by
        calc
          x⁻¹ * (s * x * s⁻¹) = (u : G)⁻¹ := hx_u
          _ = ((i : G)⁻¹) ^ 2 := hu'_inv
      have hstep : (s * x * s⁻¹) * (i : G) = x * (i : G)⁻¹ := by
        have hy : (s * x * s⁻¹) = x * ((i : G)⁻¹) ^ 2 := by
          calc
            (s * x * s⁻¹) = x * (x⁻¹ * (s * x * s⁻¹)) := by group
            _ = x * ((i : G)⁻¹) ^ 2 := by rw [hx_u']
        calc
          (s * x * s⁻¹) * (i : G) = (x * ((i : G)⁻¹) ^ 2) * (i : G) := by rw [hy]
          _ = x * (i : G)⁻¹ := by
            rw [pow_two]
            group
      calc
        s * c * s⁻¹ = s * (x * (i : G)⁻¹) * s⁻¹ := rfl
        _ = (s * x * s⁻¹) * (s * (i : G)⁻¹ * s⁻¹) := by group
        _ = (s * x * s⁻¹) * (i : G) := by rw [hi_inv]
        _ = x * (i : G)⁻¹ := hstep
        _ = c := rfl
  refine ⟨c, hcC, (i : G), ?_⟩
  exact ⟨hiI, by simp [c]⟩

/-- Fact 1.5(ii): `|I_X(s)| = |X : C_X(s)|`. -/
public theorem fact_1_5_ii_card
    {G : Type u} [Group G] [Finite G] {X : Subgroup G} {s : G}
    (hs : IsInvolution s) (hcop : Nat.Coprime 2 (Nat.card (↥X)))
    (hsX : ∀ x : G, x ∈ X → s * x * s⁻¹ ∈ X) :
    Nat.card {i : G // i ∈ invertedElements X s} =
      ((centralizerIn X s).subgroupOf X).index := by
  classical
  let C : Subgroup G := centralizerIn X s
  let I : Set G := invertedElements X s
  have hdecomp := fact_1_5_ii_decomposition (G := G) hs hcop hsX
  -- uniqueness of the decomposition: if `c * i = c' * i'`, conjugating by `s`
  -- gives `c * i⁻¹ = c' * i'⁻¹`, hence `i² = i'²`, so `i = i'` and `c = c'`.
  have huniq : ∀ {c c' : G} {i i' : G}, c ∈ C → c' ∈ C → i ∈ I → i' ∈ I →
      c * i = c' * i' → c = c' ∧ i = i' := by
    intro c c' i i' hc hc' hi hi' h
    have hc_fix : s * c * s⁻¹ = c := ((mem_centralizerIn_iff X s c).1 hc).2
    have hc'_fix : s * c' * s⁻¹ = c' := ((mem_centralizerIn_iff X s c').1 hc').2
    have h1 : c * i⁻¹ = c' * i'⁻¹ := by
      calc
        c * i⁻¹ = (s * c * s⁻¹) * i⁻¹ := by rw [hc_fix]
        _ = (s * c * s⁻¹) * (s * i * s⁻¹) := by rw [hi.2]
        _ = s * (c * i) * s⁻¹ := by group
        _ = s * (c' * i') * s⁻¹ := by rw [h]
        _ = (s * c' * s⁻¹) * (s * i' * s⁻¹) := by group
        _ = c' * i'⁻¹ := by rw [hc'_fix, hi'.2]
    have hsq : (i : G) ^ 2 = (i' : G) ^ 2 := by
      calc
        (i : G) ^ 2 = (i : G) * (i : G) := by rw [pow_two]
        _ = (c * i⁻¹)⁻¹ * (c * i) := by group
        _ = (c' * i'⁻¹)⁻¹ * (c' * i') := by rw [h1, h]
        _ = (i' : G) * (i' : G) := by group
        _ = (i' : G) ^ 2 := by rw [pow_two]
    have hi_eq : i = i' := by
      have hsqX : (⟨i, hi.1⟩ : ↥X) ^ 2 = (⟨i', hi'.1⟩ : ↥X) ^ 2 := by
        apply Subtype.ext
        simpa using hsq
      exact congrArg Subtype.val (sq_eq_sq_of_coprime_two (G := ↥X) hcop hsqX)
    have hc_eq : c = c' := by
      calc
        c = (c * i) * i⁻¹ := by group
        _ = (c' * i') * i⁻¹ := by rw [h]
        _ = c' := by rw [hi_eq]; group
    exact ⟨hc_eq, hi_eq⟩
  -- the bijection `C × I ≃ X`
  let f : (↥C × {i : G // i ∈ I}) → ↥X := fun p =>
    ⟨(p.1 : G) * (p.2 : G), X.mul_mem p.1.2.1 (p.2.2.1)⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    have h := congrArg (fun z : ↥X => (z : G)) hpq
    rcases huniq p.1.2 q.1.2 p.2.2 q.2.2 h with ⟨h1, h2⟩
    apply Prod.ext
    · apply Subtype.ext
      exact h1
    · apply Subtype.ext
      exact h2
  have hf_surj : Function.Surjective f := by
    intro x
    rcases hdecomp x x.2 with ⟨c, hcC, i, hiI, hxi⟩
    refine ⟨⟨⟨c, hcC⟩, ⟨i, hiI⟩⟩, ?_⟩
    apply Subtype.ext
    exact hxi.symm
  have hcard : Nat.card (↥X) = Nat.card C * Nat.card {i : G // i ∈ I} := by
    have he : (↥C × {i : G // i ∈ I}) ≃ ↥X := Equiv.ofBijective f (⟨hf_inj, hf_surj⟩)
    calc
      Nat.card (↥X) = Nat.card (↥C × {i : G // i ∈ I}) := (Nat.card_congr he).symm
      _ = Nat.card C * Nat.card {i : G // i ∈ I} := by simp [Nat.card_prod]
  -- the index of `C` in `X`
  have hmap : (C.subgroupOf X).map X.subtype = C := by
    apply le_antisymm
    · intro y hy
      rcases (Subgroup.mem_map.mp hy) with ⟨x, hx, rfl⟩
      exact hx
    · intro c hcC
      exact Subgroup.mem_map.mpr ⟨⟨c, hcC.1⟩, by
        simpa [Subgroup.mem_subgroupOf] using (show (⟨c, hcC.1⟩ : ↥X) ∈ C.subgroupOf X from hcC)⟩
  have hcardC : Nat.card ↥(C.subgroupOf X) = Nat.card C := by
    calc
      Nat.card ↥(C.subgroupOf X) = Nat.card ↥((C.subgroupOf X).map X.subtype) := by
        simpa [hmap] using (Subgroup.card_subtype X (C.subgroupOf X)).symm
      _ = Nat.card C := by rw [hmap]
  have hindex : Nat.card (↥X) = Nat.card C * (C.subgroupOf X).index := by
    calc
      Nat.card (↥X) = Nat.card ↥(C.subgroupOf X) * (C.subgroupOf X).index := by
        simp
      _ = Nat.card C * (C.subgroupOf X).index := by rw [hcardC]
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have : Nat.card C * Nat.card {i : G // i ∈ I} = Nat.card C * (C.subgroupOf X).index := by
    rw [← hcard, hindex]
  exact Nat.mul_left_cancel hCpos this

/-- Fact 1.5(iii): if `I_X(s)` is a subgroup, then it is an abelian normal
subgroup of `X`, hence lies in `F(X)`. -/
public theorem fact_1_5_iii_inverted_subgroup_abelian_normal
    {G : Type u} [Group G] [Finite G] {X : Subgroup G} {s : G}
    (hs : IsInvolution s) (_hcop : Nat.Coprime 2 (Nat.card (↥X)))
    (hsX : ∀ x : G, x ∈ X → s * x * s⁻¹ ∈ X)
    {I : Subgroup G} (hI : (I : Set G) = invertedElements X s) :
    IsMulCommutative I ∧ IsNormalIn I X ∧ I ≤ fittingSubgroupOf X := by
  classical
  have hIX : I ≤ X := by
    intro x hx
    have : x ∈ invertedElements X s := by simpa [← hI] using hx
    exact this.1
  have hI_mem : ∀ x : G, x ∈ I → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have : x ∈ invertedElements X s := by simpa [← hI] using hx
    exact this.2
  have hI_abelian : IsMulCommutative I := by
    rw [isMulCommutative_iff]
    intro a b
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    have hab : s * (a * b) * s⁻¹ = (a * b)⁻¹ := hI_mem (a * b) (I.mul_mem ha hb)
    have hab' : s * (a * b) * s⁻¹ = a⁻¹ * b⁻¹ := by
      calc
        s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = a⁻¹ * b⁻¹ := by rw [hI_mem a ha, hI_mem b hb]
    have hb'a' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
    have : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
      rw [← hab', hab]
      exact hb'a'
    have hba : b * a = a * b := by
      have : (a⁻¹ * b⁻¹)⁻¹ = (b⁻¹ * a⁻¹)⁻¹ := congrArg (fun z : G => z⁻¹) this
      simpa using this
    apply Subtype.ext
    exact hba.symm
  have hI_normal : IsNormalIn I X := by
    refine ⟨hIX, ?_⟩
    intro h hh x hx
    have huI : h⁻¹ * (s * h * s⁻¹) ∈ I := by
      have hu : s * (h⁻¹ * (s * h * s⁻¹)) * s⁻¹ = (h⁻¹ * (s * h * s⁻¹))⁻¹ := by
        calc
          s * (h⁻¹ * (s * h * s⁻¹)) * s⁻¹ = (s * h⁻¹ * s⁻¹) * (s * (s * h * s⁻¹) * s⁻¹) := by group
          _ = (s * h * s⁻¹)⁻¹ * h := by
            have h1 : s * h⁻¹ * s⁻¹ = (s * h * s⁻¹)⁻¹ := by group
            have h2 : s * (s * h * s⁻¹) * s⁻¹ = h := conj_conj_of_involution (G := G) hs
            rw [h1, h2]
          _ = (h⁻¹ * (s * h * s⁻¹))⁻¹ := by group
      change h⁻¹ * (s * h * s⁻¹) ∈ (I : Set G)
      rw [hI]
      exact ⟨X.mul_mem (X.inv_mem hh) (hsX h hh), hu⟩
    have hcomm : (h⁻¹ * (s * h * s⁻¹)) * x⁻¹ = x⁻¹ * (h⁻¹ * (s * h * s⁻¹)) := by
      have hxinvI : x⁻¹ ∈ I := I.inv_mem hx
      have : (⟨h⁻¹ * (s * h * s⁻¹), huI⟩ : ↥I) * ⟨x⁻¹, hxinvI⟩ =
          ⟨x⁻¹, hxinvI⟩ * ⟨h⁻¹ * (s * h * s⁻¹), huI⟩ := by
        exact isMulCommutative_iff.mp hI_abelian ⟨h⁻¹ * (s * h * s⁻¹), huI⟩ ⟨x⁻¹, hxinvI⟩
      simpa using congrArg Subtype.val this
    have hxh_inv : s * (h * x * h⁻¹) * s⁻¹ = (h * x * h⁻¹)⁻¹ := by
      let u := h⁻¹ * (s * h * s⁻¹)
      have hsh : s * h * s⁻¹ = h * u := by
        calc
          s * h * s⁻¹ = h * (h⁻¹ * (s * h * s⁻¹)) := by group
          _ = h * u := rfl
      have hsh_inv : s * h⁻¹ * s⁻¹ = u⁻¹ * h⁻¹ := by
        calc
          s * h⁻¹ * s⁻¹ = (s * h * s⁻¹)⁻¹ := by group
          _ = (h * u)⁻¹ := by rw [hsh]
          _ = u⁻¹ * h⁻¹ := by group
      calc
        s * (h * x * h⁻¹) * s⁻¹ = (s * h * s⁻¹) * (s * x * s⁻¹) * (s * h⁻¹ * s⁻¹) := by group
        _ = (h * u) * x⁻¹ * (u⁻¹ * h⁻¹) := by rw [hsh, hI_mem x hx, hsh_inv]
        _ = h * (u * x⁻¹ * u⁻¹) * h⁻¹ := by group
        _ = h * x⁻¹ * h⁻¹ := by
          have : u * x⁻¹ * u⁻¹ = x⁻¹ := by
            have hu_comm : u * x⁻¹ = x⁻¹ * u := hcomm
            calc
              u * x⁻¹ * u⁻¹ = (x⁻¹ * u) * u⁻¹ := by rw [hu_comm]
              _ = x⁻¹ := by group
          rw [this]
        _ = (h * x * h⁻¹)⁻¹ := by group
    change h * x * h⁻¹ ∈ (I : Set G)
    rw [hI]
    exact ⟨X.mul_mem (X.mul_mem hh (hIX hx)) (X.inv_mem hh), hxh_inv⟩
  have hI_le_F : I ≤ fittingSubgroupOf X := by
    let I' : Subgroup (↥X) := I.subgroupOf X
    have hI'_normal : I'.Normal := by
      refine ⟨?_⟩
      intro n hn g
      have hnI : (n : G) ∈ I := by simpa [I', Subgroup.mem_subgroupOf] using hn
      have hgX : (g : G) ∈ X := g.2
      have hv : (g : G) * (n : G) * (g : G)⁻¹ ∈ I := hI_normal.2 (g : G) hgX (n : G) hnI
      simpa [I', Subgroup.mem_subgroupOf] using hv
    have hI'_nil : Group.IsNilpotent (↥I') := by
      refine ⟨1, ?_⟩
      rw [Subgroup.upperCentralSeries_one_eq_top_iff]
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      change (a : G) * (b : G) = (b : G) * (a : G)
      have ha : (a : G) ∈ I := by exact a.2
      have hb : (b : G) ∈ I := by exact b.2
      have : (⟨(a : G), ha⟩ : ↥I) * ⟨(b : G), hb⟩ = ⟨(b : G), hb⟩ * ⟨(a : G), ha⟩ := by
        exact isMulCommutative_iff.mp hI_abelian ⟨(a : G), ha⟩ ⟨(b : G), hb⟩
      exact congrArg Subtype.val this
    have hI'_le_F : I' ≤ fittingSubgroup (↥X) := by
      exact le_sSup ⟨hI'_normal, hI'_nil⟩
    intro y hy
    have hyI' : (⟨y, hIX hy⟩ : ↥X) ∈ I' := by simpa [I', Subgroup.mem_subgroupOf] using hy
    have hyF : (⟨y, hIX hy⟩ : ↥X) ∈ fittingSubgroup (↥X) := hI'_le_F hyI'
    simpa [fittingSubgroupOf] using (Subgroup.mem_map_of_mem X.subtype hyF)
  exact ⟨hI_abelian, hI_normal, hI_le_F⟩

end CFSG.GorensteinWalter
