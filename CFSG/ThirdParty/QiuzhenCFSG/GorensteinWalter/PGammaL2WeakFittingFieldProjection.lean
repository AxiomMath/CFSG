module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalPComplementCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FieldAutomorphismTorusPrimeFreePart
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The weak semilinear endpoint: trivial field projection from the inner involution centralizer

This is the source-faithful form of Bender's Fact 1.10(ii) used by the
equation-(4) route:  the transported involution centralizer `A` is squeezed
between the inner centralizer of the involution,

`C_L(τ) := C_{PΓL₂(K)}(τ) ∩ PSL₂(K) ≤ A ≤ C_{PΓL₂(K)}(τ)`,

and `N ◁ A` is nilpotent.  The goal is `N ≤ pGammaL2LinearKernel K A`
(trivial field projection).

The proof is the p-complement/Fitting package.  Let `U` be the PSL rotation
torus of order `(q ∓ 1)/2` inside `C_L(τ)`, normal in `A`, and let `U0` be
its normal `p`-complement (of order `divMaxPow ((q ∓ 1)/2) p`).

1. `U` (cyclic) is nilpotent, so `U ≤ F(A)`, hence `U0 ≤ F(A)`.
2. The `p`-Sylow `P` of `F(A)` whose field projection is the prime-order
   automorphism `σ` commutes elementwise with `U0`:  in the nilpotent group
   `F(A)` the `p`-core and the `p'`-core commute, `P` lies in the `p`-core
   and `U0` in the `p'`-core.
3. With `|K| = r^p` (`r` the fixed-field cardinality), the pointwise
   commutation with the prime-order field component forces the fixed-field
   torus divisibility `|U0| ∣ (r ∓ 1)/2` (the transport supplies the matched
   pair with `|U| = (q ∓ 1)/2`).
4. The p-complement cardinality gives `|U0| = divMaxPow ((q ∓ 1)/2, p)`; as
   `p` is odd, the `p`-free part of an even number is twice the `p`-free
   part of its half, so `divMaxPow (r^p ∓ 1, p) ∣ divMaxPow (r ∓ 1, p)`,
   which by the LTE bound forces `r^p ∓ 1 ≤ p (r ∓ 1)` — contradicting
   `r ≥ 3`, `p ≥ 3`.

The transport must still supply:  the PSL rotation torus `U` with its
normality/order data and the matched fixed-field divisibility pair
(`hU0fixed`), derived from the commutation of the `σ`-element with `U0`
and the split/nonsplit fixed-field cardinality theorems.
-/

set_option linter.unusedVariables false in

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups
open scoped commutatorElement

universe u

/-- `K` normalizes `H` when `H` is normal in `K`. -/
private theorem le_normalizer_of_isNormalIn_local
    {G : Type u} [Group G]
    {K H : Subgroup G} (hH : IsNormalIn H K) :
    K ≤ Subgroup.normalizer (H : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hH.2 x hx y hy
  · intro hy
    have hxinv : x⁻¹ ∈ K := K.inv_mem hx
    have h := hH.2 x⁻¹ hxinv (x * y * x⁻¹) hy
    simpa [mul_assoc] using h

/-- Normality inside a subgroup, as a `Subgroup.Normal` instance on the
restriction. -/
private theorem normal_subgroupOf_of_isNormalIn_local
    {G : Type u} [Group G]
    {N K : Subgroup G} (hNK : IsNormalIn N K) :
    (N.subgroupOf K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hNK.1).mpr
    (le_normalizer_of_isNormalIn_local hNK)

/-- The Fitting subgroup of a subgroup is normal in that subgroup. -/
private theorem fittingSubgroupOf_isNormalIn_local
    {G : Type u} [Group G] (A : Subgroup G) :
    IsNormalIn (fittingSubgroupOf (G := G) A) A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ A
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥A) * f * (⟨h, hh⟩ : ↥A)⁻¹ ∈ fittingSubgroup (↥A) := by
      exact (fittingSubgroup_normal (G := ↥A)).conj_mem (n := f) hf (g := ⟨h, hh⟩)
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥A) * f * (⟨h, hh⟩ : ↥A)⁻¹, hconj, ?_⟩
    rw [hfk]
    simp
    exact hfk

/-- The Fitting subgroup of a subgroup is nilpotent (as an ambient
subgroup). -/
private theorem fittingSubgroupOf_isNilpotent_local
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Group.IsNilpotent (↥(fittingSubgroupOf H)) := by
  change Group.IsNilpotent (↥((fittingSubgroup (↥H)).map H.subtype))
  have : Group.IsNilpotent (fittingSubgroup (↥H)) := by infer_instance
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective (fittingSubgroup (↥H)) H.subtype H.subtype_injective)

/-- The `p`-core and the `p'`-core of a finite group commute elementwise. -/
private theorem pCore_commute_pPrimeCore
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    ∀ x ∈ pCore p G, ∀ y ∈ pPrimeCore p G, x * y = y * x := by
  classical
  intro x hx y hy
  have hdisj : Disjoint (pCore p G) (pPrimeCore p G) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := G) (p := p)).exists_card_eq
    have hcop0 : Nat.Coprime (p ^ n) (Nat.card (pPrimeCore p G)) :=
      (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
    have hcop : (Nat.card (pCore p G)).Coprime (Nat.card (pPrimeCore p G)) := by
      simpa [hn] using hcop0
    exact Subgroup.disjoint_of_coprime_natCard hcop
  have hmem_comm : ⁅x, y⁆ ∈ ⁅pCore p G, pPrimeCore p G⁆ :=
    Subgroup.commutator_mem_commutator hx hy
  have hle : ⁅pCore p G, pPrimeCore p G⁆ ≤ pCore p G ⊓ pPrimeCore p G :=
    Subgroup.commutator_le_inf (H₁ := pCore p G) (H₂ := pPrimeCore p G)
  have hmem_inf : ⁅x, y⁆ ∈ pCore p G ⊓ pPrimeCore p G := hle hmem_comm
  have hinf_eq : pCore p G ⊓ pPrimeCore p G = ⊥ := disjoint_iff.mp hdisj
  rw [hinf_eq] at hmem_inf
  have h1 : ⁅x, y⁆ = (1 : G) := by simpa using hmem_inf
  rwa [commutatorElement_eq_one_iff_mul_comm] at h1

/-- In a finite group, a normal `p`-subgroup and a normal subgroup of order
prime to `p` commute elementwise. -/
private theorem commute_of_normal_pGroup_and_normal_pPrime
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P U0 : Subgroup G) [P.Normal] [U0.Normal]
    (hPp : IsPGroup p P) (hU0cop : Nat.Coprime p (Nat.card U0)) :
    ∀ x ∈ P, ∀ y ∈ U0, x * y = y * x := by
  intro x hx y hy
  have hxcore : x ∈ pCore p G := by
    change x ∈ sSup (normalPSubgroups p G)
    exact le_sSup (s := normalPSubgroups p G) ⟨inferInstance, hPp⟩ hx
  have hycore : y ∈ pPrimeCore p G := by
    change y ∈ sSup (normalPPrimeSubgroups p G)
    exact le_sSup (s := normalPPrimeSubgroups p G) ⟨inferInstance, hU0cop⟩ hy
  exact pCore_commute_pPrimeCore p x hxcore y hycore

/-- A number prime to `p` dividing `n` divides the `p`-free part of `n`. -/
private theorem divMaxPow_dvd_of_coprime_dvd
    (p m n : ℕ) (hcop : Nat.Coprime p m) (h : m ∣ n) :
    m ∣ n.divMaxPow p := by
  have hdecomp := Nat.pow_padicValNat_mul_divMaxPow p n
  rw [← hdecomp] at h
  have hcop' : Nat.Coprime m (p ^ padicValNat p n) :=
    hcop.symm.pow_right (padicValNat p n)
  rw [mul_comm] at h
  exact hcop'.dvd_of_dvd_mul_right h

/-- For an odd prime `p`, the `p`-free part of an even number is twice the
`p`-free part of its half. -/
private theorem divMaxPow_eq_two_mul_half (n p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hn : 2 ∣ n) : n.divMaxPow p = 2 * (n / 2).divMaxPow p := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hp1 : 1 < p := hp.one_lt
    have h2p : ¬ 2 ∣ p := by
      intro h
      exact hpodd.not_two_dvd_nat h
    let v := padicValNat p n
    let d := n.divMaxPow p
    have hdecomp : p ^ v * d = n := Nat.pow_padicValNat_mul_divMaxPow p n
    have hpd : ¬ p ∣ d := Nat.not_dvd_divMaxPow hp1 hn0
    have hcop : Nat.Coprime 2 (p ^ v) := by
      by_cases hv : v = 0
      · rw [hv, pow_zero]
        simp
      · have hcop2 : Nat.Coprime 2 p :=
          (Nat.Prime.coprime_iff_not_dvd (p := 2) (n := p) Nat.prime_two).mpr h2p
        exact (Nat.coprime_pow_right_iff (by omega : 0 < v) 2 p).mpr hcop2
    have h2d : 2 ∣ d := by
      have hdvd2 : 2 ∣ p ^ v * d := by simpa [hdecomp] using hn
      rw [mul_comm] at hdvd2
      exact hcop.dvd_of_dvd_mul_right hdvd2
    have hd2 : d = 2 * (d / 2) := by
      rw [mul_comm, Nat.div_mul_cancel h2d]
    have hhalf : n / 2 = p ^ v * (d / 2) := by
      have hn2 : n = 2 * (p ^ v * (d / 2)) := by
        calc
          n = p ^ v * d := hdecomp.symm
          _ = p ^ v * (2 * (d / 2)) := by rw [← hd2]
          _ = 2 * (p ^ v * (d / 2)) := by ring
      rw [hn2, mul_comm, Nat.mul_div_left]
      norm_num
    have hpd2 : ¬ p ∣ d / 2 := by
      intro h
      exact hpd (dvd_trans h ⟨2, by rw [mul_comm]; exact hd2⟩)
    have hnhalf : n / 2 ≠ 0 := by
      rcases hn with ⟨k, hk⟩
      have hdiv : (2 * k) / 2 = k := by
        rw [mul_comm]
        exact Nat.mul_div_left k (by norm_num : 0 < 2)
      rw [hk, hdiv]
      intro hk0
      apply hn0
      rw [hk, hk0, mul_zero]
    have hspec := Nat.maxPowDvdDiv_of_pow_mul_eq (p := p) (n := n / 2) (k := v) (l := d / 2)
      hnhalf hhalf.symm hpd2
    have hd2' : (n / 2).divMaxPow p = d / 2 := by
      have h' := congrArg Prod.snd hspec
      simpa [Nat.divMaxPow, Nat.maxPowDvdDiv, v, d] using h'
    change d = 2 * (n / 2).divMaxPow p
    rw [hd2, ← hd2']

/-- `3 * (p + 1) ≤ 3 ^ p` for `p ≥ 1`. -/
private theorem three_mul_succ_pow_le (p : ℕ) (hp : 2 ≤ p) :
    3 * (p + 1) ≤ 3 ^ p := by
  revert hp
  induction p with
  | zero =>
      intro hp
      omega
  | succ p ih =>
      intro hp
      rw [pow_succ]
      by_cases hp2 : 2 ≤ p
      · have h : 3 * (p + 1) ≤ 3 ^ p := ih hp2
        nlinarith
      · have hp1 : p = 1 := by omega
        subst p
        norm_num

/-- `3p ≤ 3^{p-1}` for `p ≥ 2`. -/
private theorem three_pow_sub_one_ge_three_mul (p : ℕ) (hp : 3 ≤ p) :
    3 * p ≤ 3 ^ (p - 1) := by
  have h := three_mul_succ_pow_le (p - 1) (by omega : 2 ≤ p - 1)
  have hsub : (p - 1) + 1 = p := by omega
  simpa [hsub] using h

/-- The torus orders are strictly larger than `p` times the fixed-field
parts: `r^p ∓ 1 > p (r ∓ 1)` for `r ≥ 3` and `p ≥ 3`. -/
private theorem primeFreeTorusStrictBound (r p : ℕ) (hr : 3 ≤ r)
    (hp : p.Prime) (hp3 : 3 ≤ p) :
    p * (r - 1) < r ^ p - 1 ∧ p * (r + 1) < r ^ p + 1 := by
  have hp1 : 1 ≤ p := hp.one_le
  have hp2 : 2 ≤ p := hp.two_le
  have h3p : 3 * p ≤ r ^ (p - 1) := by
    calc
      3 * p ≤ 3 ^ (p - 1) := three_pow_sub_one_ge_three_mul p hp3
      _ ≤ r ^ (p - 1) := Nat.pow_le_pow_left hr (p - 1)
  have hpow : r ^ p = r * r ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hx : r ^ (p - 1) * (r - 1) = r * r ^ (p - 1) - r ^ (p - 1) := by
    calc
      r ^ (p - 1) * (r - 1) = (r - 1) * r ^ (p - 1) := by rw [mul_comm]
      _ = r * r ^ (p - 1) - 1 * r ^ (p - 1) := by rw [Nat.mul_sub_right_distrib]
      _ = r * r ^ (p - 1) - r ^ (p - 1) := by rw [one_mul]
  have hmul : r ^ (p - 1) * (r - 1) ≤ r ^ p - 1 := by
    rw [hpow, hx]
    exact Nat.sub_le_sub_left
      (Nat.one_le_of_lt (pow_pos (by omega : 0 < r) (p - 1)))
      (r * r ^ (p - 1))
  constructor
  · have h1 : p * (r - 1) < 3 * p * (r - 1) := by
      have hpos : 0 < r - 1 := by omega
      exact Nat.mul_lt_mul_of_pos_right (by omega) hpos
    have h2 : 3 * p * (r - 1) ≤ r ^ (p - 1) * (r - 1) :=
      Nat.mul_le_mul_right (r - 1) h3p
    exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) hmul
  · have h1 : p * (r + 1) < 3 * p * (r - 1) := by
      have hratio : r + 1 < (r - 1) * 3 := by omega
      exact (Nat.mul_lt_mul_of_pos_left hratio hp.pos).trans_eq (by ring)
    have h2 : 3 * p * (r - 1) ≤ r ^ (p - 1) * (r - 1) :=
      Nat.mul_le_mul_right (r - 1) h3p
    have h3 : r ^ (p - 1) * (r - 1) < r ^ p + 1 := by
      rw [hpow, hx]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
    exact lt_trans (lt_of_lt_of_le h1 h2) h3

/-- The weak semilinear endpoint:  with `A` squeezed between the inner
centralizer of the involution `τ` and the full centralizer, and `N ◁ A`
nilpotent, the field projection of `N` is trivial — provided the torus data
(the PSL rotation torus `U`, its normal `p`-complement `U0`) and the
matched fixed-field divisibility pair. -/
public theorem pGammaL2_weak_normal_nilpotent_odd_fieldProjection_trivial
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (A : Subgroup (PGammaL2 K)) (τ : PGammaL2 K)
    (hτL : τ ∈ pGammaL2PSLRange K) (hτinv : IsInvolution τ)
    (hAcent : A ≤ Subgroup.centralizer ({τ} : Set (PGammaL2 K)))
    (hAcont : (Subgroup.centralizer ({τ} : Set (PGammaL2 K)) ⊓ pGammaL2PSLRange K) ≤ A)
    (N : Subgroup A) [N.Normal]
    (hNodd : Odd (Nat.card N)) (hNnil : Group.IsNilpotent N)
    -- the prime-order field component, living in a `p`-Sylow of `F(A)`:
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (σ : K ≃+* K) (hσord : orderOf σ = p)
    (P : Subgroup (PGammaL2 K))
    (hPleF : P ≤ fittingSubgroupOf A) (hPnormF : IsNormalIn P (fittingSubgroupOf A))
    (hPp : IsPGroup p P)
    (hPproj : ∃ a₀ : PGammaL2 K, a₀ ∈ P ∧ SemidirectProduct.rightHom a₀ = σ)
    -- the PSL rotation torus and its normal `p`-complement:
    (U : Subgroup (PGammaL2 K))
    (hUleC : U ≤ Subgroup.centralizer ({τ} : Set (PGammaL2 K)) ⊓ pGammaL2PSLRange K)
    (hUnormA : IsNormalIn U A) (hUcyclic : IsCyclic U) (hUnilp : Group.IsNilpotent U)
    (U0 : Subgroup (PGammaL2 K))
    (hU0leU : U0 ≤ U) (hU0normU : IsNormalIn U0 U) (hU0normA : IsNormalIn U0 A)
    (hU0cop : Nat.Coprime p (Nat.card U0))
    (hU0quot : IsPGroup p (↥U ⧸ U0.subgroupOf U))
    -- the fixed field: `r = |Fix σ|`, `|K| = r^p`, and the matched
    -- fixed-field torus divisibility (transport):
    (r : ℕ) (hr : 3 ≤ r) (hrOdd : Odd r) (hq : Nat.card K = r ^ p)
    (hU0fixed : ∀ a₀ : PGammaL2 K, a₀ ∈ P →
      SemidirectProduct.rightHom a₀ = σ →
      (∃ k : ℕ, a₀ ^ p ^ k = 1) →
      (∀ u : PGammaL2 K, u ∈ U0 → a₀ * u * a₀⁻¹ = u) →
      (Nat.card U = (Nat.card K - 1) / 2 ∧ Nat.card U0 ∣ (r - 1) / 2) ∨
      (Nat.card U = (Nat.card K + 1) / 2 ∧ Nat.card U0 ∣ (r + 1) / 2)) :
    N ≤ pGammaL2LinearKernel K A := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let F : Subgroup (PGammaL2 K) := fittingSubgroupOf A
  have hFnil : Group.IsNilpotent (↥F) := fittingSubgroupOf_isNilpotent_local A
  have hFnormA : IsNormalIn F A := fittingSubgroupOf_isNormalIn_local A
  have hFleA : F ≤ A := hFnormA.1
  -- `N ≤ F(A)`
  have hNleF : N.map A.subtype ≤ F := by
    have hNleFit : N ≤ fittingSubgroup (↥A) := by
      change N ≤ sSup {K : Subgroup (↥A) | K.Normal ∧ Group.IsNilpotent K}
      exact le_sSup ⟨inferInstance, hNnil⟩
    simpa [F, fittingSubgroupOf] using Subgroup.map_mono (f := A.subtype) hNleFit
  -- `U ≤ F(A)`
  have hUleA : U ≤ A := hUnormA.1
  have hUleF : U ≤ F := by
    have : (U.subgroupOf A).Normal := normal_subgroupOf_of_isNormalIn_local hUnormA
    have hUnilp' : Group.IsNilpotent (U.subgroupOf A) := by
      have : Group.IsNilpotent U := hUnilp
      exact Group.nilpotent_of_mulEquiv (G := U) (G' := U.subgroupOf A)
        (Subgroup.subgroupOfEquivOfLe hUleA).symm
    have hUleFit : U.subgroupOf A ≤ fittingSubgroup (↥A) := by
      change U.subgroupOf A ≤ sSup {K : Subgroup (↥A) | K.Normal ∧ Group.IsNilpotent K}
      exact le_sSup ⟨inferInstance, hUnilp'⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hUleA]
    exact Subgroup.map_mono (f := A.subtype) hUleFit
  -- `U0 ≤ F(A)`
  have hU0leF : U0 ≤ F := hU0leU.trans hUleF
  -- `U0 ◁ F(A)`
  have hU0normF : IsNormalIn U0 F := by
    refine ⟨hU0leF, ?_⟩
    intro f hf u hu
    exact hU0normA.2 f (hFleA hf) u hu
  -- the `p`-Sylow commutes with `U0` inside the nilpotent `F(A)`
  let P' : Subgroup (↥F) := P.subgroupOf F
  let U0' : Subgroup (↥F) := U0.subgroupOf F
  have : P'.Normal := normal_subgroupOf_of_isNormalIn_local hPnormF
  have : U0'.Normal := normal_subgroupOf_of_isNormalIn_local hU0normF
  have hP'p : IsPGroup p P' :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPleF).symm
  have hU0'cop : Nat.Coprime p (Nat.card U0') := by
    have hcard : Nat.card U0' = Nat.card U0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU0leF).toEquiv
    rw [hcard]
    exact hU0cop
  have hcomm : ∀ x : ↥F, x ∈ P' → ∀ y : ↥F, y ∈ U0' → x * y = y * x :=
    commute_of_normal_pGroup_and_normal_pPrime p P' U0' hP'p hU0'cop
  -- the `σ`-element of `P` fixes `U0` pointwise
  rcases hPproj with ⟨a₀, ha₀P, ha₀σ⟩
  have ha₀F : a₀ ∈ F := hPleF ha₀P
  have hfix : ∀ u ∈ U0, a₀ * u * a₀⁻¹ = u := by
    intro u hu
    have huF : u ∈ F := hU0leF hu
    have hc := hcomm ⟨a₀, ha₀F⟩ (Subgroup.mem_subgroupOf.mpr ha₀P)
      ⟨u, huF⟩ (Subgroup.mem_subgroupOf.mpr hu)
    calc
      a₀ * u * a₀⁻¹ = (a₀ * u) * a₀⁻¹ := by group
      _ = (u * a₀) * a₀⁻¹ := by
        congr 1
        exact congrArg (fun z : ↥F => (z : PGammaL2 K)) hc
      _ = u := by group
  have ha₀pow : ∃ k : ℕ, a₀ ^ p ^ k = 1 := by
    rcases hPp ⟨a₀, ha₀P⟩ with ⟨k, hk⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hU0fixed' := hU0fixed a₀ ha₀P ha₀σ ha₀pow hfix
  -- `|U0| = (|U|).divMaxPow p`
  have hU0card : Nat.card U0 = (Nat.card U).divMaxPow p := by
    have : (U0.subgroupOf U).Normal := normal_subgroupOf_of_isNormalIn_local hU0normU
    have hU0'copU : Nat.Coprime p (Nat.card (U0.subgroupOf U)) := by
      have hcard : Nat.card (U0.subgroupOf U) = Nat.card U0 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU0leU).toEquiv
      rw [hcard]
      exact hU0cop
    have h := normalPComplement_card_eq_divMaxPow p (Fact.out : p.Prime)
      (U0.subgroupOf U) hU0'copU hU0quot
    rw [← h]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU0leU).toEquiv).symm
  -- the fixed-field divisibility contradicts the LTE bound
  have hp3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hpne2 : p ≠ 2 := by
      intro h
      exact hpodd.not_two_dvd_nat (by simp [h])
    omega
  have hFalse : False := by
    rcases hU0fixed' with ⟨hUminus, hU0dvdr⟩ | ⟨hUplus, hU0dvdr⟩
    · have hU0card' : Nat.card U0 = ((r ^ p - 1) / 2).divMaxPow p := by
        rw [hU0card, hUminus, hq]
      have hU0dvd : Nat.card U0 ∣ ((r - 1) / 2).divMaxPow p :=
        divMaxPow_dvd_of_coprime_dvd p (Nat.card U0) ((r - 1) / 2) hU0cop hU0dvdr
      have hhalf : ((r ^ p - 1) / 2).divMaxPow p ∣ ((r - 1) / 2).divMaxPow p := by
        rwa [hU0card'] at hU0dvd
      have hfull : (r ^ p - 1).divMaxPow p ∣ (r - 1).divMaxPow p := by
        have h1 : (r ^ p - 1).divMaxPow p = 2 * ((r ^ p - 1) / 2).divMaxPow p :=
          divMaxPow_eq_two_mul_half (r ^ p - 1) p (Fact.out : p.Prime) hpodd
            (by
              have hodd : Odd (r ^ p) := hrOdd.pow (n := p)
              rcases hodd with ⟨k, hk⟩
              use k
              omega)
        have h2 : (r - 1).divMaxPow p = 2 * ((r - 1) / 2).divMaxPow p :=
          divMaxPow_eq_two_mul_half (r - 1) p (Fact.out : p.Prime) hpodd
            (by rcases hrOdd with ⟨k, hk⟩; use k; omega)
        rw [h1, h2]
        exact Nat.mul_dvd_mul (dvd_refl 2) hhalf
      have hle := (fieldAutomorphism_torus_primeFreePart_bounds r p hr
        (Fact.out : p.Prime) hpodd).1 hfull
      have hgt : p * (r - 1) < r ^ p - 1 :=
        (primeFreeTorusStrictBound r p hr (Fact.out : p.Prime) hp3).1
      omega
    · have hU0card' : Nat.card U0 = ((r ^ p + 1) / 2).divMaxPow p := by
        rw [hU0card, hUplus, hq]
      have hU0dvd : Nat.card U0 ∣ ((r + 1) / 2).divMaxPow p :=
        divMaxPow_dvd_of_coprime_dvd p (Nat.card U0) ((r + 1) / 2) hU0cop hU0dvdr
      have hhalf : ((r ^ p + 1) / 2).divMaxPow p ∣ ((r + 1) / 2).divMaxPow p := by
        rwa [hU0card'] at hU0dvd
      have hfull : (r ^ p + 1).divMaxPow p ∣ (r + 1).divMaxPow p := by
        have h1 : (r ^ p + 1).divMaxPow p = 2 * ((r ^ p + 1) / 2).divMaxPow p :=
          divMaxPow_eq_two_mul_half (r ^ p + 1) p (Fact.out : p.Prime) hpodd
            (by
              have hodd : Odd (r ^ p) := hrOdd.pow (n := p)
              rcases hodd with ⟨k, hk⟩
              use k + 1
              omega)
        have h2 : (r + 1).divMaxPow p = 2 * ((r + 1) / 2).divMaxPow p :=
          divMaxPow_eq_two_mul_half (r + 1) p (Fact.out : p.Prime) hpodd
            (by rcases hrOdd with ⟨k, hk⟩; use k + 1; omega)
        rw [h1, h2]
        exact Nat.mul_dvd_mul (dvd_refl 2) hhalf
      have hle := (fieldAutomorphism_torus_primeFreePart_bounds r p hr
        (Fact.out : p.Prime) hpodd).2 hfull
      have hgt : p * (r + 1) < r ^ p + 1 :=
        (primeFreeTorusStrictBound r p hr (Fact.out : p.Prime) hp3).2
      omega
  exact False.elim hFalse

end CFSG.GorensteinWalter
