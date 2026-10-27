module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostEquationFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentCenterLeFitting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (9): the `PSL₂(q)` numeric data

This module formalizes `refs/bender-dihedral-sylow.tex` L794–816 in the
`PSL₂` branch at the *quotient* level.  After the exclusion of the `A₇`
component, `E/Z(E) ≅ PSL₂(K)` and the source introduces the torus
parameters `k` (even) and `k'` (odd), the two halves `(q ± 1)/2`, with
`k = |K|·|S₀|` (`K = I_{U∩M}(s)` the equation-(1) inverted subgroup,
`S₀ = O₂(H∩E)` the cyclic index-two subgroup of the ambient Sylow `S`).

The final arithmetic (`SecondCaseLinearParameters` →
`secondCase_linearArithmetic`) needs only the numeric data `k`, `k'`,
`q ≥ 7`, `2p ≤ k`.  Following the integration route, this module exports
the **quotient-level numeric replacement**:

1. `k := |Kinv| · |c.S0|` (exactly the equation-(10) input), even because
   `t ∈ S₀` forces `2 | |S₀|`; `2p ≤ k` follows from `p | |Kinv|`.
2. `k ≤ |T|` by injecting the commuting, disjoint images of `Kinv` and
   `S₀` into the reflected torus `T ≤ E/Z(E)` (`SecondCasePSL2QuotientTorusCard`),
   once the ambient Sylow lies in `E` (`S ⊆ E`); `|T| ≤ (q+1)/2` is the
   Huppert split/nonsplit cardinal.
3. `k'` is the odd half, for `|M : H ∩ M| = q·k'` (`hMInter`).

Two genuinely missing source assertions are documented as explicit
prerequisites, not assumed inside the data package:

* `Z(E) = 1` (the odd-center `PSL₂` cover, `PSL2CenterlessCover`): the
  Schur-multiplier step for `PSL(2,q)`; `secondCase_equationNine_E_equiv_psl2_of_centerless`
  completes `E ≃ PSL₂(K)` once it lands.  The numeric package does not
  need it.
* `S ⊆ E` (ambient Sylow containment): the equation-(8) lane supplies it
  (source L804–816); here it is the explicit hypothesis `hSleE` of the
  constructor, used only for the `k ≤ |T|` bound.  The quotient-level
  Sylow-`2` cardinality transport through the odd central kernel
  (`secondCase_equationNine_componentSylowTwo_card_eq_quotient`) is proved
  independently.
* the dihedral-rotation fact that the image of the cyclic `S₀` in
  `E/Z(E)` lies in the torus (`S₀` is a cyclic `2`-subgroup of
  `C_{L₂(q)}(t)` containing `t`): hypothesis `hS0leT` of the constructor.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## The odd-center PSL₂ cover (unresolved prerequisite) -/

/-- The missing generic "odd-center PSL₂ cover" theorem: a perfect central
extension of `PSL₂(K)` whose center has odd order coprime to `|K|` is
trivial.  This is the Schur-multiplier statement for `PSL(2, q)`, `q` odd
(the multiplier has order 2 except at `q = 9`, where it has order 6 and its
`3`-part is killed by `3 ∣ q`).  The exact coprimality hypothesis required
is `Nat.Coprime (Nat.card (Subgroup.center E)) (Nat.card K)`, supplied by
`component_center_coprime_of_fitting_coprime` from the equation-(7) prime
information `Nat.Coprime (Nat.card (fittingSubgroupOf M)) (Nat.card K)`. -/
public def PSL2CenterlessCover (K : Type u) [Field K] [Finite K] : Prop :=
  ∀ {E : Type u} [Group E] [Finite E],
    Group.IsPerfect E →
      Odd (Nat.card (Subgroup.center E)) →
        Nat.Coprime (Nat.card (Subgroup.center E)) (Nat.card K) →
          Nonempty (E ⧸ Subgroup.center E ≃* PSL2 K) →
            Subgroup.center E = ⊥

/-- Given the (still missing) odd-center cover theorem, the selected
component is centerless and therefore isomorphic to `PSL₂(K)`: the headline
of source equation (9), `E ≃ L₂(q)`. -/
public theorem secondCase_equationNine_E_equiv_psl2_of_centerless
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (hZ : Subgroup.center d.E = ⊥) :
    Nonempty (d.E ≃* PSL2 K) := by
  let qbot : d.E ⧸ (⊥ : Subgroup d.E) ≃* d.E := QuotientGroup.quotientBot
  let eZ : d.E ⧸ (⊥ : Subgroup d.E) ≃* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.quotientMulEquivOfEq (G := d.E) (M := ⊥)
      (N := Subgroup.center d.E) hZ.symm
  exact ⟨qbot.symm.trans (eZ.trans e.some)⟩

/-! ## Quotient-level replacements (no `Z(E) = 1` needed) -/

/-- An inverted subgroup of odd order has trivial intersection with the odd
center of the component: `s` inverts every element of the subgroup while it
fixes the center pointwise, so an element of the intersection has order two
and odd order, hence is trivial.  Equivalently, the quotient map
`E → E/Z(E)` is injective on it. -/
private theorem inverted_odd_intersection_center_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (A : Subgroup G)
    (hA_le_U : A ≤ c.U)
    (hA_inv : ∀ x : G, x ∈ A → (s : G) * x * (s : G)⁻¹ = x⁻¹) :
    A ⊓ (Subgroup.center d.E).map d.E.subtype = ⊥ := by
  classical
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_bot]
  have hxA : x ∈ A := hx.1
  rcases Subgroup.mem_map.mp hx.2 with ⟨e, he, hxeq⟩
  have hxinv : s * x * (s : G)⁻¹ = x⁻¹ := hA_inv x hxA
  have hxfix : s * x * (s : G)⁻¹ = x := by
    rw [← hxeq]
    have hecomm : s * e = e * s := (Subgroup.mem_center_iff.mp he) s
    have hcommG : (s : G) * (e : G) = (e : G) * (s : G) :=
      congrArg Subtype.val hecomm
    rw [mul_inv_eq_iff_eq_mul]
    exact hcommG
  have hxx : x * x = 1 := by
    have hxeqinv : x = x⁻¹ := hxfix.symm.trans hxinv
    calc
      x * x = x * x⁻¹ := congrArg (fun y : G => x * y) hxeqinv
      _ = 1 := by simp
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hxodd : Odd (orderOf x) := by
    have hdvdU : orderOf x ∣ Nat.card c.U :=
      dvd_trans (Subgroup.orderOf_dvd_natCard A hxA) (Subgroup.card_dvd_of_le hA_le_U)
    exact Odd.of_dvd_nat hUodd hdvdU
  have hx1 : x = 1 := by
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hxx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [h2'] at hxodd
      rcases hxodd with ⟨k, hk⟩
      omega
  exact hx1

/-- The quotient map `E → E/Z(E)` is injective on an inverted odd
subgroup of `E`. -/
private theorem inverted_odd_quotient_injective
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (A : Subgroup G)
    (hA_le_U : A ≤ c.U)
    (hA_inv : ∀ x : G, x ∈ A → (s : G) * x * (s : G)⁻¹ = x⁻¹)
    (hA_le_E : A ≤ d.E) :
    Function.Injective
      (fun x : A => QuotientGroup.mk' (Subgroup.center d.E)
        (⟨(x : G), hA_le_E x.2⟩ : d.E)) := by
  classical
  have hbot := inverted_odd_intersection_center_eq_bot c w d s A
    hA_le_U hA_inv
  intro x y hq
  have hdiv : (⟨(x : G), hA_le_E x.2⟩ : d.E) / (⟨(y : G), hA_le_E y.2⟩ : d.E) ∈
      Subgroup.center d.E :=
    (QuotientGroup.eq_iff_div_mem (N := Subgroup.center d.E)).mp hq
  have hxyA : (x : G) / (y : G) ∈ A := A.div_mem x.2 y.2
  have hxyE : (x : G) / (y : G) ∈ d.E := hA_le_E hxyA
  have hz : (⟨(x : G) / (y : G), hxyE⟩ : d.E) ∈ Subgroup.center d.E := by
    change (⟨(x : G) / (y : G), hxyE⟩ : d.E) ∈ Subgroup.center d.E
    exact hdiv
  have hxyZ : (x : G) / (y : G) ∈
      (Subgroup.center d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨⟨(x : G) / (y : G), hxyE⟩, hz, rfl⟩
  have hxybot : (x : G) / (y : G) ∈
      A ⊓ (Subgroup.center d.E).map d.E.subtype := ⟨hxyA, hxyZ⟩
  have hxy1 : (x : G) / (y : G) = 1 := by
    rw [hbot] at hxybot
    exact Subgroup.mem_bot.mp hxybot
  apply Subtype.ext
  exact div_eq_one.mp hxy1

/-- The quotient image of an odd cyclic subgroup of `U` lies in the
reflected torus `T` of `E/Z(E)`: it is centralized by the image of `t`
(`U ≤ C_G(t)`), hence contained in `T` by the torus-maximality clause. -/
private theorem inverted_odd_quotient_le_torus
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (A : Subgroup G)
    (hA_le_U : A ≤ c.U)
    (hA_le_E : A ≤ d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hcontainT : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
            Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T) :
    (A.subgroupOf d.E).map (QuotientGroup.mk' (Subgroup.center d.E)) ≤ T := by
  classical
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  apply hcontainT
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    have hAodd : Odd (Nat.card A) :=
      Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hA_le_U)
    have hdvd : orderOf (y : G) ∣ Nat.card A :=
      Subgroup.orderOf_dvd_natCard A hyA
    have hoddY : Odd (orderOf y) := by
      simpa [Subgroup.orderOf_coe] using Odd.of_dvd_nat hAodd hdvd
    have hqdvd : orderOf (q y) ∣ orderOf y := by
      exact orderOf_dvd_of_pow_eq_one (by
        calc
          (q y) ^ orderOf y = q (y ^ orderOf y) := (map_pow q y (orderOf y)).symm
          _ = q 1 := by rw [pow_orderOf_eq_one y]
          _ = 1 := map_one q)
    exact Odd.of_dvd_nat hoddY hqdvd
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
    have hyU : (y : G) ∈ c.U := hA_le_U hyA
    have hyC : (y : G) ∈ c.H :=
      (Subgroup.map_subtype_le (pPrimeCore 2 c.H)) hyU
    have hyT : (y : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hyC
    have hcomm : (y : G) * c.t = c.t * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyT
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommE : y * (⟨c.t, d.t_mem_E⟩ : d.E) =
        (⟨c.t, d.t_mem_E⟩ : d.E) * y := Subtype.ext hcomm
    change q y * q (⟨c.t, d.t_mem_E⟩ : d.E) =
      q (⟨c.t, d.t_mem_E⟩ : d.E) * q y
    exact congrArg q hcommE

/-- The cardinal of the quotient image of an inverted odd subgroup of `E`
equals its own order (injectivity through the odd center). -/
private theorem inverted_odd_quotient_card_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (A : Subgroup G)
    (hA_le_U : A ≤ c.U)
    (hA_inv : ∀ x : G, x ∈ A → (s : G) * x * (s : G)⁻¹ = x⁻¹)
    (hA_le_E : A ≤ d.E) :
    Nat.card ((A.subgroupOf d.E).map (QuotientGroup.mk' (Subgroup.center d.E))) =
      Nat.card A := by
  classical
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  have hinj := inverted_odd_quotient_injective c w d s A
    hA_le_U hA_inv hA_le_E
  let f : A → ((A.subgroupOf d.E).map q : Subgroup (d.E ⧸ Subgroup.center d.E)) :=
    fun x => ⟨q (⟨(x : G), hA_le_E x.2⟩ : d.E),
      Subgroup.mem_map.mpr ⟨⟨(x : G), hA_le_E x.2⟩,
        Subgroup.mem_subgroupOf.mpr x.2, rfl⟩⟩
  have hsurj : Function.Surjective f := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨a, ha, hxy⟩
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    refine ⟨⟨(a : G), haA⟩, ?_⟩
    apply Subtype.ext
    change q (⟨(a : G), hA_le_E haA⟩ : d.E) = (y : d.E ⧸ Subgroup.center d.E)
    have hae : (⟨(a : G), hA_le_E haA⟩ : d.E) = a := by
      apply Subtype.ext
      rfl
    rw [hae]
    exact hxy
  have hinj' : Function.Injective f := by
    intro x y h
    apply hinj
    exact congrArg Subtype.val h
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj', hsurj⟩).symm)

/-- The equation-(3) subgroup `K₀ = F(U) ∩ K` has trivial intersection with
the odd center of the component (it is inverted by `s` and odd), so the
quotient map is injective on `K₀`. -/
public theorem secondCase_equationNine_K0_intersection_center_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hsI : IsInvolution s) :
    K0 ⊓ (Subgroup.center d.E).map d.E.subtype = ⊥ := by
  have hK0_le_U : K0 ≤ c.U := by
    intro a ha
    rw [hK0_def] at ha
    exact fittingSubgroupOf_le c.U ha.1
  have hK0_inv : ∀ x : G, x ∈ K0 → (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
    intro x hx
    have hxKinv : x ∈ Kinv := by
      rw [hK0_def] at hx
      exact hx.2
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hKinv_carrier]
      exact hxKinv
    rw [invertedElements] at hxI
    exact hxI.2
  exact inverted_odd_intersection_center_eq_bot c w d s K0
    hK0_le_U hK0_inv

/-- The quotient map `E → E/Z(E)` is injective on the subgroup `K₀`. -/
public theorem secondCase_equationNine_quotient_injective_on_K0
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hK0leE : K0 ≤ d.E)
    (hsI : IsInvolution s) :
    Function.Injective
      (fun x : K0 => QuotientGroup.mk' (Subgroup.center d.E)
        (⟨(x : G), hK0leE x.2⟩ : d.E)) := by
  have hK0_le_U : K0 ≤ c.U := by
    intro a ha
    rw [hK0_def] at ha
    exact fittingSubgroupOf_le c.U ha.1
  have hK0_inv : ∀ x : G, x ∈ K0 → (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
    intro x hx
    have hxKinv : x ∈ Kinv := by
      rw [hK0_def] at hx
      exact hx.2
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hKinv_carrier]
      exact hxKinv
    rw [invertedElements] at hxI
    exact hxI.2
  exact inverted_odd_quotient_injective c w d s K0 hK0_le_U hK0_inv hK0leE

/-- The quotient image of `K₀` lies in the reflected torus `T` of
`E/Z(E)`: `K₀` is cyclic of odd order and lies in `U ⊆ C_G(t)`, so its
image is an odd cyclic subgroup of `E/Z(E)` centralized by the image of
`t`, hence contained in `T` by the torus-maximality clause. -/
public theorem secondCase_equationNine_K0_quotient_le_torus
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hK0leE : K0 ≤ d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hcontainT : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
            Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T) :
    (K0.subgroupOf d.E).map (QuotientGroup.mk' (Subgroup.center d.E)) ≤ T := by
  have hK0_le_U : K0 ≤ c.U := by
    intro a ha
    rw [hK0_def] at ha
    exact fittingSubgroupOf_le c.U ha.1
  exact inverted_odd_quotient_le_torus c w d s K0 hK0_le_U hK0leE T hcontainT

/-- The cardinal form of the torus bound: `|K₀| ≤ |T|`.  Together with the
injectivity on `K₀` this is the quotient-level replacement for the `k/k'`
parameter data when `Z(E) = 1` is not available. -/
public theorem secondCase_equationNine_K0_card_le_torus
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hK0leE : K0 ≤ d.E)
    (hsI : IsInvolution s)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hcontainT : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
            Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T) :
    Nat.card K0 ≤ Nat.card T := by
  classical
  have hle := secondCase_equationNine_K0_quotient_le_torus c w d s Kinv K0
    hKinv_carrier hK0_def hK0leE T hcontainT
  have hK0_le_U : K0 ≤ c.U := by
    intro a ha
    rw [hK0_def] at ha
    exact fittingSubgroupOf_le c.U ha.1
  have hK0_inv : ∀ x : G, x ∈ K0 → (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
    intro x hx
    have hxKinv : x ∈ Kinv := by
      rw [hK0_def] at hx
      exact hx.2
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hKinv_carrier]
      exact hxKinv
    rw [invertedElements] at hxI
    exact hxI.2
  have hcard := inverted_odd_quotient_card_eq c w d s K0
    hK0_le_U hK0_inv hK0leE
  have hle2 : Nat.card ((K0.subgroupOf d.E).map
      (QuotientGroup.mk' (Subgroup.center d.E))) ≤ Nat.card T :=
    Subgroup.card_le_of_le hle
  rwa [hcard] at hle2

/-- The Sylow-`2` cardinality of the component transports through the odd
central kernel: the quotient map `E → E/Z(E)` is injective on a Sylow
`2`-subgroup (the kernel is the odd center), so `|S ∩ E|` equals the order
of its image, a Sylow `2`-subgroup of `E/Z(E) ≅ PSL₂(K)`.  This is the
quotient-level replacement for the source's `S₀ = O₂(H ∩ E)` cardinal data
when `Z(E) = 1` is not available. -/
public theorem secondCase_equationNine_componentSylowTwo_card_eq_quotient
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SE : Sylow 2 (↥d.E)) :
    Nat.card (SE : Subgroup d.E) =
      Nat.card (((SE : Subgroup d.E).map
        (QuotientGroup.mk' (Subgroup.center d.E))) :
          Subgroup (d.E ⧸ Subgroup.center d.E)) := by
  classical
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  have hSEp : IsPGroup 2 (SE : Subgroup d.E) := SE.isPGroup'
  have hcop : Nat.Coprime (Nat.card (SE : Subgroup d.E))
      (Nat.card (Subgroup.center d.E)) := by
    rcases hSEp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (d.center_odd.coprime_two_left).pow_left n
  have hdisj : Disjoint (SE : Subgroup d.E) (Subgroup.center d.E) :=
    Subgroup.disjoint_of_coprime_natCard hcop
  let S : Subgroup d.E := SE
  let f : ↥S →
      (S.map q : Subgroup (d.E ⧸ Subgroup.center d.E)) :=
    fun x => ⟨q x, Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y hq
    have hxqy : q (x : d.E) = q (y : d.E) := congrArg Subtype.val hq
    have hdiv : (x : d.E) / (y : d.E) ∈ Subgroup.center d.E :=
      (QuotientGroup.eq_iff_div_mem (N := Subgroup.center d.E)).mp hxqy
    have hdivSE : (x : d.E) / (y : d.E) ∈ (SE : Subgroup d.E) :=
      (SE : Subgroup d.E).div_mem x.2 y.2
    have hbot : (x : d.E) / (y : d.E) ∈ (⊥ : Subgroup d.E) := by
      have hmem : (x : d.E) / (y : d.E) ∈
          (SE : Subgroup d.E) ⊓ Subgroup.center d.E := ⟨hdivSE, hdiv⟩
      rwa [hdisj.eq_bot] at hmem
    have hxy : (x : d.E) / (y : d.E) = 1 := Subgroup.mem_bot.mp hbot
    apply Subtype.ext
    exact div_eq_one.mp hxy
  have hsurj : Function.Surjective f := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

/-! ## The `k ≤ |T|` injection (needs `S ⊆ E`) -/

/-- The injection of `Kinv` and `S₀` into the quotient torus: once the
ambient Sylow lies in `E`, both `Kinv` (odd cyclic, inverted by `s`) and
`S₀` (cyclic `2`-subgroup containing `t`, hence lying in the torus by the
dihedral-rotation fact `hS0leT`) embed into `T` with coprime orders, so
`k := |Kinv| · |S₀| ≤ |T|`. -/
public theorem secondCase_equationNine_k_le_torus
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hKinv_le_E : Kinv ≤ d.E)
    (hKinv_cyclic : IsCyclic Kinv)
    (hSleE : (c.S : Subgroup G) ≤ d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hcontainT : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
            Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T)
    (hS0leT : (c.S0.subgroupOf d.E).map
      (QuotientGroup.mk' (Subgroup.center d.E)) ≤ T) :
    Nat.card Kinv * Nat.card c.S0 ≤ Nat.card T := by
  classical
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let A : Subgroup Q := (Kinv.subgroupOf d.E).map q
  let B : Subgroup Q := (c.S0.subgroupOf d.E).map q
  have hKinv_le_U : Kinv ≤ c.U := by
    intro x hx
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rwa [← hKinv_carrier]
    exact hxI.1.1
  have hKinv_inv : ∀ x : G, x ∈ Kinv → (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
    intro x hx
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rwa [← hKinv_carrier]
    exact hxI.2
  have hA_le_T : A ≤ T :=
    inverted_odd_quotient_le_torus c w d s Kinv hKinv_le_U hKinv_le_E T hcontainT
  have hB_le_T : B ≤ T := hS0leT
  have hA_card : Nat.card A = Nat.card Kinv := by
    let fA : Kinv → A := fun x =>
      ⟨q ⟨(x : G), hKinv_le_E x.2⟩,
        Subgroup.mem_map.mpr ⟨⟨(x : G), hKinv_le_E x.2⟩,
          Subgroup.mem_subgroupOf.mpr x.2, rfl⟩⟩
    have hinjA : Function.Injective fA := by
      intro x y hxy
      have hqxy :
          (QuotientGroup.mk' (Subgroup.center d.E)
              (⟨(x : G), hKinv_le_E x.2⟩ : d.E)) =
            QuotientGroup.mk' (Subgroup.center d.E)
              (⟨(y : G), hKinv_le_E y.2⟩ : d.E) := by
        exact congrArg Subtype.val hxy
      exact (inverted_odd_quotient_injective c w d s Kinv hKinv_le_U
        hKinv_inv hKinv_le_E) hqxy
    have hsurjA : Function.Surjective fA := by
      intro y
      rcases Subgroup.mem_map.mp y.2 with ⟨a, ha, hxy⟩
      have haK : (a : G) ∈ Kinv := Subgroup.mem_subgroupOf.mp ha
      refine ⟨⟨(a : G), haK⟩, ?_⟩
      apply Subtype.ext
      change q (⟨(a : G), hKinv_le_E haK⟩ : d.E) = (y : Q)
      have hae : (⟨(a : G), hKinv_le_E haK⟩ : d.E) = a := by
        apply Subtype.ext
        rfl
      rw [hae]
      exact hxy
    exact (Nat.card_congr (Equiv.ofBijective fA ⟨hinjA, hsurjA⟩)).symm
  have hS0_le_E : c.S0 ≤ d.E := c.S0_le_S.trans hSleE
  have hS0even : 2 ∣ Nat.card c.S0 := by
    have hdvd : orderOf c.t ∣ Nat.card c.S0 :=
      Subgroup.orderOf_dvd_natCard c.S0 c.t_mem_S0
    have hord2 : orderOf c.t = 2 := by
      have hdvd2 : orderOf c.t ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using c.t_involution.2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
      · exfalso
        exact c.t_involution.1 (orderOf_eq_one_iff.mp h1)
      · exact h2
    simpa [hord2] using hdvd
  have hB_card : Nat.card B = Nat.card c.S0 := by
    have hZodd : Odd (Nat.card (Subgroup.center d.E)) := d.center_odd
    have hcop : Nat.Coprime (Nat.card (c.S0.subgroupOf d.E))
        (Nat.card (Subgroup.center d.E)) := by
      have hS0p : IsPGroup 2 (c.S0.subgroupOf d.E) := by
        have hpS0S : IsPGroup 2 (c.S0.subgroupOf (c.S : Subgroup G)) :=
          c.S.isPGroup'.to_subgroup (c.S0.subgroupOf (c.S : Subgroup G))
        have hS0pg : IsPGroup 2 c.S0 :=
          hpS0S.of_equiv (Subgroup.subgroupOfEquivOfLe c.S0_le_S)
        exact hS0pg.of_equiv
          (Subgroup.subgroupOfEquivOfLe (c.S0_le_S.trans hSleE)).symm
      rcases hS0p.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact hZodd.coprime_two_left.pow_left n
    have hdisj : Disjoint (c.S0.subgroupOf d.E) (Subgroup.center d.E) :=
      Subgroup.disjoint_of_coprime_natCard hcop
    let f : c.S0 → ((c.S0.subgroupOf d.E).map q : Subgroup Q) :=
      fun x => ⟨q ⟨(x : G), hS0_le_E x.2⟩,
        Subgroup.mem_map.mpr ⟨⟨(x : G), hS0_le_E x.2⟩,
          Subgroup.mem_subgroupOf.mpr x.2, rfl⟩⟩
    have hinj : Function.Injective f := by
      intro x y hq
      have hxqy : q ⟨(x : G), hS0_le_E x.2⟩ = q ⟨(y : G), hS0_le_E y.2⟩ :=
        congrArg Subtype.val hq
      have hdiv : (⟨(x : G), hS0_le_E x.2⟩ : d.E) /
          (⟨(y : G), hS0_le_E y.2⟩ : d.E) ∈ Subgroup.center d.E :=
        (QuotientGroup.eq_iff_div_mem (N := Subgroup.center d.E)).mp hxqy
      have hdivS0 : (x : G) / (y : G) ∈ c.S0 := c.S0.div_mem x.2 y.2
      have hdivE : (x : G) / (y : G) ∈ d.E := hS0_le_E hdivS0
      have hz : (⟨(x : G) / (y : G), hdivE⟩ : d.E) ∈ Subgroup.center d.E := by
        change (⟨(x : G) / (y : G), hdivE⟩ : d.E) ∈ Subgroup.center d.E
        exact hdiv
      have hzS0 : (⟨(x : G) / (y : G), hdivE⟩ : d.E) ∈
          (c.S0.subgroupOf d.E) ⊓ Subgroup.center d.E := by
        constructor
        · exact Subgroup.mem_subgroupOf.mpr hdivS0
        · exact hz
      have hbot : (x : G) / (y : G) ∈ (⊥ : Subgroup G) := by
        have hzS0bot : (⟨(x : G) / (y : G), hdivE⟩ : d.E) ∈
            (⊥ : Subgroup d.E) := by
          rwa [hdisj.eq_bot] at hzS0
        have hxy1 : (⟨(x : G) / (y : G), hdivE⟩ : d.E) = 1 :=
          Subgroup.mem_bot.mp hzS0bot
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val hxy1
      have hxy : (x : G) / (y : G) = 1 := Subgroup.mem_bot.mp hbot
      apply Subtype.ext
      exact div_eq_one.mp hxy
    have hsurj : Function.Surjective f := by
      intro y
      rcases Subgroup.mem_map.mp y.2 with ⟨a, ha, hxy⟩
      have haS0 : (a : G) ∈ c.S0 := Subgroup.mem_subgroupOf.mp ha
      refine ⟨⟨(a : G), haS0⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using hxy
    have hcard : Nat.card ((c.S0.subgroupOf d.E).map q) = Nat.card c.S0 :=
      (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm)
    simpa [B, q] using hcard
  -- the product injects into `T`: disjoint (odd vs 2-power) commuting
  -- (both in the cyclic torus) images
  have hKinv_odd_card : Odd (Nat.card Kinv) :=
    Odd.of_dvd_nat (by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H)
      (Subgroup.card_dvd_of_le hKinv_le_U)
  have hS0pow : ∃ m, Nat.card c.S0 = 2 ^ m := by
    rcases c.S.isPGroup'.exists_card_eq with ⟨n, hn⟩
    rcases n with _ | n
    · have hS : Nat.card (c.S : Subgroup G) = 1 := by simpa using hn
      rw [c.S_index_two] at hS
      omega
    · refine ⟨n, ?_⟩
      have hS : Nat.card (c.S : Subgroup G) = 2 ^ (n + 1) := hn
      have hEq : 2 * Nat.card c.S0 = 2 * 2 ^ n := by
        calc
          2 * Nat.card c.S0 = Nat.card (c.S : Subgroup G) := c.S_index_two.symm
          _ = 2 * 2 ^ n := by simpa [pow_succ, mul_comm] using hS
      exact Nat.mul_left_cancel (by norm_num) hEq
  have hAB : A ⊓ B = ⊥ := by
    have hcop : Nat.Coprime (Nat.card A) (Nat.card B) := by
      rw [hA_card, hB_card]
      rcases hS0pow with ⟨m, hm⟩
      rw [hm]
      have hmpos : 0 < m := by
        by_contra hm0
        have hm0' : m = 0 := by omega
        have hS0card : Nat.card c.S0 = 1 := by simpa [hm0'] using hm
        rw [hS0card] at hS0even
        norm_num at hS0even
      exact hKinv_odd_card.coprime_two_right.pow_right m
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  let f : ↥A × ↥B → ↥T := fun p =>
    ⟨(p.1 : Q) * (p.2 : Q), T.mul_mem (hA_le_T p.1.2) (hB_le_T p.2.2)⟩
  have hinj : Function.Injective f := by
    intro p p' hpp'
    have hpp : (p.1 : Q) * (p.2 : Q) = (p'.1 : Q) * (p'.2 : Q) :=
      congrArg Subtype.val hpp'
    have hab : (p'.1 : Q)⁻¹ * (p.1 : Q) =
        (p'.2 : Q) * (p.2 : Q)⁻¹ := by
      calc
        (p'.1 : Q)⁻¹ * (p.1 : Q) =
            (p'.1 : Q)⁻¹ * ((p.1 : Q) * (p.2 : Q)) *
              (p.2 : Q)⁻¹ := by group
        _ = (p'.1 : Q)⁻¹ * ((p'.1 : Q) * (p'.2 : Q)) *
              (p.2 : Q)⁻¹ := by rw [hpp]
        _ = (p'.2 : Q) * (p.2 : Q)⁻¹ := by group
    have hboth : (p'.1 : Q)⁻¹ * (p.1 : Q) ∈ A ⊓ B := by
      constructor
      · exact A.mul_mem (A.inv_mem p'.1.2) p.1.2
      · rw [hab]
        exact B.mul_mem p'.2.2 (B.inv_mem p.2.2)
    have h1 : (p'.1 : Q)⁻¹ * (p.1 : Q) = 1 := by
      have hb : (p'.1 : Q)⁻¹ * (p.1 : Q) ∈ (⊥ : Subgroup Q) := by
        rwa [hAB] at hboth
      exact Subgroup.mem_bot.mp hb
    have hp1 : (p.1 : Q) = (p'.1 : Q) := by
      calc
        (p.1 : Q) = (p'.1 : Q) * ((p'.1 : Q)⁻¹ * (p.1 : Q)) := by group
        _ = (p'.1 : Q) * 1 := by rw [h1]
        _ = (p'.1 : Q) := by simp
    have hp2 : (p.2 : Q) = (p'.2 : Q) := by
      have hpp' : (p.1 : Q) * (p.2 : Q) =
          (p.1 : Q) * (p'.2 : Q) := by
        rw [← hp1] at hpp
        exact hpp
      exact mul_left_cancel hpp'
    apply Prod.ext
    · apply Subtype.ext
      exact hp1
    · apply Subtype.ext
      exact hp2
  have hcard : Nat.card A * Nat.card B ≤ Nat.card T := by
    have hcard' : Nat.card (↥A × ↥B) ≤ Nat.card T :=
      Nat.card_le_card_of_injective f hinj
    simpa only [Nat.card_prod] using hcard'
  rw [hA_card, hB_card] at hcard
  exact hcard

/-! ## The equation-(9) data package -/

/-- The equation-(9) numeric data of the `PSL₂` branch, at the quotient
level: the `PSL₂(K)` model of `E/Z(E)`, the quotient reflected torus `T`
with `k := |Kinv| · |S₀|` even, the bound `k ≤ |T| ≤ (q+1)/2` (the
injection of `Kinv` and `S₀` into the torus, once `S ≤ E`), the odd
partner `k'`, and the rational bounds needed by
`SecondCaseLinearParameters`.  Neither `Z(E) = 1` nor `S ≤ E` is required
for the definition (`k` and `k'`); `S ≤ E` is used only for the `k ≤ |T|`
bound via the constructor hypothesis `hSleE`, and the dihedral-rotation
fact `S₀ ⊆ T` is the constructor hypothesis `hS0leT`.  `2p ≤ k` and
`q ≥ 7` follow from `p | |Kinv|` via
`secondCase_equationNine_two_p_le_k` and
`secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv`. -/
public structure SecondCaseLinearEquationNineData
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K] where
  primePower : IsOddPrimePower (Nat.card K)
  modelEquiv : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)
  /-- The quotient reflected torus carrying the even half `(q ± 1)/2`,
  containing the quotient involution. -/
  torus : SecondCasePSL2QuotientTorusCard d K
  /-- The equation-(1) inverted subgroup `K = I_{U∩M}(s)`. -/
  Kinv : Subgroup G
  /-- The equation-(3) intersection `K₀ = F(U) ∩ K`. -/
  K0 : Subgroup G
  Kinv_cyclic : IsCyclic Kinv
  K0_le_Kinv : K0 ≤ Kinv
  /-- `K₀ ≠ 1` (equations (5)--(7), via
  `secondCase_fitting_equation5_7_of_component_centralization`). -/
  K0_ne_bot : K0 ≠ ⊥
  /-- `K₀` is odd (it lies in `U = O(H)`). -/
  K0_odd : Odd (Nat.card K0)
  /-- The even torus parameter: `k = |Kinv| · |S₀|` (equation-(10) input). -/
  k : ℕ
  k_def : k = Nat.card Kinv * Nat.card c.S0
  /-- `k` is even because `t ∈ S₀` forces `2 | |S₀|`. -/
  k_even : Even k
  /-- The injection bound `k ≤ |T| ≤ (q + 1)/2` (once `S ≤ E`). -/
  k_le_torus : k ≤ Nat.card torus.T
  /-- The odd partner, the other half of `q ± 1`. -/
  k' : ℕ
  k'_odd : Odd k'
  k'_is_half : k' = (Nat.card K + 1) / 2 ∨ k' = (Nat.card K - 1) / 2
  /-- Rational form of `k ≤ (q + 1)/2`. -/
  hk_rat : (k : ℚ) ≤ ((Nat.card K : ℚ) + 1) / 2
  /-- Rational form of `(q - 1)/2 ≤ k'`. -/
  hk'_rat : ((Nat.card K : ℚ) - 1) / 2 ≤ (k' : ℚ)

/-- The equation-(9) constructor.  It consumes the quotient torus package
(`SecondCasePSL2QuotientTorusCard`, from the Huppert split/nonsplit data),
the equations-(1)--(3) decomposition data, the post-equation-four package
(`secondCase_fitting_equation5_7_of_component_centralization`, for
`K₀ ≠ 1`), the ambient Sylow containment `S ≤ E` (equation (8) lane), the
dihedral-rotation fact `S₀ ⊆ T`, and derives the even `k`, the injection
bound `k ≤ |T|`, and the rational parameter bounds.

Explicit unresolved prerequisites (taken as hypotheses):

* `hKinv_le_E` — the source's equation-(1) identity `K = [S∩E, U∩M] ⊆ E`;
* `hKinv_carrier/hK0_def/hsI` — the equations-(1)--(3) decomposition output;
* `hF_eq/hjoin/hFcentE/hLayer` — the inputs of the (5)--(7) transfer;
* `hSleE` — the ambient Sylow containment `S ≤ E` (equation-(8) lane);
* `hS0leT` — the dihedral-rotation fact that the image of the cyclic `S₀`
  in `E/Z(E)` lies in the torus;
* `k'` with `k'_is_half` and `k'_odd` — the naming of the odd partner. -/
@[expose] public noncomputable def secondCase_linearEquationNine_data
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (torus : SecondCasePSL2QuotientTorusCard d K)
    -- equations (1)--(3): the involution `s`, the inverted subgroup
    -- `Kinv`, and its Fitting intersection `K0`
    (s : d.E) (Kinv K0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hKinv_cyclic : IsCyclic Kinv)
    (hKinv_le_E : Kinv ≤ d.E)
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hsI : IsInvolution s)
    -- equations (4)--(7): the fixed part `F`, its component
    -- centralization, and the normalizer-layer control feeding the
    -- (5)--(7) transfer
    (F : Subgroup G)
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E)
    -- the ambient Sylow containment and the dihedral-rotation fact
    (hSleE : (c.S : Subgroup G) ≤ d.E)
    (hS0leT : (c.S0.subgroupOf d.E).map
      (QuotientGroup.mk' (Subgroup.center d.E)) ≤ torus.T)
    -- the torus parameters: `k = |Kinv|·|S₀|` even and `k'` the odd half
    (k k' : ℕ)
    (hk : k = Nat.card Kinv * Nat.card c.S0)
    (hk' : k' = (Nat.card K + 1) / 2 ∨ k' = (Nat.card K - 1) / 2)
    (hk'_odd : Odd k') :
    SecondCaseLinearEquationNineData d K := by
  classical
  -- the (5)--(7) package supplies K₀ ≠ 1
  have hK0le : K0 ≤ Kinv := by
    rw [hK0_def]
    exact inf_le_right
  have h57 := secondCase_fitting_equation5_7_of_component_centralization
    hmin c w d Kinv K0 F s hKinv_cyclic hK0le hF_eq hjoin hFcentE hLayer
  have hK0ne : K0 ≠ ⊥ := h57.2.2.2.2.2.2.2.1
  -- K₀ is odd
  have hK0leU : K0 ≤ c.U := by
    intro a ha
    rw [hK0_def] at ha
    exact fittingSubgroupOf_le c.U ha.1
  have hK0odd : Odd (Nat.card K0) :=
    Odd.of_dvd_nat (by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H)
      (Subgroup.card_dvd_of_le hK0leU)
  -- k is even and bounded by the torus
  have hS0even : 2 ∣ Nat.card c.S0 := by
    have hdvd : orderOf c.t ∣ Nat.card c.S0 :=
      Subgroup.orderOf_dvd_natCard c.S0 c.t_mem_S0
    have hord2 : orderOf c.t = 2 := by
      have hdvd2 : orderOf c.t ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using c.t_involution.2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
      · exfalso
        exact c.t_involution.1 (orderOf_eq_one_iff.mp h1)
      · exact h2
    simpa [hord2] using hdvd
  have hk_even : Even k := by
    rw [hk]
    rcases hS0even with ⟨a, ha⟩
    refine ⟨Nat.card Kinv * a, ?_⟩
    rw [ha]
    ring
  have hk_le_T : k ≤ Nat.card torus.T := by
    rw [hk]
    exact secondCase_equationNine_k_le_torus c w d s Kinv
      hKinv_carrier hKinv_le_E hKinv_cyclic hSleE torus.T
      torus.T_odd_centralized_le hS0leT
  -- the rational parameter bounds
  have hqodd : Odd (Nat.card K) := by
    rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
    rw [hcard]
    exact hpodd.pow
  have h2plus : 2 ∣ Nat.card K + 1 := by
    rcases hqodd with ⟨j, hj⟩
    refine ⟨j + 1, ?_⟩
    omega
  have h2minus : 2 ∣ Nat.card K - 1 := by
    rcases hqodd with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    omega
  have hcast_plus : (((Nat.card K + 1) / 2 : ℕ) : ℚ) =
      ((Nat.card K : ℚ) + 1) / 2 := by
    rw [Nat.cast_div h2plus (by norm_num : (2 : ℚ) ≠ 0)]
    norm_num
  have hcast_minus : (((Nat.card K - 1) / 2 : ℕ) : ℚ) =
      ((Nat.card K : ℚ) - 1) / 2 := by
    have hq1 : (1 : ℕ) ≤ Nat.card K := by omega
    rw [Nat.cast_div h2minus (by norm_num : (2 : ℚ) ≠ 0)]
    rw [Nat.cast_sub hq1]
    norm_num
  have hk_rat : (k : ℚ) ≤ ((Nat.card K : ℚ) + 1) / 2 := by
    have hkT : k ≤ (Nat.card K + 1) / 2 := by
      have hle2 := Nat.le_of_dvd
        (by have hpos : 0 < Nat.card torus.T := Nat.card_pos; omega :
          0 < 2 * Nat.card torus.T)
        (dvd_mul_right 2 (Nat.card torus.T))
      rcases torus.T_card with hTminus | hTplus
      · rcases hTminus with hTminus
        have h1 : k ≤ Nat.card torus.T := hk_le_T
        rw [hTminus] at h1
        omega
      · have h1 : k ≤ Nat.card torus.T := hk_le_T
        rw [hTplus] at h1
        omega
    rw [← hcast_plus]
    exact_mod_cast hkT
  have hk'_rat : ((Nat.card K : ℚ) - 1) / 2 ≤ (k' : ℚ) := by
    have hkT : (Nat.card K - 1) / 2 ≤ k' := by
      rcases hk' with hk'plus | hk'minus
      · rw [hk'plus]
        omega
      · rw [hk'minus]
    rw [← hcast_minus]
    exact_mod_cast hkT
  exact ⟨hK, e, torus, Kinv, K0, hKinv_cyclic, hK0le, hK0ne,
    hK0odd, k, hk, hk_even, hk_le_T, k', hk'_odd, hk', hk_rat, hk'_rat⟩

/-- From an odd prime divisor `p` of `|Kinv|` one gets `2p ≤ k`:
`2 | |S₀|` (because `t ∈ S₀`) and `p` are coprime, so `2p | |Kinv|·|S₀| = k`. -/
public theorem secondCase_equationNine_two_p_le_k
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (D : SecondCaseLinearEquationNineData d K) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p) (hpdvd : p ∣ Nat.card D.Kinv) :
    2 * p ≤ D.k := by
  have hS0even : 2 ∣ Nat.card c.S0 := by
    have hdvd : orderOf c.t ∣ Nat.card c.S0 :=
      Subgroup.orderOf_dvd_natCard c.S0 c.t_mem_S0
    have hord2 : orderOf c.t = 2 := by
      have hdvd2 : orderOf c.t ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using c.t_involution.2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
      · exfalso
        exact c.t_involution.1 (orderOf_eq_one_iff.mp h1)
      · exact h2
    simpa [hord2] using hdvd
  have hp_le : p ≤ Nat.card D.Kinv :=
    Nat.le_of_dvd (Nat.card_pos (α := D.Kinv)) hpdvd
  have h2_le : 2 ≤ Nat.card c.S0 := by
    rcases hS0even with ⟨a, ha⟩
    have ha0 : 0 < a := by
      have hpos : 0 < Nat.card c.S0 := Nat.card_pos
      rw [ha] at hpos
      omega
    rw [ha]
    omega
  have hprod : 2 * p ≤ Nat.card c.S0 * Nat.card D.Kinv := by
    nlinarith
  rw [D.k_def, mul_comm]
  simpa [Nat.mul_comm] using hprod

/-- `q ≥ 7` follows from `p | |Kinv|` (odd prime `p`): `2p ≤ k ≤ (q+1)/2`
and `p ≥ 3` give `q ≥ 4p - 1 ≥ 11`. -/
public theorem secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (D : SecondCaseLinearEquationNineData d K) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p) (hpdvd : p ∣ Nat.card D.Kinv) :
    7 ≤ Nat.card K := by
  have hpk := secondCase_equationNine_two_p_le_k d K D hp hpodd hpdvd
  have hp3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hp.two_le
    rcases hpodd with ⟨k, hk⟩
    omega
  have hkq : 2 * D.k ≤ Nat.card K + 1 := by
    have hkT : D.k ≤ Nat.card D.torus.T := D.k_le_torus
    have h2 : 2 * D.k ≤ 2 * Nat.card D.torus.T := by omega
    rcases D.torus.T_card with hTminus | hTplus
    · have hdm := Nat.div_mul_le_self (Nat.card K - 1) 2
      rw [← hTminus] at hdm
      omega
    · have hdm := Nat.div_mul_le_self (Nat.card K + 1) 2
      rw [← hTplus] at hdm
      omega
  omega

end CFSG.GorensteinWalter
