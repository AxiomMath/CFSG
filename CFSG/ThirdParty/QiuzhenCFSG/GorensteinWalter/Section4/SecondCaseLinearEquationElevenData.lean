module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostEquationFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_3_split
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (11): the `PSL₂` conjugate-count data package

This module formalizes Bender's equation (11) on page 227--228 of
`refs/bender-dihedral-sylow.tex` for the linear (`PSL₂`) branch: the
conjugate count of the chosen order-`p` subgroup and the resulting
cardinality inequality feeding `SecondCaseLinearParameters`.

   Landed; applies verbatim to `G = E/Z(E)` with the torus family on the
   quotient supplied at the integration site.

2. `secondCase_linearEquation11_E_orbit_card_lower_of_component` — the
   Section-4 ambient lower bound `q · k' ≤ |{R : Subgroup G // ∃ e : E,
   R = P0^e}|` for the internal order-`p` subgroup `P0 ≤ K₀ ≤ E`.  The
   image `P̄₀` of `P0` in `Ē = E/Z(E)` keeps order `p` (`P0 ∩ Z(E) = 1`:
   the involution `s` inverts `K₀` while fixing the odd center
   pointwise — proved in Section 0), its orbit in `Ē` has cardinal
   exactly `q · k'` by (1), and the map `X ↦ q(X)` from the `E`-orbit of
   `P0` onto the `Ē`-orbit of `P̄₀` is surjective because every quotient
   conjugator lifts by surjectivity of `q`; hence the lower bound — no
   centerless or `p`-coprime-center hypothesis is needed.  This is the
   `Tori` input (as a lower bound) of
   `secondCase_linearEquation11_product_family_conjugate_card`
   (`SecondCaseLinearEquationElevenProductFamily`).

3. Planned (designed, not yet written): the `PSL₂(K)`-side torus family
   (`secondCase_linearEquation11_psl2_torus_family`, from
   `huppert_II_8_5_a_psl2_partition` + `huppert_II_8_3_split_torus_normalizer_card`
   / `huppert_II_8_4_nonsplit_torus_normalizer_card` + `psl2_card_formula`),
   the `|Ē| = 2·q·k·k'` derivation (`secondCase_linearEquation11_quotient_card_of_model`),
   the natural region inequality
   `(p₁ - 1) · q · k' · L ≤ M.index`
   (`secondCase_linearEquation11_region_inequality`, via
   `Nat.card_mul_le_of_injective_pair` from `SecondCaseEquationEleven`,
   the per-`X` `Fin L` embedding, and `conjugate_family_card`), the
   rational export (`secondCase_linearEquation11_rational_inequality`
   with `L = (p₁ - 1)·(q·k' - 1) - (q - 1)/p·q` matching
   `SecondCaseLinearParameters.hL`/`h11`), and the source-specific region
   producer consuming the peers' region-`X` count, `M`-intersection count,
   bad-fibre bound and pair-uniqueness.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace CFSG.GorensteinWalter

universe u

/-! ## 0. The internal order-`p` subgroup `P0 ≤ K0` -/

/-- `P0 ∩ Z(E) = 1` for an order-`p` subgroup `P0` of the equation-(3)
subgroup `K₀`: the involution `s` inverts every element of `K₀` while it
fixes the (odd) center of the component pointwise, so an element of the
intersection has order two and odd order, hence is trivial.  This is the
quotient-injectivity input for the image `P̄₀` of `P0` in `E/Z(E)`. -/
private lemma P0_inter_center_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (s : d.E) (Kinv K0 P0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hP0leK0 : P0 ≤ K0) :
    P0 ⊓ (Subgroup.center d.E).map d.E.subtype = ⊥ := by
  classical
  let Z : Subgroup G := (Subgroup.center d.E).map d.E.subtype
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_bot]
  have hxP0 : x ∈ P0 := hx.1
  have hxK0 : x ∈ K0 := hP0leK0 hxP0
  rcases Subgroup.mem_map.mp hx.2 with ⟨e, he, hxeq⟩
  have hxKinv : x ∈ Kinv := by
    rw [hK0_def] at hxK0
    exact hxK0.2
  have hxinv : s * x * (s : G)⁻¹ = x⁻¹ := by
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hKinv_carrier]
      exact hxKinv
    rw [invertedElements] at hxI
    exact hxI.2
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
      x * x = x * x⁻¹ := congrArg (fun z : G => x * z) hxeqinv
      _ = 1 := by simp
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hxodd : Odd (orderOf x) := by
    have hK0leU : K0 ≤ c.U := by
      intro a ha
      rw [hK0_def] at ha
      exact fittingSubgroupOf_le c.U ha.1
    have hdvdU : orderOf x ∣ Nat.card c.U :=
      dvd_trans (Subgroup.orderOf_dvd_natCard K0 hxK0) (Subgroup.card_dvd_of_le hK0leU)
    exact Odd.of_dvd_nat hUodd hdvdU
  have hx1 : x = 1 := by
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hxx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [h2'] at hxodd
      norm_num at hxodd
  exact hx1

/-! ## 1. The abstract orbit count through a cyclic torus family -/

/-- The conjugacy orbit of a subgroup under the ambient conjugation action
(as an explicit family, avoiding a global action instance). -/
private def conjFamily (G : Type u) [Group G] (P : Subgroup G) :
    Type u :=
  {X : Subgroup G // ∃ g : G, X = P.map (MulAut.conj g).toMonoidHom}

private theorem conjugate_family_card
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) :
    Nat.card (conjFamily G P) =
      (Subgroup.normalizer (P : Set G)).index := by
  classical
  let : MulAction G (Subgroup G) :=
    { smul := fun g H => H.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro H
        change H.map (MulAut.conj (1 : G)).toMonoidHom = H
        apply Subgroup.ext
        intro x
        rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
          ext x; simp]
        simp
      mul_smul := by
        intro g h H
        change H.map (MulAut.conj (g * h)).toMonoidHom =
          (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have horbit :
      MulAction.orbit G P = {X : Subgroup G | ∃ g : G,
        X = P.map (MulAut.conj g).toMonoidHom} := by
    ext X
    constructor
    · intro hX
      rcases hX with ⟨g, rfl⟩
      exact ⟨g, by change P.map _ = _; rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, by change P.map _ = _; rfl⟩
  have hstab : MulAction.stabilizer G P =
      Subgroup.normalizer (P : Set G) := by
    ext g
    change g • P = P ↔ g ∈ Subgroup.normalizer (P : Set G)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer P),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
            MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  change Nat.card ↥{X : Subgroup G | ∃ g : G,
    X = P.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer G P, hstab]

/-- The elements of a subgroup of prime order `p` have order exactly `p`. -/
private lemma orderOf_eq_prime_of_mem
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hHcard : Nat.card H = p) {x : G} (hx : x ∈ H)
    (hx1 : x ≠ 1) :
    orderOf x = p := by
  have hdvd : orderOf x ∣ p := by
    simpa [hHcard] using Subgroup.orderOf_dvd_natCard H hx
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
  · exfalso
    exact hx1 (orderOf_eq_one_iff.mp h1)
  · exact hp

/-- A cyclic group of order `k` with `p ∣ k` has a unique subgroup of
order `p`. -/
public theorem secondCase_unique_order_p_subgroup_of_cyclic
    {G : Type u} [Group G] [Finite G] {T : Subgroup G} {k p : ℕ} [Fact p.Prime]
    (hTcyc : IsCyclic T) (hTcard : Nat.card T = k) (hpk : p ∣ k) :
    ∃! H : Subgroup G, H ≤ T ∧ Nat.card H = p := by
  classical
  let : Fintype T := Fintype.ofFinite T
  have hpk' : p ∣ Fintype.card T := by
    rw [← Nat.card_eq_fintype_card, hTcard]
    exact hpk
  let Alpha : Type u := {x : T // orderOf (x : G) = p}
  have hAlpha : Nat.card Alpha = p - 1 := by
    have hc : Fintype.card Alpha = p.totient := by
      rw [Fintype.card_subtype]
      simpa only [Subgroup.orderOf_coe] using hTcyc.card_orderOf_eq_totient hpk'
    rw [Nat.card_eq_fintype_card, hc]
    exact Nat.totient_prime (Fact.out : p.Prime)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := T) p
    (by rwa [← Nat.card_eq_fintype_card] at hpk')
  let H0 : Subgroup G := Subgroup.zpowers (y : G)
  have hH0le : H0 ≤ T := by
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    exact T.zpow_mem y.2 n
  have hH0card : Nat.card H0 = p := by
    rw [Nat.card_zpowers]
    exact (Subgroup.orderOf_coe y).trans hy
  let hH0sub : {z : H0 // (z : G) ≠ 1} → Alpha :=
    fun z => ⟨⟨(z : G), hH0le z.1.2⟩, orderOf_eq_prime_of_mem (H := H0)
      hH0card z.1.2 z.2⟩
  have hH0inj : Function.Injective hH0sub := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    change (a : G) = (b : G)
    simpa [hH0sub] using congrArg (fun t : Alpha => (t.1 : G)) hab
  have hH0card' : Nat.card {z : H0 // (z : G) ≠ 1} = p - 1 := by
    let : Fintype H0 := Fintype.ofFinite H0
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, hH0card]
    simp
  have hH0surj : Function.Surjective hH0sub := by
    let : Fintype {z : H0 // (z : G) ≠ 1} := Fintype.ofFinite _
    let : Fintype Alpha := Fintype.ofFinite Alpha
    have hcard : Fintype.card {z : H0 // (z : G) ≠ 1} =
        Fintype.card Alpha := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        hH0card', hAlpha]
    exact (Finite.injective_iff_surjective_of_equiv
      (Fintype.equivOfCardEq hcard)).mp hH0inj
  have hAlpha_sub : ∀ x : Alpha, (x.1 : G) ∈ H0 := by
    intro x
    rcases hH0surj x with ⟨z, hz⟩
    have hzG : (z : G) = (x.1 : G) := by
      simpa [hH0sub] using congrArg (fun t : Alpha => (t.1 : G)) hz
    rw [← hzG]
    exact z.1.2
  refine ⟨H0, ⟨hH0le, hH0card⟩, ?_⟩
  intro H hH
  rcases hH with ⟨hHle, hHcard⟩
  -- H = H0: both inclusions via the order-`p` element counts
  apply le_antisymm
  · intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact H0.one_mem
    · have hxT : x ∈ T := hHle hx
      have hxord : orderOf x = p := orderOf_eq_prime_of_mem (H := H)
        hHcard hx hx1
      exact hAlpha_sub ⟨⟨x, hxT⟩, hxord⟩
  · intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact H.one_mem
    · have hxord : orderOf x = p := orderOf_eq_prime_of_mem (H := H0)
        hH0card hx hx1
      have hxT : x ∈ T := hH0le hx
      let hHsub : {z : H // (z : G) ≠ 1} → Alpha :=
        fun z => ⟨⟨(z : G), hHle z.1.2⟩, orderOf_eq_prime_of_mem (H := H)
          hHcard z.1.2 z.2⟩
      have hHinj : Function.Injective hHsub := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        change (a : G) = (b : G)
        simpa [hHsub] using congrArg (fun t : Alpha => (t.1 : G)) hab
      have hHcard' : Nat.card {z : H // (z : G) ≠ 1} = p - 1 := by
        let : Fintype H := Fintype.ofFinite H
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
        rw [← Nat.card_eq_fintype_card, hHcard]
        simp
      have hHsurj : Function.Surjective hHsub := by
        let : Fintype {z : H // (z : G) ≠ 1} := Fintype.ofFinite _
        let : Fintype Alpha := Fintype.ofFinite Alpha
        have hcard : Fintype.card {z : H // (z : G) ≠ 1} =
            Fintype.card Alpha := by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
            hHcard', hAlpha]
        exact (Finite.injective_iff_surjective_of_equiv
          (Fintype.equivOfCardEq hcard)).mp hHinj
      rcases hHsurj (⟨⟨x, hxT⟩, hxord⟩ : Alpha) with ⟨z, hz⟩
      have hzG : (z : G) = x := by
        simpa [hHsub] using congrArg (fun t : Alpha => (t.1 : G)) hz
      rw [← hzG]
      exact z.1.2

/-- `g` normalizes `H` iff conjugation by `g` preserves `H`. -/
private lemma mem_normalizer_iff_conj_eq
    {G : Type u} [Group G] (H : Subgroup G) (g : G) :
    g ∈ Subgroup.normalizer (H : Set G) ↔
      H.map (MulAut.conj g).toMonoidHom = H := by
  classical
  constructor
  · intro hg
    apply Subgroup.ext
    intro z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨w, hw, hwz⟩
      have hiff := (Subgroup.mem_normalizer_iff.mp hg) w
      rw [← hwz]
      exact hiff.mp hw
    · intro hz
      have hiff := (Subgroup.mem_normalizer_iff.mp hg) (g⁻¹ * z * g)
      have h2 : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      rw [h2] at hiff
      have hz' : g⁻¹ * z * g ∈ H := hiff.mpr hz
      apply Subgroup.mem_map.mpr
      exact ⟨g⁻¹ * z * g, hz', by change g * (g⁻¹ * z * g) * g⁻¹ = z; group⟩
  · intro hg
    apply Subgroup.mem_normalizer_iff.mpr
    intro z
    constructor
    · intro hz
      have hz' : (MulAut.conj g).toMonoidHom z ∈
          H.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      simpa using (hg ▸ hz')
    · intro hz'
      have hz'' : (MulAut.conj g).toMonoidHom z ∈
          H.map (MulAut.conj g).toMonoidHom := by
        rw [← hg] at hz'
        exact hz'
      rcases Subgroup.mem_map.mp hz'' with ⟨w, hw, hwz⟩
      have hwz' : w = z := (MulAut.conj g).injective hwz
      rw [← hwz']
      exact hw

/-- The conjugacy orbit of an order-`p` subgroup in a unique cyclic torus
family has cardinal `q · k'`.

This is the abstract form of Bender's equation (11) input: `E` has `qk'`
subgroups of order `p`, and the orbit of the chosen `P` is exactly the
`qk'` torus-family conjugates because the normalizer of `P` equals the
normalizer of the unique torus containing it.  The hypotheses are the
abstract form of Huppert II.8.5(a) (cyclic torus of order `k`, normalizer
of order `2k`, and the restricted partition of order-`p` elements into the
torus conjugates) together with `|G| = 2 q k k'`.
-/
public theorem secondCase_linearEquation11_orbit_card_of_unique_torus_family
    {G : Type u} [Group G] [Finite G]
    {p q k k' : ℕ} [Fact p.Prime]
    (U : Subgroup G)
    (hcyc : IsCyclic U) (hUcard : Nat.card U = k)
    (hUN : Nat.card (Subgroup.normalizer (U : Set G)) = 2 * k)
    (hpart : ∀ x : G, orderOf x = p →
      ∃! T : {T : Subgroup G // ∃ g : G,
        T = U.map (MulAut.conj g).toMonoidHom}, (x : G) ∈ T.1)
    (hpk : p ∣ k)
    (hGcard : Nat.card G = 2 * q * k * k')
    (P0 : Subgroup G) (hP0card : Nat.card P0 = p) :
    Nat.card {P : Subgroup G // ∃ g : G,
      P = P0.map (MulAut.conj g).toMonoidHom} = q * k' := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hP0ne : P0 ≠ ⊥ := by
    intro hbot
    have hc : Nat.card P0 = 1 := Subgroup.card_eq_one.mpr hbot
    omega
  have hx : ∃ x : G, x ∈ P0 ∧ x ≠ 1 := by
    by_contra hx
    have hle : P0 ≤ (⊥ : Subgroup G) := by
      intro x hx0
      apply Subgroup.mem_bot.mpr
      by_contra hx1
      exact hx ⟨x, hx0, hx1⟩
    exact hP0ne (le_bot_iff.mp hle)
  obtain ⟨x, hxP, hx1⟩ := hx
  have hord : orderOf x = p := orderOf_eq_prime_of_mem (H := P0) hP0card hxP hx1
  let T0 : {T : Subgroup G // ∃ g : G,
      T = U.map (MulAut.conj g).toMonoidHom} := (hpart x hord).choose
  have hT0x : x ∈ T0.1 := (hpart x hord).choose_spec.1
  have hT0card : Nat.card T0.1 = k := by
    rcases T0.2 with ⟨g, hg⟩
    rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hUcard]
  have hT0cyc : IsCyclic T0.1 := by
    rcases T0.2 with ⟨g, hg⟩
    rw [hg]
    exact (MulEquiv.isCyclic ((MulAut.conj g).subgroupMap U)).mp hcyc
  -- P0 is the unique order-p subgroup of T0
  have hxzp : Subgroup.zpowers x ≤ P0 := Subgroup.zpowers_le.mpr hxP
  have hxzc : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hord]
  have hxPeq : Subgroup.zpowers x = P0 :=
    Subgroup.eq_of_le_of_card_ge hxzp (by rw [hP0card, hxzc])
  have hP0leT : P0 ≤ T0.1 := by
    intro y hy
    rw [← hxPeq] at hy
    rcases hy with ⟨n, rfl⟩
    exact T0.1.zpow_mem hT0x n
  have huniqueP0 : ∀ H : Subgroup G, H ≤ T0.1 → Nat.card H = p → H = P0 := by
    intro H hHle hHcard
    have huniq := secondCase_unique_order_p_subgroup_of_cyclic (G := G) (T := T0.1)
      (k := k) (p := p) hT0cyc hT0card hpk
    exact ExistsUnique.unique huniq (y₁ := H) (y₂ := P0) ⟨hHle, hHcard⟩ ⟨hP0leT, hP0card⟩
  -- N(P0) = N(T0): both inclusions
  have hNge : Subgroup.normalizer (P0 : Set G) ≤
      Subgroup.normalizer (T0.1 : Set G) := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (P0 : Set G) := hg
    -- T0 = T0^g via the partition at `x`
    have hxT0g : x ∈ T0.1.map (MulAut.conj g).toMonoidHom := by
      have hxP0g : x ∈ P0.map (MulAut.conj g).toMonoidHom := by
        have hpre : g⁻¹ * x * g ∈ P0 := by
          have hiff := (Subgroup.mem_normalizer_iff.mp hgN) (g⁻¹ * x * g)
          have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
          rw [h2] at hiff
          exact hiff.mpr hxP
        exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hpre, by
          change g * (g⁻¹ * x * g) * g⁻¹ = x
          group⟩
      rcases Subgroup.mem_map.mp hxP0g with ⟨y, hy, hyx⟩
      exact Subgroup.mem_map.mpr ⟨y, hP0leT hy, hyx⟩
    have hT0g_in_family : ∃ g' : G,
        T0.1.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj g').toMonoidHom := by
      rcases T0.2 with ⟨g0, hg0⟩
      refine ⟨g * g0, ?_⟩
      rw [hg0]
      rw [Subgroup.map_map]
      congr 1
      ext t
      simp [MulAut.conj_apply, mul_assoc]
    have hTeq : T0.1 = T0.1.map (MulAut.conj g).toMonoidHom := by
      have huniq := ExistsUnique.unique (hpart x hord) (y₁ := T0)
        (y₂ := ⟨T0.1.map (MulAut.conj g).toMonoidHom, hT0g_in_family⟩)
        hT0x hxT0g
      exact congrArg Subtype.val huniq
    exact (mem_normalizer_iff_conj_eq T0.1 g).mpr hTeq.symm
  have hNle : Subgroup.normalizer (T0.1 : Set G) ≤
      Subgroup.normalizer (P0 : Set G) := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (T0.1 : Set G) := hg
    -- P0^g = P0: ⟨x⟩^g = ⟨x^g⟩ and x^g generates P0
    have hcxT : (MulAut.conj g).toMonoidHom x ∈ T0.1 := by
      simpa using ((Subgroup.mem_normalizer_iff.mp hgN) x).mp hT0x
    have hcxord : orderOf ((MulAut.conj g).toMonoidHom x) = p := by
      rw [orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x]
      exact hord
    have hcxle : Subgroup.zpowers ((MulAut.conj g).toMonoidHom x) ≤ T0.1 := by
      intro t ht
      rcases ht with ⟨n, rfl⟩
      exact T0.1.zpow_mem hcxT n
    have hcxcard : Nat.card (Subgroup.zpowers ((MulAut.conj g).toMonoidHom x)) = p := by
      rw [Nat.card_zpowers, hcxord]
    have hcxP : Subgroup.zpowers ((MulAut.conj g).toMonoidHom x) = P0 :=
      huniqueP0 (Subgroup.zpowers ((MulAut.conj g).toMonoidHom x)) hcxle hcxcard
    have hP0g : P0.map (MulAut.conj g).toMonoidHom = P0 := by
      calc
        P0.map (MulAut.conj g).toMonoidHom =
            (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom := by rw [← hxPeq]
        _ = Subgroup.zpowers ((MulAut.conj g).toMonoidHom x) := by
          apply Subgroup.ext
          intro t
          constructor
          · intro ht
            rcases Subgroup.mem_map.mp ht with ⟨w, hw, hwt⟩
            rcases hw with ⟨n, rfl⟩
            refine ⟨n, ?_⟩
            rw [← hwt]
            exact (map_zpow (MulAut.conj g).toMonoidHom x n).symm
          · intro ht
            rcases ht with ⟨n, rfl⟩
            exact Subgroup.mem_map.mpr ⟨x ^ n, ⟨n, rfl⟩,
              map_zpow (MulAut.conj g).toMonoidHom x n⟩
        _ = P0 := hcxP
    exact (mem_normalizer_iff_conj_eq P0 g).mpr hP0g

  -- |orbit| = [G : N(P0)] = [G : N(T0)] = |family of T0| = |family of U| = q·k'
  have hOrb : Nat.card {P : Subgroup G // ∃ g : G,
      P = P0.map (MulAut.conj g).toMonoidHom} = q * k' := by
    have hOrb' : Nat.card {P : Subgroup G // ∃ g : G,
        P = P0.map (MulAut.conj g).toMonoidHom} =
        (Subgroup.normalizer (P0 : Set G)).index :=
      conjugate_family_card P0
    have hN0 : Subgroup.normalizer (P0 : Set G) =
        Subgroup.normalizer (T0.1 : Set G) := le_antisymm hNge hNle
    have hfamU : Nat.card {X : Subgroup G // ∃ g : G,
        X = U.map (MulAut.conj g).toMonoidHom} = q * k' := by
      have hcard : Nat.card {X : Subgroup G // ∃ g : G,
          X = U.map (MulAut.conj g).toMonoidHom} =
          (Subgroup.normalizer (U : Set G)).index :=
        conjugate_family_card U
      have hindex : (Subgroup.normalizer (U : Set G)).index =
          Nat.card G / Nat.card (Subgroup.normalizer (U : Set G)) := by
        rw [Subgroup.index_eq_card]
        have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.normalizer (U : Set G))
        have hdiv : Nat.card G / Nat.card (Subgroup.normalizer (U : Set G)) =
            Nat.card (G ⧸ Subgroup.normalizer (U : Set G)) := by
          apply Nat.div_eq_of_eq_mul_right (Nat.card_pos)
          simpa [mul_comm] using hm
        exact hdiv.symm
      rw [hcard, hindex, hGcard, hUN]
      have hkpos : 0 < k := by
        simpa [← hUcard] using (Nat.card_pos (α := U))
      rw [Nat.div_eq_of_eq_mul_right (by omega)]
      simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hfamT0 : Nat.card {X : Subgroup G // ∃ g : G,
        X = T0.1.map (MulAut.conj g).toMonoidHom} = q * k' := by
      let F1 : Type u := {X : Subgroup G // ∃ g : G,
        X = T0.1.map (MulAut.conj g).toMonoidHom}
      let F2 : Type u := {X : Subgroup G // ∃ g : G,
        X = U.map (MulAut.conj g).toMonoidHom}
      let f : F1 → F2 := fun X => ⟨X.1, by
        rcases X.2 with ⟨g, hg⟩
        rcases T0.2 with ⟨g0, hg0⟩
        refine ⟨g * g0, ?_⟩
        rw [hg, hg0, Subgroup.map_map]
        congr 1
        ext t
        simp [MulAut.conj_apply, mul_assoc]⟩
      let finv : F2 → F1 := fun X => ⟨X.1, by
        rcases X.2 with ⟨g, hg⟩
        rcases T0.2 with ⟨g0, hg0⟩
        refine ⟨g * g0⁻¹, ?_⟩
        rw [hg, hg0, Subgroup.map_map]
        congr 1
        ext t
        simp [MulAut.conj_apply, mul_assoc]⟩
      have hleft : Function.LeftInverse finv f := by
        intro X
        apply Subtype.ext
        rfl
      have hright : Function.RightInverse finv f := by
        intro X
        apply Subtype.ext
        rfl
      exact (Nat.card_congr (Equiv.ofBijective f ⟨hleft.injective, hright.surjective⟩)).trans hfamU
    have hindexN0 : (Subgroup.normalizer (P0 : Set G)).index = q * k' := by
      rw [hN0]
      exact (conjugate_family_card T0.1).symm.trans hfamT0
    rw [hOrb', hindexN0]
  exact hOrb


/-! ## 2. The internal orbit through `E/Z(E)` -/

/-- Unfolding of the conjugation action. -/
private lemma conj_mul_eq {G : Type u} [Group G] (g x : G) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by
  rfl

/-- For `e ∈ E`, the quotient of the conjugate `P0^e` agrees with the
conjugate of the quotient. -/
private lemma quotient_conj_comm
    {G : Type u} [Group G] (E : Subgroup G) (P0 : Subgroup G)
    (hP0leE : P0 ≤ E) (e : E) :
    ((P0.map (MulAut.conj (e : G)).toMonoidHom).subgroupOf E).map
        (QuotientGroup.mk' (Subgroup.center E)) =
      ((P0.subgroupOf E).map (QuotientGroup.mk' (Subgroup.center E))).map
        (MulAut.conj (QuotientGroup.mk' (Subgroup.center E) e)).toMonoidHom := by
  let q : E →* E ⧸ Subgroup.center E := QuotientGroup.mk' (Subgroup.center E)
  apply Subgroup.ext
  intro z
  constructor
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, hwz⟩
    have hwG : (w : G) ∈ P0.map (MulAut.conj (e : G)).toMonoidHom := Subgroup.mem_comap.mp hw
    rcases Subgroup.mem_map.mp hwG with ⟨x, hx, hxw⟩
    let xE : E := ⟨(x : G), hP0leE hx⟩
    -- the RHS membership: z = (conj (q e)) (q xE)
    refine Subgroup.mem_map.mpr ⟨q xE, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨xE, Subgroup.mem_comap.mpr hx, rfl⟩
    · calc
        (MulAut.conj (q e)).toMonoidHom (q xE)
            = q e * q xE * (q e)⁻¹ := by exact conj_mul_eq (q e) (q xE)
        _ = q (⟨(e : G) * (x : G) * (e : G)⁻¹,
              E.mul_mem (E.mul_mem e.2 (hP0leE hx)) (E.inv_mem e.2)⟩ : E) := by
              change q (e * xE * e⁻¹) = q e * q xE * (q e)⁻¹
              rw [map_mul, map_mul, map_inv]
        _ = q w := by
              congr 1
              simpa [Subtype.ext_iff, mul_assoc] using (conj_mul_eq (e : G) (x : G)).trans hxw
        _ = z := hwz
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, hyz⟩
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
    -- hx : x ∈ P0.subgroupOf E — hmm — x : E with (x : G) ∈ P0 — hxy : q x = y — hyz : (conj (q e)) y = z
    have hxG : (x : G) ∈ P0 := Subgroup.mem_comap.mp hx
    let exe : E := ⟨(e : G) * (x : G) * (e : G)⁻¹,
      E.mul_mem (E.mul_mem e.2 (hP0leE hxG)) (E.inv_mem e.2)⟩
    refine Subgroup.mem_map.mpr ⟨exe, ?_, ?_⟩
    · -- exe ∈ (P0^e).subgroupOf E
      exact Subgroup.mem_comap.mpr
        (Subgroup.mem_map.mpr ⟨(x : G), hxG, by exact conj_mul_eq (e : G) (x : G)⟩)
    · calc
        q exe = q e * q ⟨(x : G), hP0leE hxG⟩ * (q e)⁻¹ := by
          change q (e * ⟨(x : G), hP0leE hxG⟩ * e⁻¹) = q e * q ⟨(x : G), hP0leE hxG⟩ * (q e)⁻¹
          rw [map_mul, map_mul, map_inv]
        _ = (MulAut.conj (q e)).toMonoidHom (q ⟨(x : G), hP0leE hxG⟩) := by
              exact (conj_mul_eq (q e) (q ⟨(x : G), hP0leE hxG⟩)).symm
        _ = (MulAut.conj (q e)).toMonoidHom y := by rw [hxy]
        _ = z := hyz

/-- The `E`-conjugacy orbit of the internal order-`p` subgroup `P0 ≤ K₀`
contains at least `q · k'` ambient conjugates.

The image `P̄₀` of `P0` in `Ē = E/Z(E)` has order `p` (`P0 ∩ Z(E) = 1`:
the involution `s` inverts every element of `K₀` while it fixes the odd
center pointwise), and the conjugacy orbit of `P̄₀` in `Ē` has cardinal
exactly `q · k'`
(`secondCase_linearEquation11_orbit_card_of_unique_torus_family` applied
to the torus family on `Ē`).  The map `X ↦ q(X)` from the `E`-orbit of
`P0` onto the `Ē`-orbit of `P̄₀` is surjective because every quotient
conjugator lifts by surjectivity of `q`; hence `q · k' ≤ |E-orbit of P0|`.
No centerless or `p`-coprime-center hypothesis is needed.  This is the
`Tori` input of the product-family count (as a lower bound). -/
public theorem secondCase_linearEquation11_E_orbit_card_lower_of_component
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    {p q k k' : ℕ} [Fact p.Prime]
    (s : d.E) (Kinv K0 P0 : Subgroup G)
    (hKinv_carrier : (Kinv : Set G) = invertedElements (c.U ⊓ w.M) (s : G))
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hP0leK0 : P0 ≤ K0) (hK0leE : K0 ≤ d.E)
    (hP0card : Nat.card P0 = p)
    -- the torus family on Ē = E/Z(E) (Huppert II.8.5(a) transported)
    (U : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hcyc : IsCyclic U) (hUcard : Nat.card U = k)
    (hUN : Nat.card (Subgroup.normalizer (U : Set (d.E ⧸ Subgroup.center d.E))) = 2 * k)
    (hpart : ∀ x : d.E ⧸ Subgroup.center d.E, orderOf x = p →
      ∃! T : {T : Subgroup (d.E ⧸ Subgroup.center d.E) // ∃ g : d.E ⧸ Subgroup.center d.E,
        T = U.map (MulAut.conj g).toMonoidHom}, (x : d.E ⧸ Subgroup.center d.E) ∈ T.1)
    (hpk : p ∣ k)
    (hGcard : Nat.card (d.E ⧸ Subgroup.center d.E) = 2 * q * k * k') :
    q * k' ≤ Nat.card {R : Subgroup G // ∃ e : d.E,
      R = P0.map (MulAut.conj (e : G)).toMonoidHom} := by
  classical
  let Ebar : Type u := d.E ⧸ Subgroup.center d.E
  let qbar : d.E →* Ebar := QuotientGroup.mk' (Subgroup.center d.E)
  let P0bar : Subgroup Ebar := (P0.subgroupOf d.E).map qbar
  have hP0leE : P0 ≤ d.E := hP0leK0.trans hK0leE
  -- |P̄₀| = p
  have hP0Z : P0 ⊓ (Subgroup.center d.E).map d.E.subtype = ⊥ :=
    P0_inter_center_eq_bot c w d s Kinv K0 P0 hKinv_carrier hK0_def hP0leK0
  have hP0bar_card : Nat.card P0bar = p := by
    let phi0 : P0 → P0bar := fun x =>
      ⟨qbar ⟨(x : G), hP0leE x.2⟩,
        Subgroup.mem_map.mpr ⟨⟨(x : G), hP0leE x.2⟩, Subgroup.mem_comap.mpr x.2, rfl⟩⟩
    have hinj : Function.Injective phi0 := by
      intro x y hxy
      apply Subtype.ext
      have hq : qbar ⟨(x : G), hP0leE x.2⟩ = qbar ⟨(y : G), hP0leE y.2⟩ := congrArg Subtype.val hxy
      have hdivE : ⟨(x : G), hP0leE x.2⟩ / ⟨(y : G), hP0leE y.2⟩ ∈ Subgroup.center d.E :=
        (QuotientGroup.eq_iff_div_mem (N := Subgroup.center d.E)).mp hq
      have hxyZ : (x : G) / (y : G) ∈ (Subgroup.center d.E).map d.E.subtype :=
        Subgroup.mem_map.mpr
          ⟨⟨(x : G) / (y : G), d.E.div_mem (hP0leE x.2) (hP0leE y.2)⟩, hdivE, rfl⟩
      have hxyP : (x : G) / (y : G) ∈ P0 := P0.div_mem x.2 y.2
      have hxybot : (x : G) / (y : G) ∈ P0 ⊓ (Subgroup.center d.E).map d.E.subtype := ⟨hxyP, hxyZ⟩
      have hxy1 : (x : G) / (y : G) = 1 := Subgroup.mem_bot.mp (by rwa [hP0Z] at hxybot)
      exact div_eq_one.mp hxy1
    have hsurj : Function.Surjective phi0 := by
      intro y
      rcases Subgroup.mem_map.mp y.2 with ⟨z, hz, hzy⟩
      refine ⟨⟨(z : G), Subgroup.mem_comap.mp hz⟩, ?_⟩
      apply Subtype.ext
      calc
        qbar ⟨(z : G), hP0leE (Subgroup.mem_comap.mp hz)⟩ = qbar z := by
          congr 1
        _ = y.1 := hzy
    have hEq : Nat.card P0 = Nat.card P0bar :=
      Nat.card_congr (Equiv.ofBijective phi0 ⟨hinj, hsurj⟩)
    rw [← hEq, hP0card]
  -- the orbit of P̄₀ in Ē has cardinal exactly q·k'
  have hQOrbit : Nat.card {X : Subgroup Ebar // ∃ g : Ebar,
      X = P0bar.map (MulAut.conj g).toMonoidHom} = q * k' :=
    secondCase_linearEquation11_orbit_card_of_unique_torus_family
      (G := Ebar) (U := U) hcyc hUcard hUN hpart hpk hGcard P0bar hP0bar_card
  -- the surjection from the E-orbit of P0 onto the quotient orbit
  let EOrbit : Type u := {R : Subgroup G // ∃ e : d.E,
    R = P0.map (MulAut.conj (e : G)).toMonoidHom}
  let QOrbit : Type u := {X : Subgroup Ebar // ∃ g : Ebar,
    X = P0bar.map (MulAut.conj g).toMonoidHom}
  let phi : EOrbit → QOrbit := fun R =>
    ⟨(R.1.subgroupOf d.E).map qbar, by
      rcases R.2 with ⟨e, he⟩
      refine ⟨qbar e, ?_⟩
      rw [he]
      change ((P0.map (MulAut.conj (e : G)).toMonoidHom).subgroupOf d.E).map qbar
        = ((P0.subgroupOf d.E).map qbar).map (MulAut.conj (qbar e)).toMonoidHom
      exact quotient_conj_comm d.E P0 hP0leE e⟩
  have hphi_surj : Function.Surjective phi := by
    intro Y
    rcases Y.2 with ⟨gbar, hgbar⟩
    let e : d.E := Classical.choose (QuotientGroup.mk'_surjective (N := Subgroup.center d.E) gbar)
    have hq_e : qbar e = gbar :=
      Classical.choose_spec (QuotientGroup.mk'_surjective (N := Subgroup.center d.E) gbar)
    let R : Subgroup G := P0.map (MulAut.conj (e : G)).toMonoidHom
    have hR : ∃ e0 : d.E, R = P0.map (MulAut.conj (e0 : G)).toMonoidHom := ⟨e, rfl⟩
    refine ⟨⟨R, hR⟩, ?_⟩
    have hmapR : (R.subgroupOf d.E).map qbar = P0bar.map (MulAut.conj (qbar e)).toMonoidHom := by
      change ((P0.map (MulAut.conj (e : G)).toMonoidHom).subgroupOf d.E).map qbar
        = ((P0.subgroupOf d.E).map qbar).map (MulAut.conj (qbar e)).toMonoidHom
      exact quotient_conj_comm d.E P0 hP0leE e
    apply Subtype.ext
    apply Subgroup.ext
    intro z
    change z ∈ (R.subgroupOf d.E).map qbar ↔ z ∈ Y.1
    have hmapR' : (R.subgroupOf d.E).map qbar = P0bar.map (MulAut.conj gbar).toMonoidHom := by
      rwa [hq_e] at hmapR
    rw [hmapR', ← hgbar]
  -- |QOrbit| ≤ |EOrbit| via the surjection
  have hle : Nat.card QOrbit ≤ Nat.card EOrbit :=
    Nat.card_le_card_of_surjective phi hphi_surj
  calc
    q * k' = Nat.card QOrbit := hQOrbit.symm
    _ ≤ Nat.card EOrbit := hle
    _ = Nat.card {R : Subgroup G // ∃ e : d.E,
      R = P0.map (MulAut.conj (e : G)).toMonoidHom} := rfl

#print axioms secondCase_linearEquation11_orbit_card_of_unique_torus_family
#print axioms secondCase_linearEquation11_E_orbit_card_lower_of_component
