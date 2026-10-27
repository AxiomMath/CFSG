module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenProductFamily
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (11): the quotient-lifted torus family

This module constructs the `Tori` input of the product-family count
(`secondCase_linearEquation11_product_family_conjugate_card`): an explicit
finite index type `B` of cardinal `q · k'` together with an injective
family `τ : B → secondCase_toriOf G P0 E` of internal `E`-conjugates of
the order-`p` subgroup `P0 ≤ K₀ ≤ E`.

## The construction

Let `Ē = E/Z(E)` and let `P̄₀` be the image of `P0` in `Ē`.  Since
`P0 ∩ Z(E) = 1`, the image keeps order `p`.  The torus-family orbit
theorem (`secondCase_linearEquation11_orbit_card_of_unique_torus_family`
applied in `Ē`) shows that the conjugacy orbit of `P̄₀` in `Ē` — the
type `B := secondCase_linearEquation11_quotientOrbit` — has cardinal
exactly `q · k'`.

The map `τ` (`secondCase_linearEquation11_quotientFamilyMap`) sends a
quotient conjugate `T = P̄₀^g` to the actual conjugate `P0^e` for a lift
`e ∈ E` of `g` (surjectivity of the quotient map `E → Ē`).  It is
injective: the composite with the quotient-image map
`R ↦ image of R in Ē` is the identity on the quotient orbit, so distinct
quotient images give distinct actual conjugates.  No centerless or
`p`-coprime-center hypothesis is needed.

The hypotheses are the same torus-family data on `Ē` (a cyclic torus
`U` of order `k`, normalizer of order `2k`, the restricted partition of
order-`p` elements, `p ∣ k`, and `|Ē| = 2 q k k'`) as
`secondCase_linearEquation11_E_orbit_card_lower_of_component`;
`P0 ∩ Z(E) = ⊥` and `P0 ≤ E` are explicit inputs.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## 0. Generic quotient helpers -/

/-- If `H ∩ N = ⊥` then the image of `H` in `G/N` has the same cardinal
as `H`. -/
public theorem subgroup_card_of_quotient_injective
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (H : Subgroup G) (hHZ : H ⊓ N = ⊥) :
    Nat.card (H.map (QuotientGroup.mk' N)) = Nat.card H := by
  classical
  let f : H → H.map (QuotientGroup.mk' N) := fun x =>
    ⟨(QuotientGroup.mk' N) (x : G), Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hq : (QuotientGroup.mk' N) (x : G) = (QuotientGroup.mk' N) (y : G) :=
      congrArg Subtype.val hxy
    have hdiv : (x : G) / (y : G) ∈ N := (QuotientGroup.eq_iff_div_mem (N := N)).mp hq
    have hxyH : (x : G) / (y : G) ∈ H := H.div_mem x.2 y.2
    have hboth : (x : G) / (y : G) ∈ H ⊓ N := ⟨hxyH, hdiv⟩
    have h1 : (x : G) / (y : G) = 1 := Subgroup.mem_bot.mp (by rwa [hHZ] at hboth)
    exact div_eq_one.mp h1
  have hsurj : Function.Surjective f := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

/-- Unfolding of the conjugation action. -/
private lemma conj_mul_eq {G : Type u} [Group G] (g x : G) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by
  rfl

/-- For `e ∈ E`, the quotient of the conjugate `H^e` agrees with the
conjugate of the quotient. -/
public theorem subgroup_quotient_conj_comm
    {G : Type u} [Group G] (E : Subgroup G) (H : Subgroup G)
    (hHle : H ≤ E) (e : E) :
    ((H.map (MulAut.conj (e : G)).toMonoidHom).subgroupOf E).map
        (QuotientGroup.mk' (Subgroup.center E)) =
      ((H.subgroupOf E).map (QuotientGroup.mk' (Subgroup.center E))).map
        (MulAut.conj (QuotientGroup.mk' (Subgroup.center E) e)).toMonoidHom := by
  let q : E →* E ⧸ Subgroup.center E := QuotientGroup.mk' (Subgroup.center E)
  apply Subgroup.ext
  intro z
  constructor
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, hwz⟩
    have hwG : (w : G) ∈ H.map (MulAut.conj (e : G)).toMonoidHom := Subgroup.mem_comap.mp hw
    rcases Subgroup.mem_map.mp hwG with ⟨x, hx, hxw⟩
    let xE : E := ⟨(x : G), hHle hx⟩
    refine Subgroup.mem_map.mpr ⟨q xE, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨xE, Subgroup.mem_comap.mpr hx, rfl⟩
    · calc
        (MulAut.conj (q e)).toMonoidHom (q xE)
            = q e * q xE * (q e)⁻¹ := by exact conj_mul_eq (q e) (q xE)
        _ = q (⟨(e : G) * (x : G) * (e : G)⁻¹,
              E.mul_mem (E.mul_mem e.2 (hHle hx)) (E.inv_mem e.2)⟩ : E) := by
              change q (e * xE * e⁻¹) = q e * q xE * (q e)⁻¹
              rw [map_mul, map_mul, map_inv]
        _ = q w := by
              congr 1
              simpa [Subtype.ext_iff, mul_assoc] using (conj_mul_eq (e : G) (x : G)).trans hxw
        _ = z := hwz
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, hyz⟩
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
    have hxG : (x : G) ∈ H := Subgroup.mem_comap.mp hx
    let exe : E := ⟨(e : G) * (x : G) * (e : G)⁻¹,
      E.mul_mem (E.mul_mem e.2 (hHle hxG)) (E.inv_mem e.2)⟩
    refine Subgroup.mem_map.mpr ⟨exe, ?_, ?_⟩
    · exact Subgroup.mem_comap.mpr
        (Subgroup.mem_map.mpr ⟨(x : G), hxG, by exact conj_mul_eq (e : G) (x : G)⟩)
    · calc
        q exe = q e * q ⟨(x : G), hHle hxG⟩ * (q e)⁻¹ := by
          change q (e * ⟨(x : G), hHle hxG⟩ * e⁻¹) = q e * q ⟨(x : G), hHle hxG⟩ * (q e)⁻¹
          rw [map_mul, map_mul, map_inv]
        _ = (MulAut.conj (q e)).toMonoidHom (q ⟨(x : G), hHle hxG⟩) := by
              exact (conj_mul_eq (q e) (q ⟨(x : G), hHle hxG⟩)).symm
        _ = (MulAut.conj (q e)).toMonoidHom y := by rw [hxy]
        _ = z := hyz

/-! ## 1. The quotient orbit and the lifting map -/

/-- The quotient orbit of the image `P̄₀` of `P0` in `Ē = E/Z(E)`; an
explicit finite index type of cardinal `q · k'`. -/
public def secondCase_linearEquation11_quotientOrbit
    {G : Type u} [Group G] {E : Subgroup G} (P0 : Subgroup G) : Type u :=
  secondCase_conjugatesOf (E ⧸ Subgroup.center E)
    ((P0.subgroupOf E).map (QuotientGroup.mk' (Subgroup.center E)))

/-- The lifting map: a quotient conjugate `T = P̄₀^g` is sent to the
actual conjugate `P0^e` for a lift `e ∈ E` of `g` (surjectivity of the
quotient map); distinct quotient conjugates give distinct actual
conjugates. -/
public noncomputable def secondCase_linearEquation11_quotientFamilyMap
    {G : Type u} [Group G] {E : Subgroup G} (P0 : Subgroup G) :
    secondCase_linearEquation11_quotientOrbit (G := G) (E := E) P0 →
    secondCase_toriOf G P0 E :=
  fun T =>
    let g : E ⧸ Subgroup.center E := Classical.choose T.2
    let e : E := Classical.choose (QuotientGroup.mk'_surjective (N := Subgroup.center E) g)
    ⟨P0.map (MulAut.conj (e : G)).toMonoidHom, ⟨e, rfl⟩⟩

/-- The lifting map is injective: the composite with the quotient-image
map is the identity on the quotient orbit. -/
public theorem secondCase_linearEquation11_quotientFamilyMap_injective
    {G : Type u} [Group G] [Finite G]
    {E : Subgroup G} (P0 : Subgroup G) (hP0leE : P0 ≤ E) :
    Function.Injective (secondCase_linearEquation11_quotientFamilyMap (G := G) (E := E) P0) := by
  classical
  let τ := secondCase_linearEquation11_quotientFamilyMap (G := G) (E := E) P0
  let Ebar : Type u := E ⧸ Subgroup.center E
  let qbar : E →* Ebar := QuotientGroup.mk' (Subgroup.center E)
  let P0bar : Subgroup Ebar := (P0.subgroupOf E).map qbar
  let img : secondCase_toriOf G P0 E → secondCase_conjugatesOf Ebar P0bar := fun R =>
    ⟨(R.1.subgroupOf E).map qbar, by
      rcases R.2 with ⟨e, he⟩
      refine ⟨qbar e, ?_⟩
      rw [he]
      rw [subgroup_quotient_conj_comm E P0 hP0leE e]⟩
  have hleft : Function.LeftInverse img τ := by
    intro T
    apply Subtype.ext
    dsimp [τ, img]
    let g : Ebar := Classical.choose T.2
    let e : E := Classical.choose (QuotientGroup.mk'_surjective (N := Subgroup.center E) g)
    have hq_e : qbar e = g :=
      Classical.choose_spec (QuotientGroup.mk'_surjective (N := Subgroup.center E) g)
    have hg : T.1 = P0bar.map (MulAut.conj g).toMonoidHom := Classical.choose_spec T.2
    calc
      ((P0.map (MulAut.conj (e : G)).toMonoidHom).subgroupOf E).map qbar
          = P0bar.map (MulAut.conj (qbar e)).toMonoidHom := by
              rw [subgroup_quotient_conj_comm E P0 hP0leE e]
      _ = P0bar.map (MulAut.conj g).toMonoidHom := by rw [hq_e]
      _ = T.1 := hg.symm
  exact hleft.injective

/-! ## 2. The cardinality and the packaged family -/

/-- The quotient orbit has cardinal exactly `q · k'`: `|P̄₀| = p` (from
`P0 ∩ Z(E) = ⊥`) and the torus-family orbit theorem on `Ē`. -/
public theorem secondCase_linearEquation11_quotientFamily_card
    {G : Type u} [Group G] [Finite G]
    {E : Subgroup G} {p q k k' : ℕ} [Fact p.Prime]
    (P0 : Subgroup G) (hP0leE : P0 ≤ E) (hP0card : Nat.card P0 = p)
    (hP0Z : P0 ⊓ (Subgroup.center E).map E.subtype = ⊥)
    (U : Subgroup (E ⧸ Subgroup.center E))
    (hcyc : IsCyclic U) (hUcard : Nat.card U = k)
    (hUN : Nat.card (Subgroup.normalizer (U : Set (E ⧸ Subgroup.center E))) = 2 * k)
    (hpart : ∀ x : E ⧸ Subgroup.center E, orderOf x = p →
      ∃! T : {T : Subgroup (E ⧸ Subgroup.center E) // ∃ g : E ⧸ Subgroup.center E,
        T = U.map (MulAut.conj g).toMonoidHom}, (x : E ⧸ Subgroup.center E) ∈ T.1)
    (hpk : p ∣ k)
    (hGcard : Nat.card (E ⧸ Subgroup.center E) = 2 * q * k * k') :
    Nat.card (secondCase_linearEquation11_quotientOrbit (G := G) (E := E) P0) = q * k' := by
  classical
  let Ebar : Type u := E ⧸ Subgroup.center E
  let qbar : E →* Ebar := QuotientGroup.mk' (Subgroup.center E)
  let P0bar : Subgroup Ebar := (P0.subgroupOf E).map qbar
  have hP0Z' : (P0.subgroupOf E) ⊓ (Subgroup.center E) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxP0 : (x : G) ∈ P0 := Subgroup.mem_subgroupOf.mp hx.1
    have hxC : (x : G) ∈ (Subgroup.center E).map E.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx.2, rfl⟩
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      have hmem : (x : G) ∈ P0 ⊓ (Subgroup.center E).map E.subtype :=
        Subgroup.mem_inf.mpr ⟨hxP0, hxC⟩
      simpa [hP0Z] using hmem
    have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp hxbot
    exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
  have hP0bar_card : Nat.card P0bar = p := by
    calc
      Nat.card P0bar = Nat.card (P0.subgroupOf E) :=
        subgroup_card_of_quotient_injective (N := Subgroup.center E)
          (H := P0.subgroupOf E) hP0Z'
      _ = Nat.card P0 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0leE).toEquiv
      _ = p := hP0card
  have hQOrbit : Nat.card (secondCase_conjugatesOf Ebar P0bar) = q * k' :=
    secondCase_linearEquation11_orbit_card_of_unique_torus_family
      (G := Ebar) (U := U) hcyc hUcard hUN hpart hpk hGcard P0bar hP0bar_card
  simpa [secondCase_linearEquation11_quotientOrbit, P0bar] using hQOrbit

/-- The quotient-lifted torus family: an explicit finite index type `B`
of cardinal `q · k'` together with an injective family
`τ : B → secondCase_toriOf G P0 E` obtained by lifting the distinct
quotient conjugates of `P̄₀` through the quotient map. -/
public theorem secondCase_linearEquation11_quotientFamily
    {G : Type u} [Group G] [Finite G]
    {E : Subgroup G} {p q k k' : ℕ} [Fact p.Prime]
    (P0 : Subgroup G) (hP0leE : P0 ≤ E) (hP0card : Nat.card P0 = p)
    (hP0Z : P0 ⊓ (Subgroup.center E).map E.subtype = ⊥)
    (U : Subgroup (E ⧸ Subgroup.center E))
    (hcyc : IsCyclic U) (hUcard : Nat.card U = k)
    (hUN : Nat.card (Subgroup.normalizer (U : Set (E ⧸ Subgroup.center E))) = 2 * k)
    (hpart : ∀ x : E ⧸ Subgroup.center E, orderOf x = p →
      ∃! T : {T : Subgroup (E ⧸ Subgroup.center E) // ∃ g : E ⧸ Subgroup.center E,
        T = U.map (MulAut.conj g).toMonoidHom}, (x : E ⧸ Subgroup.center E) ∈ T.1)
    (hpk : p ∣ k)
    (hGcard : Nat.card (E ⧸ Subgroup.center E) = 2 * q * k * k') :
    ∃ B : Type u, Nat.card B = q * k' ∧
      ∃ τ : B → secondCase_toriOf G P0 E, Function.Injective τ := by
  classical
  refine ⟨secondCase_linearEquation11_quotientOrbit (G := G) (E := E) P0,
    secondCase_linearEquation11_quotientFamily_card
      (G := G) (E := E) (p := p) (q := q) (k := k) (k' := k')
      P0 hP0leE hP0card hP0Z U hcyc hUcard hUN hpart hpk hGcard, ?_⟩
  refine ⟨secondCase_linearEquation11_quotientFamilyMap (G := G) (E := E) P0, ?_⟩
  exact secondCase_linearEquation11_quotientFamilyMap_injective (G := G) (E := E) P0 hP0leE

end CFSG.GorensteinWalter
