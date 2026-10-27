module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseQuotientReflectedTorus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the image of `U ∩ E` in `E / Z(E)` is cyclic and reflected

Source sentence (p. 224): "By the structure of A₇ and L₂(q), `U ∩ E / Z(E)`
is cyclic and is inverted by some involution `s ∈ S ∩ E`."

The reflected-quotient package
`secondCase_quotient_reflected_torus_data` already supplies a cyclic torus
`T ≤ E / Z(E)`, an involution `s ∈ S_E` whose image reflects `T`, and the
odd-centralizer containment for that torus.  It remains to observe that the
image of `U ∩ E` consists of odd-order elements (because `U = O(H)`) which
centralize the image of `t`, so the package's containment places `U ∩ E`
inside `T`; cyclicness and reflection then restrict to this image.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Every element of the odd core `O(H)` has odd order. -/
private theorem odd_order_of_mem_oddCoreOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : ∀ x : G, x ∈ oddCoreOf H → Odd (orderOf x) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
  have hdvd : orderOf y ∣ Nat.card (pPrimeCore 2 H) :=
    Subgroup.orderOf_dvd_natCard (pPrimeCore 2 H) hy
  have hoddcard : Odd (Nat.card (pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H))
  have hoddY : Odd (orderOf y) := Odd.of_dvd_nat hoddcard hdvd
  have hordEq : orderOf (H.subtype y) = orderOf y :=
    orderOf_injective H.subtype H.subtype_injective y
  rw [← hxy, hordEq]
  exact hoddY

/-- The image of an odd-order element under a homomorphism has odd order. -/
private theorem odd_order_of_map_of_odd_order
    {A : Type u} {B : Type u} [Group A] [Group B]
    (f : A →* B) {x : A} (hx : Odd (orderOf x)) :
    Odd (orderOf (f x)) :=
  Odd.of_dvd_nat hx (orderOf_map_dvd f x)

/-- The image of `U ∩ E` in `E / Z(E)` is cyclic and inverted by the
reflection `s` supplied by the common quotient package. -/
public theorem secondCase_U_inter_E_quotient_cyclic_inverted
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    ∃ SM : Sylow 2 (↥w.M),
      ((SM : Subgroup w.M).map w.M.subtype) ≤
        Subgroup.centralizer ({c.t} : Set G) ∧
      ∃ SE : Sylow 2 (↥d.E),
        (SE : Subgroup d.E).map d.E.subtype =
          ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E ∧
        ∃ T : Subgroup (d.E ⧸ Subgroup.center d.E),
          ∃ s : d.E,
            let q : d.E →* d.E ⧸ Subgroup.center d.E :=
              QuotientGroup.mk' (Subgroup.center d.E)
            let qt : d.E ⧸ Subgroup.center d.E := q ⟨c.t, d.t_mem_E⟩
            let UEbar : Subgroup (d.E ⧸ Subgroup.center d.E) :=
              ((c.U ⊓ d.E).subgroupOf d.E).map q
            s ∈ (SE : Subgroup d.E) ∧ IsInvolution s ∧
              IsCyclic T ∧ q s ∉ T ∧
              BenderGlauberman.IsInvertedBy (q s) T ∧
              (∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
                (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X →
                  Odd (orderOf x)) →
                  X ≤ Subgroup.centralizer
                    ({qt} : Set (d.E ⧸ Subgroup.center d.E)) →
                    X ≤ T) ∧
              UEbar ≤ T ∧
              IsCyclic UEbar ∧
              BenderGlauberman.IsInvertedBy (q s) UEbar := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb, T, s, hTcyc, hsSE, hsI, hq_s_not_T,
      hinvT, hcontainT⟩ :=
    secondCase_quotient_reflected_torus_data c w d
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let U0 : Subgroup d.E := (c.U ⊓ d.E).subgroupOf d.E
  let UEbar : Subgroup Q := U0.map q
  let tE : d.E := ⟨c.t, d.t_mem_E⟩
  have hU_le_centralizer : c.U ≤ Subgroup.centralizer ({c.t} : Set G) := by
    have hU_le_H : c.U ≤ c.H := by
      unfold CentralizerSetup.U
      unfold oddCoreOf
      exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
    rw [← c.H_eq_centralizer]
    exact hU_le_H
  have hU0odd : ∀ x : d.E, x ∈ U0 → Odd (orderOf x) := by
    intro x hx
    have hxU : (x : G) ∈ c.U := (Subgroup.mem_subgroupOf.mp hx).1
    have hordG : Odd (orderOf (x : G)) :=
      odd_order_of_mem_oddCoreOf c.H (x : G) hxU
    have hordEq : orderOf (x : G) = orderOf x :=
      orderOf_injective d.E.subtype d.E.subtype_injective x
    simpa [hordEq] using hordG
  have hUEbar_odd : ∀ y : Q, y ∈ UEbar → Odd (orderOf y) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxU0, rfl⟩
    exact odd_order_of_map_of_odd_order q (hU0odd x hxU0)
  have hUEbar_centralizer : UEbar ≤
      Subgroup.centralizer ({q tE} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hy with ⟨x, hxU0, rfl⟩
    have hxU : (x : G) ∈ c.U := (Subgroup.mem_subgroupOf.mp hxU0).1
    have hxcentG : (x : G) ∈ Subgroup.centralizer ({c.t} : Set G) :=
      hU_le_centralizer hxU
    have hcommG : (x : G) * c.t = c.t * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxcentG
    have hcommE : x * tE = tE * x := Subtype.ext hcommG
    calc
      q x * q tE = q (x * tE) := (map_mul q x tE).symm
      _ = q (tE * x) := by rw [hcommE]
      _ = q tE * q x := map_mul q tE x
  have hUEbar_le_T : UEbar ≤ T :=
    hcontainT UEbar hUEbar_odd hUEbar_centralizer
  let : IsCyclic T := hTcyc
  have hUEbar_cyclic : IsCyclic UEbar :=
    Subgroup.isCyclic_of_le hUEbar_le_T
  have hUEbar_inverted : BenderGlauberman.IsInvertedBy (q s) UEbar := by
    intro y hy
    exact hinvT y (hUEbar_le_T hy)
  have hT_inverted : BenderGlauberman.IsInvertedBy (q s) T := by
    intro y hy
    exact hinvT y hy
  refine ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc, hq_s_not_T,
    hT_inverted, hcontainT, hUEbar_le_T, hUEbar_cyclic, hUEbar_inverted⟩

end CFSG.GorensteinWalter
