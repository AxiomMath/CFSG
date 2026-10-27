module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardThree
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The order-three image of the component intersection

In the `A₇` branch, the image of `U ∩ E` in `E / Z(E)` is the order-three
part of the centralizer of the distinguished involution.  This is the
nontriviality input for the inverted subgroup in Section 4.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the `A₇` component branch, `(U ∩ E)Z(E) / Z(E)` has order three. -/
public theorem secondCase_a7_U_inter_E_quotient_card_eq_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (_hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nat.card (((c.U ⊓ d.E).subgroupOf d.E).map
      (QuotientGroup.mk' (Subgroup.center d.E))) = 3 := by
  classical
  let E : Subgroup G := d.E
  let Z : Subgroup E := Subgroup.center E
  let : Z.Normal := by
    dsimp [Z]
    infer_instance
  let q : E →* E ⧸ Z := QuotientGroup.mk' Z
  let tE : E := ⟨c.t, d.t_mem_E⟩
  let T : Subgroup E := Subgroup.zpowers tE
  let C0 : Subgroup E := Subgroup.centralizer ({tE} : Set E)
  let UE : Subgroup E := (c.U ⊓ E).subgroupOf E
  let UEbar : Subgroup (E ⧸ Z) := UE.map q
  have htE : IsInvolution tE := by
    constructor
    · intro h
      exact c.t_involution.1 (by simpa [tE] using congrArg Subtype.val h)
    · exact Subtype.ext c.t_involution.2
  have hTcard : Nat.card T = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime htE.2 htE.1
  have hTp : IsPGroup 2 T := by
    apply IsPGroup.of_card (G := T) (n := 1)
    simp [hTcard]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 T) := ⟨hTp⟩
  have hZcop : Nat.Coprime 2 (Nat.card Z) :=
    Nat.coprime_two_left.mpr d.center_odd
  have hcentmap :
      Subgroup.centralizer ((T.map q : Subgroup (E ⧸ Z)) : Set (E ⧸ Z)) =
        C0.map q := by
    have h := centralizer_map_quotient_eq_map_centralizer
      (G := E) (p := 2) T Z (by infer_instance) hZcop
    have hTsingle : Subgroup.centralizer (T : Set E) = C0 := by
      dsimp [T, C0]
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    simpa [hTsingle, q] using h
  have hqT : T.map q = Subgroup.zpowers (q tE) := by
    simp [T]
  have hTqsingle : Subgroup.centralizer
      ((T.map q : Subgroup (E ⧸ Z)) : Set (E ⧸ Z)) =
      Subgroup.centralizer ({q tE} : Set (E ⧸ Z)) := by
    rw [hqT, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hqt : IsInvolution (q tE) := by
    constructor
    · intro hq1
      have htZ : tE ∈ Z := (QuotientGroup.eq_one_iff (N := Z) tE).mp hq1
      have h2dvd : 2 ∣ Nat.card Z := by
        rw [← orderOf_eq_prime htE.2 htE.1]
        exact Subgroup.orderOf_dvd_natCard Z htZ
      exact d.center_odd.not_two_dvd_nat h2dvd
    · simpa [map_pow] using congrArg q htE.2
  let eQ : (E ⧸ Z) ≃* alternatingGroup (Fin 7) := hA7.some
  let qt7 : alternatingGroup (Fin 7) := eQ (q tE)
  have hqt7 : IsInvolution qt7 := by
    constructor
    · intro h
      apply hqt.1
      apply eQ.injective
      simpa [qt7] using h
    · simpa [qt7, map_pow] using congrArg eQ hqt.2
  obtain ⟨g, hgt⟩ := aSeven_involutions_conjugate qt7 a7t
    (by simpa using hqt7) (by constructor <;> decide)
  let b7 : alternatingGroup (Fin 7) := g⁻¹ * a7a * g
  have hb7pow : b7 ^ 3 = 1 := by
    dsimp [b7]
    have ha : a7a ^ 3 = (1 : alternatingGroup (Fin 7)) := by decide
    calc
      (g⁻¹ * a7a * g) ^ 3 =
          (g⁻¹ * a7a * g) * (g⁻¹ * a7a * g) * (g⁻¹ * a7a * g) := by
        change (g⁻¹ * a7a * g) * (g⁻¹ * a7a * g) *
          (g⁻¹ * a7a * g) = _
        rfl
      _ = g⁻¹ * a7a ^ 3 * g := by
        rw [show a7a ^ 3 = a7a * a7a * a7a by rw [pow_succ, pow_two]]
        group
      _ = 1 := by rw [ha]; simp
  have hb7ne : b7 ≠ 1 := by
    intro hb
    have ha_ne : a7a ≠ (1 : alternatingGroup (Fin 7)) := by decide
    apply ha_ne
    calc
      a7a = g * (g⁻¹ * a7a * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by change g * b7 * g⁻¹ = _; rw [hb]
      _ = 1 := by simp
  have hb7cent : b7 ∈
      Subgroup.centralizer ({qt7} : Set (alternatingGroup (Fin 7))) := by
    have ha_cent : a7a * a7t = a7t * a7a := by decide
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      b7 * qt7 = (g⁻¹ * a7a * g) * qt7 := rfl
      _ = g⁻¹ * a7a * (g * qt7) := by group
      _ = g⁻¹ * a7a * (a7t * g) := by rw [← hgt]; group
      _ = g⁻¹ * (a7a * a7t) * g := by group
      _ = g⁻¹ * (a7t * a7a) * g := by rw [ha_cent]
      _ = (g⁻¹ * a7t * g) * (g⁻¹ * a7a * g) := by group
      _ = qt7 * b7 := by
        have hgt' : g⁻¹ * a7t * g = qt7 := by rw [← hgt]; group
        rw [hgt']
  let bQ : E ⧸ Z := eQ.symm b7
  have hbQpow : bQ ^ 3 = 1 := by
    apply eQ.injective
    simpa [bQ, map_pow] using hb7pow
  have hbQne : bQ ≠ 1 := by
    intro h
    apply hb7ne
    simpa [bQ] using congrArg eQ h
  have hbQcent : bQ ∈
      Subgroup.centralizer ({q tE} : Set (E ⧸ Z)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply eQ.injective
    simpa [bQ, qt7] using
      (Subgroup.mem_centralizer_singleton_iff.mp hb7cent)
  have hbQmap : bQ ∈ C0.map q := by
    rw [← hcentmap, hTqsingle]
    exact hbQcent
  rcases Subgroup.mem_map.mp hbQmap with ⟨x, hxC0, hqx⟩
  have hxpowZ : x ^ 3 ∈ Z := by
    have hqpow : q (x ^ 3) = 1 := by rw [map_pow, hqx, hbQpow]
    apply (QuotientGroup.eq_one_iff (N := Z) (x ^ 3)).mp
    simpa [q] using hqpow
  have hxpow_order_dvd : orderOf (x ^ 3) ∣ Nat.card Z :=
    Subgroup.orderOf_dvd_natCard Z hxpowZ
  have hxpow_card : (x ^ 3) ^ Nat.card Z = 1 :=
    (orderOf_dvd_iff_pow_eq_one (x := x ^ 3) (n := Nat.card Z)).mp
      hxpow_order_dvd
  have hx_exp : x ^ (3 * Nat.card Z) = 1 := by
    rw [pow_mul]
    exact hxpow_card
  have hx_order_dvd : orderOf x ∣ 3 * Nat.card Z :=
    (orderOf_dvd_iff_pow_eq_one (x := x) (n := 3 * Nat.card Z)).mpr hx_exp
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (Odd.mul (by decide) d.center_odd) hx_order_dvd
  let P : Subgroup E := Subgroup.zpowers x
  have hPleC0 : P ≤ C0 := Subgroup.zpowers_le.mpr hxC0
  have hC0mapH : C0.map E.subtype ≤ c.H := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, rfl⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hy0
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    simpa [tE] using congrArg Subtype.val hcomm
  have hPmapH : P.map E.subtype ≤ c.H :=
    (Subgroup.map_mono hPleC0).trans hC0mapH
  have hPodd : Odd (Nat.card (P.map E.subtype)) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, Nat.card_zpowers]
    exact hxodd
  have hPmapU : P.map E.subtype ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hPmapH
      (Nat.coprime_two_left.mpr hPodd)
  have hxPmap : (x : G) ∈ P.map E.subtype :=
    Subgroup.mem_map.mpr ⟨x, Subgroup.mem_zpowers x, rfl⟩
  have hxU : (x : G) ∈ c.U := hPmapU hxPmap
  have hxUE : x ∈ UE := Subgroup.mem_subgroupOf.mpr ⟨hxU, x.2⟩
  have hbQmem : bQ ∈ UEbar := by
    exact Subgroup.mem_map.mpr ⟨x, hxUE, hqx⟩
  have hUEbar_ne : UEbar ≠ ⊥ := by
    intro hbot
    have hb1 : bQ = 1 := by
      apply Subgroup.mem_bot.mp
      simpa [hbot] using hbQmem
    exact hbQne hb1
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hUEcard : Nat.card UE = Nat.card (↥(c.U ⊓ E)) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := c.U ⊓ E) (K := E) inf_le_right).toEquiv
  have hUEodd : Odd (Nat.card UE) := by
    rw [hUEcard]
    exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hUEbarodd : Odd (Nat.card UEbar) :=
    Odd.of_dvd_nat hUEodd (Subgroup.card_map_dvd UE q)
  have hUleH : c.U ≤ c.H :=
    Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hUEbarcent : UEbar ≤
      Subgroup.centralizer ({q tE} : Set (E ⧸ Z)) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, rfl⟩
    have hyU : (y0 : G) ∈ c.U := (Subgroup.mem_subgroupOf.mp hy0).1
    have hyH : (y0 : G) ∈ c.H := hUleH hyU
    rw [c.H_eq_centralizer] at hyH
    have hycomm : y0 * tE = tE * y0 := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hyH
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa using congrArg q hycomm
  let UE7 : Subgroup (alternatingGroup (Fin 7)) := UEbar.map eQ.toMonoidHom
  have hUE7odd : Odd (Nat.card UE7) := by
    rw [Subgroup.card_map_of_injective eQ.injective]
    exact hUEbarodd
  have hUE7cent : UE7 ≤
      Subgroup.centralizer ({qt7} : Set (alternatingGroup (Fin 7))) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, rfl⟩
    have hycomm := Subgroup.mem_centralizer_singleton_iff.mp (hUEbarcent hy0)
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa [qt7] using congrArg eQ hycomm
  have hle7 : Nat.card UE7 ≤ 3 :=
    aSeven_odd_subgroup_centralizing_involution_card_le_three
      hUE7odd hqt7 hUE7cent
  have hcardUE7 : Nat.card UE7 = Nat.card UEbar :=
    Subgroup.card_map_of_injective eQ.injective
  have hle : Nat.card UEbar ≤ 3 := by rw [← hcardUE7]; exact hle7
  have hpos : 0 < Nat.card UEbar := Nat.card_pos
  have hne_one : Nat.card UEbar ≠ 1 := by
    intro h1
    apply hUEbar_ne
    exact (Subgroup.eq_bot_iff_card (H := UEbar)).mpr h1
  rcases hUEbarodd with ⟨k, hk⟩
  change Nat.card UEbar = 3
  omega

end CFSG.GorensteinWalter
