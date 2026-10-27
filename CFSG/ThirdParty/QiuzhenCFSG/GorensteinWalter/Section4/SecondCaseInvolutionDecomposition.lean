module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseUEQuotientReflected
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: equations (1)--(2), involution half

The upstream quotient theorem
`secondCase_U_inter_E_quotient_cyclic_inverted` supplies a coherent pair of
Sylow subgroups and an involution `s` whose image inverts the cyclic image of
`U ∩ E`.  This module lifts that information to the ambient odd subgroup
`X = U ∩ M`: the inverted elements of `X` form a cyclic subgroup `K`, the
centralizer `B = C_X(s)` completes the join `X = K ⊔ B`, and the ambient and
component Sylow data from the upstream theorem are preserved.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- `U = O(H)` is normal in `H = C_G(t)`. -/
private theorem centralizerSetup_U_isNormalIn_H
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : IsNormalIn c.U c.H := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹ ∈
        pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        p hp (⟨h, hh⟩ : ↥c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹, hconj, by simp⟩

/-- Every element of the odd core `U = O(H)` has odd order. -/
private theorem odd_order_of_mem_U
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : ∀ x : G, x ∈ c.U → Odd (orderOf x) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
  have hdvd : orderOf y ∣ Nat.card (pPrimeCore 2 c.H) :=
    Subgroup.orderOf_dvd_natCard (pPrimeCore 2 c.H) hy
  have hoddcard : Odd (Nat.card (pPrimeCore 2 c.H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := c.H))
  have hoddY : Odd (orderOf y) := Odd.of_dvd_nat hoddcard hdvd
  have hordEq : orderOf (c.H.subtype y) = orderOf y :=
    orderOf_injective c.H.subtype c.H.subtype_injective y
  rw [← hxy, hordEq]
  exact hoddY

/-- An element of `U ∩ M` inverted by `s` lies in the component `E`: modulo
`E`, conjugation by `s` is trivial while inversion gives an element of order
two, and oddness of `U` forces that quotient image to be trivial. -/
private theorem mem_E_of_inverted
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SM : Sylow 2 (↥w.M))
    (hSMcent : ((SM : Subgroup w.M).map w.M.subtype) ≤
      Subgroup.centralizer ({c.t} : Set G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    {s : d.E} (hsSE : s ∈ (SE : Subgroup d.E))
    {y : G} (hyU : y ∈ c.U) (hyM : y ∈ w.M)
    (hyinv : (s : G) * y * (s : G)⁻¹ = y⁻¹) :
    y ∈ d.E := by
  classical
  let sG : G := s
  have hsmap : sG ∈ (SE : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hsSM : sG ∈ ((SM : Subgroup w.M).map w.M.subtype) := by
    rw [hSEamb] at hsmap
    exact hsmap.1
  have hsM : sG ∈ w.M := (Subgroup.map_subtype_le (SM : Subgroup w.M)) hsSM
  have hsH : sG ∈ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent hsSM
  let Esub : Subgroup (↥w.M) := d.E.subgroupOf w.M
  have hEsubNormal : Esub.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := w.M) (N := d.E)
      (le_normalizer_of_isNormalIn d.E_normal)
  let : Esub.Normal := hEsubNormal
  let p : w.M →* w.M ⧸ Esub := QuotientGroup.mk' Esub
  let yM : w.M := ⟨y, hyM⟩
  let sM : w.M := ⟨sG, hsM⟩
  have hconjM : sM * yM * sM⁻¹ = yM⁻¹ := by
    apply Subtype.ext
    change sG * y * sG⁻¹ = y⁻¹
    exact hyinv
  have hsq : (p yM) ^ 2 = 1 := by
    have hp1 : p (sM * yM * sM⁻¹) = p yM := by
      calc
        p (sM * yM * sM⁻¹) = p sM * p yM * (p sM)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        _ = 1 * p yM * 1 := by
          have hs1 : p sM = 1 := by
            apply (QuotientGroup.eq_one_iff (N := Esub) sM).mpr
            exact Subgroup.mem_subgroupOf.mpr (s : d.E).2
          rw [hs1, one_mul, inv_one, mul_one]
        _ = p yM := by simp
    have hp2 : p (sM * yM * sM⁻¹) = (p yM)⁻¹ := by
      simpa using congrArg p hconjM
    have h : p yM = (p yM)⁻¹ := hp1.symm.trans hp2
    rw [pow_two]
    calc
      p yM * p yM = (p yM)⁻¹ * p yM := congrArg (fun z => z * p yM) h
      _ = 1 := by simp
  have hordY : Odd (orderOf y) := odd_order_of_mem_U c y hyU
  have hordYdiv : orderOf (p yM) ∣ orderOf y := by
    have h1 : orderOf (p yM) ∣ orderOf yM := orderOf_map_dvd p yM
    have h2 : orderOf yM = orderOf y :=
      (orderOf_injective w.M.subtype w.M.subtype_injective yM).symm
    rwa [h2] at h1
  have hordOdd : Odd (orderOf (p yM)) := Odd.of_dvd_nat hordY hordYdiv
  have hp1' : p yM = 1 := by
    have hdvd2 : orderOf (p yM) ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := p yM) (n := 2)).2 hsq
    have hcop : Nat.Coprime 2 (orderOf y) := Nat.coprime_two_left.mpr hordY
    have hdvd1 : orderOf (p yM) ∣ 1 := by
      simpa [hcop.gcd_eq_one] using (Nat.dvd_gcd hdvd2 hordYdiv)
    exact (orderOf_eq_one_iff (x := p yM)).1 (Nat.dvd_one.mp hdvd1)
  have hyEsub : yM ∈ Esub :=
    (QuotientGroup.eq_one_iff (N := Esub) yM).mp hp1'
  exact (Subgroup.mem_subgroupOf.mp hyEsub)

/-- Powers of an element inverted by `s` are inverted by `s`. -/
private theorem zpow_inverted_of_generator_inverted
    {G : Type u} [Group G] {s z : G} (h : s * z * s⁻¹ = z⁻¹) (k : ℤ) :
    s * z ^ k * s⁻¹ = (z ^ k)⁻¹ := by
  calc
    s * z ^ k * s⁻¹ = (MulAut.conj s) (z ^ k) := (MulAut.conj_apply s (z ^ k)).symm
    _ = ((MulAut.conj s) z) ^ k := by rw [map_zpow]
    _ = (z⁻¹) ^ k := by rw [MulAut.conj_apply, h]
    _ = (z ^ k)⁻¹ := by
      rw [← zpow_neg]
      simp

/-- Section 4, equations (1)--(2) (involution half): the inverted elements
of `X = U ∩ M` form a cyclic subgroup `K`, and `X = K ⊔ C_X(s)`. -/
public theorem secondCase_involution_decomposition
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
              BenderGlauberman.IsInvertedBy (q s) UEbar ∧
              ∃ K B : Subgroup G,
                (K : Set G) =
                  invertedElements (c.U ⊓ w.M) (s : G) ∧
                IsCyclic K ∧
                B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
                K ⊔ B = c.U ⊓ w.M := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc, hq_s_not_T,
      hinvT, hcontainT, hUEbar_le_T, hcyclic, hinv⟩ :=
    secondCase_U_inter_E_quotient_cyclic_inverted c w d
  let sG : G := s
  let X : Subgroup G := c.U ⊓ w.M
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let XE : Subgroup d.E := (c.U ⊓ d.E).subgroupOf d.E
  let Xbar : Subgroup Q := XE.map q
  have hcycXbar : IsCyclic Xbar := by
    change IsCyclic (XE.map (QuotientGroup.mk' (Subgroup.center d.E)))
    exact hcyclic
  have hinvXbar : ∀ z : Q, z ∈ Xbar → q s * z * (q s)⁻¹ = z⁻¹ := by
    intro z hz
    change (QuotientGroup.mk' (Subgroup.center d.E)) s * z *
        ((QuotientGroup.mk' (Subgroup.center d.E)) s)⁻¹ = z⁻¹
    exact hinv z hz
  -- ambient membership of `s`
  have hsmap : sG ∈ (SE : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hsSM : sG ∈ ((SM : Subgroup w.M).map w.M.subtype) := by
    rw [hSEamb] at hsmap
    exact hsmap.1
  have hsM : sG ∈ w.M := (Subgroup.map_subtype_le (SM : Subgroup w.M)) hsSM
  have hsH : sG ∈ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent hsSM
  have hsIG : IsInvolution sG := by
    constructor
    · intro h1
      apply hsI.1
      apply Subtype.ext
      exact h1
    · simpa [sG, pow_two] using congrArg Subtype.val hsI.2
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hcopX : Nat.Coprime 2 (Nat.card (↥X)) := by
    have hoddX : Odd (Nat.card (↥X)) :=
      Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
    exact Nat.coprime_two_left.mpr hoddX
  have hsX : ∀ x : G, x ∈ X → sG * x * sG⁻¹ ∈ X := by
    intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨(centralizerSetup_U_isNormalIn_H c).2 sG hsH x hx.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)
  -- cyclic generator of the quotient image and a lift
  let : IsCyclic Xbar := hcycXbar
  obtain ⟨xbar, hxbar_gen⟩ := IsCyclic.exists_generator (α := Xbar)
  have hxbar_mem : (xbar : Q) ∈ Xbar := xbar.2
  rcases Subgroup.mem_map.mp hxbar_mem with ⟨xE, hxE, hxq⟩
  have hxU : (xE : G) ∈ c.U := (Subgroup.mem_subgroupOf.mp hxE).1
  -- the commutator `z` lies in `U ∩ Z(E)`
  let zE : d.E := s * xE * s⁻¹ * xE
  have hq_s_x_inv : q (s * xE * s⁻¹) = (q xE)⁻¹ := by
    calc
      q (s * xE * s⁻¹) = q s * q xE * (q s)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      _ = q s * (xbar : Q) * (q s)⁻¹ := by rw [hxq]
      _ = (xbar : Q)⁻¹ := hinvXbar (xbar : Q) hxbar_mem
      _ = (q xE)⁻¹ := by rw [← hxq]
  have hqz : q zE = 1 := by
    calc
      q zE = q (s * xE * s⁻¹ * xE) := rfl
      _ = q (s * xE * s⁻¹) * q xE := by rw [map_mul]
      _ = (q xE)⁻¹ * q xE := by rw [hq_s_x_inv]
      _ = 1 := by simp
  have hzcenter : zE ∈ Subgroup.center d.E :=
    (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) zE).mp hqz
  have hzU : (zE : G) ∈ c.U := by
    change sG * (xE : G) * sG⁻¹ * (xE : G) ∈ c.U
    exact c.U.mul_mem
      ((centralizerSetup_U_isNormalIn_H c).2 sG hsH (xE : G) hxU) hxU
  -- choose the odd square root of `z⁻¹` inside `U ∩ Z(E)`
  let ZU : Subgroup d.E := c.U.subgroupOf d.E ⊓ Subgroup.center d.E
  have hZUodd : Odd (Nat.card ZU) := by
    have hdvd : Nat.card ZU ∣ Nat.card (c.U.subgroupOf d.E) :=
      Subgroup.card_dvd_of_le inf_le_left
    have hoddUsub : Odd (Nat.card (c.U.subgroupOf d.E)) := by
      have hsub_eq : (c.U ⊓ d.E).subgroupOf d.E = c.U.subgroupOf d.E := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      have hcard : Nat.card (c.U.subgroupOf d.E) =
          Nat.card (c.U ⊓ d.E : Subgroup G) := by
        rw [← hsub_eq]
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := c.U ⊓ d.E) (K := d.E)
            inf_le_right).toEquiv
      have hdvdU : Nat.card (c.U ⊓ d.E : Subgroup G) ∣ Nat.card c.U :=
        Subgroup.card_dvd_of_le inf_le_left
      rw [hcard]
      exact Odd.of_dvd_nat hUodd hdvdU
    exact Odd.of_dvd_nat hoddUsub hdvd
  have hcopZU : Nat.Coprime 2 (Nat.card ZU) := Nat.coprime_two_left.mpr hZUodd
  let zZU : ZU := ⟨zE, Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_subgroupOf.mpr hzU, hzcenter⟩⟩
  let cZU : ZU := Classical.choose
    ((sq_bijective_of_coprime_two (G := ZU) hcopZU).2 zZU⁻¹)
  have hc_sq : cZU ^ 2 = zZU⁻¹ :=
    Classical.choose_spec
      ((sq_bijective_of_coprime_two (G := ZU) hcopZU).2 zZU⁻¹)
  let cE : d.E := cZU
  let cG : G := cE
  let kE : d.E := xE * cE
  let kG : G := kE
  have hcU : (cE : G) ∈ c.U := Subgroup.mem_subgroupOf.mp cZU.2.1
  have hcCenter : cE ∈ Subgroup.center d.E := cZU.2.2
  have hkU : kG ∈ c.U := c.U.mul_mem hxU hcU
  have hkM : kG ∈ w.M := d.E_component.1 (kE : d.E).2
  have hkX : kG ∈ X := Subgroup.mem_inf.mpr ⟨hkU, hkM⟩
  have hq_c : q cE = 1 :=
    (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) cE).mpr hcCenter
  have hqk : q kE = q xE := by
    calc
      q kE = q (xE * cE) := rfl
      _ = q xE * q cE := map_mul q xE cE
      _ = q xE * 1 := by rw [hq_c]
      _ = q xE := by simp
  have hqk_bar : q kE = (xbar : Q) := hqk.trans hxq
  -- the chosen lift `k` is inverted by `s`
  have hc_sqE : cE ^ 2 = zE⁻¹ :=
    congrArg (fun z : ZU => (z : d.E)) hc_sq
  have hc_sqG : cG ^ 2 = (zE : G)⁻¹ := by
    have h' : (cE : d.E) ^ 2 = (zE : d.E)⁻¹ := hc_sqE
    simpa [cG] using congrArg (fun z : d.E => (z : G)) h'
  have hz_c_inv : (zE : G) * cG = cG⁻¹ := by
    have h1 : (zE : G) * cG ^ 2 = 1 := by
      rw [hc_sqG]
      simp
    calc
      (zE : G) * cG = (zE : G) * (cG * cG) * cG⁻¹ := by group
      _ = (zE : G) * (cG ^ 2) * cG⁻¹ := by rw [← pow_two]
      _ = 1 * cG⁻¹ := by rw [h1]
      _ = cG⁻¹ := by simp
  have hcs : sG * cG = cG * sG := by
    have h := (Subgroup.mem_center_iff.mp hcCenter s)
    simpa [sG, cG] using congrArg Subtype.val h
  have hsx : sG * (xE : G) * sG⁻¹ = (zE : G) * (xE : G)⁻¹ := by
    have hz_def : (zE : G) = sG * (xE : G) * sG⁻¹ * (xE : G) := rfl
    calc
      sG * (xE : G) * sG⁻¹ =
          (sG * (xE : G) * sG⁻¹ * (xE : G)) * (xE : G)⁻¹ := by group
      _ = (zE : G) * (xE : G)⁻¹ := by rw [hz_def]
  have hcx : (xE : G) * cG = cG * (xE : G) := by
    have h := (Subgroup.mem_center_iff.mp hcCenter xE)
    simpa [cG] using congrArg Subtype.val h
  have hkinvG : sG * kG * sG⁻¹ = kG⁻¹ := by
    calc
      sG * kG * sG⁻¹ = sG * ((xE : G) * cG) * sG⁻¹ := by
        simp [kG, kE, cG]
      _ = (sG * (xE : G) * sG⁻¹) * (sG * cG * sG⁻¹) := by group
      _ = (sG * (xE : G) * sG⁻¹) * cG := by
        have hscc : sG * cG * sG⁻¹ = cG := by
          calc
            sG * cG * sG⁻¹ = (cG * sG) * sG⁻¹ := by rw [hcs]
            _ = cG := by simp
        rw [hscc]
      _ = ((zE : G) * (xE : G)⁻¹) * cG := by rw [hsx]
      _ = (zE : G) * ((xE : G)⁻¹ * cG) := by group
      _ = (zE : G) * (cG * (xE : G)⁻¹) := by
        have hxcinv : (xE : G)⁻¹ * cG = cG * (xE : G)⁻¹ := by
          calc
            (xE : G)⁻¹ * cG = (xE : G)⁻¹ * (cG * (xE : G)) * (xE : G)⁻¹ := by group
            _ = (xE : G)⁻¹ * ((xE : G) * cG) * (xE : G)⁻¹ := by rw [hcx]
            _ = cG * (xE : G)⁻¹ := by group
        rw [hxcinv]
      _ = ((zE : G) * cG) * (xE : G)⁻¹ := by group
      _ = cG⁻¹ * (xE : G)⁻¹ := by rw [hz_c_inv]
      _ = ((xE : G) * cG)⁻¹ := by group
      _ = kG⁻¹ := by simp [kG, kE, cG]
  -- the inverted set is exactly `K = ⟨k⟩`
  let K : Subgroup G := Subgroup.zpowers kG
  let B : Subgroup G := centralizerIn X sG
  have hK_le_X : K ≤ X := Subgroup.zpowers_le.mpr hkX
  have hK_eq : (K : Set G) = invertedElements X sG := by
    ext y
    constructor
    · intro hyK
      rw [invertedElements]
      exact ⟨hK_le_X hyK, by
        rcases Subgroup.mem_zpowers_iff.mp hyK with ⟨n, hn⟩
        subst y
        exact zpow_inverted_of_generator_inverted hkinvG n⟩
    · rintro ⟨hyX, hys⟩
      have hyU : y ∈ c.U := hyX.1
      have hyM : y ∈ w.M := hyX.2
      have hyE : y ∈ d.E :=
        mem_E_of_inverted c w d SM hSMcent SE hSEamb hsSE hyU hyM hys
      let yE : d.E := ⟨y, hyE⟩
      have hyE_mem_XE : yE ∈ XE :=
        Subgroup.mem_subgroupOf.mpr ⟨hyU, hyE⟩
      have hqy_mem : q yE ∈ Xbar :=
        Subgroup.mem_map.mpr ⟨yE, hyE_mem_XE, rfl⟩
      let ybar : Xbar := ⟨q yE, hqy_mem⟩
      have hybar_gen := hxbar_gen ybar
      rcases Subgroup.mem_zpowers_iff.mp hybar_gen with ⟨n, hn⟩
      have hqy_pow : (xbar : Q) ^ n = q yE :=
        congrArg (fun z : Xbar => (z : Q)) hn
      have hqk_pow : q (kE ^ n) = q yE := by
        calc
          q (kE ^ n) = (q kE) ^ n := map_zpow q kE n
          _ = (xbar : Q) ^ n := by rw [hqk_bar]
          _ = q yE := hqy_pow
      let rE : d.E := yE * (kE ^ n)⁻¹
      have hq_r : q rE = 1 := by
        calc
          q rE = q (yE * (kE ^ n)⁻¹) := rfl
          _ = q yE * q ((kE ^ n)⁻¹) := map_mul q yE ((kE ^ n)⁻¹)
          _ = q yE * (q (kE ^ n))⁻¹ := by rw [map_inv]
          _ = q yE * (q yE)⁻¹ := by rw [hqk_pow]
          _ = 1 := by simp
      have hrcenter : rE ∈ Subgroup.center d.E :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) rE).mp hq_r
      let rG : G := rE
      have hr_def : rG = y * kG ^ (-n) := by
        calc
          rG = (yE : G) * ((kE ^ n)⁻¹ : d.E) := rfl
          _ = y * (kG ^ n)⁻¹ := by simp [kG, kE, yE]
          _ = y * kG ^ (-n) := by rw [zpow_neg]
      have hrU : rG ∈ c.U := by
        rw [hr_def]
        exact c.U.mul_mem hyU (c.U.zpow_mem hkU (-n))
      have hs_fix : sG * rG * sG⁻¹ = rG := by
        have hcomm : sG * rG = rG * sG :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hrcenter s)
        calc
          sG * rG * sG⁻¹ = (rG * sG) * sG⁻¹ := by rw [hcomm]
          _ = rG := by simp
      have hr_comm_y : y * rG = rG * y :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hrcenter yE)
      have hcomm_k_y : y * kG ^ (-n) = kG ^ (-n) * y := by
        have h' : y * (y * kG ^ (-n)) = (y * kG ^ (-n)) * y := by
          simpa [hr_def] using hr_comm_y
        calc
          y * kG ^ (-n) = y * y⁻¹ * (y * kG ^ (-n)) := by group
          _ = y⁻¹ * (y * (y * kG ^ (-n))) := by group
          _ = y⁻¹ * ((y * kG ^ (-n)) * y) := by rw [h']
          _ = kG ^ (-n) * y := by group
      have hk_neg_inv : sG * kG ^ (-n) * sG⁻¹ = (kG ^ (-n))⁻¹ :=
        zpow_inverted_of_generator_inverted hkinvG (-n)
      have hs_inv : sG * rG * sG⁻¹ = rG⁻¹ := by
        rw [hr_def]
        calc
          sG * (y * kG ^ (-n)) * sG⁻¹ =
              (sG * y * sG⁻¹) * (sG * kG ^ (-n) * sG⁻¹) := by group
          _ = y⁻¹ * (kG ^ (-n))⁻¹ := by rw [hys, hk_neg_inv]
          _ = (kG ^ (-n) * y)⁻¹ := by group
          _ = (y * kG ^ (-n))⁻¹ := by rw [hcomm_k_y]
      have hsq_r : rG ^ 2 = 1 := by
        have h : rG = rG⁻¹ := hs_fix.symm.trans hs_inv
        rw [pow_two]
        calc
          rG * rG = rG⁻¹ * rG := congrArg (fun z => z * rG) h
          _ = 1 := by simp
      have hrG_one : rG = 1 := by
        let rC : Subgroup.center d.E := ⟨rE, hrcenter⟩
        have hsq_rC : rC ^ 2 = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          simpa [rG, pow_two] using hsq_r
        have hrC_one : rC = 1 :=
          eq_one_of_sq_eq_one_of_coprime_two (G := Subgroup.center d.E)
            (Nat.coprime_two_left.mpr d.center_odd) hsq_rC
        simpa [rG, rC] using congrArg Subtype.val hrC_one
      have h1 : y * kG ^ (-n) = 1 := by
        simpa [hr_def] using hrG_one
      have hy_eq : y = kG ^ n := by
        calc
          y = (y * kG ^ (-n)) * kG ^ n := by group
          _ = 1 * kG ^ n := by rw [h1]
          _ = kG ^ n := by simp
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, hy_eq.symm⟩
  have hK_cyc : IsCyclic K := by
    dsimp [K]
    infer_instance
  -- join `X = K ⊔ B` via Fact 1.5(ii) and normality of `K` in `X`
  have hKnormal : IsNormalIn K X :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal (X := X) (s := sG)
      hsIG hcopX hsX (I := K) hK_eq).2.1
  have hB_le_X : B ≤ X := by
    intro x hx
    exact hx.1
  have hB_le_NK : B ≤ Subgroup.normalizer (K : Set G) := by
    intro b hbB
    exact le_normalizer_of_isNormalIn hKnormal (hB_le_X hbB)
  have hcarrier : (↑(K ⊔ B) : Set G) = (K : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K B hB_le_NK
  have hBK_eq : (B : Set G) * (K : Set G) = (K : Set G) * (B : Set G) :=
    Subgroup.set_mul_normalizer_comm (S := (B : Set G)) (N := K) hB_le_NK
  have hjoin : K ⊔ B = X := by
    apply le_antisymm
    · exact sup_le hK_le_X hB_le_X
    · intro x hx
      rcases fact_1_5_ii_decomposition (X := X) (s := sG) hsIG hcopX hsX x hx
        with ⟨c, hcB, i, hiI, hxi⟩
      have hiK : i ∈ K := by
        have : i ∈ invertedElements X sG := hiI
        rwa [← hK_eq] at this
      have hx_BK : x ∈ (B : Set G) * (K : Set G) :=
        ⟨c, hcB, i, hiK, hxi.symm⟩
      have hx_KB : x ∈ (K : Set G) * (B : Set G) := by
        rw [hBK_eq] at hx_BK
        exact hx_BK
      change x ∈ (↑(K ⊔ B) : Set G)
      rw [hcarrier]
      exact hx_KB
  refine ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc, hq_s_not_T,
    hinvT, hcontainT, hUEbar_le_T, hcyclic, hinv, K, B, hK_eq, hK_cyc, rfl,
    hjoin⟩

end CFSG.GorensteinWalter
