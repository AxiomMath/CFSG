module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreSetup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreFitting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreA7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.KleinFourTransitive
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreMaximal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePPg
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreComponentInverted
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ForbiddenConfigurationReflectionInvertedEqU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26Core
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleNotTwoGroupQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7PrimeOrderCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7SylowCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectSubnormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma36
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.TheoremC
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u
/-- The first-case `K₁` is exactly the set of elements of `U` inverted by
`t₁`. -/
public theorem firstCase_cyclic_K1_eq_invertedElements
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c) :
    ((firstCaseBGKData hmin c d).K1 : Set G) =
      invertedElements d.bg.U d.bg.t1 := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := firstCaseBGKData hmin c d
  exact BenderGlauberman.K1_eq_invertedElements d.bg

/-- The first-case `K₂` is exactly the set of elements of `U` inverted by
`t₂`. -/
public theorem firstCase_cyclic_K2_eq_invertedElements
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c) :
    ((firstCaseBGKData hmin c d).K2 : Set G) =
      invertedElements d.bg.U d.bg.t2 := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := firstCaseBGKData hmin c d
  exact BenderGlauberman.K2_eq_invertedElements d.bg

/-- The first-case `K = K₁ ∩ K₂` is normal in `U`. -/
public theorem firstCase_cyclic_K_normal_in_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c) :
    IsNormalIn
      (@BenderGlauberman.Hyp11.K G _ _ d.bg
        (firstCaseBGKData hmin c d))
      d.bg.U := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := firstCaseBGKData hmin c d
  exact BenderGlauberman.K_normal_in_U d.bg

/-- The first-case `K₂` is abelian and normal in `U` (Fact 1.5(iii)). -/
public theorem firstCase_cyclic_K2_abelian_normal
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c) :
    IsMulCommutative ((firstCaseBGKData hmin c d).K2) ∧
      IsNormalIn ((firstCaseBGKData hmin c d).K2) d.bg.U := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := firstCaseBGKData hmin c d
  have hUodd : Nat.Coprime 2 (Nat.card (↥d.bg.U)) := by
    rw [show d.bg.U = c.U by
      change oddCoreOf d.bg.H = oddCoreOf c.H
      rw [d.H_eq]]
    change Nat.Coprime 2
      (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hS : ∀ x : G, x ∈ d.bg.U →
      d.bg.t2 * x * d.bg.t2⁻¹ ∈ d.bg.U :=
    fun x hx => BenderGlauberman.S_normalizes_U d.bg d.bg.t2
      d.bg.t2_mem_S x hx
  have hK2eq := firstCase_cyclic_K2_eq_invertedElements hmin c d
  have h := GorensteinWalter.fact_1_5_iii_inverted_subgroup_abelian_normal
    d.bg.t2_involution hUodd hS hK2eq
  exact ⟨h.1, h.2.1⟩

/-- The first-case subgroup `A = B₁ ∩ K₂` is abelian. -/
public theorem firstCase_cyclic_A_abelian
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg] :
    IsMulCommutative (↥(d.bg.B1 ⊓ d.bg.K2)) := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  have hK2 : IsMulCommutative (↥d.bg.K2) :=
    (BenderGlauberman.theoremC_K2_abelian_normal d.bg).1
  rw [isMulCommutative_iff] at hK2 ⊢
  intro a b
  have haK2 : (a : G) ∈ d.bg.K2 := (Subgroup.mem_inf.mp a.2).2
  have hbK2 : (b : G) ∈ d.bg.K2 := (Subgroup.mem_inf.mp b.2).2
  have h := hK2 ⟨(a : G), haK2⟩ ⟨(b : G), hbK2⟩
  apply Subtype.ext
  change (a : G) * (b : G) = (b : G) * (a : G)
  exact congrArg Subtype.val h

/-- In the first case `K = K₁ ∩ K₂` is abelian (inside the abelian
`K₂`). -/
public theorem firstCase_cyclic_K_abelian
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg] :
    IsMulCommutative (↥(d.bg.K)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  have hK2 : IsMulCommutative (↥d.bg.K2) :=
    (BenderGlauberman.theoremC_K2_abelian_normal d.bg).1
  rw [isMulCommutative_iff] at hK2 ⊢
  intro a b
  have haK2 : (a : G) ∈ d.bg.K2 := (Subgroup.mem_inf.mp a.2).2
  have hbK2 : (b : G) ∈ d.bg.K2 := (Subgroup.mem_inf.mp b.2).2
  have h := hK2 ⟨(a : G), haK2⟩ ⟨(b : G), hbK2⟩
  apply Subtype.ext
  change (a : G) * (b : G) = (b : G) * (a : G)
  exact congrArg Subtype.val h

/-- In the first case, `B = C_U(S)` normalizes `K = K₁ ∩ K₂`. -/
public theorem firstCase_cyclic_B_normalizes_K
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg] :
    d.bg.B ≤ Subgroup.normalizer (d.bg.K : Set G) := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  have hKnorm := BenderGlauberman.K_normal_in_U d.bg
  intro b hbB
  rw [Subgroup.mem_normalizer_iff]
  have hbU : b ∈ d.bg.U := BenderGlauberman.theoremC_B_le_U d.bg hbB
  intro x
  constructor
  · intro hx
    exact hKnorm.2 b hbU x hx
  · intro hx
    have hb' : b⁻¹ ∈ d.bg.U := d.bg.U.inv_mem hbU
    have hback : b⁻¹ * (b * x * b⁻¹) * b ∈ d.bg.K :=
      by
        simpa using hKnorm.2 b⁻¹ hb' (b * x * b⁻¹) hx
    simpa [mul_assoc] using hback

/-- The intersection `B ∩ K` is trivial in the first case. -/
public theorem firstCase_cyclic_B_inter_K_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg] :
    d.bg.B ⊓ d.bg.K = ⊥ := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  apply le_bot_iff.mp
  intro x hx
  have hxB : x ∈ d.bg.B := (Subgroup.mem_inf.mp hx).1
  have hxK : x ∈ d.bg.K := (Subgroup.mem_inf.mp hx).2
  have hxK2 : x ∈ d.bg.K2 := by
    change x ∈ d.bg.K1 ⊓ d.bg.K2 at hxK
    exact (Subgroup.mem_inf.mp hxK).2
  have hxB2 : x ∈ d.bg.B2 :=
    BenderGlauberman.theoremC_mem_B2_of_mem_B d.bg hxB
  have hfix : d.bg.t2 * x * d.bg.t2⁻¹ = x :=
    BenderGlauberman.theoremC_fixed_by_t2_of_mem_B2 d.bg hxB2
  have hinv : d.bg.t2 * x * d.bg.t2⁻¹ = x⁻¹ :=
    hK.K2_inverted x hxK2
  have hxinv : x = x⁻¹ := hfix.symm.trans hinv
  have hx2 : x * x = 1 := by
    calc
      x * x = x⁻¹ * x := congrArg (fun z : G => z * x) hxinv
      _ = 1 := by simp
  have hord2 : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
  have hxU : x ∈ d.bg.U := BenderGlauberman.theoremC_B_le_U d.bg hxB
  have hordU : orderOf x ∣ Nat.card (↥d.bg.U) :=
    Subgroup.orderOf_dvd_natCard d.bg.U hxU
  have hUodd : Odd (Nat.card (↥d.bg.U)) := by
    have hcop : Nat.Coprime 2 (Nat.card (↥d.bg.U)) := by
      rw [show d.bg.U = c.U by
        change oddCoreOf d.bg.H = oddCoreOf c.H
        rw [d.H_eq]]
      change Nat.Coprime 2
        (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
      rw [Subgroup.card_map_of_injective c.H.subtype_injective]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    exact Nat.coprime_two_left.mp hcop
  have hord1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hUodd.not_two_dvd_nat
        (dvd_trans (by rw [h]) hordU)
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp hord1

private theorem firstCase_cyclic_mem_BK_product
    {G : Type u} [Group G] {U B K : Subgroup G}
    (hBK : B ≤ U) (hKK : K ≤ U) (hKnorm : IsNormalIn K U)
    {x : G} (hxU : x ∈ U) (hx : x ∈ B ⊔ K) :
    ∃ b : G, b ∈ B ∧ ∃ k : G, k ∈ K ∧ b * k = x := by
  classical
  let xU : U := ⟨x, hxU⟩
  have hxSub : xU ∈ (B ⊔ K).subgroupOf U :=
    Subgroup.mem_subgroupOf.mpr hx
  have hEq : (B ⊔ K).subgroupOf U =
      B.subgroupOf U ⊔ K.subgroupOf U :=
    Subgroup.subgroupOf_sup hBK hKK
  have hxSup : xU ∈ B.subgroupOf U ⊔ K.subgroupOf U := by
    simpa [hEq] using hxSub
  have : (K.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff hKK).2
      (fun h k hh hk => hKnorm.2 k hk h hh)
  rcases (Subgroup.mem_sup_of_normal_right.mp hxSup) with
    ⟨b0, hb0, k0, hk0, hprod⟩
  refine ⟨(b0 : G), Subgroup.mem_subgroupOf.mp hb0,
    (k0 : G), Subgroup.mem_subgroupOf.mp hk0, ?_⟩
  exact congrArg Subtype.val hprod

/-- In the first case, every element of `B ⊔ K` is a product `b * k` with
`b ∈ B` and `k ∈ K`. -/
public theorem firstCase_cyclic_BK_product
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg] {x : G}
    (hx : x ∈ d.bg.B ⊔ d.bg.K) :
    ∃ b : G, b ∈ d.bg.B ∧ ∃ k : G, k ∈ d.bg.K ∧ b * k = x := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  have hxU : x ∈ d.bg.U :=
    (sup_le (BenderGlauberman.theoremC_B_le_U d.bg)
      (BenderGlauberman.K_le_U d.bg)) hx
  exact firstCase_cyclic_mem_BK_product
    (BenderGlauberman.theoremC_B_le_U d.bg)
    (BenderGlauberman.K_le_U d.bg)
    (BenderGlauberman.K_normal_in_U d.bg)
    hxU hx

/-- The intersection `(B₁ ∩ K₂) ∩ (B ⊔ K)` is trivial in the first case. -/
public theorem firstCase_cyclic_A_inter_BK_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg] :
    d.bg.B1 ⊓ d.bg.K2 ⊓ (d.bg.B ⊔ d.bg.K) = ⊥ := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  apply le_bot_iff.mp
  intro x hx
  have hxA : x ∈ d.bg.B1 ⊓ d.bg.K2 := (Subgroup.mem_inf.mp hx).1
  have hxBK : x ∈ d.bg.B ⊔ d.bg.K := (Subgroup.mem_inf.mp hx).2
  have hxB1 : x ∈ d.bg.B1 := (Subgroup.mem_inf.mp hxA).1
  have hxK2 : x ∈ d.bg.K2 := (Subgroup.mem_inf.mp hxA).2
  have hxU : x ∈ d.bg.U :=
    (sup_le (BenderGlauberman.theoremC_B_le_U d.bg)
      (BenderGlauberman.K_le_U d.bg)) hxBK
  obtain ⟨b, hbB, k, hkK, hprod⟩ :=
    firstCase_cyclic_mem_BK_product
      (BenderGlauberman.theoremC_B_le_U d.bg)
      (BenderGlauberman.K_le_U d.bg)
      (BenderGlauberman.K_normal_in_U d.bg)
      hxU hxBK
  have hx_eq : x = b * k := hprod.symm
  have hfix : d.bg.t1 * x * d.bg.t1⁻¹ = x :=
    BenderGlauberman.theoremC_fixed_by_t1_of_mem_B1 d.bg hxB1
  have hb1 : b ∈ d.bg.B1 :=
    BenderGlauberman.theoremC_mem_B1_of_mem_B d.bg hbB
  have hb1fix : d.bg.t1 * b * d.bg.t1⁻¹ = b :=
    BenderGlauberman.theoremC_fixed_by_t1_of_mem_B1 d.bg hb1
  have hk1 : k ∈ d.bg.K1 := by
    change k ∈ d.bg.K1 ⊓ d.bg.K2 at hkK
    exact (Subgroup.mem_inf.mp hkK).1
  have hk1inv : d.bg.t1 * k * d.bg.t1⁻¹ = k⁻¹ :=
    hK.K1_inverted k hk1
  have hcalc : d.bg.t1 * (b * k) * d.bg.t1⁻¹ = b * k⁻¹ := by
    calc
      d.bg.t1 * (b * k) * d.bg.t1⁻¹ =
          (d.bg.t1 * b * d.bg.t1⁻¹) * (d.bg.t1 * k * d.bg.t1⁻¹) := by
            group
      _ = b * k⁻¹ := by rw [hb1fix, hk1inv]
  have hkeq : k⁻¹ = k := by
    have h1 : b * k⁻¹ = b * k := by
      calc
        b * k⁻¹ = d.bg.t1 * (b * k) * d.bg.t1⁻¹ := hcalc.symm
        _ = d.bg.t1 * x * d.bg.t1⁻¹ := by rw [hx_eq]
        _ = x := hfix
        _ = b * k := hx_eq
    exact (mul_left_cancel h1)
  have hk2 : k * k = 1 := by
    calc
      k * k = k⁻¹ * k := congrArg (fun z : G => z * k) hkeq.symm
      _ = 1 := by simp
  have hkU : k ∈ d.bg.U := BenderGlauberman.K_le_U d.bg hkK
  have hord2 : orderOf k ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hk2)
  have hordU : orderOf k ∣ Nat.card (↥d.bg.U) :=
    Subgroup.orderOf_dvd_natCard d.bg.U hkU
  have hUodd : Odd (Nat.card (↥d.bg.U)) := by
    have hcop : Nat.Coprime 2 (Nat.card (↥d.bg.U)) := by
      rw [show d.bg.U = c.U by
        change oddCoreOf d.bg.H = oddCoreOf c.H
        rw [d.H_eq]]
      change Nat.Coprime 2
        (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
      rw [Subgroup.card_map_of_injective c.H.subtype_injective]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    exact Nat.coprime_two_left.mp hcop
  have hord1 : orderOf k = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hUodd.not_two_dvd_nat
        (dvd_trans (by rw [h]) hordU)
  have hk_one : k = 1 := orderOf_eq_one_iff.mp hord1
  have hx_eq_b : x = b := by
    rw [hx_eq, hk_one]
    simp
  have hbK2 : b ∈ d.bg.K2 := by
    simpa [hx_eq_b] using hxK2
  have hbB2 : b ∈ d.bg.B2 :=
    BenderGlauberman.theoremC_mem_B2_of_mem_B d.bg hbB
  have hbfix : d.bg.t2 * b * d.bg.t2⁻¹ = b :=
    BenderGlauberman.theoremC_fixed_by_t2_of_mem_B2 d.bg hbB2
  have hbinv : d.bg.t2 * b * d.bg.t2⁻¹ = b⁻¹ :=
    hK.K2_inverted b hbK2
  have hbeq : b = b⁻¹ := hbfix.symm.trans hbinv
  have hb2 : b * b = 1 := by
    calc
      b * b = b⁻¹ * b := congrArg (fun z : G => z * b) hbeq
      _ = 1 := by simp
  have hbU : b ∈ d.bg.U := BenderGlauberman.theoremC_B_le_U d.bg hbB
  have hord2b : orderOf b ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hb2)
  have hordUb : orderOf b ∣ Nat.card (↥d.bg.U) :=
    Subgroup.orderOf_dvd_natCard d.bg.U hbU
  have hord1b : orderOf b = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2b with h | h
    · exact h
    · exfalso
      exact hUodd.not_two_dvd_nat
        (dvd_trans (by rw [h]) hordUb)
  have hb_one : b = 1 := orderOf_eq_one_iff.mp hord1b
  rw [Subgroup.mem_bot]
  rw [hx_eq_b, hb_one]

/-- In the first case, the order of `K = K₁ ∩ K₂` is coprime to the index
of `H = C_G(t)`: the Theorem-C coprimality input. -/
public theorem firstCase_cyclic_K_card_coprime_H_index
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (d : FirstCaseBGData c) :
    Nat.Coprime
      (Nat.card (@BenderGlauberman.Hyp11.K G _ _ d.bg
        (firstCaseBGKData hmin c d)))
      d.bg.H.index := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := firstCaseBGKData hmin c d
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  have hS0centK : d.bg.S0 ≤ Subgroup.centralizer (d.bg.K : Set G) := by
    intro s hs k hk
    exact ((Subgroup.mem_centralizer_iff.mp
      (BenderGlauberman.theoremC_S0_centralizes_K d.bg hk)) s hs).symm
  have hKinv : BenderGlauberman.IsInvertedBy d.bg.t1 d.bg.K := by
    intro k hk
    exact (inferInstance : BenderGlauberman.Hyp11KData d.bg).K1_inverted k
      (Subgroup.mem_inf.mp hk).1
  have hKnormU : IsNormalIn d.bg.K d.bg.U :=
    firstCase_cyclic_K_normal_in_U hmin c d
  have hKleU : d.bg.K ≤ d.bg.U := BenderGlauberman.K_le_U d.bg
  have hKodd : Nat.Coprime 2 (Nat.card (d.bg.K)) :=
    (inferInstance : BenderGlauberman.Hyp11KData d.bg).K1_odd.coprime_dvd_right
      (Subgroup.card_dvd_of_le (show d.bg.K ≤ d.bg.K1 from by
        intro k hk
        exact (Subgroup.mem_inf.mp hk).1))
  have hKFU : d.bg.K ≤ c.FU := by
    have hKleK1 : d.bg.K ≤ d.bg.K1 := by
      intro k hk
      exact (Subgroup.mem_inf.mp hk).1
    have hK1eq : d.bg.K1 = d.I1 := by
      change (firstCaseBGKData hmin c d).K1 = d.I1
      rfl
    exact hKleK1.trans (by simpa [hK1eq] using d.I1_hall.1)
  have hNX : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ d.bg.K →
      Subgroup.normalizer (X : Set G) ≤ d.bg.H := by
    intro X hXne hXK x hx
    have hXFU : X ≤ c.FU := hXK.trans hKFU
    have hNleHhat : Subgroup.normalizer (X : Set G) ≤ c.Hhat :=
      hfirst.2 X hXne hXFU
    have hNleH : Subgroup.normalizer (X : Set G) ≤ c.H := by
      simpa [hHhat] using hNleHhat
    have hNleH' : Subgroup.normalizer (X : Set G) ≤ d.bg.H := by
      simpa [d.H_eq] using hNleH
    exact hNleH' hx
  exact GorensteinWalter.invertedSubgroup_card_coprime_H_index d.bg
    hS0centK hKinv hKnormU hKleU hKodd hNX

/-- Given the A₇-model identities `A = O₃(U)` and `K = O₃′(F(U))`,
the first-case decomposition `U = F(U)·B` is the Theorem-C product. -/
private theorem firstCase_cyclic_U_eq_A_sup_BK_of_a7model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg]
    (hU0 : d.bg.U = fittingSubgroupOf d.bg.U ⊔ d.bg.B)
    (hAeq : d.bg.B1 ⊓ d.bg.K2 = qCoreOf d.bg.U 3)
    (hKeq : d.bg.K =
      ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
        (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype) :
    d.bg.U = (d.bg.B1 ⊓ d.bg.K2) ⊔ (d.bg.B ⊔ d.bg.K) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfit : fittingSubgroupOf d.bg.U =
      qCoreOf d.bg.U 3 ⊔
        ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
          (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype :=
    fittingSubgroupOf_eq_qCore_sup_pPrimeCore_map d.bg.U 3
  rw [hU0, hfit]
  simp [hAeq, hKeq, sup_assoc, sup_comm, sup_left_comm]

/-- Given the A₇-model identities and the centrality of `O₃(U)` in
`B·O₃′(F(U))`, the commutator input of Theorem C is trivial. -/
private theorem firstCase_cyclic_A_comm_BK_of_a7model
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg]
    (hAeq : d.bg.B1 ⊓ d.bg.K2 = qCoreOf d.bg.U 3)
    (hKeq : d.bg.K =
      ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
        (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype)
    (hPcentB : qCoreOf d.bg.U 3 ≤ Subgroup.centralizer
      (d.bg.B : Set G)) :
    ⁅d.bg.B1 ⊓ d.bg.K2, d.bg.B ⊔ d.bg.K⁆ = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P : Subgroup G := qCoreOf d.bg.U 3
  let F3' : Subgroup G :=
    ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
      (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype
  have hPF : P ≤ Subgroup.centralizer (F3' : Set G) :=
    qCoreOf_centralizes_pPrimeCore_fittingSubgroup d.bg.U 3
  have hPunion : P ≤ Subgroup.centralizer
      ((d.bg.B : Set G) ∪ (F3' : Set G)) := by
    intro p hp z hz
    rcases hz with hzB | hzF
    · exact (Subgroup.mem_centralizer_iff.mp (hPcentB hp)) z hzB
    · exact (Subgroup.mem_centralizer_iff.mp (hPF hp)) z hzF
  have hPsup : P ≤ Subgroup.centralizer
      ((d.bg.B ⊔ F3' : Subgroup G) : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
    exact hPunion
  rw [hAeq, hKeq]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by simpa [P, F3'] using hPsup)

/-- Given the A₇-model identity `K = O₃′(F(U))` and the fixed-point-free
action of `B` on `K`, the complement `B ⊔ K` is Frobenius with kernel
`K`. -/
private theorem firstCase_cyclic_BK_frobenius_of_a7model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg]
    (hKeq : d.bg.K =
      ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
        (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype)
    (hKne : d.bg.K ≠ ⊥)
    (hBfpf : ∀ b : G, b ∈ d.bg.B → b ≠ 1 → ∀ k : G,
      k ∈ ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
        (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype →
        k ≠ 1 → b * k * b⁻¹ ≠ k) :
    BenderGlauberman.IsFrobeniusGroupWithKernel
      (d.bg.B ⊔ d.bg.K) d.bg.K := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  let F3' : Subgroup G :=
    ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
      (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype
  have hKabel : IsMulCommutative (↥d.bg.K) :=
    firstCase_cyclic_K_abelian hmin c d
  have hKnormU : IsNormalIn d.bg.K d.bg.U :=
    BenderGlauberman.K_normal_in_U d.bg
  have hKleU : d.bg.K ≤ d.bg.U := BenderGlauberman.K_le_U d.bg
  have hBKleU : d.bg.B ⊔ d.bg.K ≤ d.bg.U :=
    sup_le (BenderGlauberman.theoremC_B_le_U d.bg) hKleU
  unfold BenderGlauberman.IsFrobeniusGroupWithKernel
  refine ⟨?_, ?_, hKne⟩
  · refine ⟨le_sup_right, ?_⟩
    intro x hx k hk
    exact hKnormU.2 x (hBKleU hx) k hk
  · intro x hx hxnotK k hk hkne
    rcases firstCase_cyclic_BK_product hmin c d hx with
      ⟨b, hbB, k0, hk0K, hprod⟩
    have hx_eq : x = b * k0 := hprod.symm
    have hbne : b ≠ 1 := by
      intro hb1
      apply hxnotK
      have hxK : x ∈ d.bg.K := by
        rw [hx_eq]
        simpa [hb1] using hk0K
      exact hxK
    have hk0comm : k0 * k = k * k0 := by
      rw [isMulCommutative_iff] at hKabel
      have h := hKabel ⟨k0, hk0K⟩ ⟨k, hk⟩
      apply congrArg Subtype.val h
    have hk0k : k0 * k * k0⁻¹ = k := by
      calc
        k0 * k * k0⁻¹ = (k * k0) * k0⁻¹ := by rw [hk0comm]
        _ = k := by group
    have hconj : x * k * x⁻¹ = b * k * b⁻¹ := by
      calc
        x * k * x⁻¹ = (b * k0) * k * (b * k0)⁻¹ := by rw [hx_eq]
        _ = b * (k0 * k * k0⁻¹) * b⁻¹ := by group
        _ = b * k * b⁻¹ := by rw [hk0k]
    have hbneK : b * k * b⁻¹ ≠ k := by
      have hkF : k ∈ F3' := by simpa [F3', hKeq] using hk
      exact hBfpf b hbB hbne k hkF hkne
    intro hfix
    apply hbneK
    calc
      b * k * b⁻¹ = x * k * x⁻¹ := hconj.symm
      _ = k := hfix

/-- Package the three remaining Theorem-C inputs from the A₇-model
identities `A = O₃(U)`, `K = O₃′(F(U))`, the centrality of `A` in
`B·K`, and the fixed-point-free action of `B` on `K`. -/
public theorem firstCase_cyclic_theoremC_inputs_of_a7model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg]
    (hU0 : d.bg.U = fittingSubgroupOf d.bg.U ⊔ d.bg.B)
    (hAeq : d.bg.B1 ⊓ d.bg.K2 = qCoreOf d.bg.U 3)
    (hKeq : d.bg.K =
      ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
        (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype)
    (hPcentB : qCoreOf d.bg.U 3 ≤ Subgroup.centralizer
      (d.bg.B : Set G))
    (hKne : d.bg.K ≠ ⊥)
    (hBfpf : ∀ b : G, b ∈ d.bg.B → b ≠ 1 → ∀ k : G,
      k ∈ ((pPrimeCore 3 (fittingSubgroup d.bg.U)).map
        (fittingSubgroup d.bg.U).subtype).map d.bg.U.subtype →
        k ≠ 1 → b * k * b⁻¹ ≠ k) :
    d.bg.U = (d.bg.B1 ⊓ d.bg.K2) ⊔ (d.bg.B ⊔ d.bg.K) ∧
      ⁅d.bg.B1 ⊓ d.bg.K2, d.bg.B ⊔ d.bg.K⁆ = ⊥ ∧
        (d.bg.U ≠ d.bg.B ⊔ d.bg.K →
          BenderGlauberman.IsFrobeniusGroupWithKernel
            (d.bg.B ⊔ d.bg.K) d.bg.K) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  exact ⟨
    firstCase_cyclic_U_eq_A_sup_BK_of_a7model hmin c d hU0 hAeq hKeq,
    firstCase_cyclic_A_comm_BK_of_a7model c d hAeq hKeq hPcentB,
    fun hne => firstCase_cyclic_BK_frobenius_of_a7model hmin c d
      hKeq hKne hBfpf⟩

/-- The intersection `(B₁ ∩ K₂) ∩ B` is trivial in the first case. -/
public theorem firstCase_cyclic_A_inter_B_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    [hK : BenderGlauberman.Hyp11KData d.bg] :
    d.bg.B1 ⊓ d.bg.K2 ⊓ d.bg.B = ⊥ := by
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData d.bg := hK
  apply le_bot_iff.mp
  intro x hx
  have hxA : x ∈ d.bg.B1 ⊓ d.bg.K2 := (Subgroup.mem_inf.mp hx).1
  have hxB : x ∈ d.bg.B := (Subgroup.mem_inf.mp hx).2
  have hxK2 : x ∈ d.bg.K2 := (Subgroup.mem_inf.mp hxA).2
  have hxB2 : x ∈ d.bg.B2 :=
    BenderGlauberman.theoremC_mem_B2_of_mem_B d.bg hxB
  have hfix : d.bg.t2 * x * d.bg.t2⁻¹ = x :=
    BenderGlauberman.theoremC_fixed_by_t2_of_mem_B2 d.bg hxB2
  have hinv : d.bg.t2 * x * d.bg.t2⁻¹ = x⁻¹ :=
    hK.K2_inverted x hxK2
  have hxinv : x = x⁻¹ := hfix.symm.trans hinv
  have hx2 : x * x = 1 := by
    calc
      x * x = x⁻¹ * x := congrArg (fun z : G => z * x) hxinv
      _ = 1 := by simp
  have hord2 : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
  have hxU : x ∈ d.bg.U := BenderGlauberman.theoremC_B_le_U d.bg hxB
  have hordU : orderOf x ∣ Nat.card (↥d.bg.U) :=
    Subgroup.orderOf_dvd_natCard d.bg.U hxU
  have hUodd : Odd (Nat.card (↥d.bg.U)) := by
    have hcop : Nat.Coprime 2 (Nat.card (↥d.bg.U)) := by
      rw [show d.bg.U = c.U by
        change oddCoreOf d.bg.H = oddCoreOf c.H
        rw [d.H_eq]]
      change Nat.Coprime 2
        (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
      rw [Subgroup.card_map_of_injective c.H.subtype_injective]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    exact Nat.coprime_two_left.mp hcop
  have hord1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hUodd.not_two_dvd_nat
        (dvd_trans (by rw [h]) hordU)
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp hord1

/-- In the cyclic two-core subcase, the oriented prime data, Klein-four
data, Sylow `p`-subgroup of `B`, and a maximal overgroup `M` can be
assembled, and the full `D`-group dispatcher places `V₂` in the component
layer of `M`. -/
public theorem firstCase_cyclic_V2_le_componentLayer_of_od
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (od : FirstCaseOrientedPrimeData c) :
    ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
      ∃ fd : FirstCaseFourData c od.d,
        ∃ Q : Sylow od.p ↥od.d.bg.B,
          ∃ M : Subgroup G,
            IsCoatom M ∧
              Subgroup.normalizer
                (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                (c.S : Subgroup G) ≤ M ∧
                  fd.V2 ≤ componentLayerOf M := by
  classical
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  have hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B := by
    have hinverted : ∀ r : G, c.IsReflection r →
        ∃ I : Subgroup G, IsInvertedSubgroup I c.U r := by
      intro r hr
      obtain ⟨I, hI, _hHall⟩ := hfirst.1 r hr
      exact ⟨I, hI⟩
    have hcomm : ⁅(c.S : Subgroup G), c.U⁆ ≤ c.FU :=
      lemma_2_8_commutator_le_FU c hinverted
    have hcommBG : ⁅(od.d.bg.S : Subgroup G), od.d.bg.U⁆ ≤
        fittingSubgroupOf od.d.bg.U := by
      have hS : (c.S : Subgroup G) = (od.d.bg.S : Subgroup G) := od.d.S_eq.symm
      have hU : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
      have hFU : c.FU = fittingSubgroupOf od.d.bg.U := by
        have hFU' : c.FU = fittingSubgroupOf c.U := rfl
        rw [hFU', hU]
      have hcomm2 : ⁅(c.S : Subgroup G), c.U⁆ ≤ fittingSubgroupOf od.d.bg.U := by
        rwa [hFU] at hcomm
      rw [hS, hU] at hcomm2
      exact hcomm2
    exact firstCase_U_eq_FU_sup_B od.d.bg hcommBG
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  obtain ⟨fd⟩ := exists_firstCaseFourData c od.d
  obtain ⟨Q⟩ := Sylow.nonempty (G := ↥od.d.bg.B)
  obtain ⟨M, hMmax, hMN, hSM, _hP0⟩ :=
    firstCase_exists_maximal_P2_with_P0_ne_bot
      hmin c od hfirst hHhat hU Q
  have hD : IsDGroup (↥M) :=
    properSubgroups_areDGroups hmin M hMmax.1
  have hV := firstCase_V2_le_componentLayer_of_DGroup
    hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM hD
  exact ⟨hU, fd, Q, M, hMmax, hMN, hSM, hV⟩

/-- In the cyclic two-core subcase, the oriented prime data, Klein-four
data, Sylow `p`-subgroup of `B`, and a maximal overgroup `M` can be
assembled, and the full `D`-group dispatcher places `V₂` in the component
layer of `M`. -/
public theorem firstCase_cyclic_V2_le_componentLayer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ od : FirstCaseOrientedPrimeData c,
      ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
        ∃ fd : FirstCaseFourData c od.d,
          ∃ Q : Sylow od.p ↥od.d.bg.B,
            ∃ M : Subgroup G,
              IsCoatom M ∧
                Subgroup.normalizer
                  (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                  (c.S : Subgroup G) ≤ M ∧
                    fd.V2 ≤ componentLayerOf M := by
  classical
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  obtain ⟨od⟩ := exists_firstCaseOrientedPrimeData hmin c hfirst hHhat
  obtain ⟨hU, fd, Q, M, hMmax, hMN, hSM, hV⟩ :=
    firstCase_cyclic_V2_le_componentLayer_of_od hmin c hfirst hcyclic od
  exact ⟨od, hU, fd, Q, M, hMmax, hMN, hSM, hV⟩

/-- In the cyclic two-core subcase, the component layer of the chosen
maximal subgroup is nontrivial. -/
public theorem firstCase_cyclic_componentLayer_exists
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G,
      IsCoatom M ∧ componentLayerOf M ≠ ⊥ := by
  classical
  obtain ⟨od, hU, fd, Q, M, hMmax, hMN, hSM, hV⟩ :=
    firstCase_cyclic_V2_le_componentLayer hmin c hfirst hcyclic
  have hV2ne : fd.V2 ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card fd.V2 = 4 := fd.V2_klein.card_four
    rw [hbot] at hcard
    norm_num at hcard
  have hEne : componentLayerOf M ≠ ⊥ := by
    intro hbot
    apply hV2ne
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.mem_bot.mp (by simpa [hbot] using hV hx)
  exact ⟨M, hMmax, hEne⟩

/-- In the cyclic two-core subcase there is a quasisimple component of a
maximal subgroup. -/
public theorem firstCase_cyclic_component_exists
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, ∃ E : Subgroup G,
      IsCoatom M ∧ IsComponentOf E M := by
  classical
  obtain ⟨M, hMmax, hEne⟩ :=
    firstCase_cyclic_componentLayer_exists hmin c hfirst hcyclic
  have hcomp : ∃ E : Subgroup G, IsComponentOf E M := by
    by_contra hnone
    have hset : {E : Subgroup G | IsComponentOf E M} = ∅ := by
      ext E
      constructor
      · intro hE
        exact False.elim (hnone ⟨E, hE⟩)
      · intro hE
        simp at hE
    have hbot : componentLayerOf M = ⊥ := by
      rw [componentLayerOf]
      simp [hset]
    exact hEne hbot
  rcases hcomp with ⟨E, hE⟩
  exact ⟨M, E, hMmax, hE⟩

/-- The selected component in the cyclic two-core subcase is a proper
`D`-group, so the `D`-group classification can be applied to it. -/
public theorem firstCase_cyclic_component_isDGroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, ∃ E : Subgroup G,
      IsCoatom M ∧ IsComponentOf E M ∧ IsDGroup (↥E) := by
  classical
  obtain ⟨M, E, hMmax, hE⟩ :=
    firstCase_cyclic_component_exists hmin c hfirst hcyclic
  have hEproper : E ≠ ⊤ := by
    intro htop
    have hMtop : M = ⊤ := le_antisymm (le_top) (by
      intro x hx
      exact hE.1 (by simpa [htop] using hx))
    exact hMmax.1 hMtop
  have hD : IsDGroup (↥E) := properSubgroups_areDGroups hmin E hEproper
  exact ⟨M, E, hMmax, hE, hD⟩

/-- The selected cyclic component is a `D`-group whose odd-core quotient is
not a `2`-group: only the `A₇` or odd `PSL₂/PGL₂` models can occur. -/
public theorem firstCase_cyclic_component_dGroup_notTwo
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, ∃ E : Subgroup G,
      IsCoatom M ∧ IsComponentOf E M ∧
        IsDGroup (↥E) ∧
          ¬ IsPGroup 2 ((↥E) ⧸ pPrimeCore 2 (↥E)) := by
  classical
  obtain ⟨M, E, hMmax, hE, hD⟩ :=
    firstCase_cyclic_component_isDGroup hmin c hfirst hcyclic
  have hnot2 : ¬ IsPGroup 2 ((↥E) ⧸ pPrimeCore 2 (↥E)) :=
    quasisimple_not_quotient_isTwoGroup hE.2.2
  exact ⟨M, E, hMmax, hE, hD, hnot2⟩

/-- The `D`-group model of the cyclic component: after excluding the
two-group quotient, it is either `A₇` or an odd `PSL₂/PGL₂` quotient. -/
public theorem firstCase_cyclic_component_model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, ∃ E : Subgroup G,
      IsCoatom M ∧ IsComponentOf E M ∧
        (Nonempty ((↥E) ⧸ pPrimeCore 2 (↥E) ≃* alternatingGroup (Fin 7)) ∨
          ∃ (K : Type u) (_ : Field K) (_ : Finite K),
            IsOddPrimePower (Nat.card K) ∧
              ∃ L : Subgroup ((↥E) ⧸ pPrimeCore 2 (↥E)),
                L.Normal ∧ Odd L.index ∧
                  (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K))) := by
  classical
  obtain ⟨M, E, hMmax, hE, hD, _hnot2⟩ :=
    firstCase_cyclic_component_dGroup_notTwo hmin c hfirst hcyclic
  rcases hD with ⟨_hSylow, hQ⟩ | ⟨_hSylow, hA7⟩ |
    ⟨_hSylow, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
  · exact False.elim (quasisimple_not_quotient_isTwoGroup hE.2.2 hQ)
  · exact ⟨M, E, hMmax, hE, Or.inl hA7⟩
  · exact ⟨M, E, hMmax, hE,
      Or.inr ⟨K, inferInstance, inferInstance, hKprime, L, hLnormal, hLindex, hLmodel⟩⟩

/-- The selected cyclic component is quasisimple. -/
public theorem firstCase_cyclic_component_isQuasisimple
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, ∃ E : Subgroup G,
      IsCoatom M ∧ IsComponentOf E M ∧ IsQuasisimple (↥E) := by
  classical
  obtain ⟨M, E, hMmax, hE, _hD, _hnot2⟩ :=
    firstCase_cyclic_component_dGroup_notTwo hmin c hfirst hcyclic
  exact ⟨M, E, hMmax, hE, hE.2.2⟩

/-- Combine the `D`-group model and the quasisimple property of the cyclic
component: the frontier is `A₇` or an odd `PSL₂/PGL₂` quotient. -/
public theorem firstCase_cyclic_component_modelData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, ∃ E : Subgroup G,
      IsCoatom M ∧ IsComponentOf E M ∧ IsQuasisimple (↥E) ∧
        (Nonempty ((↥E) ⧸ pPrimeCore 2 (↥E) ≃* alternatingGroup (Fin 7)) ∨
          ∃ (K : Type u) (_ : Field K) (_ : Finite K),
            IsOddPrimePower (Nat.card K) ∧
              ∃ L : Subgroup ((↥E) ⧸ pPrimeCore 2 (↥E)),
                L.Normal ∧ Odd L.index ∧
                  (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K))) := by
  classical
  obtain ⟨M, E, hMmax, hE, hmodel⟩ :=
    firstCase_cyclic_component_model hmin c hfirst hcyclic
  exact ⟨M, E, hMmax, hE, hE.2.2, hmodel⟩

/-- The selected cyclic component has even order, hence nontrivial Sylow
`2`-subgroups. -/
public theorem firstCase_cyclic_component_even
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, ∃ E : Subgroup G,
      IsCoatom M ∧ IsComponentOf E M ∧ 2 ∣ Nat.card (↥E) := by
  classical
  obtain ⟨M, E, hMmax, hE, _hD, _hnot2⟩ :=
    firstCase_cyclic_component_dGroup_notTwo hmin c hfirst hcyclic
  have h4 : 4 ∣ Nat.card (↥E) := isQuasisimple_four_dvd_card hE.2.2
  have h2 : 2 ∣ Nat.card (↥E) := dvd_trans (by norm_num) h4
  exact ⟨M, E, hMmax, hE, h2⟩

/-- The whole component layer in the cyclic subcase is a proper
`D`-group. -/
public theorem firstCase_cyclic_componentLayer_isDGroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G,
      IsCoatom M ∧ IsDGroup (↥(componentLayerOf M)) := by
  classical
  obtain ⟨M, hMmax, hEne⟩ :=
    firstCase_cyclic_componentLayer_exists hmin c hfirst hcyclic
  have hproper : componentLayerOf M ≠ ⊤ := by
    intro htop
    have hle : componentLayerOf M ≤ M := (componentLayerOf_isNormalIn M).1
    have hMtop : M = ⊤ := le_antisymm le_top (by
      intro x hx
      exact hle (by simpa [htop] using hx))
    exact hMmax.1 hMtop
  exact ⟨M, hMmax, properSubgroups_areDGroups hmin (componentLayerOf M) hproper⟩

/-- The `D`-group model of the whole cyclic component layer, including the
two-group quotient alternative. -/
public theorem firstCase_cyclic_componentLayer_model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G,
      IsCoatom M ∧
        (IsPGroup 2 ((componentLayerOf M) ⧸ pPrimeCore 2 (componentLayerOf M)) ∨
          Nonempty ((componentLayerOf M) ⧸ pPrimeCore 2 (componentLayerOf M) ≃*
            alternatingGroup (Fin 7)) ∨
          ∃ (K : Type u) (_ : Field K) (_ : Finite K),
            IsOddPrimePower (Nat.card K) ∧
              ∃ L : Subgroup
                ((componentLayerOf M) ⧸ pPrimeCore 2 (componentLayerOf M)),
                L.Normal ∧ Odd L.index ∧
                  (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K))) := by
  classical
  obtain ⟨M, hMmax, hD⟩ :=
    firstCase_cyclic_componentLayer_isDGroup hmin c hfirst hcyclic
  rcases hD with ⟨_hSylow, hQ⟩ | ⟨_hSylow, hA7⟩ |
    ⟨_hSylow, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
  · exact ⟨M, hMmax, Or.inl hQ⟩
  · exact ⟨M, hMmax, Or.inr (Or.inl hA7)⟩
  · exact ⟨M, hMmax,
      Or.inr (Or.inr ⟨K, inferInstance, inferInstance,
        hKprime, L, hLnormal, hLindex, hLmodel⟩)⟩

public theorem firstCase_cyclic_componentLayer_ker_le_oddCore
    {G : Type u} [Group G] [Finite G]
    (L E0 : Subgroup G) (hE0L : E0 ≤ L)
    (hOmap_norm : ∀ e : G, e ∈ E0 →
      ∀ x : G, x ∈ (pPrimeCore 2 (↥L)).map L.subtype →
        e * x * e⁻¹ ∈ (pPrimeCore 2 (↥L)).map L.subtype) :
    (pPrimeCore 2 (↥L)).map L.subtype ⊓ E0 ≤
      (pPrimeCore 2 (↥E0)).map E0.subtype := by
  classical
  let Omap : Subgroup G := (pPrimeCore 2 (↥L)).map L.subtype
  let H : Subgroup G := Omap ⊓ E0
  let X : Subgroup (↥E0) := H.subgroupOf E0
  have : X.Normal :=
    (Subgroup.normal_subgroupOf_iff (show H ≤ E0 from inf_le_right)).2
      (fun h k hh hk =>
        (Subgroup.mem_inf.mpr
          ⟨hOmap_norm k hk h (Subgroup.mem_inf.mp hh).1,
            E0.mul_mem (E0.mul_mem hk (Subgroup.mem_inf.mp hh).2)
              (E0.inv_mem hk)⟩))
  have hXodd : Nat.Coprime 2 (Nat.card X) := by
    have hXleH : X.map E0.subtype ≤ H := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    have hXleOmap : X.map E0.subtype ≤ Omap := hXleH.trans inf_le_left
    have hcard_dvd : Nat.card X ∣ Nat.card (pPrimeCore 2 (↥L)) := by
      calc
        Nat.card X = Nat.card (X.map E0.subtype) :=
          (Nat.card_congr
            (Subgroup.equivMapOfInjective X E0.subtype
              E0.subtype_injective).toEquiv)
        _ ∣ Nat.card Omap := Subgroup.card_dvd_of_le hXleOmap
        _ = Nat.card (pPrimeCore 2 (↥L)) :=
          (Subgroup.card_map_of_injective L.subtype_injective)
    exact (pPrimeCore_coprime_card (p := 2) (G := ↥L)).coprime_dvd_right
      hcard_dvd
  have hXleCore : X ≤ pPrimeCore 2 (↥E0) :=
    le_sSup
      (show X ∈ {L : Subgroup (↥E0) |
        L.Normal ∧ Nat.Coprime 2 (Nat.card L)} from ⟨inferInstance, hXodd⟩)
  intro x hx
  have hxO : x ∈ Omap := hx.1
  have hxE0 : x ∈ E0 := hx.2
  have hxH : x ∈ H := Subgroup.mem_inf.mpr ⟨hxO, hxE0⟩
  have hxX : (⟨x, hxE0⟩ : E0) ∈ X := Subgroup.mem_subgroupOf.mpr hxH
  have hxCore : (⟨x, hxE0⟩ : E0) ∈ pPrimeCore 2 (↥E0) := hXleCore hxX
  exact Subgroup.mem_map.mpr ⟨⟨x, hxE0⟩, hxCore, rfl⟩

/-- In the cyclic subcase the component layer quotient by the odd core is
not a `2`-group. -/
public theorem firstCase_cyclic_componentLayer_notTwo
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, IsCoatom M ∧
      ¬ IsPGroup 2 ((componentLayerOf M) ⧸ pPrimeCore 2 (componentLayerOf M)) := by
  classical
  obtain ⟨M, E0, hMmax, hE0, _hD0, hnot2⟩ :=
    firstCase_cyclic_component_dGroup_notTwo hmin c hfirst hcyclic
  let L : Subgroup G := componentLayerOf M
  have hE0L : E0 ≤ L := le_sSup hE0
  have hproper : L ≠ ⊤ := by
    intro htop
    have hle : L ≤ M := (componentLayerOf_isNormalIn M).1
    have hMtop : M = ⊤ := le_antisymm le_top (by
      intro x hx
      exact hle (by simpa [htop] using hx))
    exact hMmax.1 hMtop
  have hD_layer : IsDGroup (↥L) := properSubgroups_areDGroups hmin L hproper
  rcases hD_layer with ⟨_hSylow, htwo⟩ | ⟨_hSylow, hA7⟩ |
    ⟨_hSylow, K, hKprime, Lsub, hLnormal, hLindex, hLmodel⟩
  · exfalso
    let O : Subgroup (↥L) := pPrimeCore 2 (↥L)
    let Omap : Subgroup G := O.map L.subtype
    have hOmap_norm : ∀ e : G, e ∈ E0 →
        ∀ x : G, x ∈ Omap → e * x * e⁻¹ ∈ Omap := by
      intro e he x hx
      rcases Subgroup.mem_map.mp hx with ⟨o, ho, rfl⟩
      have heL : e ∈ L := hE0L he
      have hconj : (⟨e, heL⟩ : L) * o * (⟨e, heL⟩ : L)⁻¹ ∈ O :=
        (inferInstance : O.Normal).conj_mem o ho (⟨e, heL⟩ : L)
      exact Subgroup.mem_map.mpr
        ⟨(⟨e, heL⟩ : L) * o * (⟨e, heL⟩ : L)⁻¹, hconj, by
          change e * (o : G) * e⁻¹ = e * (o : G) * e⁻¹
          rfl⟩
    have hker_le_G : Omap ⊓ E0 ≤
        (pPrimeCore 2 (↥E0)).map E0.subtype :=
      firstCase_cyclic_componentLayer_ker_le_oddCore L E0 hE0L hOmap_norm
    let f0 : E0 →* (↥L ⧸ O) :=
      (QuotientGroup.mk' O).comp (Subgroup.inclusion hE0L)
    have hker_le : f0.ker ≤ pPrimeCore 2 (↥E0) := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hq1 : QuotientGroup.mk' O (Subgroup.inclusion hE0L x) = 1 := by
        simpa [f0] using hx
      have hmemO : Subgroup.inclusion hE0L x ∈ O :=
        (QuotientGroup.eq_one_iff (N := O)
          (Subgroup.inclusion hE0L x)).mp hq1
      have hxOmap : (x : G) ∈ Omap :=
        Subgroup.mem_map.mpr ⟨Subgroup.inclusion hE0L x, hmemO, by
          exact (Subgroup.coe_inclusion hE0L x)⟩
      have hxG : (x : G) ∈ Omap ⊓ E0 :=
        Subgroup.mem_inf.mpr ⟨hxOmap, x.2⟩
      have hxCoreG : (x : G) ∈ (pPrimeCore 2 (↥E0)).map E0.subtype :=
        hker_le_G hxG
      rcases Subgroup.mem_map.mp hxCoreG with ⟨y, hy, hyx⟩
      have hxy : x = y := by
        apply Subtype.ext
        exact hyx.symm
      simpa [hxy] using hy
    have hE0two : IsPGroup 2 (E0 ⧸ pPrimeCore 2 (↥E0)) :=
      isPGroup_quotient_of_map_isPGroup_of_ker_le f0
        (pPrimeCore 2 (↥E0)) hker_le htwo
    exact hnot2 hE0two
  · refine ⟨M, hMmax, ?_⟩
    intro htwo2
    have hA7two : IsPGroup 2 (alternatingGroup (Fin 7)) :=
      htwo2.of_equiv hA7.some
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA7two
    have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have hthree : 3 ∣ 2 ^ n := by
      rw [← hn, hcard]
      norm_num
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
    norm_num at h32
  · refine ⟨M, hMmax, ?_⟩
    intro htwo2
    have hLtwo : IsPGroup 2 Lsub := htwo2.to_subgroup Lsub
    rcases hLmodel with hPSLmodel | hPGLmodel
    · rcases hPSLmodel with ⟨e⟩
      exact not_isPGroup_two_of_psl2_odd K hKprime
        (hLtwo.of_equiv e)
    · rcases hPGLmodel with ⟨e⟩
      exact not_isPGroup_two_of_pgl2_odd K hKprime
        (hLtwo.of_equiv e)

/-- The cyclic component-layer quotient by the odd core is `A₇` or has an
odd-index `PSL₂/PGL₂` model; the `2`-group alternative is impossible. -/
public theorem firstCase_cyclic_componentLayer_model_noTwo
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ M : Subgroup G, IsCoatom M ∧
      (Nonempty ((componentLayerOf M) ⧸ pPrimeCore 2 (componentLayerOf M) ≃*
        alternatingGroup (Fin 7)) ∨
        ∃ (K : Type u) (_ : Field K) (_ : Finite K),
          IsOddPrimePower (Nat.card K) ∧
            ∃ L : Subgroup
              ((componentLayerOf M) ⧸ pPrimeCore 2 (componentLayerOf M)),
              L.Normal ∧ Odd L.index ∧
                (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K))) := by
  classical
  obtain ⟨M, hMmax, hnot2⟩ :=
    firstCase_cyclic_componentLayer_notTwo hmin c hfirst hcyclic
  let L : Subgroup G := componentLayerOf M
  have hproper : L ≠ ⊤ := by
    intro htop
    have hle : L ≤ M := (componentLayerOf_isNormalIn M).1
    have hMtop : M = ⊤ := le_antisymm le_top (by
      intro x hx
      exact hle (by simpa [htop] using hx))
    exact hMmax.1 hMtop
  have hD : IsDGroup (↥L) := properSubgroups_areDGroups hmin L hproper
  rcases hD with ⟨_hSylow, htwo⟩ | ⟨_hSylow, hA7⟩ |
    ⟨_hSylow, K, hKprime, Lsub, hLnormal, hLindex, hLmodel⟩
  · exact False.elim (hnot2 htwo)
  · exact ⟨M, hMmax, Or.inl hA7⟩
  · exact ⟨M, hMmax,
      Or.inr ⟨K, inferInstance, inferInstance, hKprime,
        Lsub, hLnormal, hLindex, hLmodel⟩⟩

/-- In the A₇ layer model, the image of the component layer in
`M / O(M)` is again isomorphic to `A₇`. -/
private theorem firstCase_cyclic_componentLayer_image_a7_of_layer_a7
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7))) :
    let q : M →* M ⧸ pPrimeCore 2 M := QuotientGroup.mk' (pPrimeCore 2 M)
    let E : Subgroup G := componentLayerOf M
    Nonempty ((E.subgroupOf M).map q ≃* alternatingGroup (Fin 7)) := by
  classical
  dsimp
  let q : M →* M ⧸ pPrimeCore 2 M := QuotientGroup.mk' (pPrimeCore 2 M)
  let E : Subgroup G := componentLayerOf M
  let Ei : Subgroup M := E.subgroupOf M
  let Ebar : Subgroup (M ⧸ pPrimeCore 2 M) := Ei.map q
  let OE : Subgroup E := pPrimeCore 2 E
  have hE_normalM : IsNormalIn E M := componentLayerOf_isNormalIn M
  have hE_le_M : E ≤ M := hE_normalM.1
  let eEi : Ei ≃* E := Subgroup.subgroupOfEquivOfLe hE_le_M
  have hEi_normal : Ei.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := E)
      (by
        intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          exact hE_normalM.2 m hm x hx
        · intro hx
          have hm' : m⁻¹ ∈ M := M.inv_mem hm
          have hback : m⁻¹ * (m * x * m⁻¹) * m ∈ E :=
            by simpa using hE_normalM.2 m⁻¹ hm' (m * x * m⁻¹) hx
          simpa [mul_assoc] using hback)
  have : Ei.Normal := hEi_normal
  have hOEi_le_O : (pPrimeCore 2 Ei).map Ei.subtype ≤ pPrimeCore 2 M :=
    pPrimeCore_map_subtype_le_pPrimeCore_of_normal (p := 2) Ei
  let OM : Subgroup G := (pPrimeCore 2 M).map M.subtype
  have hOE_le_OM : OE.map E.subtype ≤ OM := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨e, he, rfl⟩
    have hmap : (pPrimeCore 2 Ei).map eEi.toMonoidHom = OE :=
      pPrimeCore_map_iso 2 eEi
    have hei : eEi.symm e ∈ pPrimeCore 2 Ei := by
      have hmem : e ∈ (pPrimeCore 2 Ei).map eEi.toMonoidHom := by
        rwa [hmap]
      rcases Subgroup.mem_map.mp hmem with ⟨y, hy, hye⟩
      have hy_eq : y = eEi.symm e := by
        apply eEi.injective
        calc
          eEi y = e := hye
          _ = eEi (eEi.symm e) := (eEi.apply_symm_apply e).symm
      simpa [hy_eq] using hy
    have hxO : Ei.subtype (eEi.symm e) ∈ pPrimeCore 2 M :=
      hOEi_le_O (Subgroup.mem_map.mpr ⟨eEi.symm e, hei, rfl⟩)
    refine Subgroup.mem_map.mpr ⟨Ei.subtype (eEi.symm e), hxO, ?_⟩
    rfl
  have hOE_le_O : ∀ x : G, x ∈ OE.map E.subtype → ∀ hxM : x ∈ M,
      (⟨x, hxM⟩ : M) ∈ pPrimeCore 2 M := by
    intro x hx hxM
    have hxOM : x ∈ OM := hOE_le_OM hx
    rcases Subgroup.mem_map.mp hxOM with ⟨m, hm, hmEq⟩
    have hmEq' : m = ⟨x, hxM⟩ := by
      apply Subtype.ext
      exact hmEq
    simpa [hmEq'] using hm
  -- `O(M) ∩ E = O(E)`, so the quotient map restricted to `E` has kernel `OE`.
  let I : Subgroup E := (OM ⊓ E).subgroupOf E
  have hI_normal : I.Normal := by
    apply (Subgroup.normal_subgroupOf_iff
      (show OM ⊓ E ≤ E from inf_le_right)).2
    intro h k hh hk
    have hhO : h ∈ OM := (Subgroup.mem_inf.mp hh).1
    have hhE : h ∈ E := (Subgroup.mem_inf.mp hh).2
    have hhM : h ∈ M := hE_le_M hhE
    have hhO' : (⟨h, hhM⟩ : M) ∈ pPrimeCore 2 M := by
      rcases Subgroup.mem_map.mp hhO with ⟨m, hm, hmEq⟩
      have hmEq' : m = ⟨h, hhM⟩ := by
        apply Subtype.ext
        exact hmEq
      simpa [hmEq'] using hm
    have hconjO : k * h * k⁻¹ ∈ OM := by
      have hc := (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem
        ⟨h, hhM⟩ hhO' ⟨k, hE_le_M hk⟩
      refine Subgroup.mem_map.mpr
        ⟨⟨k, hE_le_M hk⟩ * ⟨h, hhM⟩ * (⟨k, hE_le_M hk⟩)⁻¹, hc, ?_⟩
      simp [mul_assoc]
    have hconjE : k * h * k⁻¹ ∈ E :=
      hE_normalM.2 k (hE_le_M hk) h hhE
    exact ⟨hconjO, hconjE⟩
  have hI_odd : Nat.Coprime 2 (Nat.card I) := by
    let I_G : Subgroup G := I.map E.subtype
    let O_G : Subgroup G := OM
    have hI_G_le_O_G : I_G ≤ O_G := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨e, he, rfl⟩
      have heO : (e : G) ∈ OM :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp he)).1
      rcases Subgroup.mem_map.mp heO with ⟨m, hm, hmEq⟩
      exact Subgroup.mem_map.mpr ⟨m, hm, hmEq⟩
    have hcard_dvd : Nat.card I_G ∣ Nat.card O_G :=
      Subgroup.card_dvd_of_le hI_G_le_O_G
    have hcardI : Nat.card I = Nat.card I_G := by
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective I E.subtype E.subtype_injective).toEquiv)
    have hcardO : Nat.card O_G = Nat.card (pPrimeCore 2 M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 M)) :=
      pPrimeCore_coprime_card (p := 2) (G := ↥M)
    rw [hcardI]
    exact hcop.coprime_dvd_right (by simpa [hcardO] using hcard_dvd)
  have hI_le_OE : I ≤ OE := le_sSup ⟨hI_normal, hI_odd⟩
  have hO_inter_E_le_OE : ∀ x : G, x ∈ OM → x ∈ E →
      x ∈ OE.map E.subtype := by
    intro x hxO hxE
    have hxI : (⟨x, hxE⟩ : E) ∈ I := by
      exact Subgroup.mem_subgroupOf.mpr ⟨hxO, hxE⟩
    have hxOE : (⟨x, hxE⟩ : E) ∈ OE := hI_le_OE hxI
    exact Subgroup.mem_map.mpr ⟨⟨x, hxE⟩, hxOE, rfl⟩
  let g : E →* Ebar :=
    (q.comp (Subgroup.inclusion hE_le_M)).codRestrict Ebar (fun x =>
      Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion hE_le_M x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hg_surj : Function.Surjective g := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨m, hm, hEq⟩
    refine ⟨⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, ?_⟩
    apply Subtype.ext
    simp [g]
    have hincl : Subgroup.inclusion hE_le_M ⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩ = m := by
      apply Subtype.ext
      rfl
    rw [hincl]
    exact hEq
  have hOE_le_ker : OE ≤ g.ker := by
    intro e he
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change q (⟨(e : G), hE_le_M e.2⟩ : M) = 1
    apply (QuotientGroup.eq_one_iff (N := pPrimeCore 2 M)
      (⟨(e : G), hE_le_M e.2⟩ : M)).2
    exact hOE_le_O (e : G)
      ((Subgroup.mem_map (f := E.subtype)).mpr ⟨e, he, rfl⟩)
      (hE_le_M e.2)
  have hker_le_OE : g.ker ≤ OE := by
    intro e he
    apply MonoidHom.mem_ker.mp at he
    have hq1 : q (⟨(e : G), hE_le_M e.2⟩ : M) = 1 := by
      exact congrArg Subtype.val he
    have heO : (e : G) ∈ OM := by
      have h := (QuotientGroup.eq_one_iff (N := pPrimeCore 2 M)
        (⟨(e : G), hE_le_M e.2⟩ : M)).mp hq1
      exact (Subgroup.mem_map (f := M.subtype)).mpr
        ⟨⟨(e : G), hE_le_M e.2⟩, h, rfl⟩
    have heOE : e ∈ OE := by
      have hmem : (e : G) ∈ OE.map E.subtype :=
        hO_inter_E_le_OE (e : G) heO e.2
      rcases Subgroup.mem_map.mp hmem with ⟨y, hy, hyEq⟩
      have hy_eq : y = e := by
        apply Subtype.ext
        exact hyEq
      simpa [hy_eq] using hy
    exact heOE
  have hker : g.ker = OE := le_antisymm hker_le_OE hOE_le_ker
  let φ : E ⧸ OE →* Ebar := QuotientGroup.lift OE g hOE_le_ker
  have hφ_surj : Function.Surjective φ :=
    QuotientGroup.lift_surjective_of_surjective
      (N := OE) (φ := g) hg_surj hOE_le_ker
  have hφ_ker_bot : φ.ker = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    rw [Subgroup.mem_bot]
    have hφx1 : φ x = 1 := MonoidHom.mem_ker.mp hx
    revert hφx1
    refine QuotientGroup.induction_on x ?_
    intro e hφe1
    have hg1 : g e = 1 := by
      simpa [φ, QuotientGroup.lift_mk] using hφe1
    have heO : (e : G) ∈ OM := by
      have hq1 : q (⟨(e : G), hE_le_M e.2⟩ : M) = 1 :=
        congrArg Subtype.val hg1
      have h := (QuotientGroup.eq_one_iff (N := pPrimeCore 2 M)
        (⟨(e : G), hE_le_M e.2⟩ : M)).mp hq1
      exact (Subgroup.mem_map (f := M.subtype)).mpr
        ⟨⟨(e : G), hE_le_M e.2⟩, h, rfl⟩
    have heOE : e ∈ OE := by
      have hmem : (e : G) ∈ OE.map E.subtype :=
        hO_inter_E_le_OE (e : G) heO e.2
      rcases Subgroup.mem_map.mp hmem with ⟨y, hy, hyEq⟩
      have hy_eq : y = e := by
        apply Subtype.ext
        exact hyEq
      simpa [hy_eq] using hy
    exact (QuotientGroup.eq_one_iff (N := OE) e).mpr heOE
  have hφ_inj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hφ_ker_bot
  let eBar : E ⧸ OE ≃* Ebar := MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  exact ⟨eBar.symm.trans hA7.some⟩

/-- Odd `PSL₂(K)` is never isomorphic to `A₇`. -/
private theorem psl2_ne_a7
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty (PSL2 K ≃* alternatingGroup (Fin 7))) : False := by
  classical
  rcases e with ⟨e⟩
  let q : ℕ := Nat.card K
  have hqpos : 0 < q := Nat.card_pos
  have hKodd : Odd q := by
    dsimp [q]
    rcases hK with ⟨p, n, _hp, hpodd, _hn, hcard⟩
    rw [hcard]
    exact hpodd.pow
  have hdvd2 : 2 ∣ q * (q ^ 2 - 1) := by
    have hEven : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hKodd.pow odd_one
    exact dvd_mul_of_dvd_right hEven.two_dvd _
  have hcardPSL : Nat.card (PSL2 K) = q * (q ^ 2 - 1) / 2 :=
    by simpa [q] using psl2_card_formula K hK
  have hcardA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hEq : q * (q ^ 2 - 1) / 2 = 2520 := by
    rw [← hcardPSL]
    rw [Nat.card_congr e.toEquiv, hcardA]
  have hEq' : q * (q ^ 2 - 1) = 2 * 2520 := by
    rw [← Nat.div_eq_iff_eq_mul_right (by norm_num) hdvd2]
    exact hEq
  have hEq'' : q * (q ^ 2 - 1) = 5040 := by
    norm_num at hEq'
    exact hEq'
  have hqle : q ≤ 17 := by
    by_contra hnot
    have hge : 18 ≤ q := by omega
    have hqsq_pos : 0 < q ^ 2 := pow_pos hqpos 2
    have h1 : 1 ≤ q ^ 2 := Nat.succ_le_of_lt hqsq_pos
    have hz : (q : ℤ) * ((q : ℤ) ^ 2 - 1) = 5040 := by
      have hsq : (q : ℤ) ^ 2 = (q ^ 2 : ℕ) := by norm_num
      rw [hsq]
      have hcast : ((q ^ 2 : ℕ) : ℤ) - 1 = ((q ^ 2 - 1 : ℕ) : ℤ) :=
        (Int.ofNat_sub h1).symm
      rw [hcast]
      exact_mod_cast hEq''
    have hprod : (18 : ℤ) * (18 ^ 2 - 1) ≤
        (q : ℤ) * ((q : ℤ) ^ 2 - 1) := by
      nlinarith [sq_nonneg (q : ℤ)]
    norm_num at hprod
    omega
  interval_cases q <;> norm_num at hEq''

/-- In the A₇ layer model, the whole maximal overgroup `M` has `A₇`
quotient by its odd core. -/
public theorem firstCase_cyclic_m_quotient_a7_of_layer_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7))) :
    Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin 7)) := by
  classical
  let q : M →* M ⧸ pPrimeCore 2 M := QuotientGroup.mk' (pPrimeCore 2 M)
  let E : Subgroup G := componentLayerOf M
  let Ei : Subgroup M := E.subgroupOf M
  let Ebar : Subgroup (M ⧸ pPrimeCore 2 M) := Ei.map q
  have hD : IsDGroup (↥M) := properSubgroups_areDGroups hmin M hMmax.1
  rcases hD with ⟨_hSylow, htwo⟩ | ⟨_hSylow, hA7M⟩ |
    ⟨_hSylow, K, hK, L, hLnormal, hLindex, hLmodel⟩
  · obtain ⟨eE⟩ := firstCase_cyclic_componentLayer_image_a7_of_layer_a7 M hA7
    have hEbar2 : IsPGroup 2 Ebar := htwo.to_subgroup Ebar
    have hA72 : IsPGroup 2 (alternatingGroup (Fin 7)) := hEbar2.of_equiv eE
    rcases (IsPGroup.iff_card.mp hA72) with ⟨n, hn⟩
    have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have hthree : 3 ∣ 2 ^ n := by
      rw [← hn, hcard]
      norm_num
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
    norm_num at h32
  · exact hA7M
  · let : Field K := inferInstance
    let : Finite K := inferInstance
    obtain ⟨eE⟩ := firstCase_cyclic_componentLayer_image_a7_of_layer_a7 M hA7
    have hEbarne : Ebar ≠ ⊥ := by
      intro hbot
      have hcard1 : Nat.card Ebar = 1 := by
        rw [hbot]
        simp
      have hcardA : Nat.card Ebar = 2520 := by
        rw [Nat.card_congr eE.toEquiv, nat_card_alternatingGroup]
        norm_num
      omega
    have hEbarperf : Group.IsPerfect Ebar := by
      let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
        ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
      exact Group.IsPerfect.ofSurjective (f := eE.symm.toMonoidHom) eE.symm.surjective
    have hEbarL : Ebar ≤ L := by
      let : L.Normal := hLnormal
      let : (pPrimeCore 2 (↥M)).Normal :=
        pPrimeCore_normal (p := 2) (G := ↥M)
      let pi : (M ⧸ pPrimeCore 2 M) →* (M ⧸ pPrimeCore 2 M) ⧸ L := QuotientGroup.mk' L
      let I : Subgroup ((M ⧸ pPrimeCore 2 M) ⧸ L) := Ebar.map pi
      have hIperf : Group.IsPerfect I :=
        perfect_map_subgroup Ebar pi hEbarperf
      have hQodd : Odd (Nat.card ((M ⧸ pPrimeCore 2 M) ⧸ L)) := by
        simpa only [Subgroup.index_eq_card] using hLindex
      have hQsolv : Group.IsSolvable ((M ⧸ pPrimeCore 2 M) ⧸ L) := odd_order_theorem _ hQodd
      have hIbot : I = ⊥ := by
        by_contra hIne
        let : Group.IsSolvable ((M ⧸ pPrimeCore 2 M) ⧸ L) := hQsolv
        have hIsolv : Group.IsSolvable I := inferInstance
        let : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
        let : Group.IsPerfect I := hIperf
        exact Group.IsPerfect.not_isSolvable I hIsolv
      have hker : Ebar ≤ pi.ker := (Subgroup.map_eq_bot_iff Ebar).mp hIbot
      simpa [pi, QuotientGroup.ker_mk'] using hker
    let EL : Subgroup L := Ebar.subgroupOf L
    have hELne : EL ≠ ⊥ := by
      intro hbot
      apply hEbarne
      have hmap : EL.map L.subtype = Ebar :=
        Subgroup.map_subgroupOf_eq_of_le hEbarL
      rw [hbot, Subgroup.map_bot] at hmap
      exact hmap.symm
    have hELperf : Group.IsPerfect EL := by
      let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
      exact Group.IsPerfect.ofSurjective (f := eEL.symm.toMonoidHom) eEL.symm.surjective
    have hEbar_normal : Ebar.Normal := by
      let : (pPrimeCore 2 (↥M)).Normal :=
        pPrimeCore_normal (p := 2) (G := ↥M)
      have hEi_normal : Ei.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := E)
          (by
            intro m hm
            rw [Subgroup.mem_normalizer_iff]
            intro x
            constructor
            · intro hx
              exact (componentLayerOf_isNormalIn M).2 m hm x hx
            · intro hx
              have hm' : m⁻¹ ∈ M := M.inv_mem hm
              have hback : m⁻¹ * (m * x * m⁻¹) * m ∈ E :=
                by simpa using (componentLayerOf_isNormalIn M).2 m⁻¹ hm' (m * x * m⁻¹) hx
              simpa [mul_assoc] using hback)
      have : Ei.Normal := hEi_normal
      exact QuotientGroup.map_normal (G := M) (pPrimeCore 2 M) Ei
    have hELsn : EL.IsSubnormal := hEbar_normal.isSubnormal.subgroupOf
    rcases hLmodel with hPSL | hPGL
    · rcases hPSL with ⟨e⟩
      let J : Subgroup (PSL2 K) := EL.map e.toMonoidHom
      have hJne : J ≠ ⊥ := by
        apply (Subgroup.map_eq_bot_iff_of_injective
          (H := EL) (f := e.toMonoidHom) e.injective).not.mpr
        exact hELne
      have hJperf : Group.IsPerfect J := perfect_map_subgroup EL e.toMonoidHom hELperf
      have hJsn : J.IsSubnormal := hELsn.map e.surjective
      have hJtop := psl2_perfect_subnormal_eq_top K hK J hJne hJperf hJsn
      have hELtop : EL = ⊤ := by
        have hmap : (EL.map e.toMonoidHom) = ⊤ := by
          have hJ : J = ⊤ := hJtop.2
          simpa [J] using hJ
        apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
        simpa [J] using hmap
      have hEbarLtop : Ebar = L := by
        apply le_antisymm hEbarL
        intro x hxL
        have hxEL : (⟨x, hxL⟩ : L) ∈ EL := by
          rw [hELtop]
          trivial
        exact Subgroup.mem_subgroupOf.mp hxEL
      have hL_Ebar : L ≃* Ebar := by
        exact (Subgroup.topEquiv (G := L)).symm.trans
          ((MulEquiv.subgroupCongr hELtop.symm).trans
            (Subgroup.subgroupOfEquivOfLe hEbarL))
      have hPSLA7 : Nonempty (PSL2 K ≃* alternatingGroup (Fin 7)) := by
        refine ⟨(e.symm.trans hL_Ebar).trans eE⟩
      exact False.elim (psl2_ne_a7 hK hPSLA7)
    · rcases hPGL with ⟨e⟩
      let : Finite (PGL2 K) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk
          Matrix.ProjGenLinGroup.mk_surjective
      let J : Subgroup (PGL2 K) := EL.map e.toMonoidHom
      have hJne : J ≠ ⊥ := by
        apply (Subgroup.map_eq_bot_iff_of_injective
          (H := EL) (f := e.toMonoidHom) e.injective).not.mpr
        exact hELne
      have hJperf : Group.IsPerfect J := perfect_map_subgroup EL e.toMonoidHom hELperf
      have hJsn : J.IsSubnormal := hELsn.map e.surjective
      have hJcomm := pgl2_perfect_subnormal_eq_commutator K hK J hJne hJperf hJsn
      let eJ : J ≃* PSL2 K :=
        (MulEquiv.subgroupCongr hJcomm.2).trans
          (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
            K hK hJcomm.1 (MulEquiv.refl (PGL2 K))).some
      have hELJ : EL ≃* J := Subgroup.equivMapOfInjective EL e.toMonoidHom e.injective
      have hEbar_PSL : Ebar ≃* PSL2 K := by
        exact (Subgroup.subgroupOfEquivOfLe hEbarL).symm.trans
          (hELJ.trans eJ)
      have hPSLA7 : Nonempty (PSL2 K ≃* alternatingGroup (Fin 7)) := by
        refine ⟨hEbar_PSL.symm.trans eE⟩
      exact False.elim (psl2_ne_a7 hK hPSLA7)

/-- The odd core of the component layer is central in the layer. -/
public theorem firstCase_cyclic_layer_oddCore_le_center
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} (hMmax : IsCoatom M) :
    (pPrimeCore 2 (↥(componentLayerOf M))).map
        (componentLayerOf M).subtype ≤
      (Subgroup.center (↥(componentLayerOf M))).map
        (componentLayerOf M).subtype := by
  classical
  let E : Subgroup G := componentLayerOf M
  let O : Subgroup (↥E) := pPrimeCore 2 (↥E)
  let Omap : Subgroup G := O.map E.subtype
  have hOmap_le_E : Omap ≤ E := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨o, _ho, rfl⟩
    exact o.2
  have hE_le_M : E ≤ M := (componentLayerOf_isNormalIn M).1
  have hOmap_le_M : Omap ≤ M := hOmap_le_E.trans hE_le_M
  have hOmap_odd : Odd (Nat.card Omap) := by
    have hcop : Nat.Coprime 2 (Nat.card Omap) := by
      have hcard : Nat.card Omap = Nat.card O :=
        Subgroup.card_map_of_injective E.subtype_injective
      rw [hcard]
      exact pPrimeCore_coprime_card (p := 2) (G := ↥E)
    exact Nat.coprime_two_left.mp hcop
  have hOmap_solv : Group.IsSolvable Omap := odd_order_theorem Omap hOmap_odd
  have hE_norm_Omap : E ≤ Subgroup.normalizer (Omap : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨o, ho, rfl⟩
      have hconj : (⟨e, he⟩ : E) * o * (⟨e, he⟩ : E)⁻¹ ∈ O :=
        (inferInstance : O.Normal).conj_mem o ho (⟨e, he⟩ : E)
      exact Subgroup.mem_map.mpr
        ⟨(⟨e, he⟩ : E) * o * (⟨e, he⟩ : E)⁻¹, hconj, by
          change e * (o : G) * e⁻¹ = e * (o : G) * e⁻¹
          rfl⟩
    · intro hx
      have he' : e⁻¹ ∈ E := E.inv_mem he
      rcases Subgroup.mem_map.mp hx with ⟨o, ho, heq⟩
      have hback : e⁻¹ * (o : G) * e ∈ Omap := by
        refine Subgroup.mem_map.mpr
          ⟨(⟨e⁻¹, he'⟩ : E) * o * (⟨e⁻¹, he'⟩ : E)⁻¹, ?_, ?_⟩
        · exact (inferInstance : O.Normal).conj_mem o ho (⟨e⁻¹, he'⟩ : E)
        · simp
      have hx_eq : x = e⁻¹ * (o : G) * e := by
        calc
          x = e⁻¹ * (e * x * e⁻¹) * e := by group
          _ = e⁻¹ * (E.subtype o) * e := by rw [heq]
      rw [← hx_eq] at hback
      exact hback
  have hcomm := componentLayerOf_centralizes_solvable_of_le_normalizer
    M Omap hOmap_le_M hOmap_solv hE_norm_Omap
  have hE_cent : E ≤ Subgroup.centralizer (Omap : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := E) (H₂ := Omap)).mp hcomm
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨o, ho, rfl⟩
  refine Subgroup.mem_map.mpr ⟨o, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  have hyE : (y : G) ∈ E := by simpa [E] using y.2
  have hycent := (Subgroup.mem_centralizer_iff.mp
    (hE_cent hyE)) o
    (Subgroup.mem_map.mpr ⟨o, ho, rfl⟩)
  exact Subtype.ext hycent.symm

/-- A nontrivial odd subgroup of the component layer cannot lie in the odd
core of the layer: the odd core is central in the layer (hence in the
centralizer of every involution of the layer), while the subgroup is inverted
by that involution. -/
private theorem firstCase_cyclic_layer_oddCore_meets_inverted_no
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    {M X : Subgroup G} (hMmax : IsCoatom M)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hXleL : X ≤ componentLayerOf M) (hXne : X ≠ ⊥)
    (hXp : IsPGroup od.p X)
    (hXinv : BenderGlauberman.IsInvertedBy od.d.bg.t2 X)
    (hXleO : X ≤ (pPrimeCore 2 (↥(componentLayerOf M))).map
      (componentLayerOf M).subtype) :
    False := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let L : Subgroup G := componentLayerOf M
  let O : Subgroup (↥L) := pPrimeCore 2 (↥L)
  let Omap : Subgroup G := O.map L.subtype
  have ht2L : od.d.bg.t2 ∈ L := hV2 fd.t2_mem_V2
  have hXcent : X ≤ Subgroup.centralizer ({od.d.bg.t2} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxO : x ∈ Omap := hXleO hx
    have hxcenter : x ∈ (Subgroup.center (↥L)).map L.subtype :=
      firstCase_cyclic_layer_oddCore_le_center hMmax hxO
    rcases Subgroup.mem_map.mp hxcenter with ⟨c, hc_center, hceq⟩
    have hceq' : (c : G) = x := by simpa [L] using hceq
    let t2L : L := ⟨od.d.bg.t2, ht2L⟩
    have hcomm : t2L * c = c * t2L :=
      (Subgroup.mem_center_iff.mp hc_center t2L)
    have hcommG : (od.d.bg.t2 : G) * (c : G) = (c : G) * od.d.bg.t2 := by
      simpa [t2L] using congrArg Subtype.val hcomm
    calc
      x * od.d.bg.t2 = (c : G) * od.d.bg.t2 := by rw [hceq']
      _ = od.d.bg.t2 * (c : G) := hcommG.symm
      _ = od.d.bg.t2 * x := by rw [hceq']
  have hpodd : Odd od.p :=
    (Fact.out : Nat.Prime od.p).odd_of_ne_two (firstCase_oriented_p_odd c od)
  exact no_nontrivial_oddP_inverted_centralized od.d.bg.t2 X
    hXinv hXcent hXp hpodd hXne

/-- The inverted odd subgroup of the component layer is disjoint from the
odd core of the layer.  This is the finite interface behind the later
quotient arguments: the image of the subgroup in `E / O(E)` is nontrivial. -/
public theorem firstCase_cyclic_layer_inverted_inf_oddCore_eq_bot
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    {M X : Subgroup G} (hMmax : IsCoatom M)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hXleL : X ≤ componentLayerOf M) (hXne : X ≠ ⊥)
    (hXp : IsPGroup od.p X)
    (hXinv : BenderGlauberman.IsInvertedBy od.d.bg.t2 X) :
    X ⊓ ((pPrimeCore 2 (↥(componentLayerOf M))).map
      (componentLayerOf M).subtype) = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let L : Subgroup G := componentLayerOf M
  let O : Subgroup (↥L) := pPrimeCore 2 (↥L)
  let Omap : Subgroup G := O.map L.subtype
  apply le_bot_iff.mp
  intro x hx
  let Y : Subgroup G := Subgroup.zpowers x
  have hxX : x ∈ X := (Subgroup.mem_inf.mp hx).1
  have hxO : x ∈ Omap := (Subgroup.mem_inf.mp hx).2
  have hYleL : Y ≤ L := by
    exact Subgroup.zpowers_le.mpr (hXleL hxX)
  have hYleO : Y ≤ Omap := Subgroup.zpowers_le.mpr hxO
  have hYp : IsPGroup od.p Y := hXp.to_le (Subgroup.zpowers_le.mpr hxX)
  have hYinv : BenderGlauberman.IsInvertedBy od.d.bg.t2 Y := by
    exact inverted_zpowers_of_generator_inverted (hXinv x hxX)
  by_cases hx1 : x = 1
  · rw [Subgroup.mem_bot]
    exact hx1
  · have hYne : Y ≠ ⊥ := by
      intro hbot
      have hxY : x ∈ Y := Subgroup.mem_zpowers x
      have hxbot : x ∈ (⊥ : Subgroup G) := by simpa [hbot] using hxY
      exact hx1 (Subgroup.mem_bot.mp hxbot)
    exact False.elim (firstCase_cyclic_layer_oddCore_meets_inverted_no
      od fd hMmax hV2 hYleL hYne hYp hYinv hYleO)

/-- The image of the inverted odd subgroup in `componentLayerOf M` modulo
its odd core is nontrivial. -/
public theorem firstCase_cyclic_layer_inverted_quotient_ne_bot
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    {M X : Subgroup G} (hMmax : IsCoatom M)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hXleL : X ≤ componentLayerOf M) (hXne : X ≠ ⊥)
    (hXp : IsPGroup od.p X)
    (hXinv : BenderGlauberman.IsInvertedBy od.d.bg.t2 X) :
    ((X.subgroupOf (componentLayerOf M)).map
      (QuotientGroup.mk' (pPrimeCore 2 (↥(componentLayerOf M)))) ≠ ⊥) := by
  classical
  let L : Subgroup G := componentLayerOf M
  let O : Subgroup (↥L) := pPrimeCore 2 (↥L)
  let : O.Normal := by dsimp [O]; infer_instance
  let q : L →* L ⧸ O := QuotientGroup.mk' O
  let XL : Subgroup L := X.subgroupOf L
  let Xbar : Subgroup (L ⧸ O) := XL.map q
  intro hbot
  have hker : q.ker = O := QuotientGroup.ker_mk' O
  have hXLleO : XL ≤ O := by
    have hle : XL ≤ q.ker := (Subgroup.map_eq_bot_iff (H := XL) (f := q)).mp
      (by simpa [XL, Xbar, q] using hbot)
    simpa [hker] using hle
  have hXleOmap : X ≤ ((pPrimeCore 2 (↥L)).map L.subtype) := by
    intro x hx
    have hxL : x ∈ L := hXleL hx
    have hxXL : (⟨x, hxL⟩ : L) ∈ XL := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hXLleO hxXL, rfl⟩
  have hcapbot := firstCase_cyclic_layer_inverted_inf_oddCore_eq_bot
    od fd hMmax hV2 hXleL hXne hXp hXinv
  have hXbot : X = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxinf : x ∈ X ⊓ ((pPrimeCore 2 (↥L)).map L.subtype) :=
      Subgroup.mem_inf.mpr ⟨hx, hXleOmap hx⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [hcapbot] at hxinf
      exact hxinf
    exact Subgroup.mem_bot.mp hxbot
  exact hXne hXbot

/-- In the A₇ layer model, the oriented prime of the cyclic first case is
necessarily `3`. -/
public theorem firstCase_cyclic_oriented_prime_eq_three_of_aSeven_layer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    (M X : Subgroup G) (hMmax : IsCoatom M)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hXleL : X ≤ componentLayerOf M) (hXne : X ≠ ⊥)
    (hXp : IsPGroup od.p X)
    (hXinv : BenderGlauberman.IsInvertedBy od.d.bg.t2 X)
    (hXleC : X ≤ Subgroup.centralizer (fd.V1 : Set G))
    (hA7 : Nonempty
      ((componentLayerOf M) ⧸ pPrimeCore 2 (componentLayerOf M) ≃*
        alternatingGroup (Fin 7))) :
    od.p = 3 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let L : Subgroup G := componentLayerOf M
  let O : Subgroup (↥L) := pPrimeCore 2 (↥L)
  let q : L →* (L ⧸ O) := QuotientGroup.mk' O
  let XL : Subgroup (↥L) := X.subgroupOf L
  let Xbar : Subgroup (L ⧸ O) := XL.map q
  have hXbarp : IsPGroup od.p Xbar := by
    have hXLp : IsPGroup od.p XL :=
      hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXleL).symm
    exact IsPGroup.map hXLp q
  have hXbarne : Xbar ≠ ⊥ := by
    exact firstCase_cyclic_layer_inverted_quotient_ne_bot
      od fd hMmax hV2 hXleL hXne hXp hXinv
  have htL : c.t ∈ L := hV2 fd.t_mem_V2
  let tL : L := ⟨c.t, htL⟩
  let tbar : L ⧸ O := q tL
  have htbar : IsInvolution tbar := by
    constructor
    · intro htbar1
      have htL_O : tL ∈ O :=
        (QuotientGroup.eq_one_iff (N := O) tL).mp htbar1
      have hord2 : orderOf tL = 2 := by
        apply orderOf_eq_prime
        · exact Subtype.ext (by simpa [pow_two] using c.t_involution.2)
        · intro htL1
          apply c.t_involution.1
          exact Subtype.ext_iff.mp htL1
      have h2dvd : 2 ∣ Nat.card O := by
        rw [← hord2]
        exact Subgroup.orderOf_dvd_natCard O htL_O
      have hOodd : Odd (Nat.card O) :=
        Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥L))
      exact hOodd.not_two_dvd_nat h2dvd
    · have ht2 : tL ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using c.t_involution.2
      change (q tL) ^ 2 = 1
      rw [← map_pow q tL 2, ← map_one q]
      exact congrArg q ht2
  have hXbarcent : Xbar ≤ Subgroup.centralizer ({tbar} : Set (L ⧸ O)) := by
    intro xbar hxbar
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hxbar with ⟨xL, hxXL, rfl⟩
    have hxX : (xL : G) ∈ X := Subgroup.mem_subgroupOf.mp hxXL
    have hxcent : c.t * (xL : G) = (xL : G) * c.t := by
      have hxcentV : (xL : G) ∈ Subgroup.centralizer (fd.V1 : Set G) := hXleC hxX
      exact (Subgroup.mem_centralizer_iff.mp hxcentV) c.t fd.t_mem_V1
    have hconj : c.t * (xL : G) * c.t⁻¹ = (xL : G) := by
      rw [hxcent]
      group
    have hqconj : q xL * tbar = tbar * q xL := by
      have hq : q (tL * xL * tL⁻¹) = q xL := by
        apply congrArg q
        apply Subtype.ext
        change c.t * (xL : G) * c.t⁻¹ = (xL : G)
        exact hconj
      have hqconj' : q tL * q xL * (q tL)⁻¹ = q xL := by
        simpa [map_mul, map_inv] using hq
      have hXeq : q xL = q tL * q xL * (q tL)⁻¹ := hqconj'.symm
      calc
        q xL * q tL = (q tL * q xL * (q tL)⁻¹) * q tL := by
          conv_lhs => rw [hXeq]
        _ = q tL * q xL := by group
    exact hqconj
  let e : L ⧸ O ≃* alternatingGroup (Fin 7) := hA7.some
  let XA : Subgroup (alternatingGroup (Fin 7)) := Xbar.map e.toMonoidHom
  let tA : alternatingGroup (Fin 7) := e tbar
  have hXAp : IsPGroup od.p XA := IsPGroup.map hXbarp e.toMonoidHom
  have hXAne : XA ≠ ⊥ := by
    intro hbot
    apply hXbarne
    apply (Subgroup.map_eq_bot_iff_of_injective
      (H := Xbar) (f := e.toMonoidHom) e.injective).mp
    simpa [XA] using hbot
  have htA : IsInvolution tA := by
    constructor
    · intro htA1
      apply htbar.1
      apply e.injective
      simpa [tA] using htA1
    · have h := congrArg e htbar.2
      simpa [tA, pow_two] using h
  have hXAcent : XA ≤
      Subgroup.centralizer ({tA} : Set (alternatingGroup (Fin 7))) := by
    intro xA hxA
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hxA with ⟨xbar, hxbar, rfl⟩
    have hxcomm : xbar * tbar = tbar * xbar :=
      Subgroup.mem_centralizer_singleton_iff.mp (hXbarcent hxbar)
    simpa [tA, map_mul] using congrArg e hxcomm
  let hA7contra : (od.p = 5 ∨ od.p = 7) → False := fun h57 =>
    aSeven_no_involution_centralizes_oddP_five_seven
      (p := od.p) (hp := od.p_prime) (hp57 := h57) (P := XA)
      (hPp := hXAp) (hPne := hXAne) (t := tA) (ht := htA)
      (hPcent := hXAcent)
  by_cases hp3 : od.p = 3
  · exact hp3
  · have hpodd : Odd od.p :=
      (Fact.out : Nat.Prime od.p).odd_of_ne_two (firstCase_oriented_p_odd c od)
    have hpdvdQ : od.p ∣ Nat.card (L ⧸ O) := by
      have hdivX : Nat.card Xbar ∣ Nat.card (L ⧸ O) :=
        Subgroup.card_subgroup_dvd_card Xbar
      have hpdvdX : od.p ∣ Nat.card Xbar := by
        rcases (IsPGroup.iff_card.mp hXbarp) with ⟨n, hn⟩
        have hnpos : n ≠ 0 := by
          intro h0
          apply hXbarne
          rw [Subgroup.eq_bot_iff_card]
          rw [hn, h0]
          norm_num
        rw [hn]
        exact dvd_pow_self od.p hnpos
      exact hpdvdX.trans hdivX
    have hcardQ : Nat.card (L ⧸ O) = Nat.card (alternatingGroup (Fin 7)) :=
      Nat.card_congr hA7.some.toEquiv
    have hpdvd2520 : od.p ∣ 2520 := by
      have hcard2520 : Nat.card (L ⧸ O) = 2520 := by
        rw [hcardQ, nat_card_alternatingGroup]
        norm_num
      rwa [hcard2520] at hpdvdQ
    have h357 := GorensteinWalter.odd_prime_eq_three_five_or_seven_of_dvd_2520
      od.p_prime hpodd hpdvd2520
    rcases h357 with h3 | h5 | h7
    · exact False.elim (hp3 h3)
    · have h57 : od.p = 5 ∨ od.p = 7 := Or.inl h5
      exact False.elim (hA7contra h57)
    · have h57 : od.p = 5 ∨ od.p = 7 := Or.inr h7
      exact False.elim (hA7contra h57)

/-- In the cyclic subcase, the selected odd `p`-core `P = O_p(U)`
centralizes the Klein-four subgroup `V₁`. -/
public theorem firstCase_cyclic_P_le_centralizer_V1
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d) :
    qCoreOf od.d.bg.U od.p ≤ Subgroup.centralizer (fd.V1 : Set G) :=
  firstCase_P_le_centralizer_V1 c od fd

/-- The source Sylow `P₂` lies inside `B = C_U(S)`. -/
public theorem firstCase_cyclic_P2_le_B
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    ∀ x : G,
      x ∈ sylowCarrier (firstCase_P2_sylow c od hU Q) → x ∈ od.d.bg.B := by
  intro x hx
  rw [firstCase_P2_carrier c od hU Q] at hx
  rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
  exact b.2

/-- In the cyclic subcase the common centralizer `B = C_U(S)` is nontrivial. -/
public theorem firstCase_cyclic_B_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    od.d.bg.B ≠ ⊥ := by
  intro hBbot
  have hP2bot : sylowCarrier (firstCase_P2_sylow c od hU Q) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxB : x ∈ od.d.bg.B := firstCase_cyclic_P2_le_B c od hU Q x hx
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rwa [hBbot] at hxB
    exact Subgroup.mem_bot.mp hxbot
  exact (firstCase_P2_ne_one hmin c od hfirst hHhat hU Q) hP2bot

/-- The common centralizer `B = C_U(S)` has odd order. -/
public theorem firstCase_cyclic_B_odd
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B) :
    Odd (Nat.card (↥od.d.bg.B)) := by
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2
      (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hBleU : od.d.bg.B ≤ c.U := by
    intro x hx
    have hxB1 : x ∈ od.d.bg.B1 := by
      have hx' : x ∈ od.d.bg.B1 ⊓ od.d.bg.B2 := by
        simpa [BenderGlauberman.Hyp11.B] using hx
      exact hx'.1
    have hxU : x ∈ od.d.bg.U :=
      (Subgroup.mem_inf.mp (by
        simpa [BenderGlauberman.Hyp11.B1, centralizerIn] using hxB1)).1
    have hUeq : od.d.bg.U = c.U := (firstCase_U_eq_bg_U c od.d).symm
    simpa [hUeq] using hxU
  exact Nat.coprime_two_left.mp
    (hUodd.coprime_dvd_right (Subgroup.card_dvd_of_le hBleU))

/-- In the cyclic subcase `B` is odd-order and nontrivial, hence not
perfect; equivalently `[B,B] ≠ B`, the `hB'` input for Theorem C. -/
public theorem firstCase_cyclic_B_not_perfect
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    ⁅od.d.bg.B, od.d.bg.B⁆ ≠ od.d.bg.B := by
  have hBne := firstCase_cyclic_B_ne_bot hmin c od hfirst hHhat hU Q
  have hBodd := firstCase_cyclic_B_odd c od hU
  let : Group.IsSolvable od.d.bg.B := odd_order_theorem od.d.bg.B hBodd
  let : Nontrivial (↥od.d.bg.B) :=
    (Subgroup.nontrivial_iff_ne_bot od.d.bg.B).mpr hBne
  intro hperfect
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := od.d.bg.B)
  apply hlt.ne
  apply (Subgroup.map_subtype_inj (H := od.d.bg.B)).mp
  rw [Subgroup.map_subtype_commutator, hperfect]
  simpa [MonoidHom.range_eq_map] using
    (Subgroup.range_subtype (H := od.d.bg.B)).symm

/-- In the first-case setup, any odd subgroup of `H` centralizing the
Sylow subgroup `S` lies in `B = C_U(S)`. -/
private theorem firstCase_cyclic_oddCore_le_B
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (d : FirstCaseBGData c)
    (O : Subgroup G)
    (hOleH : O ≤ d.bg.H)
    (hOodd : Odd (Nat.card O))
    (hOcentS : O ≤ Subgroup.centralizer ((d.bg.S : Subgroup G) : Set G)) :
    O ≤ d.bg.B := by
  classical
  let : Fintype G := Fintype.ofFinite G
  exact oddCore_le_centralizer_U_of_H_eq_US
    d.bg.U d.bg.S d.bg.H d.bg.B O
    d.bg.H_eq_US (bg_U_normal_in_H d.bg) d.bg.S.isPGroup'
    (BenderGlauberman.S_le_H d.bg)
    (B_eq_centralizer_U d.bg) hOleH hOodd hOcentS

/-- In the A₇ model for a maximal overgroup `M`, the intersection
`B ∩ M` lies in the odd core of `M`, provided a Sylow element of `S`
maps to the concrete `(4,2)`-element `a7rho` under the quotient
isomorphism. -/
public theorem firstCase_cyclic_B_inter_M_le_oddCore_of_a7model
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (M : Subgroup G)
    (hSM : (c.S : Subgroup G) ≤ M)
    (e : Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin 7)))
    (Sbar : Sylow 2 (alternatingGroup (Fin 7)))
    (hSbar : ((c.S : Subgroup G).subgroupOf M).map
      (e.some.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 M))) =
        (Sbar : Subgroup (alternatingGroup (Fin 7)))) :
    (od.d.bg.B ⊓ M) ≤
      ((pPrimeCore 2 M).map M.subtype) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : (pPrimeCore 2 M).Normal := pPrimeCore_normal
  let O : Subgroup (↥M) := pPrimeCore 2 M
  let q : M →* (M ⧸ O) := QuotientGroup.mk' O
  let f : M →* alternatingGroup (Fin 7) := e.some.toMonoidHom.comp q
  let B0 : Subgroup M := (od.d.bg.B ⊓ M).subgroupOf M
  let S0 : Subgroup M := (c.S : Subgroup G).subgroupOf M
  have hBodd : Odd (Nat.card (↥od.d.bg.B)) := firstCase_cyclic_B_odd c od hU
  have hB0odd : Odd (Nat.card B0) := by
    have hB0card : Nat.card B0 =
        Nat.card (od.d.bg.B ⊓ M : Subgroup G) := by
      simpa [B0] using (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := od.d.bg.B ⊓ M) (K := M)
          inf_le_right).toEquiv)
    have hdvd : Nat.card B0 ∣ Nat.card (od.d.bg.B ⊓ M : Subgroup G) :=
      by rw [hB0card]
    have hBintodd : Odd (Nat.card (od.d.bg.B ⊓ M : Subgroup G)) :=
      Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_left)
    exact Odd.of_dvd_nat hBintodd hdvd
  have hBleC : od.d.bg.B ≤
      Subgroup.centralizer ((c.S : Subgroup G) : Set G) := by
    have h := (B_eq_centralizer_U od.d.bg)
    rw [h]
    simpa [od.d.S_eq] using inf_le_right
  have hB0centS : B0 ≤ Subgroup.centralizer (S0 : Set M) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Subtype.ext
    have hbBM : (b : G) ∈ od.d.bg.B ⊓ M := Subgroup.mem_subgroupOf.mp hb
    have hbB : (b : G) ∈ od.d.bg.B := (Subgroup.mem_inf.mp hbBM).1
    have hsS : (s : G) ∈ (c.S : Subgroup G) := Subgroup.mem_subgroupOf.mp hs
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hBleC hbB)) (s : G) hsS
    change (s : G) * (b : G) = (b : G) * (s : G)
    exact hcomm
  have hker : B0 ≤ f.ker :=
    a7rho_centralizer_odd_trivial_of_sylow_image f B0 S0
      hB0odd hB0centS Sbar hSbar
  intro x hx
  have hxM : x ∈ M := (Subgroup.mem_inf.mp hx).2
  let xM : M := ⟨x, hxM⟩
  have hxB0 : xM ∈ B0 := Subgroup.mem_subgroupOf.mpr hx
  have hkerx : f xM = 1 := (MonoidHom.mem_ker).mp (hker hxB0)
  have hq1 : q xM = 1 := by
    have hfx : e.some (q xM) = 1 := by
      simpa [f, MonoidHom.comp_apply] using hkerx
    exact e.some.injective (by simpa using hfx)
  have hxO : xM ∈ O := (QuotientGroup.eq_one_iff (N := O) xM).mp hq1
  exact Subgroup.mem_map.mpr ⟨xM, hxO, rfl⟩

/-- In the cyclic first case, the odd core `U = O(H)` is the product
`F(U) · B` with `B = C_U(S)`. -/
public theorem firstCase_cyclic_U_eq_FU_sup_B
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (od : FirstCaseOrientedPrimeData c) :
    od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B := by
  classical
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hFU : fittingSubgroupOf c.U = fittingSubgroupOf od.d.bg.U :=
    congrArg fittingSubgroupOf hUeq
  have hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s := by
    intro s hs
    rcases hfirst.1 s hs with ⟨I, hI, _⟩
    exact ⟨I, hI⟩
  have hcomm : ⁅(od.d.bg.S : Subgroup G), od.d.bg.U⁆ ≤
      fittingSubgroupOf od.d.bg.U := by
    have h := lemma_2_8_commutator_le_FU c hinverted
    simpa [CentralizerSetup.FU, od.d.S_eq, hUeq, hFU] using h
  simpa [od.d.S_eq] using firstCase_U_eq_FU_sup_B od.d.bg hcomm

/-- The final Theorem-C assembly, waiting only for the A₇-model
identities. -/
public theorem firstCase_cyclicTwoCore_impossible_of_a7model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (od : FirstCaseOrientedPrimeData c)
    (hU0 : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (hAeq : od.d.bg.B1 ⊓
      @BenderGlauberman.Hyp11.K2 G _ _ od.d.bg
        (firstCaseBGKData hmin c od.d) = qCoreOf od.d.bg.U 3)
    (hKeq : @BenderGlauberman.Hyp11.K G _ _ od.d.bg
        (firstCaseBGKData hmin c od.d) =
      ((pPrimeCore 3 (fittingSubgroup od.d.bg.U)).map
        (fittingSubgroup od.d.bg.U).subtype).map od.d.bg.U.subtype)
    (hPcentB : qCoreOf od.d.bg.U 3 ≤ Subgroup.centralizer
      (od.d.bg.B : Set G))
    (hKne : @BenderGlauberman.Hyp11.K G _ _ od.d.bg
        (firstCaseBGKData hmin c od.d) ≠ ⊥)
    (hBfpf : ∀ b : G, b ∈ od.d.bg.B → b ≠ 1 → ∀ k : G,
      k ∈ ((pPrimeCore 3 (fittingSubgroup od.d.bg.U)).map
        (fittingSubgroup od.d.bg.U).subtype).map od.d.bg.U.subtype →
        k ≠ 1 → b * k * b⁻¹ ≠ k) :
    False := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData od.d.bg :=
    firstCaseBGKData hmin c od.d
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  let Q : Sylow od.p (↥od.d.bg.B) := Classical.choice Sylow.nonempty
  have hinputs := firstCase_cyclic_theoremC_inputs_of_a7model
    hmin c od.d hU0 hAeq hKeq hPcentB hKne hBfpf
  have hU := hinputs.1
  have hUint := firstCase_cyclic_A_inter_BK_eq_bot hmin c od.d
  have hUcomm := hinputs.2.1
  have hcop := firstCase_cyclic_K_card_coprime_H_index
    hmin c hfirst hcyclic od.d
  have hB' := firstCase_cyclic_B_not_perfect
    hmin c od hfirst hHhat hU0 Q
  have hFrob := hinputs.2.2
  have hns : ¬ IsSimpleGroup G :=
    BenderGlauberman.theorem_C od.d.bg hU hUint hUcomm hcop hB' hFrob
  exact hns (minimalCounterexample_isSimple hmin)

/-- Full inverted-odd data for the cyclic component layer: the maximal
subgroup, the klein-four data, and a nontrivial odd subgroup inside
`componentLayerOf M` inverted by `t₂` and centralized by `V₁`. -/
public theorem firstCase_cyclic_layer_inverted_data_of_od
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (od : FirstCaseOrientedPrimeData c) :
    ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
      ∃ fd : FirstCaseFourData c od.d,
        ∃ Q : Sylow od.p ↥od.d.bg.B,
          ∃ M : Subgroup G, ∃ X : Subgroup G,
            IsCoatom M ∧
              Subgroup.normalizer
                (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                (c.S : Subgroup G) ≤ M ∧
                  fd.V2 ≤ componentLayerOf M ∧
                    X ≤ componentLayerOf M ∧ X ≠ ⊥ ∧ IsCyclic X ∧
                      IsPGroup od.p X ∧
                      X ≤ qCoreOf od.d.bg.U od.p ∧
                      BenderGlauberman.IsInvertedBy od.d.bg.t2 X ∧
                        X ≤ Subgroup.centralizer (fd.V1 : Set G) := by
  classical
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  obtain ⟨hU, fd, Q, M, hMmax, hMN, hSM, hV⟩ :=
    firstCase_cyclic_V2_le_componentLayer_of_od hmin c hfirst hcyclic od
  have hD : IsDGroup (↥M) := properSubgroups_areDGroups hmin M hMmax.1
  have hV' := firstCase_V2_le_componentLayer_of_DGroup
    hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM hD
  obtain ⟨X, hXleE, hXne, hXcyc, hXp, hXleP, hXinv, hXleC⟩ :=
    firstCase_cyclic_inverted_component_odd
      hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM hV'
  exact ⟨hU, fd, Q, M, X, hMmax, hMN, hSM, hV', hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXleC⟩

/-- Full inverted-odd data for the cyclic component layer: the maximal
subgroup, the klein-four data, and a nontrivial odd subgroup inside
`componentLayerOf M` inverted by `t₂` and centralized by `V₁`. -/
public theorem firstCase_cyclic_layer_inverted_data
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ od : FirstCaseOrientedPrimeData c,
      ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
        ∃ fd : FirstCaseFourData c od.d,
          ∃ Q : Sylow od.p ↥od.d.bg.B,
            ∃ M : Subgroup G, ∃ X : Subgroup G,
              IsCoatom M ∧
                Subgroup.normalizer
                  (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                  (c.S : Subgroup G) ≤ M ∧
                    fd.V2 ≤ componentLayerOf M ∧
                      X ≤ componentLayerOf M ∧ X ≠ ⊥ ∧ IsCyclic X ∧
                        IsPGroup od.p X ∧
                        X ≤ qCoreOf od.d.bg.U od.p ∧
                        BenderGlauberman.IsInvertedBy od.d.bg.t2 X ∧
                          X ≤ Subgroup.centralizer (fd.V1 : Set G) := by
  classical
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  obtain ⟨od⟩ := exists_firstCaseOrientedPrimeData hmin c hfirst hHhat
  obtain ⟨hU, fd, Q, M, X, hMmax, hMN, hSM, hV, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXleC⟩ :=
    firstCase_cyclic_layer_inverted_data_of_od hmin c hfirst hcyclic od
  exact ⟨od, hU, fd, Q, M, X, hMmax, hMN, hSM, hV, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXleC⟩

/-- In the cyclic subcase the selected odd core `P = O_p(U)` meets the
component layer nontrivially. -/
public theorem firstCase_cyclic_P_inter_E_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ od : FirstCaseOrientedPrimeData c, ∃ M : Subgroup G,
      IsCoatom M ∧
        qCoreOf od.d.bg.U od.p ⊓ componentLayerOf M ≠ ⊥ := by
  classical
  obtain ⟨od, _hU, _fd, _Q, M, X, hMmax, _hMN, _hSM, _hV2,
    hXleE, hXne, _hXcyc, _hXp, hXleP, _hXinv, _hXleC⟩ :=
    firstCase_cyclic_layer_inverted_data hmin c hfirst hcyclic
  refine ⟨od, M, hMmax, ?_⟩
  intro hbot
  have hXbot : X = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxP : x ∈ qCoreOf od.d.bg.U od.p := hXleP hx
    have hxE : x ∈ componentLayerOf M := hXleE hx
    have hxinf : x ∈ qCoreOf od.d.bg.U od.p ⊓ componentLayerOf M :=
      Subgroup.mem_inf.mpr ⟨hxP, hxE⟩
    rw [hbot] at hxinf
    exact Subgroup.mem_bot.mp hxinf
  exact hXne hXbot

/-- Combine the inverted odd input with the `D`-group structure of the
component layer for the linear eliminiation. -/
public theorem firstCase_cyclic_layer_inverted_and_DGroup_of_od
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (od : FirstCaseOrientedPrimeData c) :
    ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
        ∃ fd : FirstCaseFourData c od.d,
          ∃ Q : Sylow od.p ↥od.d.bg.B,
            ∃ M : Subgroup G, ∃ X : Subgroup G,
              IsCoatom M ∧
                Subgroup.normalizer
                  (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                  (c.S : Subgroup G) ≤ M ∧
                    fd.V2 ≤ componentLayerOf M ∧
                      X ≤ componentLayerOf M ∧ X ≠ ⊥ ∧ IsCyclic X ∧
                        IsPGroup od.p X ∧
                        X ≤ qCoreOf od.d.bg.U od.p ∧
                        BenderGlauberman.IsInvertedBy od.d.bg.t2 X ∧
                          X ≤ Subgroup.centralizer (fd.V1 : Set G) ∧
                            IsDGroup (↥(componentLayerOf M)) := by
  classical
  obtain ⟨hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXleC⟩ :=
    firstCase_cyclic_layer_inverted_data_of_od hmin c hfirst hcyclic od
  have hD : IsDGroup (↥(componentLayerOf M)) :=
    properSubgroups_areDGroups hmin (componentLayerOf M) (by
      intro htop
      have hle : componentLayerOf M ≤ M := (componentLayerOf_isNormalIn M).1
      have hMtop : M = ⊤ := le_antisymm le_top (by
        intro x hx
        exact hle (by simpa [htop] using hx))
      exact hMmax.1 hMtop)
  exact ⟨hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXleC, hD⟩

/-- Combine the inverted odd input with the `D`-group structure of the
component layer for the linear eliminiation. -/
public theorem firstCase_cyclic_layer_inverted_and_DGroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ od : FirstCaseOrientedPrimeData c,
      ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
        ∃ fd : FirstCaseFourData c od.d,
          ∃ Q : Sylow od.p ↥od.d.bg.B,
            ∃ M : Subgroup G, ∃ X : Subgroup G,
              IsCoatom M ∧
                Subgroup.normalizer
                  (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                  (c.S : Subgroup G) ≤ M ∧
                    fd.V2 ≤ componentLayerOf M ∧
                      X ≤ componentLayerOf M ∧ X ≠ ⊥ ∧ IsCyclic X ∧
                        IsPGroup od.p X ∧
                        X ≤ qCoreOf od.d.bg.U od.p ∧
                        BenderGlauberman.IsInvertedBy od.d.bg.t2 X ∧
                          X ≤ Subgroup.centralizer (fd.V1 : Set G) ∧
                            IsDGroup (↥(componentLayerOf M)) := by
  classical
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  obtain ⟨od⟩ := exists_firstCaseOrientedPrimeData hmin c hfirst hHhat
  obtain ⟨hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXleC, hD⟩ :=
    firstCase_cyclic_layer_inverted_and_DGroup_of_od hmin c hfirst hcyclic od
  exact ⟨od, hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXleC, hD⟩

end CFSG.GorensteinWalter
