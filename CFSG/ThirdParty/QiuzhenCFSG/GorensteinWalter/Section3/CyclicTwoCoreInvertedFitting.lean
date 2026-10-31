module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreReflectionsInvert
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreFitting
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import all CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic first case: inversion corollaries on `F(U)`

From Step C and the nilpotent decomposition
`F(U) = O₃(U) × O₃′(F(U))`, this module derives the inversion identities
needed for the Theorem-C A₇-model inputs:

1. `I₂ = F(U)` (both `O₃(U)` and `O₃′(F(U))` are inverted by `t₂`);
2. `I₁ = O₃′(F(U))` (the part of `F(U)` inverted by `t₁`);
3. `C_{F(U)}(t₁) = O₃(U)`;
4. `B ∩ F(U) = ⊥`;
5. `F(U)` is abelian.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The `p'`-part of `F(U)` lies in `X` provided every `q`-core of `U`
with `q ≠ p` lies in `X`. -/
private theorem pPrimeCore_map_le_of_qCore_le_ne
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime]
    (X : Subgroup G)
    (hqX : ∀ q : ℕ, q.Prime → q ≠ p → qCoreOf U q ≤ X) :
    ((pPrimeCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype ≤ X := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let F0 : Subgroup U := fittingSubgroup U
  let Q : Subgroup G := ((pPrimeCore p F0).map F0.subtype).map U.subtype
  have hQleF : Q ≤ fittingSubgroupOf U := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    rcases (Subgroup.mem_map).1 hy with ⟨z, hz, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(F0.subtype z : U), z.2, rfl⟩
  have hFnil : Group.IsNilpotent (↥(fittingSubgroupOf U)) := fittingSubgroupOf_isNilpotent U
  have : Group.IsNilpotent (↥(fittingSubgroupOf U)) := hFnil
  have hQFnil : Group.IsNilpotent (↥(Q.subgroupOf (fittingSubgroupOf U))) := by infer_instance
  have : Group.IsNilpotent (↥(Q.subgroupOf (fittingSubgroupOf U))) := hQFnil
  have hQnil : Group.IsNilpotent (↥Q) :=
    Group.nilpotent_of_mulEquiv (G := ↥(Q.subgroupOf (fittingSubgroupOf U))) (G' := ↥Q)
      (Subgroup.subgroupOfEquivOfLe hQleF)
  have : Group.IsNilpotent (↥Q) := hQnil
  have hnilTopQ : Group.IsNilpotent (↥(⊤ : Subgroup Q)) :=
    Group.nilpotent_of_mulEquiv (G := Q) (G' := ↥(⊤ : Subgroup Q))
      (Subgroup.topEquiv.symm : Q ≃* ↥(⊤ : Subgroup Q))
  have htopQ : (⊤ : Subgroup Q) ≤
      ⨆ (q : (Nat.card Q).primeFactors.attach), pCore q.1 Q :=
    normal_nilpotent_le_sup_pCore (G := Q) (N := ⊤) inferInstance hnilTopQ
  have hmapQ : (⊤ : Subgroup Q).map Q.subtype ≤
      ⨆ (q : (Nat.card Q).primeFactors.attach), (pCore q.1 Q).map Q.subtype := by
    calc
      (⊤ : Subgroup Q).map Q.subtype ≤
          ((⨆ (q : (Nat.card Q).primeFactors.attach), pCore q.1 Q).map Q.subtype) :=
            Subgroup.map_mono htopQ
      _ = ⨆ (q : (Nat.card Q).primeFactors.attach), (pCore q.1 Q).map Q.subtype := by
        rw [Subgroup.map_iSup]
  have hqle (q : (Nat.card Q).primeFactors.attach) :
      (pCore q.1 Q).map Q.subtype ≤ qCoreOf U q.1 := by
    let A : Subgroup G := (pCore q.1 Q).map Q.subtype
    have hAp : IsPGroup q.1 A :=
      (pCore_isPGroup (G := Q) (p := q.1)).map Q.subtype
    have hAF : A ≤ fittingSubgroupOf U :=
      (Subgroup.map_subtype_le (H := Q) (pCore q.1 Q)).trans hQleF
    have hAq : A ≤ qCoreOf U q.1 := by
      simpa [A] using (pSubgroup_le_qCoreOf_of_le_fittingSubgroupOf U q.1 A hAp hAF)
    simpa [A] using hAq
  have hQeq : (⊤ : Subgroup Q).map Q.subtype = Q := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := Q))
  have hQleX : Q ≤ X := by
    calc
      Q = (⊤ : Subgroup Q).map Q.subtype := hQeq.symm
      _ ≤ ⨆ (q : (Nat.card Q).primeFactors.attach), (pCore q.1 Q).map Q.subtype := hmapQ
      _ ≤ ⨆ (q : (Nat.card Q).primeFactors.attach), qCoreOf U q.1 := by
        exact iSup_mono (fun q => hqle q)
      _ ≤ X := by
        refine iSup_le (fun q => ?_)
        have hqcard : (q : ℕ) ∣ Nat.card (↥Q) := (Nat.mem_primeFactors.mp q.1.2).2.1
        have hcop : Nat.Coprime p (Nat.card (↥Q)) := pPrimeCore_map_card_coprime U p
        have hndvd : ¬ p ∣ Nat.card (↥Q) :=
          (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop
        have hne : (q : ℕ) ≠ p := by
          intro hqp
          exact hndvd (by simpa [hqp] using hqcard)
        exact hqX q.1 (Nat.prime_of_mem_primeFactors q.1.2) hne
  simpa [Q] using hQleX

/-- The full `p'`-part of `F(U)` lies in `X` provided every `q`-core of
`U` lies in `X`, including `q = p`. -/
private theorem pPrimeCore_map_le_of_qCore_le
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime]
    (X : Subgroup G)
    (hpX : qCoreOf U p ≤ X)
    (hqX : ∀ q : ℕ, q.Prime → q ≠ p → qCoreOf U q ≤ X) :
    ((pPrimeCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype ≤ X := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let F0 : Subgroup U := fittingSubgroup U
  let φ : F0 →* G := U.subtype.comp F0.subtype
  have hnil : Group.IsNilpotent (↥(pPrimeCore p F0)) := by infer_instance
  have hNle : pPrimeCore p F0 ≤
      ⨆ (q : (Nat.card F0).primeFactors.attach), pCore q.1 F0 :=
    normal_nilpotent_le_sup_pCore (G := F0) (N := pPrimeCore p F0) inferInstance hnil
  have hmap : ((pPrimeCore p F0).map φ) ≤
      ⨆ (q : (Nat.card F0).primeFactors.attach), (pCore q.1 F0).map φ := by
    calc
      (pPrimeCore p F0).map φ ≤
          ((⨆ (q : (Nat.card F0).primeFactors.attach), pCore q.1 F0).map φ) :=
            Subgroup.map_mono hNle
      _ = ⨆ (q : (Nat.card F0).primeFactors.attach), (pCore q.1 F0).map φ := by
        rw [Subgroup.map_iSup]
  have hcore (q : (Nat.card F0).primeFactors.attach) :
      (pCore q.1 F0).map φ = qCoreOf U q.1 := by
    dsimp [φ]
    rw [← Subgroup.map_map (K := pCore q.1 F0) U.subtype F0.subtype]
    rw [pCore_fittingSubgroup_map_eq_pCore U q.1]
    rfl
  have hle : (pPrimeCore p F0).map φ ≤ X := by
    calc
      (pPrimeCore p F0).map φ ≤
          ⨆ (q : (Nat.card F0).primeFactors.attach), (pCore q.1 F0).map φ := hmap
      _ ≤ ⨆ (q : (Nat.card F0).primeFactors.attach), qCoreOf U q.1 := by
        exact iSup_mono (fun q => by rw [hcore q])
      _ ≤ X := by
        refine iSup_le (fun q => ?_)
        by_cases hqp : q.1 = p
        · simpa [hqp] using hpX
        · exact hqX q.1 (Nat.prime_of_mem_primeFactors q.1.2) hqp
  simpa [φ, Subgroup.map_map] using hle

/-- The ambient `p'`-part of `F(U)` equals the image of the `p'`-core of
the ambient Fitting subgroup. -/
private theorem pPrimeCore_fittingSubgroupOf_map_eq
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (p : ℕ) [Fact p.Prime] :
    ((pPrimeCore p (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype =
      (pPrimeCore p (↥(fittingSubgroupOf U))).map (fittingSubgroupOf U).subtype := by
  classical
  let F0 : Subgroup U := fittingSubgroup U
  let F : Subgroup G := fittingSubgroupOf U
  let e : F0 ≃* ↥F := F0.equivMapOfInjective U.subtype U.subtype_injective
  have hiso : (pPrimeCore p F0).map e.toMonoidHom = pPrimeCore p (↥F) :=
    pPrimeCore_map_iso (p := p) (G := F0) (G' := ↥F) (f := e)
  have hcomp : U.subtype.comp F0.subtype = F.subtype.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  calc
    ((pPrimeCore p F0).map F0.subtype).map U.subtype =
        (pPrimeCore p F0).map (U.subtype.comp F0.subtype) := by
          rw [Subgroup.map_map]
    _ = (pPrimeCore p F0).map (F.subtype.comp e.toMonoidHom) := by rw [hcomp]
    _ = ((pPrimeCore p F0).map e.toMonoidHom).map F.subtype := by
          rw [Subgroup.map_map]
    _ = (pPrimeCore p (↥F)).map F.subtype := by rw [hiso]

/-- An odd-order subgroup inverted by an involution meets its centralizer
trivially. -/
private theorem inverted_odd_subgroup_inf_centralizerIn_eq_bot
    {G : Type u} [Group G] [Finite G]
    (F X : Subgroup G) (t : G)
    (hodd : Nat.Coprime 2 (Nat.card X))
    (hinv : ∀ x : G, x ∈ X → t * x * t⁻¹ = x⁻¹) :
    X ⊓ centralizerIn F t = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxX : x ∈ X := (Subgroup.mem_inf.mp hx).1
  have hxC : x ∈ centralizerIn F t := (Subgroup.mem_inf.mp hx).2
  have hxC' : x ∈ F ⊓ Subgroup.centralizer ({t} : Set G) := by
    simpa [centralizerIn] using hxC
  have hxfix : t * x * t⁻¹ = x := by
    have hcomm : x * t = t * x :=
      ((Subgroup.mem_centralizer_iff.mp hxC'.2) t (by simp)).symm
    calc
      t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [hcomm]
      _ = x := by group
  have hxinv : t * x * t⁻¹ = x⁻¹ := hinv x hxX
  have hxinv_eq : x⁻¹ = x := hxinv.symm.trans hxfix
  have hx2 : x * x = 1 := by
    calc
      x * x = x⁻¹ * x := by rw [hxinv_eq]
      _ = 1 := by simp
  have hord2 : orderOf x ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).2 (by simpa [pow_two] using hx2)
  have hordX : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hxX
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hodd hord2 hordX)

/-- `I₁` has order coprime to `3`: any 3-element of `I₁` would lie in
`O₃(U)`, be centralized and inverted by `t₁`, hence be trivial. -/
private theorem firstCase_cyclic_I1_card_coprime_three
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hp3 : od.p = 3) :
    Nat.Coprime 3 (Nat.card (↥od.d.I1)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hFUeq : c.FU = fittingSubgroupOf od.d.bg.U := by
    change fittingSubgroupOf c.U = fittingSubgroupOf od.d.bg.U
    rw [hUeq]
  by_contra hnot
  have h3dvd : 3 ∣ Nat.card (↥od.d.I1) := by
    by_contra hndvd
    exact hnot ((Nat.prime_three.coprime_iff_not_dvd).2 hndvd)
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥od.d.I1) 3 h3dvd
  let xG : G := x
  have hxI : xG ∈ od.d.I1 := x.2
  have hx3G : orderOf xG = 3 := by
    change orderOf (x : G) = 3
    simpa [Subgroup.orderOf_coe] using hx3
  have hxFU : xG ∈ c.FU := od.d.I1_hall.1 hxI
  have hxF : xG ∈ fittingSubgroupOf od.d.bg.U := by
    rwa [hFUeq] at hxFU
  have hXp : IsPGroup 3 (Subgroup.zpowers xG) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hx3G]
      norm_num)
  have hXleF : Subgroup.zpowers xG ≤ fittingSubgroupOf od.d.bg.U :=
    Subgroup.zpowers_le.mpr hxF
  have hXleP : Subgroup.zpowers xG ≤ qCoreOf od.d.bg.U 3 :=
    pSubgroup_le_qCoreOf_of_le_fittingSubgroupOf od.d.bg.U 3
      (Subgroup.zpowers xG) hXp hXleF
  have hxP : xG ∈ qCoreOf od.d.bg.U 3 := hXleP (Subgroup.mem_zpowers xG)
  have ht1C : od.d.bg.t1 ∈ Subgroup.centralizer
      (qCoreOf od.d.bg.U 3 : Set G) := by
    simpa [hp3] using firstCase_t1_centralizes_primeCore c od
  have hcomm : xG * od.d.bg.t1 = od.d.bg.t1 * xG :=
    (Subgroup.mem_centralizer_iff.mp ht1C) xG hxP
  have hcent : od.d.bg.t1 * xG * od.d.bg.t1⁻¹ = xG := by
    calc
      od.d.bg.t1 * xG * od.d.bg.t1⁻¹ = (xG * od.d.bg.t1) * od.d.bg.t1⁻¹ := by rw [hcomm]
      _ = xG := by group
  have hxInvSet : xG ∈ invertedElements c.U od.d.bg.t1 := by
    rw [← od.d.I1_inverted]
    exact hxI
  have hinv : od.d.bg.t1 * xG * od.d.bg.t1⁻¹ = xG⁻¹ := by
    simpa [hUeq] using hxInvSet.2
  have hxinv_eq : xG⁻¹ = xG := hinv.symm.trans hcent
  have hx2 : xG * xG = 1 := by
    calc
      xG * xG = xG⁻¹ * xG := by rw [hxinv_eq]
      _ = 1 := by simp
  have hord2 : orderOf xG ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one (x := xG) (n := 2)).2 (by simpa [pow_two] using hx2)
  have h3dvd2 : (3 : ℕ) ∣ 2 := by simpa [hx3G] using hord2
  norm_num at h3dvd2

/-- `I₂ = F(U)`: `t₂` inverts all of the Fitting subgroup. -/
public theorem firstCase_cyclic_I2_eq_FU_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3) :
    od.d.I2 = c.FU := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hFUeq : c.FU = fittingSubgroupOf od.d.bg.U := by
    change fittingSubgroupOf c.U = fittingSubgroupOf od.d.bg.U
    rw [hUeq]
  have hPleI2 : qCoreOf od.d.bg.U 3 ≤ od.d.I2 := by
    have hq : qCoreOf c.U 3 = qCoreOf od.d.bg.U 3 := by rw [hUeq]
    simpa [hq, hp3] using od.primeCore_le_I2
  have hqle (q : ℕ) (hq : q.Prime) (hne : q ≠ 3) :
      qCoreOf od.d.bg.U q ≤ od.d.I2 := by
    by_cases hbot : qCoreOf od.d.bg.U q = ⊥
    · intro x hx
      have hx1 : x = 1 := Subgroup.mem_bot.mp (by simpa [hbot] using hx)
      subst x
      exact od.d.I2.one_mem
    · exact (firstCase_cyclic_reflections_invert_qCore_of_ne_three
        hmin c od hfirst hcyclic hU Q M hMmax hMN hSM fd hV2 hA7 hp3 hq hbot hne).2
  have hQleI2 : ((pPrimeCore 3 (fittingSubgroup od.d.bg.U)).map
      (fittingSubgroup od.d.bg.U).subtype).map od.d.bg.U.subtype ≤ od.d.I2 :=
    pPrimeCore_map_le_of_qCore_le od.d.bg.U 3 od.d.I2 hPleI2 hqle
  apply le_antisymm
  · exact od.d.I2_hall.1
  · rw [hFUeq, fittingSubgroupOf_eq_qCore_sup_pPrimeCore_map od.d.bg.U 3]
    exact sup_le hPleI2 hQleI2

/-- `I₁ = O₃′(F(U))`: the part of `F(U)` inverted by `t₁`. -/
public theorem firstCase_cyclic_I1_eq_pPrimeCore_fittingSubgroupOf_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3) :
    od.d.I1 =
      ((pPrimeCore 3 (fittingSubgroup od.d.bg.U)).map
        (fittingSubgroup od.d.bg.U).subtype).map od.d.bg.U.subtype := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let U : Subgroup G := od.d.bg.U
  let F : Subgroup G := fittingSubgroupOf U
  let Q3 : Subgroup G :=
    ((pPrimeCore 3 (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hFUeq : c.FU = fittingSubgroupOf od.d.bg.U := by
    change fittingSubgroupOf c.U = fittingSubgroupOf od.d.bg.U
    rw [hUeq]
  have hr1 : c.IsReflection od.d.bg.t1 := by
    constructor
    · simpa [od.d.S_eq] using od.d.bg.t1_mem_S
    · simpa [od.d.S0_eq] using od.d.bg.t1_not_mem_S0
  have hI1data := centralizerSetup_reflection_invertedSubgroup_abelian_normal
    c hr1 od.d.I1_inverted
  have hI1leF : od.d.I1 ≤ F := by
    simpa [F, hFUeq] using hI1data.2.2
  have hI1cop3 := firstCase_cyclic_I1_card_coprime_three c od hp3
  have hI1normF : (od.d.I1.subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hI1leF]
    intro x hx
    exact (le_normalizer_of_isNormalIn hI1data.2.1)
      (by simpa [hUeq] using (fittingSubgroupOf_le U hx))
  have : (od.d.I1.subgroupOf F).Normal := hI1normF
  have hI1leQ' : od.d.I1 ≤ (pPrimeCore 3 (↥F)).map F.subtype :=
    subgroupOf_le_pPrimeCore_map (H := F) (K := od.d.I1) hI1leF hI1cop3
  have hI1leQ : od.d.I1 ≤ Q3 := by
    have hQeq : ((pPrimeCore 3 (fittingSubgroup U)).map (fittingSubgroup U).subtype).map
        U.subtype = (pPrimeCore 3 (↥F)).map F.subtype :=
      pPrimeCore_fittingSubgroupOf_map_eq U 3
    simpa [Q3] using hQeq ▸ hI1leQ'
  have hqle (q : ℕ) (hq : q.Prime) (hne : q ≠ 3) :
      qCoreOf U q ≤ od.d.I1 := by
    by_cases hbot : qCoreOf U q = ⊥
    · intro x hx
      have hx1 : x = 1 := Subgroup.mem_bot.mp (by simpa [hbot] using hx)
      subst x
      exact od.d.I1.one_mem
    · exact (firstCase_cyclic_reflections_invert_qCore_of_ne_three
        hmin c od hfirst hcyclic hU Q M hMmax hMN hSM fd hV2 hA7 hp3 hq hbot hne).1
  have hQleI1 : Q3 ≤ od.d.I1 := by
    simpa [Q3] using (pPrimeCore_map_le_of_qCore_le_ne U 3 od.d.I1 hqle)
  exact le_antisymm hI1leQ hQleI1

/-- `C_{F(U)}(t₁) = O₃(U)`. -/
public theorem firstCase_cyclic_centralizer_FU_t1_eq_threeCore_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3) :
    centralizerIn c.FU od.d.bg.t1 = qCoreOf od.d.bg.U 3 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let U : Subgroup G := od.d.bg.U
  let F : Subgroup G := fittingSubgroupOf U
  let P : Subgroup G := qCoreOf U 3
  let Q3 : Subgroup G :=
    ((pPrimeCore 3 (fittingSubgroup U)).map (fittingSubgroup U).subtype).map U.subtype
  let A : Subgroup G := centralizerIn F od.d.bg.t1
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hFUeq : c.FU = fittingSubgroupOf od.d.bg.U := by
    change fittingSubgroupOf c.U = fittingSubgroupOf od.d.bg.U
    rw [hUeq]
  have ht1C : od.d.bg.t1 ∈ Subgroup.centralizer (P : Set G) := by
    simpa [P, hp3] using firstCase_t1_centralizes_primeCore c od
  have hPleA : P ≤ A := by
    intro x hx
    refine ⟨fstar_qCoreOf_le_fittingSubgroupOf U 3
      (by simpa [hp3] using od.p_prime) hx, ?_⟩
    exact (Subgroup.mem_centralizer_singleton_iff).mpr
      ((Subgroup.mem_centralizer_iff.mp ht1C) x hx)
  have hAsplit : A = P ⊔ (A ⊓ Q3) := by
    simpa [A, P, Q3] using
      (centralizerIn_fittingSubgroupOf_eq_pCore_sup_inter_pPrimeCore
        U 3 od.d.bg.t1 hPleA)
  have hqle (q : ℕ) (hq : q.Prime) (hne : q ≠ 3) :
      qCoreOf U q ≤ od.d.I1 := by
    by_cases hbot : qCoreOf U q = ⊥
    · intro x hx
      have hx1 : x = 1 := Subgroup.mem_bot.mp (by simpa [hbot] using hx)
      subst x
      exact od.d.I1.one_mem
    · exact (firstCase_cyclic_reflections_invert_qCore_of_ne_three
        hmin c od hfirst hcyclic hU Q M hMmax hMN hSM fd hV2 hA7 hp3 hq hbot hne).1
  have hQleI1 : Q3 ≤ od.d.I1 := by
    simpa [Q3] using (pPrimeCore_map_le_of_qCore_le_ne U 3 od.d.I1 hqle)
  have hQinv : ∀ x : G, x ∈ Q3 → od.d.bg.t1 * x * od.d.bg.t1⁻¹ = x⁻¹ := by
    intro x hxQ
    have hxI : x ∈ od.d.I1 := hQleI1 hxQ
    have hxInvSet : x ∈ invertedElements c.U od.d.bg.t1 := by
      rw [← od.d.I1_inverted]
      exact hxI
    simpa [hUeq] using hxInvSet.2
  have hQleU : Q3 ≤ U := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    exact y.2
  have hQodd : Nat.Coprime 2 (Nat.card Q3) := by
    have hUcop : Nat.Coprime 2 (Nat.card (↥U)) := BenderGlauberman.U_coprime_two od.d.bg
    exact hUcop.coprime_dvd_right (Subgroup.card_dvd_of_le hQleU)
  have hAQbot : A ⊓ Q3 = ⊥ := by
    simpa [A, inf_comm] using (inverted_odd_subgroup_inf_centralizerIn_eq_bot F Q3
      od.d.bg.t1 hQodd hQinv)
  have hAeq : A = P := by
    rw [hAsplit]
    simp [hAQbot]
  simpa [F, P, hFUeq] using hAeq

/-- `B ∩ F(U) = ⊥`. -/
public theorem firstCase_cyclic_B_inter_FU_eq_bot_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3) :
    od.d.bg.B ⊓ c.FU = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData od.d.bg := firstCaseBGKData hmin c od.d
  have hI2FU : od.d.I2 = c.FU :=
    firstCase_cyclic_I2_eq_FU_of_a7 hmin c od hfirst hcyclic hU Q M hMmax hMN hSM
      fd hV2 hA7 hp3
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hUcop : Nat.Coprime 2 (Nat.card (↥od.d.bg.U)) := BenderGlauberman.U_coprime_two od.d.bg
  have hFUleU : c.FU ≤ od.d.bg.U := by
    intro x hx
    have hxU : x ∈ c.U := by
      have hxFU' : x ∈ (fittingSubgroup c.U).map c.U.subtype := by
        simpa [CentralizerSetup.FU, GorensteinWalter.fittingSubgroupOf] using hx
      rcases (Subgroup.mem_map).1 hxFU' with ⟨y, hy, rfl⟩
      exact y.2
    simpa [hUeq] using hxU
  have hFUodd : Nat.Coprime 2 (Nat.card (↥c.FU)) :=
    hUcop.coprime_dvd_right (Subgroup.card_dvd_of_le hFUleU)
  apply le_bot_iff.mp
  intro x hx
  have hxB : x ∈ od.d.bg.B := (Subgroup.mem_inf.mp hx).1
  have hxF : x ∈ c.FU := (Subgroup.mem_inf.mp hx).2
  have hxI2 : x ∈ od.d.I2 := by rwa [← hI2FU] at hxF
  have hxInvSet : x ∈ invertedElements c.U od.d.bg.t2 := by
    rw [← od.d.I2_inverted]
    exact hxI2
  have hxinv : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x⁻¹ := by
    simpa [hUeq] using hxInvSet.2
  have hxB2 : x ∈ od.d.bg.B2 :=
    BenderGlauberman.theoremC_mem_B2_of_mem_B od.d.bg hxB
  have hxfix : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x :=
    BenderGlauberman.theoremC_fixed_by_t2_of_mem_B2 od.d.bg hxB2
  have hxinv_eq : x⁻¹ = x := hxinv.symm.trans hxfix
  have hx2 : x * x = 1 := by
    calc
      x * x = x⁻¹ * x := by rw [hxinv_eq]
      _ = 1 := by simp
  have hord2 : orderOf x ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).2 (by simpa [pow_two] using hx2)
  have hordF : orderOf x ∣ Nat.card (↥c.FU) := Subgroup.orderOf_dvd_natCard c.FU hxF
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hFUodd hord2 hordF)

/-- `F(U)` is abelian. -/
public theorem firstCase_cyclic_FU_abelian_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3) :
    IsMulCommutative (↥c.FU) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hI2FU : od.d.I2 = c.FU :=
    firstCase_cyclic_I2_eq_FU_of_a7 hmin c od hfirst hcyclic hU Q M hMmax hMN hSM
      fd hV2 hA7 hp3
  have hK2abel : IsMulCommutative (↥((firstCaseBGKData hmin c od.d).K2)) :=
    (firstCase_cyclic_K2_abelian_normal hmin c od.d).1
  change IsMulCommutative (↥od.d.I2) at hK2abel
  rw [← hI2FU]
  exact hK2abel

end CFSG.GorensteinWalter
