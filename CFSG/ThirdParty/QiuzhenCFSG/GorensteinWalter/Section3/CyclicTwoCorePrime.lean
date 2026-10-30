module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreSetup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
-- `B`, `B1`, `B2` are not `@[expose]`d; `swap_B_eq` needs their bodies.
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.FinalTheorem
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u

private theorem centralizerSetup_U_isNormalIn_H
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : IsNormalIn c.U c.H := by
  refine ⟨Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H), ?_⟩
  intro h hh x hx
  rcases (Subgroup.mem_map).1 hx with ⟨p, hp, rfl⟩
  have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
      pPrimeCore 2 c.H :=
    (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem p hp ⟨h, hh⟩
  exact Subgroup.mem_map.mpr
    ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩

private theorem commutator_double_eq_self_of_coprime_solvable
    {G : Type u} [Group G] [Finite G]
    (P K : Subgroup G) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K))
    (hsolv : IsSolvable K) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ := by
  classical
  let : Subgroup.Normalizes P K := ⟨hPK⟩
  let : MulDistribMulAction P K :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P K hPK
  let C : Subgroup K := commutatorAction (A := P) (G := K)
  have hCmap : C.map K.subtype = ⁅K, P⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator K P hPK
  have hC2eq : commutatorAction₂ (A := P) (G := K) = C :=
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := K) (A := P) hsolv hcop
  have hXle : ⁅⁅K, P⁆, P⁆ ≤ ⁅K, P⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right K P)
  have hcomm₂_le :
      (commutatorAction₂ (A := P) (G := K)).map K.subtype ≤
        ⁅⁅K, P⁆, P⁆ := by
    let S : Set K := {x : K | ∃ a : P, ∃ k : K,
      k ∈ C ∧ x = k⁻¹ * (a • k)}
    calc
      (commutatorAction₂ (A := P) (G := K)).map K.subtype =
          (Subgroup.closure S).map K.subtype := by rfl
      _ = Subgroup.closure (K.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := K.subtype) S)
      _ ≤ ⁅⁅K, P⁆, P⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅K, P⁆, P⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, k, hkC, rfl⟩
        have hkX : (k : G) ∈ ⁅K, P⁆ := by
          rw [← hCmap]
          exact Subgroup.mem_map.mpr ⟨k, hkC, rfl⟩
        have hgen : ⁅((k : K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, P⁆, P⁆ :=
          Subgroup.commutator_mem_commutator
            (Subgroup.inv_mem (H := ⁅K, P⁆) hkX) a.2
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          mul_assoc] using hgen
  apply le_antisymm hXle
  intro x hx
  have hx₂ : x ∈ (commutatorAction₂ (A := P) (G := K)).map K.subtype := by
    rw [hC2eq, hCmap]
    exact hx
  exact hcomm₂_le hx₂

private theorem exists_primeCore_not_centralized
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c)
    (hcomm : ⁅c.S0, c.U⁆ ≠ ⊥)
    (hcommFU : ⁅c.S0, c.U⁆ ≤ c.FU) :
    ∃ p : ℕ, p.Prime ∧
      ¬ c.S0 ≤ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
  classical
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2
      (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hnotTwoU : ¬ 2 ∣ Nat.card c.U :=
    Nat.prime_two.coprime_iff_not_dvd.mp hUodd
  have hS0card : Nat.card c.S0 = 2 ^ c.m := by
    simpa [d.S0_eq, d.m_eq] using BenderGlauberman.S0_nat_card d.bg
  have hcop : Nat.Coprime (Nat.card c.S0) (Nat.card c.U) := by
    rw [hS0card]
    exact (Nat.prime_two.coprime_pow_of_not_dvd hnotTwoU).symm
  have hS0normU : c.S0 ≤ Subgroup.normalizer (c.U : Set G) :=
    (c.S0_le_S.trans (centralizerSetup_S_le_H c)).trans
      (le_normalizer_of_isNormalIn (centralizerSetup_U_isNormalIn_H c))
  have hUsolv : IsSolvable c.U := by
    exact odd_order_theorem c.U (Nat.coprime_two_left.mp hUodd)
  have hdouble : ⁅⁅c.U, c.S0⁆, c.S0⁆ = ⁅c.U, c.S0⁆ :=
    commutator_double_eq_self_of_coprime_solvable
      c.S0 c.U hS0normU hcop hUsolv
  have hex : ∃ q : (Nat.card c.U).primeFactors.attach,
      ¬ c.S0 ≤ Subgroup.centralizer
        (qCoreOf c.U q.1.1 : Set G) := by
    by_contra hall
    push Not at hall
    have hcentFU : c.S0 ≤ Subgroup.centralizer (c.FU : Set G) := by
      change c.S0 ≤ Subgroup.centralizer (fittingSubgroupOf c.U : Set G)
      rw [fittingSubgroupOf_eq_iSup_qCoreOf c.U]
      exact subgroup_le_centralizer_iSup_of_le_centralizer
        (fun q : (Nat.card c.U).primeFactors.attach => qCoreOf c.U q.1.1)
        hall
    have hSUbot : ⁅c.S0, c.FU⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hcentFU
    have hUSbot : ⁅c.FU, c.S0⁆ = ⊥ := by
      simpa [Subgroup.commutator_comm] using hSUbot
    have hXleFU : ⁅c.U, c.S0⁆ ≤ c.FU := by
      simpa [Subgroup.commutator_comm] using hcommFU
    have hdoubleBot : ⁅⁅c.U, c.S0⁆, c.S0⁆ = ⊥ := by
      apply le_bot_iff.mp
      exact (Subgroup.commutator_mono hXleFU le_rfl).trans
        (le_of_eq hUSbot)
    have hXbot : ⁅c.U, c.S0⁆ = ⊥ := by
      rw [← hdouble]
      exact hdoubleBot
    apply hcomm
    simpa [Subgroup.commutator_comm] using hXbot
  obtain ⟨q, hq⟩ := hex
  exact ⟨q.1.1, Nat.prime_of_mem_primeFactors q.1.2, hq⟩

private theorem hallSubgroup_subgroupPrimeSet_of_isHallIn
    {G : Type u} [Group G] [Finite G]
    {K H : Subgroup G} (hHall : IsHallIn K H) :
    IsHallSubgroup (subgroupPrimeSet K) (K.subgroupOf H) := by
  classical
  rcases hHall with ⟨hKH, hcop⟩
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  refine isHallSubgroup_of
    (G := H) (subgroupPrimeSet K) (K.subgroupOf H) ?_ ?_
  · intro q hq
    simpa [subgroupPrimeSet, hcard] using hq
  · intro q hqK hqIndex
    have hqCard : q.1 ∣ Nat.card K := by
      simpa [subgroupPrimeSet] using hqK
    exact ((q.2.coprime_iff_not_dvd).1
      (hcop.coprime_dvd_left hqCard)) hqIndex

private theorem primeCore_le_or_disjoint_invertedHall
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (I : Subgroup G)
    (hHall : IsHallIn I c.FU) (p : ℕ) (hp : p.Prime) :
    qCoreOf c.U p ≤ I ∨ Disjoint I (qCoreOf c.U p) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hPleFU : qCoreOf c.U p ≤ c.FU :=
    fstar_qCoreOf_le_fittingSubgroupOf c.U p hp
  by_cases hpI : p ∣ Nat.card I
  · left
    have hHallSub :
        IsHallSubgroup (subgroupPrimeSet I) (I.subgroupOf c.FU) :=
      hallSubgroup_subgroupPrimeSet_of_isHallIn hHall
    have hpMem : (⟨p, hp⟩ : Nat.Primes) ∈ subgroupPrimeSet I := by
      change p ∣ Nat.card I
      exact hpI
    have : ((qCoreOf c.U p).subgroupOf c.FU).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPleFU]
      exact (fittingSubgroupOf_le (G := G) c.U).trans
        (le_normalizer_of_isNormalIn (qCoreOf_normal_in c.U p))
    have hPgroup : IsPGroup p ((qCoreOf c.U p).subgroupOf c.FU) :=
      (qCoreOf_isPGroup c.U p).of_equiv
        (Subgroup.subgroupOfEquivOfLe hPleFU).symm
    have hle :=
      section12_normal_pSubgroup_le_of_isHallSubgroup_of_prime_mem
        hPgroup hHallSub hpMem
    intro x hx
    have hxFU : x ∈ c.FU := hPleFU hx
    exact hle (show (⟨x, hxFU⟩ : c.FU) ∈
      (qCoreOf c.U p).subgroupOf c.FU from hx)
  · right
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (qCoreOf_isPGroup c.U p).exists_card_eq
    rw [hn]
    exact hp.coprime_pow_of_not_dvd hpI

private theorem reflection_centralizes_primeCore_of_disjoint_invertedHall
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (r : G) (hr : c.IsReflection r)
    (I : Subgroup G) (hI : IsInvertedSubgroup I c.U r)
    {p : ℕ} (hp : p.Prime)
    (hdis : Disjoint I (qCoreOf c.U p)) :
    r ∈ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
  classical
  have hrInv : IsInvolution r :=
    centralizerSetup_reflection_isInvolution c hr
  have hrH : r ∈ c.H := centralizerSetup_S_le_H c hr.1
  have hrNormU : r ∈ Subgroup.normalizer (c.U : Set G) :=
    (le_normalizer_of_isNormalIn (centralizerSetup_U_isNormalIn_H c)) hrH
  have hrP : ∀ x : G, x ∈ qCoreOf c.U p →
      r * x * r⁻¹ ∈ qCoreOf c.U p := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xU, hxCore, rfl⟩
    let rU : Subgroup.normalizer (c.U : Set G) := ⟨r, hrNormU⟩
    have hfix :
        (pCore p c.U).comap
            (Subgroup.normalizerMonoidHom c.U rU).toMonoidHom =
          pCore p c.U :=
      (pCore_characteristic (G := c.U) (p := p)).fixed
        (Subgroup.normalizerMonoidHom c.U rU)
    have hxComap : xU ∈ (pCore p c.U).comap
        (Subgroup.normalizerMonoidHom c.U rU).toMonoidHom := by
      rw [hfix]
      exact hxCore
    exact Subgroup.mem_map.mpr
      ⟨(Subgroup.normalizerMonoidHom c.U rU) xU, hxComap, by
        simp [rU, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
  have hPleU : qCoreOf c.U p ≤ c.U :=
    (fstar_qCoreOf_le_fittingSubgroupOf c.U p hp).trans
      (fittingSubgroupOf_le (G := G) c.U)
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2
      (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hPodd : Nat.Coprime 2 (Nat.card (qCoreOf c.U p)) :=
    hUodd.coprime_dvd_right (Subgroup.card_dvd_of_le hPleU)
  have hfact :=
    fact_1_5_i_invertedElements_eq_image hrInv hPodd hrP
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  let y : G := x⁻¹ * (r * x * r⁻¹)
  have hyP : y ∈ qCoreOf c.U p :=
    (qCoreOf c.U p).mul_mem ((qCoreOf c.U p).inv_mem hx) (hrP x hx)
  have hyInvP : y ∈ invertedElements (qCoreOf c.U p) r := by
    rw [hfact]
    exact ⟨⟨x, hx⟩, rfl⟩
  have hyI : y ∈ I := by
    have hyInvU : y ∈ invertedElements c.U r :=
      ⟨hPleU hyInvP.1, hyInvP.2⟩
    have hyIset : y ∈ (I : Set G) := by
      rw [hI]
      exact hyInvU
    exact hyIset
  have hyBot : y ∈ (⊥ : Subgroup G) := hdis.le_bot ⟨hyI, hyP⟩
  have hyOne : y = 1 := by simpa using hyBot
  have hconj : r * x * r⁻¹ = x := by
    calc
      r * x * r⁻¹ = x * (x⁻¹ * (r * x * r⁻¹)) := by group
      _ = x := by rw [← show y = x⁻¹ * (r * x * r⁻¹) from rfl, hyOne]; simp
  have hcomm : r * x = x * r := by
    calc
      r * x = (r * x * r⁻¹) * r := by group
      _ = x * r := by rw [hconj]
  exact hcomm.symm

public theorem primeCore_le_invertedHall_or_reflection_centralizes
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (r : G) (hr : c.IsReflection r)
    (I : Subgroup G) (hI : IsInvertedSubgroup I c.U r)
    (hHall : IsHallIn I c.FU) {p : ℕ} (hp : p.Prime) :
    qCoreOf c.U p ≤ I ∨
      r ∈ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
  rcases primeCore_le_or_disjoint_invertedHall c I hHall p hp with hle | hdis
  · exact Or.inl hle
  · exact Or.inr
      (reflection_centralizes_primeCore_of_disjoint_invertedHall
        c r hr I hI hp hdis)

public noncomputable def swapFirstCaseBGData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    FirstCaseBGData c := by
  have ht1sq : d.bg.t1 * d.bg.t1 = 1 := by
    simpa [pow_two] using d.bg.t1_involution.2
  have ht2sq : d.bg.t2 * d.bg.t2 = 1 := by
    simpa [pow_two] using d.bg.t2_involution.2
  have ht1inv : d.bg.t1⁻¹ = d.bg.t1 := by
    calc
      d.bg.t1⁻¹ = d.bg.t1⁻¹ * (d.bg.t1 * d.bg.t1) := by rw [ht1sq]; simp
      _ = d.bg.t1 := by group
  have ht2inv : d.bg.t2⁻¹ = d.bg.t2 := by
    calc
      d.bg.t2⁻¹ = d.bg.t2⁻¹ * (d.bg.t2 * d.bg.t2) := by rw [ht2sq]; simp
      _ = d.bg.t2 := by group
  let bg' : BenderGlauberman.Hyp11 G := {
    d.bg with
    t1 := d.bg.t2
    t2 := d.bg.t1
    t1_mem_S := d.bg.t2_mem_S
    t1_not_mem_S0 := d.bg.t2_not_mem_S0
    t1_involution := d.bg.t2_involution
    t2_mem_S := d.bg.t1_mem_S
    t2_not_mem_S0 := d.bg.t1_not_mem_S0
    t2_involution := d.bg.t1_involution
    S0_eq_zpowers := by
      calc
        d.bg.S0 = Subgroup.zpowers (d.bg.t1 * d.bg.t2) := d.bg.S0_eq_zpowers
        _ = Subgroup.zpowers ((d.bg.t1 * d.bg.t2)⁻¹) :=
          Subgroup.zpowers_inv.symm
        _ = Subgroup.zpowers (d.bg.t2 * d.bg.t1) := by
          rw [mul_inv_rev, ht2inv, ht1inv]
  }
  exact {
    bg := bg'
    m_eq := by simpa [bg'] using d.m_eq
    S_eq := by simpa [bg'] using d.S_eq
    S0_eq := by simpa [bg'] using d.S0_eq
    H_eq := by simpa [bg'] using d.H_eq
    t_eq := by simpa [bg'] using d.t_eq
    I1 := d.I2
    I2 := d.I1
    I1_inverted := by simpa [bg'] using d.I2_inverted
    I2_inverted := by simpa [bg'] using d.I1_inverted
    I1_hall := d.I2_hall
    I2_hall := d.I1_hall
  }

/-- Swapping the two reflections swaps `t₁` and `t₂`. -/
public theorem swap_t1_eq {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    (swapFirstCaseBGData c d).bg.t1 = d.bg.t2 := by
  rfl

/-- Swapping the two reflections swaps `t₁` and `t₂`. -/
public theorem swap_t2_eq {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    (swapFirstCaseBGData c d).bg.t2 = d.bg.t1 := by
  rfl

/-- Swapping the two reflections swaps the inverted Hall subgroups. -/
public theorem swap_I1_eq {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    (swapFirstCaseBGData c d).I1 = d.I2 := by
  rfl

/-- Swapping the two reflections swaps the inverted Hall subgroups. -/
public theorem swap_I2_eq {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    (swapFirstCaseBGData c d).I2 = d.I1 := by
  rfl

/-- Swapping the two reflections preserves the odd core `U`. -/
public theorem swap_U_eq {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    (swapFirstCaseBGData c d).bg.U = d.bg.U := by
  rfl

/-- Swapping the two reflections preserves the common centralizer `B`. -/
public theorem swap_B_eq {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    (swapFirstCaseBGData c d).bg.B = d.bg.B := by
  unfold BenderGlauberman.Hyp11.B
  unfold BenderGlauberman.Hyp11.B1 BenderGlauberman.Hyp11.B2
  simp [swap_U_eq, swap_t1_eq, swap_t2_eq, inf_comm]

/-- Swapping the two reflections preserves the Sylow `2`-subgroup `S`. -/
public theorem swap_S_eq {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    (swapFirstCaseBGData c d).bg.S = d.bg.S := by
  rfl

private theorem firstCase_S0_centralizes_primeCore_of_both_centralize
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) {p : ℕ}
    (hcent1 : d.bg.t1 ∈ Subgroup.centralizer (qCoreOf c.U p : Set G))
    (hcent2 : d.bg.t2 ∈ Subgroup.centralizer (qCoreOf c.U p : Set G)) :
    c.S0 ≤ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
  have hprod : d.bg.t1 * d.bg.t2 ∈
      Subgroup.centralizer (qCoreOf c.U p : Set G) :=
    (Subgroup.centralizer (qCoreOf c.U p : Set G)).mul_mem hcent1 hcent2
  have hbg : d.bg.S0 ≤
      Subgroup.centralizer (qCoreOf c.U p : Set G) := by
    rw [d.bg.S0_eq_zpowers]
    exact Subgroup.zpowers_le.mpr hprod
  simpa [d.S0_eq] using hbg

private theorem firstCase_S0_centralizes_primeCore_of_both_invert
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) {p : ℕ}
    (hle1 : qCoreOf c.U p ≤ d.I1)
    (hle2 : qCoreOf c.U p ≤ d.I2) :
    c.S0 ≤ Subgroup.centralizer (qCoreOf c.U p : Set G) := by
  have hprod : d.bg.t1 * d.bg.t2 ∈
      Subgroup.centralizer (qCoreOf c.U p : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxInv1 : x ∈ invertedElements c.U d.bg.t1 := by
      rw [← d.I1_inverted]
      exact hle1 hx
    have hxInv2 : x ∈ invertedElements c.U d.bg.t2 := by
      rw [← d.I2_inverted]
      exact hle2 hx
    have hconj :
        (d.bg.t1 * d.bg.t2) * x * (d.bg.t1 * d.bg.t2)⁻¹ = x := by
      calc
        (d.bg.t1 * d.bg.t2) * x * (d.bg.t1 * d.bg.t2)⁻¹ =
            d.bg.t1 * ((d.bg.t2 * x * d.bg.t2⁻¹) * d.bg.t1⁻¹) := by group
        _ = d.bg.t1 * (x⁻¹ * d.bg.t1⁻¹) := by rw [hxInv2.2]
        _ = (d.bg.t1 * x * d.bg.t1⁻¹)⁻¹ := by group
        _ = (x⁻¹)⁻¹ := by rw [hxInv1.2]
        _ = x := by simp
    have hcomm : (d.bg.t1 * d.bg.t2) * x = x * (d.bg.t1 * d.bg.t2) := by
      calc
        (d.bg.t1 * d.bg.t2) * x =
            ((d.bg.t1 * d.bg.t2) * x * (d.bg.t1 * d.bg.t2)⁻¹) *
              (d.bg.t1 * d.bg.t2) := by group
        _ = x * (d.bg.t1 * d.bg.t2) := by rw [hconj]
    exact hcomm.symm
  have hbg : d.bg.S0 ≤
      Subgroup.centralizer (qCoreOf c.U p : Set G) := by
    rw [d.bg.S0_eq_zpowers]
    exact Subgroup.zpowers_le.mpr hprod
  simpa [d.S0_eq] using hbg

public structure FirstCaseOrientedPrimeData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) where
  d : FirstCaseBGData c
  p : ℕ
  p_prime : p.Prime
  primeCore_ne_bot : qCoreOf c.U p ≠ ⊥
  t1_centralizes :
    d.bg.t1 ∈ Subgroup.centralizer (qCoreOf c.U p : Set G)
  primeCore_le_I2 : qCoreOf c.U p ≤ d.I2

public theorem exists_firstCaseOrientedPrimeData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H) :
    Nonempty (FirstCaseOrientedPrimeData c) := by
  classical
  obtain ⟨d⟩ := exists_firstCaseBGData hmin c hfirst
  have hcomm : ⁅c.S0, c.U⁆ ≠ ⊥ :=
    firstCase_commutator_S0_U_ne_bot hmin c hfirst hHhat
  have hinverted : ∀ r : G, c.IsReflection r →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U r := by
    intro r hr
    obtain ⟨I, hI, _hHall⟩ := hfirst.1 r hr
    exact ⟨I, hI⟩
  have hcommFU : ⁅c.S0, c.U⁆ ≤ c.FU :=
    (Subgroup.commutator_mono c.S0_le_S le_rfl).trans
      (lemma_2_8_commutator_le_FU c hinverted)
  obtain ⟨p, hp, hnotcent⟩ :=
    exists_primeCore_not_centralized c d hcomm hcommFU
  have hPne : qCoreOf c.U p ≠ ⊥ := by
    intro hPbot
    apply hnotcent
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx1 : x = 1 := by simpa [hPbot] using hx
    subst x
    simp
  have hr1 : c.IsReflection d.bg.t1 := by
    constructor
    · simpa [d.S_eq] using d.bg.t1_mem_S
    · simpa [d.S0_eq] using d.bg.t1_not_mem_S0
  have hr2 : c.IsReflection d.bg.t2 := by
    constructor
    · simpa [d.S_eq] using d.bg.t2_mem_S
    · simpa [d.S0_eq] using d.bg.t2_not_mem_S0
  have hcase1 := primeCore_le_invertedHall_or_reflection_centralizes
    c d.bg.t1 hr1 d.I1 d.I1_inverted d.I1_hall hp
  have hcase2 := primeCore_le_invertedHall_or_reflection_centralizes
    c d.bg.t2 hr2 d.I2 d.I2_inverted d.I2_hall hp
  rcases hcase1 with hle1 | hcent1
  · rcases hcase2 with hle2 | hcent2
    · exact False.elim (hnotcent
        (firstCase_S0_centralizes_primeCore_of_both_invert c d hle1 hle2))
    · let d' := swapFirstCaseBGData c d
      exact ⟨{
        d := d'
        p := p
        p_prime := hp
        primeCore_ne_bot := hPne
        t1_centralizes := by
          change d.bg.t2 ∈ Subgroup.centralizer (qCoreOf c.U p : Set G)
          exact hcent2
        primeCore_le_I2 := by
          change qCoreOf c.U p ≤ d.I1
          exact hle1
      }⟩
  · rcases hcase2 with hle2 | hcent2
    · exact ⟨{
        d := d
        p := p
        p_prime := hp
        primeCore_ne_bot := hPne
        t1_centralizes := hcent1
        primeCore_le_I2 := hle2
      }⟩
    · exact False.elim (hnotcent
        (firstCase_S0_centralizes_primeCore_of_both_centralize c d hcent1 hcent2))

end CFSG.GorensteinWalter
