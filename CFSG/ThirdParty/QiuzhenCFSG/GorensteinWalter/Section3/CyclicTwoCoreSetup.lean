module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.FinalTheorem
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u

public theorem cyclicCore_hhat_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    c.Hhat = c.H := by
  have h26 := theorem_2_6 hmin c
  rcases h26.2.2 with hleft | hright
  · exact hleft.2
  · rcases hright with ⟨hK4, _hquot⟩
    let f : (pCore 2 c.Hhat) →* c.S0 :=
      { toFun := fun x => ⟨(x : G), hcyclic (by
          change (x : G) ∈ (pCore 2 c.Hhat).map c.Hhat.subtype
          exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let : IsCyclic c.S0 := c.S0_cyclic
    have hpc : IsCyclic (pCore 2 c.Hhat) := by
      apply isCyclic_of_injective f
      intro x y hxy
      have hxyG : ((f x : c.S0) : G) = ((f y : c.S0) : G) :=
        congrArg Subtype.val hxy
      have hxyG' : ((x : c.Hhat) : G) = ((y : c.Hhat) : G) := by
        simpa [f] using hxyG
      apply Subtype.ext
      apply Subtype.ext
      exact hxyG'
    let : IsKleinFour (pCore 2 c.Hhat) := hK4
    exact False.elim (IsKleinFour.not_isCyclic hpc)

public theorem firstCase_commutator_S0_U_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H) :
    ⁅c.S0, c.U⁆ ≠ ⊥ := by
  intro hcomm
  apply (lemma_2_2 hmin c).1
  refine ⟨(Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm, ?_⟩
  intro s hs
  obtain ⟨I, hI, _hHall⟩ := hfirst.1 s hs
  have hnormal :=
    centralizerSetup_reflection_invertedSubgroup_abelian_normal c hs hI
  refine ⟨I, hI, hnormal.2.1, ?_⟩
  intro X hXne hXI
  have hXleFU : X ≤ c.FU := hXI.trans hnormal.2.2
  have hNX := hfirst.2 X hXne hXleFU
  simpa [hHhat] using hNX

public theorem firstCase_lemma29Hypothesis
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H) :
    Lemma29Hypothesis c := by
  intro s X hsS hXne hXU hcomm
  have hinverted : ∀ r : G, c.IsReflection r →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U r := by
    intro r hr
    obtain ⟨I, hI, _hHall⟩ := hfirst.1 r hr
    exact ⟨I, hI⟩
  have hXleFU : X ≤ c.FU := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hsS) hXU).trans
      (lemma_2_8_commutator_le_FU c hinverted)
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  have hNleHhat : N ≤ c.Hhat := hfirst.2 X hXne hXleFU
  have hNleH : N ≤ c.H := by simpa [hHhat] using hNleHhat
  let T : Subgroup G := Subgroup.zpowers c.t
  have htN : c.t ∈ N := by
    apply (Subgroup.centralizer_le_normalizer (X : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH : x ∈ c.H :=
      (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) (hXU hx)
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hxH
    exact hxH
  have hTleN : T ≤ N := Subgroup.zpowers_le.mpr htN
  have hNcentral : N ≤ Subgroup.centralizer (T : Set G) := by
    intro n hn z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨k, rfl⟩
    have hnH : n ∈ c.H := hNleH hn
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hnH
    have hcomm : Commute n c.t := hnH
    exact (hcomm.zpow_right k).eq.symm
  have hTnormal : (T.subgroupOf N).Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (H := N) (N := T)
      (hNcentral.trans (Subgroup.centralizer_le_normalizer (T : Set G)))
  have htord : orderOf c.t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using c.t_involution.2) c.t_involution.1
  have hTp : IsPGroup 2 T :=
    IsPGroup.of_card (n := 1) (by simp [T, Nat.card_zpowers, htord])
  have hTcore : T ≤ qCoreOf N 2 :=
    le_qCoreOf_of_normal_isPGroup N T 2 hTleN hTnormal hTp
  have htwo : twoCoreOf N = qCoreOf N 2 := by
    rw [twoCoreOf_eq_piCoreOf_2,
      qCoreOf_eq_piCoreOf_singleton N 2 Nat.prime_two]
  rw [htwo]
  exact hTcore (Subgroup.mem_zpowers c.t)

public structure FirstCaseBGData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) where
  bg : BenderGlauberman.Hyp11 G
  m_eq : bg.m = c.m
  S_eq : (bg.S : Subgroup G) = (c.S : Subgroup G)
  S0_eq : bg.S0 = c.S0
  H_eq : bg.H = c.H
  t_eq : bg.t = c.t
  I1 : Subgroup G
  I2 : Subgroup G
  I1_inverted : IsInvertedSubgroup I1 c.U bg.t1
  I2_inverted : IsInvertedSubgroup I2 c.U bg.t2
  I1_hall : IsHallIn I1 c.FU
  I2_hall : IsHallIn I2 c.FU

public theorem exists_firstCaseBGData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c) :
    Nonempty (FirstCaseBGData c) := by
  classical
  have hone := fact_2_preamble_involutions_conjugate_proved hmin
  have hHSU := fact_2_preamble_H_eq_SU_proved hmin c
  have hS0neS : c.S0 ≠ (c.S : Subgroup G) := by
    intro hEq
    have hcardEq : Nat.card c.S = Nat.card c.S0 := by rw [hEq]
    have hindex := c.S_index_two
    rw [hcardEq] at hindex
    have hpos : 0 < Nat.card c.S0 := Nat.card_pos
    omega
  have hnotle : ¬ (c.S : Subgroup G) ≤ c.S0 := by
    intro hle
    exact hS0neS (le_antisymm c.S0_le_S hle)
  obtain ⟨s, hsS, hsnot⟩ := Set.not_subset.mp hnotle
  obtain ⟨a, ha⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top c.S0).mp c.S0_cyclic
  have haS0 : a ∈ c.S0 := by
    rw [← ha]
    exact Subgroup.mem_zpowers a
  have haS : a ∈ (c.S : Subgroup G) := c.S0_le_S haS0
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c ⟨hsS, hsnot⟩
  let t2 : G := s * a
  have ht2S : t2 ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).mul_mem hsS haS
  have ht2not : t2 ∉ c.S0 := by
    intro ht2
    apply hsnot
    have hs0 : t2 * a⁻¹ ∈ c.S0 := c.S0.mul_mem ht2 (c.S0.inv_mem haS0)
    simpa [t2, mul_assoc] using hs0
  have ht2Inv : IsInvolution t2 :=
    centralizerSetup_reflection_isInvolution c ⟨ht2S, ht2not⟩
  have htprod : s * t2 = a := by
    have hss : s * s = 1 := by simpa [pow_two] using hsInv.2
    calc
      s * t2 = s * (s * a) := rfl
      _ = (s * s) * a := (mul_assoc s s a).symm
      _ = a := by rw [hss]; simp
  let bg : BenderGlauberman.Hyp11 G := {
    S := c.S
    m := c.m
    one_le_m := c.one_le_m
    dihedralEquiv := c.dihedralEquiv
    S0 := c.S0
    S0_le_S := c.S0_le_S
    S0_cyclic := c.S0_cyclic
    S_index_two := c.S_index_two
    t := c.t
    t_mem_S0 := c.t_mem_S0
    t_involution := c.t_involution
    one_involution_class := hone
    s := s
    s_mem_S := hsS
    s_not_mem_S0 := hsnot
    s_involution := hsInv
    t1 := s
    t2 := t2
    t1_mem_S := hsS
    t1_not_mem_S0 := hsnot
    t1_involution := hsInv
    t2_mem_S := ht2S
    t2_not_mem_S0 := ht2not
    t2_involution := ht2Inv
    S0_eq_zpowers := by rw [htprod]; exact ha.symm
    H := c.H
    H_eq_centralizer := c.H_eq_centralizer
    H_eq_US := by simpa [CentralizerSetup.U, sup_comm] using hHSU
  }
  obtain ⟨I1, hI1, hHall1⟩ := hfirst.1 bg.t1 (by
    change s ∈ (c.S : Subgroup G) ∧ s ∉ c.S0
    exact ⟨hsS, hsnot⟩)
  obtain ⟨I2, hI2, hHall2⟩ := hfirst.1 bg.t2 (by
    change t2 ∈ (c.S : Subgroup G) ∧ t2 ∉ c.S0
    exact ⟨ht2S, ht2not⟩)
  exact ⟨{
    bg := bg
    m_eq := rfl
    S_eq := rfl
    S0_eq := rfl
    H_eq := rfl
    t_eq := rfl
    I1 := I1
    I2 := I2
    I1_inverted := hI1
    I2_inverted := hI2
    I1_hall := hHall1
    I2_hall := hHall2
  }⟩

@[expose] public noncomputable def firstCaseBGKData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (d : FirstCaseBGData c) :
    BenderGlauberman.Hyp11KData d.bg := by
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2
      (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hUleH : c.U ≤ c.H :=
    Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)
  have hI1leU : d.I1 ≤ c.U := by
    intro x hx
    have hx' : x ∈ invertedElements c.U d.bg.t1 := by
      rw [← d.I1_inverted]
      exact hx
    exact hx'.1
  have hI2leU : d.I2 ≤ c.U := by
    intro x hx
    have hx' : x ∈ invertedElements c.U d.bg.t2 := by
      rw [← d.I2_inverted]
      exact hx
    exact hx'.1
  have hI1odd : Nat.Coprime 2 (Nat.card d.I1) :=
    hUodd.coprime_dvd_right (Subgroup.card_dvd_of_le hI1leU)
  have hI2odd : Nat.Coprime 2 (Nat.card d.I2) :=
    hUodd.coprime_dvd_right (Subgroup.card_dvd_of_le hI2leU)
  exact {
    K1 := d.I1
    K2 := d.I2
    K1_le_H := by simpa [d.H_eq] using hI1leU.trans hUleH
    K2_le_H := by simpa [d.H_eq] using hI2leU.trans hUleH
    K1_odd := hI1odd
    K2_odd := hI2odd
    K1_inverted := by
      intro x hx
      have hx' : x ∈ invertedElements c.U d.bg.t1 := by
        rw [← d.I1_inverted]
        exact hx
      exact hx'.2
    K2_inverted := by
      intro x hx
      have hx' : x ∈ invertedElements c.U d.bg.t2 := by
        rw [← d.I2_inverted]
        exact hx
      exact hx'.2
    K1_maximal := by
      intro X hXH hXodd hXinv x hx
      have hXH' : X ≤ c.H := by simpa [d.H_eq] using hXH
      have hXU : X ≤ c.U :=
        odd_order_subgroup_le_U_of_H_eq_SU hmin c hXH' hXodd
      have hx' : x ∈ invertedElements c.U d.bg.t1 := ⟨hXU hx, hXinv x hx⟩
      rw [← d.I1_inverted] at hx'
      exact hx'
    K2_maximal := by
      intro X hXH hXodd hXinv x hx
      have hXH' : X ≤ c.H := by simpa [d.H_eq] using hXH
      have hXU : X ≤ c.U :=
        odd_order_subgroup_le_U_of_H_eq_SU hmin c hXH' hXodd
      have hx' : x ∈ invertedElements c.U d.bg.t2 := ⟨hXU hx, hXinv x hx⟩
      rw [← d.I2_inverted] at hx'
      exact hx'
  }


end CFSG.GorensteinWalter
