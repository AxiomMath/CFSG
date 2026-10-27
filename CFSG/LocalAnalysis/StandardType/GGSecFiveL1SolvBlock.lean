module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1SolvDefs
public import CFSG.LocalAnalysis.StandardType.GGAllFixedSC
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientSolvable
public import CFSG.LocalAnalysis.StandardType.GGQTwoCentralizerLift
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapBasic
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E4Inner
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanProjection
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E3Conj
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn
public import CFSG.Quasithin.Vol2.Ch4Sec4W446

public section

namespace CFSG.StandardType.SecFiveL1Solv

open CFSG.Assembly CFSG.Quasithin CFSG.StandardType.SecFiveL1Odd
open scoped Pointwise commutatorElement

theorem commonKernel {G : Type*} [Group G] {H V X : Subgroup G}
    (hHV : H ≤ V) (hV : V ≤ H ⊔ X) :
    Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (H : Set G) =
      Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
  apply le_antisymm
  ·
    refine le_inf inf_le_left ?_
    have h1 : Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (H : Set G) ≤
        Subgroup.centralizer ((H ⊔ X : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mpr (sup_le
        (Subgroup.le_centralizer_iff.mpr inf_le_right)
        (Subgroup.le_centralizer_iff.mpr inf_le_left))
    exact h1.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV))
  ·
    refine le_inf inf_le_left ?_
    exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hHV))

section PerfectCentralizes

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_perfect_of_solvable_fixed {V X Q : Subgroup G}
    (hVN : V ≤ Subgroup.normalizer (X : Set G))
    (hQV : Q ≤ Subgroup.centralizer (V : Set G))
    (hQperf : ⁅Q, Q⁆ = Q)
    (hinner : Q ≤ X ⊔ Subgroup.centralizer (X : Set G))
    (hsolv : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (V : Set G))) :
    Q ≤ Subgroup.centralizer (X : Set G) := by
  set K : Subgroup G := X ⊓ Subgroup.centralizer (V : Set G) with hK
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hQK : Q ≤ K ⊔ C := SecFiveRk1C.le_inf_centralizer_sup_of_perfect hVN hQV hQperf hinner
  have hKN : K ≤ Subgroup.normalizer (C : Set G) :=
    inf_le_left.trans
      (Subgroup.le_normalizer.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer X))
  have hYN : K ⊔ C ≤ Subgroup.normalizer (C : Set G) :=
    sup_le hKN Subgroup.le_normalizer
  have hA : (C.subgroupOf (K ⊔ C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hYN
  have hcore : perfectCore (K ⊔ C) ≤ C :=
    perfectCore_le_of_sup_solvable (A := C) (B := K) (Y := K ⊔ C)
      le_sup_right hA (sup_comm K C) (by rw [hK]; exact hsolv)
  exact (le_perfectCore_of_perfect hQK hQperf).trans hcore

end PerfectCentralizes

section TheoremOKernel

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem false_of_two_subgroup_le_centralizer_ggG0
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hpJ : p ∣ Nat.card J)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hT : T ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G))
    (hT0 : T ≤ Subgroup.centralizer (ggG0 p B x L D J : Set G)) :
    False := by
  have hI : GGThmIHyp p B x L := hcfg.1.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.1.1.2.2
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hPU : GGPumpupInput := ggPumpupInput_of_lBalance hL
  have hG0T : ggG0 p B x L D J ≤ Subgroup.centralizer (T : Set G) :=
    Subgroup.le_centralizer_iff.mp hT0
  obtain ⟨d, hdD, hd1, hne⟩ := exists_commutator_ne_bot hcfg hT2 hT1 hT
  apply hne
  by_cases hdx : d ∈ Subgroup.zpowers x
  ·
    have hx1 : x ≠ 1 := hS.2.2.1
    have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
    have hox : orderOf x = p := orderOf_eq_prime hxp hx1
    have hod : orderOf d = p := by
      have hdvd : orderOf d ∣ p := hox ▸ orderOf_dvd_of_mem_zpowers hdx
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hd1
      · exact h
    have hzeq : Subgroup.zpowers d = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdx)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hod, hox])
    have hCd : Subgroup.centralizer ({d} : Set G) = Subgroup.centralizer ({x} : Set G) := by
      rw [← Subgroup.centralizer_closure ({d} : Set G),
        ← Subgroup.centralizer_closure ({x} : Set G),
        ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, hzeq]
    have hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({d} : Set G)) :=
      hCd ▸ hS.2.2.2.1
    exact commutator_eq_bot_of_component hT2 hLc (J_le hL hcfg hpJ (Or.inl rfl))
      ((le_sup_left : L ≤ ggG0 p B x L D J).trans hG0T)
  ·
    have hD := eq_closure_pair_of_mem hI hDJ hdD hdx
    rcases ggNbr_or_eq_sup_of_stdSub hPU hI hDJ hpJ hD with hN | hcov
    ·
      have hKc := (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hN)).1
      exact commutator_eq_bot_of_component hT2 hKc (le_of_ggNbr hL hI hDJ hpJ hN)
        ((le_ggG0_of_ggNbr hN).trans hG0T)
    ·
      exact commutator_eq_bot_of_cover ha₀ hL hcfg hpJ hD hcov hT2 hT

theorem eq_bot_of_perfect_le_centralizer_ggG0
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hpJ : p ∣ Nat.card J) {R : Subgroup G}
    (hRperf : ⁅R, R⁆ = R)
    (hR : R ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G))
    (hR0 : R ≤ Subgroup.centralizer (ggG0 p B x L D J : Set G)) :
    R = ⊥ := by
  by_contra hRne
  have hnotodd : ¬ Odd (Nat.card R) := by
    intro hodd
    have hsolv : Group.IsSolvable ↥R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hbot : perfectCore R = ⊥ := (isSolvable_iff_perfectCore_eq_bot R).mp hsolv
    rw [perfectCore_eq_self_of_perfect hRperf] at hbot
    exact hRne hbot
  have h2 : 2 ∣ Nat.card R := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnotodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  set T : Subgroup G := Subgroup.zpowers (t : G) with hTdef
  have hT2 : IsPGroup 2 T :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  have hT1 : T ≠ ⊥ := by
    intro h
    have h1 : (t : G) = 1 := Subgroup.zpowers_eq_bot.mp h
    rw [h1, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have hT : T ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G) :=
    (Subgroup.zpowers_le).mpr (hR t.2)
  have hT0 : T ≤ Subgroup.centralizer (ggG0 p B x L D J : Set G) :=
    (Subgroup.zpowers_le).mpr (hR0 t.2)
  exact false_of_two_subgroup_le_centralizer_ggG0 ha₀ hL hcfg hpJ hT2 hT1 hT hT0

end TheoremOKernel

section Bridge

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem bstar_solvable_of_all_fixed_solvable
    (ha₀ : GGLNoncyclicInput) (hLB : GGLBalanceInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hpJ : p ∣ Nat.card J)
    (hfixed : ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
      Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)))
    (hOut : ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
      CFSG.Quasithin.OutSolvable ↥X) :
    Group.IsSolvable ↥(Subgroup.centralizer (Bs : Set G)) := by
  set R : Subgroup G := perfectCore (Subgroup.centralizer (Bs : Set G)) with hRdef
  have hRperf : ⁅R, R⁆ = R := perfectCore_perfect _
  have hRv : R ≤ Subgroup.centralizer (Bs : Set G) := perfectCore_le _
  have hBsNorm : ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
      Bs ≤ Subgroup.normalizer (X : Set G) := by
    intro X hX
    rcases hX with rfl | ⟨y, hy⟩
    · exact GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
    · exact GGDichotomy.le_normalizer_of_innerDiagOn (hcfg.1.2.2.1.2 y X hy)
  have hCDNorm : ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
      Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    intro X hX
    rcases hX with rfl | ⟨y, hy⟩
    · exact SecFiveL1Odd.centralizer_le_normalizer_L ha₀ hcfg
    · exact SecFiveL1Odd.centralizer_le_normalizer_nbr ha₀ hLB hcfg hpJ hy
  have hcentral : ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
      R ≤ Subgroup.centralizer (X : Set G) := by
    intro X hX
    have hRVX : R ≤ Subgroup.normalizer (X : Set G) :=
      hRv.trans ((Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (SecFiveL1Odd.le_bstar hcfg))).trans (hCDNorm X hX))
    have hinner : R ≤ X ⊔ Subgroup.centralizer (X : Set G) :=
      CFSG.Quasithin.H13.Ch4.E443.le_sup_centralizer_of_outSolvable
        (K := X) (X := R) (hOut X hX) hRVX hRperf
    exact centralizes_of_perfect_of_solvable_fixed (V := Bs) (X := X) (Q := R)
      (hBsNorm X hX) hRv hRperf hinner (hfixed X hX)
  have hR0 : R ≤ Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    change L ⊔ (⨆ (y : G) (K : Subgroup G)
        (_ : LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J), K) ≤
      Subgroup.centralizer (R : Set G)
    refine sup_le ?_ (iSup_le fun y => iSup_le fun K => iSup_le fun hyK => ?_)
    · exact Subgroup.le_centralizer_iff.mp (hcentral L (Or.inl rfl))
    · exact Subgroup.le_centralizer_iff.mp (hcentral K (Or.inr ⟨y, hyK⟩))
  have hR : R ≤ Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (J : Set G) := by
    refine le_inf ?_ ?_
    · exact hRv.trans (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (SecFiveL1Odd.le_bstar hcfg)))
    · exact (hcentral L (Or.inl rfl)).trans (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (SecFiveL1Odd.J_le hLB hcfg hpJ (Or.inl rfl))))
  have hbot : R = ⊥ := eq_bot_of_perfect_le_centralizer_ggG0 ha₀ hLB hcfg hpJ hRperf hR hR0
  exact (isSolvable_iff_perfectCore_eq_bot (Subgroup.centralizer (Bs : Set G))).mpr hbot

end Bridge

end CFSG.StandardType.SecFiveL1Solv

end
