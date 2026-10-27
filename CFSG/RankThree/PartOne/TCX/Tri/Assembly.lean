module

public import CFSG.RankThree.PartOne.TCX.Tri.Group
public import CFSG.RankThree.PartOne.TCX.Tri.Parabolic
public import CFSG.RankThree.PartOne.TCX.Tri.StdForm
public import CFSG.RankThree.PartOne.TCX.AssemblyTools
public import CFSG.RankThree.PartOne.TCX.Transport
public import CFSG.RankThree.PartOne.TCX.Interface
public import CFSG.RankThree.PartOne.S11c.Sec66PSUFrame
public import CFSG.RankThree.PartOne.K128.D4Syl

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KLC
open CFSG.LieType.BorelTits (Holds holds_of_twistedChevalleyModel)

open CFSG.RankThree.PartOne.KE (cycloVal cycloVal_twelve)

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.RankThree.PartOne.TCX

section Main


theorem threeCompT_trialityD4 : ThreeCompT .trialityD4 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKf, hKfin, σ, δ₀, φ, hKcard, hσ, hδ₀, hδ₀ord, hzp⟩ :=
    stdForm_trialityD4 hp hp5 hM hαp hαinn
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hm1 : 1 ≤ p * f₀ := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  have hH : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 2 :=
    (holds_of_twistedChevalleyModel hm1 hch.2).of_mulEquiv φ
  have hpf : 1 ≤ 3 * (p * f₀) := by omega
  have hK' : Nat.card K = 2 ^ (3 * (p * f₀)) := by rw [hKcard, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf
      hK'
  obtain ⟨α', hα'def⟩ : ∃ α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      α' = MulAut.congr φ α := ⟨_, rfl⟩
  rw [← hα'def] at hzp
  have hαφ : ∀ t, α' (φ t) = φ (α t) := fun t => by
    rw [hα'def]
    exact congrArg φ (congrArg α (φ.symm_apply_apply t))
  have hα'p : α' ^ p = 1 := by rw [hα'def, ← map_pow, hαp, map_one]
  have hα'out : α' ∉ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [hα'def]
    exact fun h => hαinn ((mem_innerAut_congr φ α).mp h)
  have hLRG : LocalRankAut p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) α' := by
    rw [hα'def]
    exact localRankAut_congr φ hp hLRA
  have hβmem : fieldActor (t := TwistTag.D4) σ δ₀ ∈ Subgroup.zpowers α' := by
    rw [hzp]
    exact Subgroup.mem_zpowers _
  have hβp : fieldActor (t := TwistTag.D4) σ δ₀ ^ p = 1 := by
    have h1 : orderOf (fieldActor (t := TwistTag.D4) σ δ₀) ∣ orderOf α' :=
      orderOf_dvd_of_mem_zpowers hβmem
    have h2 : orderOf α' ∣ p := orderOf_dvd_of_pow_eq_one hα'p
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans h2)
  have hxφ : φ x ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hxφ1 : φ x ≠ 1 := fun h => hx1 (φ.injective (by rw [h, map_one]))
  have hxo : orderOf (φ x) = p := orderOf_eq_prime hxφ hxφ1
  have hα'x : α' (φ x) = φ x := by rw [hαφ, hαx]
  have hβx : fieldActor (t := TwistTag.D4) σ δ₀ (φ x) = φ x := fixed_of_zpowers_eq hzp.symm hα'x
  have hpT : p ∣ Nat.card T := dvd_card_of_pRank_pos hp (by omega)
  obtain ⟨m, hmem, hdvd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp
    (by omega) (by omega : 2 ≠ p) hch).1 hpT).2.2.2.2 rfl
  have hd : (p : ℤ) ∣ cycloVal m 2 (p * f₀) := hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hq1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_pow _ _ (by norm_num)
  have hq1' : 1 ≤ 2 ^ f₀ := Nat.one_le_pow _ _ (by norm_num)
  have hQ : 2 ^ (p * f₀) = (2 ^ f₀) ^ p := by rw [← pow_mul, mul_comm]
  by_cases h12 : m = 12
  ·
    exfalso
    subst h12
    rw [cycloVal_twelve] at hd
    have hpd : p ∣ (2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 := by
      have h24 : (2 ^ (p * f₀)) ^ 2 ≤ (2 ^ (p * f₀)) ^ 4 :=
        Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        exact hd
      exact_mod_cast h1
    have h1 := pRank_le_one_D4_twelve Nat.prime_two hm1 K hKcard σ hσ hp hp5 hpd
    have h2 := pRank_eq_of_mulEquiv_of_one_lt hp.one_lt φ
    omega
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
  have hpdQ : p ∣ phiNat m (2 ^ (p * f₀)) := dvd_phiNat_of_dvd_cycloVal hq1 hm' hd
  have hpdq : p ∣ phiNat m (2 ^ f₀) := by
    refine dvd_phiNat_of_dvd_pow hp hq1' hm' ?_
    rw [← hQ]
    exact hpdQ
  have hcases := tri_group_cases hp hp5 hf₀ hKcard hσ hδ₀ hδ₀ord hm' hpdq hxo hβx
  have hcases' : RegularShape (2 ^ (p * f₀)) (φ x) ∨
      SingleLayerData p (fieldActor (t := TwistTag.D4) σ δ₀)
        (Subgroup.centralizer ({φ x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
    rcases hcases with ⟨R, U, hR, hRc, hRfix, hU, hU2, hUα, hRU⟩ | h
    · exfalso
      have hstab := mem_stabSubgroup_of_zpowers_eq hp.pos hzp hβp hUα
      exact hLRG hα'p hα'out R hR hRc (fun r hr => fixed_of_zpowers_eq hzp (hRfix r hr)) U hU hU2
        hstab.1 hRU
    · exact h
  have hlayer : SingleLayerData p (fieldActor (t := TwistTag.D4) σ δ₀)
      (Subgroup.centralizer ({φ x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) →
      SingleLayerData p α (Subgroup.centralizer ({x} : Set T)) := fun hlay => by
    have hlay' : SingleLayerData p α'
        ((Subgroup.centralizer ({x} : Set T)).map φ.toMonoidHom) := by
      rw [map_centralizer_singleton_mulEquiv']
      exact singleLayerData_of_zpowers_eq hp.pos hzp hβp hlay
    exact singleLayerData_of_mulEquiv (p := p) φ hαφ hlay'
  refine ⟨fun D hD hDst => ?_, fun S hS hS2 hSα hxS => ?_⟩
  · rcases hcases' with hreg | hlay
    · exact (no_component_of_comm (centralizer_comm_of_map φ hreg.1) hD).elim
    · obtain ⟨D₀, hD₀, hst, huniq, hfix, hclaims⟩ := hlayer hlay
      have hDD₀ := huniq D hD
      subst hDD₀
      exact hclaims
  · rcases hcases' with hreg | hlay
    ·
      exfalso
      have hSG : S.map φ.toMonoidHom ≠ ⊥ := fun hbot =>
        hS ((Subgroup.map_eq_bot_iff_of_injective S φ.injective).mp hbot)
      obtain ⟨z, hz, hzo⟩ := tri_exists_centralizer_elt hm1 hKcard hσ hH hp (by omega) hxo hSG
        (hS2.map φ.toMonoidHom) (normalizer_map_of_mem φ hxS)
      have hz36 : z ^ 36 = 1 := hreg.2 z hz (by rw [← hzo]; exact pow_orderOf_eq_one z)
      have hdvd36 : 2 ^ (p * f₀) - 1 ∣ 36 := by
        rw [← hzo]
        exact orderOf_dvd_of_pow_eq_one hz36
      have h36 : 2 ^ (p * f₀) - 1 ≤ 36 := Nat.le_of_dvd (by norm_num) hdvd36
      have h5 : 5 ≤ p * f₀ := by nlinarith
      rcases Nat.eq_or_lt_of_le h5 with h | h
      · rw [← h] at hdvd36
        norm_num at hdvd36
      · have h6 : 2 ^ 6 ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) h
        omega
    · obtain ⟨D₀, hD₀, hst, huniq, hfix, -⟩ := hlayer hlay
      exact ⟨D₀, hD₀, hst, huniq, hfix⟩

end Main

end CFSG.RankThree.PartOne.TCX.Tri
