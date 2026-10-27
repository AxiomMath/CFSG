module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxDefs
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Model
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2U
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4G2Aux
import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4
import CFSG.LieType.SteinbergBROddLinearThreeParabolic
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayerAux

public section

open CFSG.RankThree.PartTwo.Sec19
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Leaves


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot CFSG.LieType.SeitzGeneration

theorem layer_fixed_of_perfect_card [Finite (C0 σ)] {x : C0 σ} (M : Subgroup (C0 σ))
    (hM : M ≤ cenX σ x) (hMG : M ≤ Gsub σ) (hperf : Group.IsPerfect M)
    (hcard : Nat.card (layerSub σ x) ≤ Nat.card M) : ∀ d ∈ layerSub σ x, tauAut σ d = d := by
  have hMD : M ≤ layerSub σ x := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
      _ ≤ ⁅cenX σ x, cenX σ x⁆ := Subgroup.commutator_mono hM hM
  have hEq : M = layerSub σ x := Subgroup.eq_of_le_of_card_ge hMD hcard
  intro d hd
  have hdM : d ∈ M := by rw [hEq]; exact hd
  exact hMG hdM

theorem exists_g2_short_preimage (P : D4Par n X σ) (hK : ringChar X = 2) {x : C0 σ}
    (hx : IsClassX σ x) (hxA : x ∈ A0sub σ) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ),
      KFacts.trialityG2Incl σ hK (g2RootSL2 g2s (fixSubfield σ) s) = x ∧
      (g2RootSL2 g2s (fixSubfield σ) s) ^ 3 = 1 ∧ g2RootSL2 g2s (fixSubfield σ) s ≠ 1 := by
  obtain ⟨s, hs⟩ := (mem_A0sub_iff P).mp hxA
  have hinj := KFacts.trialityG2Incl_injective σ hK
  have hxz : KFacts.trialityG2Incl σ hK (g2RootSL2 g2s (fixSubfield σ) s) = x := by
    rw [hs]
    exact DFunLike.congr_fun (g2RootSL2_short_hom_eq σ P hK) s
  refine ⟨s, hxz, hinj (by rw [map_pow, hxz, hx.1, map_one]), fun h => hx.2.1 ?_⟩
  rw [← hxz, h, map_one]

theorem conj_pow_three_ne_one {G : Type*} [Group G] (m z : G) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    (m * z * m⁻¹) ^ 3 = 1 ∧ m * z * m⁻¹ ≠ 1 := by
  refine ⟨?_, fun h => hz1 ?_⟩
  · rw [TorusLayerAux.pow_conj_eq, hz3]
    group
  · have : z = m⁻¹ * (m * z * m⁻¹) * m := by group
    rw [this, h]
    group

theorem g2_layer_even (P : D4Par n X σ) (hn : 2 ≤ n) (hev : Even n) {x : C0 σ} (hx : IsClassX σ x)
    (hxA : x ∈ A0sub σ) :
    ∃ M : Subgroup (C0 σ), M ≤ cenX σ x ∧ M ≤ Gsub σ ∧ Group.IsPerfect M ∧
      Nat.card M = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  haveI := P.charP
  have hK : ringChar X = 2 := ringChar.eq X 2
  have hn1 : 1 ≤ n := by omega
  have hkc : Nat.card (fixSubfield σ) = 2 ^ n := KFacts.card_fixSubfield_of_cube hn1 P.card P.frob
  have hinj := KFacts.trialityG2Incl_injective σ hK
  obtain ⟨s, hxz, hz₁3, hz₁1⟩ := exists_g2_short_preimage P hK hx hxA
  set z₁ := g2RootSL2 g2s (fixSubfield σ) s with hz₁
  obtain ⟨hz3, hz1⟩ := conj_pow_three_ne_one (g2WeylRep (fixSubfield σ)) z₁ hz₁3 hz₁1
  have hzS : g2WeylRep (fixSubfield σ) * z₁ * (g2WeylRep (fixSubfield σ))⁻¹ ∈
      KS11Lie4Proof.g2ShortSL2 (fixSubfield σ) := conj_g2RootSL2_short_mem (fixSubfield σ) s
  have h31 : 3 ∣ Nat.card (fixSubfield σ) - 1 := by
    rw [hkc]
    obtain ⟨m, hm⟩ := hev
    have h1 : 2 ^ n % 3 = 1 := by
      rw [hm, ← two_mul]
      exact TorusLayerAux.two_pow_mod_three_even m
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_SL3 h31 hzS hz3 hz1
  have eC : Subgroup.centralizer ({z₁} : Set (adjointGroup .G2 (fixSubfield σ))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (fixSubfield σ) :=
    (centralizerConjEquiv (g2WeylRep (fixSubfield σ)) z₁).trans e
  let M : Subgroup (C0 σ) :=
    (Subgroup.centralizer ({z₁} : Set (adjointGroup .G2 (fixSubfield σ)))).map
      (KFacts.trialityG2Incl σ hK)
  have eM : Matrix.SpecialLinearGroup (Fin 3) (fixSubfield σ) ≃* M :=
    eC.symm.trans ((Subgroup.centralizer ({z₁} : Set (adjointGroup .G2 (fixSubfield σ)))).equivMapOfInjective
      (KFacts.trialityG2Incl σ hK) hinj)
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ Subgroup.centralizer ({z₁} : Set (adjointGroup .G2 (fixSubfield σ))) := hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
    rw [← hxz, ← map_mul, ← map_mul, hg']
  · rintro _ ⟨g, hg, rfl⟩
    rw [← gsub_eq_range_g2Incl σ hK]
    exact ⟨g, rfl⟩
  · exact (CFSG.LocalCores.isQuasisimple_of_mulEquiv eM
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))).1
  · rw [← Nat.card_congr eM.toEquiv, CFSG.LieType.SteinbergBR.BlockPar.card_SL_three', hkc]

theorem g2_layer_odd (P : D4Par n X σ) (hn : 2 ≤ n) (hodd : Odd n) {x : C0 σ} (hx : IsClassX σ x)
    (hxA : x ∈ A0sub σ) :
    ∃ M : Subgroup (C0 σ), M ≤ cenX σ x ∧ M ≤ Gsub σ ∧ Group.IsPerfect M ∧
      Nat.card M = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
  haveI := P.charP
  have hK : ringChar X = 2 := ringChar.eq X 2
  have hn1 : 1 ≤ n := by omega
  have hkc : Nat.card (fixSubfield σ) = 2 ^ n := KFacts.card_fixSubfield_of_cube hn1 P.card P.frob
  have hinj := KFacts.trialityG2Incl_injective σ hK
  obtain ⟨s, hxz, hz₁3, hz₁1⟩ := exists_g2_short_preimage P hK hx hxA
  set z₁ := g2RootSL2 g2s (fixSubfield σ) s with hz₁
  obtain ⟨hz3, hz1⟩ := conj_pow_three_ne_one (g2WeylRep (fixSubfield σ)) z₁ hz₁3 hz₁1
  have hzS : g2WeylRep (fixSubfield σ) * z₁ * (g2WeylRep (fixSubfield σ))⁻¹ ∈
      KS11Lie4Proof.g2ShortSL2 (fixSubfield σ) := conj_g2RootSL2_short_mem (fixSubfield σ) s
  have h3 : 3 ∣ Nat.card (fixSubfield σ) + 1 := by
    rw [hkc]
    obtain ⟨m, hm⟩ := hodd
    have h1 : 2 ^ n % 3 = 2 := by
      rw [hm]
      exact TorusLayerAux.two_pow_mod_three_odd m
    omega
  have hk4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hkc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq := KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 hk4 hzS hz3 hz1
  have hcard := card_centralizer_short_unitary hn1 hkc h3 hzS hz3 hz1
  let eC := centralizerConjEquiv (g2WeylRep (fixSubfield σ)) z₁
  let M : Subgroup (C0 σ) :=
    (Subgroup.centralizer ({z₁} : Set (adjointGroup .G2 (fixSubfield σ)))).map
      (KFacts.trialityG2Incl σ hK)
  have eM : Subgroup.centralizer ({g2WeylRep (fixSubfield σ) * z₁ * (g2WeylRep (fixSubfield σ))⁻¹} :
      Set (adjointGroup .G2 (fixSubfield σ))) ≃* M :=
    eC.symm.trans ((Subgroup.centralizer ({z₁} : Set (adjointGroup .G2 (fixSubfield σ)))).equivMapOfInjective
      (KFacts.trialityG2Incl σ hK) hinj)
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ Subgroup.centralizer ({z₁} : Set (adjointGroup .G2 (fixSubfield σ))) := hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
    rw [← hxz, ← map_mul, ← map_mul, hg']
  · rintro _ ⟨g, hg, rfl⟩
    rw [← gsub_eq_range_g2Incl σ hK]
    exact ⟨g, rfl⟩
  · exact (CFSG.LocalCores.isQuasisimple_of_mulEquiv eM hq).1
  · rw [← Nat.card_congr eM.toEquiv, hcard]

theorem layer_card_odd (P : D4Par n X σ) (hn : 2 ≤ n) (hodd : Odd n) {x : C0 σ} (hx : IsClassX σ x) :
    Nat.card (layerSub σ x) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
  obtain ⟨h, U, hU, ⟨e⟩⟩ := layer_model_odd P hn hodd hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := P.charP
  haveI : CharP (AlgebraicClosure X) 2 :=
    charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective 2
  rw [← card_layer_conj h x, Nat.card_congr e.toEquiv]
  exact card_subgroup_unitarySet (ℓ := 2) (f := n) P.one_le U hU

theorem tau_fixes_layer (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x)
    (hxA : x ∈ A0sub σ) :
    ∀ d ∈ layerSub σ x,
      tauAut σ d = d := by
  haveI : Finite (C0 σ) := finite_C0
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨M, hMC, hMG, hMp, hMcard⟩ := g2_layer_even P hn hev hx hxA
    exact layer_fixed_of_perfect_card M hMC hMG hMp
      (by rw [layer_card_even P hn hev hx, hMcard])
  · obtain ⟨M, hMC, hMG, hMp, hMcard⟩ := g2_layer_odd P hn hodd hx hxA
    exact layer_fixed_of_perfect_card M hMC hMG hMp
      (by rw [layer_card_odd P hn hodd hx, hMcard])

end Leaves

end CFSG.RankThree.PartTwo.Sec4.E27
