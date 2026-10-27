module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.RealVirtualParity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 12: Theorem (12.12)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.12) -/

private theorem theorem_12_12_actor_card_dvd_group_card_sub_one
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : V, a • v = v → v = 1) :
    Nat.card A ∣ Nat.card V - 1 := by
  classical
  let V0 := {v : V // v ≠ 1}
  letI : MulAction A V0 :=
    { smul := fun a v => ⟨a • (v : V), by
        intro h
        apply v.2
        have h' := congrArg (fun x : V => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro v
        apply Subtype.ext
        change (1 : A) • (v : V) = (v : V)
        simp
      mul_smul := by
        intro a b v
        apply Subtype.ext
        change (a * b) • (v : V) = a • (b • (v : V))
        rw [mul_smul] }
  have hstab : ∀ v : V0, MulAction.stabilizer A v = ⊥ := by
    intro v
    rw [eq_bot_iff]
    intro a ha
    have hav : a • v = v := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hane : a ≠ 1 := by
      intro h
      apply ha1
      simp [h]
    exact v.2 (hfree a hane (v : V) (congrArg Subtype.val hav))
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardV0 : Nat.card V0 = Nat.card V - 1 := by
    letI : Fintype V := Fintype.ofFinite V
    letI : Fintype V0 := Fintype.ofFinite V0
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {v : V // v ≠ 1} = Fintype.card V - 1
    simp
  rw [hcardV0, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A V0)), by
    rw [mul_comm]
    exact hcard⟩

/-- The source-data package for PF `(12.12)` implies the public cyclicity and
divisibility conclusion for a complement `E`. -/
public theorem theorem_12_12_of_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (x : G)
    (p e : ℕ)
    (hsrc : theorem_12_12_source_data M K K' P0 L H Ls E x p e)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hcomp : section12ComplementIn L H E)
    (he : e = Nat.card E) :
    IsCyclic E ∧ (e ∣ p - 1 ∨ e ∣ p + 1) :=
  hsrc h128 h129 hfrob hcomp he

set_option maxHeartbeats 800000

/-- Source leaf for PF `(12.12)`: cyclicity of a complement `E` and the
divisibility alternative for `|E|`. -/
public theorem theorem_12_12_source_leaf
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (x : G)
    (p e : ℕ) :
    theorem_12_12_source_data M K K' P0 L H Ls E x p e := by
  classical
  intro h128 h129 hfrob hcomp he
  have hMLleH : M ⊓ L ≤ H :=
    (theorem_12_11 M K K' P0 L H Ls x p h128 h129 hfrob).2
  rcases h128 with
    ⟨hp, _hbad, _hmin, _hM, _hK, _hTypeIM, _hMsM, _hK', _hnoncyc,
      hP0Sylow⟩
  rcases h129 with
    ⟨hP0comm, hP0rank, _hL, hH, hLs, hP0Ls, _hxL,
      ⟨_hp', hxOmega, hxne⟩, _hCKnot, hNxM, _hCnotL⟩
  rcases hcomp with ⟨hHleL, hEleL, hLE, hdisjHE⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hP0Sylow with ⟨PM, hP0eq⟩
  have hP0M : P0 ≤ M := by
    rw [← hP0eq]
    exact section11_ambientSylow_le M PM
  have hP0p : IsPGroup p P0 := by
    rw [← hP0eq]
    dsimp [section10AmbientSylowSubgroup]
    exact IsPGroup.map (p := p) (H := (PM : Subgroup M)) PM.isPGroup' M.subtype
  have hLsL : Ls ≤ L := by
    rcases hLs with hEarly | hLate
    · rw [hEarly.2]
      exact section16MFSubgroup_le hH
    · rw [hLate.2]
      exact section12_ambientDerivedSubgroup_le
  have hP0L : P0 ≤ L := hP0Ls.trans hLsL
  have hP0H : P0 ≤ H :=
    (le_inf hP0M hP0L).trans hMLleH
  have hxP0 : x ∈ P0 := by
    rcases hxOmega with ⟨y, _hyOmega, hyx⟩
    have hyP0 : (y : G) ∈ P0 := y.property
    simpa using hyx ▸ hyP0
  let P : Subgroup G := (pCore p H).map H.subtype
  let P0H : Subgroup H := P0.subgroupOf H
  have hP0Hp : IsPGroup p P0H :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0H).symm
  have hP0HleCore : P0H ≤ pCore p H := by
    obtain ⟨S, hP0HleS⟩ :=
      IsPGroup.exists_le_sylow (G := H) (p := p) hP0Hp
    have hSnormal : (S : Subgroup H).Normal :=
      Group.IsNilpotent.sylow_normal hH.1.2.2.1 p S
    exact hP0HleS.trans (le_sSup ⟨hSnormal, S.isPGroup'⟩)
  have hP0P : P0 ≤ P := by
    intro y hy
    have hyP0H : (⟨y, hP0H hy⟩ : H) ∈ P0H := by
      simpa [P0H, Subgroup.mem_subgroupOf] using hy
    exact Subgroup.mem_map.mpr ⟨⟨y, hP0H hy⟩, hP0HleCore hyP0H, rfl⟩
  have hPp : IsPGroup p P := by
    simpa [P] using
      IsPGroup.map (p := p) (H := pCore p H)
        (pCore_isPGroup (G := H) (p := p)) H.subtype
  let B : Subgroup M := (P ⊓ M).subgroupOf M
  have hInfp : IsPGroup p (P ⊓ M : Subgroup G) := by
    have hlocal : IsPGroup p ((P ⊓ M).subgroupOf P) :=
      hPp.to_subgroup ((P ⊓ M).subgroupOf P)
    exact hlocal.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := P ⊓ M) (K := P) inf_le_left)
  have hBp : IsPGroup p B :=
    hInfp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := P ⊓ M) (K := M) inf_le_right).symm
  have hPMleB : (PM : Subgroup M) ≤ B := by
    intro y hy
    have hyP0 : (y : G) ∈ P0 := by
      rw [← hP0eq]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact ⟨hP0P hyP0, y.property⟩
  have hBeq : B = (PM : Subgroup M) := PM.is_maximal' hBp hPMleB
  have hPinfM : P ⊓ M = P0 := by
    apply le_antisymm
    · intro y hy
      let yM : M := ⟨y, hy.2⟩
      have hyB : yM ∈ B := hy
      rw [hBeq] at hyB
      rw [← hP0eq]
      exact Subgroup.mem_map.mpr ⟨yM, hyB, rfl⟩
    · exact le_inf hP0P hP0M
  let pp : Nat.Primes := ⟨p, hp⟩
  let T : Subgroup G := section10OmegaOneCenter pp P
  have hTP : T ≤ P := by
    simpa [T] using section10_omegaOneCenter_le P
  have hTcentralP : T ≤ Subgroup.centralizer (P : Set G) := by
    simpa [T] using section10_omegaOneCenter_le_centralizer P
  have hTP0 : T ≤ P0 := by
    rw [← hPinfM]
    refine le_inf hTP ?_
    intro t ht
    have htCentZpowers :
        t ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp (hTcentralP ht) y
        ((Subgroup.zpowers_le.mpr (hP0P hxP0)) hy)
    exact hNxM ((centralizer_le_normalizer (Subgroup.zpowers x)) htCentZpowers)
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hxP : x ∈ P := hP0P hxP0
    have hxbot : x ∈ (⊥ : Subgroup G) := by simpa [hPbot] using hxP
    exact hxne (Subgroup.mem_bot.mp hxbot)
  haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  have hTne : T ≠ ⊥ := by
    simpa [T, pp] using
      section10_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup
        (G := G) (p := pp) hPp
  have hTelem : IsElementaryAbelian p T := by
    simpa [T, pp] using
      section10OmegaOneCenter_isElementaryAbelian (G := G) (p := pp) P
  letI : IsElementaryAbelian p T := hTelem
  haveI : (pCore p H).Characteristic := pCore_characteristic (G := H) (p := p)
  have hLnormH : L ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHleL).1
      (section16MFSubgroup_subgroupOf_normal hH)
  have hNormHleP :
      Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    simpa [P] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := H) (K := pCore p H))
  have hEnormT : E ≤ Subgroup.normalizer (T : Set G) :=
    hEleL.trans <| hLnormH.trans <| hNormHleP.trans <| by
      simpa [T] using section11_normalizer_le_normalizer_omegaOneCenter
        (G := G) pp P
  letI : Fact (E ≤ Subgroup.normalizer (T : Set G)) := ⟨hEnormT⟩
  have hregularT : ActsRegularly E T := by
    intro a ha
    have haGne : (a : G) ≠ 1 := by
      intro ha1
      apply ha
      exact Subtype.ext ha1
    have haNotH : (a : G) ∉ H := by
      intro haH
      exact haGne (Subgroup.disjoint_def.mp hdisjHE haH a.property)
    have hcentH : Section2.centralizerIn H (a : G) = ⊥ :=
      Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
        hfrob (a : G) (hEleL a.property) haNotH
    have hcentT : elementCentralizerIn T (a : G) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have hyH : y ∈ Section2.centralizerIn H (a : G) :=
        ⟨hTP0.trans hP0H hy.1, hy.2⟩
      have hybot : y ∈ (⊥ : Subgroup G) := by simpa [hcentH] using hyH
      exact hybot
    rw [fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
      T E hEnormT a]
    simp [hcentT]
  haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hTne
  obtain ⟨V, hVnormal, hVinv, hVne, hVmin⟩ :=
    exists_minimal_normal_isInvariant (G := T) (A := E)
  letI : V.Normal := hVnormal
  letI : IsInvariant E T V := hVinv
  have hVelem : IsElementaryAbelian p V := by
    refine
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro v
    apply Subtype.ext
    have hvpow : (v.1 : T) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p T) v.1
    exact hvpow
  letI : IsElementaryAbelian p V := hVelem
  letI : CommGroup V := IsMulCommutative.instCommGroup
  have hregularV : ActsRegularly E V :=
    ActsRegularly.invariantSubgroup hregularT V
  have hTcard : Nat.card T ≤ p ^ 2 := by
    by_contra hnot
    have hgt : p ^ 2 < Nat.card T := Nat.lt_of_not_ge hnot
    have hgen3 : 3 ≤ generatorRank T := by
      letI : CommGroup T := IsMulCommutative.instCommGroup
      have hcardDvd : Nat.card T ∣ p ^ Group.rank T := by
        simpa using card_dvd_exponent_pow_rank' (G := T) (n := p) (fun t =>
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p T) t)
      have hnle : ¬ Group.rank T ≤ 2 := by
        intro hrank
        have hcardLe : Nat.card T ≤ p ^ Group.rank T :=
          Nat.le_of_dvd (pow_pos hp.pos _) hcardDvd
        have hpowLe : p ^ Group.rank T ≤ p ^ 2 :=
          Nat.pow_le_pow_right hp.pos hrank
        exact (not_lt_of_ge (hcardLe.trans hpowLe)) hgt
      have : 3 ≤ Group.rank T := by omega
      simpa [generatorRank_eq_group_rank] using this
    letI : Fact (IsPGroup p T) := ⟨IsElementaryAbelian.isPGroup p T⟩
    have hgenLeRankT : generatorRank T ≤ groupRank T :=
      generatorRank_le_groupRank_of_commutative_pgroup (p := p) T
    have hRankTle : groupRank T ≤ groupRank P0 :=
      section10_groupRank_le_of_le hTP0
    omega
  haveI : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).2 hVne
  have hVp : IsPGroup p V := IsElementaryAbelian.isPGroup p V
  obtain ⟨n, hnpos, hVcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := V) hVp).1 inferInstance
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).1
    rw [← hVcard]
    exact (Subgroup.card_le_card_group V).trans hTcard
  have hn : n = 1 ∨ n = 2 := by omega
  rcases hn with rfl | rfl
  · have hVcardPrime : Nat.card V = p := by simpa using hVcard
    have hfree : ∀ a : E, a ≠ 1 → ∀ v : V, a • v = v → v = 1 := by
      intro a ha v hav
      have hvfix : v ∈ fixedPointSubgroup (↑(Subgroup.zpowers a)) V := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro z
        rcases z.2 with ⟨k, hk⟩
        change (z : E) • v = v
        rw [← hk]
        exact MulAction.mem_fixedBy_zpow hav k
      have hvbot : v ∈ (⊥ : Subgroup V) := by
        simpa [hregularV a ha] using hvfix
      simpa using hvbot
    have hdiv : Nat.card E ∣ p - 1 := by
      have hdiv' := theorem_12_12_actor_card_dvd_group_card_sub_one hfree
      rw [hVcardPrime] at hdiv'
      exact hdiv'
    have hVcyc : IsCyclic V := isCyclic_of_prime_card hVcardPrime
    letI : IsCyclic V := hVcyc
    let φ : E →* MulAut V := MulDistribMulAction.toMulAut E V
    have hφinj : Function.Injective φ := by
      apply (MonoidHom.ker_eq_bot_iff φ).mp
      rw [Subgroup.eq_bot_iff_forall]
      intro a haKer
      by_contra ha
      have hfixTop : fixedPointSubgroup (↑(Subgroup.zpowers a)) V = ⊤ := by
        apply top_unique
        intro v _hv
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro z
        rcases z.2 with ⟨k, hk⟩
        have haAct : φ a = 1 := MonoidHom.mem_ker.mp haKer
        have haFix : a • v = v := by
          change φ a v = v
          rw [haAct]
          rfl
        change (z : E) • v = v
        rw [← hk]
        exact MulAction.mem_fixedBy_zpow haFix k
      have hbotTop : (⊥ : Subgroup V) = ⊤ := by
        rw [← hregularV a ha, hfixTop]
      exact (bot_ne_top : (⊥ : Subgroup V) ≠ ⊤) hbotTop
    have hAutCyclic : IsCyclic (MulAut V) := by
      let autEquiv : MulAut V ≃* (ZMod (Nat.card V))ˣ :=
        IsCyclic.mulAutMulEquiv (G := V)
      have hUnits : IsCyclic (ZMod (Nat.card V))ˣ := by
        rw [hVcardPrime]
        exact ZMod.isCyclic_units_prime hp
      letI : IsCyclic (ZMod (Nat.card V))ˣ := hUnits
      exact isCyclic_of_injective autEquiv.toMonoidHom autEquiv.injective
    letI : IsCyclic (MulAut V) := hAutCyclic
    refine ⟨isCyclic_of_injective φ hφinj, ?_⟩
    left
    simpa [he] using hdiv
  · have hVcardSq : Nat.card V = p ^ 2 := by simpa using hVcard
    let VG : Subgroup G := V.map T.subtype
    let P1 : Subgroup G := section12OmegaOneSubgroup pp P0
    have hVGP1 : VG ≤ P1 := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
      apply section12_mem_omegaOneSubgroup_of_mem_pow_eq_one (p := pp)
      · exact hTP0 v.property
      · have hvpow : v ^ p = 1 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p T) v
        simpa [pp] using congrArg Subtype.val hvpow
    have hVGcard : Nat.card VG = p ^ 2 := by
      calc
        Nat.card VG = Nat.card V := by
          exact Subgroup.card_map_of_injective
            (K := V) (f := T.subtype) T.subtype_injective
        _ = p ^ 2 := hVcardSq
    letI : IsMulCommutative P0 := hP0comm
    letI : Fact (IsPGroup p P0) := ⟨hP0p⟩
    have hP0gen : generatorRank P0 = 2 := by
      apply le_antisymm
      · exact
          (generatorRank_le_groupRank_of_commutative_pgroup (p := p) P0).trans_eq
            hP0rank
      · rw [← hP0rank]
        exact groupRank_le_generatorRank_of_commutative_pgroup hP0p hP0comm
    have hP1card : Nat.card P1 = p ^ 2 := by
      calc
        Nat.card P1 = Nat.card (omega₁ (G := P0) (p := p)) := by
          exact Subgroup.card_map_of_injective
            (K := omega₁ (G := P0) (p := p)) (f := P0.subtype)
            P0.subtype_injective
        _ = p ^ generatorRank P0 :=
          omega₁_card_eq_pow_generatorRank_of_commutative_pgroup (p := p) P0
        _ = p ^ 2 := by rw [hP0gen]
    have hVGeqP1 : VG = P1 :=
      Subgroup.eq_of_le_of_card_ge hVGP1 (by rw [hVGcard, hP1card])
    have hxVG : x ∈ VG := by
      rw [hVGeqP1]
      simpa [pp] using hxOmega
    rcases Subgroup.mem_map.mp hxVG with ⟨xT, hxTV, hxT⟩
    let xV : V := ⟨xT, hxTV⟩
    have hxVcoe : (((xV : V) : T) : G) = x := by
      simpa [xV] using hxT
    let ρ :=
      Theory.Representation.ofElementaryAbelianAction (A := E) (G := V) (p := p)
    letI : FiniteDimensional (ZMod p) (Additive V) := Module.Finite.of_finite
    have hρdim : Module.finrank (ZMod p) (Additive V) = 2 := by
      apply Nat.pow_right_injective hp.two_le
      calc
        p ^ Module.finrank (ZMod p) (Additive V) = Nat.card (Additive V) := by
          simpa [ZMod.card] using
            (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)).symm
        _ = Nat.card V := by rfl
        _ = p ^ 2 := hVcardSq
    have hρinj : Function.Injective ρ := by
      apply (MonoidHom.ker_eq_bot_iff ρ).mp
      rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
      rw [Subgroup.eq_bot_iff_forall]
      intro a haFix
      by_contra ha
      have hfixTop : fixedPointSubgroup (↑(Subgroup.zpowers a)) V = ⊤ := by
        apply top_unique
        intro v _hv
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro z
        rcases z.2 with ⟨k, hk⟩
        have haFixV : a • v = v :=
          (mem_fixingSubgroup_iff
            (M := E) (s := (Set.univ : Set V))).1 haFix v (Set.mem_univ v)
        change (z : E) • v = v
        rw [← hk]
        exact MulAction.mem_fixedBy_zpow haFixV k
      have hbotTop : (⊥ : Subgroup V) = ⊤ := by
        rw [← hregularV a ha, hfixTop]
      exact (bot_ne_top : (⊥ : Subgroup V) ≠ ⊤) hbotTop
    have hVminimalTop :
        ∀ N : Subgroup V, N.Normal → IsInvariant E V N → N ≠ ⊥ → N = ⊤ := by
      intro N hNnormal hNinv hNne
      letI : N.Normal := hNnormal
      letI : IsInvariant E V N := hNinv
      let Nmap : Subgroup T := N.map V.subtype
      have hNmapInv : IsInvariant E T Nmap := by
        simpa [Nmap] using isInvariant_map_subtype (A := E) (G := T) V N
      letI : IsInvariant E T Nmap := hNmapInv
      have hNmapNormal : Nmap.Normal := by infer_instance
      have hNmapNe : Nmap ≠ ⊥ := by
        intro hbot
        exact hNne
          ((Subgroup.map_eq_bot_iff_of_injective
            (H := N) (f := V.subtype) V.subtype_injective).1 hbot)
      have hNmapLe : Nmap ≤ V := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨n, hn, rfl⟩
        exact n.property
      have hNmapEq : Nmap = V :=
        hVmin Nmap hNmapNormal hNmapInv hNmapNe hNmapLe
      have htopMap : (⊤ : Subgroup V).map V.subtype = V := by
        ext t
        constructor
        · intro ht
          rcases Subgroup.mem_map.mp ht with ⟨v, _hv, rfl⟩
          exact v.property
        · intro ht
          exact Subgroup.mem_map.mpr ⟨⟨t, ht⟩, trivial, rfl⟩
      apply (Subgroup.map_injective (f := V.subtype) V.subtype_injective)
      simpa only [htopMap, Nmap] using hNmapEq
    have hρirr : Representation.IsIrreducible ρ := by
      simpa [ρ] using
        Section9.theorem_9_1_ofElementaryAbelianAction_irreducible_of_minimal_invariant_sec9
          (A := E) (M := V) (p := p) hVminimalTop
    have hfree : ∀ a : E, a ≠ 1 → ∀ v : V, a • v = v → v = 1 := by
      intro a ha v hav
      have hvfix : v ∈ fixedPointSubgroup (↑(Subgroup.zpowers a)) V := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        intro z
        rcases z.2 with ⟨k, hk⟩
        change (z : E) • v = v
        rw [← hk]
        exact MulAction.mem_fixedBy_zpow hav k
      have hvbot : v ∈ (⊥ : Subgroup V) := by
        simpa [hregularV a ha] using hvfix
      simpa using hvbot
    have hEdivSq : Nat.card E ∣ p ^ 2 - 1 := by
      have hdiv := theorem_12_12_actor_card_dvd_group_card_sub_one hfree
      change Nat.card E ∣ Nat.card V - 1 at hdiv
      rw [hVcardSq] at hdiv
      exact hdiv
    have hpNotDvdE : ¬ p ∣ Nat.card E := by
      intro hpE
      have hpPred : p ∣ p ^ 2 - 1 := hpE.trans hEdivSq
      have hpPow : p ∣ p ^ 2 := dvd_pow_self p (by omega)
      have hsubAdd : p ^ 2 - 1 + 1 = p ^ 2 :=
        Nat.sub_add_cancel (by nlinarith [hp.two_le])
      have hpSum : p ∣ p ^ 2 - 1 + 1 := by
        rw [hsubAdd]
        exact hpPow
      have hpOne : p ∣ 1 :=
        (Nat.dvd_add_iff_left hpPred).2 (by
          simpa [Nat.add_comm] using hpSum)
      exact hp.not_dvd_one hpOne
    have hcharNotDvdE : ¬ ringChar (ZMod p) ∣ Nat.card E := by
      simpa [ZMod.ringChar_zmod_n] using hpNotDvdE
    have hEodd : Odd (Nat.card E) :=
      odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card E)
    have hEcomm : IsMulCommutative E :=
      theorem_2_6_a (F := ZMod p) hEodd hρdim hρinj hcharNotDvdE
    letI : IsMulCommutative E := hEcomm
    letI : CommGroup E := IsMulCommutative.instCommGroup
    have hnonScalar :
        ∀ y : E, y ≠ 1 →
          ¬ ∃ a : ZMod p, ∀ v : Additive V, ρ y v = a • v := by
      intro y hy
      rintro ⟨a, ha⟩
      have hyxV : y • xV = xV ^ a.val := by
        apply Additive.ofMul.injective
        calc
          Additive.ofMul (y • xV) = ρ y (Additive.ofMul xV) := by
            apply (Theory.Representation.ofElementaryAbelianAction_apply_ofMul
              (A := E) (G := V) (p := p) y xV).symm
          _ = a • Additive.ofMul xV := ha (Additive.ofMul xV)
          _ = (a.val : ℕ) • Additive.ofMul xV := by
            nth_rw 1 [← ZMod.natCast_zmod_val a]
            rw [Nat.cast_smul_eq_nsmul]
          _ = Additive.ofMul (xV ^ a.val) := by simp
      have hyx : (y : G) * x * (y : G)⁻¹ = x ^ a.val := by
        have hcoe := congrArg (fun z : V => (((z : V) : T) : G)) hyxV
        have hactCoe :
            ((((y • xV : V) : T) : G)) =
              (y : G) * (((xV : V) : T) : G) * (y : G)⁻¹ := by
          calc
            ((((y • xV : V) : T) : G)) =
                (((y • (xV : T) : T) : G)) := by rfl
            _ = (y : G) * (((xV : V) : T) : G) * (y : G)⁻¹ :=
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe E T y (xV : T)
        calc
          (y : G) * x * (y : G)⁻¹ = ((((y • xV : V) : T) : G)) := by
            rw [hactCoe, hxVcoe]
          _ = ((((xV ^ a.val : V) : T) : G)) := hcoe
          _ = x ^ a.val := by
            change ((((xV : V) : T) : G) ^ a.val) = x ^ a.val
            rw [hxVcoe]
      have hconjLe :
          (Subgroup.zpowers x).conjBy (y : G) ≤ Subgroup.zpowers x := by
        rw [Subgroup.conjBy, MonoidHom.map_zpowers]
        apply Subgroup.zpowers_le.mpr
        change (y : G) * x * (y : G)⁻¹ ∈ Subgroup.zpowers x
        rw [hyx]
        exact (Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) a.val
      have hconjCard :
          Nat.card ((Subgroup.zpowers x).conjBy (y : G)) =
            Nat.card (Subgroup.zpowers x) := by
        simpa [Subgroup.conjBy] using
          (Subgroup.card_map_of_injective
            (K := Subgroup.zpowers x)
            (f := (MulAut.conj (y : G)).toMonoidHom)
            (MulAut.conj (y : G)).injective)
      have hconjEq :
          (Subgroup.zpowers x).conjBy (y : G) = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge hconjLe (by rw [hconjCard])
      have hyNorm : (y : G) ∈
          Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
        section10_mem_normalizer_of_conjBy_eq (G := G) hconjEq
      have hyH : (y : G) ∈ H :=
        hMLleH ⟨hNxM hyNorm, hEleL y.property⟩
      exact hy (Subtype.ext (Subgroup.disjoint_def.mp hdisjHE hyH y.property))
    have hHneL : H ≠ L := by
      rintro rfl
      rcases hfrob with
        ⟨_hHL, _hHnormal, R, hcompR, _hHne, hRne, _hfixedR⟩
      have hHtop : H.subgroupOf H = ⊤ := by
        ext h
        simp
      have hRleBot : R ≤ (⊥ : Subgroup H) := by
        rw [← hcompR.disjoint.eq_bot]
        simp
      exact hRne (le_bot_iff.mp hRleBot)
    have hEne : E ≠ ⊥ := by
      intro hEbot
      have hLE' := hLE
      simp [hEbot] at hLE'
      exact hHneL hLE'.symm
    letI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
    letI : Representation.IsIrreducible ρ := hρirr
    let F2 := Module.End (MonoidAlgebra (ZMod p) E) ρ.asModule
    letI : Field F2 := endField_field ρ
    letI : Fintype F2 := Fintype.ofFinite F2
    letI : Module F2 ρ.asModule := endFieldModule ρ
    letI : Finite ρ.asModule :=
      Finite.of_equiv (Additive V) ρ.asModuleEquiv.symm.toEquiv
    letI : Module.Finite F2 ρ.asModule := by
      set_option maxHeartbeats 800000 in
        exact Module.Finite.of_finite
    have hAsCard : Nat.card ρ.asModule = p ^ 2 := by
      calc
        Nat.card ρ.asModule = Nat.card (Additive V) :=
          Nat.card_congr ρ.asModuleEquiv.toEquiv
        _ = Nat.card V := by rfl
        _ = p ^ 2 := hVcardSq
    have hF2Char : ringChar F2 = p := by
      have hchar :=
        @Algebra.ringChar_eq (ZMod p) F2 inferInstance inferInstance
          inferInstance
          (Module.End.instAlgebra (ZMod p) (MonoidAlgebra (ZMod p) E) ρ.asModule)
      simpa [ZMod.ringChar_zmod_n] using hchar.symm
    letI : CharP F2 p := ringChar.of_eq hF2Char
    obtain ⟨n, _hp', hF2CardPow'⟩ := FiniteField.card F2 p
    have hF2CardPow : Nat.card F2 = p ^ (n : ℕ) := by
      simpa [Nat.card_eq_fintype_card] using hF2CardPow'
    have hAsCardField :
        Nat.card ρ.asModule = Nat.card F2 ^ Module.finrank F2 ρ.asModule :=
      @Module.natCard_eq_pow_finrank F2 ρ.asModule
        (@Field.toDivisionRing F2 inferInstance) ρ.instAddCommGroupAsModule
        (endFieldModule ρ) inferInstance
    have hnMul : 2 = (n : ℕ) * Module.finrank F2 ρ.asModule := by
      apply Nat.pow_right_injective hp.two_le
      calc
        p ^ 2 = Nat.card ρ.asModule := hAsCard.symm
        _ = Nat.card F2 ^ Module.finrank F2 ρ.asModule := hAsCardField
        _ = (p ^ (n : ℕ)) ^ Module.finrank F2 ρ.asModule := by
          rw [hF2CardPow]
        _ = p ^ ((n : ℕ) * Module.finrank F2 ρ.asModule) := by
          rw [pow_mul]
    have hn : (n : ℕ) = 1 ∨ (n : ℕ) = 2 := by
      have hndvd : (n : ℕ) ∣ 2 :=
        ⟨Module.finrank F2 ρ.asModule, hnMul⟩
      exact (Nat.dvd_prime Nat.prime_two).1 hndvd
    have hF2Card : Nat.card F2 = p ^ 2 := by
      rcases hn with hn | hn
      · have hcardPrime : Nat.card F2 = p := by
          simpa [hn] using hF2CardPow
        have hAlgBij : Function.Bijective (algebraMap (ZMod p) F2) := by
          apply (Fintype.bijective_iff_injective_and_card _).2
          refine ⟨(algebraMap (ZMod p) F2).injective, ?_⟩
          rw [ZMod.card]
          simpa [Nat.card_eq_fintype_card] using hcardPrime.symm
        let repEnd : E →* F2 :=
          (Module.toModuleEnd
            (MonoidAlgebra (ZMod p) E) ρ.asModule).toMonoidHom.comp
              (MonoidAlgebra.of (ZMod p) E)
        obtain ⟨y, hy⟩ := exists_ne (1 : E)
        rcases hAlgBij.2 (repEnd y) with ⟨a, ha⟩
        exfalso
        apply hnonScalar y hy
        refine ⟨a, ?_⟩
        intro v
        let m : ρ.asModule := ρ.asModuleEquiv.symm v
        have hrepApply :
            repEnd y m =
              ρ.asModuleEquiv.symm (ρ y (ρ.asModuleEquiv m)) := by
          change ((Module.toModuleEnd
            (MonoidAlgebra (ZMod p) E) ρ.asModule)
              ((MonoidAlgebra.of (ZMod p) E) y)) m = _
          rw [show (MonoidAlgebra.of (ZMod p) E) y =
            MonoidAlgebra.single y (1 : ZMod p) by rfl]
          change (MonoidAlgebra.single y (1 : ZMod p)) • m = _
          rw [Representation.single_smul]
          apply ρ.asModuleEquiv.injective
          simp
        calc
          ρ y v = ρ.asModuleEquiv (repEnd y m) := by
            symm
            calc
              ρ.asModuleEquiv (repEnd y m) =
                  ρ y (ρ.asModuleEquiv m) := by
                rw [hrepApply]
                exact ρ.asModuleEquiv.apply_symm_apply _
              _ = ρ y v := by simp [m]
          _ = ρ.asModuleEquiv ((algebraMap (ZMod p) F2) a m) := by
            rw [ha]
          _ = a • v := by
            calc
              ρ.asModuleEquiv ((algebraMap (ZMod p) F2) a m) =
                  ρ.asModuleEquiv (a • m) := by
                rw [Module.algebraMap_end_apply]
              _ = a • ρ.asModuleEquiv m := by
                exact ρ.asModuleEquiv.map_smul a m
              _ = a • v := by simp [m]
      · simpa [hn] using hF2CardPow
    have hF2Dim : Module.finrank F2 ρ.asModule = 1 := by
      apply Nat.pow_right_injective (show 2 ≤ p ^ 2 by nlinarith [hp.two_le])
      calc
        (p ^ 2) ^ Module.finrank F2 ρ.asModule =
            Nat.card F2 ^ Module.finrank F2 ρ.asModule := by rw [hF2Card]
        _ = Nat.card ρ.asModule := hAsCardField.symm
        _ = (p ^ 2) ^ 1 := by simpa using hAsCard
    let scalarWitness (f : Module.End F2 ρ.asModule) :=
      @LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
        F2 _ _ ρ.asModule _ (endFieldModule ρ)
          (@Module.Free.of_divisionRing F2 ρ.asModule _ _
            (endFieldModule ρ)) hF2Dim f
    let scalarVal (f : Module.End F2 ρ.asModule) : F2 :=
      Classical.choose (scalarWitness f)
    have hscalarApply (f : Module.End F2 ρ.asModule) (m : ρ.asModule) :
        f m = scalarVal f • m := by
      have hs := (Classical.choose_spec (scalarWitness f)).1
      have hm := LinearMap.congr_fun hs m
      simpa only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] using hm
    have hscalarUnique (f : Module.End F2 ρ.asModule) (a : F2)
        (ha : ∀ m : ρ.asModule, f m = a • m) : scalarVal f = a := by
      apply ((Classical.choose_spec (scalarWitness f)).2 a ?_).symm
      ext m
      simpa only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] using ha m
    let scalarHom : E →* F2 :=
      { toFun := fun y => scalarVal ((endFieldRep ρ) y)
        map_one' := by
          apply hscalarUnique
          intro m
          simp
        map_mul' := by
          intro y z
          apply hscalarUnique
          intro m
          rw [map_mul, Module.End.mul_apply, hscalarApply, hscalarApply]
          exact (mul_smul _ _ _).symm }
    have hEndRepInj : Function.Injective (endFieldRep ρ) := by
      intro y z hyz
      apply hρinj
      apply LinearMap.ext
      intro v
      let m : ρ.asModule := ρ.asModuleEquiv.symm v
      have htemp : (ρ y) (ρ.asModuleEquiv m) = (ρ z) (ρ.asModuleEquiv m) := by
        calc
          (ρ y) (ρ.asModuleEquiv m) = ρ.asModuleEquiv ((endFieldRep ρ) y m) := by
            rw [← endFieldRep_apply' ρ y m]
          _ = ρ.asModuleEquiv ((endFieldRep ρ) z m) := by rw [hyz]
          _ = (ρ z) (ρ.asModuleEquiv m) := by rw [endFieldRep_apply' ρ z m]
      simpa [m] using htemp
    have hscalarHomInj : Function.Injective scalarHom := by
      intro y z hyz
      apply hEndRepInj
      ext m
      change scalarVal ((endFieldRep ρ) y) =
        scalarVal ((endFieldRep ρ) z) at hyz
      rw [hscalarApply, hscalarApply, hyz]
    have hEcyclic : IsCyclic E := by
      exact isCyclic_of_injective_ringHom scalarHom hscalarHomInj
    letI : IsCyclic F2ˣ :=
      isCyclic_of_injective_ringHom (Units.coeHom F2) Units.val_injective
    let baseUnits : (ZMod p)ˣ →* F2ˣ :=
      Units.map (algebraMap (ZMod p) F2).toMonoidHom
    let pRoots : Finset F2ˣ :=
      Finset.univ.filter (fun u => u ^ (p - 1) = 1)
    let baseImage : Finset F2ˣ := Finset.univ.image baseUnits
    have hbaseInj : Function.Injective baseUnits :=
      Units.map_injective (algebraMap (ZMod p) F2).injective
    have hbaseImageCard : baseImage.card = p - 1 := by
      change (Finset.univ.image baseUnits).card = p - 1
      rw [Finset.card_image_of_injective _ hbaseInj]
      simp [Fintype.card_units, ZMod.card]
    have hbaseImageLe : baseImage ⊆ pRoots := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨a, _ha, rfl⟩
      simp only [pRoots, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using congrArg baseUnits
        (ZMod.units_pow_card_sub_one_eq_one p a)
    have hrootCard : pRoots.card ≤ p - 1 := by
      simpa [pRoots] using
        (IsCyclic.card_pow_eq_one_le
          (α := F2ˣ) (show 0 < p - 1 by exact Nat.sub_pos_of_lt hp.one_lt))
    have hbaseImageEq : baseImage = pRoots :=
      Finset.eq_of_subset_of_card_le hbaseImageLe (by
        rw [hbaseImageCard]
        exact hrootCard)
    have hbaseRoot (u : F2ˣ) (hu : u ^ (p - 1) = 1) :
        u ∈ MonoidHom.range baseUnits := by
      have huRoots : u ∈ pRoots := by simp [pRoots, hu]
      have huImage : u ∈ baseImage := by
        rw [hbaseImageEq]
        exact huRoots
      rcases Finset.mem_image.mp huImage with ⟨a, _ha, ha⟩
      exact ⟨a, ha⟩
    have hCoprime : (Nat.card E).Coprime (p - 1) := by
      by_contra hnot
      rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with
        ⟨r, hr, hrE, hrP⟩
      letI : Fact r.Prime := ⟨hr⟩
      obtain ⟨z, hzOrder⟩ := exists_prime_orderOf_dvd_card' r hrE
      have hzNe : z ≠ 1 := by
        intro hz
        rw [hz, orderOf_one] at hzOrder
        exact hr.ne_one hzOrder.symm
      have hzPow : z ^ (p - 1) = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        simpa [hzOrder] using hrP
      have hszPow : (scalarHom.toHomUnits z) ^ (p - 1) = 1 := by
        simpa using congrArg scalarHom.toHomUnits hzPow
      rcases hbaseRoot (scalarHom.toHomUnits z) hszPow with ⟨a, ha⟩
      have hscalarEq :
          scalarHom z = (algebraMap (ZMod p) F2) (a : ZMod p) := by
        have hval := congrArg (fun u : F2ˣ => (u : F2)) ha
        simpa [baseUnits] using hval.symm
      exfalso
      apply hnonScalar z hzNe
      refine ⟨(a : ZMod p), ?_⟩
      intro v
      let m : ρ.asModule := ρ.asModuleEquiv.symm v
      calc
        ρ z v = ρ.asModuleEquiv ((endFieldRep ρ) z m) := by
          symm
          calc
            ρ.asModuleEquiv ((endFieldRep ρ) z m) =
                ρ z (ρ.asModuleEquiv m) := endFieldRep_apply' ρ z m
            _ = ρ z v := by simp [m]
        _ = ρ.asModuleEquiv (scalarHom z • m) := by
          have htemp : (endFieldRep ρ) z m = scalarHom z • m := by
            calc
              (endFieldRep ρ) z m = ((endFieldRep ρ) z) m := rfl
              _ = scalarVal ((endFieldRep ρ) z) • m := hscalarApply ((endFieldRep ρ) z) m
              _ = scalarHom z • m := rfl
          rw [htemp]
        _ = ρ.asModuleEquiv
            ((algebraMap (ZMod p) F2) (a : ZMod p) • m) := by
          rw [hscalarEq]
        _ = ρ.asModuleEquiv ((a : ZMod p) • m) := by
          rw [endFieldModule_smul_apply, Module.algebraMap_end_apply]
        _ = (a : ZMod p) • ρ.asModuleEquiv m := by
          exact ρ.asModuleEquiv.map_smul (a : ZMod p) m
        _ = (a : ZMod p) • v := by simp [m]
    have hEdivPlus : Nat.card E ∣ p + 1 := by
      apply hCoprime.dvd_of_dvd_mul_right
      rw [← Nat.sq_sub_sq]
      simpa using hEdivSq
    refine ⟨hEcyclic, Or.inr ?_⟩
    rw [he]
    exact hEdivPlus

set_option maxHeartbeats 200000

/-- Peterfalvi `(12.12)`.

Let `E` be a complement of `H` in `L` and `e = |E|`.
Then `E` is cyclic and `e` divides `p - 1` or `p + 1`. -/
public theorem theorem_12_12
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls E : Subgroup G)
    (x : G)
    (p e : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hcomp : section12ComplementIn L H E)
    (he : e = Nat.card E) :
    IsCyclic E ∧ (e ∣ p - 1 ∨ e ∣ p + 1) := by
  exact theorem_12_12_of_source_data M K K' P0 L H Ls E x p e
    (theorem_12_12_source_leaf M K K' P0 L H Ls E x p e) h128 h129 hfrob
    hcomp he

end CFSG.Section12
