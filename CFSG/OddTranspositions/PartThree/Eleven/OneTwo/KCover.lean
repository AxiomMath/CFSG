module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.DerivedShared
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.KStructure

import CFSG.OddTranspositions.PartThree.CardWidth
import CFSG.GroupTheory.SylowOrbitCard
import CFSG.OddTranspositions.PartThree.Eleven.GroupLemmas
import CFSG.GH74.Generic.BProg.B2.L2Cover
import CFSG.Milestones.ASVolI.I2Covers
import CFSG.Timmesfeld.Bridge.Asc72ZAlt
import CFSG.OddTranspositions.PartThree.LocalBenderCenter
import CFSG.OddTranspositions.PartThree.EightFive.Transitive

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open MulAction CFSG.GroupTheory
open scoped commutatorElement
open DerivedShared

section KCover

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

private theorem le_secondCommutator_of_central_sup {X : Type} [Group X] [Finite X]
    (R : Subgroup X) [R.Normal] {Λ : Set X} {d₀ : X} (hclass : Λ = {g : X | IsConj d₀ g})
    (hgen : Subgroup.closure Λ = ⊤) (hRcenter : R ≤ Subgroup.center X)
    (hdecomp : commutator X = ⁅commutator X, commutator X⁆ ⊔ R) :
    R ≤ ⁅commutator X, commutator X⁆ := by
  have hH1eq : commutator X = ⁅commutator X, commutator X⁆ := by
    let H1 := commutator X
    let H2 : Subgroup X := ⁅H1, H1⁆
    have hH2le : H2 ≤ H1 := by
      show ⁅H1, H1⁆ ≤ H1
      simpa using Subgroup.commutator_le_sup H1 H1
    apply le_antisymm ?_ hH2le
    let Q := X ⧸ H2
    let π₂' : X →* Q := QuotientGroup.mk' H2
    obtain ⟨c, hc⟩ := CFSG.OddTranspositions.image_isClass_quotient hclass H2
    have hQgen : Subgroup.closure {g : Q | IsConj c g} = ⊤ := by
      rw [← hc]
      exact CFSG.OddTranspositions.image_closure_eq_top_quotient H2 hgen
    have hmap : (commutator X).map π₂' = commutator Q := by
      simp only [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective π₂' (QuotientGroup.mk'_surjective H2)]
    have hQle : commutator Q ≤ Subgroup.center Q := by
      rw [← hmap]
      refine (Subgroup.map_le_iff_le_comap).mpr ?_
      have hle1 : H2 ≤ Subgroup.comap π₂' (Subgroup.center Q) := by
        intro x hx
        rw [Subgroup.mem_comap]
        have hx1 : π₂' x = 1 := by
          rw [← MonoidHom.mem_ker, show π₂'.ker = H2 from QuotientGroup.ker_mk' H2]
          exact hx
        rw [hx1]
        exact Subgroup.one_mem _
      have hle2 : R ≤ Subgroup.comap π₂' (Subgroup.center Q) := by
        intro x hx
        rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective H2 q
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_center_iff.mp (hRcenter hx) y
      calc H1 = H2 ⊔ R := hdecomp
        _ ≤ Subgroup.comap π₂' (Subgroup.center Q) := sup_le hle1 hle2
    have hab := commute_of_closure_isConj_of_commutator_le_center c hQgen hQle
    have hQab : IsMulCommutative Q :=
      isMulCommutative_iff.mpr (fun a b => (hab a b).eq)
    have hQbot : commutator Q = ⊥ := (commutator_eq_bot_iff Q).mpr hQab
    have hmapH1 : H1.map π₂' = ⊥ := by
      change (commutator X).map π₂' = ⊥
      rw [show (commutator X).map π₂' = commutator Q from hmap, hQbot]
    have hle : H1 ≤ π₂'.ker := (Subgroup.map_eq_bot_iff H1).mp hmapH1
    rwa [show π₂'.ker = H2 from QuotientGroup.ker_mk' H2] at hle
  have hRle : R ≤ commutator X := le_sup_right.trans hdecomp.ge
  rwa [hH1eq] at hRle

private theorem sl2_of_central_extension_alt5 {L : Type} [Group L] [Finite L]
    (hLperfect : Group.IsPerfect L) (hcenterCard : Nat.card (Subgroup.center L) = 2)
    (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) :
    Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := MulEquiv.isSimpleGroup e
  have hcardq : Nat.card (L ⧸ Subgroup.center L) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hnoncomm : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative (L ⧸ Subgroup.center L) :=
      isMulCommutative_iff.mpr fun a b => (h a b)
    have hp : Nat.Prime (Nat.card (L ⧸ Subgroup.center L)) :=
      (Group.is_simple_iff_prime_card).mp hsimple
    rw [hcardq] at hp
    exact absurd hp (by norm_num)
  have hq : CFSG.IsQuasisimple L := ⟨hLperfect, hsimple, hnoncomm⟩
  have hcenterNe : Subgroup.center L ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (Subgroup.center L) = 1 := by rw [hbot]; simp
    omega
  exact isSL2_of_center_eq_bot hq hcenterNe (le_of_eq hcenterCard) e

private abbrev kcoverK (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : Subgroup G :=
  localGroup D (frameE hC r)

private abbrev kcoverR (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) :
    Subgroup (kcoverK hC r) :=
  CFSG.solvableRadical (kcoverK hC r)

private abbrev kcoverQ (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) : Type :=
  kcoverK hC r ⧸ kcoverR hC r

private abbrev kcoverPi (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) :
    kcoverK hC r →* kcoverQ hC r :=
  QuotientGroup.mk' (kcoverR hC r)

private structure FactorBase (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha) where
  hsetupK : Setup (kcoverK hC r) (localSet D (frameE hC r))
  hmapComm : (commutator (kcoverK hC r)).map (kcoverPi hC r) =
    commutator (kcoverQ hC r)
  heK : frameE hC r ∈ kcoverK hC r
  heR : (⟨frameE hC r, heK⟩ : kcoverK hC r) ∈ kcoverR hC r
  hRcard : Nat.card (kcoverR hC r) = 2
  hRcenter : kcoverR hC r ≤ Subgroup.center (kcoverK hC r)

private structure FactorSetup (hC : HypothesisC D) (r : Fin 3 → Halpha D hC.alpha)
    extends FactorBase hC r where
  hRle : kcoverR hC r ≤ commutator (kcoverK hC r)
  A₁ : Subgroup (kcoverQ hC r)
  A₂ : Subgroup (kcoverQ hC r)
  hA1 : Nonempty (A₁ ≃* CFSG.Theory.Comparator.PSL2Model 2)
  hA2 : Nonempty (A₂ ≃* CFSG.Theory.Comparator.PSL2Model 2)
  hcommAB : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b
  hinfAB : A₁ ⊓ A₂ = ⊥
  hsupAB : A₁ ⊔ A₂ = commutator (kcoverQ hC r)
  hidxAB : (commutator (kcoverQ hC r)).index = 2
  hswapAB : ∀ y : kcoverQ hC r, y ∉ commutator (kcoverQ hC r) →
    A₁.map (MulAut.conj y).toMonoidHom = A₂
  eA : A₁ ≃* alternatingGroup (Fin 5)
  eA2 : A₂ ≃* alternatingGroup (Fin 5)
  hperfA1 : Group.IsPerfect ↥A₁
  hperfA2 : Group.IsPerfect ↥A₂
  hcenterA1 : Subgroup.center ↥A₁ = ⊥
  hcenterA2 : Subgroup.center ↥A₂ = ⊥
  hRleLam1 : kcoverR hC r ≤ A₁.comap (kcoverPi hC r)
  hRleLam2 : kcoverR hC r ≤ A₂.comap (kcoverPi hC r)

private abbrev factorL1 {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) : Subgroup (kcoverK hC r) :=
  F.A₁.comap (kcoverPi hC r)

private abbrev factorL2 {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) : Subgroup (kcoverK hC r) :=
  F.A₂.comap (kcoverPi hC r)

private abbrev factorL1' {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) : Subgroup (kcoverK hC r) :=
  ⁅factorL1 F, factorL1 F⁆

private abbrev factorL2' {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) : Subgroup (kcoverK hC r) :=
  ⁅factorL2 F, factorL2 F⁆

private abbrev factorPi1 {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) : factorL1 F →* kcoverQ hC r :=
  (kcoverPi hC r).comp (factorL1 F).subtype

private abbrev factorPi2 {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) : factorL2 F →* kcoverQ hC r :=
  (kcoverPi hC r).comp (factorL2 F).subtype

private structure FactorMaps {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) : Prop where
  hsupLam : factorL1 F ⊔ factorL2 F = commutator (kcoverK hC r)
  hinfLam : factorL1 F ⊓ factorL2 F = kcoverR hC r
  hmapLam1 : (factorL1 F).map (kcoverPi hC r) = F.A₁
  hmapLam2 : (factorL2 F).map (kcoverPi hC r) = F.A₂
  hmapL1' : (factorL1' F).map (kcoverPi hC r) = F.A₁
  hmapL2' : (factorL2' F).map (kcoverPi hC r) = F.A₂

private structure FactorLifts {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) (M : FactorMaps F) : Prop where
  hker₁ : (factorPi1 F).ker = (kcoverR hC r).subgroupOf (factorL1 F)
  hrange₁ : (factorPi1 F).range = F.A₁
  hperf₁ : commutator ↥(factorL1 F) ⊔ (kcoverR hC r).subgroupOf (factorL1 F) = ⊤
  hker₂ : (factorPi2 F).ker = (kcoverR hC r).subgroupOf (factorL2 F)
  hrange₂ : (factorPi2 F).range = F.A₂
  hperf₂ : commutator ↥(factorL2 F) ⊔ (kcoverR hC r).subgroupOf (factorL2 F) = ⊤
  hL1_eq : factorL1 F = factorL1' F ⊔ kcoverR hC r
  hL2_eq : factorL2 F = factorL2' F ⊔ kcoverR hC r
  hcomm : ∀ a ∈ factorL1 F, ∀ b ∈ factorL2 F, Commute a b

private structure FactorDecomp {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) (M : FactorMaps F) : Prop where
  hH2eq : ⁅commutator (kcoverK hC r), commutator (kcoverK hC r)⁆ =
    factorL1' F ⊔ factorL2' F
  hdecomp : commutator (kcoverK hC r) =
    ⁅commutator (kcoverK hC r), commutator (kcoverK hC r)⁆ ⊔ kcoverR hC r
  hRleL12 : kcoverR hC r ≤ factorL1' F ⊔ factorL2' F
  hK_decomp : kcoverR hC r =
    (factorL1' F ⊓ kcoverR hC r) ⊔ (factorL2' F ⊓ kcoverR hC r)

private structure FirstCover {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) (M : FactorMaps F) (Dec : FactorDecomp F M) : Prop where
  hL1'K_eq : factorL1' F ⊓ kcoverR hC r = factorL2' F ⊓ kcoverR hC r
  hRleL1' : kcoverR hC r ≤ factorL1' F
  hperfect1 : Group.IsPerfect ↥(factorL1 F)
  hcenterL1 : Subgroup.center (factorL1 F) =
    (kcoverR hC r).subgroupOf (factorL1 F)
  hSL1 : Nonempty (factorL1 F ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))

private structure SecondCover {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) (M : FactorMaps F) (Dec : FactorDecomp F M)
    (C1 : FirstCover F M Dec) : Prop where
  hRleL2' : kcoverR hC r ≤ factorL2' F
  hperfect2 : Group.IsPerfect ↥(factorL2 F)
  hcenterL2 : Subgroup.center (factorL2 F) =
    (kcoverR hC r).subgroupOf (factorL2 F)
  hSL2 : Nonempty (factorL2 F ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))

private lemma center_eq_bot_of_simple_card_sixty {A : Type} [Group A] [Finite A]
    (hsimple : IsSimpleGroup A) (hcard : Nat.card A = 60) :
    Subgroup.center A = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center A) with h | h
  · exact h
  · exfalso
    have hcommA : IsMulCommutative A := by
      rw [isMulCommutative_iff]
      intro x y
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm
    haveI := hcommA
    have hp : Nat.Prime (Nat.card A) := (Group.is_simple_iff_prime_card).mp hsimple
    rw [hcard] at hp
    exact absurd hp (by norm_num)

private lemma factorBase
    (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Nonempty (FactorBase hC r) := by
  classical
  let e : G := frameE hC r
  let K : Subgroup G := localGroup D e
  let R : Subgroup K := CFSG.solvableRadical K
  let Q : Type := K ⧸ R
  let π : K →* Q := QuotientGroup.mk' R
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hsetupK : Setup K (localSet D e) :=
    setup_localGroup_of_transitive hC.setup (d_mem_centSet h hF)
      (transitive_pair_of_transitive (z := frameE hC r) (u := hC.d)
        (transitive (hC := hC) (S := S) (T := T) (r := r) h hF))
  have hmapComm : (commutator K).map π = commutator Q := by
    simp only [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hπsurj]
  have heK : e ∈ K := frameE_mem_localGroup h hF
  have heR : (⟨e, heK⟩ : K) ∈ R := by
    have hmem : e ∈ R.map K.subtype := by
      rw [solvableRadical_localGroup h hF]
      exact Subgroup.mem_zpowers e
    obtain ⟨r, hr, hr'⟩ := Subgroup.mem_map.mp hmem
    have hr'' : r = ⟨e, heK⟩ := Subtype.ext hr'
    rwa [hr''] at hr
  have hRcard : Nat.card R = 2 := by
    have hcardmap : Nat.card (R.map K.subtype) = Nat.card R :=
      Subgroup.card_map_of_injective K.subtype_injective
    rw [solvableRadical_localGroup h hF, Nat.card_zpowers, orderOf_frameE h hF] at hcardmap
    exact hcardmap.symm
  have hRcenter : R ≤ Subgroup.center K := by
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hr' : (r : G) ∈ Subgroup.zpowers e := by
      have : (r : G) ∈ R.map K.subtype := ⟨r, hr, rfl⟩
      rwa [solvableRadical_localGroup h hF] at this
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hr'
    have hcy : Commute (r : G) (y : G) := by
      rw [← hn]
      exact (commute_frameE h hF (y : K) y.2).symm.zpow_left n
    exact hcy.eq.symm
  exact ⟨{
    hsetupK := hsetupK
    hmapComm := hmapComm
    heK := heK
    heR := heR
    hRcard := hRcard
    hRcenter := hRcenter }⟩

private lemma factorSetup_exists
    (h91 : Theorem9_1) (h : ElevenTwoHyp hC)
    (hF : ElevenTwoFrame hC S T r) (B : FactorBase hC r)
    (φ : kcoverQ hC r ≃* L2Wreath 2 2)
    (eAlt : CFSG.Theory.Comparator.PSL2Model 2 ≃* alternatingGroup (Fin 5)) :
    Nonempty (FactorSetup hC r) := by
  classical
  let e : G := frameE hC r
  let K : Subgroup G := localGroup D e
  let R : Subgroup K := CFSG.solvableRadical K
  let Q : Type := K ⧸ R
  let π : K →* Q := QuotientGroup.mk' R
  obtain ⟨A₁, A₂, hA1, hA2, hcommAB, hinfAB, hsupAB, hidxAB, hswapAB⟩ :=
    exists_factors_l2Wreath_two φ
  have hRle : R ≤ commutator K :=
    le_commutator_of_index_commutator_quotient R B.hsetupK.index_commutator_le_two hidxAB
  have hRleLam1 : R ≤ A₁.comap π := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact A₁.one_mem
  have hRleLam2 : R ≤ A₂.comap π := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact A₂.one_mem
  let Lam1 : Subgroup K := A₁.comap π
  let Lam2 : Subgroup K := A₂.comap π
  let L1' : Subgroup K := ⁅Lam1, Lam1⁆
  let L2' : Subgroup K := ⁅Lam2, Lam2⁆
  let eA₁ : A₁ ≃* CFSG.Theory.Comparator.PSL2Model 2 := Classical.choice hA1
  let eA₂ : A₂ ≃* CFSG.Theory.Comparator.PSL2Model 2 := Classical.choice hA2
  let eA : A₁ ≃* alternatingGroup (Fin 5) := eA₁.trans eAlt
  let eA2 : A₂ ≃* alternatingGroup (Fin 5) := eA₂.trans eAlt
  haveI hperfAlt : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  haveI hperfA1 : Group.IsPerfect ↥A₁ :=
    Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
  haveI hperfA2 : Group.IsPerfect ↥A₂ :=
    Group.IsPerfect.ofSurjective (f := eA2.symm.toMonoidHom) eA2.symm.surjective
  have hsimpleA1 : IsSimpleGroup ↥A₁ := MulEquiv.isSimpleGroup eA
  have hsimpleA2 : IsSimpleGroup ↥A₂ := MulEquiv.isSimpleGroup eA2
  have hcardA1 : Nat.card ↥A₁ = 60 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcardA2 : Nat.card ↥A₂ = 60 := by
    rw [Nat.card_congr eA2.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcenterA1 : Subgroup.center ↥A₁ = ⊥ :=
    center_eq_bot_of_simple_card_sixty hsimpleA1 hcardA1
  have hcenterA2 : Subgroup.center ↥A₂ = ⊥ :=
    center_eq_bot_of_simple_card_sixty hsimpleA2 hcardA2
  exact ⟨{
    toFactorBase := B
    hRle := hRle
    A₁ := A₁
    A₂ := A₂
    hA1 := hA1
    hA2 := hA2
    hcommAB := hcommAB
    hinfAB := hinfAB
    hsupAB := hsupAB
    hidxAB := hidxAB
    hswapAB := hswapAB
    eA := eA
    eA2 := eA2
    hperfA1 := hperfA1
    hperfA2 := hperfA2
    hcenterA1 := hcenterA1
    hcenterA2 := hcenterA2
    hRleLam1 := hRleLam1
    hRleLam2 := hRleLam2 }⟩

private lemma factorMaps (F : FactorSetup hC r) : Nonempty (FactorMaps F) := by
  classical
  let K : Subgroup G := kcoverK hC r
  let R : Subgroup K := kcoverR hC r
  let Q : Type := kcoverQ hC r
  let π : K →* Q := kcoverPi hC r
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hπker : π.ker = R := QuotientGroup.ker_mk' R
  have hπrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπsurj
  have hmapComm : (commutator K).map π = commutator Q := F.hmapComm
  let A₁ : Subgroup Q := F.A₁
  let A₂ : Subgroup Q := F.A₂
  let Lam1 : Subgroup K := A₁.comap π
  let Lam2 : Subgroup K := A₂.comap π
  let L1' : Subgroup K := ⁅Lam1, Lam1⁆
  let L2' : Subgroup K := ⁅Lam2, Lam2⁆
  have hRleLam1 : R ≤ A₁.comap π := F.hRleLam1
  have hRleLam2 : R ≤ A₂.comap π := F.hRleLam2
  have hperfA1 : Group.IsPerfect ↥A₁ := F.hperfA1
  have hperfA2 : Group.IsPerfect ↥A₂ := F.hperfA2
  have hsupAB : A₁ ⊔ A₂ = commutator Q := F.hsupAB
  have hinfAB : A₁ ⊓ A₂ = ⊥ := F.hinfAB
  have hRle : R ≤ commutator K := F.hRle
  have hsupLam : Lam1 ⊔ Lam2 = commutator K := by
    have hker_le : π.ker ≤ Lam1 ⊔ Lam2 := by
      rw [hπker]
      exact hRleLam1.trans le_sup_left
    have hmapSup : (Lam1 ⊔ Lam2).map π = (commutator K).map π := by
      rw [Subgroup.map_sup]
      rw [show Lam1 = A₁.comap π from rfl, show Lam2 = A₂.comap π from rfl]
      rw [Subgroup.map_comap_eq_self (H := A₁) (by rw [hπrange]; exact le_top),
        Subgroup.map_comap_eq_self (H := A₂) (by rw [hπrange]; exact le_top),
        hsupAB, hmapComm]
    calc Lam1 ⊔ Lam2
        = Subgroup.comap π ((Lam1 ⊔ Lam2).map π) :=
          (Subgroup.comap_map_eq_self hker_le).symm
      _ = Subgroup.comap π ((commutator K).map π) := by rw [hmapSup]
      _ = commutator K := Subgroup.comap_map_eq_self (by rw [hπker]; exact hRle)
  have hinfLam : Lam1 ⊓ Lam2 = R := by
    have h1 : Lam1 ⊓ Lam2 = (A₁ ⊓ A₂).comap π := by rw [Subgroup.comap_inf]
    rw [h1, hinfAB]
    change π.ker = R
    exact hπker
  have hmapLam1 : Lam1.map π = A₁ := by
    rw [show Lam1 = A₁.comap π from rfl,
      Subgroup.map_comap_eq_self (by rw [hπrange]; exact le_top)]
  have hmapLam2 : Lam2.map π = A₂ := by
    rw [show Lam2 = A₂.comap π from rfl,
      Subgroup.map_comap_eq_self (by rw [hπrange]; exact le_top)]
  have hmapL1' : L1'.map π = A₁ := by
    show (⁅Lam1, Lam1⁆ : Subgroup K).map π = A₁
    rw [Subgroup.map_commutator, hmapLam1]
    exact Subgroup.isPerfect_iff.mp hperfA1
  have hmapL2' : L2'.map π = A₂ := by
    show (⁅Lam2, Lam2⁆ : Subgroup K).map π = A₂
    rw [Subgroup.map_commutator, hmapLam2]
    exact Subgroup.isPerfect_iff.mp hperfA2
  exact ⟨{
    hsupLam := hsupLam
    hinfLam := hinfLam
    hmapLam1 := hmapLam1
    hmapLam2 := hmapLam2
    hmapL1' := hmapL1'
    hmapL2' := hmapL2' }⟩

private structure FactorLift1 {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (F : FactorSetup hC r) (M : FactorMaps F) : Prop where
  hker₁ : (factorPi1 F).ker = (kcoverR hC r).subgroupOf (factorL1 F)
  hrange₁ : (factorPi1 F).range = F.A₁
  hperf₁ : commutator ↥(factorL1 F) ⊔ (kcoverR hC r).subgroupOf (factorL1 F) = ⊤
  hL1_eq : factorL1 F = factorL1' F ⊔ kcoverR hC r

private lemma factorLift_first (F : FactorSetup hC r) (M : FactorMaps F) :
    Nonempty (FactorLift1 F M) := by
  classical
  let K : Subgroup G := kcoverK hC r
  let R : Subgroup K := kcoverR hC r
  let Q : Type := kcoverQ hC r
  let π : K →* Q := kcoverPi hC r
  let A₁ : Subgroup Q := F.A₁
  let Lam1 : Subgroup K := A₁.comap π
  let L1' : Subgroup K := ⁅Lam1, Lam1⁆
  have hπker : π.ker = R := QuotientGroup.ker_mk' R
  have hπrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective R)
  have hperfA1 : Group.IsPerfect ↥A₁ := F.hperfA1
  have hmapLam1 : Lam1.map π = A₁ := M.hmapLam1
  have hmapL1' : L1'.map π = A₁ := M.hmapL1'
  let π₁ : Lam1 →* Q := π.comp Lam1.subtype
  have hker₁ : π₁.ker = R.subgroupOf Lam1 := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπker]
    rfl
  have hrange₁ : π₁.range = A₁ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change Subgroup.map π Lam1 = A₁
    rw [show Lam1 = A₁.comap π from rfl, Subgroup.map_comap_eq, hπrange, top_inf_eq]
  have hmap₁ : (commutator ↥Lam1).map π₁ = A₁ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, hrange₁]
    exact Subgroup.isPerfect_iff.mp hperfA1
  have hperf₁ : commutator ↥Lam1 ⊔ R.subgroupOf Lam1 = ⊤ := by
    have hmapS : (commutator ↥Lam1 ⊔ π₁.ker).map π₁ = A₁ := by
      rw [Subgroup.map_sup, hmap₁]
      have : (π₁.ker).map π₁ = ⊥ := (Subgroup.map_eq_bot_iff (π₁.ker)).mpr le_rfl
      rw [this, sup_bot_eq]
    have hcomapA : Subgroup.comap π₁ A₁ = ⊤ := by
      apply (Subgroup.eq_top_iff' (Subgroup.comap π₁ A₁)).mpr
      intro x
      rw [Subgroup.mem_comap, ← hrange₁]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    calc commutator ↥Lam1 ⊔ R.subgroupOf Lam1
        = commutator ↥Lam1 ⊔ π₁.ker := by rw [hker₁]
      _ = Subgroup.comap π₁ ((commutator ↥Lam1 ⊔ π₁.ker).map π₁) :=
          (Subgroup.comap_map_eq_self le_sup_right).symm
      _ = Subgroup.comap π₁ A₁ := by rw [hmapS]
      _ = ⊤ := hcomapA
  have hL1_eq : Lam1 = L1' ⊔ R := by
    apply le_antisymm
    · intro x hx
      have hxA : π x ∈ A₁ := Subgroup.mem_comap.mp hx
      have hxmap : π x ∈ L1'.map π := by rw [hmapL1']; exact hxA
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
      have hyR : y⁻¹ * x ∈ R := by
        rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have hx_eq : x = y * (y⁻¹ * x) := by group
      rw [hx_eq]
      exact Subgroup.mul_mem_sup hy hyR
    · exact sup_le (by simpa using Subgroup.commutator_le_sup Lam1 Lam1) F.hRleLam1
  exact ⟨{
    hker₁ := hker₁
    hrange₁ := hrange₁
    hperf₁ := hperf₁
    hL1_eq := hL1_eq }⟩

private lemma factorLifts (F : FactorSetup hC r) (M : FactorMaps F) :
    Nonempty (FactorLifts F M) := by
  classical
  obtain ⟨L1⟩ := factorLift_first F M
  let K : Subgroup G := kcoverK hC r
  let R : Subgroup K := kcoverR hC r
  let Q : Type := kcoverQ hC r
  let π : K →* Q := kcoverPi hC r
  let A₁ : Subgroup Q := F.A₁
  let A₂ : Subgroup Q := F.A₂
  let Lam2 : Subgroup K := A₂.comap π
  let L2' : Subgroup K := ⁅Lam2, Lam2⁆
  have hπker : π.ker = R := QuotientGroup.ker_mk' R
  have hπrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective R)
  have hperfA2 : Group.IsPerfect ↥A₂ := F.hperfA2
  have hmapLam2 : Lam2.map π = A₂ := M.hmapLam2
  have hmapL2' : L2'.map π = A₂ := M.hmapL2'
  have hcommAB : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b := F.hcommAB
  have hRcenter : R ≤ Subgroup.center K := F.hRcenter
  let π₂ : Lam2 →* Q := π.comp Lam2.subtype
  have hker₂ : π₂.ker = R.subgroupOf Lam2 := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπker]
    rfl
  have hrange₂ : π₂.range = A₂ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change Subgroup.map π Lam2 = A₂
    rw [show Lam2 = A₂.comap π from rfl, Subgroup.map_comap_eq, hπrange, top_inf_eq]
  have hmap₂ : (commutator ↥Lam2).map π₂ = A₂ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, hrange₂]
    exact Subgroup.isPerfect_iff.mp hperfA2
  have hperf₂ : commutator ↥Lam2 ⊔ R.subgroupOf Lam2 = ⊤ := by
    have hmapS : (commutator ↥Lam2 ⊔ π₂.ker).map π₂ = A₂ := by
      rw [Subgroup.map_sup, hmap₂]
      have : (π₂.ker).map π₂ = ⊥ := (Subgroup.map_eq_bot_iff (π₂.ker)).mpr le_rfl
      rw [this, sup_bot_eq]
    have hcomapA : Subgroup.comap π₂ A₂ = ⊤ := by
      apply (Subgroup.eq_top_iff' (Subgroup.comap π₂ A₂)).mpr
      intro x
      rw [Subgroup.mem_comap, ← hrange₂]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    calc commutator ↥Lam2 ⊔ R.subgroupOf Lam2
        = commutator ↥Lam2 ⊔ π₂.ker := by rw [hker₂]
      _ = Subgroup.comap π₂ ((commutator ↥Lam2 ⊔ π₂.ker).map π₂) :=
          (Subgroup.comap_map_eq_self le_sup_right).symm
      _ = Subgroup.comap π₂ A₂ := by rw [hmapS]
      _ = ⊤ := hcomapA
  have hL2_eq : Lam2 = L2' ⊔ R := by
    apply le_antisymm
    · intro x hx
      have hxA : π x ∈ A₂ := Subgroup.mem_comap.mp hx
      have hxmap : π x ∈ L2'.map π := by rw [hmapL2']; exact hxA
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
      have hyR : y⁻¹ * x ∈ R := by
        rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      have hx_eq : x = y * (y⁻¹ * x) := by group
      rw [hx_eq]
      exact Subgroup.mul_mem_sup hy hyR
    · exact sup_le (by simpa using Subgroup.commutator_le_sup Lam2 Lam2) F.hRleLam2
  have hcomm : ∀ a ∈ factorL1 F, ∀ b ∈ factorL2 F, Commute a b := by
    intro a ha b hb
    have hmem : ∀ x ∈ factorL1 F, ⁅x, b⁆ ∈ R := by
      intro x hx
      have hxA : π x ∈ A₁ := Subgroup.mem_comap.mp hx
      have hbB : π b ∈ A₂ := Subgroup.mem_comap.mp hb
      have h1 : π ⁅x, b⁆ = 1 := by
        rw [map_commutatorElement]
        exact (hcommAB (π x) hxA (π b) hbB).commutator_eq
      exact (QuotientGroup.eq_one_iff ⁅x, b⁆).mp h1
    exact comm_of_perfect R hRcenter (factorL1 F) L1.hperf₁ hmem a ha
  exact ⟨{
    hker₁ := L1.hker₁
    hrange₁ := L1.hrange₁
    hperf₁ := L1.hperf₁
    hker₂ := hker₂
    hrange₂ := hrange₂
    hperf₂ := hperf₂
    hL1_eq := L1.hL1_eq
    hL2_eq := hL2_eq
    hcomm := hcomm }⟩

private lemma factorDecomp (F : FactorSetup hC r) (M : FactorMaps F)
    (L : FactorLifts F M) : Nonempty (FactorDecomp F M) := by
  classical
  let K : Subgroup G := kcoverK hC r
  let R : Subgroup K := kcoverR hC r
  let Q : Type := kcoverQ hC r
  let π : K →* Q := kcoverPi hC r
  let A₁ : Subgroup Q := F.A₁
  let A₂ : Subgroup Q := F.A₂
  let Lam1 : Subgroup K := A₁.comap π
  let Lam2 : Subgroup K := A₂.comap π
  let L1' : Subgroup K := ⁅Lam1, Lam1⁆
  let L2' : Subgroup K := ⁅Lam2, Lam2⁆
  have hπker : π.ker = R := QuotientGroup.ker_mk' R
  have hinfAB : A₁ ⊓ A₂ = ⊥ := F.hinfAB
  have hRcenter : R ≤ Subgroup.center K := F.hRcenter
  have hsetupK : Setup K (localSet D (frameE hC r)) := F.hsetupK
  have hsupLam : Lam1 ⊔ Lam2 = commutator K := M.hsupLam
  have hL1_eq : Lam1 = L1' ⊔ R := L.hL1_eq
  have hL2_eq : Lam2 = L2' ⊔ R := L.hL2_eq
  have hcomm : ∀ a ∈ Lam1, ∀ b ∈ Lam2, Commute a b := L.hcomm
  have hH1sup : commutator K = Lam1 ⊔ Lam2 := hsupLam.symm
  have hH2eq : ⁅commutator K, commutator K⁆ = L1' ⊔ L2' := by
    apply le_antisymm
    · rw [hH1sup, Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨x1, hx1, x2, hx2, rfl⟩ := (mem_sup_of_commute hcomm).mp hx
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := (mem_sup_of_commute hcomm).mp hy
      have hm1 : ⁅x1, y1⁆ ∈ Lam1 := by
        simpa using (Subgroup.commutator_le_sup Lam1 Lam1)
          (Subgroup.commutator_mem_commutator hx1 hy1)
      have hm2 : ⁅x2, y2⁆ ∈ Lam2 := by
        simpa using (Subgroup.commutator_le_sup Lam2 Lam2)
          (Subgroup.commutator_mem_commutator hx2 hy2)
      have h := TauCeti.commutatorElement_mul_mul_eq_mul_of_commute
        (hcomm y1 hy1 x2 hx2).symm (hcomm x1 hx1 y2 hy2)
        (hcomm y1 hy1 ⁅x2, y2⁆ hm2) (hcomm x1 hx1 ⁅x2, y2⁆ hm2)
        (hcomm ⁅x1, y1⁆ hm1 ⁅x2, y2⁆ hm2)
      rw [h]
      exact Subgroup.mul_mem_sup (Subgroup.commutator_mem_commutator hx1 hy1)
        (Subgroup.commutator_mem_commutator hx2 hy2)
    · rw [hH1sup]
      exact sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)
  have hdecomp : commutator K = ⁅commutator K, commutator K⁆ ⊔ R := by
    rw [hH2eq, ← hsupLam, hL1_eq, hL2_eq]
    ac_rfl
  obtain ⟨d₀, hd₀⟩ := hsetupK.isClass
  have hRleH2 : R ≤ ⁅commutator K, commutator K⁆ :=
    le_secondCommutator_of_central_sup R hd₀ hsetupK.gen hRcenter hdecomp
  have hRleL12 : R ≤ L1' ⊔ L2' := by
    rwa [hH2eq] at hRleH2
  have hL1'le : L1' ≤ Lam1 := by
    simpa using Subgroup.commutator_le_sup Lam1 Lam1
  have hL2'le : L2' ≤ Lam2 := by
    simpa using Subgroup.commutator_le_sup Lam2 Lam2
  have hcommL1'L2' : ∀ a ∈ L1', ∀ b ∈ L2', Commute a b :=
    fun a ha b hb => hcomm a (hL1'le ha) b (hL2'le hb)
  have hK_decomp : R = (L1' ⊓ R) ⊔ (L2' ⊓ R) := by
    apply le_antisymm
    · intro k hk
      have hkH2 : k ∈ L1' ⊔ L2' := hRleL12 hk
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_commute hcommL1'L2').mp hkH2
      have hpa : π a ∈ A₁ := Subgroup.mem_comap.mp (hL1'le ha)
      have hpb : π b ∈ A₂ := Subgroup.mem_comap.mp (hL2'le hb)
      have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
      have hpab : π a * π b = 1 := by
        rw [← map_mul, hab, hk1]
      have haR : a ∈ R := by
        have hpaB : π a ∈ A₂ := by
          have hpa_eq : π a = (π b)⁻¹ := by
            have h := congrArg (fun z => z * (π b)⁻¹) hpab
            simpa using h
          rw [hpa_eq]
          exact A₂.inv_mem hpb
        have hpa1 : π a = 1 := by
          have : π a ∈ A₁ ⊓ A₂ := ⟨hpa, hpaB⟩
          rw [hinfAB] at this
          exact Subgroup.mem_bot.mp this
        exact (QuotientGroup.eq_one_iff a).mp hpa1
      have hbR : b ∈ R := by
        have hpbA : π b ∈ A₁ := by
          have hpb_eq : π b = (π a)⁻¹ := by
            have h := congrArg (fun z => (π a)⁻¹ * z) hpab
            simpa using h
          rw [hpb_eq]
          exact A₁.inv_mem hpa
        have hpb1 : π b = 1 := by
          have : π b ∈ A₁ ⊓ A₂ := ⟨hpbA, hpb⟩
          rw [hinfAB] at this
          exact Subgroup.mem_bot.mp this
        exact (QuotientGroup.eq_one_iff b).mp hpb1
      rw [← hab]
      exact Subgroup.mul_mem_sup ⟨ha, haR⟩ ⟨hb, hbR⟩
    · exact sup_le inf_le_right inf_le_right
  exact ⟨{
    hH2eq := hH2eq
    hdecomp := hdecomp
    hRleL12 := hRleL12
    hK_decomp := hK_decomp }⟩

private lemma firstCover (F : FactorSetup hC r)
    (M : FactorMaps F) (L : FactorLifts F M) (Dec : FactorDecomp F M) :
    Nonempty (FirstCover F M Dec) := by
  classical
  let K : Subgroup G := kcoverK hC r
  let R : Subgroup K := kcoverR hC r
  let Q : Type := kcoverQ hC r
  let π : K →* Q := kcoverPi hC r
  let A₁ : Subgroup Q := F.A₁
  let A₂ : Subgroup Q := F.A₂
  let Lam1 : Subgroup K := A₁.comap π
  let Lam2 : Subgroup K := A₂.comap π
  let L1' : Subgroup K := ⁅Lam1, Lam1⁆
  let L2' : Subgroup K := ⁅Lam2, Lam2⁆
  let π₁ : Lam1 →* Q := π.comp Lam1.subtype
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hRcenter : R ≤ Subgroup.center K := F.hRcenter
  have hcenterA1 : Subgroup.center ↥A₁ = ⊥ := F.hcenterA1
  have hswapAB : ∀ y : Q, y ∉ commutator Q →
      A₁.map (MulAut.conj y).toMonoidHom = A₂ := F.hswapAB
  have hmapL1' : L1'.map π = A₁ := M.hmapL1'
  have hL1_eq : Lam1 = L1' ⊔ R := L.hL1_eq
  have hRleLam1 : R ≤ A₁.comap π := F.hRleLam1
  have hker₁ : π₁.ker = R.subgroupOf Lam1 := L.hker₁
  have hrange₁ : π₁.range = A₁ := L.hrange₁
  have eA : A₁ ≃* alternatingGroup (Fin 5) := F.eA
  have hRcard : Nat.card R = 2 := F.hRcard
  have hK_decomp : R = (L1' ⊓ R) ⊔ (L2' ⊓ R) := Dec.hK_decomp
  have hidxAB : (commutator Q).index = 2 := F.hidxAB
  have hy_ex : ∃ y : K, π y ∉ commutator Q := by
    have hlt : commutator Q < ⊤ := by
      refine lt_of_le_of_ne le_top (fun hEq => ?_)
      have h1 : (commutator Q).index = 1 := Subgroup.index_eq_one.mpr hEq
      rw [hidxAB] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨y₀, -, hy₀⟩ := SetLike.exists_of_lt hlt
    obtain ⟨y, rfl⟩ := hπsurj y₀
    exact ⟨y, hy₀⟩
  obtain ⟨y, hy⟩ := hy_ex
  have hfixR : ∀ x ∈ R, (MulAut.conj y).toMonoidHom x = x := by
    intro x hx
    have hc : (y : K) * x = x * (y : K) := Subgroup.mem_center_iff.mp (hRcenter hx) y
    change (y : K) * x * (y : K)⁻¹ = x
    rw [hc]
    group
  have hswapLam : Lam1.map (MulAut.conj y).toMonoidHom = Lam2 := by
    rw [show Lam1 = A₁.comap π from rfl, show Lam2 = A₂.comap π from rfl]
    exact map_conj_comap π (hswapAB (π y) hy)
  have hmapL1'conj : L1'.map (MulAut.conj y).toMonoidHom = L2' := by
    show (⁅Lam1, Lam1⁆ : Subgroup K).map (MulAut.conj y).toMonoidHom = L2'
    rw [Subgroup.map_commutator, hswapLam]
  have hL1'K_eq : L1' ⊓ R = L2' ⊓ R := by
    have hfix : ∀ x ∈ L1' ⊓ R, (MulAut.conj y).toMonoidHom x = x :=
      fun x hx => hfixR x (Subgroup.mem_inf.mp hx).2
    calc L1' ⊓ R = (L1' ⊓ R).map (MulAut.conj y).toMonoidHom :=
          (map_eq_self _ _ hfix).symm
      _ = L1'.map (MulAut.conj y).toMonoidHom ⊓
            R.map (MulAut.conj y).toMonoidHom :=
          Subgroup.map_inf L1' R _ (MulAut.conj y).injective
      _ = L2' ⊓ R := by rw [hmapL1'conj, map_eq_self _ R hfixR]
  have hRleL1' : R ≤ L1' := by
    calc R = (L1' ⊓ R) ⊔ (L2' ⊓ R) := hK_decomp
      _ = (L1' ⊓ R) ⊔ (L1' ⊓ R) := by rw [hL1'K_eq]
      _ = L1' ⊓ R := sup_idem _
      _ ≤ L1' := inf_le_left
  have hL1_perf : Lam1 = L1' := by
    calc Lam1 = L1' ⊔ R := hL1_eq
      _ = L1' := sup_eq_left.mpr hRleL1'
  have hperfect1 : Group.IsPerfect ↥Lam1 := Subgroup.isPerfect_iff.mpr hL1_perf.symm
  have hcenterL1 : Subgroup.center Lam1 = R.subgroupOf Lam1 := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxA : π (x : K) ∈ A₁ := Subgroup.mem_comap.mp x.2
      have hxcent : (⟨π (x : K), hxA⟩ : A₁) ∈ Subgroup.center ↥A₁ := by
        rw [Subgroup.mem_center_iff]
        intro a
        apply Subtype.ext
        change a.val * π (x : K) = π (x : K) * a.val
        have ha : a.val ∈ π₁.range := by rw [hrange₁]; exact a.2
        obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp ha
        rw [← hz]
        change π (z : K) * π (x : K) = π (x : K) * π (z : K)
        have hc := Subgroup.mem_center_iff.mp hx z
        have hc' : (z : K) * (x : K) = (x : K) * (z : K) := by
          simpa using congrArg (Subgroup.subtype Lam1) hc
        rw [← map_mul, ← map_mul, hc']
      rw [hcenterA1, Subgroup.mem_bot] at hxcent
      have hx1 : π (x : K) = 1 := congrArg Subtype.val hxcent
      exact (QuotientGroup.eq_one_iff (x : K)).mp hx1
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro z
      have hxcen : (x : K) ∈ Subgroup.center K := hRcenter (Subgroup.mem_subgroupOf.mp hx)
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxcen (z : K))
  have eA1q : Lam1 ⧸ Subgroup.center Lam1 ≃* ↥A₁ :=
    (QuotientGroup.quotientMulEquivOfEq (hcenterL1.trans hker₁.symm)).trans
      ((QuotientGroup.quotientKerEquivRange π₁).trans (MulEquiv.subgroupCongr hrange₁))
  have e1 : Lam1 ⧸ Subgroup.center Lam1 ≃* alternatingGroup (Fin 5) :=
    eA1q.trans eA
  have hcenterCard1 : Nat.card (Subgroup.center Lam1) = 2 := by
    rw [hcenterL1,
      ← Subgroup.card_map_of_injective (K := R.subgroupOf Lam1) Lam1.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hRleLam1, hRcard]
  have hSL1 : Nonempty (Lam1 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    sl2_of_central_extension_alt5 hperfect1 hcenterCard1 e1
  exact ⟨{
    hL1'K_eq := hL1'K_eq
    hRleL1' := hRleL1'
    hperfect1 := hperfect1
    hcenterL1 := hcenterL1
    hSL1 := hSL1 }⟩

private lemma secondCover (F : FactorSetup hC r)
    (M : FactorMaps F) (L : FactorLifts F M) (Dec : FactorDecomp F M)
    (C1 : FirstCover F M Dec) : Nonempty (SecondCover F M Dec C1) := by
  classical
  let K : Subgroup G := kcoverK hC r
  let R : Subgroup K := kcoverR hC r
  let Q : Type := kcoverQ hC r
  let π : K →* Q := kcoverPi hC r
  let A₁ : Subgroup Q := F.A₁
  let A₂ : Subgroup Q := F.A₂
  let Lam1 : Subgroup K := A₁.comap π
  let Lam2 : Subgroup K := A₂.comap π
  let L1' : Subgroup K := ⁅Lam1, Lam1⁆
  let L2' : Subgroup K := ⁅Lam2, Lam2⁆
  let π₂ : Lam2 →* Q := π.comp Lam2.subtype
  have hRcenter : R ≤ Subgroup.center K := F.hRcenter
  have hcenterA2 : Subgroup.center ↥A₂ = ⊥ := F.hcenterA2
  have hRleLam2 : R ≤ A₂.comap π := F.hRleLam2
  have hker₂ : π₂.ker = R.subgroupOf Lam2 := L.hker₂
  have hrange₂ : π₂.range = A₂ := L.hrange₂
  have eA2 : A₂ ≃* alternatingGroup (Fin 5) := F.eA2
  have hRcard : Nat.card R = 2 := F.hRcard
  have hK_decomp : R = (L1' ⊓ R) ⊔ (L2' ⊓ R) := Dec.hK_decomp
  have hL1'K_eq : L1' ⊓ R = L2' ⊓ R := C1.hL1'K_eq
  have hL2_eq : Lam2 = L2' ⊔ R := L.hL2_eq
  have hRleL2' : R ≤ L2' := by
    calc R = (L1' ⊓ R) ⊔ (L2' ⊓ R) := hK_decomp
      _ = (L2' ⊓ R) ⊔ (L2' ⊓ R) := by rw [← hL1'K_eq]
      _ = L2' ⊓ R := sup_idem _
      _ ≤ L2' := inf_le_left
  have hL2_perf : Lam2 = L2' := by
    calc Lam2 = L2' ⊔ R := hL2_eq
      _ = L2' := sup_eq_left.mpr hRleL2'
  have hperfect2 : Group.IsPerfect ↥Lam2 := Subgroup.isPerfect_iff.mpr hL2_perf.symm
  have hcenterL2 : Subgroup.center Lam2 = R.subgroupOf Lam2 := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxA : π (x : K) ∈ A₂ := Subgroup.mem_comap.mp x.2
      have hxcent : (⟨π (x : K), hxA⟩ : A₂) ∈ Subgroup.center ↥A₂ := by
        rw [Subgroup.mem_center_iff]
        intro a
        apply Subtype.ext
        change a.val * π (x : K) = π (x : K) * a.val
        have ha : a.val ∈ π₂.range := by rw [hrange₂]; exact a.2
        obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp ha
        rw [← hz]
        change π (z : K) * π (x : K) = π (x : K) * π (z : K)
        have hc := Subgroup.mem_center_iff.mp hx z
        have hc' : (z : K) * (x : K) = (x : K) * (z : K) := by
          simpa using congrArg (Subgroup.subtype Lam2) hc
        rw [← map_mul, ← map_mul, hc']
      rw [hcenterA2, Subgroup.mem_bot] at hxcent
      have hx1 : π (x : K) = 1 := congrArg Subtype.val hxcent
      exact (QuotientGroup.eq_one_iff (x : K)).mp hx1
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro z
      have hxcen : (x : K) ∈ Subgroup.center K := hRcenter (Subgroup.mem_subgroupOf.mp hx)
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxcen (z : K))
  have eA2q : Lam2 ⧸ Subgroup.center Lam2 ≃* ↥A₂ :=
    (QuotientGroup.quotientMulEquivOfEq (hcenterL2.trans hker₂.symm)).trans
      ((QuotientGroup.quotientKerEquivRange π₂).trans (MulEquiv.subgroupCongr hrange₂))
  have e2 : Lam2 ⧸ Subgroup.center Lam2 ≃* alternatingGroup (Fin 5) :=
    eA2q.trans eA2
  have hcenterCard2 : Nat.card (Subgroup.center Lam2) = 2 := by
    rw [hcenterL2,
      ← Subgroup.card_map_of_injective (K := R.subgroupOf Lam2) Lam2.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hRleLam2, hRcard]
  have hSL2 : Nonempty (Lam2 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    sl2_of_central_extension_alt5 hperfect2 hcenterCard2 e2
  exact ⟨{
    hRleL2' := hRleL2'
    hperfect2 := hperfect2
    hcenterL2 := hcenterL2
    hSL2 := hSL2 }⟩

theorem exists_sl25 (h91 : Theorem9_1) (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ∃ L₁ L₂ : Subgroup G,
      Nonempty (L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      Nonempty (L₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      (∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) ∧ L₁ ⊓ L₂ = Subgroup.zpowers (frameE hC r) ∧
      L₁ ⊔ L₂ ≤ localGroup D (frameE hC r) ∧ L₁ ⊔ L₂ ≤ commutator G ∧
      Nat.card (localGroup D (frameE hC r)) = 2 * Nat.card ↥(L₁ ⊔ L₂) := by
  classical
  obtain ⟨φ⟩ := nonempty_kbar_mulEquiv (hC := hC) (S := S) (T := T) (r := r) h91 h hF
  obtain ⟨eAlt⟩ := CFSG.Timmesfeld.Bridge.Asc72.AltFive.nonempty_psl2Model_two_equiv
  obtain ⟨B⟩ := factorBase (hC := hC) (S := S) (T := T) (r := r) h hF
  obtain ⟨F⟩ := factorSetup_exists (hC := hC) (S := S) (T := T) (r := r) h91 h hF B φ eAlt
  obtain ⟨M⟩ := factorMaps F
  obtain ⟨L⟩ := factorLifts F M
  obtain ⟨Dec⟩ := factorDecomp F M L
  obtain ⟨C1⟩ := firstCover F M L Dec
  obtain ⟨C2⟩ := secondCover F M L Dec C1
  let e : G := frameE hC r
  let K : Subgroup G := localGroup D e
  let R : Subgroup K := CFSG.solvableRadical K
  let Q : Type := K ⧸ R
  let π : K →* Q := QuotientGroup.mk' R
  let Lam1 : Subgroup K := F.A₁.comap π
  let Lam2 : Subgroup K := F.A₂.comap π
  let L₁ : Subgroup G := Lam1.map K.subtype
  let L₂ : Subgroup G := Lam2.map K.subtype
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hπrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπsurj
  have hsetupK : Setup K (localSet D e) := F.hsetupK
  have hmapComm : (commutator K).map π = commutator Q := F.hmapComm
  have hidxAB : (commutator Q).index = 2 := F.hidxAB
  have hsupLam : Lam1 ⊔ Lam2 = commutator K := M.hsupLam
  have hinfLam : Lam1 ⊓ Lam2 = R := M.hinfLam
  have hcomm : ∀ a ∈ Lam1, ∀ b ∈ Lam2, Commute a b := L.hcomm
  have hSL1 : Nonempty (Lam1 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := C1.hSL1
  have hSL2 : Nonempty (Lam2 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := C2.hSL2
  let L₁ : Subgroup G := Lam1.map K.subtype
  let L₂ : Subgroup G := Lam2.map K.subtype
  have hK'idx : (commutator K).index = 2 := by
    refine le_antisymm hsetupK.index_commutator_le_two ?_
    have hne : (commutator K).index ≠ 1 := by
      intro h1
      have htop : commutator K = ⊤ := Subgroup.index_eq_one.mp h1
      have hmap := hmapComm
      rw [htop, Subgroup.map_top, hπrange] at hmap
      have h1' : (commutator Q).index = 1 := Subgroup.index_eq_one.mpr hmap.symm
      rw [hidxAB] at h1'
      exact absurd h1' (by norm_num)
    have hpos : 0 < (commutator K).index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    omega
  have hsupEq : L₁ ⊔ L₂ = (commutator K).map K.subtype := by
    rw [show L₁ = Lam1.map K.subtype from rfl, show L₂ = Lam2.map K.subtype from rfl,
      ← Subgroup.map_sup, hsupLam]
  refine ⟨L₁, L₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨eSL⟩ := hSL1
    exact ⟨(Subgroup.equivMapOfInjective Lam1 K.subtype K.subtype_injective).symm.trans eSL⟩
  · obtain ⟨eSL⟩ := hSL2
    exact ⟨(Subgroup.equivMapOfInjective Lam2 K.subtype K.subtype_injective).symm.trans eSL⟩
  · intro a ha b hb
    rw [show L₁ = Lam1.map K.subtype from rfl] at ha
    rw [show L₂ = Lam2.map K.subtype from rfl] at hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact (hcomm a' ha' b' hb').map K.subtype
  · calc L₁ ⊓ L₂ = (Lam1.map K.subtype) ⊓ (Lam2.map K.subtype) := rfl
      _ = (Lam1 ⊓ Lam2).map K.subtype :=
          (Subgroup.map_inf Lam1 Lam2 K.subtype K.subtype_injective).symm
      _ = R.map K.subtype := by rw [hinfLam]
      _ = Subgroup.zpowers e := solvableRadical_localGroup h hF
      _ = Subgroup.zpowers (frameE hC r) := rfl
  · rw [hsupEq]
    exact Subgroup.map_subtype_le (commutator K)
  · rw [hsupEq]
    exact (Subgroup.map_subtype_commutator K).trans_le
      (by rw [_root_.commutator_def]; exact Subgroup.commutator_mono le_top le_top)
  · have hcardSup : Nat.card ↥(L₁ ⊔ L₂) = Nat.card (commutator K) := by
      rw [hsupEq]
      exact Subgroup.card_map_of_injective K.subtype_injective
    have hKcard : Nat.card K = 14400 :=
      card_localGroup (hC := hC) (S := S) (T := T) (r := r) h91 h hF
    have hcardK' : Nat.card (commutator K) = 7200 := by
      have h := Subgroup.card_mul_index (commutator K)
      rw [hK'idx, hKcard] at h
      omega
    change Nat.card K = 2 * Nat.card ↥(L₁ ⊔ L₂)
    rw [hKcard, hcardSup, hcardK']


theorem card_centralizer_e (h91 : Theorem9_1) (h : ElevenTwoHyp hC)
    (hF : ElevenTwoFrame hC S T r) :
    Nat.card (Subgroup.centralizer {frameE hC r}) =
      2 * Nat.card (localGroup D (frameE hC r)) := by
  classical
  let e : G := frameE hC r
  let K : Subgroup G := localGroup D e
  let Q : Type := K ⧸ CFSG.solvableRadical K
  let Γ : Set G := centSet D e
  have huΓ : hC.d ∈ Γ := d_mem_centSet h hF
  have hQcard : Nat.card Q = 7200 := by
    obtain ⟨φ⟩ := nonempty_kbar_mulEquiv (hC := hC) (S := S) (T := T) (r := r) h91 h hF
    exact (Nat.card_congr φ.toEquiv).trans card_l2Wreath_two_two
  have hsetupBar : Setup Q (centSetBar D e) :=
    setup_kbar (hC := hC) (S := S) (T := T) (r := r) h hF
  letI hNbar : CFSG.GroupTheory.NormalizesSet (⊤ : Subgroup Q) (centSetBar D e) :=
    ⟨fun a _ x hx => hsetupBar.conj_mem a hx⟩
  have hpreBar : IsPretransitive Q ↥(centSetBar D e) := by
    apply MulAction.IsPretransitive.mk
    intro x y
    obtain ⟨g, hg⟩ := isConj_iff.mp (hsetupBar.isConj x.2 y.2)
    exact ⟨g, by
      apply Subtype.ext
      change g * x.1 * g⁻¹ = y.1
      exact hg⟩
  let xBar : ↥(centSetBar D e) :=
    ⟨mkCentSet D e hC.d huΓ, mem_centSetBar_mkCentSet huΓ⟩
  have hCbar : Nat.card (Subgroup.centralizer {(xBar : Q)}) = 120 :=
    card_centralizer_kbar (hC := hC) (S := S) (T := T) (r := r) h91 h hF huΓ
  have hGammaBar : Nat.card ↥(centSetBar D e) = 60 := by
    have h := card_centralizer_mul_card_of_pretransitive hpreBar xBar
    rw [hCbar, hQcard] at h
    omega
  have himage : (Subtype.val : K → G) '' (localSet D e) = Γ := by
    show (Subtype.val : K → G) '' (Subtype.val ⁻¹' centSet D e) = centSet D e
    rw [Set.image_preimage_eq_of_subset]
    intro y hy
    exact ⟨⟨y, mem_localGroup_of_mem hy⟩, rfl⟩
  have hGamma : Nat.card ↥Γ = 60 := by
    have hlocal : (centSet D e).ncard = (localSet D e).ncard :=
      calc (centSet D e).ncard = ((Subtype.val : K → G) '' localSet D e).ncard := by
            rw [himage]
        _ = (localSet D e).ncard :=
            Set.ncard_image_of_injective _ Subtype.val_injective
    have hbar : (centSetBar D e).ncard = (localSet D e).ncard := by
      have h := Set.InjOn.ncard_image (f := QuotientGroup.mk' (CFSG.solvableRadical K))
        (injOn_kbar (hC := hC) (S := S) (T := T) (r := r) h hF)
      rwa [show (QuotientGroup.mk' (CFSG.solvableRadical K)) '' localSet D e =
        centSetBar D e from rfl] at h
    have hGamma' : (centSet D e).ncard = 60 := by
      rw [hlocal, ← hbar]
      exact hGammaBar
    exact hGamma'
  let A : Subgroup G := Subgroup.centralizer {e}
  have hKA : K ≤ A := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_frameE (hC := hC) (S := S) (T := T) (r := r) h hF k hk
  have hbase : ∀ x ∈ Γ, ∃ k ∈ K, k * hC.d * k⁻¹ = x :=
    transitive (hC := hC) (S := S) (T := T) (r := r) h hF
  letI hNA : CFSG.GroupTheory.NormalizesSet A Γ :=
    ⟨fun a ha x hx => by
      have hae : a * e * a⁻¹ = e := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp ha
        calc a * e * a⁻¹ = e * a * a⁻¹ := by rw [h]
          _ = e := by group
      refine ⟨hC.setup.conj_mem a hx.1, ?_⟩
      have hc := hx.2.conj a
      rwa [hae] at hc⟩
  have htrans : IsPretransitive ↥A ↥Γ :=
    CFSG.GroupTheory.isPretransitive_of_forall_conj (fun x y => by
      obtain ⟨k₁, hk₁, hk₁x⟩ := hbase x.1 x.2
      obtain ⟨k₂, hk₂, hk₂y⟩ := hbase y.1 y.2
      refine ⟨k₂ * k₁⁻¹, ?_, ?_⟩
      · exact hKA (Subgroup.mul_mem K hk₂ (Subgroup.inv_mem K hk₁))
      · calc (k₂ * k₁⁻¹) * (x : G) * (k₂ * k₁⁻¹)⁻¹
            = k₂ * (k₁⁻¹ * x * k₁) * k₂⁻¹ := by group
          _ = k₂ * (k₁⁻¹ * (k₁ * hC.d * k₁⁻¹) * k₁) * k₂⁻¹ := by rw [hk₁x]
          _ = k₂ * hC.d * k₂⁻¹ := by group
          _ = (y : G) := hk₂y)
  have horb : MulAction.orbit (↥(A.subgroupOf A)) (⟨hC.d, huΓ⟩ : ↥Γ) = ⊤ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    rw [MulAction.mem_orbit_iff]
    obtain ⟨a, ha⟩ := htrans.exists_smul_eq (⟨hC.d, huΓ⟩ : ↥Γ) y
    refine ⟨⟨a, Subgroup.mem_subgroupOf.mpr a.2⟩, ?_⟩
    apply Subtype.ext
    rw [Subgroup.smul_def, conjMulActionOfNormalizesSet_smul_coe]
    simpa using congrArg Subtype.val ha
  have hOGS := card_orbit_subgroupOf_mul_card_centralizer (A := A) (D := Γ) (S := A)
    le_rfl ⟨hC.d, huΓ⟩
  rw [horb] at hOGS
  simp only [Set.top_eq_univ, Nat.card_coe_set_eq, Set.ncard_univ] at hOGS
  have hOGS' : Nat.card ↥Γ * Nat.card ↥(Subgroup.centralizer {hC.d} ⊓
      Subgroup.centralizer {frameE hC r}) = Nat.card A := hOGS
  rw [card_centralizer_d_inf (hC := hC) (S := S) (T := T) (r := r) h hF, hGamma]
    at hOGS'
  change Nat.card A = 2 * Nat.card K
  rw [card_localGroup (hC := hC) (S := S) (T := T) (r := r) h91 h hF]
  omega

end ElevenTwoFrame

end KCover

end CFSG.OddTranspositions.PartThree
