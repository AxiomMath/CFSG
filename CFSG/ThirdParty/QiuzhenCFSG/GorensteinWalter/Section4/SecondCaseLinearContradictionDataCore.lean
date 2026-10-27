module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineAligned
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP1Data
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenOuterRegion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenIndexedRegion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOuterRegionTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearConjugateFamilyTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenGoodFiber
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenBadFiber
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearContradictionDataOfPostNineRational
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearDirectProductProjection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearSemidirectComplement
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPrimeSubgroupCyclicJoin
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPSL2ComplementClassification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearCyclicPGroupProjection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearMinimalInvariantRootCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearHalfCoprime
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearNormalSylowUnique
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP0LowerBound
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearKleinFourCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalComplementEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalComplementSubgroupOf
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the completed linear contradiction-data producer

This module is the source-faithful integration layer for the PSL₂ branch.
It aligns the product regions, proves the two centralizer/complement
interfaces used by the bad-fibre estimate, counts minimal invariant
subgroups through the two normalized root Sylows, and exports the resulting
rational equation-(11) inequality to the parameter package.  `Basic.lean`
contains only the public wrapper, so this module remains below that landing
boundary.
-/

noncomputable section
namespace CFSG.GorensteinWalter
open Matrix
open scoped Pointwise
universe u

set_option maxHeartbeats 8000000

public theorem secondCase_linearContradictionData_core
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hKprimePower : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (hmodel : d.model = ComponentQuotientModel.projectiveSpecialLinear
      K hKprimePower e) :
    LinearCaseContradictionData := by
  obtain ⟨c', w', d', hwM, hdE, ⟨post⟩⟩ :=
    secondCase_linear_aligned_postNineData hmin c w d K hKprimePower e
  have hmodel' : d'.model = ComponentQuotientModel.projectiveSpecialLinear
      K hKprimePower (hdE ▸ e) := by
    simpa [hmodel]
  obtain ⟨p1, hp1eq, hp01, hp1p, hLines⟩ :=
    secondCase_linear_p1_data c' w' d' post.od post.indices.p0
      post.indices.p0_def
  have hp0p : post.indices.p0 ≤ post.od.p :=
    secondCase_linear_p0_le_p_of_le_add_one c' w' d' post.od
      post.indices.p0 post.indices.p0_def (hp01.trans hp1p)
  have hPinterE : post.od.P ⊓ d'.E = ⊥ :=
    secondCase_linear_P_inf_E_eq_bot hmin c' w' d' K hKprimePower (hdE ▸ e) post
  have hτex := secondCase_linearEquation11_outer_region_torus_injection c' w' d' K post
  rcases hτex with ⟨τ, hτ⟩
  let Lines := secondCase_linesIn G post.od.P post.od.P0
  let Xs := Lines × Fin (Nat.card K * post.equation9.k')
  let X : Xs → Subgroup G := fun x =>
    secondCase_linearEquation11_familyMap (G := G) post.od.P post.od.P0 d'.E
      ⟨x.1, τ x.2⟩
  let TConj : Xs → d'.E := fun x =>
    secondCase_toriConjugator post.od.P0 d'.E (τ x.2)
  let BaseConj : Lines → G := fun l =>
    Classical.choose (secondCase_linear_aligned_second_chain hmin c' w' d' K
      hKprimePower (hdE ▸ e) post l.1 (by simpa [post.od.A_eq] using l.2.1)
        l.2.2.1 l.2.2.2)
  have BaseSpec : ∀ l : Lines,
      l.1 = conjugateSubgroup post.od.P (BaseConj l) ∧
      BaseConj l * c'.t * (BaseConj l)⁻¹ = c'.t ∧
      conjugateSubgroup post.od.A (BaseConj l) = post.od.A ∧
      (conjugateSubgroup w'.M (BaseConj l) ⊓ (post.od.P ⊔ d'.E) =
          (post.od.P ⊔ d'.E) ⊓ Subgroup.normalizer (l.1 : Set G)) ∧
      ((post.od.P ⊔ d'.E) ⊓ Subgroup.normalizer (l.1 : Set G) =
          post.od.P ⊔ (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d'.E)) ∧
      (post.od.P ⊔ (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d'.E) =
          (post.od.P ⊔ d'.E) ⊓ Subgroup.centralizer (post.od.A : Set G)) ∧
      (d'.E ⊓ Subgroup.normalizer (l.1 : Set G) =
          Subgroup.centralizer (post.od.P0 : Set G) ⊓ d'.E) ∧
      (w'.M ⊓ (l.1 ⊔ conjugateSubgroup d'.E (BaseConj l)) =
          l.1 ⊔ conjugateSubgroup
            (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d'.E) (BaseConj l)) ∧
      (l.1 ⊔ conjugateSubgroup
          (Subgroup.centralizer (post.od.P0 : Set G) ⊓ d'.E) (BaseConj l) =
        (l.1 ⊔ conjugateSubgroup d'.E (BaseConj l)) ⊓
          Subgroup.centralizer (post.od.A : Set G)) := by
    intro l
    exact Classical.choose_spec (secondCase_linear_aligned_second_chain hmin c' w' d' K
      hKprimePower (hdE ▸ e) post l.1 (by simpa [post.od.A_eq] using l.2.1)
        l.2.2.1 l.2.2.2)
  let Aidx : Xs → Subgroup G := fun x =>
    conjugateSubgroup post.od.A (TConj x)
  let Xreg : Xs → Subgroup G := fun x =>
    conjugateSubgroup x.1.1 (TConj x : G)
  let hreg : Xs → G := fun x =>
    (TConj x : G) * BaseConj x.1
  let Reg : Xs → Subgroup G := fun x =>
    Xreg x ⊔ conjugateSubgroup d'.E (hreg x)
  let C : Subgroup G :=
    Subgroup.centralizer (post.od.P0 : Set G) ⊓ d'.E
  have hEcentP : d'.E ≤ Subgroup.centralizer (post.od.P : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp
      (post.od.P_le_F.trans post.od.F_centralizes_E hp)) z hz |>.symm
  have hXreg : ∀ x : Xs,
      Xreg x = conjugateSubgroup x.1.1 (TConj x : G) := by
    intro x
    rfl
  have htr : ∀ x : Xs,
      Xreg x = conjugateSubgroup post.od.P
          ((TConj x : G) * BaseConj x.1) ∧
      (conjugateSubgroup w'.M ((TConj x : G) * BaseConj x.1) ⊓
          (post.od.P ⊔ d'.E) =
        (post.od.P ⊔ d'.E) ⊓
          Subgroup.normalizer (Xreg x : Set G)) ∧
      ((post.od.P ⊔ d'.E) ⊓
          Subgroup.normalizer (Xreg x : Set G) =
        post.od.P ⊔ conjugateSubgroup C (TConj x : G)) ∧
      (post.od.P ⊔ conjugateSubgroup C (TConj x : G) =
        (post.od.P ⊔ d'.E) ⊓
          Subgroup.centralizer
            (conjugateSubgroup post.od.A (TConj x : G) : Set G)) ∧
      (w'.M ⊓ Reg x =
        Xreg x ⊔ conjugateSubgroup C
          ((TConj x : G) * BaseConj x.1)) ∧
      (Xreg x ⊔ conjugateSubgroup C
          ((TConj x : G) * BaseConj x.1) =
        Reg x ⊓ Subgroup.centralizer
          (conjugateSubgroup post.od.A (TConj x : G) : Set G)) := by
    intro x
    rcases BaseSpec x.1 with ⟨hX0, hfix, hAg, hf, hfN, hfC, hEnorm, hs, hsc⟩
    have h := secondCase_linear_outer_region_transport
      (P := post.od.P) (E := d'.E) (M := w'.M) (A := post.od.A) (C := C)
      (X₀ := x.1.1) (BaseConj x.1) (TConj x : G) hEcentP
      (TConj x).2 (by exact d'.E_component.1 (TConj x).2) hX0 hf hfN hfC hs hsc
    simpa [Xreg, secondCase_linearEquation11_familyMap, Reg, C] using h
  have hXcard : ∀ x : Xs, Nat.card (Xreg x) = post.od.p := by
    intro x
    change Nat.card (conjugateSubgroup x.1.1 (TConj x : G)) = post.od.p
    rw [show conjugateSubgroup x.1.1 (TConj x : G) =
      x.1.1.map (MulAut.conj (TConj x : G)).toMonoidHom by rfl,
      Subgroup.card_map_of_injective (MulAut.conj (TConj x : G)).injective]
    rcases x.1.2.2.2 with ⟨g, hg⟩
    rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact post.od.P_card
  have hXleAidx : ∀ x : Xs, Xreg x ≤ Aidx x := by
    intro x
    dsimp [Xreg, Aidx]
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨y, ?_, rfl⟩
    simpa [post.od.A_eq] using x.1.2.1 hy
  let TotalBase : Type u := {Y : Subgroup G //
    Y ≤ post.od.P ⊔ d'.E ∧ Y ≠ post.od.P ∧
      (∃ g : G, Y = conjugateSubgroup post.od.P g)}
  let TotalReg : Xs → Type u := fun x => {Y : Subgroup G //
    Y ≤ conjugateSubgroup (post.od.P ⊔ d'.E) (hreg x) ∧
      Y ≠ conjugateSubgroup post.od.P (hreg x) ∧
      (∃ g : G, Y = conjugateSubgroup post.od.P g)}
  have hTotal : ∀ x : Xs,
      (p1 - 1) * Nat.card K * post.equation9.k' ≤ Nat.card (TotalReg x) := by
    intro x
    have hbase : (p1 - 1) * Nat.card K * post.equation9.k' ≤
        Nat.card TotalBase := by
      simpa [TotalBase, secondCase_familyIn, conjugateSubgroup] using
        (secondCase_linearEquation11_outer_region c' w' d' K post hLines hPinterE)
    have htrans := secondCase_linear_conjugate_family_card_transport
      (P := post.od.P) (E := d'.E) (hreg x)
    have hxeq := htr x
    have hregPE : conjugateSubgroup (post.od.P ⊔ d'.E) (hreg x) = Reg x := by
      change (post.od.P ⊔ d'.E).map
        (MulAut.conj (hreg x)).toMonoidHom = Reg x
      rw [Subgroup.map_sup]
      have hPmap : post.od.P.map (MulAut.conj (hreg x)).toMonoidHom = Xreg x := by
        simpa [hreg, conjugateSubgroup, Subgroup.map_map] using hxeq.1.symm
      rw [hPmap]
      rfl
    have hregP : conjugateSubgroup post.od.P (hreg x) = Xreg x :=
      hxeq.1.symm
    have hcardeq : Nat.card TotalBase = Nat.card (TotalReg x) := by
      simpa [TotalBase, TotalReg, conjugateSubgroup] using htrans
    rw [← hcardeq]
    exact hbase
  have hZ : Subgroup.center d'.E = ⊥ :=
    secondCase_linear_center_eq_bot hmin c' w' d' K hKprimePower (hdE ▸ e) post
  have hCcyc : IsCyclic C := by
    let qbar : d'.E →* (d'.E ⧸ Subgroup.center d'.E) :=
      QuotientGroup.mk' (Subgroup.center d'.E)
    have hqker : qbar.ker = ⊥ := by
      rw [QuotientGroup.ker_mk', hZ]
    have hqinj : Function.Injective qbar :=
      (MonoidHom.ker_eq_bot_iff qbar).mp hqker
    have hCmap : ((C.subgroupOf d'.E).map qbar) = post.torus.T := by
      exact secondCase_linear_P0_centralizer_eq_torus c' w' d' K post hZ
    have hCsubcyc : IsCyclic (↥(C.subgroupOf d'.E)) := by
      let eC := Subgroup.equivMapOfInjective (C.subgroupOf d'.E) qbar hqinj
      have himage : IsCyclic (↥((C.subgroupOf d'.E).map qbar)) := by
        rw [hCmap]
        exact post.torus.T_cyclic
      exact (MulEquiv.isCyclic eC).mpr himage
    have eC : (C.subgroupOf d'.E) ≃* C :=
      Subgroup.subgroupOfEquivOfLe inf_le_right
    exact (MulEquiv.isCyclic eC).mp hCsubcyc
  have hPcentC : C ≤ Subgroup.centralizer (post.od.P : Set G) := by
    intro z hz
    have hzE : z ∈ d'.E := (show C ≤ d'.E from inf_le_right) hz
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro p hp
      have hpcent : p ∈ Subgroup.centralizer (d'.E : Set G) :=
        (post.od.P_le_F.trans post.od.F_centralizes_E) hp
      exact ((Subgroup.mem_centralizer_iff.mp hpcent) z hzE).symm)
  have hconj_conj : ∀ (H : Subgroup G) (a b : G),
      conjugateSubgroup (conjugateSubgroup H a) b =
        conjugateSubgroup H (b * a) := by
    intro H a b
    change (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hconj_one : ∀ (H : Subgroup G),
      conjugateSubgroup H (1 : G) = H := by
    intro H
    change H.map (MulAut.conj (1 : G)).toMonoidHom = H
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
      ext z; simp, Subgroup.map_id]
  have hconj_mono : ∀ {H J : Subgroup G}, H ≤ J → ∀ g : G,
      conjugateSubgroup H g ≤ conjugateSubgroup J g := by
    intro H J hHJ g z hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, hHJ hy, rfl⟩
  have hM : ∀ x : Xs, Nat.card {Y : Subgroup G //
      (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧
      Y ≤ Reg x ∧ Y ≠ Xreg x ∧ Y ≤ w'.M} ≤ p1 - 1 := by
    intro x
    let InM : Type u := {Y : Subgroup G //
      (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧
      Y ≤ Reg x ∧ Y ≠ Xreg x ∧ Y ≤ w'.M}
    rcases htr x with ⟨hXh, hMfirst, hN, hCPEA, hMReg, hCReg⟩
    rcases BaseSpec x.1 with ⟨_, _, _, _, _, hCbase, _, _, _⟩
    have hregPE : Reg x = conjugateSubgroup (post.od.P ⊔ d'.E) (hreg x) := by
      change Xreg x ⊔ conjugateSubgroup d'.E (hreg x) =
        (post.od.P ⊔ d'.E).map (MulAut.conj (hreg x)).toMonoidHom
      rw [Subgroup.map_sup]
      have hXh' : post.od.P.map (MulAut.conj (hreg x)).toMonoidHom = Xreg x := by
        change conjugateSubgroup post.od.P (hreg x) = Xreg x
        exact hXh.symm
      simpa [conjugateSubgroup] using
        congrArg (fun H : Subgroup G => H ⊔ conjugateSubgroup d'.E (hreg x)) hXh'.symm
    have hregBack : conjugateSubgroup (Reg x) (hreg x)⁻¹ =
        post.od.P ⊔ d'.E := by
      rw [hregPE]
      change ((post.od.P ⊔ d'.E).map
          (MulAut.conj (hreg x)).toMonoidHom).map
          (MulAut.conj (hreg x)⁻¹).toMonoidHom = post.od.P ⊔ d'.E
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hYcard : ∀ Y : InM, Nat.card Y.1 = post.od.p := by
        intro Y
        rcases Y.2.1 with ⟨g, hg⟩
        rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          post.od.P_card]
    have hYlePE : ∀ Y : InM,
          conjugateSubgroup Y.1 (hreg x)⁻¹ ≤ post.od.P ⊔ d'.E := by
        intro Y
        have hYmap : conjugateSubgroup Y.1 (hreg x)⁻¹ ≤
            conjugateSubgroup (Reg x) (hreg x)⁻¹ :=
          hconj_mono Y.2.2.1 (hreg x)⁻¹
        rw [hregBack] at hYmap
        exact hYmap
    have hAconj : ∀ x : Xs,
        conjugateSubgroup post.od.A (TConj x : G) =
          conjugateSubgroup post.od.A (hreg x) := by
      intro x
      rcases BaseSpec x.1 with ⟨_, _, hAg, _, _, _, _, _, _⟩
      calc
        conjugateSubgroup post.od.A (TConj x : G) =
            conjugateSubgroup (conjugateSubgroup post.od.A (BaseConj x.1))
              (TConj x : G) := by rw [hAg]
        _ = conjugateSubgroup post.od.A (hreg x) := by
          exact hconj_conj post.od.A (BaseConj x.1) (TConj x : G)
    have hYleCen : ∀ Y : InM,
          Y.1 ≤ Subgroup.centralizer
            (conjugateSubgroup post.od.A (TConj x : G) : Set G) := by
        intro Y
        have hYleJoin : Y.1 ≤ Xreg x ⊔
            conjugateSubgroup C (hreg x) := by
          rw [← hMReg]
          exact le_inf Y.2.2.2.2 Y.2.2.1
        rw [hCReg] at hYleJoin
        exact le_inf_iff.mp hYleJoin |>.2
    have hYleCen' : ∀ Y : InM,
          conjugateSubgroup Y.1 (hreg x)⁻¹ ≤
            Subgroup.centralizer (post.od.A : Set G) := by
        intro Y
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨y, hy, hzy⟩
        have hzy' : (hreg x)⁻¹ * y * hreg x = z := by
          simpa [MulAut.conj_apply] using hzy
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have ha' : hreg x * (a : G) * (hreg x)⁻¹ ∈
            conjugateSubgroup post.od.A (hreg x) := by
          exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
        have hycomm := (Subgroup.mem_centralizer_iff.mp
          (hYleCen Y hy)) _ (by rw [hAconj x]; exact ha')
        rw [← hzy']
        calc
          (a : G) * ((hreg x)⁻¹ * y * hreg x) =
              (hreg x)⁻¹ * ((hreg x * (a : G) * (hreg x)⁻¹) * y) * hreg x := by group
          _ = (hreg x)⁻¹ * (y * (hreg x * (a : G) * (hreg x)⁻¹)) * hreg x := by
            rw [hycomm]
          _ = (hreg x)⁻¹ * y * hreg x * (a : G) := by group
    have hYleA' : ∀ Y : InM,
          conjugateSubgroup Y.1 (hreg x)⁻¹ ≤ post.od.A := by
        intro Y
        have hZle : conjugateSubgroup Y.1 (hreg x)⁻¹ ≤
            (post.od.P ⊔ d'.E) ⊓ Subgroup.centralizer (post.od.A : Set G) :=
          le_inf (hYlePE Y) (hYleCen' Y)
        rw [← hCbase] at hZle
        rw [post.od.A_eq]
        let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
        have hP0leC : post.od.P0 ≤ C := by
          have hP0cent : post.od.P0 ≤
              Subgroup.centralizer (post.od.P0 : Set G) := by
            rw [Subgroup.le_centralizer_iff]
            intro z hz
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            let : IsCyclic (↥post.od.P0) :=
              isCyclic_of_prime_card post.od.P0_card
            let : CommGroup (↥post.od.P0) := IsCyclic.commGroup
            exact congrArg Subtype.val
              (show (⟨y, hy⟩ : post.od.P0) * ⟨z, hz⟩ =
                  ⟨z, hz⟩ * ⟨y, hy⟩ by exact mul_comm _ _)
          intro z hz
          refine ⟨?_, ?_⟩
          · exact hP0cent hz
          · exact post.od.P0_le_K0.trans (by
              rw [post.od.K0_eq]
              exact inf_le_right.trans post.od.K_le_E) hz
        exact secondCase_linear_prime_subgroup_le_sup_of_cyclic_join
          post.od.P_card post.od.P0_card
          hP0leC hCcyc hPcentC
          (by
            apply eq_bot_iff.mpr
            intro z hz
            have hzPE : z ∈ post.od.P ⊓ d'.E :=
              ⟨hz.1, (show C ≤ d'.E from inf_le_right) hz.2⟩
            rw [hPinterE] at hzPE
            exact Subgroup.mem_bot.mp hzPE)
          hZle (by
            change Nat.card (conjugateSubgroup Y.1 (hreg x)⁻¹) = post.od.p
            change Nat.card (Y.1.map (MulAut.conj (hreg x)⁻¹).toMonoidHom) = post.od.p
            rw [Subgroup.card_map_of_injective (MulAut.conj (hreg x)⁻¹).injective]
            exact hYcard Y)
    have hYneP : ∀ Y : InM,
          conjugateSubgroup Y.1 (hreg x)⁻¹ ≠ post.od.P := by
        intro Y hEq
        apply Y.2.2.2.1
        have hmap := congrArg (fun H : Subgroup G => conjugateSubgroup H (hreg x)) hEq
        have hcancel : conjugateSubgroup
            (conjugateSubgroup Y.1 (hreg x)⁻¹) (hreg x) = Y.1 := by
          calc
            conjugateSubgroup
                (conjugateSubgroup Y.1 (hreg x)⁻¹) (hreg x) =
                conjugateSubgroup Y.1 ((hreg x) * (hreg x)⁻¹) :=
              hconj_conj Y.1 (hreg x)⁻¹ (hreg x)
            _ = conjugateSubgroup Y.1 1 := by rw [mul_inv_cancel]
            _ = Y.1 := hconj_one Y.1
        calc
          Y.1 = conjugateSubgroup
              (conjugateSubgroup Y.1 (hreg x)⁻¹) (hreg x) := hcancel.symm
          _ = conjugateSubgroup post.od.P (hreg x) := hmap
          _ = Xreg x := hXh.symm
    have hYconj : ∀ Y : InM, ∃ g : G,
          conjugateSubgroup Y.1 (hreg x)⁻¹ =
            post.od.P.map (MulAut.conj g).toMonoidHom := by
      intro Y
      rcases Y.2.1 with ⟨g, hg⟩
      refine ⟨(hreg x)⁻¹ * g, ?_⟩
      rw [hg]
      change (post.od.P.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj (hreg x)⁻¹).toMonoidHom =
        post.od.P.map (MulAut.conj ((hreg x)⁻¹ * g)).toMonoidHom
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    let toLine : InM → Lines := fun Y =>
      ⟨conjugateSubgroup Y.1 (hreg x)⁻¹,
        (by simpa [post.od.A_eq] using hYleA' Y), hYneP Y, hYconj Y⟩
    have htoLine : Function.Injective toLine := by
      intro Y Z hEq
      apply Subtype.ext
      have hmap := congrArg (fun H : Subgroup G =>
          conjugateSubgroup H (hreg x)) (congrArg Subtype.val hEq)
      have hcancelY : conjugateSubgroup
            (conjugateSubgroup Y.1 (hreg x)⁻¹) (hreg x) = Y.1 := by
        calc
          conjugateSubgroup
              (conjugateSubgroup Y.1 (hreg x)⁻¹) (hreg x) =
              conjugateSubgroup Y.1 ((hreg x) * (hreg x)⁻¹) :=
            hconj_conj Y.1 (hreg x)⁻¹ (hreg x)
          _ = conjugateSubgroup Y.1 1 := by rw [mul_inv_cancel]
          _ = Y.1 := hconj_one Y.1
      have hcancelZ : conjugateSubgroup
            (conjugateSubgroup Z.1 (hreg x)⁻¹) (hreg x) = Z.1 := by
        calc
          conjugateSubgroup
              (conjugateSubgroup Z.1 (hreg x)⁻¹) (hreg x) =
              conjugateSubgroup Z.1 ((hreg x) * (hreg x)⁻¹) :=
            hconj_conj Z.1 (hreg x)⁻¹ (hreg x)
          _ = conjugateSubgroup Z.1 1 := by rw [mul_inv_cancel]
          _ = Z.1 := hconj_one Z.1
      rw [hcancelY, hcancelZ] at hmap
      exact hmap
    have hcard : Nat.card InM ≤ Nat.card Lines :=
      Nat.card_le_card_of_injective _ htoLine
    rw [hLines] at hcard
    simpa [InM, Lines] using hcard

  have hXeq : ∀ x : Xs, X x = Xreg x := by
    intro x
    rfl

  have hconjFixP : ∀ t : d'.E,
      post.od.P.map (MulAut.conj (t : G)).toMonoidHom = post.od.P := by
    intro t
    apply Subgroup.ext
    intro z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨p, hp, rfl⟩
      have hcomm : (p : G) * (t : G) = (t : G) * (p : G) :=
        (Subgroup.mem_centralizer_iff.mp (hEcentP t.2)) p hp
      have hfix : (t : G) * (p : G) * (t : G)⁻¹ = p := by
        calc
          (t : G) * (p : G) * (t : G)⁻¹ = (p : G) * (t : G) * (t : G)⁻¹ := by rw [hcomm.symm]
          _ = p := by simp
      simpa [MulAut.conj_apply, hfix] using hp
    · intro hz
      apply Subgroup.mem_map.mpr
      refine ⟨z, hz, ?_⟩
      have hcomm : z * (t : G) = (t : G) * z :=
        (Subgroup.mem_centralizer_iff.mp (hEcentP t.2)) z hz
      change (t : G) * z * (t : G)⁻¹ = z
      calc
        (t : G) * z * (t : G)⁻¹ = z * (t : G) * (t : G)⁻¹ := by rw [hcomm.symm]
        _ = z := by simp

  have hconjFixP' : ∀ t : d'.E,
      conjugateSubgroup post.od.P (t : G) = post.od.P := by
    intro t
    simpa [conjugateSubgroup] using hconjFixP t

  have hLineJoin : ∀ x : Xs, post.od.P ⊔ x.1.1 = post.od.A := by
    intro x
    let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
    have hLcard : Nat.card x.1.1 = post.od.p := by
      rcases x.1.2.2.2 with ⟨g, hg⟩
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        post.od.P_card]
    have hPnotleL : ¬ post.od.P ≤ x.1.1 := by
      intro hle
      apply x.1.2.2.1
      exact (Subgroup.eq_of_le_of_card_ge hle (by
        rw [post.od.P_card, hLcard])).symm
    have hLinterP : x.1.1 ⊓ post.od.P = ⊥ :=
      inf_eq_bot_of_not_le_of_prime_card
        (H := x.1.1) (P := post.od.P)
        (post.od.P_card ▸ post.od.hp_prime) hPnotleL
    have hcomm : ∀ p : post.od.P, ∀ z : x.1.1,
        (p : G) * (z : G) = (z : G) * (p : G) := by
      intro p z
      let : IsElementaryAbelian post.od.p post.od.A := post.od.A_elem_abelian
      have hpA : (p : G) ∈ post.od.A := by
        rw [post.od.A_eq]
        exact (le_sup_left : post.od.P ≤ post.od.P ⊔ post.od.P0) p.2
      have hzA0 : (z : G) ∈ post.od.P ⊔ post.od.P0 := x.1.2.1 z.2
      have hzA : (z : G) ∈ post.od.A := by
        rw [post.od.A_eq]
        exact hzA0
      exact congrArg Subtype.val
        (post.od.A_elem_abelian.toIsMulCommutative.is_comm.comm
          (⟨p, hpA⟩ : post.od.A) (⟨z, hzA⟩ : post.od.A))
    have hcard : Nat.card (post.od.P ⊔ x.1.1 : Subgroup G) = post.od.p ^ 2 := by
      rw [subgroup_card_sup_of_commute hcomm
        (by simpa [disjoint_iff, inf_comm] using hLinterP)]
      rw [post.od.P_card, hLcard, pow_two]
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le (by rw [post.od.A_eq]; exact le_sup_left)
        (by rw [post.od.A_eq]; exact x.1.2.1)
    · rw [post.od.A_card, hcard]

  have hAidxJoin : ∀ x : Xs, Aidx x = post.od.P ⊔ X x := by
    intro x
    dsimp [Aidx, conjugateSubgroup]
    simp only [← MulEquiv.toMonoidHom_eq_coe]
    rw [← hLineJoin x, Subgroup.map_sup, hconjFixP (TConj x)]
    change post.od.P ⊔ Xreg x = post.od.P ⊔ X x
    rw [hXeq x]

  have hAidxlePE : ∀ x : Xs, Aidx x ≤ post.od.P ⊔ d'.E := by
    intro x
    dsimp [Aidx, conjugateSubgroup]
    simp only [← MulEquiv.toMonoidHom_eq_coe]
    rw [post.od.A_eq, Subgroup.map_sup, hconjFixP (TConj x)]
    refine sup_le le_sup_left ?_
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, rfl⟩
    have hzK0 : z0 ∈ post.od.K0 := post.od.P0_le_K0 hz0
    have hzE : z0 ∈ d'.E := by
      rw [post.od.K0_eq] at hzK0
      exact post.od.K_le_E hzK0.2
    exact (le_sup_right : d'.E ≤ post.od.P ⊔ d'.E)
      (d'.E.mul_mem (d'.E.mul_mem (TConj x).2 hzE)
        (d'.E.inv_mem (TConj x).2))

  have hD_front : ∀ x : Xs, ∀ Y : Subgroup G,
      (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) →
      Y ≤ Reg x → ¬ Y ≤ w'.M →
      (let D : Subgroup G := Subgroup.centralizer (Y : Set G) ⊓
          (post.od.P ⊔ d'.E)
       X x ≤ D ∧ ¬ post.od.P ⊔ X x ≤ D) := by
    intro x Y hYconj hYle hYnotM
    dsimp
    let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
    have hXleReg : X x ≤ Reg x := by
      rw [hXeq x]
      exact le_sup_left
    have hXcent : X x ≤ Subgroup.centralizer (Y : Set G) := by
      intro z hz
      have hXself : Xreg x ≤ Subgroup.centralizer (Xreg x : Set G) := by
        let : IsCyclic (↥(Xreg x)) := isCyclic_of_prime_card (hXcard x)
        exact (Subgroup.le_centralizer_iff_isMulCommutative).2
          (IsCyclic.isMulCommutative (α := ↥(Xreg x)))
      have hXE : Xreg x ≤ Subgroup.centralizer
          (conjugateSubgroup d'.E (hreg x) : Set G) := by
        intro z hz
        have hzX : z ∈ conjugateSubgroup post.od.P (hreg x) := by
          rw [← (htr x).1]
          exact hz
        rcases Subgroup.mem_map.mp hzX with ⟨p0, hp0, hz⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨e0, he0, hy⟩
        have hcomm : (e0 : G) * (p0 : G) = (p0 : G) * (e0 : G) :=
          ((Subgroup.mem_centralizer_iff.mp (hEcentP he0)) p0 hp0).symm
        rw [← hz, ← hy]
        calc
          ((hreg x : G) * (e0 : G) * (hreg x)⁻¹) *
              ((hreg x : G) * (p0 : G) * (hreg x)⁻¹) =
            (hreg x : G) * ((e0 : G) * (p0 : G)) * (hreg x)⁻¹ := by group
          _ = (hreg x : G) * ((p0 : G) * (e0 : G)) * (hreg x)⁻¹ := by rw [hcomm]
          _ = ((hreg x : G) * (p0 : G) * (hreg x)⁻¹) *
              ((hreg x : G) * (e0 : G) * (hreg x)⁻¹) := by group
      have hXregcent : Xreg x ≤ Subgroup.centralizer (Reg x : Set G) := by
        exact le_centralizer_sup_of_le_centralizers hXself hXE
      have hzReg := hXregcent (hXeq x ▸ hz)
      rw [Subgroup.mem_centralizer_iff] at hzReg ⊢
      intro y hy
      exact hzReg y (hYle hy)
    have hXleD : X x ≤ Subgroup.centralizer (Y : Set G) ⊓
        (post.od.P ⊔ d'.E) := by
      refine le_inf hXcent ?_
      exact (hXleAidx x).trans (hAidxlePE x)
    refine ⟨hXleD, ?_⟩
    intro hAX
    have hYinC : Y ≤ Subgroup.centralizer (Aidx x : Set G) := by
      rw [hAidxJoin x]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact ((Subgroup.mem_centralizer_iff.mp
        (hAX ha).1 y hy).symm)
    have hYinM : Y ≤ w'.M := by
      rcases htr x with ⟨_, _, _, _, hMReg, hCReg⟩
      have hYinter : Y ≤ Reg x ⊓
          Subgroup.centralizer (Aidx x : Set G) := le_inf hYle hYinC
      have hYgood : Y ≤ Xreg x ⊔ conjugateSubgroup C (hreg x) := by
        rw [hCReg]
        exact hYinter
      have hYMReg : Y ≤ w'.M ⊓ Reg x := by
        rw [hMReg]
        exact hYgood
      exact le_inf_iff.mp hYMReg |>.1
    exact hYnotM hYinM

  have hD_core_probe : ∀ x : Xs, ∀ Y : Subgroup G,
      (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) →
      Y ≤ Reg x → ¬ Y ≤ w'.M →
      (let D : Subgroup G := Subgroup.centralizer (Y : Set G) ⊓
          (post.od.P ⊔ d'.E)
       X x ≤ D ∧ ¬ post.od.p ∣ ((X x).subgroupOf D).index ∧
        ∃ Q : Subgroup G, IsNormalIn Q D ∧
          D = Q ⊔ (D ⊓ Subgroup.normalizer (X x : Set G)) ∧
          Q ⊓ (D ⊓ Subgroup.normalizer (X x : Set G)) = ⊥ ∧
          Nat.card Q ∣ Nat.card K) := by
    intro x Y hYconj hYle hYnotM
    let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
    have hpdvd : post.od.p ∣ Nat.card post.equation9.Kinv :=
      secondCase_linear_p_dvd_Kinv c' w' d' post
    have hpodd : Odd post.od.p :=
      secondCase_linear_omega_p_odd c' w' d' post.od
    have hKseven : 7 ≤ Nat.card K :=
      secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv
        d' K post.equation9 post.od.hp_prime hpodd hpdvd
    rcases post.torus.primePower with ⟨r, f, hr, hrOdd, hf, hKcard⟩
    let : Fact r.Prime := ⟨hr⟩
    let qbar : d'.E →* (d'.E ⧸ Subgroup.center d'.E) :=
      QuotientGroup.mk' (Subgroup.center d'.E)
    have hqker : qbar.ker = ⊥ := by
      rw [QuotientGroup.ker_mk', hZ]
    have hqinj : Function.Injective qbar :=
      (MonoidHom.ker_eq_bot_iff qbar).mp hqker
    have hCmap : ((C.subgroupOf d'.E).map qbar) = post.torus.T := by
      exact secondCase_linear_P0_centralizer_eq_torus c' w' d' K post hZ
    have hP0subC : post.od.P0.subgroupOf d'.E ≤ C.subgroupOf d'.E := by
      intro z hz
      change (z : G) ∈ C
      refine ⟨?_, z.property⟩
      change (z : G) ∈ Subgroup.centralizer (post.od.P0 : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      let : IsCyclic (↥post.od.P0) :=
        isCyclic_of_prime_card post.od.P0_card
      let : CommGroup (↥post.od.P0) := IsCyclic.commGroup
      have hzP0 : (z : G) ∈ post.od.P0 := by
        exact hz
      exact congrArg Subtype.val
        (show (⟨p, hp⟩ : post.od.P0) * ⟨(z : G), hzP0⟩ =
            ⟨(z : G), hzP0⟩ * ⟨p, hp⟩ by exact mul_comm _ _)
    have hP0maple : (post.od.P0.subgroupOf d'.E).map qbar ≤ post.torus.T := by
      rw [← hCmap]
      exact Subgroup.map_mono hP0subC
    have hP0mapcard : Nat.card ((post.od.P0.subgroupOf d'.E).map qbar) = post.od.p := by
      calc
        Nat.card ((post.od.P0.subgroupOf d'.E).map qbar) =
            Nat.card (post.od.P0.subgroupOf d'.E) :=
          Subgroup.card_map_of_injective hqinj
        _ = Nat.card post.od.P0 := by
          rw [← Subgroup.card_map_of_injective d'.E.subtype_injective,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (by
              exact post.od.P0_le_K0.trans (by
                rw [post.od.K0_eq]
                exact inf_le_right.trans post.od.K_le_E))]
        _ = post.od.p := post.od.P0_card
    have hpT : post.od.p ∣ Nat.card post.torus.T := by
      rw [← hP0mapcard]
      exact Subgroup.card_dvd_of_le hP0maple
    have hp_ne_r : post.od.p ≠ r := by
      intro hpr
      have hqodd : Odd (Nat.card K) := by
        rw [hKcard]
        exact hrOdd.pow
      have hminus : 2 ∣ Nat.card K - 1 := by
        rcases hqodd with ⟨a, ha⟩
        use a
        omega
      have hplus : 2 ∣ Nat.card K + 1 := by
        rcases hqodd with ⟨a, ha⟩
        use a + 1
        omega
      have hminusdiv : r ∣ Nat.card K - 1 := by
        rcases post.torus.T_card with h | h
        · rw [h] at hpT
          rw [Nat.dvd_div_iff_mul_dvd hminus] at hpT
          have hmul : r ∣ 2 * post.od.p := by
            rw [hpr]
            simpa [Nat.mul_comm] using (Nat.dvd_mul_right r 2)
          exact dvd_trans hmul hpT
        · rw [h] at hpT
          rw [Nat.dvd_div_iff_mul_dvd hplus] at hpT
          have hmul : r ∣ 2 * post.od.p := by
            rw [hpr]
            simpa [Nat.mul_comm] using (Nat.dvd_mul_right r 2)
          have htmp : r ∣ Nat.card K + 1 := dvd_trans hmul hpT
          have hrK : r ∣ Nat.card K := by
            rw [hKcard]
            exact dvd_pow_self r (Nat.ne_of_gt hf)
          have hrone : r ∣ 1 := by
            simpa using (Nat.dvd_sub htmp hrK)
          exact False.elim (hr.ne_one (Nat.dvd_one.mp hrone))
      have hrK : r ∣ Nat.card K := by
        rw [hKcard]
        exact dvd_pow_self r (Nat.ne_of_gt hf)
      have hrone : r ∣ 1 := by
        have hdiv := Nat.dvd_sub hrK hminusdiv
        have hsub : Nat.card K - (Nat.card K - 1) = 1 := by omega
        rw [hsub] at hdiv
        exact hdiv
      exact hr.ne_one (Nat.dvd_one.mp hrone)
    have hprcop : Nat.Coprime post.od.p r :=
      (Fact.out : Nat.Prime post.od.p).coprime_iff_not_dvd.mpr (by
        intro h
        exact hp_ne_r ((Nat.prime_dvd_prime_iff_eq
          (Fact.out : Nat.Prime post.od.p) hr).mp h))
    have hpqcop : Nat.Coprime post.od.p (Nat.card K) := by
      rw [hKcard]
      exact hprcop.pow_right f
    let qE : (d'.E ⧸ Subgroup.center d'.E) ≃* d'.E :=
      (QuotientGroup.quotientMulEquivOfEq (G := d'.E) hZ).trans
        (QuotientGroup.quotientBot (G := d'.E))
    have eE : d'.E ≃* PSL2 K :=
      qE.symm.trans (hdE ▸ e).some
    have hSylowCyc : ∀ S : Sylow post.od.p (d'.E), IsCyclic S := by
      intro S
      have hpne2 : post.od.p ≠ 2 := by
        intro hp2
        apply hpodd.not_two_dvd_nat
        rw [hp2]
      have hmap := psl2_sylow_isCyclic_of_coprime_field_card
        K hKcard hKseven post.od.p
          hpne2 hpqcop
          (S.mapSurjective (f := eE.toMonoidHom) eE.surjective)
      let eS := MulEquiv.subgroupMap eE (S : Subgroup d'.E)
      have hmap' : IsCyclic (↥((S.mapSurjective
          (f := eE.toMonoidHom) eE.surjective) : Subgroup (PSL2 K))) := by
        simpa using hmap
      exact (MulEquiv.isCyclic eS).mpr hmap'
    let D : Subgroup G := Subgroup.centralizer (Y : Set G) ⊓
      (post.od.P ⊔ d'.E)
    have hfront := hD_front x Y hYconj hYle hYnotM
    have hXleD : X x ≤ D := hfront.1
    have hnot : ¬ post.od.P ⊔ X x ≤ D := hfront.2
    have hcommPE : ∀ p e, p ∈ post.od.P → e ∈ d'.E → Commute p e := by
      intro p e hp he
      change p * e = e * p
      exact Subgroup.mem_centralizer_iff.mp (hEcentP he) p hp
    obtain ⟨ePE, heP, heE⟩ :=
      subgroup_sup_exists_prod_equiv_of_commute_of_disjoint
        post.od.P d'.E hPinterE hcommPE
    let incD : D →* (post.od.P ⊔ d'.E : Subgroup G) :=
      Subgroup.inclusion inf_le_right
    let φ : D →* d'.E :=
      (MonoidHom.snd post.od.P d'.E).comp
        (ePE.toMonoidHom.comp incD)
    let ψ : D →* post.od.P :=
      (MonoidHom.fst post.od.P d'.E).comp
        (ePE.toMonoidHom.comp incD)
    have hDP : D ⊓ post.od.P = ⊥ := by
      by_contra hne
      have hcardDiv : Nat.card (↥(D ⊓ post.od.P : Subgroup G)) ∣ post.od.p := by
        rw [← post.od.P_card]
        exact Subgroup.card_dvd_of_le inf_le_right
      have hcardEq : Nat.card (↥(D ⊓ post.od.P : Subgroup G)) = post.od.p := by
        rcases (Nat.dvd_prime post.od.hp_prime).mp hcardDiv with hone | hp'
        · exact False.elim (hne (Subgroup.card_eq_one.mp hone))
        · exact hp'
      have hEq : D ⊓ post.od.P = post.od.P :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by
          rw [post.od.P_card, hcardEq])
      have hPleD : post.od.P ≤ D := by
        rw [← hEq]
        exact inf_le_left
      exact hnot (sup_le hPleD hXleD)
    have hφinj : Function.Injective φ := by
      apply (MonoidHom.ker_eq_bot_iff φ).mp
      apply le_bot_iff.mp
      intro z hz
      have hsnd : (ePE (incD z)).2 = 1 := by simpa [φ] using hz
      let a : post.od.P := (ePE (incD z)).1
      have heq : ePE (incD z) = (a, 1) := by
        apply Prod.ext
        · rfl
        · exact hsnd
      have hpa : ePE ⟨(a : G), Subgroup.mem_sup_left a.2⟩ = (a, 1) := heP a
      have hincEq : incD z = ⟨(a : G), Subgroup.mem_sup_left a.2⟩ :=
        ePE.injective (heq.trans hpa.symm)
      have hzP : (z : G) ∈ post.od.P := by
        have hv := congrArg Subtype.val hincEq
        change (z : G) = (a : G) at hv
        rw [hv]
        exact a.2
      have hzInf : (z : G) ∈ (D ⊓ post.od.P : Subgroup G) := ⟨z.2, hzP⟩
      have hzOne : (z : G) = 1 := by
        rw [hDP] at hzInf
        exact Subgroup.mem_bot.mp hzInf
      exact Subtype.ext hzOne
    let CT : Subgroup G := conjugateSubgroup C (TConj x : G)
    have hCTleE : CT ≤ d'.E := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, rfl⟩
      exact d'.E.mul_mem (d'.E.mul_mem (TConj x).2
          ((show C ≤ d'.E from inf_le_right) hz0))
        (d'.E.inv_mem (TConj x).2)
    have hCTcentP : CT ≤ Subgroup.centralizer (post.od.P : Set G) := by
      intro z hz
      exact hEcentP (hCTleE hz)
    have hCTnormP : CT ≤ Subgroup.normalizer (post.od.P : Set G) :=
      hCTcentP.trans (Subgroup.centralizer_le_normalizer (post.od.P : Set G))
    have hCTcyc : IsCyclic CT := by
      let eCT : C ≃* CT :=
        Subgroup.equivMapOfInjective C (MulAut.conj (TConj x : G)).toMonoidHom
          (MulAut.conj (TConj x : G)).injective
      exact (MulEquiv.isCyclic eCT).mp hCcyc
    let CTE : Subgroup d'.E := CT.subgroupOf d'.E
    have hCTEcyc : IsCyclic CTE := by
      exact (Subgroup.subgroupOfEquivOfLe hCTleE).isCyclic.mpr hCTcyc
    let Nsub : Subgroup D :=
      (D ⊓ Subgroup.normalizer (X x : Set G)).subgroupOf D
    have hφNleCT : ∀ z : Nsub, φ z.1 ∈ CTE := by
      intro z
      have hzInf : (z.1 : G) ∈ D ⊓ Subgroup.normalizer (X x : Set G) :=
        Subgroup.mem_subgroupOf.mp z.property
      have hzPE : (z.1 : G) ∈ post.od.P ⊔ d'.E := hzInf.1.2
      have hzN : (z.1 : G) ∈ Subgroup.normalizer (X x : Set G) := hzInf.2
      have hzN' : (z.1 : G) ∈ Subgroup.normalizer (Xreg x : Set G) := by
        simpa [hXeq x] using hzN
      have hzEq' : (z.1 : G) ∈ post.od.P ⊔
          conjugateSubgroup C (TConj x : G) := by
        exact (congrArg (fun H : Subgroup G => (z.1 : G) ∈ H)
          (htr x).2.2.1).mp ⟨hzPE, hzN'⟩
      have hzEq : (z.1 : G) ∈ post.od.P ⊔ CT := by
        simpa [CT] using hzEq'
      have hzprod : (z.1 : G) ∈ (post.od.P : Set G) * (CT : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left post.od.P CT hCTnormP]
        exact hzEq
      rcases hzprod with ⟨p0, hp0, c0, hc0, hzc⟩
      let zd : D := z.1
      have hφz : (φ zd : G) = c0 := by
        let zPE : (post.od.P ⊔ d'.E : Subgroup G) :=
          ⟨(p0 : G) * (c0 : G), (post.od.P ⊔ d'.E).mul_mem
            (Subgroup.mem_sup_left hp0) (Subgroup.mem_sup_right (hCTleE hc0))⟩
        have hinc : incD zd = zPE := by
          apply Subtype.ext
          exact hzc.symm
        have heval := congrArg ePE hinc
        have hpe : ePE (incD zd) = ((⟨p0, hp0⟩ : post.od.P),
            ⟨c0, hCTleE hc0⟩) := by
          rw [heval]
          have hzprodPE : zPE =
              (⟨p0, Subgroup.mem_sup_left hp0⟩ : (post.od.P ⊔ d'.E : Subgroup G)) *
                (⟨c0, Subgroup.mem_sup_right (hCTleE hc0)⟩ :
                  (post.od.P ⊔ d'.E : Subgroup G)) := by
            apply Subtype.ext
            rfl
          have hp' : ePE (⟨p0, Subgroup.mem_sup_left hp0⟩ :
              (post.od.P ⊔ d'.E : Subgroup G)) =
              ((⟨p0, hp0⟩ : post.od.P), 1) := by
            simpa using heP (⟨p0, hp0⟩ : post.od.P)
          have hc' : ePE (⟨c0, Subgroup.mem_sup_right (hCTleE hc0)⟩ :
              (post.od.P ⊔ d'.E : Subgroup G)) =
              (1, (⟨c0, hCTleE hc0⟩ : d'.E)) := by
            simpa using heE (⟨c0, hCTleE hc0⟩ : d'.E)
          rw [hzprodPE, map_mul, hp', hc']
          simp
        have hφzE : φ zd = (⟨c0, hCTleE hc0⟩ : d'.E) := by
          simpa [φ, zd] using congrArg Prod.snd hpe
        have hφzG : (φ zd : G) = c0 := congrArg Subtype.val hφzE
        exact hφzG
      change (φ zd : G) ∈ CT
      rw [hφz]
      exact hc0
    have hNcyc : IsCyclic Nsub := by
      let fN0 : Nsub →* d'.E :=
        φ.comp Nsub.subtype
      let fN : Nsub →* CTE :=
        MonoidHom.codRestrict fN0 CTE (by
          intro z
          simpa [fN0] using hφNleCT z)
      have hfNinj : Function.Injective fN := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        have hφab : φ a.1 = φ b.1 := by
          apply Subtype.ext
          exact congrArg (fun z : CTE => (z : G)) hab
        exact congrArg Subtype.val (hφinj hφab)
      exact isCyclic_of_injective fN hfNinj
    have hXnotE : ¬ X x ≤ d'.E := by
      intro hXleE
      have hback : conjugateSubgroup (X x) (TConj x : G)⁻¹ ≤ d'.E := by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
        have hyE : y ∈ d'.E := hXleE hy
        exact d'.E.mul_mem (d'.E.mul_mem (d'.E.inv_mem (TConj x).2) hyE)
          (d'.E.inv_mem (d'.E.inv_mem (TConj x).2))
      have hxlineE : x.1.1 ≤ d'.E := by
        have hconjEq : conjugateSubgroup (X x) (TConj x : G)⁻¹ = x.1.1 := by
          change (x.1.1.map (MulAut.conj (TConj x : G)).toMonoidHom).map
              (MulAut.conj (TConj x : G)⁻¹).toMonoidHom = x.1.1
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
        rw [← hconjEq]
        exact hback
      have hP0leA : post.od.P0 ≤ post.od.A := by
        rw [post.od.A_eq]
        exact le_sup_right
      have hP0leE : post.od.P0 ≤ d'.E := by
        exact post.od.P0_le_K0.trans (by
          rw [post.od.K0_eq]
          exact inf_le_right.trans post.od.K_le_E)
      have hP0leCGP : post.od.P0 ≤
          Subgroup.centralizer (post.od.P : Set G) :=
        hP0leE.trans hEcentP
      have hAinterE : post.od.A ⊓ d'.E = post.od.P0 := by
        apply le_antisymm
        · intro a ha
          have hP0leN : post.od.P0 ≤
              Subgroup.normalizer (post.od.P : Set G) := by
            exact hP0leCGP.trans
              (Subgroup.centralizer_le_normalizer (post.od.P : Set G))
          have hcoe : ((post.od.P ⊔ post.od.P0 : Subgroup G) : Set G) =
              (post.od.P : Set G) * (post.od.P0 : Set G) :=
            Subgroup.coe_mul_of_right_le_normalizer_left
              post.od.P post.od.P0 hP0leN
          have haPP0 : a ∈ (post.od.P : Set G) * (post.od.P0 : Set G) := by
            have haA' : a ∈ post.od.P ⊔ post.od.P0 := by
              simpa [post.od.A_eq] using ha.1
            rwa [← hcoe]
          rcases haPP0 with ⟨p, hp, p0, hp0, hEq⟩
          have hpE : p ∈ d'.E := by
            have hmem : a * p0⁻¹ ∈ d'.E :=
              d'.E.mul_mem ha.2 (d'.E.inv_mem (hP0leE hp0))
            have hEq' : p = a * p0⁻¹ := by
              rw [← hEq]
              group
            rwa [hEq']
          have hpbot : p = 1 := by
            have hmem : p ∈ post.od.P ⊓ d'.E := ⟨hp, hpE⟩
            have hbot : p ∈ (⊥ : Subgroup G) := by
              rwa [hPinterE] at hmem
            exact Subgroup.mem_bot.mp hbot
          have ha_eq : a = p0 := by
            calc
              a = p * p0 := hEq.symm
              _ = p0 := by rw [hpbot]; simp
          rwa [ha_eq]
        · intro p0 hp0
          exact ⟨by
            rw [post.od.A_eq]
            exact (le_sup_right : post.od.P0 ≤ post.od.P ⊔ post.od.P0) hp0,
            hP0leE hp0⟩
      have hlineleA : x.1.1 ≤ post.od.A := by
        rw [post.od.A_eq]
        exact x.1.2.1
      have hlineleE : x.1.1 ≤ d'.E := hxlineE
      have hlineleP0 : x.1.1 ≤ post.od.P0 := by
        intro y hy
        have hyinter : y ∈ post.od.A ⊓ d'.E :=
          ⟨hlineleA hy, hlineleE hy⟩
        rw [hAinterE] at hyinter
        exact hyinter
      have hxcard : Nat.card x.1.1 = post.od.p := by
        rcases x.1.2.2.2 with ⟨g, hg⟩
        rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          post.od.P_card]
      have heq : x.1.1 = post.od.P0 := by
        apply Subgroup.eq_of_le_of_card_ge hlineleP0
        rw [post.od.P0_card, hxcard]
      exact (by
        have hlineP0 : x.1.1 ≠ post.od.P0 := by
          intro heq'
          apply secondCase_linear_P_not_conjugate_P0 c' w' d' K post
          rcases x.1.2.2.2 with ⟨g, hg⟩
          refine ⟨g, ?_⟩
          simpa [conjugateSubgroup] using hg.symm.trans heq'
        exact hlineP0 heq)
    let XD : Subgroup D := (X x).subgroupOf D
    have hXDcard : Nat.card XD = post.od.p := by
      calc
        Nat.card XD = Nat.card (XD.map D.subtype) :=
          (Subgroup.card_map_of_injective D.subtype_injective).symm
        _ = Nat.card (X x) := by
          rw [show XD.map D.subtype = X x by
            dsimp [XD]
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXleD]]
        _ = post.od.p := by rw [hXeq x, hXcard x]
    have hXDnotker : ¬ XD ≤ ψ.ker := by
      intro hXDker
      apply hXnotE
      intro z hzX
      let zd : D := ⟨z, hXleD hzX⟩
      have hzdXD : zd ∈ XD := by
        exact Subgroup.mem_subgroupOf.mpr hzX
      have hψone : ψ zd = 1 := hXDker hzdXD
      let ed : d'.E := φ zd
      have heqprod : ePE (incD zd) = (1, ed) := by
        apply Prod.ext
        · simpa [ψ] using hψone
        · rfl
      have hembed : ePE
          (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
            (post.od.P ⊔ d'.E : Subgroup G)) =
          (1, ed) := heE ed
      have hsubeq : incD zd =
          (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
            (post.od.P ⊔ d'.E : Subgroup G)) :=
        ePE.injective (heqprod.trans hembed.symm)
      have hval : z = (ed : G) := congrArg Subtype.val hsubeq
      rw [hval]
      exact ed.2
    have hXDp : IsPGroup post.od.p XD :=
      IsPGroup.of_card (n := 1) (by simpa [hXDcard])
    obtain ⟨SD, hXDleSD⟩ := hXDp.exists_le_sylow
    have hSDcyc : IsCyclic SD := by
      obtain ⟨SE, hSleSE⟩ :=
        (SD.isPGroup').map φ |>.exists_le_sylow
      have hSEcyc : IsCyclic SE := hSylowCyc SE
      have hmapcyc : IsCyclic ((SD : Subgroup D).map φ) := by
        let : IsCyclic SE := hSEcyc
        exact Subgroup.isCyclic_of_le hSleSE
      let eSD : SD ≃* ((SD : Subgroup D).map φ) :=
        Subgroup.equivMapOfInjective (SD : Subgroup D) φ hφinj
      exact (MulEquiv.isCyclic eSD).mpr hmapcyc
    let XSD : Subgroup SD := XD.subgroupOf (SD : Subgroup D)
    have hXSDcard : Nat.card XSD = post.od.p := by
      calc
        Nat.card XSD = Nat.card XD :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXDleSD).toEquiv
        _ = post.od.p := hXDcard
    let ψSD : SD →* post.od.P := ψ.comp (SD : Subgroup D).subtype
    have hXSDnotker : ¬ XSD ≤ ψSD.ker := by
      intro hle
      apply hXDnotker
      intro z hzXD
      let zs : SD := ⟨z, hXDleSD hzXD⟩
      have hzsX : zs ∈ XSD := by
        exact Subgroup.mem_subgroupOf.mpr hzXD
      have hzs := hle hzsX
      simpa [ψSD, zs] using hzs
    have hψSDinj : Function.Injective ψSD :=
      cyclic_pGroup_hom_injective_of_prime_subgroup_not_le_ker
        SD.isPGroup' hSDcyc XSD hXSDcard ψSD hXSDnotker
    have hSDcardle : Nat.card SD ≤ Nat.card post.od.P :=
      Nat.card_le_card_of_injective ψSD hψSDinj
    have hSDcard : Nat.card SD = post.od.p := by
      apply le_antisymm
      · simpa [post.od.P_card] using hSDcardle
      · calc
          post.od.p = Nat.card XD := hXDcard.symm
          _ ≤ Nat.card SD := Subgroup.card_le_of_le hXDleSD
    have hXD_eq_SD : XD = (SD : Subgroup D) := by
      apply Subgroup.eq_of_le_of_card_ge hXDleSD
      rw [hXDcard, hSDcard]
    have hXidx : ¬ post.od.p ∣ XD.index := by
      rw [hXD_eq_SD]
      exact SD.not_dvd_index
    let fD : D →* PSL2 K := eE.toMonoidHom.comp φ
    have hfDinj : Function.Injective fD := eE.injective.comp hφinj
    let HD : Subgroup (PSL2 K) := fD.range
    let fR : D →* HD := fD.rangeRestrict
    have hfRinj : Function.Injective fR := by
      intro a b hab
      apply hfDinj
      exact congrArg Subtype.val hab
    let eDH : D ≃* HD := MulEquiv.ofBijective fR
      ⟨hfRinj, fD.rangeRestrict_surjective⟩
    let PH : Sylow post.od.p HD :=
      SD.mapSurjective (f := eDH.toMonoidHom) eDH.surjective
    have hPHcard : Nat.card (PH : Subgroup HD) = post.od.p := by
      change Nat.card ((SD : Subgroup D).map eDH.toMonoidHom) = post.od.p
      rw [Subgroup.card_map_of_injective
        (f := eDH.toMonoidHom) eDH.injective]
      exact hSDcard
    have hNormXDcyc : IsCyclic (Subgroup.normalizer (XD : Set D)) := by
      rw [show Subgroup.normalizer (XD : Set D) =
          (D ⊓ Subgroup.normalizer (X x : Set G)).subgroupOf D by
        dsimp [XD]
        exact normalizer_subgroupOf_eq_subgroupOf_inf_normalizer D (X x) hXleD]
      exact hNcyc
    have hNormSDcyc : IsCyclic
        (Subgroup.normalizer ((SD : Subgroup D) : Set D)) := by
      have hset : ((SD : Subgroup D) : Set D) = (XD : Set D) :=
        congrArg (fun H : Subgroup D => (H : Set D)) hXD_eq_SD.symm
      rw [hset]
      exact hNormXDcyc
    have hMapNormSDcyc : IsCyclic
        ((Subgroup.normalizer ((SD : Subgroup D) : Set D)).map
          eDH.toMonoidHom) := by
      let eN : Subgroup.normalizer ((SD : Subgroup D) : Set D) ≃*
          (Subgroup.normalizer ((SD : Subgroup D) : Set D)).map
            eDH.toMonoidHom :=
        Subgroup.equivMapOfInjective _ eDH.toMonoidHom eDH.injective
      exact (MulEquiv.isCyclic eN).mp hNormSDcyc
    have hNormPHcyc : IsCyclic
        (Subgroup.normalizer ((PH : Subgroup HD) : Set HD)) := by
      change IsCyclic (Subgroup.normalizer
        (((SD : Subgroup D).map eDH.toMonoidHom) : Set HD))
      rw [← Subgroup.map_equiv_normalizer_eq (SD : Subgroup D) eDH]
      exact hMapNormSDcyc
    rcases secondCase_linear_psl2_normalComplement_or_kleinFour
        hKcard hrOdd hKseven hpodd hpqcop hp_ne_r HD PH hPHcard hNormPHcyc with
      hcomp | hklein
    · rcases hcomp with ⟨QH, hQHnormal, hQHcomp, hQHcard⟩
      let QD : Subgroup D := QH.map eDH.symm.toMonoidHom
      have hback := normalComplement_map_mulEquiv
        (PH : Subgroup HD) QH eDH.symm hQHnormal hQHcomp
      have hPHback : (PH : Subgroup HD).map eDH.symm.toMonoidHom = XD := by
        change (((SD : Subgroup D).map eDH.toMonoidHom).map
          eDH.symm.toMonoidHom) = XD
        rw [Subgroup.map_map]
        have heq : eDH.symm.toMonoidHom.comp eDH.toMonoidHom = MonoidHom.id D := by
          ext z
          simp
        rw [heq, Subgroup.map_id, ← hXD_eq_SD]
      have hQDnormal : QD.Normal := hback.1
      have hQDcomp : QD.IsComplement'
          (Subgroup.normalizer (XD : Set D)) := by
        have hc := hback.2
        rw [hPHback] at hc
        exact hc
      let QA : Subgroup G := QD.map D.subtype
      have hamb := ambient_normalComplement_of_subgroupOf
        D (X x) hXleD QD hQDnormal (by simpa [XD] using hQDcomp)
      refine ⟨hXleD, hXidx, QA, hamb.1, hamb.2.1, hamb.2.2.1, ?_⟩
      have hQDcard : Nat.card QD = Nat.card QH := by
        dsimp [QD]
        rw [Subgroup.card_map_of_injective eDH.symm.injective]
      rw [hamb.2.2.2, hQDcard]
      exact hQHcard
    · rcases hklein with ⟨VH, hVHK⟩
      let VD : Subgroup D := VH.map eDH.symm.toMonoidHom
      have hVDK : IsKleinFour VD :=
        isKleinFour_map_mulEquiv_cross VH hVHK eDH.symm
      let IP : Subgroup post.od.P := VD.map ψ
      have hIPdvd4 : Nat.card IP ∣ 4 := by
        have hdiv := Subgroup.card_map_dvd VD ψ
        simpa [IP, hVDK.card_four] using hdiv
      have hIPdvdp : Nat.card IP ∣ post.od.p := by
        have hdiv : Nat.card IP ∣ Nat.card (⊤ : Subgroup post.od.P) :=
          Subgroup.card_dvd_of_le
            (H := IP) (K := (⊤ : Subgroup post.od.P)) le_top
        simpa [post.od.P_card] using hdiv
      have hcop : Nat.Coprime 4 post.od.p := by
        have hc := (Nat.coprime_two_left.mpr hpodd).pow_left 2
        change Nat.Coprime (2 ^ 2) post.od.p
        exact hc
      have hIPone : Nat.card IP = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hIPdvd4 hIPdvdp
      have hIPbot : IP = ⊥ := Subgroup.card_eq_one.mp hIPone
      have hVDleker : VD ≤ ψ.ker := by
        intro v hv
        change ψ v = 1
        have himg : ψ v ∈ IP :=
          Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
        rw [hIPbot] at himg
        exact Subgroup.mem_bot.mp himg
      let VA : Subgroup G := VD.map D.subtype
      have hVAK : IsKleinFour VA :=
        isKleinFour_map_injective VD hVDK D.subtype D.subtype_injective
      have hVAleE : VA ≤ d'.E := by
        intro v hv
        rcases Subgroup.mem_map.mp hv with ⟨vd, hvd, rfl⟩
        have hψone : ψ vd = 1 := hVDleker hvd
        let ed : d'.E := φ vd
        have heqprod : ePE (incD vd) = (1, ed) := by
          apply Prod.ext
          · simpa [ψ] using hψone
          · rfl
        have hembed : ePE
            (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
              (post.od.P ⊔ d'.E : Subgroup G)) = (1, ed) := heE ed
        have hsubeq : incD vd =
            (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
              (post.od.P ⊔ d'.E : Subgroup G)) :=
          ePE.injective (heqprod.trans hembed.symm)
        have hval : (vd : G) = (ed : G) := congrArg Subtype.val hsubeq
        change (vd : G) ∈ d'.E
        rw [hval]
        exact ed.2
      have hVAleCY : VA ≤ Subgroup.centralizer (Y : Set G) :=
        (Subgroup.map_subtype_le VD).trans inf_le_left
      have hYleCVA : Y ≤ Subgroup.centralizer (VA : Set G) :=
        (Subgroup.le_centralizer_iff).mpr hVAleCY
      have hCVAleM : Subgroup.centralizer (VA : Set G) ≤ w'.M :=
        secondCase_linear_kleinFour_centralizer_le_M
          hmin c' w' d' K post VA hVAleE hVAK
      exact False.elim (hYnotM (hYleCVA.trans hCVAleM))
  have hW_probe : ∀ x : Xs, ∀ W Y : Subgroup G,
      W ≤ (post.od.P ⊔ d'.E) → Nat.card W ∣ Nat.card K →
      MinimalXInvariant (X x) W →
      (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) →
      Y ≤ Reg x → Y ≤ Subgroup.centralizer (W : Set G) →
      (let D : Subgroup G := Subgroup.centralizer (W : Set G) ⊓ Reg x
       Y ≤ D ∧ ¬ post.od.p ∣ (Y.subgroupOf D).index ∧
        ∃ Q : Subgroup G, IsNormalIn Q D ∧
          D = Q ⊔ (D ⊓ Subgroup.normalizer (Y : Set G)) ∧
          Q ⊓ (D ⊓ Subgroup.normalizer (Y : Set G)) = ⊥ ∧
          Nat.card Q ∣ Nat.card K) := by
    intro x W Y hWle hWcard hWmin hYconj hYle hYcent
    let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
    have hpdvd : post.od.p ∣ Nat.card post.equation9.Kinv :=
      secondCase_linear_p_dvd_Kinv c' w' d' post
    have hpodd : Odd post.od.p :=
      secondCase_linear_omega_p_odd c' w' d' post.od
    have hKseven : 7 ≤ Nat.card K :=
      secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv
        d' K post.equation9 post.od.hp_prime hpodd hpdvd
    rcases post.torus.primePower with ⟨r, f, hr, hrOdd, hf, hKcard⟩
    let : Fact r.Prime := ⟨hr⟩
    let qbar : d'.E →* (d'.E ⧸ Subgroup.center d'.E) :=
      QuotientGroup.mk' (Subgroup.center d'.E)
    have hqker : qbar.ker = ⊥ := by
      rw [QuotientGroup.ker_mk', hZ]
    have hqinj : Function.Injective qbar :=
      (MonoidHom.ker_eq_bot_iff qbar).mp hqker
    have hCmap : ((C.subgroupOf d'.E).map qbar) = post.torus.T := by
      exact secondCase_linear_P0_centralizer_eq_torus c' w' d' K post hZ
    have hP0subC : post.od.P0.subgroupOf d'.E ≤ C.subgroupOf d'.E := by
      intro z hz
      change (z : G) ∈ C
      refine ⟨?_, z.property⟩
      change (z : G) ∈ Subgroup.centralizer (post.od.P0 : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      let : IsCyclic (↥post.od.P0) :=
        isCyclic_of_prime_card post.od.P0_card
      let : CommGroup (↥post.od.P0) := IsCyclic.commGroup
      have hzP0 : (z : G) ∈ post.od.P0 := by
        exact hz
      exact congrArg Subtype.val
        (show (⟨p, hp⟩ : post.od.P0) * ⟨(z : G), hzP0⟩ =
            ⟨(z : G), hzP0⟩ * ⟨p, hp⟩ by exact mul_comm _ _)
    have hP0maple : (post.od.P0.subgroupOf d'.E).map qbar ≤ post.torus.T := by
      rw [← hCmap]
      exact Subgroup.map_mono hP0subC
    have hP0mapcard : Nat.card ((post.od.P0.subgroupOf d'.E).map qbar) = post.od.p := by
      calc
        Nat.card ((post.od.P0.subgroupOf d'.E).map qbar) =
            Nat.card (post.od.P0.subgroupOf d'.E) :=
          Subgroup.card_map_of_injective hqinj
        _ = Nat.card post.od.P0 := by
          rw [← Subgroup.card_map_of_injective d'.E.subtype_injective,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (by
              exact post.od.P0_le_K0.trans (by
                rw [post.od.K0_eq]
                exact inf_le_right.trans post.od.K_le_E))]
        _ = post.od.p := post.od.P0_card
    have hpT : post.od.p ∣ Nat.card post.torus.T := by
      rw [← hP0mapcard]
      exact Subgroup.card_dvd_of_le hP0maple
    have hp_ne_r : post.od.p ≠ r := by
      intro hpr
      have hqodd : Odd (Nat.card K) := by
        rw [hKcard]
        exact hrOdd.pow
      have hminus : 2 ∣ Nat.card K - 1 := by
        rcases hqodd with ⟨a, ha⟩
        use a
        omega
      have hplus : 2 ∣ Nat.card K + 1 := by
        rcases hqodd with ⟨a, ha⟩
        use a + 1
        omega
      have hminusdiv : r ∣ Nat.card K - 1 := by
        rcases post.torus.T_card with h | h
        · rw [h] at hpT
          rw [Nat.dvd_div_iff_mul_dvd hminus] at hpT
          have hmul : r ∣ 2 * post.od.p := by
            rw [hpr]
            simpa [Nat.mul_comm] using (Nat.dvd_mul_right r 2)
          exact dvd_trans hmul hpT
        · rw [h] at hpT
          rw [Nat.dvd_div_iff_mul_dvd hplus] at hpT
          have hmul : r ∣ 2 * post.od.p := by
            rw [hpr]
            simpa [Nat.mul_comm] using (Nat.dvd_mul_right r 2)
          have htmp : r ∣ Nat.card K + 1 := dvd_trans hmul hpT
          have hrK : r ∣ Nat.card K := by
            rw [hKcard]
            exact dvd_pow_self r (Nat.ne_of_gt hf)
          have hrone : r ∣ 1 := by
            simpa using (Nat.dvd_sub htmp hrK)
          exact False.elim (hr.ne_one (Nat.dvd_one.mp hrone))
      have hrK : r ∣ Nat.card K := by
        rw [hKcard]
        exact dvd_pow_self r (Nat.ne_of_gt hf)
      have hrone : r ∣ 1 := by
        have hdiv := Nat.dvd_sub hrK hminusdiv
        have hsub : Nat.card K - (Nat.card K - 1) = 1 := by omega
        rw [hsub] at hdiv
        exact hdiv
      exact hr.ne_one (Nat.dvd_one.mp hrone)
    have hprcop : Nat.Coprime post.od.p r :=
      (Fact.out : Nat.Prime post.od.p).coprime_iff_not_dvd.mpr (by
        intro h
        exact hp_ne_r ((Nat.prime_dvd_prime_iff_eq
          (Fact.out : Nat.Prime post.od.p) hr).mp h))
    have hpqcop : Nat.Coprime post.od.p (Nat.card K) := by
      rw [hKcard]
      exact hprcop.pow_right f
    let qE : (d'.E ⧸ Subgroup.center d'.E) ≃* d'.E :=
      (QuotientGroup.quotientMulEquivOfEq (G := d'.E) hZ).trans
        (QuotientGroup.quotientBot (G := d'.E))
    have eE : d'.E ≃* PSL2 K :=
      qE.symm.trans (hdE ▸ e).some
    have hSylowCyc : ∀ S : Sylow post.od.p (d'.E), IsCyclic S := by
      intro S
      have hpne2 : post.od.p ≠ 2 := by
        intro hp2
        apply hpodd.not_two_dvd_nat
        rw [hp2]
      have hmap := psl2_sylow_isCyclic_of_coprime_field_card
        K hKcard hKseven post.od.p
          hpne2 hpqcop
          (S.mapSurjective (f := eE.toMonoidHom) eE.surjective)
      let eS := MulEquiv.subgroupMap eE (S : Subgroup d'.E)
      have hmap' : IsCyclic (↥((S.mapSurjective
          (f := eE.toMonoidHom) eE.surjective) : Subgroup (PSL2 K))) := by
        simpa using hmap
      exact (MulEquiv.isCyclic eS).mpr hmap'
    -- the fixed line is not centralized by the minimal invariant `W`
    have hWne : W ≠ ⊥ := by
      dsimp [MinimalXInvariant] at hWmin
      exact hWmin.1
    let hCt : Subgroup G := conjugateSubgroup C (TConj x)
    have hPEinterN : (post.od.P ⊔ d'.E) ⊓
        Subgroup.normalizer (X x : Set G) = post.od.P ⊔ hCt := by
      simpa [hCt, hXeq] using (htr x).2.2.1
    have hPCt_inter : post.od.P ⊓ hCt = ⊥ := by
      apply le_bot_iff.mp
      intro z hz
      have hzP : z ∈ post.od.P := hz.1
      have hzCt : z ∈ hCt := hz.2
      rcases Subgroup.mem_map.mp hzCt with ⟨c0, hc0, hzEq⟩
      have hzE : z ∈ d'.E := by
        have hzEq' : z = (TConj x : G) * (c0 : G) * (TConj x : G)⁻¹ := by
          simpa [MulAut.conj_apply] using hzEq.symm
        rw [hzEq']
        exact d'.E.mul_mem (d'.E.mul_mem (TConj x).2 hc0.2)
          (d'.E.inv_mem (TConj x).2)
      have hzInf : z ∈ post.od.P ⊓ d'.E := ⟨hzP, hzE⟩
      have hbot : z ∈ (⊥ : Subgroup G) := by
        rwa [hPinterE] at hzInf
      exact Subgroup.mem_bot.mp hbot
    have hPCt_comm : ∀ a b : G, a ∈ post.od.P → b ∈ hCt → Commute a b := by
      intro a b ha hb
      rcases Subgroup.mem_map.mp hb with ⟨c0, hc0, hbEq⟩
      have hcE : (TConj x : G) * (c0 : G) * (TConj x : G)⁻¹ ∈ d'.E :=
        d'.E.mul_mem (d'.E.mul_mem (TConj x).2 hc0.2)
          (d'.E.inv_mem (TConj x).2)
      have hb' : b ∈ d'.E := by
        have hbEq' : b = (TConj x : G) * (c0 : G) * (TConj x : G)⁻¹ := by
          simpa [MulAut.conj_apply] using hbEq.symm
        rw [hbEq']
        exact hcE
      exact (Subgroup.mem_centralizer_iff.mp (hEcentP hb')) a ha
    have hWleCt : ∀ Wt : Subgroup G, Wt ≤ post.od.P ⊔ hCt →
        Nat.card Wt ∣ Nat.card K → Wt ≤ hCt := by
      intro Wt hWtle hWtcard
      obtain ⟨ePCt, heP, heCt⟩ :=
        subgroup_sup_exists_prod_equiv_of_commute_of_disjoint
          post.od.P hCt hPCt_inter hPCt_comm
      let ψP : (post.od.P ⊔ hCt : Subgroup G) →* post.od.P :=
        (MonoidHom.fst post.od.P hCt).comp ePCt.toMonoidHom
      let WtI : Subgroup (post.od.P ⊔ hCt : Subgroup G) :=
        Wt.subgroupOf (post.od.P ⊔ hCt)
      let IP : Subgroup post.od.P := WtI.map ψP
      have hIPdvdW : Nat.card IP ∣ Nat.card Wt := by
        have h := Subgroup.card_map_dvd WtI ψP
        have hWtI : Nat.card WtI = Nat.card Wt := by
          calc
            Nat.card WtI = Nat.card (WtI.map (post.od.P ⊔ hCt).subtype) :=
              (Subgroup.card_map_of_injective (post.od.P ⊔ hCt).subtype_injective).symm
            _ = Nat.card (Wt ⊓ (post.od.P ⊔ hCt) : Subgroup G) := by
              rw [Subgroup.subgroupOf_map_subtype]
            _ = Nat.card Wt := by rw [inf_eq_left.mpr hWtle]
        rw [hWtI] at h
        exact h
      have hIPdvdp : Nat.card IP ∣ post.od.p := by
        have h := Subgroup.card_dvd_of_le
          (H := IP) (K := (⊤ : Subgroup post.od.P)) le_top
        simpa [post.od.P_card] using h
      have hpr : ¬ post.od.p ∣ r := by
        intro h
        exact hp_ne_r ((Nat.prime_dvd_prime_iff_eq
          (Fact.out : Nat.Prime post.od.p) hr).mp h)
      have hpcopr : Nat.Coprime post.od.p r :=
        (Fact.out : Nat.Prime post.od.p).coprime_iff_not_dvd.mpr hpr
      have hcop : Nat.Coprime post.od.p (Nat.card K) := by
        rw [hKcard]
        exact hpcopr.pow_right f
      have hIPdvdq : Nat.card IP ∣ Nat.card K := hIPdvdW.trans hWtcard
      have hIPone : Nat.card IP = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hIPdvdp hIPdvdq
      have hIPbot : IP = ⊥ := Subgroup.card_eq_one.mp hIPone
      intro z hz
      let zi : (post.od.P ⊔ hCt : Subgroup G) := ⟨z, hWtle hz⟩
      have hψone : ψP zi = 1 := by
        have himg : ψP zi ∈ IP :=
          Subgroup.mem_map.mpr ⟨zi, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
        rw [hIPbot] at himg
        exact Subgroup.mem_bot.mp himg
      let e0 : hCt := (ePCt zi).2
      have heqprod : ePCt zi = (1, e0) := by
        apply Prod.ext
        · simpa [ψP] using hψone
        · rfl
      have hembed : ePCt (⟨(e0 : G), Subgroup.mem_sup_right e0.2⟩ :
          (post.od.P ⊔ hCt : Subgroup G)) = (1, e0) :=
        heCt e0
      have hsubeq : zi =
          (⟨(e0 : G), Subgroup.mem_sup_right e0.2⟩ :
            (post.od.P ⊔ hCt : Subgroup G)) :=
        ePCt.injective (heqprod.trans hembed.symm)
      have hval : z = (e0 : G) := congrArg Subtype.val hsubeq
      rw [hval]
      exact e0.2
    have hqodd : Odd (Nat.card K) := by
      rw [hKcard]
      exact hrOdd.pow
    have hTcard_cop : Nat.Coprime (Nat.card post.torus.T) (Nat.card K) := by
      rcases post.torus.T_card with h | h
      · rw [h]
        apply Nat.coprime_of_dvd
        intro p hp hpdvd hpdvdK
        have h2 : 2 ∣ Nat.card K - 1 := by
          rcases hqodd with ⟨a, ha⟩
          use a
          omega
        have hpdvdq1 : p ∣ Nat.card K - 1 := by
          rcases hpdvd with ⟨k, hk⟩
          refine ⟨2 * k, ?_⟩
          calc
            Nat.card K - 1 = ((Nat.card K - 1) / 2) * 2 :=
              (Nat.div_mul_cancel h2).symm
            _ = (p * k) * 2 := by rw [hk]
            _ = p * (2 * k) := by ring
        have hpdvd1 : p ∣ 1 := by
          have hdiv := Nat.dvd_sub hpdvdK hpdvdq1
          have hsub : Nat.card K - (Nat.card K - 1) = 1 := by omega
          rwa [hsub] at hdiv
        exact hp.not_dvd_one hpdvd1
      · rw [h]
        apply Nat.coprime_of_dvd
        intro p hp hpdvd hpdvdK
        have h2 : 2 ∣ Nat.card K + 1 := by
          rcases hqodd with ⟨a, ha⟩
          use a + 1
          omega
        have hpdvdq1 : p ∣ Nat.card K + 1 := by
          rcases hpdvd with ⟨k, hk⟩
          refine ⟨2 * k, ?_⟩
          calc
            Nat.card K + 1 = ((Nat.card K + 1) / 2) * 2 :=
              (Nat.div_mul_cancel h2).symm
            _ = (p * k) * 2 := by rw [hk]
            _ = p * (2 * k) := by ring
        have hpdvd1 : p ∣ 1 := by
          have hdiv := Nat.dvd_sub hpdvdq1 hpdvdK
          have hsub : Nat.card K + 1 - Nat.card K = 1 := by omega
          rwa [hsub] at hdiv
        exact hp.not_dvd_one hpdvd1
    have hCcard : Nat.card C = Nat.card post.torus.T := by
      calc
        Nat.card C = Nat.card (C.subgroupOf d'.E) := by
          rw [← Subgroup.card_map_of_injective d'.E.subtype_injective,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
        _ = Nat.card ((C.subgroupOf d'.E).map qbar) := by
          rw [Subgroup.card_map_of_injective hqinj]
        _ = Nat.card post.torus.T := by rw [hCmap]
    have hCtcop : Nat.Coprime (Nat.card hCt) (Nat.card K) := by
      change Nat.Coprime (Nat.card
        (C.map (MulAut.conj (TConj x : G)).toMonoidHom)) (Nat.card K)
      rw [Subgroup.card_map_of_injective (MulAut.conj (TConj x : G)).injective]
      rw [hCcard]
      exact hTcard_cop
    have hWnotCX : ¬ W ≤ Subgroup.centralizer (X x : Set G) := by
      intro hWleC
      have hWleN : W ≤ Subgroup.normalizer (X x : Set G) :=
        hWleC.trans (Subgroup.centralizer_le_normalizer (X x : Set G))
      have hWlePCt : W ≤ post.od.P ⊔ hCt := by
        intro z hz
        have hmem : z ∈ (post.od.P ⊔ d'.E) ⊓
            Subgroup.normalizer (X x : Set G) := ⟨hWle hz, hWleN hz⟩
        rwa [hPEinterN] at hmem
      have hWleCt' : W ≤ hCt := hWleCt W hWlePCt hWcard
      have hWdivCt : Nat.card W ∣ Nat.card hCt :=
        Subgroup.card_dvd_of_le hWleCt'
      have hWone : Nat.card W = 1 :=
        Nat.eq_one_of_dvd_coprimes hCtcop hWdivCt hWcard
      exact hWne (Subgroup.card_eq_one.mp hWone)
    have hXnotCW : ¬ X x ≤ Subgroup.centralizer (W : Set G) := by
      intro hle
      exact hWnotCX ((Subgroup.le_centralizer_iff).mpr hle)
    -- the region is a direct product `X x × E'`
    let E' : Subgroup G := conjugateSubgroup d'.E (hreg x)
    have hXeqh : X x = conjugateSubgroup post.od.P (hreg x) := by
      rw [hXeq x]
      exact (htr x).1
    have hXinterE' : X x ⊓ E' = ⊥ := by
      rw [hXeqh]
      have hmap : conjugateSubgroup (post.od.P ⊓ d'.E) (hreg x) =
          conjugateSubgroup post.od.P (hreg x) ⊓
            conjugateSubgroup d'.E (hreg x) := by
        change (post.od.P ⊓ d'.E).map (MulAut.conj (hreg x)).toMonoidHom =
          post.od.P.map (MulAut.conj (hreg x)).toMonoidHom ⊓
            d'.E.map (MulAut.conj (hreg x)).toMonoidHom
        exact Subgroup.map_inf post.od.P d'.E
          (MulAut.conj (hreg x)).toMonoidHom (MulAut.conj (hreg x)).injective
      rw [← hmap, hPinterE]
      change (⊥ : Subgroup G).map (MulAut.conj (hreg x)).toMonoidHom = ⊥
      rw [Subgroup.map_bot]
    have hE'centX : E' ≤ Subgroup.centralizer (X x : Set G) := by
      rw [hXeqh]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      rcases Subgroup.mem_map.mp hz with ⟨e0, he0, rfl⟩
      rcases Subgroup.mem_map.mp hp with ⟨p0, hp0, rfl⟩
      have hcomm : p0 * e0 = e0 * p0 :=
        (Subgroup.mem_centralizer_iff.mp (hEcentP he0)) p0 hp0
      calc
        (MulEquiv.toMonoidHom (MulAut.conj (hreg x))) p0 *
            (MulEquiv.toMonoidHom (MulAut.conj (hreg x))) e0 =
          (MulEquiv.toMonoidHom (MulAut.conj (hreg x))) (p0 * e0) := by
            rw [← map_mul]
        _ = (MulEquiv.toMonoidHom (MulAut.conj (hreg x))) (e0 * p0) := by
            rw [hcomm]
        _ = (MulEquiv.toMonoidHom (MulAut.conj (hreg x))) e0 *
            (MulEquiv.toMonoidHom (MulAut.conj (hreg x))) p0 := by
            rw [map_mul]
    have hcommRE : ∀ a b : G, a ∈ X x → b ∈ E' → Commute a b := by
      intro a b ha hb
      exact (Subgroup.mem_centralizer_iff.mp (hE'centX hb)) a ha
    let D : Subgroup G := Subgroup.centralizer (W : Set G) ⊓ Reg x
    have hYleD : Y ≤ D := le_inf hYcent hYle
    have hXcardX : Nat.card (X x) = post.od.p := by
      simpa [hXeq] using hXcard x
    have hDX : D ⊓ X x = ⊥ := by
      by_contra hne
      have hcardDiv : Nat.card (↥(D ⊓ X x : Subgroup G)) ∣ post.od.p := by
        rw [← hXcardX]
        exact Subgroup.card_dvd_of_le inf_le_right
      have hcardEq : Nat.card (↥(D ⊓ X x : Subgroup G)) = post.od.p := by
        rcases (Nat.dvd_prime post.od.hp_prime).mp hcardDiv with hone | hp'
        · exact False.elim (hne (Subgroup.card_eq_one.mp hone))
        · exact hp'
      have hEq : D ⊓ X x = X x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by
          rw [hXcardX, hcardEq])
      have hXleD : X x ≤ D := by
        rw [← hEq]
        exact inf_le_left
      exact hXnotCW (hXleD.trans inf_le_left)
    let incD : D →* Reg x := Subgroup.inclusion inf_le_right
    obtain ⟨eRE, heX, heE'⟩ :=
      subgroup_sup_exists_prod_equiv_of_commute_of_disjoint (X x) E' hXinterE' hcommRE
    let φ : D →* E' :=
      (MonoidHom.snd (X x) E').comp (eRE.toMonoidHom.comp incD)
    let ψ : D →* X x :=
      (MonoidHom.fst (X x) E').comp (eRE.toMonoidHom.comp incD)
    have hφinj : Function.Injective φ := by
      apply (MonoidHom.ker_eq_bot_iff φ).mp
      apply le_bot_iff.mp
      intro z hz
      have hsnd : (eRE (incD z)).2 = 1 := by
        dsimp [φ] at hz
        exact hz
      let a : X x := (eRE (incD z)).1
      have heq : eRE (incD z) = (a, 1) := by
        apply Prod.ext
        · rfl
        · exact hsnd
      have hpa : eRE ⟨(a : G), Subgroup.mem_sup_left a.2⟩ = (a, 1) := heX a
      have hincEq : incD z = ⟨(a : G), Subgroup.mem_sup_left a.2⟩ :=
        eRE.injective (heq.trans hpa.symm)
      have hzX : (z : G) ∈ X x := by
        have hv := congrArg Subtype.val hincEq
        change (z : G) = (a : G) at hv
        rw [hv]
        exact a.2
      have hzInf : (z : G) ∈ (D ⊓ X x : Subgroup G) := ⟨z.2, hzX⟩
      have hzOne : (z : G) = 1 := by
        rw [hDX] at hzInf
        exact Subgroup.mem_bot.mp hzInf
      exact Subtype.ext hzOne
    have hYcard : Nat.card Y = post.od.p := by
      rcases hYconj with ⟨g, hg⟩
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        post.od.P_card]
    have hYneX : Y ≠ X x := by
      intro hY
      apply hXnotCW
      rw [← hY]
      exact hYcent
    have hYinterX : Y ⊓ X x = ⊥ := by
      exact inf_eq_bot_of_not_le_of_prime_card (H := Y) (P := X x)
        (hXcardX ▸ post.od.hp_prime) (by
          intro hle
          exact hYneX ((Subgroup.eq_of_le_of_card_ge hle
            (by rw [hXcardX, hYcard])).symm))
    -- every order-`p` subgroup of the component is a conjugate of `P0`
    have hOrderP_conj : ∀ (R : Subgroup G), R ≤ d'.E → Nat.card R = post.od.p →
        ∃ e : d'.E, R = conjugateSubgroup post.od.P0 (e : G) := by
      intro R hRleE hRcard
      let RE : Subgroup (d'.E) := R.subgroupOf d'.E
      have hREcard : Nat.card RE = post.od.p := by
        calc
          Nat.card RE = Nat.card (RE.map d'.E.subtype) :=
            (Subgroup.card_map_of_injective d'.E.subtype_injective).symm
          _ = Nat.card (R ⊓ d'.E : Subgroup G) := by
            rw [Subgroup.subgroupOf_map_subtype]
          _ = Nat.card R := by rw [inf_eq_left.mpr hRleE]
          _ = post.od.p := hRcard
      have hREp : IsPGroup post.od.p RE :=
        IsPGroup.of_card (n := 1) (by simpa [hREcard])
      obtain ⟨S, hRS⟩ := hREp.exists_le_sylow
      let P0E : Subgroup (d'.E) := post.od.P0.subgroupOf d'.E
      have hP0Ecard : Nat.card P0E = post.od.p := by
        calc
          Nat.card P0E = Nat.card (P0E.map d'.E.subtype) :=
            (Subgroup.card_map_of_injective d'.E.subtype_injective).symm
          _ = Nat.card (post.od.P0 ⊓ d'.E : Subgroup G) := by
            rw [Subgroup.subgroupOf_map_subtype]
          _ = Nat.card post.od.P0 := by
            rw [inf_eq_left.mpr (by
              exact post.od.P0_le_K0.trans (by
                rw [post.od.K0_eq]
                exact inf_le_right.trans post.od.K_le_E))]
          _ = post.od.p := post.od.P0_card
      have hP0Ep : IsPGroup post.od.p P0E :=
        IsPGroup.of_card (n := 1) (by simpa [hP0Ecard])
      obtain ⟨S0, hP0S0⟩ := hP0Ep.exists_le_sylow
      obtain ⟨e, he⟩ :=
        @MulAction.IsPretransitive.exists_smul_eq (d'.E) (Sylow post.od.p (d'.E))
          inferInstance inferInstance S0 S
      have hSmap : (S0 : Subgroup (d'.E)).map (MulAut.conj e).toMonoidHom =
          (S : Subgroup (d'.E)) := by
        have hcoe := congrArg
          (fun T : Sylow post.od.p (d'.E) => (T : Subgroup (d'.E))) he
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hcoe
        have hmap : (S0 : Subgroup (d'.E)).map (MulAut.conj e).toMonoidHom =
            (S0 : Subgroup (d'.E)).map
              (MulDistribMulAction.toMonoidEnd (M := MulAut (d'.E)) (A := d'.E)
                (MulAut.conj e)) := by
          congr 1
        rw [hmap]
        exact hcoe
      have hS : IsCyclic (S : Subgroup (d'.E)) := hSylowCyc S
      have hS0 : IsCyclic (S0 : Subgroup (d'.E)) := hSylowCyc S0
      let : IsCyclic (S : Subgroup (d'.E)) := hS
      have hpkS : post.od.p ∣ Nat.card (S : Subgroup (d'.E)) := by
        have hREdvd : Nat.card RE ∣ Nat.card (S : Subgroup (d'.E)) :=
          Subgroup.card_dvd_of_le hRS
        rwa [hREcard] at hREdvd
      obtain ⟨H0, hH0, huniq⟩ := secondCase_unique_order_p_subgroup_of_cyclic
        (G := d'.E) (T := (S : Subgroup (d'.E))) hS rfl hpkS
      have hRE_H0 : RE = H0 := huniq RE ⟨hRS, hREcard⟩
      have hP0map_H0 : P0E.map (MulAut.conj e).toMonoidHom = H0 := by
        apply huniq
        constructor
        · rw [← hSmap]
          exact Subgroup.map_mono hP0S0
        · rw [Subgroup.card_map_of_injective (MulAut.conj e).injective, hP0Ecard]
      have hREmap : RE = P0E.map (MulAut.conj e).toMonoidHom := by
        rw [hRE_H0, hP0map_H0]
      refine ⟨e, ?_⟩
      have hRmap : R = RE.map d'.E.subtype := by
        dsimp [RE]
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRleE]
      rw [hRmap]
      change (RE.map d'.E.subtype) =
        conjugateSubgroup post.od.P0 (e : G)
      have hP0map : (P0E.map (MulAut.conj (e : d'.E)).toMonoidHom).map d'.E.subtype =
          conjugateSubgroup post.od.P0 (e : G) := by
        change (P0E.map (MulAut.conj (e : d'.E)).toMonoidHom).map d'.E.subtype =
          post.od.P0.map (MulAut.conj (e : G)).toMonoidHom
        apply Subgroup.ext
        intro z
        constructor
        · intro hz
          rcases Subgroup.mem_map.mp hz with ⟨x, hx, hzx⟩
          rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, hxx⟩
          have hx0P0 : (x0 : G) ∈ post.od.P0 := Subgroup.mem_subgroupOf.mp hx0
          refine Subgroup.mem_map.mpr ⟨(x0 : G), hx0P0, ?_⟩
          calc
            (e : G) * (x0 : G) * (e : G)⁻¹ = d'.E.subtype x := by
              have hxx' : x = (e : d'.E) * x0 * (e : d'.E)⁻¹ := by
                simpa [MulAut.conj_apply] using hxx.symm
              rw [hxx']
              rfl
            _ = z := hzx
        · intro hz
          rcases Subgroup.mem_map.mp hz with ⟨p0, hp0, hzp⟩
          have hp0E : (p0 : G) ∈ d'.E := post.od.P0_le_K0.trans (by
            rw [post.od.K0_eq]
            exact inf_le_right.trans post.od.K_le_E) hp0
          let p0E : d'.E := ⟨p0, hp0E⟩
          refine Subgroup.mem_map.mpr ⟨
            (⟨(e : d'.E) * p0E * (e : d'.E)⁻¹,
              d'.E.mul_mem (d'.E.mul_mem e.2 hp0E) (d'.E.inv_mem e.2)⟩ : d'.E), ?_, ?_⟩
          · refine Subgroup.mem_map.mpr ⟨p0E, Subgroup.mem_subgroupOf.mpr hp0, ?_⟩
            · apply Subtype.ext
              rfl
          · calc
              d'.E.subtype (⟨(e : d'.E) * p0E * (e : d'.E)⁻¹,
                  d'.E.mul_mem (d'.E.mul_mem e.2 hp0E) (d'.E.inv_mem e.2)⟩ : d'.E) =
                  (e : G) * (p0 : G) * (e : G)⁻¹ := by rfl
              _ = z := hzp
      rw [hREmap, hP0map]
    have hYnotE' : ¬ Y ≤ E' := by
      intro hYleE'
      let Y0 : Subgroup G := conjugateSubgroup Y (hreg x)⁻¹
      have hY0leE : Y0 ≤ d'.E := by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
        have hyE' : y ∈ E' := hYleE' hy
        rcases Subgroup.mem_map.mp hyE' with ⟨e0, he0, hyeq⟩
        have hyeq' : y = (hreg x) * e0 * (hreg x)⁻¹ := by
          simpa [MulAut.conj_apply] using hyeq.symm
        rw [hyeq']
        have hEq : (MulEquiv.toMonoidHom (MulAut.conj (hreg x)⁻¹))
            ((hreg x) * e0 * (hreg x)⁻¹) = (e0 : G) := by
          simp [MulAut.conj_apply, mul_assoc]
        rw [hEq]
        exact he0
      have hY0card : Nat.card Y0 = post.od.p := by
        change Nat.card (Y.map (MulAut.conj (hreg x)⁻¹).toMonoidHom) = post.od.p
        rw [Subgroup.card_map_of_injective (MulAut.conj (hreg x)⁻¹).injective]
        exact hYcard
      obtain ⟨e0, he0⟩ := hOrderP_conj Y0 hY0leE hY0card
      have hY0conjP : ∃ g : G, Y0 = conjugateSubgroup post.od.P g := by
        rcases hYconj with ⟨g, hg⟩
        refine ⟨(hreg x)⁻¹ * g, ?_⟩
        dsimp [Y0]
        rw [hg]
        change (post.od.P.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj (hreg x)⁻¹).toMonoidHom =
          post.od.P.map (MulAut.conj ((hreg x)⁻¹ * g)).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext z
        simp [MulAut.conj_apply, mul_assoc]
      rcases hY0conjP with ⟨g, hg⟩
      have hPconjP0 : ∃ z : G, conjugateSubgroup post.od.P z = post.od.P0 := by
        refine ⟨(e0 : G)⁻¹ * g, ?_⟩
        calc
          conjugateSubgroup post.od.P ((e0 : G)⁻¹ * g) =
              conjugateSubgroup (conjugateSubgroup post.od.P g) (e0 : G)⁻¹ := by
            change post.od.P.map (MulAut.conj ((e0 : G)⁻¹ * g)).toMonoidHom =
              (post.od.P.map (MulAut.conj g).toMonoidHom).map
                (MulAut.conj (e0 : G)⁻¹).toMonoidHom
            rw [Subgroup.map_map]
            congr 1
            ext z
            simp [MulAut.conj_apply, mul_assoc]
          _ = conjugateSubgroup Y0 (e0 : G)⁻¹ := by rw [hg]
          _ = conjugateSubgroup
              (conjugateSubgroup post.od.P0 (e0 : G)) (e0 : G)⁻¹ := by rw [he0]
          _ = post.od.P0 := by
            change (post.od.P0.map (MulAut.conj (e0 : G)).toMonoidHom).map
              (MulAut.conj (e0 : G)⁻¹).toMonoidHom = post.od.P0
            rw [Subgroup.map_map]
            congr 1
            ext z
            simp [MulAut.conj_apply, mul_assoc]
      exact secondCase_linear_P_not_conjugate_P0 c' w' d' K post hPconjP0
    let YD : Subgroup D := Y.subgroupOf D
    have hYDcard : Nat.card YD = post.od.p := by
      calc
        Nat.card YD = Nat.card (YD.map D.subtype) :=
          (Subgroup.card_map_of_injective D.subtype_injective).symm
        _ = Nat.card Y := by
          rw [show YD.map D.subtype = Y by
            dsimp [YD]
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYleD]]
        _ = post.od.p := hYcard
    have hYDnotker : ¬ YD ≤ ψ.ker := by
      intro hYDker
      apply hYnotE'
      intro z hzY
      let zd : D := ⟨z, hYleD hzY⟩
      have hzdYD : zd ∈ YD := by
        exact Subgroup.mem_subgroupOf.mpr hzY
      have hψone : ψ zd = 1 := hYDker hzdYD
      let ed : E' := φ zd
      have heqprod : eRE (incD zd) = (1, ed) := by
        apply Prod.ext
        · dsimp [ψ] at hψone ⊢
          exact hψone
        · rfl
      have hembed : eRE
          (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
            (Reg x : Subgroup G)) =
          (1, ed) := heE' ed
      have hsubeq : incD zd =
          (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
            (Reg x : Subgroup G)) :=
        eRE.injective (heqprod.trans hembed.symm)
      have hval : z = (ed : G) := congrArg Subtype.val hsubeq
      rw [hval]
      exact ed.2
    have hYDp : IsPGroup post.od.p YD :=
      IsPGroup.of_card (n := 1) (by simpa [hYDcard])
    obtain ⟨SD, hYDleSD⟩ := hYDp.exists_le_sylow
    have hSDcyc : IsCyclic SD := by
      obtain ⟨SE, hSleSE⟩ :=
        (SD.isPGroup').map φ |>.exists_le_sylow
      have hSEcyc : IsCyclic SE := by
        let eE' : (d'.E) ≃* (E' : Subgroup G) :=
          MulEquiv.subgroupMap (MulAut.conj (hreg x)) d'.E
        let SE0 : Sylow post.od.p (d'.E) :=
          SE.mapSurjective (f := eE'.symm.toMonoidHom) eE'.symm.surjective
        exact (MulEquiv.isCyclic (MulEquiv.subgroupMap eE'.symm
          (SE : Subgroup (E' : Type u)))).mpr
            (hSylowCyc SE0)
      have hmapcyc : IsCyclic ((SD : Subgroup D).map φ) := by
        let : IsCyclic SE := hSEcyc
        exact Subgroup.isCyclic_of_le hSleSE
      let eSD : SD ≃* ((SD : Subgroup D).map φ) :=
        Subgroup.equivMapOfInjective (SD : Subgroup D) φ hφinj
      exact (MulEquiv.isCyclic eSD).mpr hmapcyc
    let YSD : Subgroup SD := YD.subgroupOf (SD : Subgroup D)
    have hYSDcard : Nat.card YSD = post.od.p := by
      calc
        Nat.card YSD = Nat.card YD :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYDleSD).toEquiv
        _ = post.od.p := hYDcard
    let ψSD : SD →* X x := ψ.comp (SD : Subgroup D).subtype
    have hYSDnotker : ¬ YSD ≤ ψSD.ker := by
      intro hle
      apply hYDnotker
      intro z hzYD
      let zs : SD := ⟨z, hYDleSD hzYD⟩
      have hzsY : zs ∈ YSD := by
        exact Subgroup.mem_subgroupOf.mpr hzYD
      have hzs := hle hzsY
      simpa [ψSD, zs] using hzs
    have hψSDinj : Function.Injective ψSD :=
      cyclic_pGroup_hom_injective_of_prime_subgroup_not_le_ker
        SD.isPGroup' hSDcyc YSD hYSDcard ψSD hYSDnotker
    have hSDcardle : Nat.card SD ≤ Nat.card (X x) :=
      Nat.card_le_card_of_injective ψSD hψSDinj
    have hSDcard : Nat.card SD = post.od.p := by
      apply le_antisymm
      · simpa [hXcardX] using hSDcardle
      · calc
          post.od.p = Nat.card YD := hYDcard.symm
          _ ≤ Nat.card SD := Subgroup.card_le_of_le hYDleSD
    have hYD_eq_SD : YD = (SD : Subgroup D) := by
      apply Subgroup.eq_of_le_of_card_ge hYDleSD
      rw [hYDcard, hSDcard]
    have hYidx : ¬ post.od.p ∣ YD.index := by
      rw [hYD_eq_SD]
      exact SD.not_dvd_index
    -- `Y` does not meet the transported component
    have hYinterE' : Y ⊓ E' = ⊥ := by
      by_contra hne
      have hcardDiv : Nat.card (↥(Y ⊓ E' : Subgroup G)) ∣ post.od.p := by
        rw [← hYcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hcardEq : Nat.card (↥(Y ⊓ E' : Subgroup G)) = post.od.p := by
        rcases (Nat.dvd_prime post.od.hp_prime).mp hcardDiv with hone | hp'
        · exact False.elim (hne (Subgroup.card_eq_one.mp hone))
        · exact hp'
      have hEq : Y ⊓ E' = Y :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hYcard, hcardEq])
      have hYleE' : Y ≤ E' := by
        rw [← hEq]
        exact inf_le_right
      exact hYnotE' hYleE'
    -- the projected line and its centralizer in the transported component
    let R0 : Subgroup E' := YD.map φ
    have hR0card : Nat.card R0 = post.od.p := by
      change Nat.card (YD.map φ) = post.od.p
      rw [Subgroup.card_map_of_injective hφinj, hYDcard]
    have hR0gen : ∀ r : R0, r ≠ 1 → ∀ s : R0, ∃ k : ℕ, (s : E') = (r : E') ^ k := by
      intro r hr s
      have hrorder : orderOf (r : E') = post.od.p := by
        have hdvd : orderOf (r : E') ∣ post.od.p := by
          rw [← hR0card]
          exact Subgroup.orderOf_dvd_natCard R0 r.2
        rcases (Nat.dvd_prime post.od.hp_prime).mp hdvd with h1 | hp'
        · exact False.elim (hr (by
            apply Subtype.ext
            exact orderOf_eq_one_iff.mp h1))
        · exact hp'
      have hzcard : Nat.card (Subgroup.zpowers (r : E') : Subgroup E') = post.od.p := by
        rw [Nat.card_zpowers, hrorder]
      have hzle : Subgroup.zpowers (r : E') ≤ R0 := Subgroup.zpowers_le.mpr r.2
      have hzeq : Subgroup.zpowers (r : E') = R0 :=
        Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard, hR0card])
      have hs : (s : E') ∈ Subgroup.zpowers (r : E') := by
        rw [hzeq]
        exact s.2
      rcases Subgroup.mem_zpowers_iff.mp hs with ⟨k, hk⟩
      have hmod : (r : E') ^ k = (r : E') ^ ((k % (post.od.p : ℤ)).toNat) := by
        have h1 := zpow_mod_orderOf (r : E') k
        rw [hrorder] at h1
        have h2 : (r : E') ^ (k % (post.od.p : ℤ)) =
            (r : E') ^ ((k % (post.od.p : ℤ)).toNat) := by
          rw [← zpow_natCast]
          congr 1
          exact (Int.toNat_of_nonneg (Int.emod_nonneg k (by
            exact_mod_cast (Nat.Prime.ne_zero (Fact.out : Nat.Prime post.od.p))))).symm
        exact h1.symm.trans h2
      refine ⟨(k % (post.od.p : ℤ)).toNat, ?_⟩
      rw [← hmod]
      exact hk.symm
    have hkerψ_le : ψ.ker ≤ (D ⊓ E').subgroupOf D := by
      intro z hz
      have hz' : (eRE (incD z)).1 = 1 := by
        dsimp [ψ] at hz
        exact hz
      let ed : E' := (eRE (incD z)).2
      have heq : eRE (incD z) = (1, ed) := by
        apply Prod.ext
        · exact hz'
        · rfl
      have hembed : eRE (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
          (Reg x : Subgroup G)) = (1, ed) := heE' ed
      have hsubeq : incD z =
          (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
            (Reg x : Subgroup G)) :=
        eRE.injective (heq.trans hembed.symm)
      have hzDE : (z : G) ∈ D ⊓ E' := by
        refine ⟨z.2, ?_⟩
        have hv := congrArg Subtype.val hsubeq
        change (z : G) = (ed : G) at hv
        rw [hv]
        exact ed.2
      exact Subgroup.mem_subgroupOf.mpr hzDE
    let Nsub : Subgroup D := (D ⊓ Subgroup.normalizer (Y : Set G)).subgroupOf D
    have hφNleC : ∀ z : Nsub,
        φ z.1 ∈ Subgroup.centralizer (R0 : Set E') := by
      intro z
      have hzInf : (z.1 : G) ∈ D ⊓ Subgroup.normalizer (Y : Set G) :=
        Subgroup.mem_subgroupOf.mp z.property
      have hzD : (z.1 : G) ∈ D := hzInf.1
      have hzN : (z.1 : G) ∈ Subgroup.normalizer (Y : Set G) := hzInf.2
      let e : E' := φ z.1
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      by_cases hr1 : r = 1
      · subst r
        simp
      · rcases Subgroup.mem_map.mp hr with ⟨y, hy, hry⟩
        have hyDmem : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
        let zy : G := (z.1 : G) * (y : G) * (z.1 : G)⁻¹
        have hzyzD : zy ∈ D :=
          D.mul_mem (D.mul_mem hzD (hYleD hyDmem)) (D.inv_mem hzD)
        have hzyzY : zy ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp hzN (y : G)).mp hyDmem
        have hφzyz : φ ⟨zy, hzyzD⟩ = e * r * e⁻¹ := by
          dsimp [e]
          have hsub : ⟨zy, hzyzD⟩ =
              (⟨z.1, hzD⟩ : D) * y * (⟨z.1, hzD⟩ : D)⁻¹ := by
            apply Subtype.ext
            dsimp [zy]
          rw [hsub]
          rw [map_mul, map_mul, map_inv]
          rw [hry]
        have hψzyz : ψ ⟨zy, hzyzD⟩ =
            ψ y := by
          have hsub : ⟨zy, hzyzD⟩ =
              (⟨z.1, hzD⟩ : D) * y * (⟨z.1, hzD⟩ : D)⁻¹ := by
            apply Subtype.ext
            dsimp [zy]
          rw [hsub]
          rw [map_mul, map_mul]
          let : IsCyclic (↥(X x)) := isCyclic_of_prime_card hXcardX
          let : CommGroup (↥(X x)) := IsCyclic.commGroup
          have hcomm : ψ (⟨z.1, hzD⟩ : D) * ψ y =
              ψ y * ψ (⟨z.1, hzD⟩ : D) :=
            mul_comm _ _
          rw [hcomm, map_inv]
          group
        have hR0mem : e * r * e⁻¹ ∈ R0 := by
          have hzyzYD : ⟨zy, hzyzD⟩ ∈ YD := by
            exact Subgroup.mem_subgroupOf.mpr hzyzY
          exact Subgroup.mem_map.mpr ⟨⟨zy, hzyzD⟩, hzyzYD, hφzyz⟩
        let rr : R0 := ⟨r, hr⟩
        have hrr1 : rr ≠ 1 := by
          intro hrr
          apply hr1
          exact congrArg Subtype.val hrr
        rcases hR0gen rr hrr1 ⟨e * r * e⁻¹, hR0mem⟩ with ⟨k, hk⟩
        change e * r * e⁻¹ = r ^ k at hk
        have hk0 : k ≠ 0 := by
          intro hk0
          apply hr1
          have h1 : e * r * e⁻¹ = 1 := by
            rw [hk, hk0]
            simp
          calc
            r = e⁻¹ * (e * r * e⁻¹) * e := by group
            _ = e⁻¹ * 1 * e := by rw [h1]
            _ = 1 := by simp
        have hyne : y ≠ 1 := by
          intro hy1
          apply hr1
          rw [← hry, hy1]
          simp
        have hψy_ne : ψ y ≠ 1 := by
          intro hψ1
          have hyE' : (y : G) ∈ E' := by
            have hker : y ∈ ψ.ker := hψ1
            have hker' := hkerψ_le hker
            exact Subgroup.mem_subgroupOf.mp hker'.2
          have hyint : (y : G) ∈ Y ⊓ E' := ⟨hyDmem, hyE'⟩
          have hbot : (y : G) ∈ (⊥ : Subgroup G) := by
            rwa [hYinterE'] at hyint
          have hy1 : y = 1 :=
            Subtype.ext (Subgroup.mem_bot.mp hbot)
          exact hyne hy1
        let fy : X x := ψ y
        have hfy_order : orderOf (fy : G) = post.od.p := by
          have hdvd : orderOf (fy : G) ∣ post.od.p := by
            rw [← hXcardX]
            exact Subgroup.orderOf_dvd_natCard (X x) fy.2
          rcases (Nat.dvd_prime post.od.hp_prime).mp hdvd with h1 | hp'
          · exact False.elim (hψy_ne (by
              apply Subtype.ext
              exact orderOf_eq_one_iff.mp h1))
          · exact hp'
        have hzyz_eq : ⟨zy, hzyzD⟩ =
            y ^ k := by
          apply hφinj
          calc
            φ ⟨zy, hzyzD⟩ = e * r * e⁻¹ := hφzyz
            _ = (r : E') ^ k := hk
            _ = φ (y ^ k) := by
              rw [map_pow, hry]
        have hψy_pow : (fy : X x) ^ k = fy := by
          calc
            (fy : X x) ^ k = ψ (y ^ k) := by
              dsimp [fy]
              rw [map_pow]
            _ = ψ ⟨zy, hzyzD⟩ := by rw [hzyz_eq]
            _ = ψ y := hψzyz
        have hkpos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
        have hsplit : k = (k - 1) + 1 := (Nat.sub_add_cancel hkpos).symm
        have hpow : (fy : X x) ^ (k - 1) = 1 := by
          rw [hsplit, pow_add, pow_one] at hψy_pow
          apply mul_right_cancel (b := fy)
          simpa using hψy_pow
        have hgpow : (fy : G) ^ (k - 1) = 1 := by
          exact congrArg Subtype.val hpow
        have hkdvd : post.od.p ∣ k - 1 := by
          exact hfy_order ▸ orderOf_dvd_of_pow_eq_one hgpow
        have hrdvd : orderOf (r : E') ∣ k - 1 := by
          have hord : orderOf (r : E') = post.od.p := by
            have hdvd : orderOf (r : E') ∣ post.od.p := by
              rw [← hR0card]
              exact Subgroup.orderOf_dvd_natCard R0 hr
            rcases (Nat.dvd_prime post.od.hp_prime).mp hdvd with h1 | hp''
            · exact False.elim (hr1 (orderOf_eq_one_iff.mp h1))
            · exact hp''
          rw [hord]
          exact hkdvd
        have hrkm1 : (r : E') ^ (k - 1) = 1 :=
          (orderOf_dvd_iff_pow_eq_one).mp hrdvd
        have hrpow : (r : E') ^ k = r := by
          calc
            (r : E') ^ k = (r : E') ^ ((k - 1) + 1) :=
              congrArg (fun n : ℕ => (r : E') ^ n) hsplit
            _ = (r : E') ^ (k - 1) * r := by rw [pow_add, pow_one]
            _ = 1 * r := by rw [hrkm1]
            _ = r := by simp
        have her : e * r = r * e := by
          calc
            e * r = (e * r * e⁻¹) * e := by group
            _ = r ^ k * e := by rw [hk]
            _ = r * e := by rw [hrpow]
        exact her.symm
    let TY : Subgroup E' := Subgroup.centralizer (R0 : Set E')
    have hTYcyc : IsCyclic TY := by
      let eE' : d'.E ≃* E' :=
        MulEquiv.subgroupMap (MulAut.conj (hreg x)) d'.E
      let R0E : Subgroup (d'.E) := R0.map eE'.symm.toMonoidHom
      have hR0Ecard : Nat.card R0E = post.od.p := by
        dsimp [R0E]
        rw [Subgroup.card_map_of_injective eE'.symm.injective, hR0card]
      have hR0Eamb : (R0E.map d'.E.subtype) ≤ d'.E := Subgroup.map_subtype_le R0E
      have hR0Eambcard : Nat.card (R0E.map d'.E.subtype) = post.od.p := by
        rw [Subgroup.card_map_of_injective d'.E.subtype_injective, hR0Ecard]
      obtain ⟨e0, he0⟩ := hOrderP_conj (R0E.map d'.E.subtype) hR0Eamb hR0Eambcard
      have hR0Eeq : R0E = (post.od.P0.subgroupOf d'.E).map
          (MulAut.conj e0).toMonoidHom := by
        apply (Subgroup.map_injective d'.E.subtype_injective)
        have hP0map : ((post.od.P0.subgroupOf d'.E).map (MulAut.conj e0).toMonoidHom).map
            d'.E.subtype = conjugateSubgroup post.od.P0 (e0 : G) := by
          change ((post.od.P0.subgroupOf d'.E).map (MulAut.conj (e0 : d'.E)).toMonoidHom).map
            d'.E.subtype = post.od.P0.map (MulAut.conj (e0 : G)).toMonoidHom
          rw [Subgroup.map_map]
          apply Subgroup.ext
          intro z
          constructor
          · intro hz
            rcases Subgroup.mem_map.mp hz with ⟨x, hx, hzx⟩
            have hx0P0 : (x : G) ∈ post.od.P0 := Subgroup.mem_subgroupOf.mp hx
            refine Subgroup.mem_map.mpr ⟨(x : G), hx0P0, ?_⟩
            calc
              (e0 : G) * (x : G) * (e0 : G)⁻¹ =
                  d'.E.subtype ((MulAut.conj (e0 : d'.E)) x) := by
                    simp [MulAut.conj_apply]
              _ = z := hzx
          · intro hz
            rcases Subgroup.mem_map.mp hz with ⟨p0, hp0, hzp⟩
            have hp0E : (p0 : G) ∈ d'.E := post.od.P0_le_K0.trans (by
              rw [post.od.K0_eq]
              exact inf_le_right.trans post.od.K_le_E) hp0
            let p0E : d'.E := ⟨p0, hp0E⟩
            refine Subgroup.mem_map.mpr ⟨p0E, Subgroup.mem_subgroupOf.mpr hp0, ?_⟩
            calc
              d'.E.subtype ((MulAut.conj (e0 : d'.E)) p0E) =
                  (e0 : G) * (p0 : G) * (e0 : G)⁻¹ := by
                    simp [MulAut.conj_apply, p0E]
              _ = z := by
                simpa [MulAut.conj_apply] using hzp
        rw [hP0map]
        exact he0
      have hC0eq : Subgroup.centralizer ((post.od.P0.subgroupOf d'.E) : Set (d'.E)) =
          (C.subgroupOf d'.E) := by
        apply Subgroup.ext
        intro z
        constructor
        · intro hz
          refine Subgroup.mem_subgroupOf.mpr ⟨?_, z.2⟩
          change (z : G) ∈ Subgroup.centralizer (post.od.P0 : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro p hp
          have hpE : (p : G) ∈ d'.E := post.od.P0_le_K0.trans (by
            rw [post.od.K0_eq]
            exact inf_le_right.trans post.od.K_le_E) hp
          let pE : d'.E := ⟨p, hpE⟩
          have hpE0 : pE ∈ post.od.P0.subgroupOf d'.E :=
            Subgroup.mem_subgroupOf.mpr hp
          exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hz) pE hpE0)
        · intro hz
          rw [Subgroup.mem_centralizer_iff]
          intro p hp
          have hpE : (p : G) ∈ d'.E := post.od.P0_le_K0.trans (by
            rw [post.od.K0_eq]
            exact inf_le_right.trans post.od.K_le_E) hp
          let pE : d'.E := ⟨p, hpE⟩
          have hpE0 : pE ∈ post.od.P0.subgroupOf d'.E :=
            Subgroup.mem_subgroupOf.mpr hp
          have hzcentE : (z : d'.E) ∈ Subgroup.centralizer
              ((post.od.P0.subgroupOf d'.E) : Set (d'.E)) := by
            apply Subgroup.mem_centralizer_iff.mpr
            intro q hq
            have hqP0 : (q : G) ∈ post.od.P0 := Subgroup.mem_subgroupOf.mp hq
            have hcommG : (q : G) * (z : G) = (z : G) * (q : G) :=
              (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hz).1)
                (q : G) hqP0
            apply Subtype.ext
            simpa using hcommG
          have hcommE : pE * z = z * pE :=
            (Subgroup.mem_centralizer_iff.mp hzcentE) pE hpE0
          apply Subtype.ext
          simpa using congrArg Subtype.val hcommE
      have hCcyc' : IsCyclic (C.subgroupOf d'.E) := by
        let eC : (C.subgroupOf d'.E) ≃* C :=
          Subgroup.subgroupOfEquivOfLe inf_le_right
        exact (MulEquiv.isCyclic eC).mpr hCcyc
      have hC0cyc : IsCyclic (Subgroup.centralizer
          ((post.od.P0.subgroupOf d'.E) : Set (d'.E))) := by
        rw [hC0eq]
        exact hCcyc'
      have hC0mapcyc : IsCyclic ((Subgroup.centralizer
          ((post.od.P0.subgroupOf d'.E) : Set (d'.E))).map
            (MulAut.conj e0).toMonoidHom) := by
        let eC0 := Subgroup.equivMapOfInjective
          (Subgroup.centralizer ((post.od.P0.subgroupOf d'.E) : Set (d'.E)))
          (MulAut.conj e0).toMonoidHom (MulAut.conj e0).injective
        exact (MulEquiv.isCyclic eC0).mp hC0cyc
      have hCEeq : Subgroup.centralizer (R0E : Set (d'.E)) =
          (Subgroup.centralizer ((post.od.P0.subgroupOf d'.E) : Set (d'.E))).map
            (MulAut.conj e0).toMonoidHom := by
        apply Subgroup.ext
        intro z
        constructor
        · intro hz
          refine Subgroup.mem_map.mpr ⟨(e0⁻¹ : d'.E) * z * e0, ?_, ?_⟩
          · apply Subgroup.mem_centralizer_iff.mpr
            intro p hp
            have hpR : (e0 : d'.E) * p * (e0 : d'.E)⁻¹ ∈ R0E := by
              rw [hR0Eeq]
              exact Subgroup.mem_map.mpr ⟨p, hp, by
                change (e0 : d'.E) * (p : d'.E) * (e0 : d'.E)⁻¹ =
                  (e0 : d'.E) * (p : d'.E) * (e0 : d'.E)⁻¹
                rfl⟩
            have hcomm : ((e0 : d'.E) * p * (e0 : d'.E)⁻¹) * z =
                z * ((e0 : d'.E) * p * (e0 : d'.E)⁻¹) :=
              (Subgroup.mem_centralizer_iff.mp hz)
                ((e0 : d'.E) * p * (e0 : d'.E)⁻¹) hpR
            calc
              p * ((e0⁻¹ : d'.E) * z * e0) =
                  (e0⁻¹ : d'.E) * ((e0 : d'.E) * p * (e0 : d'.E)⁻¹) * z * e0 := by group
              _ = (e0⁻¹ : d'.E) *
                  (((e0 : d'.E) * p * (e0 : d'.E)⁻¹) * z) * e0 := by group
              _ = (e0⁻¹ : d'.E) *
                  (z * ((e0 : d'.E) * p * (e0 : d'.E)⁻¹)) * e0 := by
                rw [hcomm]
              _ = (e0⁻¹ : d'.E) * z *
                  ((e0 : d'.E) * p * (e0 : d'.E)⁻¹) * e0 := by group
              _ = ((e0⁻¹ : d'.E) * z * e0) * p := by group
          · simp [MulAut.conj_apply, mul_assoc]
        · intro hz
          rcases Subgroup.mem_map.mp hz with ⟨w, hw, hzw⟩
          apply Subgroup.mem_centralizer_iff.mpr
          intro p hp
          have hp' : p ∈ (post.od.P0.subgroupOf d'.E).map
              (MulAut.conj e0).toMonoidHom := by
            rwa [hR0Eeq] at hp
          rcases Subgroup.mem_map.mp hp' with ⟨p0, hp0, hpp⟩
          have hwcomm : w * p0 = p0 * w :=
            ((Subgroup.mem_centralizer_iff.mp hw) p0 hp0).symm
          have hzw' : (e0 : d'.E) * w * (e0 : d'.E)⁻¹ = z := by
            simpa [MulAut.conj_apply] using hzw
          have hpp' : (e0 : d'.E) * p0 * (e0 : d'.E)⁻¹ = p := by
            simpa [MulAut.conj_apply] using hpp
          calc
            p * z = ((e0 : d'.E) * p0 * (e0 : d'.E)⁻¹) *
                ((e0 : d'.E) * w * (e0 : d'.E)⁻¹) := by rw [hpp', hzw']
            _ = (e0 : d'.E) * (p0 * w) * (e0 : d'.E)⁻¹ := by group
            _ = (e0 : d'.E) * (w * p0) * (e0 : d'.E)⁻¹ := by rw [hwcomm]
            _ = ((e0 : d'.E) * w * (e0 : d'.E)⁻¹) *
                ((e0 : d'.E) * p0 * (e0 : d'.E)⁻¹) := by group
            _ = z * p := by rw [hzw', hpp']
      have hC0Ecyc : IsCyclic (Subgroup.centralizer (R0E : Set (d'.E))) := by
        rw [hCEeq]
        exact hC0mapcyc
      have hC0mapE' : (Subgroup.centralizer (R0E : Set (d'.E))).map
          eE'.toMonoidHom = TY := by
        apply Subgroup.ext
        intro z
        constructor
        · intro hz
          rcases Subgroup.mem_map.mp hz with ⟨w, hw, hzw⟩
          apply Subgroup.mem_centralizer_iff.mpr
          intro r hr
          have hrback : eE'.symm r ∈ R0E := by
            dsimp [R0E]
            exact Subgroup.mem_map.mpr ⟨r, hr, by simp⟩
          have hwr : eE'.symm r * w = w * eE'.symm r :=
            (Subgroup.mem_centralizer_iff.mp hw) (eE'.symm r) hrback
          have hzw' : eE' w = z := hzw
          calc
            r * z = eE' (eE'.symm r) * eE' w := by
              calc
                r * z = r * eE' w :=
                  congrArg (fun a : E' => r * a) hzw'.symm
                _ = eE' (eE'.symm r) * eE' w := by
                  rw [eE'.apply_symm_apply]
            _ = eE' (eE'.symm r * w) := by rw [map_mul]
            _ = eE' (w * eE'.symm r) := by rw [hwr]
            _ = eE' w * eE' (eE'.symm r) := by rw [map_mul]
            _ = z * r := by
              calc
                eE' w * eE' (eE'.symm r) = eE' w * r := by
                  rw [eE'.apply_symm_apply]
                _ = z * r := congrArg (fun a : E' => a * r) hzw'
        · intro hz
          refine Subgroup.mem_map.mpr ⟨eE'.symm z, ?_, ?_⟩
          · apply Subgroup.mem_centralizer_iff.mpr
            intro r hr
            have hmem : eE' r ∈ R0 := by
              change r ∈ R0.map eE'.symm.toMonoidHom at hr
              rcases Subgroup.mem_map.mp hr with ⟨s, hs, hrs⟩
              have hrs' : eE' r = s := by
                rw [← hrs]
                simp
              rw [hrs']
              exact hs
            have hzr : eE' r * z = z * eE' r :=
              (Subgroup.mem_centralizer_iff.mp hz) (eE' r) hmem
            apply eE'.injective
            calc
              eE' (r * (eE'.symm z)) = eE' r * eE' (eE'.symm z) := by rw [map_mul]
              _ = eE' r * z := by rw [eE'.apply_symm_apply]
              _ = z * eE' r := hzr
              _ = eE' (eE'.symm z) * eE' r := by rw [eE'.apply_symm_apply]
              _ = eE' ((eE'.symm z) * r) := by rw [map_mul]
          · simp
      let eTY : Subgroup.centralizer (R0E : Set (d'.E)) ≃* TY :=
        (MulEquiv.subgroupMap eE' (Subgroup.centralizer (R0E : Set (d'.E)))).trans
          (MulEquiv.subgroupCongr hC0mapE')
      exact (MulEquiv.isCyclic eTY).mp hC0Ecyc
    have hNcyc : IsCyclic Nsub := by
      let fN0 : Nsub →* E' := φ.comp Nsub.subtype
      let fN : Nsub →* TY :=
        MonoidHom.codRestrict fN0 TY (by
          intro z
          simpa [fN0] using hφNleC z)
      have hfNinj : Function.Injective fN := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        have hφab : φ a.1 = φ b.1 := by
          apply Subtype.ext
          exact congrArg (fun z : TY => ((z : E') : G)) hab
        exact congrArg Subtype.val (hφinj hφab)
      let : IsCyclic TY := hTYcyc
      exact isCyclic_of_injective fN hfNinj
    have hNormYDcyc : IsCyclic (Subgroup.normalizer (YD : Set D)) := by
      rw [show Subgroup.normalizer (YD : Set D) =
          (D ⊓ Subgroup.normalizer (Y : Set G)).subgroupOf D by
        dsimp [YD]
        exact normalizer_subgroupOf_eq_subgroupOf_inf_normalizer D Y hYleD]
      exact hNcyc
    have hNormSDcyc : IsCyclic
        (Subgroup.normalizer ((SD : Subgroup D) : Set D)) := by
      have hset : ((SD : Subgroup D) : Set D) = (YD : Set D) :=
        congrArg (fun H : Subgroup D => (H : Set D)) hYD_eq_SD.symm
      rw [hset]
      exact hNormYDcyc
    let fD : D →* PSL2 K :=
      eE.toMonoidHom.comp
        ((MulEquiv.subgroupMap (MulAut.conj (hreg x)) d'.E).symm.toMonoidHom.comp φ)
    have hfDinj : Function.Injective fD := by
      apply eE.injective.comp
      apply (MulEquiv.subgroupMap (MulAut.conj (hreg x)) d'.E).symm.injective.comp
      exact hφinj
    let HD : Subgroup (PSL2 K) := fD.range
    let fR : D →* HD := fD.rangeRestrict
    have hfRinj : Function.Injective fR := by
      intro a b hab
      apply hfDinj
      exact congrArg Subtype.val hab
    let eDH : D ≃* HD := MulEquiv.ofBijective fR
      ⟨hfRinj, fD.rangeRestrict_surjective⟩
    let PH : Sylow post.od.p HD :=
      SD.mapSurjective (f := eDH.toMonoidHom) eDH.surjective
    have hPHcard : Nat.card (PH : Subgroup HD) = post.od.p := by
      change Nat.card ((SD : Subgroup D).map eDH.toMonoidHom) = post.od.p
      rw [Subgroup.card_map_of_injective
        (f := eDH.toMonoidHom) eDH.injective]
      exact hSDcard
    have hMapNormSDcyc : IsCyclic
        ((Subgroup.normalizer ((SD : Subgroup D) : Set D)).map
          eDH.toMonoidHom) := by
      let eN : Subgroup.normalizer ((SD : Subgroup D) : Set D) ≃*
          (Subgroup.normalizer ((SD : Subgroup D) : Set D)).map
            eDH.toMonoidHom :=
        Subgroup.equivMapOfInjective _ eDH.toMonoidHom eDH.injective
      exact (MulEquiv.isCyclic eN).mp hNormSDcyc
    have hNormPHcyc : IsCyclic
        (Subgroup.normalizer ((PH : Subgroup HD) : Set HD)) := by
      change IsCyclic (Subgroup.normalizer
        (((SD : Subgroup D).map eDH.toMonoidHom) : Set HD))
      rw [← Subgroup.map_equiv_normalizer_eq (SD : Subgroup D) eDH]
      exact hMapNormSDcyc
    rcases secondCase_linear_psl2_normalComplement_or_kleinFour
        hKcard hrOdd hKseven hpodd hpqcop hp_ne_r HD PH hPHcard hNormPHcyc with
      hcomp | hklein
    · rcases hcomp with ⟨QH, hQHnormal, hQHcomp, hQHcard⟩
      let QD : Subgroup D := QH.map eDH.symm.toMonoidHom
      have hback := normalComplement_map_mulEquiv
        (PH : Subgroup HD) QH eDH.symm hQHnormal hQHcomp
      have hPHback : (PH : Subgroup HD).map eDH.symm.toMonoidHom = YD := by
        change (((SD : Subgroup D).map eDH.toMonoidHom).map
          eDH.symm.toMonoidHom) = YD
        rw [Subgroup.map_map]
        have heq : eDH.symm.toMonoidHom.comp eDH.toMonoidHom = MonoidHom.id D := by
          ext z
          simp
        rw [heq, Subgroup.map_id, ← hYD_eq_SD]
      have hQDnormal : QD.Normal := hback.1
      have hQDcomp : QD.IsComplement'
          (Subgroup.normalizer (YD : Set D)) := by
        have hc := hback.2
        rw [hPHback] at hc
        exact hc
      let QA : Subgroup G := QD.map D.subtype
      have hamb := ambient_normalComplement_of_subgroupOf
        D Y hYleD QD hQDnormal (by simpa [YD] using hQDcomp)
      refine ⟨hYleD, hYidx, QA, hamb.1, hamb.2.1, hamb.2.2.1, ?_⟩
      have hQDcard : Nat.card QD = Nat.card QH := by
        dsimp [QD]
        rw [Subgroup.card_map_of_injective eDH.symm.injective]
      rw [hamb.2.2.2, hQDcard]
      exact hQHcard
    · rcases hklein with ⟨VH, hVHK⟩
      let VD : Subgroup D := VH.map eDH.symm.toMonoidHom
      have hVDK : IsKleinFour VD :=
        isKleinFour_map_mulEquiv_cross VH hVHK eDH.symm
      let IX : Subgroup (X x) := VD.map ψ
      have hIXdvd4 : Nat.card IX ∣ 4 := by
        have hdiv := Subgroup.card_map_dvd VD ψ
        simpa [IX, hVDK.card_four] using hdiv
      have hIXdvdp : Nat.card IX ∣ post.od.p := by
        have hdiv : Nat.card IX ∣ Nat.card (⊤ : Subgroup (X x)) :=
          Subgroup.card_dvd_of_le
            (H := IX) (K := (⊤ : Subgroup (X x))) le_top
        simpa [hXcardX] using hdiv
      have hcop : Nat.Coprime 4 post.od.p := by
        have hc := (Nat.coprime_two_left.mpr hpodd).pow_left 2
        change Nat.Coprime (2 ^ 2) post.od.p
        exact hc
      have hIXone : Nat.card IX = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hIXdvd4 hIXdvdp
      have hIXbot : IX = ⊥ := Subgroup.card_eq_one.mp hIXone
      have hVDleker : VD ≤ ψ.ker := by
        intro v hv
        change ψ v = 1
        have himg : ψ v ∈ IX :=
          Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
        rw [hIXbot] at himg
        exact Subgroup.mem_bot.mp himg
      let VA : Subgroup G := VD.map D.subtype
      have hVAK : IsKleinFour VA :=
        isKleinFour_map_injective VD hVDK D.subtype D.subtype_injective
      have hVAleE' : VA ≤ E' := by
        intro v hv
        rcases Subgroup.mem_map.mp hv with ⟨vd, hvd, rfl⟩
        have hψone : ψ vd = 1 := hVDleker hvd
        let ed : E' := φ vd
        have heqprod : eRE (incD vd) = (1, ed) := by
          apply Prod.ext
          · dsimp [ψ] at hψone ⊢
            exact hψone
          · rfl
        have hembed : eRE
            (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
              (Reg x : Subgroup G)) = (1, ed) := heE' ed
        have hsubeq : incD vd =
            (⟨(ed : G), Subgroup.mem_sup_right ed.2⟩ :
              (Reg x : Subgroup G)) :=
          eRE.injective (heqprod.trans hembed.symm)
        have hval : (vd : G) = (ed : G) := congrArg Subtype.val hsubeq
        change (vd : G) ∈ E'
        rw [hval]
        exact ed.2
      have hVA'K : IsKleinFour (conjugateSubgroup VA (hreg x)⁻¹) := by
        change IsKleinFour (VA.map (MulAut.conj (hreg x)⁻¹).toMonoidHom)
        exact isKleinFour_map_mulEquiv_cross VA hVAK
          (MulAut.conj (hreg x)⁻¹)
      have hVA'leE : conjugateSubgroup VA (hreg x)⁻¹ ≤ d'.E := by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨v, hv, rfl⟩
        have hvE' : v ∈ E' := hVAleE' hv
        rcases Subgroup.mem_map.mp hvE' with ⟨e0, he0, hveq⟩
        have hveq' : v = (hreg x) * e0 * (hreg x)⁻¹ := by
          simpa [MulAut.conj_apply] using hveq.symm
        have hback_raw : (hreg x)⁻¹ * v * hreg x = e0 := by
          rw [hveq']
          group
        have hback : (MulEquiv.toMonoidHom (MulAut.conj (hreg x)⁻¹)) v = e0 := by
          simpa [MulAut.conj_apply] using hback_raw
        rw [hback]
        exact he0
      have hCVA'leM : Subgroup.centralizer
          (conjugateSubgroup VA (hreg x)⁻¹ : Set G) ≤ w'.M :=
        secondCase_linear_kleinFour_centralizer_le_M
          hmin c' w' d' K post (conjugateSubgroup VA (hreg x)⁻¹) hVA'leE hVA'K
      have hCVAleMh : Subgroup.centralizer (VA : Set G) ≤
          conjugateSubgroup w'.M (hreg x) := by
        intro z hz
        refine Subgroup.mem_map.mpr
          ⟨(hreg x)⁻¹ * z * hreg x, hCVA'leM ?_, by
            simp [MulAut.conj_apply, mul_assoc]⟩
        apply Subgroup.mem_centralizer_iff.mpr
        intro a ha
        rcases Subgroup.mem_map.mp ha with ⟨v, hv, hav⟩
        have hav' : a = (hreg x)⁻¹ * v * hreg x := by
          simpa [MulAut.conj_apply] using hav.symm
        have hvz : v * z = z * v :=
          (Subgroup.mem_centralizer_iff.mp hz) v hv
        rw [hav']
        calc
          ((hreg x)⁻¹ * v * hreg x) *
              ((hreg x)⁻¹ * z * hreg x) =
            (hreg x)⁻¹ * (v * z) * hreg x := by group
          _ = (hreg x)⁻¹ * (z * v) * hreg x := by rw [hvz]
          _ = ((hreg x)⁻¹ * z * hreg x) *
              ((hreg x)⁻¹ * v * hreg x) := by group
      have hVAleD : VA ≤ D := Subgroup.map_subtype_le VD
      have hWleCVA : W ≤ Subgroup.centralizer (VA : Set G) :=
        (Subgroup.le_centralizer_iff).mpr (hVAleD.trans inf_le_left)
      have hWleMh : W ≤ conjugateSubgroup w'.M (hreg x) :=
        hWleCVA.trans hCVAleMh
      have hWlePCt' : W ≤ post.od.P ⊔ hCt := by
        intro z hz
        have hzN : z ∈ Subgroup.normalizer (X x : Set G) := by
          rw [hXeqh]
          rcases Subgroup.mem_map.mp (hWleMh hz) with ⟨m, hm, rfl⟩
          change (MulAut.conj (hreg x)) m ∈
            Subgroup.normalizer
              (post.od.P.map (MulAut.conj (hreg x)).toMonoidHom : Set G)
          rw [← Subgroup.map_normalizer_eq_of_bijective post.od.P
            (MulAut.conj (hreg x)).bijective]
          have hmN : m ∈ Subgroup.normalizer (post.od.P : Set G) := by
            rw [secondCase_linear_P_normalizer_eq_M c' w' d' post.od]
            exact hm
          exact Subgroup.mem_map.mpr ⟨m, hmN, rfl⟩
        have hmem : z ∈ (post.od.P ⊔ d'.E) ⊓
            Subgroup.normalizer (X x : Set G) := ⟨hWle hz, hzN⟩
        rwa [hPEinterN] at hmem
      have hWleCt'' : W ≤ hCt := hWleCt W hWlePCt' hWcard
      have hWdivCt : Nat.card W ∣ Nat.card hCt :=
        Subgroup.card_dvd_of_le hWleCt''
      have hWone : Nat.card W = 1 :=
        Nat.eq_one_of_dvd_coprimes hCtcop hWdivCt hWcard
      exact False.elim (hWne (Subgroup.card_eq_one.mp hWone))

  have hWcount : ∀ x : Xs,
      Nat.card (MinimalXInvariantFamily (post.od.P ⊔ d'.E)
        (Nat.card K) (X x)) ≤ (Nat.card K - 1) / post.od.p := by
    intro x
    let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
    have hpodd : Odd post.od.p :=
      secondCase_linear_omega_p_odd c' w' d' post.od
    rcases post.torus.primePower with ⟨r, f, hr, hrOdd, hf, hKcard⟩
    let : Fact r.Prime := ⟨hr⟩
    have hqodd : Odd (Nat.card K) := by
      rw [hKcard]
      exact hrOdd.pow
    let qbar : d'.E →* (d'.E ⧸ Subgroup.center d'.E) :=
      QuotientGroup.mk' (Subgroup.center d'.E)
    have hqker : qbar.ker = ⊥ := by
      rw [QuotientGroup.ker_mk', hZ]
    have hqinj : Function.Injective qbar :=
      (MonoidHom.ker_eq_bot_iff qbar).mp hqker
    have hCmap : ((C.subgroupOf d'.E).map qbar) = post.torus.T := by
      exact secondCase_linear_P0_centralizer_eq_torus c' w' d' K post hZ
    have hP0subC : post.od.P0.subgroupOf d'.E ≤ C.subgroupOf d'.E := by
      intro z hz
      change (z : G) ∈ C
      refine ⟨?_, z.property⟩
      change (z : G) ∈ Subgroup.centralizer (post.od.P0 : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      let : IsCyclic (↥post.od.P0) :=
        isCyclic_of_prime_card post.od.P0_card
      let : CommGroup (↥post.od.P0) := IsCyclic.commGroup
      have hzP0 : (z : G) ∈ post.od.P0 := hz
      exact congrArg Subtype.val
        (show (⟨p, hp⟩ : post.od.P0) * ⟨(z : G), hzP0⟩ =
            ⟨(z : G), hzP0⟩ * ⟨p, hp⟩ by exact mul_comm _ _)
    have hP0maple : (post.od.P0.subgroupOf d'.E).map qbar ≤ post.torus.T := by
      rw [← hCmap]
      exact Subgroup.map_mono hP0subC
    have hP0mapcard : Nat.card ((post.od.P0.subgroupOf d'.E).map qbar) = post.od.p := by
      calc
        Nat.card ((post.od.P0.subgroupOf d'.E).map qbar) =
            Nat.card (post.od.P0.subgroupOf d'.E) :=
          Subgroup.card_map_of_injective hqinj
        _ = Nat.card post.od.P0 := by
          rw [← Subgroup.card_map_of_injective d'.E.subtype_injective,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (by
              exact post.od.P0_le_K0.trans (by
                rw [post.od.K0_eq]
                exact inf_le_right.trans post.od.K_le_E))]
        _ = post.od.p := post.od.P0_card
    have hpT : post.od.p ∣ Nat.card post.torus.T := by
      rw [← hP0mapcard]
      exact Subgroup.card_dvd_of_le hP0maple
    have hTcard_cop : Nat.Coprime (Nat.card post.torus.T) (Nat.card K) := by
      rcases post.torus.T_card with h | h
      · rw [h]
        exact (secondCase_linear_half_coprime_of_odd hqodd).1
      · rw [h]
        exact (secondCase_linear_half_coprime_of_odd hqodd).2
    have hp_ne_r : post.od.p ≠ r := by
      intro hpr
      have hrT : r ∣ Nat.card post.torus.T := by simpa [hpr] using hpT
      have hrK : r ∣ Nat.card K := by
        rw [hKcard]
        exact dvd_pow_self r (Nat.ne_of_gt hf)
      have hone : r = 1 := Nat.eq_one_of_dvd_coprimes hTcard_cop hrT hrK
      exact hr.ne_one hone
    have hcommPE : ∀ a b : G, a ∈ post.od.P → b ∈ d'.E → Commute a b := by
      intro a b ha hb
      exact (Subgroup.mem_centralizer_iff.mp (hEcentP hb)) a ha
    have hXcardX : Nat.card (X x) = post.od.p := by
      rw [hXeq x]
      exact hXcard x
    have hXlePE : X x ≤ post.od.P ⊔ d'.E := by
      rw [hXeq x]
      exact (hXleAidx x).trans (hAidxlePE x)
    have hXneP : X x ≠ post.od.P := by
      intro hXP
      apply x.1.2.2.1
      have hXP' : x.1.1.map
          (MulAut.conj (TConj x : G)).toMonoidHom = post.od.P := by
        simpa [X, secondCase_linearEquation11_familyMap] using hXP
      have hback :
          (x.1.1.map (MulAut.conj (TConj x : G)).toMonoidHom).map
              (MulAut.conj ((TConj x : G)⁻¹)).toMonoidHom = x.1.1 := by
        rw [Subgroup.map_map]
        congr 1
        ext z
        simp [MulAut.conj_apply, mul_assoc]
      have hPback : post.od.P.map
          (MulAut.conj ((TConj x : G)⁻¹)).toMonoidHom = post.od.P :=
        hconjFixP ⟨(TConj x : G)⁻¹, d'.E.inv_mem (TConj x).2⟩
      calc
        x.1.1 =
            (x.1.1.map (MulAut.conj (TConj x : G)).toMonoidHom).map
              (MulAut.conj ((TConj x : G)⁻¹)).toMonoidHom := hback.symm
        _ = post.od.P.map
              (MulAut.conj ((TConj x : G)⁻¹)).toMonoidHom := by rw [hXP']
        _ = post.od.P := hPback
    have hPnotleX : ¬ post.od.P ≤ X x := by
      intro hle
      apply hXneP
      exact (Subgroup.eq_of_le_of_card_ge hle (by
        rw [post.od.P_card, hXcardX])).symm
    have hPX : post.od.P ⊓ X x = ⊥ := by
      have hi : X x ⊓ post.od.P = ⊥ :=
        inf_eq_bot_of_not_le_of_prime_card (X x) post.od.P
          (post.od.P_card ▸ post.od.hp_prime) hPnotleX
      simpa [inf_comm] using hi
    obtain ⟨ePE, heP, heE⟩ :=
      subgroup_sup_exists_prod_equiv_of_commute_of_disjoint
        post.od.P d'.E hPinterE hcommPE
    let π0 : (post.od.P ⊔ d'.E : Subgroup G) →* d'.E :=
      (MonoidHom.snd post.od.P d'.E).comp ePE.toMonoidHom
    let eE : d'.E ≃* PSL2 K :=
      ((QuotientGroup.quotientMulEquivOfEq (G := d'.E) hZ).trans
        (QuotientGroup.quotientBot (G := d'.E))).symm.trans (hdE ▸ e).some
    let π : (post.od.P ⊔ d'.E : Subgroup G) →* PSL2 K :=
      eE.toMonoidHom.comp π0
    have hπE : ∀ z : d'.E,
        π ⟨z, Subgroup.mem_sup_right z.2⟩ = eE z := by
      intro z
      change eE (ePE ⟨z, Subgroup.mem_sup_right z.2⟩).2 = eE z
      rw [congrArg Prod.snd (heE z)]
    have hπXinj : Function.Injective
        (π.comp (Subgroup.inclusion hXlePE)) := by
      have hπ0Xinj : Function.Injective
          (π0.comp (Subgroup.inclusion hXlePE)) :=
        second_projection_restriction_injective_of_disjoint
          post.od.P d'.E (X x) hXlePE ePE heP hPX
      intro a b hab
      apply hπ0Xinj
      apply eE.injective
      simpa [π] using hab
    have hWleE : ∀ W : Subgroup G,
        W ∈ MinimalXInvariantFamily (post.od.P ⊔ d'.E)
          (Nat.card K) (X x) → W ≤ d'.E := by
      intro W hW
      exact subgroup_le_second_factor_of_card_dvd_prime_power
        (P := post.od.P) (E := d'.E) (W := W)
        post.od.P_card hPinterE hcommPE hKcard hp_ne_r hW.1 hW.2.1
    let hCt : Subgroup G := conjugateSubgroup C (TConj x : G)
    have hPEinterN : (post.od.P ⊔ d'.E) ⊓
        Subgroup.normalizer (X x : Set G) = post.od.P ⊔ hCt := by
      simpa [hCt, hXeq] using (htr x).2.2.1
    have hPCt_inter : post.od.P ⊓ hCt = ⊥ := by
      apply le_bot_iff.mp
      intro z hz
      have hzP : z ∈ post.od.P := hz.1
      have hzCt : z ∈ hCt := hz.2
      rcases Subgroup.mem_map.mp hzCt with ⟨c0, hc0, hzEq⟩
      have hzE : z ∈ d'.E := by
        have hzEq' : z = (TConj x : G) * (c0 : G) * (TConj x : G)⁻¹ := by
          simpa [MulAut.conj_apply] using hzEq.symm
        rw [hzEq']
        exact d'.E.mul_mem (d'.E.mul_mem (TConj x).2 hc0.2)
          (d'.E.inv_mem (TConj x).2)
      have hzInf : z ∈ post.od.P ⊓ d'.E := ⟨hzP, hzE⟩
      have hbot : z ∈ (⊥ : Subgroup G) := by
        rwa [hPinterE] at hzInf
      exact Subgroup.mem_bot.mp hbot
    have hPCt_comm : ∀ a b : G, a ∈ post.od.P → b ∈ hCt → Commute a b := by
      intro a b ha hb
      rcases Subgroup.mem_map.mp hb with ⟨c0, hc0, hbEq⟩
      have hcE : (TConj x : G) * (c0 : G) * (TConj x : G)⁻¹ ∈ d'.E :=
        d'.E.mul_mem (d'.E.mul_mem (TConj x).2 hc0.2)
          (d'.E.inv_mem (TConj x).2)
      have hb' : b ∈ d'.E := by
        have hbEq' : b = (TConj x : G) * (c0 : G) * (TConj x)⁻¹ := by
          simpa [MulAut.conj_apply] using hbEq.symm
        rw [hbEq']
        exact hcE
      exact (Subgroup.mem_centralizer_iff.mp (hEcentP hb')) a ha
    have hWleCt : ∀ Wt : Subgroup G, Wt ≤ post.od.P ⊔ hCt →
        Nat.card Wt ∣ Nat.card K → Wt ≤ hCt := by
      intro Wt hWtle hWtcard
      exact subgroup_le_second_factor_of_card_dvd_prime_power
        (P := post.od.P) (E := hCt) (W := Wt)
        post.od.P_card hPCt_inter hPCt_comm hKcard hp_ne_r hWtle hWtcard
    have hCcard : Nat.card C = Nat.card post.torus.T := by
      calc
        Nat.card C = Nat.card (C.subgroupOf d'.E) := by
          rw [← Subgroup.card_map_of_injective d'.E.subtype_injective,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
        _ = Nat.card ((C.subgroupOf d'.E).map qbar) := by
          rw [Subgroup.card_map_of_injective hqinj]
        _ = Nat.card post.torus.T := by rw [hCmap]
    have hCtcop : Nat.Coprime (Nat.card hCt) (Nat.card K) := by
      change Nat.Coprime (Nat.card
        (C.map (MulAut.conj (TConj x : G)).toMonoidHom)) (Nat.card K)
      rw [Subgroup.card_map_of_injective (MulAut.conj (TConj x : G)).injective]
      rw [hCcard]
      exact hTcard_cop
    have hnotcent : ∀ W : Subgroup G,
        W ∈ MinimalXInvariantFamily (post.od.P ⊔ d'.E)
          (Nat.card K) (X x) →
        ¬ X x ≤ Subgroup.centralizer (W : Set G) := by
      intro W hW hXcent
      have hWne : W ≠ ⊥ := by
        have hWmin : MinimalXInvariant (X x) W := hW.2.2
        exact hWmin.1
      have hWleC : W ≤ Subgroup.centralizer (X x : Set G) :=
        (Subgroup.le_centralizer_iff).mpr hXcent
      have hWleN : W ≤ Subgroup.normalizer (X x : Set G) :=
        hWleC.trans (Subgroup.centralizer_le_normalizer (X x : Set G))
      have hWlePCt : W ≤ post.od.P ⊔ hCt := by
        intro z hz
        have hmem : z ∈ (post.od.P ⊔ d'.E) ⊓
            Subgroup.normalizer (X x : Set G) :=
          ⟨hW.1 hz, hWleN hz⟩
        rwa [hPEinterN] at hmem
      have hWleCt' : W ≤ hCt :=
        hWleCt W hWlePCt hW.2.1
      have hWdivCt : Nat.card W ∣ Nat.card hCt :=
        Subgroup.card_dvd_of_le hWleCt'
      have hWone : Nat.card W = 1 :=
        Nat.eq_one_of_dvd_coprimes hCtcop hWdivCt hW.2.1
      exact hWne (Subgroup.card_eq_one.mp hWone)
    exact secondCase_linear_minimalInvariant_root_count
      (post.od.P ⊔ d'.E) d'.E (X x) le_sup_right hpodd hqodd K
      hKcard rfl eE π hXlePE hπXinj hπE hXcardX hWleE hnotcent

  let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
  have hK0leK : post.od.K0 ≤ post.od.K := by
    rw [post.od.K0_eq]
    exact inf_le_right
  have hP0leE : post.od.P0 ≤ d'.E :=
    post.od.P0_le_K0.trans (hK0leK.trans post.od.K_le_E)
  have hP0comm : ∀ h : post.od.P, ∀ k : post.od.P0,
      (h : G) * (k : G) = (k : G) * (h : G) := by
    intro h k
    exact (Subgroup.mem_centralizer_iff.mp (hEcentP (hP0leE k.2))) h h.2
  have hP0interP : post.od.P ⊓ post.od.P0 = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hzPE : z ∈ post.od.P ⊓ d'.E := ⟨hz.1, hP0leE hz.2⟩
    rw [hPinterE] at hzPE
    exact Subgroup.mem_bot.mp hzPE
  have hNP : Subgroup.normalizer (post.od.P : Set G) = w'.M :=
    secondCase_linear_P_normalizer_eq_M c' w' d' post.od
  have hXcardX : ∀ x : Xs, Nat.card (X x) = post.od.p := by
    intro x
    rw [hXeq x]
    exact hXcard x
  have hXinj : Function.Injective X := by
    intro a b hab
    have hab' :
        secondCase_linearEquation11_familyMap (G := G) post.od.P post.od.P0 d'.E
            ⟨a.1, τ a.2⟩ =
          secondCase_linearEquation11_familyMap (G := G) post.od.P post.od.P0 d'.E
            ⟨b.1, τ b.2⟩ := by
      simpa [X] using hab
    have hpair : (a.1, τ a.2) = (b.1, τ b.2) :=
      secondCase_linearEquation11_familyMap_injective
        (G := G) (P := post.od.P) (P0 := post.od.P0) (E := d'.E)
        (p := post.od.p) post.od.P_card post.od.P0_card hP0interP hP0leE
        hPinterE hEcentP hP0comm hab'
    have hline : a.1 = b.1 := by
      exact congrArg (fun z : Lines × secondCase_toriOf G post.od.P0 d'.E => z.1) hpair
    have htorus : τ a.2 = τ b.2 := by
      exact congrArg (fun z : Lines × secondCase_toriOf G post.od.P0 d'.E => z.2) hpair
    exact Prod.ext hline (hτ htorus)
  let Bad : Xs → Subgroup G → Prop := fun x Y =>
    secondCase_linearEquation11_bad_pred (post.od.P ⊔ d'.E)
      (Nat.card K) (X x) Y
  let CoreAdm : Xs → Subgroup G → Prop := fun x Y =>
    Y ≤ Reg x ∧ Y ≠ X x ∧ ¬ Y ≤ w'.M ∧ ¬ Bad x Y
  let Adm : Xs → Subgroup G → Prop := fun x Y =>
    (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧ CoreAdm x Y
  let : Fintype Lines := Fintype.ofFinite Lines
  let : Fintype Xs := Fintype.ofFinite Xs
  let : DecidableEq Xs := Classical.decEq Xs
  have hRegP : ∀ x : Xs,
      conjugateSubgroup post.od.P (hreg x) = X x := by
    intro x
    change post.od.P.map
        (MulAut.conj ((TConj x : G) * BaseConj x.1)).toMonoidHom = X x
    rw [hXeq x]
    exact (htr x).1.symm
  have hRegPE : ∀ x : Xs,
      conjugateSubgroup (post.od.P ⊔ d'.E) (hreg x) = Reg x := by
    intro x
    change (post.od.P ⊔ d'.E).map
        (MulAut.conj ((TConj x : G) * BaseConj x.1)).toMonoidHom = Reg x
    rw [Subgroup.map_sup]
    have hPmap : post.od.P.map
        (MulAut.conj ((TConj x : G) * BaseConj x.1)).toMonoidHom = Xreg x := by
      exact (htr x).1.symm
    rw [hPmap]
    rfl
  have hBad : ∀ x : Xs,
      Nat.card {Y : Subgroup G //
        (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧
          Y ≤ Reg x ∧ Y ≠ X x ∧ ¬ Y ≤ w'.M ∧ Bad x Y} ≤
        ((Nat.card K - 1) / post.od.p) * Nat.card K := by
    intro x
    simpa [Bad] using
      (secondCase_linearEquation11_badFiber_count
        (c := c') (w := w') (P := post.od.P) (q := Nat.card K)
        (p := post.od.p) (hq := by
          exact secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv
            d' K post.equation9 post.od.hp_prime
            (secondCase_linear_omega_p_odd c' w' d' post.od)
            (secondCase_linear_p_dvd_Kinv c' w' d' post))
        (hPcard := post.od.P_card) (Xs := Xs) (X := X) (R := Reg)
        (PE := post.od.P ⊔ d'.E) hD_core_probe hW_probe hWcount x)
  let Lnat : ℕ :=
    (p1 - 1) * (Nat.card K * post.equation9.k' - 1) -
      ((Nat.card K - 1) / post.od.p) * Nat.card K
  have hLnat_eq : Lnat =
      ((p1 - 1) * Nat.card K * post.equation9.k' - (p1 - 1)) -
        ((Nat.card K - 1) / post.od.p) * Nat.card K := by
    dsimp [Lnat]
    rw [Nat.mul_sub_left_distrib]
    simp [Nat.mul_assoc]
  have hYs : ∀ x : Xs,
      Lnat ≤ Nat.card {Y : Subgroup G //
        (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧ Adm x Y} := by
    intro x
    have hgood : Lnat ≤ Nat.card {Y : Subgroup G //
        (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧
          CoreAdm x Y} := by
      let TotalSrc : Type u := {Y : Subgroup G //
        Y ≤ Reg x ∧ Y ≠ X x ∧
          (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom)}
      let TotalTgt : Type u := {Y : Subgroup G //
        (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧
          Y ≤ Reg x ∧ Y ≠ X x}
      have hTotalSrc : (p1 - 1) * Nat.card K * post.equation9.k' ≤
          Nat.card TotalSrc := by
        have ht := hTotal x
        change (p1 - 1) * Nat.card K * post.equation9.k' ≤
          Nat.card {Y : Subgroup G //
            Y ≤ conjugateSubgroup (post.od.P ⊔ d'.E) (hreg x) ∧
            Y ≠ conjugateSubgroup post.od.P (hreg x) ∧
            (∃ g : G, Y = conjugateSubgroup post.od.P g)} at ht
        rw [hRegPE x, hRegP x] at ht
        simpa [TotalSrc, conjugateSubgroup] using ht
      let eTotal : TotalSrc ≃ TotalTgt :=
        Equiv.subtypeEquiv (Equiv.refl (Subgroup G)) (by
          intro Y
          constructor
          · rintro ⟨hle, hne, hconj⟩
            exact ⟨hconj, hle, hne⟩
          · rintro ⟨hconj, hle, hne⟩
            exact ⟨hle, hne, hconj⟩)
      have hTotal' : (p1 - 1) * Nat.card K * post.equation9.k' ≤
          Nat.card TotalTgt := by
        calc
          (p1 - 1) * Nat.card K * post.equation9.k' ≤ Nat.card TotalSrc := hTotalSrc
          _ = Nat.card TotalTgt := Nat.card_congr eTotal
      have hg := secondCase_linearEquation11_goodFiber_count
        (P := post.od.P) (X := X x) (R := Reg x) (M := w'.M)
        (Bad := fun Y => Bad x Y)
        (a := (p1 - 1) * Nat.card K * post.equation9.k')
        (m := p1 - 1)
        (b := ((Nat.card K - 1) / post.od.p) * Nat.card K)
        hTotal' (hM x) (by simpa [Bad] using hBad x)
      rw [hLnat_eq]
      simpa [CoreAdm] using hg
    let Dup : Type u := {Y : Subgroup G //
      (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧ Adm x Y}
    let Single : Type u := {Y : Subgroup G //
      (∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom) ∧ CoreAdm x Y}
    let eGood : Dup ≃ Single :=
      Equiv.subtypeEquiv (Equiv.refl (Subgroup G)) (by
        intro Y
        constructor
        · rintro ⟨hconj, ⟨_hconj', hcore⟩⟩
          exact ⟨hconj, hcore⟩
        · rintro ⟨hconj, hcore⟩
          exact ⟨hconj, ⟨hconj, hcore⟩⟩)
    have hcard : Nat.card Dup = Nat.card Single := Nat.card_congr eGood
    change Lnat ≤ Nat.card Dup
    rw [hcard]
    exact hgood
  have huniq : ∀ {x₁ x₂ : Xs} {Y : Subgroup G},
      Adm x₁ Y → Adm x₂ Y → x₁ = x₂ := by
    intro x₁ x₂ Y h₁ h₂
    rcases h₁ with ⟨hYconj₁, hYle₁, hYne₁, hYnotM₁, hnotbad₁⟩
    rcases h₂ with ⟨hYconj₂, hYle₂, hYne₂, hYnotM₂, hnotbad₂⟩
    let D : Subgroup G :=
      Subgroup.centralizer (Y : Set G) ⊓ (post.od.P ⊔ d'.E)
    have hd₁ : X x₁ ≤ D ∧ ¬ post.od.p ∣
        ((X x₁).subgroupOf D).index ∧
        ∃ Q : Subgroup G, IsNormalIn Q D ∧
          D = Q ⊔ (D ⊓ Subgroup.normalizer (X x₁ : Set G)) ∧
          Q ⊓ (D ⊓ Subgroup.normalizer (X x₁ : Set G)) = ⊥ ∧
          Nat.card Q ∣ Nat.card K := by
      simpa [D] using hD_core_probe x₁ Y hYconj₁ hYle₁ hYnotM₁
    rcases hd₁ with ⟨hX₁leD, hidx₁, ⟨Q, hQnormal, hDQ, hQinter, hQcard⟩⟩
    have hQbot : Q = ⊥ := by
      by_contra hQne
      have hbad : Bad x₁ Y := by
        exact secondCase_linearEquation11_bad_pred_mk
          (post.od.P ⊔ d'.E) (Nat.card K) (X x₁) Y Q
          hQnormal hDQ hQinter hQcard hQne
      exact hnotbad₁ hbad
    have hDleN₁ : D ≤ Subgroup.normalizer (X x₁ : Set G) := by
      have hDeq : D = D ⊓ Subgroup.normalizer (X x₁ : Set G) := by
        simpa [hQbot] using hDQ
      rw [hDeq]
      exact inf_le_right
    have hd₂ : X x₂ ≤ D ∧ ¬ post.od.p ∣
        ((X x₂).subgroupOf D).index ∧
        ∃ Q : Subgroup G, IsNormalIn Q D ∧
          D = Q ⊔ (D ⊓ Subgroup.normalizer (X x₂ : Set G)) ∧
          Q ⊓ (D ⊓ Subgroup.normalizer (X x₂ : Set G)) = ⊥ ∧
          Nat.card Q ∣ Nat.card K := by
      simpa [D] using hD_core_probe x₂ Y hYconj₂ hYle₂ hYnotM₂
    rcases hd₂ with ⟨hX₂leD, hidx₂, _⟩
    have hXX : X x₁ = X x₂ :=
      secondCase_linear_eq_of_normal_sylow D (X x₁) (X x₂)
        hX₁leD hX₂leD (hXcardX x₁) (hXcardX x₂) hidx₁ hidx₂ hDleN₁
    exact hXinj hXX
  have hXsCard : Nat.card Xs = (p1 - 1) * Nat.card K * post.equation9.k' := by
    change Nat.card (Lines × Fin (Nat.card K * post.equation9.k')) = _
    rw [Nat.card_prod, hLines]
    simp [Nat.card_eq_fintype_card, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hregion := secondCase_linearEquation11_indexed_region_inequality
    (M := w'.M) (P := post.od.P) (Xs := Xs)
    (p := p1) (q := Nat.card K) (k' := post.equation9.k')
    (L := Lnat) hNP Adm hYs huniq (by
      rw [hXsCard])
  have hpdvd : post.od.p ∣ Nat.card post.equation9.Kinv :=
    secondCase_linear_p_dvd_Kinv c' w' d' post
  have hpodd : Odd post.od.p :=
    secondCase_linear_omega_p_odd c' w' d' post.od
  have hqseven : 7 ≤ Nat.card K :=
    secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv
      d' K post.equation9 post.od.hp_prime hpodd hpdvd
  have hp0 : 3 ≤ post.indices.p0 :=
    secondCase_linear_p0_ge_three hmin c' w' d' K post
  have hp3 : 3 ≤ post.od.p := by omega
  have ha2 : 2 ≤ p1 - 1 := by omega
  have hk'lower : (Nat.card K - 1) / 2 ≤ post.equation9.k' := by
    rcases post.equation9.k'_is_half with h | h
    · rw [h]
      exact Nat.div_le_div_right (by omega)
    · rw [h]
  have h11 : ((p1 : ℚ) - 1) * (Nat.card K : ℚ) *
      (post.equation9.k' : ℚ) *
        (((p1 : ℚ) - 1) *
          ((Nat.card K : ℚ) * (post.equation9.k' : ℚ) - 1) -
          ((Nat.card K : ℚ) - 1) / (post.od.p : ℚ) *
            (Nat.card K : ℚ)) ≤ (w'.M.index : ℚ) := by
    have hcast : ((p1 - 1) * Nat.card K * post.equation9.k' * Lnat : ℕ) ≤
        w'.M.index := hregion
    have hLcast :
        ((p1 : ℚ) - 1) *
          ((Nat.card K : ℚ) * (post.equation9.k' : ℚ) - 1) -
          ((Nat.card K : ℚ) - 1) / (post.od.p : ℚ) *
            (Nat.card K : ℚ) ≤ (Lnat : ℚ) := by
      have hsub : (Nat.card K - 1) / post.od.p * Nat.card K ≤
          (p1 - 1) * (Nat.card K * post.equation9.k' - 1) := by
        have hr : (Nat.card K - 1) / post.od.p ≤
            (Nat.card K - 1) / 3 :=
          Nat.div_le_div_left hp3 (by omega)
        have hrq : (Nat.card K - 1) / post.od.p * Nat.card K ≤
            (Nat.card K - 1) / 3 * Nat.card K :=
          Nat.mul_le_mul_right (Nat.card K) hr
        have hes : (Nat.card K - 1) / 3 ≤
            (Nat.card K - 1) / 2 :=
          Nat.div_le_div_left (by omega) (by omega)
        have heq : (Nat.card K - 1) / 3 * Nat.card K ≤
            (Nat.card K - 1) / 2 * Nat.card K :=
          Nat.mul_le_mul_right (Nat.card K) hes
        have hs : 3 ≤ (Nat.card K - 1) / 2 := by
          apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
          omega
        have hmulq : Nat.card K ≤
            Nat.card K * ((Nat.card K - 1) / 2) := by
          have hone : 1 ≤ (Nat.card K - 1) / 2 := by omega
          simpa using Nat.mul_le_mul_left (Nat.card K) hone
        have hsq : 2 ≤ Nat.card K * ((Nat.card K - 1) / 2) - 1 := by
          omega
        have hsq' : (Nat.card K - 1) / 2 * Nat.card K ≤
            2 * (Nat.card K * ((Nat.card K - 1) / 2) - 1) := by
          rw [Nat.mul_comm]
          omega
        have hhalf : (Nat.card K - 1) / 3 * Nat.card K ≤
            2 * (Nat.card K * ((Nat.card K - 1) / 2) - 1) :=
          heq.trans (by simpa [Nat.mul_comm] using hsq')
        have hmul : Nat.card K * ((Nat.card K - 1) / 2) ≤
            Nat.card K * post.equation9.k' :=
          Nat.mul_le_mul_left (Nat.card K) hk'lower
        have hhalfprod :
            2 * (Nat.card K * ((Nat.card K - 1) / 2) - 1) ≤
              2 * (Nat.card K * post.equation9.k' - 1) := by
          omega
        have hprod : 2 * (Nat.card K * post.equation9.k' - 1) ≤
            (p1 - 1) * (Nat.card K * post.equation9.k' - 1) := by
          exact Nat.mul_le_mul_right
            (Nat.card K * post.equation9.k' - 1) ha2
        exact hrq.trans (hhalf.trans (hhalfprod.trans hprod))
      have hdiv : (((Nat.card K - 1) / post.od.p : ℕ) : ℚ) ≤
          ((Nat.card K : ℚ) - 1) / (post.od.p : ℚ) := by
        have h := (Nat.cast_div_le (α := ℚ)
          (m := Nat.card K - 1) (n := post.od.p))
        rw [Nat.cast_sub (by omega : 1 ≤ Nat.card K)] at h
        exact h
      have hC : (((Nat.card K - 1) / post.od.p * Nat.card K : ℕ) : ℚ) ≤
          ((Nat.card K : ℚ) - 1) / (post.od.p : ℚ) *
            (Nat.card K : ℚ) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_right hdiv (by positivity)
      have hp1pos : 1 ≤ p1 := by omega
      have hqkp : 1 ≤ Nat.card K * post.equation9.k' := by
        have hone : 1 ≤ post.equation9.k' := by omega
        exact le_trans (by omega)
          (Nat.mul_le_mul_left (Nat.card K) hone)
      dsimp [Lnat]
      rw [Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_sub hp1pos,
        Nat.cast_sub hqkp, Nat.cast_mul]
      exact sub_le_sub_left hC _
    have hmul :
        (((p1 : ℚ) - 1) * (Nat.card K : ℚ) *
          (post.equation9.k' : ℚ)) *
          (((p1 : ℚ) - 1) *
            ((Nat.card K : ℚ) * (post.equation9.k' : ℚ) - 1) -
            ((Nat.card K : ℚ) - 1) / (post.od.p : ℚ) *
              (Nat.card K : ℚ)) ≤
        (((p1 : ℚ) - 1) * (Nat.card K : ℚ) *
          (post.equation9.k' : ℚ)) * (Lnat : ℚ) := by
      have hp1q : (0 : ℚ) ≤ (p1 : ℚ) - 1 := by
        have hp1 : 1 ≤ p1 := by omega
        exact sub_nonneg.mpr (by exact_mod_cast hp1)
      exact mul_le_mul_of_nonneg_left hLcast
        (mul_nonneg (mul_nonneg hp1q (by positivity)) (by positivity))
    have hcast' :
        (((p1 - 1) * Nat.card K * post.equation9.k' * Lnat : ℕ) : ℚ) ≤
          (w'.M.index : ℚ) := by
      exact_mod_cast hcast
    have hcast'' :
        (((p1 : ℚ) - 1) * (Nat.card K : ℚ) *
          (post.equation9.k' : ℚ)) * (Lnat : ℚ) ≤
          (w'.M.index : ℚ) := by
      simpa [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p1)] using hcast'
    exact hmul.trans hcast''
  exact secondCase_linearContradictionData_of_postNine_rational
    c' w' d' K post hp0 hp01 hp0p h11 hpdvd

end CFSG.GorensteinWalter
