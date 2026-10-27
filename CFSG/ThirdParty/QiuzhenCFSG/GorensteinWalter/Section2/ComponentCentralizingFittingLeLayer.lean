module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectNormalLinearModelSimple
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleOfCentralExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

namespace CFSG
end CFSG
open CFSG

/-!
# Absorption of a component centralizing the Fitting subgroup

This is the specialized Bender 1.7(v) core needed by Gorenstein--Walter
Lemma 2.5.  For a finite `D`-group `B`, a component of another subgroup that
is contained in `B` and centralizes `F(B)` lies in the layer `E(B)`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- A component contained in a finite `D`-group and centralizing its Fitting
subgroup is absorbed by the `D`-group's component layer. -/
public theorem component_le_componentLayerOf_of_isDGroup_of_centralizes_fitting
    {G : Type u} [Group G] [Finite G]
    (A B K : Subgroup G)
    (hD : IsDGroup B)
    (hK : IsComponentOf K A)
    (hKB : K ≤ B)
    (hKF : ⁅K, fittingSubgroupOf B⁆ = ⊥) :
    K ≤ componentLayerOf B := by
  classical
  let Ki : Subgroup B := K.subgroupOf B
  let eKi : Ki ≃* K := Subgroup.subgroupOfEquivOfLe hKB
  have hKne : K ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot K).mp hK.2.2.1
  have hKine : Ki ≠ ⊥ := by
    intro hbot
    apply hKne
    have hmap : Ki.map B.subtype = K :=
      Subgroup.map_subgroupOf_eq_of_le hKB
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hKiperf : Group.IsPerfect Ki := by
    let : Group.IsPerfect K := (Group.isPerfect_def).2 hK.2.2.2.1
    exact Group.IsPerfect.ofSurjective
      (f := eKi.symm.toMonoidHom) eKi.symm.surjective
  let : Group.IsPerfect Ki := hKiperf
  have hKcG : K ≤ Subgroup.centralizer (fittingSubgroupOf B : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hKF
  have hKiC : Ki ≤ Subgroup.centralizer (fittingSubgroup B : Set B) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    have hyF : (y : G) ∈ fittingSubgroupOf B :=
      Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hKcG hxK) (y : G) hyF
  let N : Subgroup B := Subgroup.normalClosure (Ki : Set B)
  have hKiN : Ki ≤ N := Subgroup.le_normalClosure
  have hNnormal : N.Normal := Subgroup.normalClosure_normal
  let : N.Normal := hNnormal
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hKine
    exact le_bot_iff.mp (hKiN.trans (le_of_eq hbot))
  have hNperf : Group.IsPerfect N := by
    apply Subgroup.isPerfect_iff.mpr
    apply le_antisymm
    · exact Subgroup.commutator_le_left (H₁ := N) (H₂ := N)
    · apply Subgroup.normalClosure_le_normal
      intro x hx
      have hx' : x ∈ ⁅Ki, Ki⁆ := by
        rw [Subgroup.commutator_eq_self]
        exact hx
      exact Subgroup.commutator_mono hKiN hKiN hx'
  let : Group.IsPerfect N := hNperf
  have : (fittingSubgroup B).Normal := fittingSubgroup_normal
  have hNCF : N ≤ Subgroup.centralizer (fittingSubgroup B : Set B) := by
    exact Subgroup.normalClosure_le_normal hKiC
  let O : Subgroup B := pPrimeCore 2 B
  let : O.Normal := by
    dsimp [O]
    infer_instance
  have hOodd : Odd (Nat.card O) := by
    have hOcop : Nat.Coprime 2 (Nat.card O) := by
      simpa [O] using pPrimeCore_coprime_card (p := 2) (G := B)
    exact Nat.coprime_two_left.mp hOcop
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  let FO : Subgroup B := fittingSubgroupOf O
  have hFOnormal : FO.Normal := by
    dsimp [FO]
    exact fittingSubgroupOf_normal O (inferInstance : O.Normal)
  have hFOnil : Group.IsNilpotent FO := by
    dsimp [FO]
    exact fittingSubgroupOf_isNilpotent O
  have hFOF : FO ≤ fittingSubgroup B :=
    le_sSup ⟨hFOnormal, hFOnil⟩
  have hNCFO : N ≤ Subgroup.centralizer (FO : Set B) :=
    hNCF.trans (Subgroup.centralizer_le hFOF)
  have hNOFO : N ⊓ O ≤ FO := by
    have hle : N ⊓ O ≤ O ⊓ Subgroup.centralizer (FO : Set B) :=
      le_inf inf_le_right (inf_le_left.trans hNCFO)
    have hfact : O ⊓ Subgroup.centralizer (FO : Set B) ≤ FO := by
      simpa [FO] using
        (fact_1_2_centralizer_fitting_le_fitting O hOsolv)
    exact hle.trans hfact
  let q : B →* B ⧸ O := QuotientGroup.mk' O
  let S : Subgroup (B ⧸ O) := N.map q
  let f : N →* S :=
    (q.comp N.subtype).codRestrict S (fun x =>
      Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  have hSnormal : S.Normal := by
    dsimp [S]
    exact hNnormal.map q (QuotientGroup.mk'_surjective O)
  have hSperf : Group.IsPerfect S := by
    dsimp [S]
    exact Group.IsPerfect.map q
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hNleO : N ≤ O := by
      have hker : N ≤ q.ker := (Subgroup.map_eq_bot_iff N).mp hbot
      simpa [q, QuotientGroup.ker_mk'] using hker
    let NO : Subgroup O := N.subgroupOf O
    let : Group.IsSolvable O := hOsolv
    have : Group.IsSolvable NO := inferInstance
    let eNO : NO ≃* N := Subgroup.subgroupOfEquivOfLe hNleO
    have hNsolv : Group.IsSolvable N :=
      Group.isSolvable_of_surjective (f := eNO.toMonoidHom) eNO.surjective
    let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hNne
    exact Group.IsPerfect.not_isSolvable N hNsolv
  have hSsimple : IsSimpleGroup S := by
    rcases hD with ⟨_hSylow, hQ⟩ | ⟨_hSylow, hA7⟩ |
        ⟨_hSylow, LField, hLField, L, hLnormal, hLindex, hLmodel⟩
    · have hSp : IsPGroup 2 S := hQ.to_subgroup S
      let : Group.IsNilpotent S := hSp.isNilpotent
      have hSsolv : Group.IsSolvable S := inferInstance
      let : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hSne
      let : Group.IsPerfect S := hSperf
      exact False.elim (Group.IsPerfect.not_isSolvable S hSsolv)
    · rcases hA7 with ⟨eA7⟩
      have hA7simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by norm_num)
      have hQsimple : IsSimpleGroup (B ⧸ O) :=
        (MulEquiv.isSimpleGroup_congr eA7).mpr hA7simple
      have hStop : S = ⊤ :=
        ((haveI := hSnormal; hQsimple.eq_bot_or_eq_top_of_normal S)).resolve_left hSne
      let eS : S ≃* (B ⧸ O) :=
        (MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv
      exact (MulEquiv.isSimpleGroup_congr eS).mpr hQsimple
    · exact perfect_normal_subgroup_isSimple_of_linear_model
        S L hSnormal hSne hSperf hLnormal hLindex
        LField hLField hLmodel
  have hker_center : f.ker ≤ Subgroup.center N := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hfx : f x = 1 := MonoidHom.mem_ker.mp hx
    have hxq : q (x : B) = 1 := congrArg Subtype.val hfx
    have hxO : (x : B) ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) (x := (x : B))).mp hxq
    have hxFO : (x : B) ∈ FO := hNOFO ⟨x.2, hxO⟩
    have hyC : (y : B) ∈ Subgroup.centralizer (fittingSubgroup B : Set B) :=
      hNCF y.2
    exact (Subgroup.mem_centralizer_iff.mp hyC (x : B) (hFOF hxFO)).symm
  have hNq : IsQuasisimple N :=
    isQuasisimple_of_perfect_of_ker_le_center_of_surjective_simple
      f hf ((Subgroup.nontrivial_iff_ne_bot N).2 hNne) hNperf
      hSsimple hker_center
  have hNcompTop : IsComponentOf N (⊤ : Subgroup B) :=
    ⟨le_top, hNnormal.isSubnormal.subgroupOf, hNq⟩
  let Nm : Subgroup G := N.map B.subtype
  have hNmcomp : IsComponentOf Nm B := by
    refine ⟨Subgroup.map_subtype_le N, ?_, ?_⟩
    · have hNsub : N.IsSubnormal := by
        have hmap : ((N.subgroupOf (⊤ : Subgroup B)).map
            (⊤ : Subgroup B).subtype).IsSubnormal :=
          hNcompTop.2.1.map (f := (⊤ : Subgroup B).subtype)
            (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
        rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : N ≤ (⊤ : Subgroup B))]
          at hmap
      have hEq : Nm.subgroupOf B = N := by
        apply le_antisymm
        · intro y hy
          rw [Subgroup.mem_subgroupOf] at hy
          rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
          have hyx : x = y := B.subtype_injective (by simpa using hxy)
          simpa [hyx] using hx
        · intro y hy
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      simpa [hEq] using hNsub
    · let eNm : N ≃* Nm :=
        Subgroup.equivMapOfInjective N B.subtype B.subtype_injective
      have hNontriv : Nontrivial Nm := by
        let : Nontrivial N := hNq.1
        exact eNm.toEquiv.injective.nontrivial
      have hPerf : Group.IsPerfect Nm := by
        let : Group.IsPerfect N := (Group.isPerfect_def).2 hNq.2.1
        exact Group.IsPerfect.ofSurjective
          (f := eNm.toMonoidHom) eNm.surjective
      have hcenter : (Subgroup.center N).map eNm.toMonoidHom =
          Subgroup.center Nm := by
        apply le_antisymm
        · intro x hx
          rcases hx with ⟨y, hy, rfl⟩
          exact (Subgroup.centerCongr eNm ⟨y, hy⟩).2
        · intro x hx
          refine ⟨eNm.symm x, ?_, ?_⟩
          · exact ((Subgroup.centerCongr eNm).symm ⟨x, hx⟩).2
          · exact eNm.apply_symm_apply x
      have hSimple : IsSimpleGroup (Nm ⧸ Subgroup.center Nm) :=
        (MulEquiv.isSimpleGroup_congr
          (QuotientGroup.congr (Subgroup.center N) (Subgroup.center Nm)
            eNm hcenter)).mp hNq.2.2
      exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩
  have hKleNm : K ≤ Nm := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hKB hx⟩, hKiN (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  exact hKleNm.trans
    (le_sSup (s := {E : Subgroup G | IsComponentOf E B}) hNmcomp)

end CFSG.GorensteinWalter
