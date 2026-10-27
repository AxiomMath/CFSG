module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.RankThree.PartTwo.Sec4.T444.Lift
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofCompOne
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec16.Item16Res9ProofA10Seven
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof167End

theorem false_of_pCore_le_theta {Y₀ J : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) (hYJ : Y₀ ≤ J)
    (hθ : inSubgroup (CFSG.pCore 2) Y₀ ≤ inSubgroup (aschbacherSolvableCore 3) J)
    (hc : ⁅aschbacherSolvableCore 3 ↥J, (⊤ : Subgroup ↥J)⁆ ≤ CFSG.oddCore ↥J) : False := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀
  let θJ : Subgroup ↥J := aschbacherSolvableCore 3 ↥J
  let OJ : Subgroup ↥J := CFSG.oddCore ↥J
  let inc : ↥Y₀ →* ↥J := Subgroup.inclusion hYJ
  let W : Subgroup ↥Y₀ := OJ.comap inc
  have hθ' : Q.map Y₀.subtype ≤ θJ.map J.subtype := by
    simpa [Q, θJ, inSubgroup] using hθ
  have hQJθ : Q.map inc ≤ θJ := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := J.subtype) J.subtype_injective]
    rw [Subgroup.map_map]
    have hcomp : J.subtype.comp inc = Y₀.subtype := rfl
    rw [hcomp]
    exact hθ'
  have hc' : ⁅θJ, (⊤ : Subgroup ↥J)⁆ ≤ OJ := by
    simpa [θJ, OJ] using hc
  have hcommMap : (⁅Q, (⊤ : Subgroup ↥Y₀)⁆).map inc ≤ OJ := by
    rw [Subgroup.map_commutator]
    exact (Subgroup.commutator_mono hQJθ le_top).trans hc'
  have hcommW : ⁅Q, (⊤ : Subgroup ↥Y₀)⁆ ≤ W := by
    simpa [W] using (Subgroup.map_le_iff_le_comap.mp hcommMap)
  have hWodd : Odd (Nat.card W) := by
    have hmap : W.map inc ≤ OJ := by
      simpa [W] using (Subgroup.map_comap_le (f := inc) (H := OJ))
    rw [← Subgroup.card_map_of_injective (f := inc) (K := W)
      (Subgroup.inclusion_injective hYJ)]
    exact Odd.of_dvd_nat (CFSG.ABGLocalTools.odd_card_oddCore (H := ↥J))
      (Subgroup.card_dvd_of_le hmap)
  have hWQ : W ⊓ Q = ⊥ := by
    have hQ2 : IsPGroup 2 Q := by
      simpa [Q] using (CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀))
    have hcop : Nat.Coprime (Nat.card W) (Nat.card Q) := by
      obtain ⟨k, hk⟩ := hQ2.exists_card_eq
      rw [hk]
      exact (Nat.coprime_two_left.mpr hWodd).symm.pow_right k
    exact Subgroup.inf_eq_bot_of_coprime hcop
  have hWQcomm : ⁅W, Q⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_of_disjoint (disjoint_iff.mpr hWQ)
  have hWcent : W ≤ Subgroup.centralizer (Q : Set ↥Y₀) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWQcomm
  have hcent : Subgroup.centralizer (Q : Set ↥Y₀) ≤ Q := by
    have h := CFSG.centralizer_generalizedFitting_le (G := ↥Y₀)
    simpa [Q, hF] using h
  have hWbot : W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxQ : x ∈ Q := hcent (hWcent hx)
    have hxinf : x ∈ W ⊓ Q := ⟨hx, hxQ⟩
    rwa [hWQ, Subgroup.mem_bot] at hxinf
  have hQcommTop : ⁅Q, (⊤ : Subgroup ↥Y₀)⁆ = ⊥ := by
    rw [hWbot] at hcommW
    exact le_bot_iff.mp hcommW
  have hQcenter : Q ≤ Subgroup.center ↥Y₀ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hQcommTop
  have hYcent : (⊤ : Subgroup ↥Y₀) ≤ Subgroup.centralizer (Q : Set ↥Y₀) := by
    intro y _
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_center_iff.mp (hQcenter hq) y).symm
  have hYQ : (⊤ : Subgroup ↥Y₀) ≤ Q := hYcent.trans hcent
  have hQtop : Q = ⊤ := eq_top_iff.mpr hYQ
  have hsub : Subsingleton (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := by
    have hQtop' : CFSG.pCore 2 ↥Y₀ = ⊤ := by simpa [Q] using hQtop
    rw [hQtop']
    exact QuotientGroup.subsingleton_quotient_top
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact hab (Subsingleton.elim (a * b) (b * a))

theorem pCore_le_theta_of_eq_sup {Y₀ J : Subgroup G} (hYJ : Y₀ ≤ J)
    (hJs : IsSimpleGroup (↥J ⧸ aschbacherSolvableCore 3 ↥J)) (hJp : Group.IsPerfect ↥J)
    (hJ : J = Y₀ ⊔ inSubgroup (aschbacherSolvableCore 3) J) :
    inSubgroup (CFSG.pCore 2) Y₀ ≤ inSubgroup (aschbacherSolvableCore 3) J := by
  classical
  let θ : Subgroup ↥J := aschbacherSolvableCore 3 ↥J
  let π : ↥J →* ↥J ⧸ θ := QuotientGroup.mk' θ
  let inc : ↥Y₀ →* ↥J := Subgroup.inclusion hYJ
  let φ : ↥Y₀ →* ↥J ⧸ θ := π.comp inc
  let Q : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀
  let P : Subgroup (↥J ⧸ θ) := Q.map φ
  have hYJsup : Y₀.subgroupOf J ⊔ θ = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYJ, Subgroup.map_top,
      Subgroup.range_subtype]
    change Y₀ ⊔ inSubgroup (aschbacherSolvableCore 3) J = J
    exact hJ.symm
  have hYJmapTop : (Y₀.subgroupOf J).map π = ⊤ := by
    have h1 : (Y₀.subgroupOf J ⊔ θ).map π = ⊤ := by
      rw [hYJsup]
      exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective θ)
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
  have hφrange : φ.range = (Y₀.subgroupOf J).map π := by
    rw [show φ = π.comp inc from rfl, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, hφrange, hYJmapTop]
  have hPnormal : P.Normal := by
    have hbase : (Q.map φ).Normal :=
      (inferInstance : Q.Normal).map φ hφsurj
    simpa [P] using hbase
  have hP2 : IsPGroup 2 P := by
    have hQ2 : IsPGroup 2 Q := by
      simpa [Q] using (CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀))
    have hbase : IsPGroup 2 (Q.map φ) := IsPGroup.map (p := 2) hQ2 φ
    simpa [P] using hbase
  haveI : P.Normal := hPnormal
  haveI : IsSimpleGroup (↥J ⧸ θ) := hJs
  haveI : Group.IsPerfect ↥J := hJp
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hPbot | hPtop
  · have hPbot' : Q.map φ = ⊥ := by
      simpa [P] using hPbot
    have hQker : Q ≤ φ.ker := (Subgroup.map_eq_bot_iff (H := Q) (f := φ)).mp hPbot'
    intro x hx
    change x ∈ (CFSG.pCore 2 ↥Y₀).map Y₀.subtype at hx
    change x ∈ (aschbacherSolvableCore 3 ↥J).map J.subtype
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    have hφq : φ q = 1 := MonoidHom.mem_ker.mp (hQker hq)
    have hincθ : inc q ∈ θ := by
      rw [← QuotientGroup.eq_one_iff]
      simpa [φ, π] using hφq
    exact Subgroup.mem_map.mpr ⟨inc q, hincθ, rfl⟩
  · exfalso
    have hPtop' : IsPGroup 2 (⊤ : Subgroup (↥J ⧸ θ)) := hPtop ▸ hP2
    have hH2 : IsPGroup 2 (↥J ⧸ θ) :=
      hPtop'.of_equiv (Subgroup.topEquiv (G := ↥J ⧸ θ))
    have hperf : Group.IsPerfect (↥J ⧸ θ) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' θ)
        (QuotientGroup.mk'_surjective θ)
    haveI : Group.IsPerfect (↥J ⧸ θ) := hperf
    have hnil : Group.IsNilpotent (↥J ⧸ θ) := hH2.isNilpotent
    exact (Group.IsPerfect.not_isNilpotent (↥J ⧸ θ)) hnil

theorem eq_sup_theta_of_img148_eq {A N L Y₀ J : Subgroup G} [(Sec14.ker148 A N).Normal]
    (hAN : A ≤ N) (hJ : J ∈ thetaComponentsIn N) (h3 : 3 ∣ Nat.card J) (hLY : L ≤ Y₀) (hYJ : Y₀ ≤ J)
    (heq : Sec14.img148 A N L = Sec14.img148 A N J) :
    J = Y₀ ⊔ inSubgroup (aschbacherSolvableCore 3) J := by
  have hJN : J ≤ N := le_of_mem_thetaComponentsIn hJ
  have hLJ : L ≤ J := hLY.trans hYJ
  have hXM : J ≤ N ⊔ A := by
    rw [sup_eq_left.mpr hAN]
    exact hJN
  have hEq :=
    CFSG.RankThree.PartTwo.Sec14.Desc143X.eq_sup_theta_of_img148_eq
      (A := A) (Y := N) (X := J) (T := L) hJ h3 hXM hLJ heq
  apply le_antisymm
  · calc
      J = L ⊔ inSubgroup (aschbacherSolvableCore 3) J := hEq
      _ ≤ Y₀ ⊔ inSubgroup (aschbacherSolvableCore 3) J :=
        sup_le (hLY.trans le_sup_left) le_sup_right
  · exact sup_le hYJ (Subgroup.map_subtype_le _)

theorem pCore_le_theta_of_alt {A N L Y₀ J : Subgroup G} [(Sec14.ker148 A N).Normal]
    (hAN : A ≤ N) (hJ : J ∈ thetaComponentsIn N) (h3 : 3 ∣ Nat.card J) (hLY : L ≤ Y₀) (hYJ : Y₀ ≤ J)
    (h7 : Nonempty (↥(Sec14.img148 A N L) ≃* alternatingGroup (Fin 7)))
    (h10 : Nonempty (↥(Sec14.img148 A N J) ≃* alternatingGroup (Fin 10))) :
    inSubgroup (CFSG.pCore 2) Y₀ ≤ inSubgroup (aschbacherSolvableCore 3) J := by
  classical
  let QG : Subgroup G := inSubgroup (CFSG.pCore 2) Y₀
  let X : Subgroup (↥(N ⊔ A) ⧸ Sec14.ker148 A N) := Sec14.img148 A N J
  let K : Subgroup ↥X := (Sec14.img148 A N L).subgroupOf X
  let T : Subgroup ↥X := (Sec14.img148 A N QG).subgroupOf X
  have hJN : J ≤ N := le_of_mem_thetaComponentsIn hJ
  have hQY : QG ≤ Y₀ := Subgroup.map_subtype_le _
  have hQJ : QG ≤ J := hQY.trans hYJ
  have hLJ : L ≤ J := hLY.trans hYJ
  have hKle : Sec14.img148 A N L ≤ X := Sec14.img148_mono hLJ
  have hTle : Sec14.img148 A N QG ≤ X := Sec14.img148_mono hQJ
  have hQ2 : IsPGroup 2 (Sec14.img148 A N QG) := by
    have hQG2 : IsPGroup 2 QG :=
      IsPGroup.map (p := 2) (CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀)) Y₀.subtype
    have hsub : IsPGroup 2 (QG.subgroupOf (N ⊔ A)) :=
      hQG2.comap_of_injective (N ⊔ A).subtype (N ⊔ A).subtype_injective
    exact hsub.map (QuotientGroup.mk' (Sec14.ker148 A N))
  have hLQ : L ≤ Subgroup.normalizer (QG : Set G) :=
    hLY.trans (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 Y₀)
  have hKT : K ≤ Subgroup.normalizer (T : Set ↥X) := by
    have hImgNorm : Sec14.img148 A N L ≤
        Subgroup.normalizer (Sec14.img148 A N QG : Set _) :=
      Sec14.img148_le_normalizer hLQ
    rw [← Subgroup.subgroupOf_normalizer_eq hTle]
    intro k hk
    exact Subgroup.mem_subgroupOf.mpr (hImgNorm (Subgroup.mem_subgroupOf.mp hk))
  obtain ⟨φ⟩ := h10
  have hK : Nonempty (K ≃* alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := h7
    exact ⟨(Subgroup.subgroupOfEquivOfLe hKle).trans e⟩
  have hT : IsPGroup 2 T :=
    hQ2.comap_of_injective X.subtype X.subtype_injective
  have hTbot : T = ⊥ :=
    CFSG.RankThree.PartTwo.Sec16.Res9A10.eq_bot_of_le_normalizer_of_mulEquiv φ hK hT hKT
  have hTimgBot : Sec14.img148 A N QG = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzX : z ∈ X := hTle hz
    have hzT : (⟨z, hzX⟩ : ↥X) ∈ T := hz
    rw [hTbot, Subgroup.mem_bot] at hzT
    exact congrArg Subtype.val hzT
  have hQGcore : QG ≤ pPrimeCoreOf 3 N := by
    intro x hx
    have hxJ : x ∈ J := hQJ hx
    have hxN : x ∈ N := hJN hxJ
    have hxNA : x ∈ N ⊔ A := by
      rw [sup_eq_left.mpr hAN]
      exact hxN
    have hxQimg : QuotientGroup.mk' (Sec14.ker148 A N) ⟨x, hxNA⟩ ∈
        Sec14.img148 A N QG :=
      Sec14.mem_img148_iff.mpr ⟨x, hxNA, hx, rfl⟩
    have hxX : QuotientGroup.mk' (Sec14.ker148 A N) ⟨x, hxNA⟩ ∈ X := hTle hxQimg
    have hxT : (⟨_, hxX⟩ : ↥X) ∈ T := hxQimg
    rw [hTbot, Subgroup.mem_bot] at hxT
    have h1 : QuotientGroup.mk' (Sec14.ker148 A N) ⟨x, hxNA⟩ = 1 :=
      congrArg Subtype.val hxT
    exact (Sec14.mk'_ker148_eq_one_iff (A := A) (Y := N)).mp h1
  let QN : Subgroup ↥N := QG.subgroupOf N
  let JN : Subgroup ↥N := J.subgroupOf N
  have hQN : QG ≤ N := hQJ.trans hJN
  have hQNJN : QN ≤ JN := Subgroup.subgroupOf_mono N hQJ
  have hQNcore : QN ≤ CFSG.pPrimeCore 3 ↥N := by
    intro x hx
    have hxQ : (x : G) ∈ QG := Subgroup.mem_subgroupOf.mp hx
    have hxG : (x : G) ∈ pPrimeCoreOf 3 N := hQGcore hxQ
    exact (Subgroup.mem_map_iff_mem N.subtype_injective).mp
      (by simpa [pPrimeCoreOf] using hxG)
  have hJ' : JN ∈ thetaComponents 3 N := (mem_thetaComponentsIn_iff.mp hJ).2
  have h3N : 3 ∣ Nat.card JN := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv]
    exact h3
  have hθeqN : JN ⊓ CFSG.pPrimeCore 3 ↥N =
      inSubgroup (aschbacherSolvableCore 3) JN :=
    Sec4.inf_pPrimeCore_eq_of_mem_thetaComponents hJ' h3N
  have hQNθ : QN ≤ inSubgroup (aschbacherSolvableCore 3) JN := by
    rw [← hθeqN]
    exact le_inf hQNJN hQNcore
  have hmapQN : QN.map N.subtype = QG := Subgroup.map_subgroupOf_eq_of_le hQN
  have hmapθ : (inSubgroup (aschbacherSolvableCore 3) JN).map N.subtype =
      inSubgroup (aschbacherSolvableCore 3) J := by
    let e : JN ≃* J := Subgroup.subgroupOfEquivOfLe hJN
    have hθe : (aschbacherSolvableCore 3 JN).map e.toMonoidHom =
        aschbacherSolvableCore 3 J :=
      CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
    have hcomp : J.subtype.comp e.toMonoidHom = N.subtype.comp JN.subtype := by
      ext x
      rfl
    calc
      (inSubgroup (aschbacherSolvableCore 3) JN).map N.subtype
          = ((aschbacherSolvableCore 3 JN).map JN.subtype).map N.subtype := rfl
      _ = (aschbacherSolvableCore 3 JN).map (N.subtype.comp JN.subtype) := by
          rw [Subgroup.map_map]
      _ = (aschbacherSolvableCore 3 JN).map (J.subtype.comp e.toMonoidHom) := by
          rw [hcomp]
      _ = ((aschbacherSolvableCore 3 JN).map e.toMonoidHom).map J.subtype := by
          rw [Subgroup.map_map]
      _ = (aschbacherSolvableCore 3 J).map J.subtype := by rw [hθe]
      _ = inSubgroup (aschbacherSolvableCore 3) J := rfl
  have hmap := Subgroup.map_mono (f := N.subtype) hQNθ
  rwa [hmapQN, hmapθ] at hmap

end Proof167End

end CFSG.RankThree.PartTwo.Sec16
