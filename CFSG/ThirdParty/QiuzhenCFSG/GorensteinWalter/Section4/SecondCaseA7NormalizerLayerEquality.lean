module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7ComponentLeNormalizerLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AmbientModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectImageNormalOddIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CommutatorCentralDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerPerfect
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Equality of controlled normalizer layers in the A7 branch

The forward containment comes from Lemma 2.7.  For the reverse containment,
classify the proper normalizer as a D-group.  Its quotient cannot be a
2-group or a linear group because it contains a nontrivial perfect A7 image.
In the A7 quotient case that image is the whole quotient, and perfectness
removes the odd kernel from the component layer.
-/

noncomputable section

open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- Every nontrivial subgroup of the equation-(4) fixed part has normalizer
with component layer exactly the selected A7 component. -/
public theorem secondCase_a7_normalizer_layer_eq_component
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (F X : Subgroup G)
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hXne : X ≠ ⊥) (hXleF : X ≤ F) :
    componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E := by
  classical
  let E : Subgroup G := d.E
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let L : Subgroup G := componentLayerOf N
  have hforward : E ≤ L := by
    simpa [E, N, L] using secondCase_a7_component_le_normalizer_layer
      hmin c w d hA7 hmodel F X hFleFU hFleM hFcentE hXne hXleF
  have hEqE : IsQuasisimple E := d.E_component.2.2
  have hEcenterA7 : Nonempty
      (E ⧸ Subgroup.center E ≃* alternatingGroup (Fin 7)) := by
    simpa [E] using hA7
  have hZodd : Odd (Nat.card (Subgroup.center E)) := by
    simpa [E] using d.center_odd
  have hEleN : E ≤ N :=
    hforward.trans (componentLayerOf_isNormalIn N).1
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hXnormal : X.Normal :=
      (Subgroup.normalizer_eq_top_iff (H := X)).mp htop
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (minimalCounterexample_isSimple hmin)
        X hXnormal with hXbot | hXtop
    · exact hXne hXbot
    · apply w.M_maximal.ne_top
      apply top_unique
      intro g _hg
      have hgX : g ∈ X := by rw [hXtop]; trivial
      exact hFleM (hXleF hgX)
  have hDN : IsDGroup N := properSubgroups_areDGroups hmin N hNtop
  let EN : Subgroup N := E.subgroupOf N
  let O : Subgroup N := pPrimeCore 2 N
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let q : N →* N ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (N ⧸ O) := EN.map q
  let eEN : EN ≃* E := Subgroup.subgroupOfEquivOfLe hEleN
  have hENq : IsQuasisimple EN :=
    isQuasisimple_mulEquiv_local eEN.symm hEqE
  have hENcenterA7 : Nonempty
      (EN ⧸ Subgroup.center EN ≃* alternatingGroup (Fin 7)) :=
    central_quotient_of_mulEquiv eEN.symm hEcenterA7
  have hEperfect : Group.IsPerfect E := (Group.isPerfect_def).2 hEqE.2.1
  have hENperfect : Group.IsPerfect EN := by
    let : Group.IsPerfect E := hEperfect
    exact Group.IsPerfect.ofSurjective
      (f := eEN.symm.toMonoidHom) eEN.symm.surjective
  have hENne : EN ≠ ⊥ := by
    intro hbot
    have hmap : EN.map N.subtype = E :=
      Subgroup.map_subgroupOf_eq_of_le hEleN
    rw [hbot, Subgroup.map_bot] at hmap
    exact (Subgroup.nontrivial_iff_ne_bot E).mp hEqE.1 hmap.symm
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp
      (pPrimeCore_coprime_card (p := 2) (G := N))
  have hOsolvable : Group.IsSolvable O := odd_order_theorem O hOodd
  let Oamb : Subgroup G := O.map N.subtype
  have hOamb_le_N : Oamb ≤ N := Subgroup.map_subtype_le O
  have hOamb_solvable : Group.IsSolvable Oamb :=
    isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective O N.subtype N.subtype_injective)
  have hOamb_normal : IsNormalIn Oamb N := by
    refine ⟨hOamb_le_N, ?_⟩
    intro n hn o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨n, hn⟩ : N) * o0 * (⟨n, hn⟩ : N)⁻¹,
        (pPrimeCore_normal (p := 2) (G := N)).conj_mem
          o0 ho0 ⟨n, hn⟩, rfl⟩
  have hL_norm_Oamb : L ≤ Subgroup.normalizer (Oamb : Set G) :=
    (componentLayerOf_isNormalIn N).1.trans
      (le_normalizer_of_isNormalIn hOamb_normal)
  have hcomm_LO : ⁅L, Oamb⁆ = ⊥ :=
    componentLayerOf_centralizes_solvable_of_le_normalizer
      N Oamb hOamb_le_N hOamb_solvable hL_norm_Oamb
  have hLcentOamb : L ≤ Subgroup.centralizer (Oamb : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := L) (H₂ := Oamb)).mp hcomm_LO
  have hENcentO : EN ≤ Subgroup.centralizer (O : Set N) := by
    intro e he o ho
    apply Subtype.ext
    have heL : (e : G) ∈ L := hforward (Subgroup.mem_subgroupOf.mp he)
    have hoOamb : (o : G) ∈ Oamb :=
      Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hLcentOamb heL)
      (o : G) hoOamb
  have hAbar : Nonempty
      (Ebar ⧸ Subgroup.center Ebar ≃* alternatingGroup (Fin 7)) :=
    a7_central_quotient_of_image_of_central_kernel
      EN hENq O hOsolvable hENcentO hENcenterA7
  have hEbarData :=
    @perfect_image_le_normal_odd_index_of_solvable_kernel
      N _ _ EN hENperfect hENne O (inferInstance : O.Normal) hOsolvable
        (⊤ : Subgroup (N ⧸ O)) (by infer_instance) (by simp)
  have hEbar_ne_perf : Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar := by
    simpa [Ebar, q] using ⟨hEbarData.1, hEbarData.2.1⟩
  rcases hDN with
      ⟨_hSylowN, hQtwo⟩ | ⟨_hSylowN, hA7q⟩ |
        ⟨_hSylowN, K, hK, Lq, hLqnormal, hLqindex, hlin⟩
  · exfalso
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQsolvable : Group.IsSolvable (N ⧸ O) :=
      isSolvable_of_isPGroup hQtwo
    have hEbarSolvable : Group.IsSolvable Ebar := by
      let : Group.IsSolvable (N ⧸ O) := hQsolvable
      infer_instance
    let : Group.IsPerfect Ebar := hEbar_ne_perf.2
    let : Nontrivial Ebar :=
      (Subgroup.nontrivial_iff_ne_bot Ebar).2 hEbar_ne_perf.1
    exact Group.IsPerfect.not_isSolvable Ebar hEbarSolvable
  · have hcard_dvd : (2520 : ℕ) ∣ Nat.card Ebar :=
      a7_quotient_card_dvd (Subgroup.center Ebar) hAbar
    have h2520_le : 2520 ≤ Nat.card Ebar :=
      Nat.le_of_dvd (by norm_num) hcard_dvd
    have hEbar_card : Nat.card Ebar ≤ Nat.card (N ⧸ O) :=
      Subgroup.card_le_card_group (H := Ebar)
    have hNq_card : Nat.card (N ⧸ O) = 2520 := by
      rw [Nat.card_congr hA7q.some.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hEbar_top : Ebar = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      omega
    have hEN_Osup : O ⊔ EN = ⊤ := by
      have hcomap : (EN.map q).comap q = O ⊔ EN :=
        QuotientGroup.comap_map_mk' O EN
      have htop : (EN.map q).comap q = ⊤ := by
        change EN.map q = ⊤ at hEbar_top
        rw [hEbar_top, Subgroup.comap_top]
      rwa [← hcomap]
    have hLL_le_E : ⁅L, L⁆ ≤ E := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hLleN : L ≤ N := (componentLayerOf_isNormalIn N).1
      have hxN : (⟨x, hLleN hx⟩ : N) ∈ O ⊔ EN := by
        rw [hEN_Osup]
        trivial
      have hyN : (⟨y, hLleN hy⟩ : N) ∈ O ⊔ EN := by
        rw [hEN_Osup]
        trivial
      rcases (Subgroup.mem_sup_of_normal_left (s := O) (t := EN)).mp hxN with
        ⟨z₁, hz₁, e₁, he₁, hx_eq⟩
      rcases (Subgroup.mem_sup_of_normal_left (s := O) (t := EN)).mp hyN with
        ⟨z₂, hz₂, e₂, he₂, hy_eq⟩
      have hxG : x = (z₁ : G) * (e₁ : G) := by
        simpa using (congrArg Subtype.val hx_eq).symm
      have hyG : y = (z₂ : G) * (e₂ : G) := by
        simpa using (congrArg Subtype.val hy_eq).symm
      have he₁E : (e₁ : G) ∈ E := Subgroup.mem_subgroupOf.mp he₁
      have he₂E : (e₂ : G) ∈ E := Subgroup.mem_subgroupOf.mp he₂
      have he₁L : (e₁ : G) ∈ L := hforward he₁E
      have he₂L : (e₂ : G) ∈ L := hforward he₂E
      have hz₁Oamb : (z₁ : G) ∈ Oamb :=
        Subgroup.mem_map.mpr ⟨z₁, hz₁, rfl⟩
      have hz₂Oamb : (z₂ : G) ∈ Oamb :=
        Subgroup.mem_map.mpr ⟨z₂, hz₂, rfl⟩
      have hz₁e₁ : (z₁ : G) * (e₁ : G) = (e₁ : G) * (z₁ : G) :=
        Subgroup.mem_centralizer_iff.mp (hLcentOamb he₁L)
          (z₁ : G) hz₁Oamb
      have hz₁e₂ : (z₁ : G) * (e₂ : G) = (e₂ : G) * (z₁ : G) :=
        Subgroup.mem_centralizer_iff.mp (hLcentOamb he₂L)
          (z₁ : G) hz₁Oamb
      have hz₂e₁ : (z₂ : G) * (e₁ : G) = (e₁ : G) * (z₂ : G) :=
        Subgroup.mem_centralizer_iff.mp (hLcentOamb he₁L)
          (z₂ : G) hz₂Oamb
      have hz₂e₂ : (z₂ : G) * (e₂ : G) = (e₂ : G) * (z₂ : G) :=
        Subgroup.mem_centralizer_iff.mp (hLcentOamb he₂L)
          (z₂ : G) hz₂Oamb
      have hz₁y : (z₁ : G) * y = y * (z₁ : G) :=
        Subgroup.mem_centralizer_iff.mp (hLcentOamb hy)
          (z₁ : G) hz₁Oamb
      have hz₂x : (z₂ : G) * x = x * (z₂ : G) :=
        Subgroup.mem_centralizer_iff.mp (hLcentOamb hx)
          (z₂ : G) hz₂Oamb
      rw [commutator_eq_of_central_decomposition hxG hyG hz₁e₁ hz₁e₂
        hz₂e₁ hz₂e₂ hz₁y hz₂x]
      exact Subgroup.commutator_le_self E
        (E.commutator_mem_commutator he₁E he₂E)
    have hLleE : L ≤ E := by
      have hLL : ⁅L, L⁆ = L :=
        Subgroup.isPerfect_iff.mp (componentLayerOf_isPerfect N)
      rw [← hLL]
      exact hLL_le_E
    simpa [L, E] using le_antisymm hLleE hforward
  · exfalso
    rcases hlin with hPSL | hPGL
    · rcases hPSL with ⟨eL⟩
      have hIm := @perfect_image_le_normal_odd_index_of_solvable_kernel
        N _ _ EN hENperfect hENne O (inferInstance : O.Normal) hOsolvable
          Lq hLqnormal hLqindex
      have hEbarL : Ebar ≤ Lq := by simpa [Ebar, q] using hIm.2.2
      let EL : Subgroup Lq := Ebar.subgroupOf Lq
      have hELne : EL ≠ ⊥ := by
        intro hbot
        have hmap : EL.map Lq.subtype = Ebar :=
          Subgroup.map_subgroupOf_eq_of_le hEbarL
        rw [hbot, Subgroup.map_bot] at hmap
        exact hIm.1 hmap.symm
      have hELperfect : Group.IsPerfect EL := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
        let : Group.IsPerfect Ebar := hIm.2.1
        exact Group.IsPerfect.ofSurjective
          (f := eEL.symm.toMonoidHom) eEL.symm.surjective
      let J : Subgroup (PSL2 K) := EL.map eL.toMonoidHom
      have hJA7 : Nonempty
          (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
        let eMap : EL ≃* J :=
          Subgroup.equivMapOfInjective EL eL.toMonoidHom eL.injective
        exact central_quotient_of_mulEquiv (eEL.symm.trans eMap) hAbar
      exact no_a7_quotient_subgroup_of_psl2_odd hK J hJA7
    · rcases hPGL with ⟨eL⟩
      have hIm := @perfect_image_le_normal_odd_index_of_solvable_kernel
        N _ _ EN hENperfect hENne O (inferInstance : O.Normal) hOsolvable
          Lq hLqnormal hLqindex
      have hEbarL : Ebar ≤ Lq := by simpa [Ebar, q] using hIm.2.2
      let EL : Subgroup Lq := Ebar.subgroupOf Lq
      have hELne : EL ≠ ⊥ := by
        intro hbot
        have hmap : EL.map Lq.subtype = Ebar :=
          Subgroup.map_subgroupOf_eq_of_le hEbarL
        rw [hbot, Subgroup.map_bot] at hmap
        exact hIm.1 hmap.symm
      have hELperfect : Group.IsPerfect EL := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
        let : Group.IsPerfect Ebar := hIm.2.1
        exact Group.IsPerfect.ofSurjective
          (f := eEL.symm.toMonoidHom) eEL.symm.surjective
      let J : Subgroup (PGL2 K) := EL.map eL.toMonoidHom
      have hJperfect : Group.IsPerfect J := by
        dsimp [J]
        let : Group.IsPerfect EL := hELperfect
        exact Group.IsPerfect.map eL.toMonoidHom
      have hJA7 : Nonempty
          (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) := by
        let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
        let eMap : EL ≃* J :=
          Subgroup.equivMapOfInjective EL eL.toMonoidHom eL.injective
        exact central_quotient_of_mulEquiv (eEL.symm.trans eMap) hAbar
      let : Finite (PGL2 K) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk
          Matrix.ProjGenLinGroup.mk_surjective
      by_cases hK3 : Nat.card K = 3
      · have hPGLcard : Nat.card (PGL2 K) = 3 * (3 ^ 2 - 1) := by
          simp [pgl2_card_formula K, hK3]
        have hcardJ : Nat.card J < 2520 := by
          have hle : Nat.card J ≤ Nat.card (PGL2 K) :=
            Subgroup.card_le_card_group (H := J)
          rw [hPGLcard] at hle
          omega
        exact a7_quotient_absurd_of_card_lt
          (N := Subgroup.center J) hcardJ hJA7
      · have hcard_ge : 3 ≤ Nat.card K := by
          rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
          have hpne2 : p ≠ 2 := by
            intro hp2
            subst p
            exact hpodd.not_two_dvd_nat (by simp)
          have hpge : 3 ≤ p := by
            have hp2 := hp.two_le
            omega
          rw [hcard]
          exact hpge.trans (by
            calc
              p = p ^ 1 := by simp
              _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn)
        have hcard_gt : 3 < Nat.card K := by omega
        have hJleComm : J ≤ commutator (PGL2 K) := by
          let : Group.IsPerfect J := hJperfect
          have hJJ : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
          rw [← hJJ]
          exact Subgroup.commutator_mono le_top le_top
        let C : Subgroup (PGL2 K) := commutator (PGL2 K)
        have eC : Nonempty (C ≃* PSL2 K) :=
          commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
            K hK hcard_gt (MulEquiv.refl (PGL2 K))
        let JC : Subgroup C := J.subgroupOf C
        let JPSL : Subgroup (PSL2 K) := JC.map eC.some.toMonoidHom
        have hJPSLA7 : Nonempty
            (JPSL ⧸ Subgroup.center JPSL ≃* alternatingGroup (Fin 7)) := by
          let eJCJ : JC ≃* J := Subgroup.subgroupOfEquivOfLe hJleComm
          let eMap : JC ≃* JPSL :=
            Subgroup.equivMapOfInjective JC eC.some.toMonoidHom
              eC.some.injective
          exact central_quotient_of_mulEquiv (eJCJ.symm.trans eMap) hJA7
        exact no_a7_quotient_subgroup_of_psl2_odd hK JPSL hJPSLA7

end CFSG.GorensteinWalter
