module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.NormalPSL2InvolutionCentralizerOddFittingPSLRange
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingActionCommon
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerSylowNoncyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2ComponentLeNormalizerLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectNormalSubgroupMulEquivPSL2OfLinearModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectImageNormalOddIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelCentralizerSurjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalCenterlessDihedral
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The normalizer inner action in the linear D-group model
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix

universe u

/-- In the linear model case for `N_G(X)/O₂'(N_G(X))`, the local odd
Fitting subgroup induces inner automorphisms on the actual normalizer layer.
The field projection is killed in the quotient involution centralizer and
the resulting inner representative is lifted across the odd core. -/
public theorem secondCase_psl2_normalizer_innerAction_of_linear_model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (F X : Subgroup G)
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hXne : X ≠ ⊥) (hXleF : X ≤ F)
    (hSylowN : HasCyclicOrDihedralSylowTwo
      (Subgroup.normalizer (X : Set G)))
    (K' : Type u) [Field K'] [Finite K']
    (hK' : IsOddPrimePower (Nat.card K'))
    (Lq : Subgroup (Subgroup.normalizer (X : Set G) ⧸
      pPrimeCore 2 (Subgroup.normalizer (X : Set G))))
    (hLqnormal : Lq.Normal) (hLqindex : Odd Lq.index)
    (hLqmodel : Nonempty (Lq ≃* PSL2 K') ∨ Nonempty (Lq ≃* PGL2 K')) :
    secondCase_psl2_normalizer_innerAction c X := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let L : Subgroup G := componentLayerOf N
  let O : Subgroup N := pPrimeCore 2 N
  let : O.Normal := by dsimp [O]; infer_instance
  let q : N →* N ⧸ O := QuotientGroup.mk' O
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective O
  have hLleN : L ≤ N := (componentLayerOf_isNormalIn N).1
  have hLnorm : IsNormalIn L N := componentLayerOf_isNormalIn N
  have hforward : d.E ≤ L := by
    simpa [N, L] using secondCase_psl2_component_le_normalizer_layer
      hmin c w d K hK e F X hFleFU hFleM hFcentE hXne hXleF
  have hEleN : d.E ≤ N := hforward.trans hLleN
  let LN : Subgroup N := L.subgroupOf N
  let Lbar : Subgroup (N ⧸ O) := LN.map q
  have hLperf : Group.IsPerfect L := componentLayerOf_isPerfect N
  have hLNperf : Group.IsPerfect LN := by
    let eLN : LN ≃* L := Subgroup.subgroupOfEquivOfLe hLleN
    let : Group.IsPerfect L := hLperf
    exact Group.IsPerfect.ofSurjective
      (f := eLN.symm.toMonoidHom) eLN.symm.surjective
  have hLne : L ≠ ⊥ := by
    intro hbot
    have htL : c.t ∈ L := hforward d.t_mem_E
    have ht1 : c.t = 1 := by simpa [hbot] using htL
    exact c.t_involution.1 ht1
  have hLNne : LN ≠ ⊥ := by
    intro hbot
    apply hLne
    have hmap : LN.map N.subtype = L :=
      Subgroup.map_subgroupOf_eq_of_le hLleN
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := N))
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  have hLbarData := @perfect_image_le_normal_odd_index_of_solvable_kernel
    N _ _ LN hLNperf hLNne O (inferInstance : O.Normal) hOsolv
      Lq hLqnormal hLqindex
  have hLbarne : Lbar ≠ ⊥ := by simpa [Lbar, q] using hLbarData.1
  have hLbarperf : Group.IsPerfect Lbar := by
    simpa [Lbar, q] using hLbarData.2.1
  have hLNnormal : LN.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLleN]
    intro l n hl hn
    exact hLnorm.2 n hn l hl
  have hLbarNormal : Lbar.Normal := by
    dsimp [Lbar]
    exact hLNnormal.map q hqsurj
  obtain ⟨hKcard, eLbar⟩ :=
    perfect_normal_subgroup_mulEquiv_psl2_of_linear_model
      Lbar Lq hLbarNormal hLbarne hLbarperf hLqnormal hLqindex
        K' hK' hLqmodel
  have hNdihedral : HasDihedralSylowTwo N := by
    intro S
    rcases hSylowN S with hScyc | hSd
    · exact False.elim
        (secondCase_psl2_sylow_not_cyclic_of_component_le
          c w d K hK e N hEleN S hScyc)
    · exact hSd
  have hQdihedral : HasDihedralSylowTwo (N ⧸ O) := by
    have hRange : HasDihedralSylowTwo q.range :=
      image_hasDihedralSylowTwo_of_odd_kernel hNdihedral q (by
        have hker : q.ker = O := by simpa [q] using QuotientGroup.ker_mk' O
        rwa [hker])
    let eqQ : q.range ≃* (N ⧸ O) :=
      (MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hqsurj)).trans
        Subgroup.topEquiv
    exact hasDihedralSylowTwo_of_mulEquiv eqQ.symm hRange
  have hQcore : pPrimeCore 2 (N ⧸ O) = ⊥ := by
    simpa [O] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := N) 2)
  have hLbarCenter : Subgroup.center Lbar = ⊥ :=
    center_eq_bot_of_mulEquiv eLbar.some (psl2_center_eq_bot K')
  have hLbarDihedral : HasDihedralSylowTwo Lbar :=
    hasDihedralSylowTwo_of_mulEquiv eLbar.some
      (psl2_odd_hasDihedralSylowTwo_model K' hK')
  have hLbarCent : Subgroup.centralizer (Lbar : Set (N ⧸ O)) = ⊥ :=
    centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
      hQdihedral hQcore Lbar hLbarNormal hLbarCenter hLbarDihedral
  rcases hK' with ⟨ell, n, hell, hellodd, hn, hKcardEq⟩
  let : Fact ell.Prime := ⟨hell⟩
  let hKfull : IsOddPrimePower (Nat.card K') :=
    ⟨ell, n, hell, hellodd, hn, hKcardEq⟩
  let hsurj : Function.Surjective
      (pGammaL2ToMulAutPSL2 K' hKfull hKcard) :=
    pGammaL2ToMulAutPSL2_surjective K' hKcardEq hKfull hKcard
  let fmap : (N ⧸ O) →* PGammaL2 K' :=
    normalPSL2ToPGammaL2 Lbar K' hKfull hKcard eLbar.some hsurj
  have hfmapinj : Function.Injective fmap :=
    normalPSL2ToPGammaL2_injective Lbar K' hKfull hKcard eLbar.some
      hLbarCent hsurj
  let tN : N := ⟨c.t, hEleN d.t_mem_E⟩
  let tbar : N ⧸ O := q tN
  have htN : IsInvolution tN := by
    constructor
    · intro h1
      exact c.t_involution.1 (congrArg Subtype.val h1)
    · apply Subtype.ext
      simpa using c.t_involution.2
  have htbar : IsInvolution tbar :=
    quotient_involution_of_involution O hOodd htN
  have htbarL : tbar ∈ Lbar := by
    exact Subgroup.mem_map.mpr
      ⟨tN, Subgroup.mem_subgroupOf.mpr (hforward d.t_mem_E), rfl⟩
  let PG : Subgroup G := c.FU ⊓ N
  let PN : Subgroup N := PG.subgroupOf N
  let Pbar : Subgroup (N ⧸ O) := PN.map q
  let CN : Subgroup N := Subgroup.centralizer ({tN} : Set N)
  have hPNleCN : PN ≤ CN := by
    intro p hp
    have hpG : (p : G) ∈ PG := Subgroup.mem_subgroupOf.mp hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (p : G) * c.t = c.t * (p : G)
    have hpH : (p : G) ∈ c.H :=
      (centralizerSetup_FU_isNormalIn_H c).1 hpG.1
    rwa [c.H_eq_centralizer,
      Subgroup.mem_centralizer_singleton_iff] at hpH
  have hPNnormalCN : IsNormalIn PN CN := by
    refine ⟨hPNleCN, ?_⟩
    intro a ha p hp
    apply Subgroup.mem_subgroupOf.mpr
    have haH : (a : G) ∈ c.H := by
      rw [c.H_eq_centralizer,
        Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp ha)
    have hpG : (p : G) ∈ PG := Subgroup.mem_subgroupOf.mp hp
    exact ⟨(centralizerSetup_FU_isNormalIn_H c).2
        (a : G) haH (p : G) hpG.1,
      N.mul_mem (N.mul_mem a.2 hpG.2) (N.inv_mem a.2)⟩
  have hPNodd : Odd (Nat.card PN) := by
    have hPGodd : Odd (Nat.card PG) := by
      have hPleU : PG ≤ c.U :=
        inf_le_left.trans (fittingSubgroupOf_le c.U)
      have hUodd : Odd (Nat.card c.U) := by
        change Odd (Nat.card (oddCoreOf c.H))
        exact odd_card_oddCoreOf c.H
      exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hPleU)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact hPGodd
  have hPNnil : Group.IsNilpotent PN := by
    let : Group.IsNilpotent c.FU := fittingSubgroupOf_isNilpotent c.U
    have hPGnil : Group.IsNilpotent PG := by
      have : Group.IsNilpotent (PG.subgroupOf c.FU) := inferInstance
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe inf_le_left)
    have : Group.IsNilpotent PG := hPGnil
    exact Group.nilpotent_of_mulEquiv
      (G := PG) (G' := PN)
      (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hPbarOdd : Odd (Nat.card Pbar) :=
    Odd.of_dvd_nat hPNodd (Subgroup.card_map_dvd PN q)
  have hPbarNil : Group.IsNilpotent Pbar := by
    let fP : PN →* Pbar :=
      (q.comp PN.subtype).codRestrict Pbar (fun p =>
        Subgroup.mem_map.mpr ⟨p, p.2, rfl⟩)
    have hfPsurj : Function.Surjective fP := by
      intro y
      rcases Subgroup.mem_map.mp y.2 with ⟨p, hp, hpy⟩
      exact ⟨⟨p, hp⟩, Subtype.ext hpy⟩
    exact Group.nilpotent_of_surjective fP hfPsurj
  have hPbarLeC : Pbar ≤ Subgroup.centralizer ({tbar} : Set (N ⧸ O)) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change q p * q tN = q tN * q p
    rw [← map_mul, ← map_mul]
    exact congrArg q (Subgroup.mem_centralizer_singleton_iff.mp (hPNleCN hp))
  have hPbarNormal : IsNormalIn Pbar
      (Subgroup.centralizer ({tbar} : Set (N ⧸ O))) := by
    refine ⟨hPbarLeC, ?_⟩
    intro a ha y hy
    obtain ⟨a0, ha0C, ha0q⟩ :=
      exists_centralizer_lift_of_odd_kernel O hOodd htN a ha
    rcases Subgroup.mem_map.mp hy with ⟨p0, hp0, hp0q⟩
    apply Subgroup.mem_map.mpr
    refine ⟨a0 * p0 * a0⁻¹, hPNnormalCN.2 a0 ha0C p0 hp0, ?_⟩
    rw [map_mul, map_mul, map_inv, ha0q, hp0q]
  have hPbarImage : Pbar.map fmap ≤ pGammaL2PSLRange K' :=
    normalPSL2_involutionCentralizer_oddFitting_image_le_pslRange
      Lbar K' hKfull hKcard eLbar.some hLbarCent hsurj htbarL htbar
      Pbar hPbarLeC hPbarNormal hPbarOdd hPbarNil
  have hLcentO : L ≤ Subgroup.centralizer
      (((pPrimeCore 2 N).map N.subtype) : Set G) :=
    layer_centralizes_oddCore N
  intro p hp
  let pN : N := ⟨p, hp.2⟩
  have hpPbar : q pN ∈ Pbar :=
    Subgroup.mem_map.mpr
      ⟨pN, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
  have hfp : fmap (q pN) ∈ pGammaL2PSLRange K' :=
    hPbarImage (Subgroup.mem_map.mpr ⟨q pN, hpPbar, rfl⟩)
  rcases (mem_pGammaL2PSLRange_iff K' (fmap (q pN))).mp hfp with
    ⟨a, hfa⟩
  let lbar : Lbar := eLbar.some.symm a
  obtain ⟨lN, hlLN, hqL⟩ := Subgroup.mem_map.mp lbar.2
  let ell : G := lN
  have hellL : ell ∈ L := Subgroup.mem_subgroupOf.mp hlLN
  have hflbar : fmap (lbar : N ⧸ O) =
      SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL a) := by
    calc
      fmap (lbar : N ⧸ O) = SemidirectProduct.inl
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (eLbar.some lbar)) := by
        simpa [fmap] using
          normalPSL2ToPGammaL2_apply_subtype Lbar K' hKfull hKcard
            eLbar.some hsurj lbar
      _ = SemidirectProduct.inl
          (Matrix.ProjectiveSpecialLinearGroup.toPGL a) := by simp [lbar]
  have hqpL : q pN = (lbar : N ⧸ O) := by
    apply hfmapinj
    exact hfa.symm.trans hflbar.symm
  have hqplN : q (pN * lN⁻¹) = 1 := by
    rw [map_mul, map_inv, hqL]
    change q pN * (lbar : N ⧸ O)⁻¹ = 1
    rw [hqpL]
    simp
  have hplO : p * ell⁻¹ ∈ (pPrimeCore 2 N).map N.subtype := by
    have hmem : pN * lN⁻¹ ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) (pN * lN⁻¹)).mp hqplN
    exact Subgroup.mem_map.mpr ⟨pN * lN⁻¹, hmem, rfl⟩
  refine ⟨ell, hellL, ?_⟩
  intro x hx
  calc
    p * x * p⁻¹ = (p * ell⁻¹) * (ell * x * ell⁻¹) *
        (p * ell⁻¹)⁻¹ := by group
    _ = (ell * x * ell⁻¹) * (p * ell⁻¹) *
        (p * ell⁻¹)⁻¹ := by
      have hcomm' : (ell * x * ell⁻¹) * (p * ell⁻¹) =
          (p * ell⁻¹) * (ell * x * ell⁻¹) := by
        have hconjL : ell * x * ell⁻¹ ∈ L :=
          L.mul_mem (L.mul_mem hellL hx) (L.inv_mem hellL)
        exact ((Subgroup.mem_centralizer_iff.mp (hLcentO hconjL))
          (p * ell⁻¹) hplO).symm
      rw [hcomm'.symm]
    _ = ell * x * ell⁻¹ := by group

end CFSG.GorensteinWalter
