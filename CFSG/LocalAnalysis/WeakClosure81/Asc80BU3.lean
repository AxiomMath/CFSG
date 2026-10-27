module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BFrame

import CFSG.LocalAnalysis.WeakClosure81.FiveSevenRed
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderGenAux1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
import CFSG.LargeExtraspecial.S8CBFSmall
import CFSG.RankThree.GF2n.Tim77.AutDichU3
import CFSG.CGT.T75M.SzBorel
import CFSG.CGT.T75E.RootOrders
import CFSG.Timmesfeld.Bridge.OddTranspGenL2
import CFSG.GH74.KGroups.BalanceLift
import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut
import CFSG.Goldschmidt75.Closure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.BenderSuzuki
open CFSG.GH74.Uniqueness.Bender (rootCenter)

private theorem false_of_simple_le_normalizer_twoGroup
    {G : Type} [Group G] [Finite G] {X U : Subgroup G}
    (hXsimple : IsSimpleGroup ↥X)
    (hXnab : ∃ a b : ↥X, a * b ≠ b * a)
    (hU2 : IsPGroup 2 U)
    (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hne : X ⊓ U ≠ ⊥) : False := by
  haveI : IsSimpleGroup ↥X := hXsimple
  have hnormal : ((X ⊓ U).subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_left : X ⊓ U ≤ X)]
    intro h k hh hk
    obtain ⟨hhX, hhU⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem hk hhX) (X.inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXU hk) h).mp hhU
  haveI := hnormal
  have hne' : (X ⊓ U).subgroupOf X ≠ ⊥ := by
    intro hbot
    apply hne
    have hmap := Subgroup.map_subgroupOf_eq_of_le (inf_le_left : X ⊓ U ≤ X)
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X ⊓ U).subgroupOf X) with hbot | htop
  · exact hne' hbot
  · have hXU' : X ≤ U := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥X) ∈ (X ⊓ U).subgroupOf X := by
        rw [htop]
        trivial
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx')).2
    have hXP : IsPGroup 2 ↥X := hU2.to_le hXU'
    have hsol : Group.IsSolvable ↥X := by
      haveI : Group.IsNilpotent ↥X := IsPGroup.isNilpotent hXP
      exact IsNilpotent.to_isSolvable
    obtain ⟨a, b, hab⟩ := hXnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)

theorem asc80ThmBCase_u3 :
    Asc80ThmBCase fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .PSU 3 2 f := by
  intro G _ _ H A M hs hnab hP hAH hA hM
  exfalso
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hm⟩ := hP
  let L : Subgroup G := Fstar H
  have hLH : L ≤ H := fstar_le_group H
  have hLnorm : (L.subgroupOf H).Normal := normal_subgroupOf_fstar H
  have S := asc80BSetup hs hnab hAH hA hM
  have hf : 2 ≤ f := by
    have h := hm.1
    simp only [CFSG.Open.StatedLieAdmissible] at h
    by_contra hlt
    have hf1 : f = 1 := by omega
    exact h.2.2.2 (by rw [hf1]; norm_num)
  have hcl : CFSG.Open.StatedClassicalModel ↥L .PSU 3 2 f :=
    (CFSG.RankTwoShapes.open_statedClassicalModel_PSU_iff ↥L 3 2 f).mpr
      (hm.statedClassicalModel (by decide))
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.open_statedClassicalModel_PSU_three_two_iff ↥L f hf).mp hcl
  have hBL : IsBenderGroup ↥L := IsBenderGroup.isPSU3 f hf e
  have hBp : CFSG.Blueprint.LieModel ↥L .PSU 3 2 f := hm.toBlueprint (by decide)
  have hB : CFSG.Open.fusionIsBenderGroup ↥L :=
    CFSG.LargeExtraspecial.S8.fusionIsBenderGroup_of_lieModel_psu_three hBp
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 hAH hA.isPGroup
  have hTM : T ≤ M := (isUniqueMaxOver_iff.mp (S.maxOver_sylow hT hAT)).2.1
  let U : Subgroup G := T ⊓ L
  have hUL : U ≤ L := inf_le_right
  have hUsyl : IsSylowIn 2 U L := CFSG.Quasithin.IsSylowIn.inf_normal hT hLH hLnorm
  have hU2 : IsPGroup 2 U := hUsyl.isPGroup
  let Q : Sylow 2 ↥L := hUsyl.toSylow
  have hQco : (Q : Subgroup ↥L) = U.subgroupOf L := CFSG.Quasithin.IsSylowIn.coe_toSylow hUsyl
  have hTML : T ⊓ L ≤ M ⊓ L := le_inf (inf_le_left.trans hTM) inf_le_right
  have hMLne : M ⊓ L ≠ L := by
    intro h
    exact S.not_fstar_le (le_of_eq_of_le h.symm inf_le_left)
  have hMLtop : (M ⊓ L).subgroupOf L ≠ ⊤ := by
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hMLne (le_antisymm htop inf_le_right).symm
  have hQle : (Q : Subgroup ↥L) ≤ (M ⊓ L).subgroupOf L := by
    rw [hQco]
    exact Subgroup.subgroupOf_mono L hTML
  have hMnormL : M ⊓ L ≤ Subgroup.normalizer (U : Set G) := by
    haveI : IsSimpleGroup ↥L := hs
    have hle := CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB Q hQle hMLtop
    intro x hx
    let xL : ↥L := ⟨x, hx.2⟩
    have hxP : xL ∈ (M ⊓ L).subgroupOf L := hx
    have hxN : xL ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := hle hxP
    have hxN' : xL ∈ Subgroup.normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rwa [hQco] at hxN
    exact CFSG.Goldschmidt75.mem_normalizer_of_mem_normalizer_subgroupOf hUL hxN'
  have hEvenL : Even (Nat.card ↥L) := by
    rw [Nat.card_congr e.toEquiv]
    obtain ⟨r, hr, hcard⟩ := CFSG.CGT.T75E.exists_odd_card_psu3Model (f := f) (by omega)
    rw [show Nat.card ↥(Theory.Comparator.PSU3Model f) = 2 ^ (3 * f) * r from hcard]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right r
  have hU1 : U ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card U = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hUsyl.card_eq] at hcard1
    have hpos : 0 < (Nat.card ↥L).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne'
        (even_iff_two_dvd.mp hEvenL)
    have hgt : 1 < 2 ^ (Nat.card ↥L).factorization 2 :=
      Nat.one_lt_pow hpos.ne' (by norm_num)
    omega
  have hAL : A ≤ L := by
    by_contra hnot
    rw [SetLike.not_le_iff_exists] at hnot
    obtain ⟨a, haA, haL⟩ := hnot
    have haH : a ∈ H := hAH haA
    have haT : a ∈ T := hAT haA
    have haa : a * a = 1 := by
      have := hA.2 a haA
      simpa [pow_two] using this
    have haN : a ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hLnorm haH
    let C₀ : Subgroup G := H ⊓ Subgroup.centralizer ({a} : Set G)
    have hAC : A ≤ C₀ := by
      intro x hx
      refine ⟨hAH hx, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg (fun z : ↥A => (z : G)) (hA.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
    have hCne : C₀ ≠ H := by
      intro hCH
      have hHC : H ≤ Subgroup.centralizer ({a} : Set G) := hCH ▸ inf_le_right
      have haCent : a ∈ Subgroup.centralizer (L : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (hHC (hLH hy))
      have : a ∈ H ⊓ Subgroup.centralizer (L : Set G) := ⟨haH, haCent⟩
      rw [S.inf_centralizer] at this
      have ha1 : a = 1 := Subgroup.mem_bot.mp this
      exact haL (ha1 ▸ L.one_mem)
    have hClt : C₀ < H := lt_of_le_of_ne inf_le_left hCne
    have hCM : C₀ ≤ M := S.le_of_lt C₀ hAC hClt
    have haU : ∀ w ∈ U, a * w * a⁻¹ ∈ U := by
      intro w hw
      obtain ⟨hwT, hwL⟩ := Subgroup.mem_inf.mp hw
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer haT) w).mp hwT,
          (Subgroup.mem_normalizer_iff.mp haN w).mp hwL⟩
    have hEvenU : Even (Nat.card U) := by
      obtain ⟨k, hk⟩ := hU2.exists_card_eq
      have hk0 : k ≠ 0 := by
        intro hk0
        apply hU1
        exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])
      rw [hk]
      exact Nat.even_pow.2 ⟨even_two, hk0⟩
    obtain ⟨ā, hāU, hā2, hā1, hācomm⟩ :=
      CFSG.GH74.KGroups.Bal.exists_fixed_involution (a := a) haa haU hEvenU
    have hāL : ā ∈ L := hUL hāU
    have hāconj : a * ā * a⁻¹ = ā := by rw [hācomm]; group
    let Lsub : Subgroup ↥H := L.subgroupOf H
    have hLsubNormal : Lsub.Normal := hLnorm
    have hCentL : Subgroup.centralizer (Lsub : Set ↥H) = ⊥ := by
      ext x
      constructor
      · intro hx
        have hxG : (x : G) ∈ H ⊓ Subgroup.centralizer (L : Set G) := by
          refine ⟨x.2, ?_⟩
          refine Subgroup.mem_centralizer_iff.mpr ?_
          intro y hy
          have hyH : y ∈ H := hLH hy
          have hyL : (⟨y, hyH⟩ : ↥H) ∈ Lsub := by
            rw [Subgroup.mem_subgroupOf]
            exact hy
          have hcomm := (Subgroup.mem_centralizer_iff.mp hx) ⟨y, hyH⟩ hyL
          exact congrArg (fun t : ↥H => (t : G)) hcomm
        have hxG' : (x : G) ∈ H ⊓ Subgroup.centralizer (Fstar H : Set G) := by
          simpa [L] using hxG
        rw [S.inf_centralizer] at hxG'
        have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp hxG' 
        exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact (Subgroup.centralizer _).one_mem
    let aH : ↥H := ⟨a, haH⟩
    let σH : MulAut ↥Lsub := MulAut.conjNormal (H := Lsub) aH
    have hσHmul : σH * σH = 1 := by
      change MulAut.conjNormal (H := Lsub) aH * MulAut.conjNormal (H := Lsub) aH = 1
      rw [← map_mul, show aH * aH = 1 from Subtype.ext haa, map_one]
    let āLsub : ↥Lsub := ⟨⟨ā, hLH hāL⟩, by
      rw [Subgroup.mem_subgroupOf]
      exact hāL⟩
    have hāLsub2 : āLsub * āLsub = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hā2
    have hāLsub1 : āLsub ≠ 1 := by
      intro h
      apply hā1
      have hcoe : ((āLsub : ↥H) : G) = 1 := by
        simpa using congrArg (fun z : ↥Lsub => ((z : ↥H) : G)) h
      exact hcoe
    have hāord : orderOf āLsub = 2 := orderOf_eq_prime (by rwa [pow_two]) hāLsub1
    have hfixā : σH āLsub = āLsub := by
      apply Subtype.ext
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      simpa using hāconj
    let eL : ↥Lsub ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
    have hPSU : ↥Lsub ≃* PSU3Model f := eL.trans e
    rcases CFSG.RankThree.GF2n.Tim77.autDich_u3 hf hPSU σH hσHmul hāord hfixā with
      ⟨τ, hτ2, hτā, hconj⟩ | ⟨t, ht_ord, ht_fix, ht_notcomm⟩
    ·
      have hconj_eq : σH = MulAut.conjNormal (H := Lsub) (τ : ↥H) := by
        rw [MulAut.conjNormal_val]
        apply MulEquiv.ext
        intro z
        simpa [MulAut.conj_apply] using hconj z
      have haeq : aH = (τ : ↥H) :=
        CFSG.LieType.SeitzGeneration.conjNormal_injective (K := Lsub) hCentL (by
          simpa [σH] using hconj_eq)
      have haL' : a ∈ L := by
        have hmem : aH ∈ Lsub := by
          rw [haeq]
          exact τ.2
        exact Subgroup.mem_subgroupOf.mp hmem
      exact haL haL'
    ·
      have htLsub : (t : ↥H) ∈ Lsub := t.2
      have htG_L : ((t : ↥H) : G) ∈ L := Subgroup.mem_subgroupOf.mp htLsub
      have ht_fixG : a * ((t : ↥H) : G) * a⁻¹ = ((t : ↥H) : G) := by
        have h := congrArg (fun z : ↥Lsub => ((z : ↥H) : G)) ht_fix
        simpa [σH, MulAut.conjNormal_apply] using h
      have htcomm : a * ((t : ↥H) : G) = ((t : ↥H) : G) * a := by
        calc a * ((t : ↥H) : G) = (a * ((t : ↥H) : G) * a⁻¹) * a := by group
          _ = ((t : ↥H) : G) * a := by rw [ht_fixG]
      have htC : ((t : ↥H) : G) ∈ C₀ := by
        refine ⟨(t : ↥H).2, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr htcomm.symm
      have htM : ((t : ↥H) : G) ∈ M := hCM htC
      have htNormU : ((t : ↥H) : G) ∈ Subgroup.normalizer (U : Set G) :=
        hMnormL ⟨htM, htG_L⟩
      let tL : ↥L := ⟨((t : ↥H) : G), htG_L⟩
      let āL : ↥L := ⟨ā, hāL⟩
      have htL2 : tL * tL = 1 := by
        have ht2 : t * t = 1 := by
          have := pow_orderOf_eq_one t
          rw [ht_ord] at this
          simpa [pow_two] using this
        have h := congrArg (fun z : ↥Lsub => ((z : ↥H) : G)) ht2
        apply Subtype.ext
        simpa [tL] using h
      have hāL2 : āL * āL = 1 := by
        apply Subtype.ext
        exact hā2
      have htNormQ : tL ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
        rw [hQco, ← Subgroup.subgroupOf_normalizer_eq hUL]
        exact Subgroup.mem_subgroupOf.mpr (by simpa [tL] using htNormU)
      have hāNormU : ā ∈ Subgroup.normalizer (U : Set G) := Subgroup.le_normalizer hāU
      have hāNormQ : āL ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
        rw [hQco, ← Subgroup.subgroupOf_normalizer_eq hUL]
        exact Subgroup.mem_subgroupOf.mpr (by simpa [āL] using hāNormU)
      have htZ := CFSG.CGT.T75M.mem_center_of_mem_normalizer_sylow hBL Q htNormQ htL2
      have hāZ := CFSG.CGT.T75M.mem_center_of_mem_normalizer_sylow hBL Q hāNormQ hāL2
      have hcommL : Commute āL tL := by
        obtain ⟨t', ht'c, ht'eq⟩ := Subgroup.mem_map.mp htZ
        obtain ⟨ā', hā'c, hā'eq⟩ := Subgroup.mem_map.mp hāZ
        have hcomm'' : Commute t' ā' := Subgroup.mem_center_iff.mp hā'c t'
        have hcomm' : Commute ((Q : Subgroup ↥L).subtype ā')
            ((Q : Subgroup ↥L).subtype t') :=
          (hcomm''.map (Q : Subgroup ↥L).subtype).symm
        rw [hā'eq, ht'eq] at hcomm'
        exact hcomm' 
      have heLā : eL āLsub = āL := by
        apply Subtype.ext
        rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
      have heLt : eL t = tL := by
        apply Subtype.ext
        rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
      exact ht_notcomm (Commute.of_map eL.injective (by simpa [heLā, heLt] using hcommL))
  have hH : H = L := by
    rw [S.eq_sup]
    exact sup_eq_left.mpr hAL
  have hAUL : A ≤ U := le_inf hAT hAL
  have hAroot : A ≤ rootCenter U := by
    intro a haA
    have haU : a ∈ U := hAUL haA
    have haL : a ∈ L := hUL haU
    have ha2 : a * a = 1 := by
      have := hA.2 a haA
      simpa [pow_two] using this
    have haQ2 : (⟨a, haL⟩ : ↥L) * ⟨a, haL⟩ = 1 := Subtype.ext ha2
    have haQ : (⟨a, haL⟩ : ↥L) ∈ (Q : Subgroup ↥L) := by
      rw [hQco]
      exact Subgroup.mem_subgroupOf.mpr haU
    have hcent := CFSG.CGT.T75A.mem_sylowCenter_of_involution hf hcl Q haQ haQ2
    have hcent' : (⟨a, haL⟩ : ↥L) ∈
        CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (Q : Subgroup ↥L) := hcent
    have hsub : (Q : Subgroup ↥L) = U.subgroupOf L := hQco
    have hcentU : (⟨a, haL⟩ : ↥L) ∈
        CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (U.subgroupOf L) := by
      simpa [hsub] using hcent'
    have haRoot : a ∈ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter U :=
      (CFSG.ComponentClassification.AschbacherToolkit.BenderExt.Bridge.mem_sylowCenter_subgroupOf
        hUL ⟨a, haL⟩).mp hcentU
    simpa [rootCenter, CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter]
      using haRoot
  have hQtop : (Q : Subgroup ↥L) ≠ ⊤ := by
    intro htop
    have hQ2 : IsPGroup 2 (Q : Subgroup ↥L) := Q.isPGroup'
    have hL2 : IsPGroup 2 ↥L := (htop ▸ hQ2).of_equiv Subgroup.topEquiv
    have hsol : Group.IsSolvable ↥L := by
      haveI : Group.IsNilpotent ↥L := IsPGroup.isNilpotent hL2
      exact IsNilpotent.to_isSolvable
    haveI : IsSimpleGroup ↥L := hs
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsol x y)
  have hQnotnormal : ¬ (Q : Subgroup ↥L).Normal := by
    intro hN
    haveI : (Q : Subgroup ↥L).Normal := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q : Subgroup ↥L) with hbot | htop
    · have hUmap : U = (Q : Subgroup ↥L).map L.subtype := by
        rw [hQco]
        exact (Subgroup.map_subgroupOf_eq_of_le hUL).symm
      have hUbot : U = ⊥ := by rw [hUmap, hbot, Subgroup.map_bot]
      exact hU1 hUbot
    · exact hQtop htop
  have hNne : Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) ≠ ⊤ := by
    intro htop
    exact hQnotnormal ((Subgroup.normalizer_eq_top_iff).mp htop)
  obtain ⟨g, -, hgnot⟩ :=
    SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hNne)
  let Q' : Sylow 2 ↥L := g • Q
  have hQ'ne : Q' ≠ Q := by
    intro h
    exact hgnot ((Sylow.smul_eq_iff_mem_normalizer).mp h)
  let KL : Subgroup ↥L := rootCenter (Q : Subgroup ↥L) ⊔ rootCenter (Q' : Subgroup ↥L)
  let K : Subgroup G := KL.map L.subtype
  obtain ⟨ψ⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.TimTI.timti_isPSL2_sup_rootCenter_of_ne hf e (Ne.symm hQ'ne)
  let eK : ↥KL ≃* ↥K := Subgroup.equivMapOfInjective KL L.subtype L.subtype_injective
  have hKcard : Nat.card ↥K = Nat.card (PSL2Model f) := by
    rw [← Nat.card_congr eK.toEquiv, Nat.card_congr ψ.toEquiv]
  have hLcard : Nat.card ↥L = Nat.card (PSU3Model f) := Nat.card_congr e.toEquiv
  have hineq : Nat.card (PSL2Model f) < Nat.card (PSU3Model f) := by
    rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega)]
    obtain ⟨r, hr, hcard⟩ := CFSG.CGT.T75E.exists_odd_card_psu3Model (f := f) (by omega)
    rw [hcard]
    have hlt : 2 ^ f * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 3 := by
      calc 2 ^ f * ((2 ^ f) ^ 2 - 1) < 2 ^ f * (2 ^ f) ^ 2 :=
            Nat.mul_lt_mul_of_pos_left
              (Nat.sub_lt (by positivity) (by norm_num)) (by positivity)
        _ = (2 ^ f) ^ 3 := by ring
    have hq3 : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by
      rw [← pow_mul]
      congr 1
      omega
    exact hlt.trans_le (hq3 ▸ Nat.le_mul_of_pos_right _ hr.pos)
  have hKleL : K ≤ L := Subgroup.map_subtype_le KL
  have hKltL : K < L := by
    refine lt_of_le_of_ne hKleL ?_
    intro hKL
    have hcard_eq : Nat.card ↥K = Nat.card ↥L := by rw [hKL]
    rw [hKcard, hLcard] at hcard_eq
    omega
  have hAK : A ≤ K := by
    have hrootU : rootCenter U = (rootCenter (Q : Subgroup ↥L)).map L.subtype := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxU, hxcent⟩ := Subgroup.mem_inf.mp hx
        have hxL : x ∈ L := hUL hxU
        let xL : ↥L := ⟨x, hxL⟩
        have hxQ : xL ∈ (Q : Subgroup ↥L) := by
          rw [hQco]
          exact Subgroup.mem_subgroupOf.mpr hxU
        have hxcentQ : xL ∈ Subgroup.centralizer ((Q : Subgroup ↥L) : Set ↥L) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hyU : (y : G) ∈ U := by
            have hy' : y ∈ U.subgroupOf L := by rwa [← hQco]
            exact Subgroup.mem_subgroupOf.mp hy'
          exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxcent) (y : G) hyU)
        exact Subgroup.mem_map.mpr ⟨xL, Subgroup.mem_inf.mpr ⟨hxQ, hxcentQ⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨hyQ, hycent⟩ := Subgroup.mem_inf.mp hy
        have hyU : (y : G) ∈ U := by
          have hy' : y ∈ U.subgroupOf L := by rwa [← hQco]
          exact Subgroup.mem_subgroupOf.mp hy'
        refine Subgroup.mem_inf.mpr ⟨hyU, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have huQ : (⟨u, hUL hu⟩ : ↥L) ∈ (Q : Subgroup ↥L) := by
          rw [hQco]
          exact Subgroup.mem_subgroupOf.mpr hu
        exact congrArg (fun z : ↥L => (z : G))
          ((Subgroup.mem_centralizer_iff.mp hycent) ⟨u, hUL hu⟩ huQ)
    exact hAroot.trans (by
      rw [hrootU]
      exact Subgroup.map_mono le_sup_left)
  have hKltH : K < H := by simpa [hH] using hKltL
  have hKM : K ≤ M := S.le_of_lt K hAK hKltH
  have hKML : K ≤ M ⊓ L := le_inf hKM hKleL
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := hKML.trans hMnormL
  have hKinf : K ⊓ U ≠ ⊥ := by
    intro hbot
    have hAle : A ≤ K ⊓ U := le_inf hAK hAUL
    exact S.ne_bot (le_bot_iff.mp (hAle.trans_eq hbot))
  have hBK : IsBenderGroup ↥K := IsBenderGroup.isPSL2 f hf (eK.symm.trans ψ)
  exact false_of_simple_le_normalizer_twoGroup
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hBK)
    (by
      obtain ⟨x, y, hxy⟩ :=
        CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hBK
      exact ⟨x, y, fun h => hxy ((commute_iff_eq x y).mpr h)⟩)
    hU2 hKN hKinf

end CFSG.LocalAnalysis.WeakClosure81

end
