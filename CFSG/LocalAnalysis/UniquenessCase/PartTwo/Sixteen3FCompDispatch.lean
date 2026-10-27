module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeComp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen3FCompNaturalThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen3FCompIrreducible
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTwoAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSolvableRowReduction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNonthinComponentCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem false_of_isComponentOf_sup_of_distinct_components
    {X : Type*} [Group X] [Finite X] {A L K K' : Subgroup X}
    (hL : CFSG.Open.IsComponentOf L A)
    (hK : CFSG.Open.IsComponentOf K A)
    (hK' : CFSG.Open.IsComponentOf K' A)
    (hne : K ≠ K')
    (hEq : L = K ⊔ K') : False := by
  have hKL : K ≤ L := by
    rw [hEq]
    exact le_sup_left
  have hK'L : K' ≤ L := by
    rw [hEq]
    exact le_sup_right
  have hKsub : CFSG.IsComponent (K.subgroupOf A) :=
    CFSG.Quasithin.F918V5G.isComponent_subgroupOf hK
  have hK'sub : CFSG.IsComponent (K'.subgroupOf A) :=
    CFSG.Quasithin.F918V5G.isComponent_subgroupOf hK'
  have hLsub : CFSG.IsComponent (L.subgroupOf A) :=
    CFSG.Quasithin.F918V5G.isComponent_subgroupOf hL
  have hKLe : K.subgroupOf A ≤ L.subgroupOf A := by
    intro x hx
    exact hKL hx
  have hK'Le : K'.subgroupOf A ≤ L.subgroupOf A := by
    intro x hx
    exact hK'L hx
  have hKeq : K.subgroupOf A = L.subgroupOf A :=
    CFSG.Quasithin.C2Push.eq_of_isComponent_of_le hKsub hLsub hKLe
  have hK'eq : K'.subgroupOf A = L.subgroupOf A :=
    CFSG.Quasithin.C2Push.eq_of_isComponent_of_le hK'sub hLsub hK'Le
  have hKmap : (K.subgroupOf A).map A.subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hK.1]
  have hK'map : (K'.subgroupOf A).map A.subtype = K' := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hK'.1]
  have hLmap : (L.subgroupOf A).map A.subtype = L := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hL.1]
  have hK_eq_L : K = L := by
    rw [← hKmap, hKeq, hLmap]
  have hK'_eq_L : K' = L := by
    rw [← hK'map, hK'eq, hLmap]
  exact hne (hK_eq_L.trans hK'_eq_L.symm)

theorem r16_3FComp_of_std_of_r880_of_alt67_three
    (D : Data G)
    (hstd : S168e3Std D)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hAlt3 :
      ∀ {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
        (_c : S168e3Ctx D V₀ V L hV)
        (_hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
        (_hs : s15 D.M V₀ V hV L = 2)
        {n : ℕ} (_hn : n = 6 ∨ n = 7)
        (_hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
        (_hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
          (lBar V₀ V hV L) (wTil V₀ V hV L)
          (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
        (_htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
          ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
          ∃ g ∈ Mbar D.M V₀ V hV ⊓
            normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
            I₂ = I₁.map g.toMonoidHom),
        Concl163F D V₀ V hV L) :
    R16_3FComp D := by
  intro V₀ V L hV hSetting hConc hs hcomp hodd
  have hlbar_ne : barSub V₀ V hV L ≠ ⊥ := by
    have hqN : CFSG.IsQuasisimple ↥(lBar V₀ V hV L) :=
      (CFSG.Quasithin.A3.isQuasisimple_iff_open
        (Q := ↥(lBar V₀ V hV L))).mpr hcomp.2.2
    have hnt : Nontrivial ↥(lBar V₀ V hV L) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hqN
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt
  have c : S168e3Ctx D V₀ V L hV := ⟨hstd, hSetting, hlbar_ne, hConc⟩
  obtain ⟨t, htmem, ht2, htne, htrk, h136W⟩ := hConc
  rcases h136W with ⟨hspan, hconj, hbranch⟩
  rcases hbranch with h133 | hprod | hnat | hirr
  ·
    rcases concl163F_or_cyclic_three_rank_six_s1_of_conc4_133 c h133 with h | ⟨-, -, hs1⟩
    · exact h
    · exact False.elim (by omega)
  ·
    rcases hprod with ⟨K, hK, g, hg, hKgne, hEq, -⟩
    have hKg : IsComponentOf (K.map (MulAut.conj g).toMonoidHom)
        (Mbar D.M V₀ V hV) :=
      CFSG.Quasithin.F918V5G.isComponentOf_map_conj hK hg
    exact (false_of_isComponentOf_sup_of_distinct_components hcomp hK hKg hKgne hEq).elim
  ·
    rcases hnat with ⟨-, hsum3, htrans⟩
    rcases (sumOfAtMostThreeNat_iff (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))).mp hsum3 with ⟨k, hk3, hshape⟩
    have hkpos : 1 ≤ k := by
      by_contra hk
      have hk0 : k = 0 := by omega
      subst k
      have hUZ : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) =
          commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
            fixV (lBar V₀ V hV L) := by
        rcases hshape with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
        · exact s16k_sumOfNat_zero hSL.2
        · exact s16k_sumOfNat_zero hSp.2
        · exact s16k_sumOfNat_zero hOp.2
        · exact s16k_sumOfNat_zero hOm.2
        · exact s16k_sumOfNat_zero hAlt.2
      have hle : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ≤
          fixV (lBar V₀ V hV L) := by
        rw [hUZ]
        exact inf_le_right
      have hperf : Group.IsPerfect ↥(lBar V₀ V hV L) :=
        Group.isPerfect_def.mpr hcomp.2.2.1
      have hEq : commSub (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
          (lBar V₀ V hV L) =
          commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) :=
        s16jp_commSub_commSub (L := lBar V₀ V hV L) hperf
          (fun l _ y _ => Subgroup.mem_top (l y))
      have hbot : commSub (commSub (⊤ : Subgroup (Vtil V₀ V hV))
          (lBar V₀ V hV L)) (lBar V₀ V hV L) = ⊥ :=
        CFSG.Quasithin.commSub_eq_bot_iff.mpr hle
      rw [hEq] at hbot
      exact (s16_LemmaP_commSub_ne_bot hlbar_ne) hbot
    interval_cases k
    · exact s168e3_concl163F_of_sumOfNatShape_one c h880 hcomp hs hodd hshape
    · exact s168e3_concl163F_of_sumOfNatShape_two c hcomp hshape
    · have hs2 : s15 D.M V₀ V hV L = 2 :=
        s168e3_s_eq_two_of_nonThin_component c hcomp hs hodd
      exact s168e3_concl163F_of_sumOfNatShape_three_of_alt67_three
        c hcomp hs2 hodd hshape htrans hAlt3
  ·
    rcases hirr with ⟨hirr_mem, ht, -, h135⟩
    let m : ℕ := E3.mQuot
      (commSub (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
          (Subgroup.zpowers t) ⊔
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
          fixV (lBar V₀ V hV L)))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))
    have hm : m = E3.mQuot
      (commSub (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
          (Subgroup.zpowers t) ⊔
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
          fixV (lBar V₀ V hV L)))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) := rfl
    have hm3 : m ≤ 3 := by
      have hle := s16k_mQuot_le_rk V₀ V hV
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
          fixV (lBar V₀ V hV L)) t
      exact hle.trans htrk
    exact s16k_concl163F_of_irr_sameL c h880 hcomp hs hodd ht hirr_mem
      m hm hm3 h135

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
