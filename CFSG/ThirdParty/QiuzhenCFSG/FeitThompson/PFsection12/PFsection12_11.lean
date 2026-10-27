module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_10
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
# Peterfalvi, Section 12: Theorem (12.11)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.11) -/

/-- The source-data package for PF `(12.11)` implies the public complement and
containment conclusion. -/
public theorem theorem_12_11_of_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ)
    (hsrc : theorem_12_11_source_data M K K' P0 L H Ls x p)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (hfrob : Section7.frobeniusWithKernel L H) :
    section12ComplementIn M K (M ⊓ L) ∧
      M ⊓ L ≤ H :=
  hsrc h128 h129 hfrob

/-- Source leaf for PF `(12.11)`: the complement assertion and containment
`M ∩ L ≤ H` from `(12.9)` and `(12.10)`. -/
public theorem theorem_12_11_source_leaf
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ) :
    theorem_12_11_source_data M K K' P0 L H Ls x p := by
  classical
  intro h128 h129 hfrob
  have hTypeI : Section8.typeIDefinitionData L H :=
    theorem_12_10_typeI_reduction_source_leaf M K K' P0 L H Ls x p h128 h129
  rcases h128 with
    ⟨hp, _hbad, _hmin, hM, hK, hTypeIM, _hMsM, _hK', _hnoncyc,
      hP0Sylow⟩
  rcases h129 with
    ⟨hP0comm, hP0rank, hL, hH, hLs, hP0Ls, hxL,
      ⟨_hp', hxOmega, hxne⟩, hCKnot, hNxM, hCnotL⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hxP0 : x ∈ P0 := by
    rcases hxOmega with ⟨y, _hyOmega, hyx⟩
    have hyP0 : (y : G) ∈ P0 := y.property
    simpa using hyx ▸ hyP0
  have hLsEq : Ls = H := by
    rcases hLs with hEarly | hLate
    · exact hEarly.2
    · rcases hLate.1 with hIII | hIV
      · rcases Section8.theorem_8_8_typeIII_to_source_public
          (G := G) hL hH hIII with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeI)
      · rcases Section8.theorem_8_8_typeIV_to_source_public
          (G := G) hL hH hIV with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeI)
  have hxH : x ∈ H := by
    rw [← hLsEq]
    exact hP0Ls hxP0
  have hNotation :
      Section8.notation_8_10_source_data L H H
        (typeIASet L H) (typeIASet L H) (Section8.a1Set H) :=
    notation_8_10_source_data_of_typeI_msChoice L H hL hH hTypeI
      (Section8.msChoiceSource_of_typeIDefinitionData hTypeI)
  have hxA : x ∈ typeIASet L H :=
    ⟨hxL, hxne, x, hxH, hxne,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hCnotL' : ¬ Subgroup.centralizer ({x} : Set G) ≤ L := by
    simpa [elementCentralizerIn] using hCnotL
  have hxD : x ∈ Section8.section8DSet L (typeIASet L H) :=
    ⟨hxA, hCnotL'⟩
  have hC_le_N :
      Subgroup.centralizer ({x} : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using
      (centralizer_le_normalizer (Subgroup.zpowers x))
  have hMcont :
      M ∈ section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({x} : Set G)) :=
    ⟨hM, hC_le_N.trans hNxM⟩
  rcases
      ((Section8.theorem_8_13 (G := G) L H H
        (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
        (typeIASet L H)) inferInstance hNotation (Or.inl rfl)).2.2.2
        x hxD M hMcont with
    ⟨LF, hSupp⟩
  have hLFK : LF = K := section16MFSubgroup_unique hSupp.2.1 hK
  have hcomp : section12ComplementIn M LF (L ⊓ M) := hSupp.2.2.2.1.1
  have hcompK : section12ComplementIn M K (M ⊓ L) := by
    simpa [hLFK, inf_comm] using hcomp
  constructor
  · exact hcompK
  · have hHleL : H ≤ L := section16MFSubgroup_le hH
    have hP0H : P0 ≤ H := by
      rw [← hLsEq]
      exact hP0Ls
    rcases hP0Sylow with ⟨PM, hP0eq⟩
    have hP0M : P0 ≤ M := by
      rw [← hP0eq]
      exact section11_ambientSylow_le M PM
    have hP0p : IsPGroup p P0 := by
      rw [← hP0eq]
      dsimp [section10AmbientSylowSubgroup]
      exact IsPGroup.map (p := p) (H := (PM : Subgroup M)) PM.isPGroup' M.subtype
    let ML : Subgroup L := (M ⊓ L).subgroupOf L
    have hMLpi : IsPiSubgroup (G := L) (subgroupPrimeSet H) ML := by
      intro q hqML
      haveI : Fact q.val.Prime := ⟨q.property⟩
      rcases exists_prime_orderOf_dvd_card' (G := ML) q.val hqML with
        ⟨zML, hzMLorder⟩
      let z : G := zML
      have hzML : z ∈ M ⊓ L := zML.property
      have hzorder : orderOf z = q.val := by
        simpa [z, Subgroup.orderOf_coe] using hzMLorder
      have hzne : z ≠ 1 := by
        intro hz
        have : q.val = 1 := by rw [← hzorder, hz, orderOf_one]
        exact q.property.ne_one this
      let A : Subgroup G := Subgroup.zpowers z
      have hAcard : Nat.card A = q.val := by
        simpa [A, hzorder] using Nat.card_zpowers z
      have hA_ML : A ≤ M ⊓ L :=
        Subgroup.zpowers_le.mpr hzML
      by_contra hqH
      have hqnotH : q ∉ subgroupPrimeSet H := hqH
      let P : Subgroup G := (pCore p H).map H.subtype
      let P0H : Subgroup H := P0.subgroupOf H
      have hP0Hp : IsPGroup p P0H :=
        hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0H).symm
      have hP0H_le_core : P0H ≤ pCore p H := by
        obtain ⟨S, hP0H_le_S⟩ :=
          IsPGroup.exists_le_sylow (G := H) (p := p) hP0Hp
        have hSnormal : (S : Subgroup H).Normal :=
          Group.IsNilpotent.sylow_normal hH.1.2.2.1 p S
        exact hP0H_le_S.trans (le_sSup ⟨hSnormal, S.isPGroup'⟩)
      have hP0P : P0 ≤ P := by
        intro y hy
        exact Subgroup.mem_map.mpr
          ⟨⟨y, hP0H hy⟩, hP0H_le_core (by
            simpa [P0H, Subgroup.mem_subgroupOf] using hy), rfl⟩
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
      haveI : (pCore p H).Characteristic :=
        pCore_characteristic (G := H) (p := p)
      have hLnormH : L ≤ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hHleL).1
          (section16MFSubgroup_subgroupOf_normal hH)
      have hNormHleP :
          Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (P : Set G) := by
        simpa [P] using
          (section8_normalizer_map_subtype_le_of_characteristic
            (G := G) (H := H) (K := pCore p H))
      have hA_norm_P : A ≤ Subgroup.normalizer (P : Set G) :=
        (hA_ML.trans inf_le_right).trans (hLnormH.trans hNormHleP)
      have hA_norm_M : A ≤ Subgroup.normalizer (M : Set G) :=
        (hA_ML.trans inf_le_left).trans Subgroup.le_normalizer
      have hA_norm_P0 : A ≤ Subgroup.normalizer (P0 : Set G) := by
        rw [← hPinfM]
        exact (le_inf hA_norm_P hA_norm_M).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hcopHA : Nat.Coprime (Nat.card H) (Nat.card A) := by
        rw [hAcard]
        exact (prime_coprime_card_of_not_mem_subgroupPrimeSet
          q.property hqnotH).symm
      have hdisjHA : Disjoint H A := by
        rw [Subgroup.disjoint_def]
        intro y hyH hyA
        apply orderOf_eq_one_iff.mp
        exact Nat.eq_one_of_dvd_coprimes hcopHA
          (Subgroup.orderOf_dvd_natCard H hyH)
          (Subgroup.orderOf_dvd_natCard A hyA)
      have hdisjP0A : Disjoint P0 A := hdisjHA.mono hP0H le_rfl
      let S : Subgroup G := P0 ⊔ A
      have hcompP0A : section12ComplementIn S P0 A :=
        ⟨le_sup_left, le_sup_right, rfl, hdisjP0A⟩
      have hP0ne : P0 ≠ ⊥ := by
        intro hbot
        have hcyc : IsCyclic P0 := by rw [hbot]; infer_instance
        letI : IsCyclic P0 := hcyc
        have hrank : groupRank P0 ≤ 1 := groupRank_le_one_of_isCyclic P0
        omega
      have hAne : A ≠ ⊥ := by
        intro hbot
        have hzA : z ∈ A := by exact Subgroup.mem_zpowers z
        have hzbot : z ∈ (⊥ : Subgroup G) := hbot ▸ hzA
        exact hzne (Subgroup.mem_bot.mp hzbot)
      have hP0normalS : (P0.subgroupOf S).Normal := by
        rw [show S = A ⊔ P0 by simp [S, sup_comm]]
        exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := A) (N := P0) hA_norm_P0
      have hcompLocal :
          (P0.subgroupOf S).IsComplement' (A.subgroupOf S) :=
        section12ComplementIn_left_normal_isComplement' hcompP0A hP0normalS
      have hP0locne : P0.subgroupOf S ≠ ⊥ := by
        intro hbot
        apply hP0ne
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        have hyS : y ∈ S := (show P0 ≤ S from le_sup_left) hy
        have hyloc : (⟨y, hyS⟩ : S) ∈ P0.subgroupOf S := hy
        have : (⟨y, hyS⟩ : S) = 1 :=
          Subgroup.mem_bot.mp (by simpa [hbot] using hyloc)
        exact congrArg Subtype.val this
      have hAlocne : A.subgroupOf S ≠ ⊥ := by
        intro hbot
        apply hAne
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        have hyS : y ∈ S := (show A ≤ S from le_sup_right) hy
        have hyloc : (⟨y, hyS⟩ : S) ∈ A.subgroupOf S := hy
        have : (⟨y, hyS⟩ : S) = 1 :=
          Subgroup.mem_bot.mp (by simpa [hbot] using hyloc)
        exact congrArg Subtype.val this
      have hfrob6 : Section6.frobeniusWithKernel L H := by
        simpa [Section6.frobeniusWithKernel, Section7.frobeniusWithKernel] using hfrob
      have hcentP0A :
          ∀ a : A.subgroupOf S, a ≠ 1 →
            elementCentralizerIn (P0.subgroupOf S) (a : S) = ⊥ := by
        intro a hane
        have haA : ((a : S) : G) ∈ A := a.property
        have haL : ((a : S) : G) ∈ L :=
          (hA_ML.trans inf_le_right) haA
        have hanotH : ((a : S) : G) ∉ H := by
          intro haH
          have haone : ((a : S) : G) = 1 :=
            Subgroup.disjoint_def.mp hdisjHA haH haA
          exact hane (Subtype.ext (Subtype.ext haone))
        have hcentH :
            Section2.centralizerIn H ((a : S) : G) = ⊥ :=
          Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
            hfrob6 ((a : S) : G) haL hanotH
        apply le_antisymm
        · intro y hy
          have hyH : ((y : S) : G) ∈ H := hP0H hy.1
          have hycent :
              ((y : S) : G) ∈
                Subgroup.centralizer ({((a : S) : G)} : Set G) := by
            exact Subgroup.mem_centralizer_singleton_iff.mpr
              (congrArg Subtype.val
                (Subgroup.mem_centralizer_singleton_iff.mp hy.2))
          have hybot : ((y : S) : G) ∈ (⊥ : Subgroup G) := by
            simpa [hcentH] using (show ((y : S) : G) ∈
              Section2.centralizerIn H ((a : S) : G) from ⟨hyH, hycent⟩)
          exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hybot))
        · exact bot_le
      have hfrobP0A : section12FrobeniusJoinWithKernel P0 A := by
        rw [section12FrobeniusJoinWithKernel, ← hcompP0A.2.2.1]
        exact (lemma_3_1 (P0.subgroupOf S) (A.subgroupOf S)
          hP0locne hAlocne hP0normalS hcompLocal).2 hcentP0A
      have hKnormal : (K.subgroupOf M).Normal :=
        section16MFSubgroup_subgroupOf_normal hK
      have hcompKLocal :
          (K.subgroupOf M).IsComplement' ((M ⊓ L).subgroupOf M) :=
        section12ComplementIn_left_normal_isComplement' hcompK hKnormal
      have hcopKE :
          Nat.Coprime (Nat.card K) (Nat.card (M ⊓ L : Subgroup G)) := by
        have hcopLocal :=
          (section16MFSubgroup_subgroupOf_isHall hK).card_coprime_index
        have hcardK : Nat.card (K.subgroupOf M) = Nat.card K :=
          natCard_subgroupOf_eq K M hcompK.1
        have hcardE :
            Nat.card ((M ⊓ L : Subgroup G).subgroupOf M) =
              Nat.card (M ⊓ L : Subgroup G) :=
          natCard_subgroupOf_eq (M ⊓ L) M hcompK.2.1
        rw [← hcardK, ← hcardE]
        rw [← hcompKLocal.symm.index_eq_card]
        exact hcopLocal
      have hS_ML : S ≤ M ⊓ L :=
        sup_le (le_inf hP0M (hP0H.trans hHleL)) hA_ML
      have hcopKS : Nat.Coprime (Nat.card K) (Nat.card S) :=
        hcopKE.of_dvd_right (Subgroup.card_dvd_of_le hS_ML)
      have hS_norm_K : S ≤ Subgroup.normalizer (K : Set G) := by
        have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer
            (section16MFSubgroup_le hK)).1 hKnormal
        exact hS_ML.trans (inf_le_left.trans hMnormK)
      have hKsolv : IsSolvable K := by
        letI : Group.IsNilpotent K := hK.1.2.2.1
        exact IsNilpotent.to_isSolvable
      have haction : Section9.frobeniusActionData S P0 A K :=
        ⟨hcompP0A, hfrobP0A, hS_norm_K, hKsolv, hcopKS⟩
      rcases hTypeIM with ⟨U, U1, U0, hF, _hTypeICases⟩
      have hcompULocal :
          (K.subgroupOf M).IsComplement' (U.subgroupOf M) :=
        section12ComplementIn_left_normal_isComplement' hF.2.2.2.2.2.2.1 hKnormal
      have hKHall := section16MFSubgroup_subgroupOf_isHall hK
      have hUHall :
          IsHallSubgroup (subgroupPrimeSet K)ᶜ (U.subgroupOf M) :=
        section16_complement_isHall_compl_of_isHall hKHall hcompULocal
      have hEHall :
          IsHallSubgroup (subgroupPrimeSet K)ᶜ ((M ⊓ L).subgroupOf M) :=
        section16_complement_isHall_compl_of_isHall hKHall hcompKLocal
      obtain ⟨d, hd⟩ :=
        exists_conj_eq_of_isHallSubgroup_of_solvable hF.1 hUHall hEHall
      have hEeq : M ⊓ L = U.conjBy (d : G) :=
        section16_eq_conjBy_of_subgroupOf_map_conj
          hF.2.2.2.2.2.2.1.2.1 hcompK.2.1 hd
      have hMnormK : M ≤ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (section16MFSubgroup_le hK)).1 hKnormal
      have hMconj : M.conjBy (d : G)⁻¹ = M :=
        section11_conjBy_eq_of_mem_normalizer
          (Subgroup.le_normalizer (M.inv_mem d.property))
      have hKconj : K.conjBy (d : G)⁻¹ = K :=
        section11_conjBy_eq_of_mem_normalizer
          ((Subgroup.normalizer (K : Set G)).inv_mem (hMnormK d.property))
      have hFconj :
          Section8.typeFData (M.conjBy (d : G)⁻¹) (K.conjBy (d : G)⁻¹)
            U U1 U0 := by
        simpa [hMconj, hKconj] using hF
      have hFback :=
        Section8.theorem_8_18_typeFData_conj_back (G := G) (d : G)⁻¹ hFconj
      have hFE :
          Section8.typeFData M K (M ⊓ L)
            (U1.conjBy (d : G)) (U0.conjBy (d : G)) := by
        simpa [hEeq] using hFback
      let P1 : Subgroup G := section12OmegaOneSubgroup ⟨p, hp⟩ P0
      have hP1elem : IsElementaryAbelian p P1 := by
        simpa [P1] using
          (theorem_12_9_omega_one_noncyclic P0 p hp hP0p hP0comm hP0rank).1
      letI : IsElementaryAbelian p P1 := hP1elem
      have hxpowP1 : (⟨x, by simpa [P1] using hxOmega⟩ : P1) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p P1) _
      have hxpow : x ^ p = 1 := congrArg Subtype.val hxpowP1
      have hxorder : orderOf x = p := orderOf_eq_prime hxpow hxne
      have hxE : x ∈ M ⊓ L := ⟨hP0M hxP0, hxL⟩
      have hpExpE : p ∣ Monoid.exponent (M ⊓ L : Subgroup G) := by
        rw [← hxorder]
        simpa [Subgroup.orderOf_coe] using
          (Monoid.order_dvd_exponent (⟨x, hxE⟩ : (M ⊓ L : Subgroup G)))
      have hFEcopy := hFE
      rcases hFEcopy with
        ⟨_hMsolv, _hModd, _hKdata, hKpos, _hKlt, _hEne, _hcompE,
          hE1le, hE1comm, _hE1norm, hcentE1, hE0le, hExpE0, hfrobKE0⟩
      let E1 : Subgroup G := U1.conjBy (d : G)
      let E0 : Subgroup G := U0.conjBy (d : G)
      have hpExpE0 : p ∣ Monoid.exponent E0 := by
        rw [hExpE0]
        exact hpExpE
      have hpCardE0 : p ∣ Nat.card E0 :=
        hpExpE0.trans (Group.exponent_dvd_nat_card (G := E0))
      rcases exists_prime_orderOf_dvd_card' (G := E0) p hpCardE0 with
        ⟨tE0, htorder⟩
      let t : G := tE0
      have htE0 : t ∈ E0 := tE0.property
      have htorderG : orderOf t = p := by
        simpa [t, Subgroup.orderOf_coe] using htorder
      have htne : t ≠ 1 := by
        intro ht
        have : p = 1 := by rw [← htorderG, ht, orderOf_one]
        exact hp.ne_one this
      let Q : Subgroup G := Subgroup.zpowers t
      have hQE0 : Q ≤ E0 := Subgroup.zpowers_le.mpr htE0
      have hQcard : Nat.card Q = p := by
        simpa [Q, htorderG] using Nat.card_zpowers t
      have hQp : IsPGroup p Q := by
        refine IsPGroup.of_card (p := p) (G := Q) (n := 1) ?_
        simpa [pow_one] using hQcard
      have hQne : Q ≠ ⊥ := by
        intro hbot
        have htbot : t ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers t
        exact htne (Subgroup.mem_bot.mp htbot)
      have hQM : Q ≤ M := hQE0.trans (hE0le.trans inf_le_left)
      let Qsub : Subgroup M := Q.subgroupOf M
      have hQsubp : IsPGroup p Qsub :=
        hQp.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M) hQM).symm
      obtain ⟨SQ, hQsubSQ⟩ :=
        IsPGroup.exists_le_sylow (G := M) (p := p) hQsubp
      obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M SQ PM
      have hQsubConjPM : Qsub.conjBy m ≤ (PM : Subgroup M) := by
        calc
          Qsub.conjBy m ≤ (SQ : Subgroup M).conjBy m :=
            section10_conjBy_mono hQsubSQ m
          _ = ((m • SQ : Sylow p M) : Subgroup M) := by
            rw [section10_sylow_smul_coe_eq_conjBy]
          _ = (PM : Subgroup M) := by rw [hm]
      have hQconjP0 : Q.conjBy (m : G) ≤ P0 := by
        calc
          Q.conjBy (m : G) = (Qsub.conjBy m).map M.subtype := by
            symm
            exact section10_subgroupOf_conjBy_map_subtype hQM m
          _ ≤ (PM : Subgroup M).map M.subtype :=
            Subgroup.map_mono hQsubConjPM
          _ = P0 := by simpa [section10AmbientSylowSubgroup] using hP0eq
      have hP0notCentK : ¬ P0 ≤ Subgroup.centralizer (K : Set G) := by
        intro hP0centK
        have hQconjCentK :
            Q.conjBy (m : G) ≤ Subgroup.centralizer (K : Set G) :=
          hQconjP0.trans hP0centK
        have hmNormK : (m : G) ∈ Subgroup.normalizer (K : Set G) :=
          hMnormK m.property
        have hQcentK : Q ≤ Subgroup.centralizer (K : Set G) := by
          intro y hyQ
          have hyConj :
              (m : G) * y * (m : G)⁻¹ ∈ Q.conjBy (m : G) := by
            rw [Subgroup.conjBy, Subgroup.mem_map]
            exact ⟨y, hyQ, rfl⟩
          have hyConjCent := hQconjCentK hyConj
          have hyBack := section10_centralizer_conj_mem_of_mem_normalizer
            ((Subgroup.normalizer (K : Set G)).inv_mem hmNormK) hyConjCent
          simpa [mul_assoc] using hyBack
        have htCentK : t ∈ Subgroup.centralizer (K : Set G) :=
          hQcentK (Subgroup.mem_zpowers t)
        let SKE : Subgroup G := K ⊔ E0
        let Ksub : Subgroup SKE := K.subgroupOf SKE
        let E0sub : Subgroup SKE := E0.subgroupOf SKE
        have hFrobKE0 : IsFrobeniusGroupWithKernelComplement Ksub E0sub := by
          simpa [section12FrobeniusJoinWithKernel, SKE, Ksub, E0sub] using
            hfrobKE0
        have hcentLocal :
            ∀ a : E0sub, a ≠ 1 →
              elementCentralizerIn Ksub (a : SKE) = ⊥ :=
          (lemma_3_1 (G := SKE) Ksub E0sub hFrobKE0.kernel_ne_bot
            hFrobKE0.complement_ne_bot hFrobKE0.normal
            hFrobKE0.isComplement').1 hFrobKE0
        have htSKE : t ∈ SKE := Subgroup.mem_sup_right htE0
        let tSKE : SKE := ⟨t, htSKE⟩
        have htE0sub : tSKE ∈ E0sub := by
          simpa [E0sub, Subgroup.mem_subgroupOf, tSKE] using htE0
        let tE0sub : E0sub := ⟨tSKE, htE0sub⟩
        have htE0subne : tE0sub ≠ 1 := by
          intro htone
          apply htne
          simpa [tE0sub, tSKE] using
            congrArg (fun a : E0sub => ((a : SKE) : G)) htone
        apply hFrobKE0.kernel_ne_bot
        rw [Subgroup.eq_bot_iff_forall]
        intro y hyKsub
        have hyK : ((y : SKE) : G) ∈ K := by
          simpa [Ksub, Subgroup.mem_subgroupOf] using hyKsub
        have hyCent :
            y ∈ Subgroup.centralizer ({(tE0sub : SKE)} : Set SKE) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          simpa [tE0sub, tSKE] using
            (Subgroup.mem_centralizer_iff.mp htCentK _ hyK)
        have hyLocal : y ∈ elementCentralizerIn Ksub (tE0sub : SKE) :=
          ⟨hyKsub, hyCent⟩
        have hyBot : y ∈ (⊥ : Subgroup SKE) := by
          simpa [hcentLocal tE0sub htE0subne] using hyLocal
        exact Subgroup.mem_bot.mp hyBot
      have hCKAne : subgroupCentralizerIn K A ≠ ⊥ := by
        intro hCKAbot
        have h91 := Section9.theorem_9_1 S P0 A K haction
        have hCKP0 : subgroupCentralizerIn K P0 = K := h91.2.1 hCKAbot
        apply hP0notCentK
        apply (Subgroup.le_centralizer_iff (H := K) (K := P0)).mp
        intro y hyK
        have hyCKP0 : y ∈ subgroupCentralizerIn K P0 := by
          rw [hCKP0]
          exact hyK
        exact hyCKP0.2
      haveI : Nontrivial (subgroupCentralizerIn K A) :=
        (Subgroup.nontrivial_iff_ne_bot (subgroupCentralizerIn K A)).2 hCKAne
      obtain ⟨yKA, hyKAne⟩ := exists_ne (1 : subgroupCentralizerIn K A)
      let y : G := yKA
      have hyK : y ∈ K := yKA.property.1
      have hyCentA : y ∈ Subgroup.centralizer (A : Set G) := yKA.property.2
      have hyne : y ≠ 1 := by
        intro hyone
        apply hyKAne
        exact Subtype.ext hyone
      have hA_E1 : A ≤ E1 := by
        have hAcentY : A ≤ elementCentralizerIn (M ⊓ L) y := by
          intro a haA
          refine ⟨hA_ML haA, ?_⟩
          change a ∈ Subgroup.centralizer ({y} : Set G)
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hyCentA a haA
        exact hAcentY.trans (by simpa [E1] using hcentE1 y hyK hyne)
      obtain ⟨w, hwCent, hwnotK'⟩ := Set.not_subset.mp hCKnot
      have hwne : w ≠ 1 := by
        intro hwone
        apply hwnotK'
        simp [hwone]
      have hxCentW : x ∈ elementCentralizerIn (M ⊓ L) w := by
        refine ⟨hxE, ?_⟩
        change x ∈ Subgroup.centralizer ({w} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hwCent.2).symm
      have hwCentE1 : elementCentralizerIn (M ⊓ L) w ≤ E1 := by
        simpa [E1] using hcentE1 w hwCent.1 hwne
      have hxE1 : x ∈ E1 := hwCentE1 hxCentW
      have hAcentX : A ≤ Subgroup.centralizer ({x} : Set G) := by
        intro a haA
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact setLike_mul_comm
          (s := E1) (hA_E1 haA) hxE1
      have hzA : z ∈ A := Subgroup.mem_zpowers z
      have hznotH : z ∉ H := by
        intro hzH
        exact hzne (Subgroup.disjoint_def.mp hdisjHA hzH hzA)
      have hcentHz : Section2.centralizerIn H z = ⊥ :=
        Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
          hfrob6 z (hA_ML.trans inf_le_right hzA) hznotH
      have hxCentZ : x ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hAcentX hzA)).symm
      have hxBot : x ∈ (⊥ : Subgroup G) := by
        simpa [hcentHz] using
          (show x ∈ Section2.centralizerIn H z from ⟨hxH, hxCentZ⟩)
      exact hxne (Subgroup.mem_bot.mp hxBot)
    haveI : (H.subgroupOf L).Normal :=
      section16MFSubgroup_subgroupOf_normal hH
    have hMLle : ML ≤ H.subgroupOf L :=
      section12_piSubgroup_le_normal_hall
        (section16MFSubgroup_subgroupOf_isHall hH) hMLpi
    intro y hy
    let yL : L := ⟨y, hy.2⟩
    have hyML : yL ∈ ML := by
      simpa [ML, yL, Subgroup.mem_subgroupOf] using hy.1
    exact hMLle hyML

/-- Peterfalvi `(12.11)`.

`M ∩ L` is a complement of `K` in `M` and `M ∩ L ⊂ H`. -/
public theorem theorem_12_11
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p)
    (hfrob : Section7.frobeniusWithKernel L H) :
    section12ComplementIn M K (M ⊓ L) ∧
      M ⊓ L ≤ H := by
  exact theorem_12_11_of_source_data M K K' P0 L H Ls x p
    (theorem_12_11_source_leaf M K K' P0 L H Ls x p) h128 h129 hfrob

end CFSG.Section12
