module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection10.PFsection10_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection11.PFsection11_9

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_1
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.1) -/


private noncomputable def section13_pointedFinEquiv
    (n : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
    (hn : 0 < n) (hcard : Fintype.card I = n) (i0 : I) :
    Fin n ≃ I := by
  classical
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  exact (Equiv.swap ⟨0, hn⟩ (e.symm i0)).trans e

private theorem section13_pointedFinEquiv_zero
    (n : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
    (hn : 0 < n) (hcard : Fintype.card I = n) (i0 : I) :
    section13_pointedFinEquiv n I hn hcard i0 ⟨0, hn⟩ = i0 := by
  classical
  simp [section13_pointedFinEquiv]

private theorem section13_notation_3_3_reindex
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G}
    {I J I' J' : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype I'] [Fintype J'] [DecidableEq I'] [DecidableEq J']
    {i0 : I} {j0 : J} {i0' : I'} {j0' : J'}
    {ω : I → J → Section1.ClassFunction W}
    (eI : I' ≃ I) (eJ : J' ≃ J)
    (hi0 : eI i0' = i0) (hj0 : eJ j0' = j0)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    Section3.notation_3_3_statement W1 W2 W I' J' i0' j0'
      (fun i j => ω (eI i) (eJ j)) := by
  classical
  change Section3.OmegaSystem W1 W2 W I J i0 j0 ω at hω
  change Section3.OmegaSystem W1 W2 W I' J' i0' j0'
    (fun i j => ω (eI i) (eJ j))
  refine
    { card_left := ?_
      card_right := ?_
      principal := ?_
      left_kernel := ?_
      right_kernel := ?_
      left_kernel_exact := ?_
      right_kernel_exact := ?_
      product := ?_
      degree_one := ?_
      is_class := ?_
      irreducible := ?_
      orthonormal := ?_
      pairwise_eq := ?_
      all_irreducibles := ?_ }
  · exact (Fintype.card_congr eI).trans hω.card_left
  · exact (Fintype.card_congr eJ).trans hω.card_right
  · simpa [hi0, hj0] using hω.principal
  · intro i
    simpa [hj0] using hω.left_kernel (eI i)
  · intro j
    simpa [hi0] using hω.right_kernel (eJ j)
  · intro χ hχ
    constructor
    · intro hker
      rcases (hω.left_kernel_exact χ hχ).1 hker with ⟨i, hi⟩
      refine ⟨eI.symm i, ?_⟩
      simpa [hj0] using hi
    · rintro ⟨i, rfl⟩
      simpa [hj0] using hω.left_kernel (eI i)
  · intro χ hχ
    constructor
    · intro hker
      rcases (hω.right_kernel_exact χ hχ).1 hker with ⟨j, hj⟩
      refine ⟨eJ.symm j, ?_⟩
      simpa [hi0] using hj
    · rintro ⟨j, rfl⟩
      simpa [hi0] using hω.right_kernel (eJ j)
  · intro i j x
    simpa [hi0, hj0] using hω.product (eI i) (eJ j) x
  · intro i j
    exact hω.degree_one (eI i) (eJ j)
  · intro i j
    exact hω.is_class (eI i) (eJ j)
  · intro i j
    exact hω.irreducible (eI i) (eJ j)
  · intro p q
    have hbase := hω.orthonormal (eI p.1, eJ p.2) (eI q.1, eJ q.2)
    by_cases hpq : p = q
    · simp [hpq] at hbase ⊢
      exact hbase
    · have hne : (eI p.1, eJ p.2) ≠ (eI q.1, eJ q.2) := by
        intro h
        apply hpq
        exact Prod.ext (eI.injective (congrArg Prod.fst h))
          (eJ.injective (congrArg Prod.snd h))
      simp [hpq, hne] at hbase ⊢
      exact hbase
  · intro i i' j j' hij
    have hpair := hω.pairwise_eq hij
    exact ⟨eI.injective hpair.1, eJ.injective hpair.2⟩
  · intro χ hχ
    rcases hω.all_irreducibles χ hχ with ⟨i, j, hij⟩
    refine ⟨eI.symm i, eJ.symm j, ?_⟩
    simpa using hij

public theorem section13_isInternalDirectProduct_of_section12InternalDirectProduct
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W) :
    Section2.IsInternalDirectProduct W W1 W2 := by
  classical
  rcases hprod with ⟨hW1le, hW2le, hW, hdisj, hcent⟩
  refine
    { left_le := hW1le
      right_le := hW2le
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro h hh k hk
    exact (Subgroup.mem_centralizer_iff.mp (hcent hh) k hk).symm
  · apply le_antisymm
    · intro x hx
      exact Subgroup.disjoint_def.mp hdisj hx.1 hx.2
    · exact bot_le
  · intro c hc
    let J : Subgroup G := W1 ⊔ W2
    have hW1_norm_W2 : W1 ≤ Subgroup.normalizer (W2 : Set G) :=
      hcent.trans (centralizer_le_normalizer W2)
    let W1J : Subgroup J := W1.subgroupOf J
    let W2J : Subgroup J := W2.subgroupOf J
    haveI : W2J.Normal := by
      simpa [J, W2J] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := W1) (N := W2) hW1_norm_W2)
    have hcJ : c ∈ J := by
      simpa [J, hW] using hc
    let cJ : J := ⟨c, hcJ⟩
    have htop : W1J ⊔ W2J = ⊤ := by
      calc
        W1J ⊔ W2J = J.subgroupOf J := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := W1) (A' := W2) (B := J)
            (by simp [J])
            (by simp [J])
        _ = ⊤ := by simp
    have hcSup : cJ ∈ W1J ⊔ W2J := by
      rw [htop]
      trivial
    rcases (Subgroup.mem_sup_of_normal_right (s := W1J) (t := W2J) (x := cJ)).1
        hcSup with
      ⟨aJ, haJ, bJ, hbJ, hprodJ⟩
    have haW1 : (aJ : G) ∈ W1 := by
      simpa [W1J, Subgroup.mem_subgroupOf] using haJ
    have hbW2 : (bJ : G) ∈ W2 := by
      simpa [W2J, Subgroup.mem_subgroupOf] using hbJ
    refine ⟨(aJ : G), haW1, (bJ : G), hbW2, ?_⟩
    have hval := congrArg (fun z : J => (z : G)) hprodJ
    simpa [cJ] using hval.symm

private theorem section13_setNormalizer_eq_subgroupNormalizer
    {G : Type u} [Group G] (A : Set G) :
    Section2.setNormalizer A = Subgroup.normalizer A := by
  ext g
  simp [Section2.setNormalizer, Section2.normalizesSet, Section2.conjBy,
    Subgroup.normalizer, iff_comm]

private theorem section13_normalizer_le_of_cyclic_subgroup
    {G : Type u} [Group G] [Finite G]
    {W W1 : Subgroup G} (hW1le : W1 ≤ W) (hWcyc : IsCyclic W) :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (W1 : Set G) := by
  classical
  have hW1_char : (W1.subgroupOf W).Characteristic := by
    haveI : IsCyclic W := hWcyc
    exact section12_subgroup_characteristic_of_cyclic (W1.subgroupOf W)
  have hle : Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (((W1.subgroupOf W).map W.subtype : Subgroup G) : Set G) := by
    letI : (W1.subgroupOf W).Characteristic := hW1_char
    exact section8_normalizer_map_subtype_le_of_characteristic
      (G := G) (H := W) (K := W1.subgroupOf W)
  have hmap_eq : ((W1.subgroupOf W).map W.subtype : Subgroup G) = W1 := by
    simpa using Subgroup.map_subgroupOf_eq_of_le hW1le
  simpa [hmap_eq] using hle

private theorem section13_normalizesSet_cyclicTISet_of_mem_normalizer
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G}
    (hW1le : W1 ≤ W) (hW2le : W2 ≤ W) (hWcyc : IsCyclic W)
    {g : G} (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    Section2.normalizesSet (Section3.cyclicTISet W1 W2 W) g := by
  classical
  have hgW1 : g ∈ Subgroup.normalizer (W1 : Set G) :=
    section13_normalizer_le_of_cyclic_subgroup hW1le hWcyc hgW
  have hgW2 : g ∈ Subgroup.normalizer (W2 : Set G) :=
    section13_normalizer_le_of_cyclic_subgroup hW2le hWcyc hgW
  have hnormW : Section2.normalizesSet (W : Set G) g := by
    have hgSet : g ∈ Section2.setNormalizer (W : Set G) := by
      simpa [section13_setNormalizer_eq_subgroupNormalizer] using hgW
    simpa [Section2.setNormalizer] using hgSet
  have hnormW1 : Section2.normalizesSet (W1 : Set G) g := by
    have hgSet : g ∈ Section2.setNormalizer (W1 : Set G) := by
      simpa [section13_setNormalizer_eq_subgroupNormalizer] using hgW1
    simpa [Section2.setNormalizer] using hgSet
  have hnormW2 : Section2.normalizesSet (W2 : Set G) g := by
    have hgSet : g ∈ Section2.setNormalizer (W2 : Set G) := by
      simpa [section13_setNormalizer_eq_subgroupNormalizer] using hgW2
    simpa [Section2.setNormalizer] using hgSet
  intro x
  constructor
  · intro hx
    rw [Section3.cyclicTISet_mem_iff] at hx ⊢
    refine ⟨(hnormW x).1 hx.1, ?_, ?_⟩
    · intro hxW1
      exact hx.2.1 ((hnormW1 x).2 hxW1)
    · intro hxW2
      exact hx.2.2 ((hnormW2 x).2 hxW2)
  · intro hx
    rw [Section3.cyclicTISet_mem_iff] at hx ⊢
    refine ⟨(hnormW x).2 hx.1, ?_, ?_⟩
    · intro hxW1
      exact hx.2.1 ((hnormW1 x).1 hxW1)
    · intro hxW2
      exact hx.2.2 ((hnormW2 x).1 hxW2)

private theorem section13_singleton_normalizer_conj_mem
    {G : Type u} [Group G] [Finite G] {b g x : G}
    (hx : x ∈ Subgroup.normalizer ({b} : Set G)) :
    Section2.conjBy g x ∈ Subgroup.normalizer ({Section2.conjBy g b} : Set G) := by
  classical
  refine Subgroup.mem_normalizer_fintype ?_
  intro y hy
  rw [Set.mem_singleton_iff] at hy ⊢
  subst y
  have hxnorm : ∀ n : G, n ∈ ({b} : Set G) ↔ x * n * x⁻¹ ∈ ({b} : Set G) := by
    simpa [Subgroup.normalizer] using hx
  have hxb : x * b * x⁻¹ = b := by
    have hmem : x * b * x⁻¹ ∈ ({b} : Set G) := (hxnorm b).1 (by simp)
    simpa using hmem
  unfold Section2.conjBy
  calc
    g * x * g⁻¹ * (g * b * g⁻¹) * (g * x * g⁻¹)⁻¹ =
        g * (x * b * x⁻¹) * g⁻¹ := by group
    _ = g * b * g⁻¹ := by rw [hxb]

private theorem section13_mem_normalizer_of_conjBy_mem_cyclicTISet
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G}
    (hnorm : ∀ W0 : Set G,
      W0.Nonempty →
        W0 ⊆ Section3.cyclicTISet W1 W2 W →
          Subgroup.normalizer W0 = W)
    {b g : G}
    (hbA : b ∈ Section3.cyclicTISet W1 W2 W)
    (hgbA : Section2.conjBy g b ∈ Section3.cyclicTISet W1 W2 W) :
    g ∈ Subgroup.normalizer (W : Set G) := by
  classical
  let B : Set G := {b}
  let C : Set G := {Section2.conjBy g b}
  have hBnorm : Subgroup.normalizer B = W := by
    apply hnorm B
    · exact ⟨b, by simp [B]⟩
    · intro x hx
      have hx_eq : x = b := by simpa [B] using hx
      simpa [hx_eq] using hbA
  have hCnorm : Subgroup.normalizer C = W := by
    apply hnorm C
    · exact ⟨Section2.conjBy g b, by simp [C]⟩
    · intro x hx
      have hx_eq : x = Section2.conjBy g b := by simpa [C] using hx
      simpa [hx_eq] using hgbA
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hxW
  have hxB : x ∈ Subgroup.normalizer B := by
    simpa [hBnorm] using hxW
  have hxC : Section2.conjBy g x ∈ Subgroup.normalizer C := by
    simpa [B, C] using section13_singleton_normalizer_conj_mem (g := g) hxB
  simpa [hCnorm, Section2.conjBy] using hxC

private theorem section13_cyclicTISet_nonempty_of_internalDirectProduct_ne_bot
    {G : Type u} [Group G]
    {W W1 W2 : Subgroup G}
    (hW : Section2.IsInternalDirectProduct W W1 W2)
    (hW1ne : W1 ≠ ⊥) (hW2ne : W2 ≠ ⊥) :
    (Section3.cyclicTISet W1 W2 W).Nonempty := by
  classical
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW1ne with ⟨x, hxne⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW2ne with ⟨y, hyne⟩
  refine ⟨(x : G) * (y : G), ?_⟩
  rw [Section3.cyclicTISet_mem_iff]
  refine ⟨W.mul_mem (hW.left_le x.property) (hW.right_le y.property), ?_, ?_⟩
  · intro hxyW1
    have hyW1 : (y : G) ∈ W1 := by
      have htmp : (x : G)⁻¹ * ((x : G) * (y : G)) ∈ W1 :=
        W1.mul_mem (W1.inv_mem x.property) hxyW1
      simpa [mul_assoc] using htmp
    have hybot : (y : G) ∈ W1 ⊓ W2 := ⟨hyW1, y.property⟩
    have hyEq1 : (y : G) = 1 := by
      have hyBot' : (y : G) ∈ (⊥ : Subgroup G) := by
        simpa [hW.inf_eq_bot] using hybot
      simpa using hyBot'
    exact hyne (Subtype.ext hyEq1)
  · intro hxyW2
    have hxW2 : (x : G) ∈ W2 := by
      have htmp : ((x : G) * (y : G)) * (y : G)⁻¹ ∈ W2 :=
        W2.mul_mem hxyW2 (W2.inv_mem y.property)
      simpa [mul_assoc] using htmp
    have hxbot : (x : G) ∈ W1 ⊓ W2 := ⟨x.property, hxW2⟩
    have hxEq1 : (x : G) = 1 := by
      have hxBot' : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hW.inf_eq_bot] using hxbot
      simpa using hxBot'
    exact hxne (Subtype.ext hxEq1)


private theorem hypothesis_13_1_typeP_induced_family_source
    {G : Type u} [Group G] [Finite G]
    {M MF U Wleft Wright : Subgroup G}
    (_hmin : IsMinCE G)
    (_hM : M ∈ section9MaximalSubgroups G)
    (hTypeP : Section8.typePData M MF U Wleft Wright) :
    ∃ Mfam : Finset (Section1.ClassFunction M),
        nonkernelInducedFamily M (MF ⊔ U) MF Mfam := by
  rcases hTypeP with ⟨_hMF, hCommon⟩
  rcases hCommon with
    ⟨_hHallD, _hMFleD, hCompMFU, _hUnil, _hWleftNorm, _hWleftCyc,
      _hWleftCard, _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hWrightLeMF, _hWrightNe, _hWrightCyc, _hCentralizer, _hHatW,
      _hT6, _hWrightSecond⟩
  have hDerEq : ambientDerivedSubgroup M = MF ⊔ U := hCompMFU.2.2.1
  have hHleM : MF ⊔ U ≤ M := by
    rw [← hDerEq]
    exact section12_ambientDerivedSubgroup_le
  exact exists_nonkernelInducedFamily M (MF ⊔ U) MF hHleM le_sup_left

private theorem hypothesis_13_1_typePDefinitionData_of_maximal_typeP
    {G : Type u} [Group G] [Finite G]
    {M MF U Wleft Wright : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hTypeP : Section8.typePData M MF U Wleft Wright) :
    Section8.typePDefinitionData M MF U Wleft Wright := by
  letI : IsMinCE G := hmin
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, KU, hKU15⟩
  have hKU : section16KUData M K KU := by
    simpa [section16KUData] using hKU15
  exact
    Section8.theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hM hTypeP.1 hKU hTypeP.2

private theorem hypothesis_13_1_cyclicTIHypothesis_odd_card_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    Odd (Nat.card W) := by
  exact Odd.of_dvd_nat hmin.odd_order (Subgroup.card_subgroup_dvd_card W)

private theorem hypothesis_13_1_cyclicTIHypothesis_tiNormalizer_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    Section2.IsTISubsetWithNormalizer (Section3.cyclicTISet W1 W2 W) W := by
  classical
  rcases hcase with
    ⟨hprod, hWcyc, hW1ne, hW2ne, hnormRaw, _hSmax, _hTmax, _hSMF, _hTMF,
      _hSnotI, _hTnotI, _hSeq, _hTeq, _hSinf, _hTinf, _hW2le, _hW1le,
      _hSTeq, _hallMax, _hII, _hSsrc, _hTsrc, _hUV⟩
  rcases hprod with ⟨hW1le, hW2le, hWeq, hdisj, hcent⟩
  let A : Set G := Section3.cyclicTISet W1 W2 W
  have hnorm : ∀ W0 : Set G, W0.Nonempty → W0 ⊆ A →
      Subgroup.normalizer W0 = W := by
    intro W0 hne hsub
    exact hnormRaw W0 hne (by simpa [A, Section3.cyclicTISet] using hsub)
  have hWint : Section2.IsInternalDirectProduct W W1 W2 :=
    section13_isInternalDirectProduct_of_section12InternalDirectProduct
      ⟨hW1le, hW2le, hWeq, hdisj, hcent⟩
  have hAnonempty : A.Nonempty := by
    simpa [A] using
      section13_cyclicTISet_nonempty_of_internalDirectProduct_ne_bot
        hWint hW1ne hW2ne
  refine ⟨hAnonempty, ?_, ?_, ?_⟩
  · intro a ha ha1
    exact (Section3.cyclicTISet_not_mem_left W1 W2 W (by simpa [A] using ha))
      (by simp [ha1])
  · intro g hgInter
    rcases hgInter with ⟨a, haA, haConj⟩
    rcases haConj with ⟨b, hbA, hab⟩
    have hgbA : Section2.conjBy g b ∈ A := by
      simpa [A, hab] using haA
    have hgW : g ∈ Subgroup.normalizer (W : Set G) :=
      section13_mem_normalizer_of_conjBy_mem_cyclicTISet
        (W := W) (W1 := W1) (W2 := W2)
        hnorm (by simpa [A] using hbA) (by simpa [A] using hgbA)
    exact section13_normalizesSet_cyclicTISet_of_mem_normalizer hW1le hW2le hWcyc hgW
  · have hnormA : Subgroup.normalizer A = W := hnorm A hAnonempty (by intro x hx; exact hx)
    rw [section13_setNormalizer_eq_subgroupNormalizer, hnormA]

private theorem hypothesis_13_1_cyclicTIHypothesis_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    Section3.hypothesis_3_1_statement W1 W2 W := by
  classical
  have hcase' := hcase
  rcases hcase with
    ⟨hprod, hWcyc, hW1ne_bot, hW2ne_bot, _hnorm, _hrest⟩
  change Section3.isCyclicTIHypothesis W1 W2 W
  have hprod' := hprod
  rcases hprod with ⟨hW1le, hW2le, _hW, _hdisj, _hcent⟩
  refine ⟨hW1le, hW2le, ?_, hWcyc, ?_, ?_, ?_, ?_⟩
  · exact section13_isInternalDirectProduct_of_section12InternalDirectProduct hprod'
  · exact hypothesis_13_1_cyclicTIHypothesis_odd_card_source hmin hcase' hSTypeP hTTypeP
  · intro hcard
    exact hW1ne_bot ((Subgroup.card_eq_one (H := W1)).mp hcard)
  · intro hcard
    exact hW2ne_bot ((Subgroup.card_eq_one (H := W2)).mp hcard)
  · exact hypothesis_13_1_cyclicTIHypothesis_tiNormalizer_source hcase' hSTypeP hTTypeP

private theorem hypothesis_13_1_omegaNotationData_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    ∃ (ω : ℕ → ℕ → Section1.ClassFunction W),
      hypothesis_13_1_omegaNotationData W W1 W2
        (Nat.card W2) (Nat.card W1) ω := by
  classical
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    hypothesis_13_1_cyclicTIHypothesis_source hmin hcase hSTypeP hTTypeP
  rcases Section3.exists_notation_3_3_of_hypothesis_3_1 h31 with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, ωSrc, hωSrc⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  change Section3.OmegaSystem W1 W2 W I J i0 j0 ωSrc at hωSrc
  have hq : 0 < Nat.card W1 := Nat.card_pos (α := W1)
  have hp : 0 < Nat.card W2 := Nat.card_pos (α := W2)
  let eI : Fin (Nat.card W1) ≃ I :=
    section13_pointedFinEquiv (Nat.card W1) I hq hωSrc.card_left i0
  let eJ : Fin (Nat.card W2) ≃ J :=
    section13_pointedFinEquiv (Nat.card W2) J hp hωSrc.card_right j0
  let ωFin : Fin (Nat.card W1) → Fin (Nat.card W2) →
      Section1.ClassFunction W :=
    fun i j => ωSrc (eI i) (eJ j)
  have hωFin : Section3.notation_3_3_statement W1 W2 W
      (Fin (Nat.card W1)) (Fin (Nat.card W2)) ⟨0, hq⟩ ⟨0, hp⟩ ωFin := by
    exact section13_notation_3_3_reindex eI eJ
      (by
        change eI ⟨0, hq⟩ = i0
        exact section13_pointedFinEquiv_zero (Nat.card W1) I hq
          hωSrc.card_left i0)
      (by
        change eJ ⟨0, hp⟩ = j0
        exact section13_pointedFinEquiv_zero (Nat.card W2) J hp
          hωSrc.card_right j0)
      hωSrc
  let ω : ℕ → ℕ → Section1.ClassFunction W := fun i j =>
    if hi : i < Nat.card W1 then
      if hj : j < Nat.card W2 then
        ωFin ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0
  refine ⟨ω, h31, hq, hp, ωFin, hωFin, ?_⟩
  intro i j hi hj
  dsimp [ω]
  rw [dif_pos hi, dif_pos hj]

private theorem hypothesis_13_1_omegaEtaNotationData_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    ∃ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_omegaNotationData W W1 W2
          (Nat.card W2) (Nat.card W1) ω ∧
        Section3.theorem_3_2_map_statement W1 W2 W σ ∧
        ∀ i j, i < Nat.card W1 → j < Nat.card W2 → η i j = σ (ω i j) := by
  rcases hypothesis_13_1_omegaNotationData_source hmin _hcase _hSTypeP _hTTypeP with
    ⟨ω, hω⟩
  rcases hω with ⟨h31, hq, hp, ωFin, hωFin, hωspec⟩
  rcases Section3.theorem_3_2_of_notation_3_3
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin (Nat.card W1)) (J := Fin (Nat.card W2))
      (i0 := ⟨0, hq⟩) (j0 := ⟨0, hp⟩) (ω := ωFin) h31 hωFin with
    ⟨σ, hσ⟩
  exact ⟨ω, (fun i j => σ (ω i j)), σ,
    ⟨h31, hq, hp, ωFin, hωFin, hωspec⟩, hσ, by
      intro i j _hi _hj
      rfl⟩

private theorem hypothesis_13_1_omegaNotationData_swap_local
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G} {p q : ℕ}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    (hω : hypothesis_13_1_omegaNotationData W W1 W2 p q ω) :
    hypothesis_13_1_omegaNotationData W W2 W1 q p (fun i j => ω j i) := by
  rcases hω with ⟨h31, hq, hp, ωFin, hωFin, hωspec⟩
  refine ⟨Section3.hypothesis_3_1_statement_swap h31, hp, hq,
    (fun i j => ωFin j i), ?_, ?_⟩
  · exact Section3.notation_3_3_statement_swap hωFin
  · intro i j hi hj
    exact hωspec j i hj hi

private theorem hypothesis_13_1_notation_3_3_split_table_eq_base_col_injective
    {L : Type u}
    [Group L]
    [Finite L]
    (W1 W2 W : Subgroup L)
    {I J I' J' : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    [Fintype I']
    [Fintype J']
    [DecidableEq I']
    [DecidableEq J']
    (i0 : I)
    (j0 : J)
    (i0' : I')
    (j0' : J')
    (ω : I → J → Section1.ClassFunction W)
    (ω' : I' → J' → Section1.ClassFunction W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hω' : Section3.notation_3_3_statement W1 W2 W I' J' i0' j0' ω') :
    ∃ fI : I → I', ∃ fJ : J → J',
      Function.Injective fI ∧
        Function.Injective fJ ∧
          fI i0 = i0' ∧
            fJ j0 = j0' ∧
              ∀ i j, ω i j = ω' (fI i) (fJ j) := by
  classical
  have hleft : ∀ i : I, ∃ i' : I', ω i j0 = ω' i' j0' := by
    intro i
    exact
      (hω'.left_kernel_exact (ω i j0) (hω.irreducible i j0)).1
        (hω.left_kernel i)
  choose fI hfI using hleft
  have hright : ∀ j : J, ∃ j' : J', ω i0 j = ω' i0' j' := by
    intro j
    exact
      (hω'.right_kernel_exact (ω i0 j) (hω.irreducible i0 j)).1
        (hω.right_kernel j)
  choose fJ hfJ using hright
  have hfI0 : fI i0 = i0' := by
    have heq : ω' (fI i0) j0' = ω' i0' j0' := by
      calc
        ω' (fI i0) j0' = ω i0 j0 := (hfI i0).symm
        _ = ω' i0' j0' := by rw [hω.principal, hω'.principal]
    exact (hω'.pairwise_eq heq).1
  have hfJ0 : fJ j0 = j0' := by
    have heq : ω' i0' (fJ j0) = ω' i0' j0' := by
      calc
        ω' i0' (fJ j0) = ω i0 j0 := (hfJ j0).symm
        _ = ω' i0' j0' := by rw [hω.principal, hω'.principal]
    exact (hω'.pairwise_eq heq).2
  have hfJinj : Function.Injective fJ := by
    intro j j' hmap
    have heq : ω i0 j = ω i0 j' := by
      calc
        ω i0 j = ω' i0' (fJ j) := hfJ j
        _ = ω' i0' (fJ j') := by rw [hmap]
        _ = ω i0 j' := (hfJ j').symm
    exact (hω.pairwise_eq heq).2
  have hfIinj : Function.Injective fI := by
    intro i i' hmap
    have heq : ω i j0 = ω i' j0 := by
      calc
        ω i j0 = ω' (fI i) j0' := hfI i
        _ = ω' (fI i') j0' := by rw [hmap]
        _ = ω i' j0 := (hfI i').symm
    exact (hω.pairwise_eq heq).1
  refine ⟨fI, fJ, hfIinj, hfJinj, hfI0, hfJ0, ?_⟩
  intro i j
  ext x
  calc
    ω i j x = ω i j0 x * ω i0 j x := hω.product i j x
    _ = ω' (fI i) j0' x * ω' i0' (fJ j) x := by
      rw [hfI i, hfJ j]
    _ = ω' (fI i) (fJ j) x := (hω'.product (fI i) (fJ j) x).symm

private theorem hypothesis_13_1_typePFourSixTableInducedTransport_source
    {G : Type u} [Group G] [Finite G]
    {W M K U Wleft Wright : Subgroup G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (_hTypeP : Section8.typePData M K U Wleft Wright)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (_hω : hypothesis_13_1_omegaNotationData W Wleft Wright
      (Nat.card Wright) (Nat.card Wleft) ω)
    (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (Wsec : Subgroup M)
    (A : Set M)
    (A0 : Set M)
    (i0 : I)
    (j0 : J)
    (μsel : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM)
    (hrowPos : 0 < Nat.card Wleft)
    (hcolPos : 0 < Nat.card Wright) :
    ∃ e : W ≃* Wsec,
      (∀ x : W, (((e x : Wsec) : M) : G) = (x : G)) ∧
      ∃ rowB : {i : ℕ // i < Nat.card Wleft} → I,
        ∃ colB : {j : ℕ // j < Nat.card Wright} → J,
          Function.Injective rowB ∧
            Function.Surjective rowB ∧
              Function.Injective colB ∧
              Function.Surjective colB ∧
                rowB ⟨0, hrowPos⟩ = i0 ∧
                  colB ⟨0, hcolPos⟩ = j0 ∧
                  (∀ i j, (hi : i < Nat.card Wleft) →
                      (hj : j < Nat.card Wright) →
                    Section1.inducedCF (W.subgroupOf M)
                        (Section1.subgroupOfClassFunction (T := M)
                          (ω i j - ω 0 j)) =
                      Section1.inducedCF Wsec
                        (ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) -
                          ωsec i0 (colB ⟨j, hj⟩))) ∧
                  ∀ i j, (hi : i < Nat.card Wleft) →
                      (hj : j < Nat.card Wright) →
                    Section6.theorem_6_8_transportClassFunction e (ω i j) =
                      ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) := by
  classical
  rcases _hω with ⟨h31, hq0, hp0, ωFin, hωFin, hωEq⟩
  have h31copy := h31
  rcases _hTypeP with ⟨hMF, hCommon⟩
  rcases hCommon with
    ⟨_hHallD, _hMFleD, _hCompMFU, _hUnil, hWleftNorm, _hWleftCyc,
      _hWleftCard, _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      hWrightLeK, _hWrightNe, _hWrightCyc, _hCentralizer, _hHatW,
      _hT6, _hWrightSecond⟩
  have hKleM : K ≤ M := Section12.section16MFSubgroup_le hMF
  have hWleftLeM : Wleft ≤ M := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hWleftNorm hx)).2
  have hWrightLeM : Wright ≤ M := hWrightLeK.trans hKleM
  have hW_eq_sup : W = Wleft ⊔ Wright := by
    change Section3.isCyclicTIHypothesis Wleft Wright W at h31copy
    rcases h31copy with
      ⟨_hWleftW, _hWrightW, hIP, _hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    apply le_antisymm
    · intro x hxW
      rcases hIP.mul_surjective x hxW with ⟨a, ha, b, hb, hx⟩
      rw [hx]
      exact (Wleft ⊔ Wright).mul_mem
        ((show Wleft ≤ Wleft ⊔ Wright from le_sup_left) ha)
        ((show Wright ≤ Wleft ⊔ Wright from le_sup_right) hb)
    · exact sup_le hIP.left_le hIP.right_le
  have hWsup_le : Wleft ⊔ Wright ≤ M := sup_le hWleftLeM hWrightLeM
  rcases _hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource10,
      hWsec_eq, _hA0eq, _h46, hωsecData, _hIso, _hVirt, _hPrin,
      _hσAgreeCyc, _h45, _h48, _hTauIso, _hFull⟩
  subst Wsec
  let e : W ≃* (Wleft ⊔ Wright).subgroupOf M :=
    (MulEquiv.subgroupCongr hW_eq_sup).trans
      (Subgroup.subgroupOfEquivOfLe
        (H := Wleft ⊔ Wright) (K := M) hWsup_le).symm
  let ωM : Fin (Nat.card Wleft) → Fin (Nat.card Wright) →
      Section1.ClassFunction ((Wleft ⊔ Wright).subgroupOf M) :=
    fun i j => Section6.theorem_6_8_transportClassFunction e (ωFin i j)
  have hcardWleft :
      Nat.card (Wleft.subgroupOf M) = Nat.card Wleft :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWleftLeM).toEquiv
  have hcardWright :
      Nat.card (Wright.subgroupOf M) = Nat.card Wright :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWrightLeM).toEquiv
  have hVleft :
      ∀ x : W,
        ((x : G) ∈ Wleft) ↔
          (((e x : (Wleft ⊔ Wright).subgroupOf M) : M) ∈ Wleft.subgroupOf M) := by
    intro x
    simp [e, Subgroup.mem_subgroupOf]
  have hVright :
      ∀ x : W,
        ((x : G) ∈ Wright) ↔
          (((e x : (Wleft ⊔ Wright).subgroupOf M) : M) ∈ Wright.subgroupOf M) := by
    intro x
    simp [e, Subgroup.mem_subgroupOf]
  have hωM :
      Section3.notation_3_3_statement
        (Wleft.subgroupOf M) (Wright.subgroupOf M)
        ((Wleft ⊔ Wright).subgroupOf M)
        (Fin (Nat.card Wleft)) (Fin (Nat.card Wright))
        ⟨0, hq0⟩ ⟨0, hp0⟩ ωM := by
    simpa [ωM] using
      Section6.theorem_6_8_notation_3_3_transport
        (L := G) (M := M)
        (W1 := Wleft) (W2 := Wright) (W := W)
        (V1 := Wleft.subgroupOf M)
        (V2 := Wright.subgroupOf M)
        (V := (Wleft ⊔ Wright).subgroupOf M)
        (e := e) hcardWleft hcardWright hVleft hVright hωFin
  rcases
      hypothesis_13_1_notation_3_3_split_table_eq_base_col_injective
        (Wleft.subgroupOf M) (Wright.subgroupOf M)
        ((Wleft ⊔ Wright).subgroupOf M)
        (⟨0, hq0⟩ : Fin (Nat.card Wleft))
        (⟨0, hp0⟩ : Fin (Nat.card Wright)) i0 j0
        ωM ωsec hωM hωsecData with
    ⟨fI, fJ, hfIinj, hfJinj, hfI0, hfJ0, hωTable⟩
  let rowB : {i : ℕ // i < Nat.card Wleft} → I := fun i =>
    fI ⟨i.1, i.2⟩
  let colB : {j : ℕ // j < Nat.card Wright} → J := fun j =>
    fJ ⟨j.1, j.2⟩
  have hcolB_inj : Function.Injective colB := by
    intro j j' hmap
    have hfin :
        (⟨j.1, j.2⟩ : Fin (Nat.card Wright)) =
          (⟨j'.1, j'.2⟩ : Fin (Nat.card Wright)) :=
      hfJinj hmap
    exact Subtype.ext (congrArg Fin.val hfin)
  have hrowB_inj : Function.Injective rowB := by
    intro i i' hmap
    have hfin :
        (⟨i.1, i.2⟩ : Fin (Nat.card Wleft)) =
          (⟨i'.1, i'.2⟩ : Fin (Nat.card Wleft)) :=
      hfIinj hmap
    exact Subtype.ext (congrArg Fin.val hfin)
  have hrowB_surj : Function.Surjective rowB := by
    have hcardDom : Fintype.card {i : ℕ // i < Nat.card Wleft} =
        Nat.card Wleft := by
      let e : {i : ℕ // i < Nat.card Wleft} ≃ Fin (Nat.card Wleft) :=
        { toFun := fun i => ⟨i.1, i.2⟩
          invFun := fun i => ⟨i.1, i.2⟩
          left_inv := by intro i; rfl
          right_inv := by intro i; rfl }
      exact (Fintype.card_congr e).trans (Fintype.card_fin (Nat.card Wleft))
    have hcardI : Fintype.card I = Nat.card Wleft :=
      hωsecData.card_left.trans hcardWleft
    have hcard : Fintype.card {i : ℕ // i < Nat.card Wleft} = Fintype.card I := by
      rw [hcardDom, ← hcardI]
    exact Function.Injective.surjective_of_finite
      (Fintype.equivOfCardEq hcard) hrowB_inj
  have hcolB_surj : Function.Surjective colB := by
    have hcardDom : Fintype.card {j : ℕ // j < Nat.card Wright} =
        Nat.card Wright := by
      let e : {j : ℕ // j < Nat.card Wright} ≃ Fin (Nat.card Wright) :=
        { toFun := fun j => ⟨j.1, j.2⟩
          invFun := fun j => ⟨j.1, j.2⟩
          left_inv := by intro j; rfl
          right_inv := by intro j; rfl }
      exact (Fintype.card_congr e).trans (Fintype.card_fin (Nat.card Wright))
    have hcardJ : Fintype.card J = Nat.card Wright :=
      hωsecData.card_right.trans hcardWright
    have hcard : Fintype.card {j : ℕ // j < Nat.card Wright} = Fintype.card J := by
      rw [hcardDom, ← hcardJ]
    exact Function.Injective.surjective_of_finite
      (Fintype.equivOfCardEq hcard) hcolB_inj
  have hrowB0 : rowB ⟨0, hrowPos⟩ = i0 := by
    dsimp [rowB]
    simpa using hfI0
  have hcolB0 : colB ⟨0, hcolPos⟩ = j0 := by
    dsimp [colB]
    simpa using hfJ0
  have hcoe : ∀ x : W,
      (((e x : (Wleft ⊔ Wright).subgroupOf M) : M) : G) = (x : G) := by
    intro x
    rfl
  have hExactB : ∀ i j, (hi : i < Nat.card Wleft) →
      (hj : j < Nat.card Wright) →
      Section6.theorem_6_8_transportClassFunction e (ω i j) =
        ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) := by
    intro i j hi hj
    calc
      Section6.theorem_6_8_transportClassFunction e (ω i j) =
          Section6.theorem_6_8_transportClassFunction e
            (ωFin ⟨i, hi⟩ ⟨j, hj⟩) := by rw [hωEq i j hi hj]
      _ = ωM ⟨i, hi⟩ ⟨j, hj⟩ := rfl
      _ = ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) := by
        dsimp [rowB, colB]
        exact hωTable ⟨i, hi⟩ ⟨j, hj⟩
  have hIndB : ∀ i j, (hi : i < Nat.card Wleft) → (hj : j < Nat.card Wright) →
      Section1.inducedCF (W.subgroupOf M)
          (Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j)) =
        Section1.inducedCF ((Wleft ⊔ Wright).subgroupOf M)
          (ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) -
            ωsec i0 (colB ⟨j, hj⟩)) := by
    subst W
    intro i j hi hj
    let iF : Fin (Nat.card Wleft) := ⟨i, hi⟩
    let jF : Fin (Nat.card Wright) := ⟨j, hj⟩
    have hrow :
        (ωM iF jF - ωM ⟨0, hq0⟩ jF) =
          Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j) := by
      ext x
      have hx :
          e.symm x =
            (⟨((x : (Wleft ⊔ Wright).subgroupOf M) : G), x.2⟩ :
              ↥(Wleft ⊔ Wright)) := by
        ext
        rfl
      simp [ωM, e, Section6.theorem_6_8_transportClassFunction,
        Section1.subgroupOfClassFunction, hωEq i j hi hj,
        hωEq 0 j hq0 hj, hx, iF, jF]
    have htable :
        (ωM iF jF - ωM ⟨0, hq0⟩ jF) =
          ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) -
            ωsec i0 (colB ⟨j, hj⟩) := by
      dsimp [rowB, colB, iF, jF]
      have hfI0' : fI (0 : Fin (Nat.card ↥Wleft)) = i0 := by simpa using hfI0
      rw [hωTable ⟨i, hi⟩ ⟨j, hj⟩,
        hωTable 0 ⟨j, hj⟩, hfI0']
    calc
      Section1.inducedCF ((Wleft ⊔ Wright).subgroupOf M)
          (Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j)) =
        Section1.inducedCF ((Wleft ⊔ Wright).subgroupOf M)
          (ωM iF jF - ωM ⟨0, hq0⟩ jF) := by
            rw [← hrow]
      _ = Section1.inducedCF ((Wleft ⊔ Wright).subgroupOf M)
          (ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) -
            ωsec i0 (colB ⟨j, hj⟩)) := by
            rw [htable]
  exact ⟨e, hcoe, rowB, colB, hrowB_inj, hrowB_surj, hcolB_inj,
    hcolB_surj, hrowB0, hcolB0, hIndB, hExactB⟩

private def hypothesis_13_1_typePFourSixTableExactTransportData
    {G : Type u} [Group G] [Finite G]
    {W M : Subgroup G}
    (Wsec : Subgroup M)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    {I J : Type u}
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (row : ℕ → I)
    (col : ℕ → J)
    (rowCount colCount : ℕ) : Prop :=
  ∃ e : W ≃* Wsec,
    (∀ x : W, (((e x : Wsec) : M) : G) = (x : G)) ∧
      ∀ i j, i < rowCount → j < colCount →
        Section6.theorem_6_8_transportClassFunction e (ω i j) =
          ωsec (row i) (col j)

private theorem hypothesis_13_1_typePFourSixTableIndexing_source
    {G : Type u} [Group G] [Finite G]
    {W M K U Wleft Wright : Subgroup G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (hTypeP : Section8.typePData M K U Wleft Wright)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W Wleft Wright
      (Nat.card Wright) (Nat.card Wleft) ω)
    (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (Wsec : Subgroup M)
    (A : Set M)
    (A0 : Set M)
    (i0 : I)
    (j0 : J)
    (μsel : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM) :
    ∃ row : ℕ → I,
      ∃ col : ℕ → J,
        row 0 = i0 ∧
        col 0 = j0 ∧
        (∀ j, 0 < j → j < Nat.card Wright → col j ≠ j0) ∧
        (∀ j k, j < Nat.card Wright → k < Nat.card Wright →
          col j = col k → j = k) ∧
        (∀ i k, i < Nat.card Wleft → k < Nat.card Wleft →
          row i = row k → i = k) ∧
        (∀ iSel : I, ∃ k, k < Nat.card Wleft ∧ row k = iSel) ∧
        (∀ jSel : J, ∃ k, k < Nat.card Wright ∧ col k = jSel) ∧
        (∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
          Section1.inducedCF (W.subgroupOf M)
              (Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j)) =
            Section1.inducedCF Wsec
              (ωsec (row i) (col j) - ωsec i0 (col j))) ∧
        hypothesis_13_1_typePFourSixTableExactTransportData Wsec ω ωsec row col
          (Nat.card Wleft) (Nat.card Wright) := by
  classical
  have hrowPos : 0 < Nat.card Wleft := Nat.card_pos (α := Wleft)
  have hcolPos : 0 < Nat.card Wright := Nat.card_pos (α := Wright)
  rcases
      hypothesis_13_1_typePFourSixTableInducedTransport_source
        hTypeP ω hω τM Wsec A A0 i0 j0 μsel δSign ωsec σsec hNotation
        hrowPos hcolPos with
    ⟨e, hcoe, rowB, colB, hrowB_inj, hrowB_surj, hcolB_inj, hcolB_surj,
      hrowB0, hcolB0, hIndB, hExactB⟩
  let row : ℕ → I := fun i =>
    if hi : i < Nat.card Wleft then rowB ⟨i, hi⟩ else i0
  let col : ℕ → J := fun j =>
    if hj : j < Nat.card Wright then colB ⟨j, hj⟩ else j0
  have hrow0 : row 0 = i0 := by
    dsimp [row]
    rw [dif_pos hrowPos]
    exact hrowB0
  have hcol0 : col 0 = j0 := by
    dsimp [col]
    rw [dif_pos hcolPos]
    exact hcolB0
  have hcol_ne : ∀ j, 0 < j → j < Nat.card Wright → col j ≠ j0 := by
    intro j hj0 hj hcol_eq
    have hcol_eval : col j = colB ⟨j, hj⟩ := by
      dsimp [col]
      rw [dif_pos hj]
    have hsub :
        (⟨j, hj⟩ : {j : ℕ // j < Nat.card Wright}) =
          ⟨0, hcolPos⟩ := by
      apply hcolB_inj
      calc
        colB ⟨j, hj⟩ = col j := hcol_eval.symm
        _ = j0 := hcol_eq
        _ = colB ⟨0, hcolPos⟩ := hcolB0.symm
    exact (Nat.ne_of_gt hj0) (congrArg Subtype.val hsub)
  have hrow_inj :
      ∀ i k, i < Nat.card Wleft → k < Nat.card Wleft →
        row i = row k → i = k := by
    intro i k hi hk hrow_eq
    have hrow_i : row i = rowB ⟨i, hi⟩ := by
      dsimp [row]
      rw [dif_pos hi]
    have hrow_k : row k = rowB ⟨k, hk⟩ := by
      dsimp [row]
      rw [dif_pos hk]
    have hsub :
        (⟨i, hi⟩ : {i : ℕ // i < Nat.card Wleft}) =
          ⟨k, hk⟩ := by
      apply hrowB_inj
      calc
        rowB ⟨i, hi⟩ = row i := hrow_i.symm
        _ = row k := hrow_eq
        _ = rowB ⟨k, hk⟩ := hrow_k
    exact congrArg Subtype.val hsub
  have hcol_inj :
      ∀ j k, j < Nat.card Wright → k < Nat.card Wright →
        col j = col k → j = k := by
    intro j k hj hk hcol_eq
    have hcol_j : col j = colB ⟨j, hj⟩ := by
      dsimp [col]
      rw [dif_pos hj]
    have hcol_k : col k = colB ⟨k, hk⟩ := by
      dsimp [col]
      rw [dif_pos hk]
    have hsub :
        (⟨j, hj⟩ : {j : ℕ // j < Nat.card Wright}) = ⟨k, hk⟩ := by
      apply hcolB_inj
      calc
        colB ⟨j, hj⟩ = col j := hcol_j.symm
        _ = col k := hcol_eq
        _ = colB ⟨k, hk⟩ := hcol_k
    exact congrArg Subtype.val hsub
  have hrow_surj : ∀ iSel : I, ∃ k, k < Nat.card Wleft ∧ row k = iSel := by
    intro iSel
    rcases hrowB_surj iSel with ⟨k, hk⟩
    refine ⟨k.1, k.2, ?_⟩
    dsimp [row]
    rw [dif_pos k.2]
    exact hk
  have hcol_surj : ∀ jSel : J, ∃ k, k < Nat.card Wright ∧ col k = jSel := by
    intro jSel
    rcases hcolB_surj jSel with ⟨k, hk⟩
    refine ⟨k.1, k.2, ?_⟩
    dsimp [col]
    rw [dif_pos k.2]
    exact hk
  have hInd : ∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
      Section1.inducedCF (W.subgroupOf M)
          (Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j)) =
        Section1.inducedCF Wsec (ωsec (row i) (col j) - ωsec i0 (col j)) := by
    intro i j hi hj
    calc
      Section1.inducedCF (W.subgroupOf M)
          (Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j)) =
        Section1.inducedCF Wsec
          (ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) -
            ωsec i0 (colB ⟨j, hj⟩)) := hIndB i j hi hj
      _ = Section1.inducedCF Wsec (ωsec (row i) (col j) - ωsec i0 (col j)) := by
        have hrow_eval : row i = rowB ⟨i, hi⟩ := by
          dsimp [row]
          rw [dif_pos hi]
        have hcol_eval : col j = colB ⟨j, hj⟩ := by
          dsimp [col]
          rw [dif_pos hj]
        rw [hrow_eval, hcol_eval]
  have hExact : hypothesis_13_1_typePFourSixTableExactTransportData
      Wsec ω ωsec row col (Nat.card Wleft) (Nat.card Wright) := by
    refine ⟨e, hcoe, ?_⟩
    intro i j hi hj
    calc
      Section6.theorem_6_8_transportClassFunction e (ω i j) =
          ωsec (rowB ⟨i, hi⟩) (colB ⟨j, hj⟩) := hExactB i j hi hj
      _ = ωsec (row i) (col j) := by
        have hrow_eval : row i = rowB ⟨i, hi⟩ := by
          dsimp [row]
          rw [dif_pos hi]
        have hcol_eval : col j = colB ⟨j, hj⟩ := by
          dsimp [col]
          rw [dif_pos hj]
        rw [hrow_eval, hcol_eval]
  exact ⟨row, col, hrow0, hcol0, hcol_ne, hcol_inj, hrow_inj, hrow_surj,
    hcol_surj, hInd, hExact⟩

private def hypothesis_13_1_selectedTypePFourSixTableData
    {G : Type u} [Group G] [Finite G]
    {W M K U Wleft Wright : Subgroup G}
    (_hTypeP : Section8.typePData M K U Wleft Wright)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (_hω : hypothesis_13_1_omegaNotationData W Wleft Wright
      (Nat.card Wright) (Nat.card Wleft) ω)
    (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (χ : ℕ → ℕ → Section1.ClassFunction M)
    (δsel : ℕ → ℤ)
    (Wsel : Subgroup M)
    (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
    (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
    ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
        ∃ μsel : I → J → Section1.ClassFunction M,
          ∃ δSign : J → ℤ,
            ∃ ωsec : I → J → Section1.ClassFunction Wsel,
              ∃ _hNotation : @Section10.section10FourSixNotationSupportedData G _ _ I J
                instI instJ decI decJ M Wleft Wright Wsel
                A A0 i0 j0 μsel δSign ωsec σsel τM,
                ∃ row : ℕ → I, ∃ col : ℕ → J,
                  row 0 = i0 ∧
                  col 0 = j0 ∧
                  (∀ j, 0 < j → j < Nat.card Wright → col j ≠ j0) ∧
                  (∀ i k, i < Nat.card Wleft → k < Nat.card Wleft →
                    row i = row k → i = k) ∧
                  (∀ iSel : I, ∃ k, k < Nat.card Wleft ∧ row k = iSel) ∧
                  (∀ jSel : J, ∃ k, k < Nat.card Wright ∧ col k = jSel) ∧
                  (∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
                    Section1.inducedCF (W.subgroupOf M)
                        (Section1.subgroupOfClassFunction (T := M)
                          (ω i j - ω 0 j)) =
                      Section1.inducedCF Wsel
                        (ωsec (row i) (col j) - ωsec i0 (col j))) ∧
                  hypothesis_13_1_typePFourSixTableExactTransportData
                      Wsel ω ωsec row col
                        (Nat.card Wleft) (Nat.card Wright) ∧
                  (∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
                    χ i j = μsel (row i) (col j)) ∧
                  (∀ j, j < Nat.card Wright → δsel j = δSign (col j)) ∧
                  ∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
                    ωsel i j = ωsec (row i) (col j)

private theorem hypothesis_13_1_selectedTypePFourSixTableData_of_package
    {G : Type u} [Group G] [Finite G]
    {W M K U Wleft Wright : Subgroup G}
    (hTypeP : Section8.typePData M K U Wleft Wright)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W Wleft Wright
      (Nat.card Wright) (Nat.card Wleft) ω)
    (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsel : Subgroup M} {A A0 : Set M} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsel}
    {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsel
      A A0 i0 j0 μsel δSign ωsec σsel τM)
    (row : ℕ → I) (col : ℕ → J)
    (hrow0 : row 0 = i0)
    (hcol0 : col 0 = j0)
    (hcol_ne : ∀ j, 0 < j → j < Nat.card Wright → col j ≠ j0)
    (hrow_inj : ∀ i k, i < Nat.card Wleft → k < Nat.card Wleft →
      row i = row k → i = k)
    (hrow_surj : ∀ iSel : I, ∃ k, k < Nat.card Wleft ∧ row k = iSel)
    (hcol_surj : ∀ jSel : J, ∃ k, k < Nat.card Wright ∧ col k = jSel)
    (hIndTransport : ∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
      Section1.inducedCF (W.subgroupOf M)
          (Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j)) =
        Section1.inducedCF Wsel (ωsec (row i) (col j) - ωsec i0 (col j)))
    (hExactTransport : hypothesis_13_1_typePFourSixTableExactTransportData
      Wsel ω ωsec row col (Nat.card Wleft) (Nat.card Wright)) :
    hypothesis_13_1_selectedTypePFourSixTableData hTypeP ω hω τM
      (fun i j => μsel (row i) (col j)) (fun j => δSign (col j)) Wsel
      (fun i j => ωsec (row i) (col j)) σsel := by
  refine ⟨I, inferInstance, inferInstance, J, inferInstance, inferInstance,
    A, A0, i0, j0, μsel, δSign, ωsec, hNotation, row, col, hrow0, hcol0,
    hcol_ne, hrow_inj, hrow_surj, hcol_surj, hIndTransport, hExactTransport,
    ?_, ?_, ?_⟩
  · intro i j _hi _hj
    rfl
  · intro j _hj
    rfl
  · intro i j _hi _hj
    rfl

private theorem hypothesis_13_1_typePFourSixTableData_source
    {G : Type u} [Group G] [Finite G]
    {W M K U Wleft Wright : Subgroup G}
    (_hTypeP : Section8.typePData M K U Wleft Wright)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W Wleft Wright
      (Nat.card Wright) (Nat.card Wleft) ω)
    (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (_hFourSix : typePFourSixTauSourceData M K U Wleft Wright τM) :
    ∃ (χ : ℕ → ℕ → Section1.ClassFunction M)
      (δ : ℕ → ℤ),
        (∀ j, j < Nat.card Wright → δ j = 1 ∨ δ j = -1) ∧
        (∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
          Section1.IsIrreducibleCharacterOnGroup (χ i j)) ∧
        (∀ j, 0 < j → j < Nat.card Wright →
          χ 0 j ≠ Section1.principalCharacter M) ∧
        (∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
          Section1.inducedCF (W.subgroupOf M)
              (Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j)) =
            (((δ j : ℤ) : ℂ) • (χ i j - χ 0 j))) ∧
        (∀ j k, 0 < j → j < Nat.card Wright → 0 < k →
          k < Nat.card Wright →
            Section1.degree (χ 0 j) = Section1.degree (χ 0 k)) ∧
        (((δ 0 : ℤ) : ℂ) • χ 0 0 = Section1.principalCharacter M) := by
  classical
  rcases _hFourSix with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hNotation, _hSigmaAgree, ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      _hTypeP ω hω τM Wsec A A0 i0 j0 μsel δSign ωsec σsec hNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, _hcol_inj, _hrow_inj, _hrow_surj,
      _hcol_surj, hIndTransport, _hExactTransport⟩
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData
      hNotation with
    ⟨σM, _xCharD, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨hωsec, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  have h43bAll := h43b
  rcases h43b with
    ⟨_hσmap, _hsign, hIrr, hDistinct, hInd, _hSigma⟩
  have hbaseAll :=
    Section4.proposition_4_4_base
      (W1 := Wleft.subgroupOf M)
      (W2 := Wright.subgroupOf M)
      (W := Wsec)
      (I := I)
      (J := J)
      (i0 := i0)
      (j0 := j0)
      (ω := ωsec)
      (σ := σM)
      (piChar := μsel)
      (deltaSign := fun j => (δSign j : ℂ))
      hωsec h43bAll
  refine ⟨(fun i j => μsel (row i) (col j)), (fun j => δSign (col j)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _hj
    exact Section10.deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData
      hNotation (col j)
  · intro i j _hi _hj
    exact hIrr (row i) (col j)
  · intro j hj0 hj hprincipal
    have hentry :
        μsel (row 0) (col j) = μsel i0 j0 := by
      calc
        μsel (row 0) (col j) = Section1.principalCharacter M := hprincipal
        _ = μsel i0 j0 := hbaseAll.2.symm
    have hpair_ne : (row 0, col j) ≠ (i0, j0) := by
      intro hpair
      exact hcol_ne j hj0 hj (congrArg Prod.snd hpair)
    exact hDistinct (row 0, col j) (i0, j0) hpair_ne hentry
  · intro i j hi hj
    calc
      Section1.inducedCF (W.subgroupOf M)
          (Section1.subgroupOfClassFunction (T := M) (ω i j - ω 0 j)) =
        Section1.inducedCF Wsec (ωsec (row i) (col j) - ωsec i0 (col j)) :=
          hIndTransport i j hi hj
      _ = (((δSign (col j) : ℤ) : ℂ) •
            (μsel (row i) (col j) - μsel i0 (col j))) := hInd (row i) (col j)
      _ = (((δSign (col j) : ℤ) : ℂ) •
            (μsel (row i) (col j) - μsel (row 0) (col j))) := by
          rw [hrow0]
  · intro j k hj0 hj hk0 hk
    calc
      Section1.degree (μsel (row 0) (col j)) =
          Section1.degree (μsel i0 (col j)) := by rw [hrow0]
      _ = Section1.degree (μsel i0 (col k)) :=
          Section10.baseRow_degree_eq_of_section10FourSixNotationSupportedData
            hNotation (hcol_ne j hj0 hj) (hcol_ne k hk0 hk)
      _ = Section1.degree (μsel (row 0) (col k)) := by rw [hrow0]
  · calc
      (((δSign (col 0) : ℤ) : ℂ) • μsel (row 0) (col 0)) =
          (((δSign j0 : ℤ) : ℂ) • μsel i0 j0) := by
            rw [hrow0, hcol0]
      _ = Section1.principalCharacter M := by
            simp [hbaseAll.1, hbaseAll.2]

private theorem hypothesis_13_1_typePFourSixRowRestriction_source
    {G : Type u} [Group G] [Finite G]
    {W M K U Wleft Wright : Subgroup G}
    (hTypeP : Section8.typePData M K U Wleft Wright)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W Wleft Wright
      (Nat.card Wright) (Nat.card Wleft) ω)
    (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (hFourSix : typePFourSixTauSourceData M K U Wleft Wright τM) :
    ∃ (χ : ℕ → ℕ → Section1.ClassFunction M)
      (δ : ℕ → ℤ)
      (Wsel : Subgroup M)
      (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
      (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_selectedTypePFourSixTableData hTypeP ω hω τM
          χ δ Wsel ωsel σsel ∧
        (∀ i j k, i < Nat.card Wleft → 0 < j → j < Nat.card Wright →
          0 < k → k < Nat.card Wright →
            Section1.degree (χ i j) = Section1.degree (χ i k) →
              τM (χ i j - χ i k) =
                (((δ j : ℤ) : ℂ) • (σsel (ωsel i j) - σsel (ωsel i k)))) ∧
        ∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
          ∀ x : M,
            (x : G) ∈ ((K ⊔ U : Subgroup G) : Set G) →
              χ i j x = χ 0 j x := by
  classical
  have hTypePIndex := hTypeP
  rcases hTypeP with ⟨_hMF, hCommon⟩
  rcases hCommon with
    ⟨_hHallD, _hMFleD, hCompMFU, _hUnil, _hWleftNorm, _hWleftCyc,
      _hWleftCard, _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hWrightLeMF, _hWrightNe, _hWrightCyc, _hCentralizer, _hHatW,
      _hT6, _hWrightSecond⟩
  have hDerEq : ambientDerivedSubgroup M = K ⊔ U := hCompMFU.2.2.1
  rcases hFourSix with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hNotation, _hSigmaAgree, ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      hTypePIndex ω hω τM Wsec A A0 i0 j0 μsel δSign ωsec σsec hNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, _hcol_inj, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport⟩
  have hNotationFull := hNotation
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, h45, h48,
      _hTauIso, _hFull⟩
  rcases h45 with ⟨xChar, h45a, _h45b⟩
  rcases h45a with ⟨hres, _hirrX, _hindX⟩
  let χ : ℕ → ℕ → Section1.ClassFunction M := fun i j => μsel (row i) (col j)
  let δ : ℕ → ℤ := fun j => δSign (col j)
  let ωselN : ℕ → ℕ → Section1.ClassFunction Wsec :=
    fun i j => ωsec (row i) (col j)
  have hSelected :
      hypothesis_13_1_selectedTypePFourSixTableData hTypePIndex ω hω τM
        χ δ Wsec ωselN σsec :=
    hypothesis_13_1_selectedTypePFourSixTableData_of_package
      hTypePIndex ω hω τM hNotationFull row col hrow0 hcol0 hcol_ne hrow_inj
      hrow_surj hcol_surj hIndTransport hExactTransport
  have hselDade :
      ∀ i j k, i < Nat.card Wleft → 0 < j → j < Nat.card Wright →
        0 < k → k < Nat.card Wright →
          Section1.degree (χ i j) = Section1.degree (χ i k) →
            τM (χ i j - χ i k) =
              (((δ j : ℤ) : ℂ) • (σsec (ωselN i j) - σsec (ωselN i k))) := by
    intro i j k _hi hj0 hj hk0 hk hdeg
    have hjne : col j ≠ j0 := hcol_ne j hj0 hj
    have hkne : col k ≠ j0 := hcol_ne k hk0 hk
    rcases h48 (row i) (col j) (col k) hjne hkne (by
        simpa [χ] using hdeg) with
      ⟨_hsupp, _hdelta, hτ⟩
    simpa [χ, δ, ωselN] using hτ
  have hrow :
      ∀ i j, i < Nat.card Wleft → j < Nat.card Wright →
        ∀ x : M,
          (x : G) ∈ ((K ⊔ U : Subgroup G) : Set G) →
            χ i j x = χ 0 j x := by
    intro i j _hi _hj x hxKU
    have hxDerG : (x : G) ∈ ambientDerivedSubgroup M := by
      simpa [hDerEq] using hxKU
    have hxDerSub : x ∈ (ambientDerivedSubgroup M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxDerG
    have hxDer : x ∈ derivedSubgroup M := by
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M)]
        using hxDerSub
    let xD : derivedSubgroup M := ⟨x, hxDer⟩
    have hres_eq :
        Section1.subgroupRestriction (derivedSubgroup M) (μsel (row i) (col j)) =
          Section1.subgroupRestriction (derivedSubgroup M) (μsel (row 0) (col j)) := by
      calc
        Section1.subgroupRestriction (derivedSubgroup M) (μsel (row i) (col j)) =
            xChar (col j) := hres (row i) (col j)
        _ = Section1.subgroupRestriction (derivedSubgroup M) (μsel (row 0) (col j)) :=
            (hres (row 0) (col j)).symm
    have hval := congrFun hres_eq xD
    simpa [χ, Section1.subgroupRestriction, xD] using hval
  exact ⟨χ, δ, Wsec, ωselN, σsec, hSelected, hselDade, hrow⟩

private theorem hypothesis_13_1_conjugateIndexSelectedPackageSigmaConjugateBaseRow_source
    {G : Type u} [Group G] [Finite G]
    {M Wleft Wright : Subgroup G}
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup M} {A A0 : Set M} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (_hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM) :
    ∀ j : J, j ≠ j0 →
      σsec (Section1.conjugateCharacter (ωsec i0 j)) =
        Section1.conjugateCharacter (σsec (ωsec i0 j)) := by
  exact
    Section10.ambientRelativePF39BaseRowConjugateData_of_section10FourSixNotationSupportedData
      _hNotation

private theorem hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaCanonical_core_source
    {G : Type u} [Group G] [Finite G]
    {M Wleft Wright : Subgroup G}
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup M} {A A0 : Set M} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (_hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM) :
    ∀ j : J, (hj : j ≠ j0) →
      let hConj :=
        Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
          _hNotation hj
      σsec (ωsec i0 (Classical.choose hConj)) =
        Section1.conjugateCharacter (σsec (ωsec i0 j)) := by
  /-
  Checked canonical selected-column bookkeeping over the narrower source
  boundary saying `σsec` commutes with complex conjugation on selected
  base-row `ω` values.
  -/
  classical
  intro j hj
  let hConj :=
    Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
      _hNotation hj
  change
    σsec (ωsec i0 (Classical.choose hConj)) =
      Section1.conjugateCharacter (σsec (ωsec i0 j))
  rcases
      Section10.exists_conjugate_baseRow_omega_mu_index_of_section10FourSixNotationSupportedData
        _hNotation hj with
    ⟨k0, _hk0, _hk0ne, hωk0, hμk0⟩
  have hConjSpec := Classical.choose_spec hConj
  rcases hConjSpec with ⟨_hchoose0, _hchoose_ne, hchoose_mu⟩
  have hμ_eq :
      μsel i0 k0 = μsel i0 (Classical.choose hConj) :=
    hμk0.symm.trans hchoose_mu
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData
      _hNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  rcases h43b with ⟨_hσmap, _hsign, _hirr, hDistinct, _hind, _hSigma⟩
  have hk0_eq : k0 = Classical.choose hConj := by
    by_contra hne
    have hp_ne : (i0, k0) ≠ (i0, Classical.choose hConj) := by
      intro hp
      exact hne (congrArg Prod.snd hp)
    exact (hDistinct (i0, k0) (i0, Classical.choose hConj) hp_ne) hμ_eq
  have hωchoose :
      Section1.conjugateCharacter (ωsec i0 j) =
        ωsec i0 (Classical.choose hConj) := by
    simpa [hk0_eq] using hωk0
  have hcomm :
      σsec (Section1.conjugateCharacter (ωsec i0 j)) =
        Section1.conjugateCharacter (σsec (ωsec i0 j)) :=
    hypothesis_13_1_conjugateIndexSelectedPackageSigmaConjugateBaseRow_source
      _hNotation j hj
  calc
    σsec (ωsec i0 (Classical.choose hConj)) =
        σsec (Section1.conjugateCharacter (ωsec i0 j)) := by
          rw [hωchoose]
    _ = Section1.conjugateCharacter (σsec (ωsec i0 j)) := hcomm

private theorem hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaCanonical_source
    {G : Type u} [Group G] [Finite G]
    {M K U Wleft Wright : Subgroup G}
    (_hTypeP : Section8.typePData M K U Wleft Wright)
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup M} {A A0 : Set M} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (_hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM) :
    ∀ j : J, (hj : j ≠ j0) →
      let hConj :=
        Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
          _hNotation hj
      σsec (ωsec i0 (Classical.choose hConj)) =
        Section1.conjugateCharacter (σsec (ωsec i0 j)) := by
  /-
  Checked wrapper around the selected Section10 package source boundary.
  -/
  exact
    hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaCanonical_core_source
      _hNotation

private theorem hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaTransfer_source
    {G : Type u} [Group G] [Finite G]
    {M K U Wleft Wright : Subgroup G}
    (hTypeP : Section8.typePData M K U Wleft Wright)
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup M} {A A0 : Set M} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM) :
    ∀ j k : J, j ≠ j0 → k ≠ j0 →
      Section1.conjugateCharacter (ωsec i0 j) = ωsec i0 k →
        σsec (ωsec i0 k) =
          Section1.conjugateCharacter (σsec (ωsec i0 j)) := by
  /-
  Checked arbitrary-column wrapper around the canonical selected transfer:
  uniqueness of the Section `(3.3)` table identifies any selected column with
  the same conjugate `ω` value with the canonical Section `(4.9.a)` column.
  -/
  classical
  intro j k hj hk hωk
  let hConj :=
    Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
      hNotation hj
  have hcanonical :
      σsec (ωsec i0 (Classical.choose hConj)) =
        Section1.conjugateCharacter (σsec (ωsec i0 j)) := by
    simpa [hConj] using
      hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaCanonical_source
        hTypeP hNotation j hj
  rcases
      Section10.exists_conjugate_baseRow_omega_mu_index_of_section10FourSixNotationSupportedData
        hNotation hj with
    ⟨k0, _hk0, _hk0ne, hωk0, hμk0⟩
  have hConjSpec := Classical.choose_spec hConj
  rcases hConjSpec with ⟨_hchoose0, _hchoose_ne, hchoose_mu⟩
  have hμ_eq :
      μsel i0 k0 = μsel i0 (Classical.choose hConj) :=
    hμk0.symm.trans hchoose_mu
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData
      hNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  rcases h43b with ⟨_hσmap, _hsign, _hirr, hDistinct, _hind, _hSigma⟩
  have hk0_eq : k0 = Classical.choose hConj := by
    by_contra hne
    have hp_ne : (i0, k0) ≠ (i0, Classical.choose hConj) := by
      intro hp
      exact hne (congrArg Prod.snd hp)
    exact (hDistinct (i0, k0) (i0, Classical.choose hConj) hp_ne) hμ_eq
  have hωchoose :
      Section1.conjugateCharacter (ωsec i0 j) =
        ωsec i0 (Classical.choose hConj) := by
    simpa [hk0_eq] using hωk0
  have hω_eq :
      ωsec i0 k = ωsec i0 (Classical.choose hConj) :=
    hωk.symm.trans hωchoose
  have hk_eq : k = Classical.choose hConj :=
    (hω.pairwise_eq hω_eq).2
  simpa [hk_eq] using hcanonical

private theorem hypothesis_13_1_conjugateIndexSelectedPackageOmegaWitness
    {G : Type u} [Group G] [Finite G]
    {M K U Wleft Wright : Subgroup G}
    (_hTypeP : Section8.typePData M K U Wleft Wright)
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup M} {A A0 : Set M} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM) :
    ∀ j : J, (hj : j ≠ j0) →
      let hConj :=
        Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
          hNotation hj
      Section1.conjugateCharacter (ωsec i0 j) =
        ωsec i0 (Classical.choose hConj) := by
  classical
  intro j hj
  let hConj :=
    Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
      hNotation hj
  change
    Section1.conjugateCharacter (ωsec i0 j) =
      ωsec i0 (Classical.choose hConj)
  rcases
      Section10.exists_conjugate_baseRow_omega_mu_index_of_section10FourSixNotationSupportedData
        hNotation hj with
    ⟨k, _hk0, _hkne, hωk, hμk⟩
  have hConjSpec := Classical.choose_spec hConj
  rcases hConjSpec with ⟨_hchoose0, _hchoose_ne, hchoose_mu⟩
  have hμ_eq :
      μsel i0 k = μsel i0 (Classical.choose hConj) :=
    hμk.symm.trans hchoose_mu
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData
      hNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  rcases h43b with ⟨_hσmap, _hsign, _hirr, hDistinct, _hind, _hSigma⟩
  have hk_eq : k = Classical.choose hConj := by
    by_contra hne
    have hp_ne : (i0, k) ≠ (i0, Classical.choose hConj) := by
      intro hp
      exact hne (congrArg Prod.snd hp)
    exact (hDistinct (i0, k) (i0, Classical.choose hConj) hp_ne) hμ_eq
  simpa [hk_eq] using hωk

private theorem hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaWitness_source
    {G : Type u} [Group G] [Finite G]
    {M K U Wleft Wright : Subgroup G}
    (hTypeP : Section8.typePData M K U Wleft Wright)
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup M} {A A0 : Set M} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM) :
    ∀ j : J, (hj : j ≠ j0) →
      let hConj :=
        Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
          hNotation hj
      σsec (ωsec i0 (Classical.choose hConj)) =
        Section1.conjugateCharacter (σsec (ωsec i0 j)) := by
  /-
  Source pointwise alignment for PF `(13.18)` on the actual selected Section
  `(4.6)` package, narrowed to the canonical non-base conjugate column supplied
  by Section `(4.9.a)`.  The arbitrary-column wrapper below is checked using
  pairwise distinctness of the selected table entries.
  -/
  classical
  intro j hj
  let hConj :=
    Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
      hNotation hj
  have hω :
      Section1.conjugateCharacter (ωsec i0 j) =
        ωsec i0 (Classical.choose hConj) := by
    simpa [hConj] using
      hypothesis_13_1_conjugateIndexSelectedPackageOmegaWitness
        hTypeP hNotation j hj
  have hk0 : Classical.choose hConj ≠ j0 := (Classical.choose_spec hConj).1
  exact
    hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaTransfer_source
      hTypeP hNotation j (Classical.choose hConj) hj hk0 hω

private theorem hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaAlignment_source
    {G : Type u} [Group G] [Finite G]
    {M K U Wleft Wright : Subgroup G}
    (_hTypeP : Section8.typePData M K U Wleft Wright)
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup M} {A A0 : Set M} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (_hNotation : Section10.section10FourSixNotationSupportedData M Wleft Wright Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τM) :
    ∀ j k : J, j ≠ j0 → k ≠ j0 →
      μsel i0 k = Section1.conjugateCharacter (μsel i0 j) →
        σsec (ωsec i0 k) =
          Section1.conjugateCharacter (σsec (ωsec i0 j)) := by
  /-
  Source pointwise alignment for PF `(13.18)` on the actual selected Section
  `(4.6)` package: selected zero-row conjugation transfers to conjugation of
  the selected `σ(ω)` values.
  -/
  classical
  intro j k hj hk hχ
  let hConj :=
    Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
      _hNotation hj
  have hsrc :
      σsec (ωsec i0 (Classical.choose hConj)) =
        Section1.conjugateCharacter (σsec (ωsec i0 j)) := by
    simpa [hConj] using
      hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaWitness_source
        _hTypeP _hNotation j hj
  have hConjSpec := Classical.choose_spec hConj
  rcases hConjSpec with ⟨_hj'0, _hj'ne, hconj⟩
  have hμ_eq :
      μsel i0 k = μsel i0 (Classical.choose hConj) := hχ.trans hconj
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData
      _hNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  rcases h43b with ⟨_hσmap, _hsign, _hirr, hDistinct, _hind, _hSigma⟩
  have hk_eq : k = Classical.choose hConj := by
    by_contra hne
    have hp_ne : (i0, k) ≠ (i0, Classical.choose hConj) := by
      intro hp
      exact hne (congrArg Prod.snd hp)
    exact (hDistinct (i0, k) (i0, Classical.choose hConj) hp_ne) hμ_eq
  simpa [hk_eq] using hsrc

private theorem hypothesis_13_1_typePFourSixBaseRowConjugateSigmaOmega_source
    {G : Type u} [Group G] [Finite G]
    {W M K U Wleft Wright : Subgroup G}
    (hTypeP : Section8.typePData M K U Wleft Wright)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W Wleft Wright
      (Nat.card Wright) (Nat.card Wleft) ω)
    (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (hFourSix : typePFourSixTauSourceData M K U Wleft Wright τM) :
    ∃ (χ : ℕ → ℕ → Section1.ClassFunction M)
      (_δ : ℕ → ℤ)
      (Wsel : Subgroup M)
      (_ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
      (_σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_selectedTypePFourSixTableData hTypeP ω hω τM
          χ _δ Wsel _ωsel _σsel ∧
        (∀ j, 0 < j → j < Nat.card Wright →
          ∃ k : ℕ, 0 < k ∧ k < Nat.card Wright ∧ k ≠ j ∧
            χ 0 k = Section1.conjugateCharacter (χ 0 j)) ∧
        ∀ j k, 0 < j → j < Nat.card Wright →
          0 < k → k < Nat.card Wright →
            χ 0 k = Section1.conjugateCharacter (χ 0 j) →
              _σsel (_ωsel 0 k) =
                Section1.conjugateCharacter (_σsel (_ωsel 0 j)) := by
  classical
  rcases hFourSix with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hNotation, _hSigmaAgree, ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      hTypeP ω hω τM Wsec A A0 i0 j0 μsel δSign ωsec σsec hNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, _hcol_inj, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport⟩
  let χ : ℕ → ℕ → Section1.ClassFunction M := fun i j => μsel (row i) (col j)
  let δ : ℕ → ℤ := fun j => δSign (col j)
  let ωsel : ℕ → ℕ → Section1.ClassFunction Wsec := fun i j => ωsec (row i) (col j)
  have hSelected :
      hypothesis_13_1_selectedTypePFourSixTableData hTypeP ω hω τM
        χ δ Wsec ωsel σsec :=
    hypothesis_13_1_selectedTypePFourSixTableData_of_package
      hTypeP ω hω τM hNotation row col hrow0 hcol0 hcol_ne hrow_inj
      hrow_surj hcol_surj hIndTransport hExactTransport
  refine ⟨χ, δ, Wsec, ωsel, σsec, hSelected, ?_, ?_⟩
  · intro j hj0 hj
    have hcolj_ne : col j ≠ j0 := hcol_ne j hj0 hj
    rcases Section10.exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
        hNotation hcolj_ne with
      ⟨j', hj'0, hj'ne, hconj⟩
    rcases hcol_surj j' with ⟨k, hk, hcolk⟩
    have hk0 : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hkzero
      have hbad : j' = j0 := by
        calc
          j' = col k := hcolk.symm
          _ = col 0 := by rw [hkzero]
          _ = j0 := hcol0
      exact hj'0 hbad
    have hkne : k ≠ j := by
      intro hkj
      apply hj'ne
      calc
        j' = col k := hcolk.symm
        _ = col j := by rw [hkj]
    refine ⟨k, hk0, hk, hkne, ?_⟩
    simpa [χ, hrow0, hcolk] using hconj.symm
  · intro j k hj0 hj hk0 hk hχ
    have hjne : col j ≠ j0 := hcol_ne j hj0 hj
    have hkne : col k ≠ j0 := hcol_ne k hk0 hk
    have hχsel :
        μsel i0 (col k) = Section1.conjugateCharacter (μsel i0 (col j)) := by
      simpa [χ, hrow0] using hχ
    have hσsel :
        σsec (ωsec i0 (col k)) =
          Section1.conjugateCharacter (σsec (ωsec i0 (col j))) :=
      hypothesis_13_1_conjugateIndexSelectedPackageSigmaOmegaAlignment_source
        hTypeP hNotation (col j) (col k) hjne hkne hχsel
    simpa [ωsel, hrow0] using hσsel


private theorem hypothesis_13_1_typePFourSixDadeDifference_source
    {G : Type u} [Group G] [Finite G]
    {W M K U Wleft Wright : Subgroup G}
    (hTypeP : Section8.typePData M K U Wleft Wright)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W Wleft Wright
      (Nat.card Wright) (Nat.card Wleft) ω)
    (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (hFourSix : typePFourSixTauSourceData M K U Wleft Wright τM) :
    ∃ (χ : ℕ → ℕ → Section1.ClassFunction M)
      (δ : ℕ → ℤ)
      (Wsel : Subgroup M)
      (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
      (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_selectedTypePFourSixTableData hTypeP ω hω τM
          χ δ Wsel ωsel σsel ∧
        ∀ i j k, i < Nat.card Wleft → 0 < j → j < Nat.card Wright →
          0 < k → k < Nat.card Wright →
            Section1.degree (χ i j) = Section1.degree (χ i k) →
              τM (χ i j - χ i k) =
                (((δ j : ℤ) : ℂ) • (σsel (ωsel i j) - σsel (ωsel i k))) := by
  classical
  rcases hFourSix with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hNotation, _hSigmaAgree, ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      hTypeP ω hω τM Wsec A A0 i0 j0 μsel δSign ωsec σsec hNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, _hcol_inj, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport⟩
  let χ : ℕ → ℕ → Section1.ClassFunction M := fun i j => μsel (row i) (col j)
  let δ : ℕ → ℤ := fun j => δSign (col j)
  let ωsel : ℕ → ℕ → Section1.ClassFunction Wsec := fun i j => ωsec (row i) (col j)
  have hSelected :
      hypothesis_13_1_selectedTypePFourSixTableData hTypeP ω hω τM
        χ δ Wsec ωsel σsec :=
    hypothesis_13_1_selectedTypePFourSixTableData_of_package
      hTypeP ω hω τM hNotation row col hrow0 hcol0 hcol_ne hrow_inj
      hrow_surj hcol_surj hIndTransport hExactTransport
  refine ⟨χ, δ, Wsec, ωsel, σsec, hSelected, ?_⟩
  intro i j k _hi hj0 hj hk0 hk hdeg
  have hjne : col j ≠ j0 := hcol_ne j hj0 hj
  have hkne : col k ≠ j0 := hcol_ne k hk0 hk
  have h48 := Section10.theorem_4_8_of_section10FourSixNotationSupportedData hNotation
  rcases h48 (row i) (col j) (col k) hjne hkne (by
      simpa [χ] using hdeg) with
    ⟨_hsupp, _hdelta, hτ⟩
  simpa [χ, δ, ωsel] using hτ

private theorem hypothesis_13_1_muTableData_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W W1 W2
      (Nat.card W2) (Nat.card W1) ω)
    (_η : ℕ → ℕ → Section1.ClassFunction G)
    (_σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS) :
    ∃ (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (δ : ℕ → ℤ),
        (∀ j, j < Nat.card W2 → δ j = 1 ∨ δ j = -1) ∧
        (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
          Section1.IsIrreducibleCharacterOnGroup (μ i j)) ∧
        (∀ j, 0 < j → j < Nat.card W2 →
          μ 0 j ≠ Section1.principalCharacter Smax) ∧
        (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
          Section1.inducedCF (W.subgroupOf Smax)
              (Section1.subgroupOfClassFunction (T := Smax) (ω i j - ω 0 j)) =
            (((δ j : ℤ) : ℂ) • (μ i j - μ 0 j))) ∧
        (∀ j k, 0 < j → j < Nat.card W2 → 0 < k →
          k < Nat.card W2 →
            Section1.degree (μ 0 j) = Section1.degree (μ 0 k)) ∧
        (((δ 0 : ℤ) : ℂ) • μ 0 0 = Section1.principalCharacter Smax) :=
  hypothesis_13_1_typePFourSixTableData_source _hSTypeP ω hω τS hFourSixS

private theorem hypothesis_13_1_muNotationData_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W W1 W2
      (Nat.card W2) (Nat.card W1) ω)
    (_η : ℕ → ℕ → Section1.ClassFunction G)
    (_σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (_hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS) :
    ∃ (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (δ : ℕ → ℤ),
        (∀ j, j < Nat.card W2 → δ j = 1 ∨ δ j = -1) ∧
        (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
          Section1.IsIrreducibleCharacterOnGroup (μ i j)) ∧
        (∀ j, 0 < j → j < Nat.card W2 →
          μ 0 j ≠ Section1.principalCharacter Smax) ∧
        (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
          Section1.inducedCF (W.subgroupOf Smax)
              (Section1.subgroupOfClassFunction (T := Smax) (ω i j - ω 0 j)) =
            (((δ j : ℤ) : ℂ) • (μ i j - μ 0 j))) ∧
        (∀ j, j < Nat.card W2 →
          μsum j = (Finset.range (Nat.card W1)).sum (fun i => μ i j)) ∧
        (∀ j k, 0 < j → j < Nat.card W2 → 0 < k →
          k < Nat.card W2 →
            Section1.degree (μ 0 j) = Section1.degree (μ 0 k)) ∧
        (((δ 0 : ℤ) : ℂ) • μ 0 0 = Section1.principalCharacter Smax) := by
  rcases hypothesis_13_1_muTableData_source
      _hcase _hSTypeP _hTTypeP ω hω _η _σ τS _hFourSixS with
    ⟨μ, δ, hδ, hμirr, hμzero_nonprincipal, hμind, hμzeroDegree, hbaseS⟩
  let μsum : ℕ → Section1.ClassFunction Smax :=
    fun j => (Finset.range (Nat.card W1)).sum (fun i => μ i j)
  refine ⟨μ, μsum, δ, hδ, hμirr, hμzero_nonprincipal, hμind, ?_,
    hμzeroDegree, hbaseS⟩
  · intro j _hj
    rfl

private theorem hypothesis_13_1_nuTableData_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W W1 W2
      (Nat.card W2) (Nat.card W1) ω)
    (_η : ℕ → ℕ → Section1.ClassFunction G)
    (_σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∃ (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (δ' : ℕ → ℤ),
        (∀ i, i < Nat.card W1 → δ' i = 1 ∨ δ' i = -1) ∧
        (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
          Section1.IsIrreducibleCharacterOnGroup (ν i j)) ∧
        (∀ i, 0 < i → i < Nat.card W1 →
          ν i 0 ≠ Section1.principalCharacter Tmax) ∧
        (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
          Section1.inducedCF (W.subgroupOf Tmax)
              (Section1.subgroupOfClassFunction (T := Tmax) (ω i j - ω i 0)) =
            (((δ' i : ℤ) : ℂ) • (ν i j - ν i 0))) ∧
        (∀ i k, 0 < i → i < Nat.card W1 → 0 < k →
          k < Nat.card W1 →
            Section1.degree (ν i 0) = Section1.degree (ν k 0)) ∧
        (((δ' 0 : ℤ) : ℂ) • ν 0 0 = Section1.principalCharacter Tmax) := by
  let ωT : ℕ → ℕ → Section1.ClassFunction W := fun j i => ω i j
  have hωT : hypothesis_13_1_omegaNotationData W W2 W1
      (Nat.card W1) (Nat.card W2) ωT :=
    hypothesis_13_1_omegaNotationData_swap_local hω
  rcases hypothesis_13_1_typePFourSixTableData_source
      _hTTypeP ωT hωT τT hFourSixT with
    ⟨χ, δ', hδ', hχirr, hχzero_nonprincipal, hχind, hχzeroDegree, hbaseT⟩
  refine ⟨(fun i j => χ j i), δ', hδ', ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj
    exact hχirr j i hj hi
  · intro i hi0 hi
    exact hχzero_nonprincipal i hi0 hi
  · intro i j hi hj
    simpa [ωT] using hχind j i hj hi
  · intro i k hi0 hi hk0 hk
    exact hχzeroDegree i k hi0 hi hk0 hk
  · simpa using hbaseT

private theorem hypothesis_13_1_nuNotationData_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W W1 W2
      (Nat.card W2) (Nat.card W1) ω)
    (_η : ℕ → ℕ → Section1.ClassFunction G)
    (_σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∃ (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ' : ℕ → ℤ),
        (∀ i, i < Nat.card W1 → δ' i = 1 ∨ δ' i = -1) ∧
        (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
          Section1.IsIrreducibleCharacterOnGroup (ν i j)) ∧
        (∀ i, 0 < i → i < Nat.card W1 →
          ν i 0 ≠ Section1.principalCharacter Tmax) ∧
        (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
          Section1.inducedCF (W.subgroupOf Tmax)
              (Section1.subgroupOfClassFunction (T := Tmax) (ω i j - ω i 0)) =
            (((δ' i : ℤ) : ℂ) • (ν i j - ν i 0))) ∧
        (∀ i, i < Nat.card W1 →
          νsum i = (Finset.range (Nat.card W2)).sum (fun j => ν i j)) ∧
        (∀ i k, 0 < i → i < Nat.card W1 → 0 < k →
          k < Nat.card W1 →
            Section1.degree (ν i 0) = Section1.degree (ν k 0)) ∧
        (((δ' 0 : ℤ) : ℂ) • ν 0 0 = Section1.principalCharacter Tmax) := by
  rcases hypothesis_13_1_nuTableData_source
      _hcase _hSTypeP _hTTypeP ω hω _η _σ τT _hFourSixT with
    ⟨ν, δ', hδ', hνirr, hνzero_nonprincipal, hνind, hνzeroDegree, hbaseT⟩
  let νsum : ℕ → Section1.ClassFunction Tmax :=
    fun i => (Finset.range (Nat.card W2)).sum (fun j => ν i j)
  refine ⟨ν, νsum, δ', hδ', hνirr, hνzero_nonprincipal, hνind, ?_,
    hνzeroDegree, hbaseT⟩
  · intro i _hi
    rfl

private theorem hypothesis_13_1_characterNotationData_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    hypothesis_13_1_characterNotationData Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) := by
  rcases hypothesis_13_1_omegaEtaNotationData_source
      hmin _hcase _hSTypeP _hTTypeP with
    ⟨ω, η, σ, hω, hσ, hη⟩
  rcases hypothesis_13_1_muNotationData_source
      _hcase _hSTypeP _hTTypeP ω hω η σ τS hFourSixS with
    ⟨μ, μsum, δ, hδ, hμirr, hμzero_nonprincipal, hμind, hμsum,
      hμzeroDegree, hbaseS⟩
  rcases hypothesis_13_1_nuNotationData_source
      _hcase _hSTypeP _hTTypeP ω hω η σ τT hFourSixT with
    ⟨ν, νsum, δ', hδ', hνirr, hνzero_nonprincipal, hνind, hνsum,
      hνzeroDegree, hbaseT⟩
  exact ⟨ω, η, μ, ν, μsum, νsum, δ, δ', σ,
    hω, hσ, hη, hδ, hδ', hμirr, hνirr, hμzero_nonprincipal,
    hνzero_nonprincipal, hμind, hνind, hμsum, hνsum, hbaseS, hbaseT,
    hμzeroDegree, hνzeroDegree⟩

private theorem hypothesis_13_1_section12InternalDirectProduct_swap
    {G : Type u} [Group G]
    {W1 W2 W : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W) :
    section12InternalDirectProduct W2 W1 W := by
  rcases hprod with ⟨hW1le, hW2le, hW, hdisj, hcent⟩
  refine ⟨hW2le, hW1le, ?_, hdisj.symm, ?_⟩
  · simpa [sup_comm] using hW
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent hy) x hx).symm

private theorem hypothesis_13_1_case_b_data_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q : Subgroup G}
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q) :
    Section8.theorem_8_8_case_b_data W W2 W1 Tmax Smax Q P := by
  rcases hcase with
    ⟨hprod, hcyc, hW1ne, hW2ne, hnorm, hSmax, hTmax, hP, hQ,
      hSnotTypeI, hTnotTypeI, hSeq, hTeq, hSinf, hTinf, hSW2leSecond,
      hTW1leSecond, hST, hCover, hTypeII, hSType, hTType, hAligned⟩
  refine ⟨hypothesis_13_1_section12InternalDirectProduct_swap hprod, hcyc,
    hW2ne, hW1ne, ?_, hTmax, hSmax, hQ, hP, hTnotTypeI, hSnotTypeI,
    hTeq, hSeq, hTinf, hSinf, hTW1leSecond, hSW2leSecond, ?_, ?_, ?_,
    hTType, hSType, ?_⟩
  · intro W0 hW0ne hW0sub
    exact hnorm W0 hW0ne (by
      intro x hx
      simpa [Set.union_comm] using hW0sub hx)
  · simpa [inf_comm] using hST
  · intro M hM
    rcases hCover M hM with hS | hT | hI
    · exact Or.inr (Or.inl hS)
    · exact Or.inl hT
    · exact Or.inr (Or.inr hI)
  · rcases hTypeII with hSII | hTII
    · exact Or.inr hSII
    · exact Or.inl hTII
  · rcases hAligned with ⟨U, V, hSP, hTQ⟩
    exact ⟨V, U, hTQ, hSP⟩

private theorem hypothesis_13_1_theorem_3_2_map_statement_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
    Section3.theorem_3_2_map_statement W2 W1 W σ := by
  rcases hσ with ⟨hiso, hvirt, hind, hclass, hprin, hagree, hvanish⟩
  refine ⟨hiso, hvirt, ?_, hclass, hprin, ?_, ?_⟩
  · intro α hα
    exact hind α (by simpa [Section3.cyclicTISet, Set.union_comm] using hα)
  · intro α hα x hx
    simpa [Section3.cyclicTISet, Set.union_comm] using hagree α hα x (by
      simpa [Section3.cyclicTISet, Set.union_comm] using hx)
  · intro χ hχ hχnot
    simpa [Section3.VanishesOn, Section3.cyclicTISet, Set.union_comm] using
      hvanish χ hχ hχnot

private theorem hypothesis_13_1_omegaNotationData_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G} {p q : ℕ}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    (hω : hypothesis_13_1_omegaNotationData W W1 W2 p q ω) :
    hypothesis_13_1_omegaNotationData W W2 W1 q p (fun i j => ω j i) := by
  rcases hω with ⟨h31, hq, hp, ωFin, hωFin, hωspec⟩
  refine ⟨Section3.hypothesis_3_1_statement_swap h31, hp, hq,
    (fun i j => ωFin j i), ?_, ?_⟩
  · exact Section3.notation_3_3_statement_swap hωFin
  · intro i j hi hj
    exact hωspec j i hj hi

private theorem hypothesis_13_1_characterNotationDataFor_swap_local
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G} {p q : ℕ}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    hypothesis_13_1_characterNotationDataFor Tmax Smax W W2 W1 q p
      (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
      (fun i j => μ j i) νsum μsum δ' δ σ := by
  rcases hnotation with
    ⟨hω, hσ, hη, hδ, hδ', hμirr, hνirr, hμzero_nonprincipal,
      hνzero_nonprincipal, hμind, hνind, hμsum, hνsum, hbaseS, hbaseT,
      hμzeroDegree, hνzeroDegree⟩
  refine ⟨hypothesis_13_1_omegaNotationData_swap hω,
    hypothesis_13_1_theorem_3_2_map_statement_swap hσ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj
    exact hη j i hj hi
  · intro j hj
    exact hδ' j hj
  · intro i hi
    exact hδ i hi
  · intro i j hi hj
    exact hνirr j i hj hi
  · intro i j hi hj
    exact hμirr j i hj hi
  · intro j hj0 hjq
    exact hνzero_nonprincipal j hj0 hjq
  · intro i hi0 hip
    exact hμzero_nonprincipal i hi0 hip
  · intro i j hi hj
    exact hνind j i hj hi
  · intro i j hi hj
    exact hμind j i hj hi
  · intro j hj
    exact hνsum j hj
  · intro i hi
    exact hμsum i hi
  · exact hbaseT
  · exact hbaseS
  · intro j k hj0 hjq hk0 hkq
    exact hνzeroDegree j k hj0 hjq hk0 hkq
  · intro i k hi0 hip hk0 hkp
    exact hμzeroDegree i k hi0 hip hk0 hkp

private theorem hypothesis_13_1_irreducible_sub_eq_sub
    {G : Type u} [Group G] [Finite G]
    {a b c d : Section1.ClassFunction G}
    (ha : Section1.IsIrreducibleCharacterOnGroup a)
    (hb : Section1.IsIrreducibleCharacterOnGroup b)
    (hc : Section1.IsIrreducibleCharacterOnGroup c)
    (hd : Section1.IsIrreducibleCharacterOnGroup d)
    (hab : a ≠ b)
    (hcd : c ≠ d)
    (heq : a - b = c - d) :
    a = c ∧ b = d := by
  have haa : Section1.scalarProduct G a a = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self ha
  have hab0 : Section1.scalarProduct G a b = 0 :=
    Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne ha hb hab
  have hpair := congrArg (fun ξ => Section1.scalarProduct G a ξ) heq
  change Section1.scalarProduct G a (a - b) =
    Section1.scalarProduct G a (c - d) at hpair
  by_cases hac : a = c
  · subst c
    exact ⟨rfl, sub_right_inj.mp heq⟩
  · have hac0 : Section1.scalarProduct G a c = 0 :=
      Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne ha hc hac
    by_cases had : a = d
    · subst d
      rw [Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
        haa, hab0, hac0] at hpair
      norm_num at hpair
    · have had0 : Section1.scalarProduct G a d = 0 :=
        Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne ha hd had
      rw [Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
        haa, hab0, hac0, had0] at hpair
      norm_num at hpair

private theorem hypothesis_13_1_signed_irreducible_sub_eq_cases
    {G : Type u} [Group G] [Finite G]
    {eps1 eps2 : ℤ}
    {a b c d : Section1.ClassFunction G}
    (he1 : eps1 = 1 ∨ eps1 = -1)
    (he2 : eps2 = 1 ∨ eps2 = -1)
    (ha : Section1.IsIrreducibleCharacterOnGroup a)
    (hb : Section1.IsIrreducibleCharacterOnGroup b)
    (hc : Section1.IsIrreducibleCharacterOnGroup c)
    (hd : Section1.IsIrreducibleCharacterOnGroup d)
    (hcd : c ≠ d)
    (heq : (((eps1 : ℤ) : ℂ) • (a - b)) =
      (((eps2 : ℤ) : ℂ) • (c - d))) :
    (eps1 = eps2 ∧ a = c ∧ b = d) ∨
      (eps1 = -eps2 ∧ a = d ∧ b = c) := by
  rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl
  · have h : a - b = c - d := by simpa using heq
    have hab : a ≠ b := by
      intro hab
      apply hcd
      exact sub_eq_zero.mp (by rw [← h, hab]; simp)
    exact Or.inl
      ⟨rfl, hypothesis_13_1_irreducible_sub_eq_sub ha hb hc hd hab hcd h⟩
  · have h : a - b = d - c := by
      simpa [sub_eq_add_neg, add_comm] using heq
    have hab : a ≠ b := by
      intro hab
      apply hcd.symm
      exact sub_eq_zero.mp (by rw [← h, hab]; simp)
    exact Or.inr
      ⟨by norm_num,
        hypothesis_13_1_irreducible_sub_eq_sub ha hb hd hc hab hcd.symm h⟩
  · have h : b - a = c - d := by simpa using heq
    have hba : b ≠ a := by
      intro hba
      apply hcd
      exact sub_eq_zero.mp (by rw [← h, hba]; simp)
    have hcase :=
      hypothesis_13_1_irreducible_sub_eq_sub hb ha hc hd hba hcd h
    exact Or.inr ⟨by norm_num, hcase.2, hcase.1⟩
  · have h : b - a = d - c := by simpa using heq
    have hba : b ≠ a := by
      intro hba
      apply hcd.symm
      exact sub_eq_zero.mp (by rw [← h, hba]; simp)
    have hcase :=
      hypothesis_13_1_irreducible_sub_eq_sub hb ha hd hc hba hcd.symm h
    exact Or.inl ⟨rfl, hcase.2, hcase.1⟩

private theorem hypothesis_13_1_signed_row_alignment
    {G I : Type u} [Group G] [Finite G]
    (n : ℕ)
    (hthree : 3 ≤ n)
    (row : ℕ → I)
    (i0 : I)
    (hrow0 : row 0 = i0)
    (hrow_inj : ∀ i k, i < n → k < n → row i = row k → i = k)
    (μ : ℕ → Section1.ClassFunction G)
    (μsel : I → Section1.ClassFunction G)
    (δ δsel : ℤ)
    (hδ : δ = 1 ∨ δ = -1)
    (hδsel : δsel = 1 ∨ δsel = -1)
    (hμIrr : ∀ i, i < n → Section1.IsIrreducibleCharacterOnGroup (μ i))
    (hμselIrr : ∀ r, Section1.IsIrreducibleCharacterOnGroup (μsel r))
    (hμselDistinct : ∀ r s, r ≠ s → μsel r ≠ μsel s)
    (hdiff : ∀ i, i < n →
      (((δ : ℤ) : ℂ) • (μ i - μ 0)) =
        (((δsel : ℤ) : ℂ) • (μsel (row i) - μsel i0))) :
    δ = δsel ∧ ∀ i, i < n → μ i = μsel (row i) := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have h2 : 2 < n := by omega
  have hrow_ne_base : ∀ i, i < n → 0 < i → row i ≠ i0 := by
    intro i hi hi0 hri
    have : i = 0 := hrow_inj i 0 hi h0 (hri.trans hrow0.symm)
    omega
  have hrow12 : row 1 ≠ row 2 := by
    intro h
    have : (1 : ℕ) = 2 := hrow_inj 1 2 h1 h2 h
    omega
  have hcase : ∀ i, i < n → 0 < i →
      (δ = δsel ∧ μ i = μsel (row i) ∧ μ 0 = μsel i0) ∨
        (δ = -δsel ∧ μ i = μsel i0 ∧ μ 0 = μsel (row i)) := by
    intro i hi hi0
    exact hypothesis_13_1_signed_irreducible_sub_eq_cases hδ hδsel
      (hμIrr i hi) (hμIrr 0 h0) (hμselIrr (row i)) (hμselIrr i0)
      (hμselDistinct (row i) i0 (hrow_ne_base i hi hi0)) (hdiff i hi)
  rcases hcase 1 h1 (by omega) with hordered1 | hswapped1
  · rcases hordered1 with ⟨hδEq, _hμ1, hbase⟩
    refine ⟨hδEq, ?_⟩
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa [hrow0] using hbase
    · rcases hcase i hi (Nat.pos_of_ne_zero hi0) with hordered | hswapped
      · exact hordered.2.1
      · exfalso
        apply hμselDistinct (row i) i0
          (hrow_ne_base i hi (Nat.pos_of_ne_zero hi0))
        calc
          μsel (row i) = μ 0 := hswapped.2.2.symm
          _ = μsel i0 := hbase
  · rcases hcase 2 h2 (by omega) with hordered2 | hswapped2
    · exfalso
      apply hμselDistinct (row 1) i0 (hrow_ne_base 1 h1 (by omega))
      calc
        μsel (row 1) = μ 0 := hswapped1.2.2.symm
        _ = μsel i0 := hordered2.2.2
    · exfalso
      apply hμselDistinct (row 1) (row 2) hrow12
      calc
        μsel (row 1) = μ 0 := hswapped1.2.2.symm
        _ = μsel (row 2) := hswapped2.2.2

private theorem hypothesis_13_1_dadeDifferencePointwiseMuDeltaAlignment_selectedColumn
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax : Subgroup G}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    {Wsel : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction Smax}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsel}
    {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G}
    (hSelNotation : Section10.section10FourSixNotationSupportedData
      Smax W1 W2 Wsel A A0 i0 j0 μsel δSign ωsec σsel τS)
    (row : ℕ → I) (col : ℕ → J)
    (hrow0 : row 0 = i0)
    (_hcol0 : col 0 = j0)
    (_hcol_ne : ∀ j, 0 < j → j < Nat.card W2 → col j ≠ j0)
    (hrow_inj : ∀ i k, i < Nat.card W1 → k < Nat.card W1 →
      row i = row k → i = k)
    (hIndTransport : ∀ i j, i < Nat.card W1 → j < Nat.card W2 →
      Section1.inducedCF (W.subgroupOf Smax)
          (Section1.subgroupOfClassFunction (T := Smax) (ω i j - ω 0 j)) =
        Section1.inducedCF Wsel
          (ωsec (row i) (col j) - ωsec i0 (col j)))
    (j : ℕ) (_hj0 : 0 < j) (hj : j < Nat.card W2) :
    δ j = δSign (col j) ∧
      ∀ i, i < Nat.card W1 → μ i j = μsel (row i) (col j) := by
  rcases hnotation with
    ⟨hω, _hσ, _hη, hδ, _hδ', hμIrr, _hνIrr,
      _hμNonprincipal, _hνNonprincipal, hμInd, _hνInd,
      _hμSum, _hνSum, _hBaseS, _hBaseT, _hμDegree, _hνDegree⟩
  have hthree : 3 ≤ Nat.card W1 :=
    Section3.natCard_left_ge_three_of_hypothesis_3_1 hω.1
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData
      hSelNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨_hωsec, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  rcases h43b with
    ⟨_hσmap, _hsign, hSelIrr, hSelDistinct, hSelInd, _hSelSigma⟩
  have hdiff : ∀ i, i < Nat.card W1 →
      (((δ j : ℤ) : ℂ) • (μ i j - μ 0 j)) =
        (((δSign (col j) : ℤ) : ℂ) •
          (μsel (row i) (col j) - μsel i0 (col j))) := by
    intro i hi
    calc
      (((δ j : ℤ) : ℂ) • (μ i j - μ 0 j)) =
          Section1.inducedCF (W.subgroupOf Smax)
            (Section1.subgroupOfClassFunction (T := Smax)
              (ω i j - ω 0 j)) := (hμInd i j hi hj).symm
      _ = Section1.inducedCF Wsel
          (ωsec (row i) (col j) - ωsec i0 (col j)) :=
        hIndTransport i j hi hj
      _ = (((δSign (col j) : ℤ) : ℂ) •
          (μsel (row i) (col j) - μsel i0 (col j))) :=
        hSelInd (row i) (col j)
  exact hypothesis_13_1_signed_row_alignment
    (Nat.card W1) hthree row i0 hrow0 hrow_inj
    (fun i => μ i j) (fun r => μsel r (col j)) (δ j) (δSign (col j))
    (hδ j hj)
    (Section10.deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData
      hSelNotation (col j))
    (fun i hi => hμIrr i j hi hj)
    (fun r => hSelIrr r (col j))
    (fun r s hrs => hSelDistinct (r, col j) (s, col j) (by
      intro hp
      exact hrs (congrArg Prod.fst hp)))
    hdiff

private theorem hypothesis_13_1_dadeDifferencePointwiseMuAlignment_selectedEntry_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax : Subgroup G}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G} :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ {I J : Type u} [Fintype I] [DecidableEq I]
            [Fintype J] [DecidableEq J]
            {Wsel : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
            {μsel : I → J → Section1.ClassFunction Smax}
            {δSign : J → ℤ}
            {ωsec : I → J → Section1.ClassFunction Wsel}
            {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G},
              Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsel
                A A0 i0 j0 μsel δSign ωsec σsel τS →
              ∀ (row : ℕ → I) (col : ℕ → J),
                row 0 = i0 →
                col 0 = j0 →
                (∀ j, 0 < j → j < Nat.card W2 → col j ≠ j0) →
                (∀ i k, i < Nat.card W1 → k < Nat.card W1 →
                  row i = row k → i = k) →
                (∀ iSel : I, ∃ k, k < Nat.card W1 ∧ row k = iSel) →
                (∀ jSel : J, ∃ k, k < Nat.card W2 ∧ col k = jSel) →
                (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
                  Section1.inducedCF (W.subgroupOf Smax)
                      (Section1.subgroupOfClassFunction (T := Smax)
                        (ω i j - ω 0 j)) =
                    Section1.inducedCF Wsel
                      (ωsec (row i) (col j) - ωsec i0 (col j))) →
                ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
                  μ i j = μsel (row i) (col j) := by
  /-
  Source PF `(13.1)` visible/selected `μ` convention for the concrete
  selected Section `(4.6)` row and column maps.  The S/T family, Dade, and
  T-side hypotheses are not part of this entrywise alignment boundary.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation I J _instI _decI _instJ _decJ
    Wsel A A0 i0 j0 μsel δSign ωsec σsel hSelNotation row col hrow0 hcol0
    hcol_ne hrow_inj _hrow_surj _hcol_surj hIndTransport i j hi hj0 hj
  exact
    (hypothesis_13_1_dadeDifferencePointwiseMuDeltaAlignment_selectedColumn
      ω η μ ν μsum νsum δ δ' σ hnotation hSelNotation row col hrow0 hcol0
      hcol_ne hrow_inj hIndTransport j hj0 hj).2 i hi

private theorem hypothesis_13_1_dadeDifferencePointwiseMuAlignment_selectedTable_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (_Sfam : Finset (Section1.ClassFunction Smax))
    (_Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P _Sfam)
    (_hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q _Tfam)
    (_hDadeS : dadeIsometryRelativeToAZero Smax P _Sfam τS)
    (_hDadeT : dadeIsometryRelativeToAZero Tmax Q _Tfam τT)
    (_hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ {I J : Type u} [Fintype I] [DecidableEq I]
            [Fintype J] [DecidableEq J]
            {Wsel : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
            {μsel : I → J → Section1.ClassFunction Smax}
            {δSign : J → ℤ}
            {ωsec : I → J → Section1.ClassFunction Wsel}
            {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G},
              Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsel
                A A0 i0 j0 μsel δSign ωsec σsel τS →
              ∀ (row : ℕ → I) (col : ℕ → J),
                row 0 = i0 →
                col 0 = j0 →
                (∀ j, 0 < j → j < Nat.card W2 → col j ≠ j0) →
                (∀ i k, i < Nat.card W1 → k < Nat.card W1 →
                  row i = row k → i = k) →
                (∀ iSel : I, ∃ k, k < Nat.card W1 ∧ row k = iSel) →
                (∀ jSel : J, ∃ k, k < Nat.card W2 ∧ col k = jSel) →
                (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
                  Section1.inducedCF (W.subgroupOf Smax)
                      (Section1.subgroupOfClassFunction (T := Smax)
                        (ω i j - ω 0 j)) =
                    Section1.inducedCF Wsel
                      (ωsec (row i) (col j) - ωsec i0 (col j))) →
                ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
                  μ i j = μsel (row i) (col j) := by
  /-
  Checked wrapper around the entrywise source boundary for visible/selected
  `μ` alignment.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation I J _instI _decI _instJ _decJ
    Wsel A A0 i0 j0 μsel δSign ωsec σsel hSelNotation row col hrow0 hcol0
    hcol_ne hrow_inj hrow_surj hcol_surj hIndTransport i j hi hj0 hj
  exact
    hypothesis_13_1_dadeDifferencePointwiseMuAlignment_selectedEntry_source
      ω η μ ν μsum νsum δ δ' σ hnotation hSelNotation
      row col hrow0 hcol0 hcol_ne hrow_inj hrow_surj hcol_surj hIndTransport
      i j hi hj0 hj

private theorem hypothesis_13_1_dadeDifferencePointwiseMuAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          ∀ (χ : ℕ → ℕ → Section1.ClassFunction Smax)
            (δsel : ℕ → ℤ)
            (Wsel : Subgroup Smax)
            (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
            (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G),
            hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
                hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
            μ i j = χ i j := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
    hSelected i j hi hj0 hj
  rcases hSelected with
    ⟨I, instI, decI, J, instJ, decJ, A, A0, i0, j0, μsel, δSign, ωsec,
      hSelNotation, row, col, hrow0, hcol0, hcol_ne, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, _hExactTransport, hχ, _hδsel, _hωsel⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  have hsrc : μ i j = μsel (row i) (col j) :=
    hypothesis_13_1_dadeDifferencePointwiseMuAlignment_selectedTable_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation
      hSelNotation row col hrow0 hcol0 hcol_ne hrow_inj hrow_surj
      hcol_surj hIndTransport i j hi hj0 hj
  exact hsrc.trans (hχ i j hi hj).symm

private theorem hypothesis_13_1_dadeDifferencePointwiseDeltaAlignment_selectedColumn_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax : Subgroup G}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G} :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ {I J : Type u} [Fintype I] [DecidableEq I]
            [Fintype J] [DecidableEq J]
            {Wsel : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
            {μsel : I → J → Section1.ClassFunction Smax}
            {δSign : J → ℤ}
            {ωsec : I → J → Section1.ClassFunction Wsel}
            {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G},
              Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsel
                A A0 i0 j0 μsel δSign ωsec σsel τS →
              ∀ (row : ℕ → I) (col : ℕ → J),
                row 0 = i0 →
                col 0 = j0 →
                (∀ j, 0 < j → j < Nat.card W2 → col j ≠ j0) →
                (∀ i k, i < Nat.card W1 → k < Nat.card W1 →
                  row i = row k → i = k) →
                (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
                  Section1.inducedCF (W.subgroupOf Smax)
                      (Section1.subgroupOfClassFunction (T := Smax)
                        (ω i j - ω 0 j)) =
                    Section1.inducedCF Wsel
                      (ωsec (row i) (col j) - ωsec i0 (col j))) →
                ∀ j, 0 < j → j < Nat.card W2 →
                  δ j = δSign (col j) := by
  /-
  Source PF `(13.1)` visible/selected sign convention for the concrete
  selected Section `(4.6)` column.  Its orientation is fixed by the same
  two-row signed-difference comparison as the entrywise `μ` alignment.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation I J _instI _decI _instJ _decJ
    Wsel A A0 i0 j0 μsel δSign ωsec σsel hSelNotation row col hrow0 hcol0
    hcol_ne hrow_inj hIndTransport j hj0 hj
  exact
    (hypothesis_13_1_dadeDifferencePointwiseMuDeltaAlignment_selectedColumn
      ω η μ ν μsum νsum δ δ' σ hnotation hSelNotation row col hrow0 hcol0
      hcol_ne hrow_inj hIndTransport j hj0 hj).1

private theorem hypothesis_13_1_dadeDifferencePointwiseDeltaAlignment_selectedTable_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (_Sfam : Finset (Section1.ClassFunction Smax))
    (_Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P _Sfam)
    (_hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q _Tfam)
    (_hDadeS : dadeIsometryRelativeToAZero Smax P _Sfam τS)
    (_hDadeT : dadeIsometryRelativeToAZero Tmax Q _Tfam τT)
    (_hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ {I J : Type u} [Fintype I] [DecidableEq I]
            [Fintype J] [DecidableEq J]
            {Wsel : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
            {μsel : I → J → Section1.ClassFunction Smax}
            {δSign : J → ℤ}
            {ωsec : I → J → Section1.ClassFunction Wsel}
            {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G},
              Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsel
                A A0 i0 j0 μsel δSign ωsec σsel τS →
              ∀ (row : ℕ → I) (col : ℕ → J),
                row 0 = i0 →
                col 0 = j0 →
                (∀ j, 0 < j → j < Nat.card W2 → col j ≠ j0) →
                (∀ i k, i < Nat.card W1 → k < Nat.card W1 →
                  row i = row k → i = k) →
                (∀ iSel : I, ∃ k, k < Nat.card W1 ∧ row k = iSel) →
                (∀ jSel : J, ∃ k, k < Nat.card W2 ∧ col k = jSel) →
                (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
                  Section1.inducedCF (W.subgroupOf Smax)
                      (Section1.subgroupOfClassFunction (T := Smax)
                        (ω i j - ω 0 j)) =
                    Section1.inducedCF Wsel
                      (ωsec (row i) (col j) - ωsec i0 (col j))) →
                ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
                  δ j = δSign (col j) := by
  /-
  Checked wrapper around the selected-column sign comparison.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation I J _instI _decI _instJ _decJ
    Wsel A A0 i0 j0 μsel δSign ωsec σsel hSelNotation row col hrow0 hcol0
    hcol_ne hrow_inj _hrow_surj _hcol_surj hIndTransport _i j _hi hj0 hj
  exact
    hypothesis_13_1_dadeDifferencePointwiseDeltaAlignment_selectedColumn_source
      ω η μ ν μsum νsum δ δ' σ hnotation hSelNotation row col hrow0 hcol0
      hcol_ne hrow_inj hIndTransport j hj0 hj

private theorem hypothesis_13_1_dadeDifferencePointwiseDeltaAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          ∀ (χ : ℕ → ℕ → Section1.ClassFunction Smax)
            (δsel : ℕ → ℤ)
            (Wsel : Subgroup Smax)
            (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
            (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G),
            hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
                hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
            δ j = δsel j := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
    hSelected i j hi hj0 hj
  rcases hSelected with
    ⟨I, instI, decI, J, instJ, decJ, A, A0, i0, j0, μsel, δSign, ωsec,
      hSelNotation, row, col, hrow0, hcol0, hcol_ne, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, _hExactTransport, _hχ, hδsel, _hωsel⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  have hsrc : δ j = δSign (col j) :=
    hypothesis_13_1_dadeDifferencePointwiseDeltaAlignment_selectedTable_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation
      hSelNotation row col hrow0 hcol0 hcol_ne hrow_inj hrow_surj
      hcol_surj hIndTransport i j hi hj0 hj
  exact hsrc.trans (hδsel j hj).symm

private theorem hypothesis_13_1_sigma_transport_eq_of_cyclicTI_agreement
    {G L : Type u} [Group G] [Finite G] [Group L] [Finite L]
    {W W1 W2 : Subgroup G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {σsel : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {p q : ℕ}
    (hq : 0 < q)
    (hp : 0 < p)
    {ωFin : Fin q → Fin p → Section1.ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hωFin : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hq⟩ ⟨0, hp⟩ ωFin)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (hIsoSel : Section3.IsCFLinearIsometry σsel)
    (hVirtSel : Section3.MapsVirtualCharacters σsel)
    (e : W ≃* L)
    (ξ : Section1.ClassFunction W)
    (hξ : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hVagree :
      ∀ z : G, ∀ hz : z ∈ Section3.cyclicTISet W1 W2 W,
        σsel (Section6.theorem_6_8_transportClassFunction e ξ) z =
          ξ ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩) :
    σ ξ = σsel (Section6.theorem_6_8_transportClassFunction e ξ) := by
  classical
  rcases Section3.pf35_data_of_theorem_3_2_map_statement hωFin σ hσ with
    ⟨χ, horth, hsigned, h00, hInd, hσω⟩
  have hσEq : σ = Section3.sigmaOfPF35 ωFin χ :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hq⟩) (j0 := ⟨0, hp⟩)
      (ω := ωFin) (χ := χ) h31 hωFin hσω
  have htransportIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section6.theorem_6_8_transportClassFunction_irreducible e hξ
  have hξClass : Section1.IsClassFunction ξ := by
    rcases hξ with ⟨_n, ρ, _hρIrr, hξEq⟩
    rw [hξEq]
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have htransportClass :
      Section1.IsClassFunction
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section6.theorem_6_8_transportClassFunction_isClass e hξClass
  have htransportVirt :
      Theory.Character.IsVirtualCharacter
        (Section6.theorem_6_8_transportClassFunction e ξ) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup htransportIrr
  have hImageVirt :
      Theory.Character.IsVirtualCharacter
        (σsel (Section6.theorem_6_8_transportClassFunction e ξ)) :=
    hVirtSel _ htransportVirt
  have hselfW : Section1.scalarProduct W ξ ξ = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self hξ
  have hself :
      Section1.scalarProduct G
        (σsel (Section6.theorem_6_8_transportClassFunction e ξ))
        (σsel (Section6.theorem_6_8_transportClassFunction e ξ)) = 1 := by
    calc
      Section1.scalarProduct G
          (σsel (Section6.theorem_6_8_transportClassFunction e ξ))
          (σsel (Section6.theorem_6_8_transportClassFunction e ξ)) =
        Section1.scalarProduct L
          (Section6.theorem_6_8_transportClassFunction e ξ)
          (Section6.theorem_6_8_transportClassFunction e ξ) :=
          hIsoSel _ _ htransportClass htransportClass
      _ = Section1.scalarProduct W ξ ξ :=
          Section6.theorem_6_8_scalarProduct_transportClassFunction e ξ ξ
      _ = 1 := hselfW
  have hXsigned :
      Section3.IsSignedIrreducibleCharacter
        (σsel (Section6.theorem_6_8_transportClassFunction e ξ)) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hImageVirt hself
  have hXeq :
      σsel (Section6.theorem_6_8_transportClassFunction e ξ) =
        Section3.sigmaOfPF35 ωFin χ ξ :=
    Section3.proposition_3_9_a_uniqueness_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hq⟩) (j0 := ⟨0, hp⟩)
      (ω := ωFin) (χ := χ) h31 hωFin horth hsigned h00 hInd
      hξ hXsigned hVagree
  calc
    σ ξ = Section3.sigmaOfPF35 ωFin χ ξ := by rw [hσEq]
    _ = σsel (Section6.theorem_6_8_transportClassFunction e ξ) := hXeq.symm

private theorem hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_of_exactTransport
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax : Subgroup G}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    {Wsel : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction Smax}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsel}
    {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G}
    (hSelNotation : Section10.section10FourSixNotationSupportedData
      Smax W1 W2 Wsel A A0 i0 j0 μsel δSign ωsec σsel τS)
    (row : ℕ → I)
    (col : ℕ → J)
    (hExactTransport : hypothesis_13_1_typePFourSixTableExactTransportData
      Wsel ω ωsec row col (Nat.card W1) (Nat.card W2))
    (i j : ℕ)
    (hi : i < Nat.card W1)
    (hj : j < Nat.card W2) :
    σ (ω i j) = σsel (ωsec (row i) (col j)) := by
  classical
  rcases hnotation with
    ⟨hω, hσ, _hη, _hδ, _hδ', _hμIrr, _hνIrr,
      _hμNonprincipal, _hνNonprincipal, _hμInd, _hνInd,
      _hμSum, _hνSum, _hBaseS, _hBaseT, _hμDegree, _hνDegree⟩
  rcases hω with ⟨h31, hq, hp, ωFin, hωFin, hωEq⟩
  rcases hSelNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource, _hWselEq, _hA0Eq,
      _h46, _hωsec, hIsoSel, hVirtSel, _hPrincipal, hσAgree,
      _h45, _h48, _hTauIso, _hFull⟩
  rcases hExactTransport with ⟨e, hcoe, hentry⟩
  have hξIrr : Section1.IsIrreducibleCharacterOnGroup (ω i j) := by
    rw [hωEq i j hi hj]
    exact hωFin.irreducible ⟨i, hi⟩ ⟨j, hj⟩
  have hξClass : Section1.IsClassFunction (ω i j) := by
    rcases hξIrr with ⟨_n, ρ, _hρIrr, hξEq⟩
    rw [hξEq]
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have htransportClass :
      Section1.IsClassFunction
        (Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
    Section6.theorem_6_8_transportClassFunction_isClass e hξClass
  have hVagree :
      ∀ z : G, ∀ hz : z ∈ Section3.cyclicTISet W1 W2 W,
        σsel (Section6.theorem_6_8_transportClassFunction e (ω i j)) z =
          (ω i j) ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩ := by
    intro z hz
    let wz : W := ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩
    let zWsel : Wsel := e wz
    let zS : Smax := zWsel
    have hzS : ((zS : Smax) : G) = z := by
      simpa [zS, zWsel, wz] using hcoe wz
    have hzlocal :
        zS ∈ Section3.cyclicTISet
          (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsel := by
      rw [Section3.cyclicTISet_mem_iff]
      refine ⟨?_, ?_, ?_⟩
      · exact zWsel.property
      · intro hleft
        exact Section3.cyclicTISet_not_mem_left W1 W2 W hz (by
          simpa [Subgroup.mem_subgroupOf, hzS] using hleft)
      · intro hright
        exact Section3.cyclicTISet_not_mem_right W1 W2 W hz (by
          simpa [Subgroup.mem_subgroupOf, hzS] using hright)
    have hagree :=
      hσAgree (Section6.theorem_6_8_transportClassFunction e (ω i j))
        htransportClass zS hzlocal
    have harg :
        e.symm
          ⟨zS, Section3.cyclicTISet_subset
            (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsel hzlocal⟩ = wz := by
      apply e.injective
      simp [zS, zWsel]
    calc
      σsel (Section6.theorem_6_8_transportClassFunction e (ω i j)) z =
        σsel (Section6.theorem_6_8_transportClassFunction e (ω i j))
          ((zS : Smax) : G) := by rw [hzS]
      _ = Section6.theorem_6_8_transportClassFunction e (ω i j)
          ⟨zS, Section3.cyclicTISet_subset
            (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsel hzlocal⟩ := hagree
      _ = (ω i j) ⟨z, Section3.cyclicTISet_subset W1 W2 W hz⟩ := by
        simp [Section6.theorem_6_8_transportClassFunction, harg, wz]
  have hσEq :
      σ (ω i j) =
        σsel (Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
    hypothesis_13_1_sigma_transport_eq_of_cyclicTI_agreement
      hq hp h31 hωFin hσ hIsoSel hVirtSel e (ω i j) hξIrr hVagree
  calc
    σ (ω i j) =
        σsel (Section6.theorem_6_8_transportClassFunction e (ω i j)) := hσEq
    _ = σsel (ωsec (row i) (col j)) := by rw [hentry i j hi hj]

private theorem hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_selectedImage_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax : Subgroup G}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G} :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ {I J : Type u} [Fintype I] [DecidableEq I]
            [Fintype J] [DecidableEq J]
            {Wsel : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
            {μsel : I → J → Section1.ClassFunction Smax}
            {δSign : J → ℤ}
            {ωsec : I → J → Section1.ClassFunction Wsel}
            {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G},
              Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsel
                A A0 i0 j0 μsel δSign ωsec σsel τS →
              ∀ (row : ℕ → I) (col : ℕ → J),
                row 0 = i0 →
                col 0 = j0 →
                (∀ j, 0 < j → j < Nat.card W2 → col j ≠ j0) →
                (∀ i k, i < Nat.card W1 → k < Nat.card W1 →
                  row i = row k → i = k) →
                (∀ iSel : I, ∃ k, k < Nat.card W1 ∧ row k = iSel) →
                (∀ jSel : J, ∃ k, k < Nat.card W2 ∧ col k = jSel) →
                (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
                  Section1.inducedCF (W.subgroupOf Smax)
                      (Section1.subgroupOfClassFunction (T := Smax)
                        (ω i j - ω 0 j)) =
                    Section1.inducedCF Wsel
                      (ωsec (row i) (col j) - ωsec i0 (col j))) →
                hypothesis_13_1_typePFourSixTableExactTransportData
                  Wsel ω ωsec row col (Nat.card W1) (Nat.card W2) →
                ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
                  σ (ω i j) = σsel (ωsec (row i) (col j)) := by
  /-
  Source PF `(13.1)` visible/selected cyclic-TI image convention for the
  concrete selected Section `(4.6)` row and column maps.  The S/T family,
  Dade, and T-side hypotheses are not part of this pointwise image boundary.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation I J _instI _decI _instJ _decJ
    Wsel A A0 i0 j0 μsel δSign ωsec σsel hSelNotation row col _hrow0 _hcol0
    _hcol_ne _hrow_inj _hrow_surj _hcol_surj _hIndTransport hExactTransport
    i j hi _hj0 hj
  exact
    hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_of_exactTransport
      ω η μ ν μsum νsum δ δ' σ hnotation hSelNotation row col hExactTransport
      i j hi hj

private theorem hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_selectedTable_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (_Sfam : Finset (Section1.ClassFunction Smax))
    (_Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P _Sfam)
    (_hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q _Tfam)
    (_hDadeS : dadeIsometryRelativeToAZero Smax P _Sfam τS)
    (_hDadeT : dadeIsometryRelativeToAZero Tmax Q _Tfam τT)
    (_hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ {I J : Type u} [Fintype I] [DecidableEq I]
            [Fintype J] [DecidableEq J]
            {Wsel : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
            {μsel : I → J → Section1.ClassFunction Smax}
            {δSign : J → ℤ}
            {ωsec : I → J → Section1.ClassFunction Wsel}
            {σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G},
              Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsel
                A A0 i0 j0 μsel δSign ωsec σsel τS →
              ∀ (row : ℕ → I) (col : ℕ → J),
                row 0 = i0 →
                col 0 = j0 →
                (∀ j, 0 < j → j < Nat.card W2 → col j ≠ j0) →
                (∀ i k, i < Nat.card W1 → k < Nat.card W1 →
                  row i = row k → i = k) →
                (∀ iSel : I, ∃ k, k < Nat.card W1 ∧ row k = iSel) →
                (∀ jSel : J, ∃ k, k < Nat.card W2 ∧ col k = jSel) →
                (∀ i j, i < Nat.card W1 → j < Nat.card W2 →
                  Section1.inducedCF (W.subgroupOf Smax)
                      (Section1.subgroupOfClassFunction (T := Smax)
                        (ω i j - ω 0 j)) =
                    Section1.inducedCF Wsel
                      (ωsec (row i) (col j) - ωsec i0 (col j))) →
                hypothesis_13_1_typePFourSixTableExactTransportData
                  Wsel ω ωsec row col (Nat.card W1) (Nat.card W2) →
                ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
                  σ (ω i j) = σsel (ωsec (row i) (col j)) := by
  /-
  Checked wrapper around the pointwise source boundary for visible/selected
  cyclic-TI image alignment.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation I J _instI _decI _instJ _decJ
    Wsel A A0 i0 j0 μsel δSign ωsec σsel hSelNotation row col hrow0 hcol0
    hcol_ne hrow_inj hrow_surj hcol_surj hIndTransport hExactTransport
    i j hi hj0 hj
  exact
    hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_selectedImage_source
      ω η μ ν μsum νsum δ δ' σ hnotation hSelNotation
      row col hrow0 hcol0 hcol_ne hrow_inj hrow_surj hcol_surj hIndTransport
      hExactTransport i j hi hj0 hj

private theorem hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          ∀ (χ : ℕ → ℕ → Section1.ClassFunction Smax)
            (δsel : ℕ → ℤ)
            (Wsel : Subgroup Smax)
            (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
            (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G),
            hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
                hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
            σ (ω i j) = σsel (ωsel i j) := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
    hSelected i j hi hj0 hj
  rcases hSelected with
    ⟨I, instI, decI, J, instJ, decJ, A, A0, i0, j0, μsel, δSign, ωsec,
      hSelNotation, row, col, hrow0, hcol0, hcol_ne, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport, _hχ, _hδsel, hωsel⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  have hsrc : σ (ω i j) = σsel (ωsec (row i) (col j)) :=
    hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_selectedTable_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation
      hSelNotation row col hrow0 hcol0 hcol_ne hrow_inj hrow_surj
      hcol_surj hIndTransport hExactTransport i j hi hj0 hj
  exact hsrc.trans (congrArg σsel (hωsel i j hi hj).symm)

private theorem hypothesis_13_1_dadeDifferencePointwiseVisibleAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          ∀ (χ : ℕ → ℕ → Section1.ClassFunction Smax)
            (δsel : ℕ → ℤ)
            (Wsel : Subgroup Smax)
            (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
            (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G),
            hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
                hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
            μ i j = χ i j ∧ δ j = δsel j ∧
              σ (ω i j) = σsel (ωsel i j) := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
    hSelected i j hi hj0 hj
  exact ⟨
    hypothesis_13_1_dadeDifferencePointwiseMuAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
      hSelected i j hi hj0 hj,
    hypothesis_13_1_dadeDifferencePointwiseDeltaAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
      hSelected i j hi hj0 hj,
    hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
      hSelected i j hi hj0 hj⟩

private theorem hypothesis_13_1_dadeDifferenceVisibleAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (χ : ℕ → ℕ → Section1.ClassFunction Smax)
    (δsel : ℕ → ℤ)
    (Wsel : Subgroup Smax)
    (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
    (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G)
    (hselDade : ∀ i j k, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
      0 < k → k < Nat.card W2 →
        Section1.degree (χ i j) = Section1.degree (χ i k) →
          τS (χ i j - χ i k) =
            (((δsel j : ℤ) : ℂ) • (σsel (ωsel i j) - σsel (ωsel i k)))) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
            hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ i j k, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
            0 < k → k < Nat.card W2 →
              Section1.degree (μ i j) = Section1.degree (μ i k) →
                τS (μ i j - μ i k) =
                  (((δ j : ℤ) : ℂ) • (σ (ω i j) - σ (ω i k))) := by
  /-
  Source alignment from the checked selected natural `(4.8)` Dade
  row-difference endpoint to arbitrary visible PF `(13.1)` notation.  This keeps
  the selected `σsel`/table formula separate from the visible `σ`/`μ` formula.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation hSelected i j k hi hj0 hj
    hk0 hk hdeg
  have hAlign :=
    hypothesis_13_1_dadeDifferencePointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
      hSelected
  rcases hAlign i j hi hj0 hj with ⟨hμj, hδj, hσj⟩
  rcases hAlign i k hi hk0 hk with ⟨hμk, _hδk, hσk⟩
  have hdegSel : Section1.degree (χ i j) = Section1.degree (χ i k) := by
    simpa [hμj, hμk] using hdeg
  have hsel := hselDade i j k hi hj0 hj hk0 hk hdegSel
  simpa [hμj, hμk, hδj, hσj, hσk] using hsel

private theorem hypothesis_13_1_dadeDifferenceDataFor_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ i j k, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
            0 < k → k < Nat.card W2 →
              Section1.degree (μ i j) = Section1.degree (μ i k) →
                τS (μ i j - μ i k) =
                  (((δ j : ℤ) : ℂ) • (σ (ω i j) - σ (ω i k))) := by
  /-
  One-sided PF `(13.1)` source boundary for the Dade image of selected row
  differences.  The selected `(4.8)` Dade row-difference endpoint is checked;
  the remaining source content is only the visible notation-alignment bridge.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  rcases hnotation with
    ⟨hω, hσ, hη, hδ, hδ', hμirr, hνirr, hμzero_nonprincipal,
      hνzero_nonprincipal, hμind, hνind, hμsum, hνsum, hbaseS, hbaseT,
      hμzeroDegree, hνzeroDegree⟩
  have hnotation' :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ :=
    ⟨hω, hσ, hη, hδ, hδ', hμirr, hνirr, hμzero_nonprincipal,
      hνzero_nonprincipal, hμind, hνind, hμsum, hνsum, hbaseS, hbaseT,
      hμzeroDegree, hνzeroDegree⟩
  rcases hypothesis_13_1_typePFourSixDadeDifference_source
      hSTypeP ω hω τS hFourSixS with
    ⟨χ, δsel, Wsel, ωsel, σsel, hSelected, hselDade⟩
  exact hypothesis_13_1_dadeDifferenceVisibleAlignment_s_side_source
    hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
    hDadeS hDadeT hFourSixS hFourSixT χ δsel Wsel ωsel σsel hselDade
    ω η μ ν μsum νsum δ δ' σ hnotation' hSelected

private theorem hypothesis_13_1_dadeDifferenceDataFor_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2 τS τT
      (Nat.card W2) (Nat.card W1) := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  refine ⟨?_, ?_⟩
  · exact
      hypothesis_13_1_dadeDifferenceDataFor_s_side_source hmin hcase
        hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
        hFourSixS hFourSixT ω η μ ν μsum νsum δ δ' σ hnotation
  · intro i k j hi0 hi hk0 hk hj hdeg
    have hnotationSwap :
        hypothesis_13_1_characterNotationDataFor Tmax Smax W W2 W1
          (Nat.card W1) (Nat.card W2)
          (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
          (fun i j => μ j i) νsum μsum δ' δ σ :=
      hypothesis_13_1_characterNotationDataFor_swap_local hnotation
    exact
      hypothesis_13_1_dadeDifferenceDataFor_s_side_source hmin
        (hypothesis_13_1_case_b_data_swap hcase) hTTypeP hSTypeP Tfam Sfam
        τT τS hTnonker hSnonker hDadeT hDadeS hFourSixT hFourSixS
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ hnotationSwap
        j i k hj hi0 hi hk0 hk hdeg

private theorem hypothesis_13_1_zeroBaseDegreeDataFor_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  rcases hnotation with
    ⟨_hω, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, _hbaseS, _hbaseT, hμzeroDegree, hνzeroDegree⟩
  exact ⟨hμzeroDegree, hνzeroDegree⟩

private theorem hypothesis_13_1_conjugateIndexSigmaOmegaPointwiseVisibleAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (χ : ℕ → ℕ → Section1.ClassFunction Smax)
    (δsel : ℕ → ℤ)
    (Wsel : Subgroup Smax)
    (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
    (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G)
    (hselSigmaOmega : ∀ j k, 0 < j → j < Nat.card W2 →
      0 < k → k < Nat.card W2 →
        χ 0 k = Section1.conjugateCharacter (χ 0 j) →
          σsel (ωsel 0 k) =
            Section1.conjugateCharacter (σsel (ωsel 0 j))) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
            hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ j k, 0 < j → j < Nat.card W2 →
            0 < k → k < Nat.card W2 →
              χ 0 k = Section1.conjugateCharacter (χ 0 j) →
                σ (ω 0 k) = Section1.conjugateCharacter (σ (ω 0 j)) := by
  /-
  Checked visible/selected transport for the PF `(13.18)` Sigma/Omega
  conjugation step.  The remaining source content is the selected-table
  Sigma/Omega conjugation transfer above.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation hSelected j k hj0 hj hk0 hk hχ
  have hrow0lt : 0 < Nat.card W1 := Nat.card_pos (α := W1)
  have hDadeAlign :=
    hypothesis_13_1_dadeDifferencePointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
      hSelected
  rcases hDadeAlign 0 j hrow0lt hj0 hj with ⟨_hμj, _hδj, hσj⟩
  rcases hDadeAlign 0 k hrow0lt hk0 hk with ⟨_hμk, _hδk, hσk⟩
  have hsel :
      σsel (ωsel 0 k) =
        Section1.conjugateCharacter (σsel (ωsel 0 j)) :=
    hselSigmaOmega j k hj0 hj hk0 hk hχ
  calc
    σ (ω 0 k) = σsel (ωsel 0 k) := hσk
    _ = Section1.conjugateCharacter (σsel (ωsel 0 j)) := hsel
    _ = Section1.conjugateCharacter (σ (ω 0 j)) :=
      congrArg Section1.conjugateCharacter hσj.symm

private theorem hypothesis_13_1_conjugateIndexEtaPointwiseVisibleAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (χ : ℕ → ℕ → Section1.ClassFunction Smax)
    (δsel : ℕ → ℤ)
    (Wsel : Subgroup Smax)
    (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
    (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G)
    (hselSigmaOmega : ∀ j k, 0 < j → j < Nat.card W2 →
      0 < k → k < Nat.card W2 →
        χ 0 k = Section1.conjugateCharacter (χ 0 j) →
          σsel (ωsel 0 k) =
            Section1.conjugateCharacter (σsel (ωsel 0 j))) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
            hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ j k, 0 < j → j < Nat.card W2 →
            0 < k → k < Nat.card W2 →
              χ 0 k = Section1.conjugateCharacter (χ 0 j) →
                η 0 k = Section1.conjugateCharacter (η 0 j) := by
  /-
  Checked rewrite through the visible PF `(13.1)` notation field
  `η i j = σ (ω i j)`.  The remaining source content is the corresponding
  conjugation transfer for the visible `σ(ω)` values.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation hSelected j k hj0 hj hk0 hk hχ
  have hnotationSource := hnotation
  rcases hnotation with
    ⟨_hω, _hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, _hbaseS, _hbaseT, _hμzeroDegree, _hνzeroDegree⟩
  have hrow0 : 0 < Nat.card W1 := Nat.card_pos (α := W1)
  have hσω :
      σ (ω 0 k) = Section1.conjugateCharacter (σ (ω 0 j)) :=
    hypothesis_13_1_conjugateIndexSigmaOmegaPointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT χ δsel Wsel ωsel σsel hselSigmaOmega
      ω η μ ν μsum νsum δ δ' σ hnotationSource hSelected
      j k hj0 hj hk0 hk hχ
  calc
    η 0 k = σ (ω 0 k) := hη 0 k hrow0 hk
    _ = Section1.conjugateCharacter (σ (ω 0 j)) := hσω
    _ = Section1.conjugateCharacter (η 0 j) := by
      rw [← hη 0 j hrow0 hj]

private theorem hypothesis_13_1_conjugateIndexPointwiseVisibleAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (χ : ℕ → ℕ → Section1.ClassFunction Smax)
    (δsel : ℕ → ℤ)
    (Wsel : Subgroup Smax)
    (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
    (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G)
    (hselSigmaOmega : ∀ j k, 0 < j → j < Nat.card W2 →
      0 < k → k < Nat.card W2 →
        χ 0 k = Section1.conjugateCharacter (χ 0 j) →
          σsel (ωsel 0 k) =
            Section1.conjugateCharacter (σsel (ωsel 0 j))) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
            hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ j k, 0 < j → j < Nat.card W2 →
            0 < k → k < Nat.card W2 →
              μ 0 j = χ 0 j ∧ μ 0 k = χ 0 k ∧
                (χ 0 k = Section1.conjugateCharacter (χ 0 j) →
                  η 0 k = Section1.conjugateCharacter (η 0 j)) := by
  /-
  Checked pointwise wrapper: visible/selected zero-row `μ` equality is already
  part of the Dade pointwise alignment source; the visible `η` conjugation
  transfer is checked glue over the Sigma/Omega helper.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation hSelected j k hj0 hj hk0 hk
  have hrow0lt : 0 < Nat.card W1 := Nat.card_pos (α := W1)
  have hDadeAlign :=
    hypothesis_13_1_dadeDifferencePointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
      hSelected
  rcases hDadeAlign 0 j hrow0lt hj0 hj with ⟨hμj, _hδj, _hσj⟩
  rcases hDadeAlign 0 k hrow0lt hk0 hk with ⟨hμk, _hδk, _hσk⟩
  have hη_ofχ :
      χ 0 k = Section1.conjugateCharacter (χ 0 j) →
        η 0 k = Section1.conjugateCharacter (η 0 j) :=
    hypothesis_13_1_conjugateIndexEtaPointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT χ δsel Wsel ωsel σsel hselSigmaOmega
      ω η μ ν μsum νsum δ δ' σ hnotation hSelected j k hj0 hj hk0 hk
  exact ⟨hμj, hμk, hη_ofχ⟩

private theorem hypothesis_13_1_conjugateIndexVisibleAlignment_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (χ : ℕ → ℕ → Section1.ClassFunction Smax)
    (δsel : ℕ → ℤ)
    (Wsel : Subgroup Smax)
    (ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
    (σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G)
    (hχconj : ∀ j, 0 < j → j < Nat.card W2 →
      ∃ k : ℕ, 0 < k ∧ k < Nat.card W2 ∧ k ≠ j ∧
        χ 0 k = Section1.conjugateCharacter (χ 0 j))
    (hselSigmaOmega : ∀ j k, 0 < j → j < Nat.card W2 →
      0 < k → k < Nat.card W2 →
        χ 0 k = Section1.conjugateCharacter (χ 0 j) →
          σsel (ωsel 0 k) =
            Section1.conjugateCharacter (σsel (ωsel 0 j))) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ) →
          hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω
            hnotation.1 τS χ δsel Wsel ωsel σsel →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∃ k : ℕ, 0 < k ∧ k < Nat.card W2 ∧ k ≠ j ∧
              η 0 k = Section1.conjugateCharacter (η 0 j) ∧
                μ 0 k = Section1.conjugateCharacter (μ 0 j) := by
  /-
  Source alignment from the checked selected natural `(4.6)` zero-row
  conjugation endpoint to arbitrary visible PF `(13.1)` notation.  The wrapper
  below checks the selected endpoint separately, leaving only this visible
  `η`/`μ` notation alignment as source content.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation hSelected j hj0 hj
  rcases hχconj j hj0 hj with ⟨k, hk0, hk, hkne, hχ⟩
  have hAlign :=
    hypothesis_13_1_conjugateIndexPointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT χ δsel Wsel ωsel σsel hselSigmaOmega
      ω η μ ν μsum νsum δ δ' σ hnotation hSelected
  rcases hAlign j k hj0 hj hk0 hk with ⟨hμj, hμk, hη_ofχ⟩
  have hη : η 0 k = Section1.conjugateCharacter (η 0 j) := hη_ofχ hχ
  have hμ : μ 0 k = Section1.conjugateCharacter (μ 0 j) := by
    simpa [hμj, hμk] using hχ
  exact ⟨k, hk0, hk, hkne, hη, hμ⟩

private theorem hypothesis_13_1_conjugateIndexDataFor_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∃ k : ℕ, 0 < k ∧ k < Nat.card W2 ∧ k ≠ j ∧
              η 0 k = Section1.conjugateCharacter (η 0 j) ∧
                μ 0 k = Section1.conjugateCharacter (μ 0 j) := by
  /-
  One-sided PF `(13.1)` source boundary for the zero-row conjugate-index
  convention used by the PF `(13.18)` beta argument.  The selected `(4.6)`
  zero-row conjugation endpoint is checked; the remaining source content is
  only the visible `η`/`μ` notation-alignment bridge.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  rcases hnotation with
    ⟨hω, hσ, hη, hδ, hδ', hμirr, hνirr, hμzero_nonprincipal,
      hνzero_nonprincipal, hμind, hνind, hμsum, hνsum, hbaseS, hbaseT,
      hμzeroDegree, hνzeroDegree⟩
  have hnotation' :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ :=
    ⟨hω, hσ, hη, hδ, hδ', hμirr, hνirr, hμzero_nonprincipal,
      hνzero_nonprincipal, hμind, hνind, hμsum, hνsum, hbaseS, hbaseT,
      hμzeroDegree, hνzeroDegree⟩
  rcases hypothesis_13_1_typePFourSixBaseRowConjugateSigmaOmega_source
      hSTypeP ω hω τS hFourSixS with
    ⟨χ, δsel, Wsel, ωsel, σsel, hSelected, hχconj, hselSigmaOmega⟩
  exact hypothesis_13_1_conjugateIndexVisibleAlignment_s_side_source
    hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
    hDadeS hDadeT hFourSixS hFourSixT χ δsel Wsel ωsel σsel hχconj
    hselSigmaOmega
    ω η μ ν μsum νsum δ δ' σ hnotation' hSelected

private theorem hypothesis_13_1_conjugateIndexDataFor_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  refine ⟨?_, ?_⟩
  · exact
      hypothesis_13_1_conjugateIndexDataFor_s_side_source hmin hcase
        hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
        hFourSixS hFourSixT
        ω η μ ν μsum νsum δ δ' σ hnotation
  · intro i hi0 hi
    have hnotationSwap :
        hypothesis_13_1_characterNotationDataFor Tmax Smax W W2 W1
          (Nat.card W1) (Nat.card W2)
          (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
          (fun i j => μ j i) νsum μsum δ' δ σ :=
      hypothesis_13_1_characterNotationDataFor_swap_local hnotation
    exact
      hypothesis_13_1_conjugateIndexDataFor_s_side_source hmin
        (hypothesis_13_1_case_b_data_swap hcase) hTTypeP hSTypeP Tfam Sfam
        τT τS hTnonker hSnonker hDadeT hDadeS hFourSixT hFourSixS
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ hnotationSwap
        i hi0 hi

private theorem hypothesis_13_1_conjugateCharacter_dadeTransform
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G}
    (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) :
    Section1.conjugateCharacter (Section2.dadeTransform H hAL α) =
      Section2.dadeTransform H hAL (Section1.conjugateCharacter α) := by
  ext g
  by_cases hg : ∃ a ∈ A, ∃ h ∈ H a, Section2.conjugateIn g (a * h)
  · simp [Section2.dadeTransform, hg, Section1.conjugateCharacter]
  · simp [Section2.dadeTransform, hg, Section1.conjugateCharacter]

private theorem hypothesis_13_1_typePDefinitionData_of_case_typeP
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    Section8.typePDefinitionData Smax P U W1 W2 := by
  letI : IsMinCE G := hmin
  have hSmax : Smax ∈ section9MaximalSubgroups G := by
    rcases hcase with
      ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, hSmax, _hTmax,
        _hSF, _hTF, _hSnotI, _hTnotI, _hSeq, _hTeq, _hSdisj,
        _hTdisj, _hW2le, _hW1le, _hST, _hcover, _hTypeII, _hSType,
        _hTType, _hCommon⟩
    exact hSmax
  rcases section15_exists_KUData_for_maximal (G := G) (M := Smax) hSmax with
    ⟨K, KU, hKU15⟩
  have hKU : section16KUData Smax K KU := by
    simpa [section16KUData] using hKU15
  exact
    Section8.theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hSmax hSTypeP.1 hKU hSTypeP.2


private theorem hypothesis_13_1_isClassFunction_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hρ, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

private theorem hypothesis_13_1_betaPreimage_isClassFunction
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P : Subgroup G}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ)
    (j : ℕ) (hj : j < Nat.card W2) :
    Section1.IsClassFunction
      (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
          μ 0 j) := by
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  have hμclass : Section1.IsClassFunction (μ 0 j) :=
    hypothesis_13_1_isClassFunction_of_irreducible (hμirr 0 j hqpos hj)
  have hindClass :
      Section1.IsClassFunction
        (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) :=
    Section1.inducedCF_isClassFunction ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))
  intro x g
  simp [hindClass x g, hμclass x g]

private theorem hypothesis_13_1_inducedPrincipal_identity_value
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (x : G) (hx : x = 1) :
    Section1.inducedCF H (Section1.principalCharacter H) x =
      (Subgroup.index H : ℂ) := by
  subst hx
  change Section1.degree (Section1.inducedCF H (Section1.principalCharacter H)) =
    (Subgroup.index H : ℂ)
  rw [Section1.degree_inducedClassFunction]
  simp [Section1.degree_apply]

private theorem hypothesis_13_1_inducedCF_eq_zero_of_not_mem_conjugates
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (θ : Section1.ClassFunction H) {x : G}
    (hx : x ∉ section16ConjugatesOfSetBySet (H : Set G) Set.univ) :
    Section1.inducedCF H θ x = 0 := by
  classical
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      (∑ y : G,
        if hy : y * x * y⁻¹ ∈ H then θ ⟨y * x * y⁻¹, hy⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y _hy
    by_cases hyH : y * x * y⁻¹ ∈ H
    · have hxConj :
          x ∈ section16ConjugatesOfSetBySet (H : Set G) Set.univ := by
        refine ⟨y * x * y⁻¹, hyH, y⁻¹, by simp, ?_⟩
        simp [mul_assoc]
      exact False.elim (hx hxConj)
    · simp [hyH]
  rw [hsum, mul_zero]

private theorem hypothesis_13_1_inducedCF_principal_eq_one_of_conjugator_card
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (x : G)
    (hcard : Nat.card {y : G // y * x * y⁻¹ ∈ H} = Nat.card H) :
    Section1.inducedCF H (Section1.principalCharacter H) x = 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype H := Fintype.ofFinite H
  have hcardH_ne : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      (∑ y : G,
        if hy : y * x * y⁻¹ ∈ H then
          Section1.principalCharacter H ⟨y * x * y⁻¹, hy⟩
        else 0) = (Nat.card H : ℂ) := by
    calc
      (∑ y : G,
        if hy : y * x * y⁻¹ ∈ H then
          Section1.principalCharacter H ⟨y * x * y⁻¹, hy⟩
        else 0)
          = (∑ y : G, if y * x * y⁻¹ ∈ H then (1 : ℂ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro y _hy
              by_cases hyH : y * x * y⁻¹ ∈ H
              · simp [hyH, Section1.principalCharacter]
              · simp [hyH]
      _ = (Fintype.card {y : G // y * x * y⁻¹ ∈ H} : ℂ) := by
              simp [Fintype.card_subtype]
      _ = (Nat.card {y : G // y * x * y⁻¹ ∈ H} : ℂ) := by
              rw [Nat.card_eq_fintype_card]
      _ = (Nat.card H : ℂ) := by rw [hcard]
  rw [hsum]
  exact inv_mul_cancel₀ hcardH_ne

private theorem hypothesis_13_1_mem_normalizer_of_conjugateSet_eq
    {G : Type u} [Group G]
    {X : Set G} {g : G}
    (hX : section16ConjugateSet X g = X) :
    g ∈ Subgroup.normalizer X := by
  change ∀ y : G, y ∈ X ↔ g * y * g⁻¹ ∈ X
  intro y
  constructor
  · intro hy
    rw [← hX]
    exact ⟨y, hy, rfl⟩
  · intro hy
    have hmem : g * y * g⁻¹ ∈ section16ConjugateSet X g := by
      simpa [hX] using hy
    rcases hmem with ⟨x, hx, hxy⟩
    have hyx : y = x := by
      calc
        y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hxy]
        _ = x := by group
    simpa [hyx] using hx

private theorem hypothesis_13_1_conjugator_card_eq_of_ti_normalizer
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (hTINorm : section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet H) H)
    {x : G} (hx : x ∈ Section7.puncturedSubgroupSet H) :
    Nat.card {y : G // y * x * y⁻¹ ∈ H} = Nat.card H := by
  classical
  let X : Set G := Section7.puncturedSubgroupSet H
  have hTI : section16TISubset X := hTINorm.1
  have hNorm : Subgroup.normalizer X = H := hTINorm.2
  let e : H ≃ {y : G // y * x * y⁻¹ ∈ H} :=
    { toFun := fun h =>
        ⟨(h : G), by
          exact H.mul_mem (H.mul_mem h.property hx.1) (H.inv_mem h.property)⟩
      invFun := fun y =>
        ⟨(y : G), by
          have hyX : y.1 * x * y.1⁻¹ ∈ X :=
            ⟨y.2, by
              intro hconj_one
              exact hx.2 (by
                have := congrArg (fun z : G => y.1⁻¹ * z * y.1) hconj_one
                simpa [mul_assoc] using this)⟩
          have hyConj : y.1 * x * y.1⁻¹ ∈ section16ConjugateSet X y.1 :=
            ⟨x, hx, rfl⟩
          rcases hTI y.1 with hsame | hsmall
          · have hyNorm : y.1 ∈ Subgroup.normalizer X :=
              hypothesis_13_1_mem_normalizer_of_conjugateSet_eq hsame
            simpa [hNorm] using hyNorm
          · have hone : y.1 * x * y.1⁻¹ ∈ ({1} : Set G) :=
              hsmall ⟨hyX, hyConj⟩
            have hone_eq : y.1 * x * y.1⁻¹ = 1 := by
              simpa using hone
            exact False.elim (hx.2 (by
              calc
                x = y.1⁻¹ * (y.1 * x * y.1⁻¹) * y.1 := by group
                _ = 1 := by rw [hone_eq]; simp))⟩
      left_inv := by
        intro h
        rfl
      right_inv := by
        intro y
        rfl }
  exact Nat.card_congr e.symm

private theorem hypothesis_13_1_conjugator_card_conj_eq_of_ti_normalizer
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (hTINorm : section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet H) H)
    {x t : G} (hx : x ∈ Section7.puncturedSubgroupSet H) :
    Nat.card {y : G // y * (t * x * t⁻¹) * y⁻¹ ∈ H} = Nat.card H := by
  classical
  have hcard :
      Nat.card {a : G // a * x * a⁻¹ ∈ H} = Nat.card H :=
    hypothesis_13_1_conjugator_card_eq_of_ti_normalizer H hTINorm hx
  let e :
      {y : G // y * (t * x * t⁻¹) * y⁻¹ ∈ H} ≃
        {a : G // a * x * a⁻¹ ∈ H} :=
    { toFun := fun y =>
        ⟨y.1 * t, by
          simpa [mul_assoc] using y.2⟩
      invFun := fun a =>
        ⟨a.1 * t⁻¹, by
          simpa [mul_assoc] using a.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := by
        intro a
        apply Subtype.ext
        simp [mul_assoc] }
  exact (Nat.card_congr e).trans hcard

private theorem hypothesis_13_1_card_conjugatesOfSetBySet_eq_card_mul_index_of_ti
    {G : Type u} [Group G] [Finite G]
    {X : Set G}
    (hX1 : (1 : G) ∉ X)
    (hXti : section16TISubset X) :
    Nat.card (section16ConjugatesOfSetBySet X Set.univ) =
      Nat.card X * (Subgroup.normalizer X).index := by
  classical
  let N : Subgroup G := Subgroup.normalizer X
  let Ω := Quotient (QuotientGroup.rightRel N)
  let X0 := {x : G // x ∈ X}
  let f : Ω × X0 → {z : G // z ∈ section16ConjugatesOfSetBySet X Set.univ} := fun qx =>
    let a : G := Quotient.out qx.1
    ⟨a⁻¹ * qx.2.1 * a, ⟨qx.2.1, qx.2.2, a⁻¹, Set.mem_univ _, by simp [mul_assoc]⟩⟩
  have hfBij : Function.Bijective f := by
    constructor
    · intro qx1 qx2 hEq
      rcases qx1 with ⟨q1, x1⟩
      rcases qx2 with ⟨q2, x2⟩
      let a1 : G := Quotient.out q1
      let a2 : G := Quotient.out q2
      have hval : a1⁻¹ * x1.1 * a1 = a2⁻¹ * x2.1 * a2 :=
        congrArg Subtype.val hEq
      by_cases hq : q1 = q2
      · have ha : a2 = a1 := by simpa [a1, a2] using congrArg Quotient.out hq.symm
        have hx : x1 = x2 := by
          apply Subtype.ext
          rw [ha] at hval
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, mul_assoc] using hconj
        cases hq
        cases hx
        rfl
      · have hgNotN : a1 * a2⁻¹ ∉ N := by
          intro hgN
          apply hq
          have hginv : a2 * a1⁻¹ ∈ N := by
            simpa using N.inv_mem hgN
          calc
            q1 = Quotient.mk'' a1 := (Quotient.out_eq' q1).symm
            _ = Quotient.mk'' a2 := Quotient.sound' (QuotientGroup.rightRel_apply.mpr hginv)
            _ = q2 := Quotient.out_eq' q2
        have hx1Conj : x1.1 ∈ section16ConjugateSet X (a1 * a2⁻¹) := by
          refine ⟨x2.1, x2.2, ?_⟩
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, a2, mul_assoc] using hconj
        rcases hXti (a1 * a2⁻¹) with hsame | hsmall
        · exact False.elim (hgNotN (hypothesis_13_1_mem_normalizer_of_conjugateSet_eq hsame))
        · have hx1one : x1.1 = 1 := by
            simpa using hsmall ⟨x1.2, hx1Conj⟩
          exact False.elim (hX1 (hx1one ▸ x1.2))
    · intro z
      rcases z.2 with ⟨x, hxX, y, _hy, hzy⟩
      let q : Ω := Quotient.mk'' y⁻¹
      let a : G := Quotient.out q
      have hyaN : y⁻¹ * a⁻¹ ∈ N := by
        have hqa : (Quotient.mk'' a : Ω) = Quotient.mk'' y⁻¹ := by
          simp [q, a]
        exact QuotientGroup.rightRel_apply.mp (Quotient.exact' hqa)
      let n : G := y⁻¹ * a⁻¹
      have hnInvNorm : n⁻¹ ∈ N := N.inv_mem hyaN
      have hx' : n⁻¹ * x * n ∈ X := by
        change ∀ z : G, z ∈ X ↔ n⁻¹ * z * (n⁻¹)⁻¹ ∈ X at hnInvNorm
        simpa [n] using (hnInvNorm x).1 hxX
      refine ⟨(q, ⟨n⁻¹ * x * n, hx'⟩), ?_⟩
      apply Subtype.ext
      calc
        ((f (q, ⟨n⁻¹ * x * n, hx'⟩)).1) = y * x * y⁻¹ := by
          simp [f, q, a, n, mul_assoc]
        _ = z := by simpa using hzy.symm
  have hcardOmega : Nat.card Ω = N.index := by
    calc
      Nat.card Ω = Nat.card (G ⧸ N) := by
        exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel N)
      _ = N.index := N.index_eq_card.symm
  calc
    Nat.card (section16ConjugatesOfSetBySet X Set.univ) = Nat.card (Ω × X0) := by
      exact Nat.card_congr (Equiv.ofBijective f hfBij).symm
    _ = Nat.card Ω * Nat.card X0 := Nat.card_prod _ _
    _ = Nat.card Ω * Nat.card X := rfl
    _ = Nat.card X * N.index := by rw [hcardOmega, Nat.mul_comm]

private theorem hypothesis_13_1_natCard_puncturedSubgroupSet
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    Nat.card (Section7.puncturedSubgroupSet H) = Nat.card H - 1 := by
  classical
  let e : {x : G // x ∈ Section7.puncturedSubgroupSet H} ≃ {x : H // x ≠ 1} :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        intro hx
        exact x.2.2 (congrArg Subtype.val hx)⟩
      invFun := fun x => ⟨x.1.1, ⟨x.1.2, by
        intro hx
        exact x.2 (Subtype.ext hx)⟩⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl }
  calc
    Nat.card (Section7.puncturedSubgroupSet H) = Nat.card {x : H // x ≠ 1} :=
      Nat.card_congr e
    _ = Fintype.card {x : H // x ≠ 1} := Nat.card_eq_fintype_card
    _ = Fintype.card H - 1 := by
      have hcompl := Fintype.card_subtype_compl (fun x : H => x = 1)
      simp [hcompl]
    _ = Nat.card H - 1 := by rw [Nat.card_eq_fintype_card]

private theorem hypothesis_13_1_PU_nonP_not_mem_PW1_conjugates_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    ∀ x : Smax,
      (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) →
        (x : G) ∉ (P : Set G) →
          x ∉ section16ConjugatesOfSetBySet
            (((P ⊔ W1).subgroupOf Smax : Subgroup Smax) : Set Smax)
            Set.univ := by
  /-
  Source PF `(13.18)` `PVSbeta`, induced-principal half of the non-`P`
  subcase: if `x ∈ P ⊔ U` but `x ∉ P`, then `x` is not conjugate in `Smax`
  to an element of `P ⊔ W1`.
  -/
  classical
  let D : Subgroup G := ambientDerivedSubgroup Smax
  have hTypePDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  rcases hTypePDef with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, hCompMW1, _hUleD, _hUnil,
      _hW1normU, hCompDU, _hPnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormHatW⟩
  have hDleS : D ≤ Smax := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := Smax))
  have hDnorm : (D.subgroupOf Smax).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax)).2
  have hSleNormD : Smax ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDleS).1 hDnorm
  have hPleD : P ≤ D := by
    simpa [D] using hCompDU.1
  have hPleS : P ≤ Smax := hPleD.trans hDleS
  have hPnorm : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hSleNormP : Smax ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleS).1 hPnorm
  have hW1leNormP : W1 ≤ Subgroup.normalizer (P : Set G) :=
    hCompMW1.2.1.trans hSleNormP
  have hPW1set :
      (((P ⊔ W1 : Subgroup G) : Set G)) = (W1 : Set G) * (P : Set G) := by
    simpa [sup_comm] using
      (Subgroup.coe_mul_of_left_le_normalizer_right W1 P hW1leNormP)
  intro x hxPU hxNotP hxConj
  have hxD : (x : G) ∈ D := by
    simpa [D, hCompDU.2.2.1] using hxPU
  rcases hxConj with ⟨y, hyPW1sub, s, _hs, hx_eq⟩
  have hyPW1 : (y : G) ∈ (P ⊔ W1 : Subgroup G) := by
    simpa [Subgroup.mem_subgroupOf] using hyPW1sub
  have hx_eq_G : (x : G) = (s : G) * (y : G) * (s : G)⁻¹ :=
    congrArg Subtype.val hx_eq
  have hyD : (y : G) ∈ D := by
    have hsInvNormD : (s : G)⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
      hSleNormD (Smax.inv_mem s.property)
    have hconjD :
        (s : G)⁻¹ * (x : G) * ((s : G)⁻¹)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp hsInvNormD (x : G)).1 hxD
    simpa [hx_eq_G, mul_assoc] using hconjD
  have hyProd : (y : G) ∈ (W1 : Set G) * (P : Set G) := by
    rw [← hPW1set]
    exact hyPW1
  rcases hyProd with ⟨w, hwW1, p, hpP, hwp⟩
  have hpD : p ∈ D := hPleD hpP
  have hwpD : w * p ∈ D := by
    simpa [hwp] using hyD
  have hwD : w ∈ D := by
    have hmul : (w * p) * p⁻¹ ∈ D := D.mul_mem hwpD (D.inv_mem hpD)
    simpa [mul_assoc] using hmul
  have hwBot : w ∈ (⊥ : Subgroup G) :=
    hCompMW1.2.2.2.le_bot ⟨hwD, hwW1⟩
  have hw_one : w = 1 := Subgroup.mem_bot.mp hwBot
  have hyP : (y : G) ∈ P := by
    have hy_eq_p : (y : G) = p := by
      simpa [hw_one] using hwp.symm
    simpa [hy_eq_p] using hpP
  have hxP : (x : G) ∈ P := by
    have hsNormP : (s : G) ∈ Subgroup.normalizer (P : Set G) :=
      hSleNormP s.property
    have hconjP : (s : G) * (y : G) * (s : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hsNormP (y : G)).1 hyP
    simpa [hx_eq_G] using hconjP
  exact hxNotP hxP

private theorem hypothesis_13_1_mu_zero_on_PU_nonP_row_restriction_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) →
                (x : G) ∉ (P : Set G) →
                  ∀ i, i < Nat.card W1 →
                    μ i j x = μ 0 j x := by
  
  classical
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxPU _hxNotP i hi
  have hnotationAlign := hnotation
  rcases hnotation with
    ⟨hω, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal,
      _hνzero_nonprincipal, _hμind, _hνind, _hμsum, _hνsum, _hbaseS,
      _hbaseT, _hμzeroDegree, _hνzeroDegree⟩
  rcases hypothesis_13_1_typePFourSixRowRestriction_source
      hSTypeP ω hω τS hFourSixS with
    ⟨χ, δsel, Wsel, ωsel, σsel, hSelected, _hselDade, hχres⟩
  have hAligni :
      μ i j = χ i j :=
    (hypothesis_13_1_dadeDifferencePointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotationAlign χ δsel Wsel ωsel σsel
      hSelected i j hi hj0 hj).1
  have h0 : 0 < Nat.card W1 := Nat.card_pos (α := W1)
  have hAlign0 :
      μ 0 j = χ 0 j :=
    (hypothesis_13_1_dadeDifferencePointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotationAlign χ δsel Wsel ωsel σsel
      hSelected 0 j h0 hj0 hj).1
  calc
    μ i j x = χ i j x := congrFun hAligni x
    _ = χ 0 j x := hχres i j hi hj x hxPU
    _ = μ 0 j x := congrFun hAlign0.symm x

private theorem hypothesis_13_1_mu_zero_on_PU_nonP_restriction_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) →
                (x : G) ∉ (P : Set G) →
                  μ 0 j x = (Nat.card W1 : ℂ)⁻¹ * μsum j x := by
  
  classical
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxPU hxNotP
  have hnotationRows := hnotation
  rcases hnotation with
    ⟨_hω, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal,
      _hνzero_nonprincipal, _hμind, _hνind, hμsum, _hνsum, _hbaseS,
      _hbaseT, _hμzeroDegree, _hνzeroDegree⟩
  have hrows :
      ∀ i, i < Nat.card W1 → μ i j x = μ 0 j x :=
    hypothesis_13_1_mu_zero_on_PU_nonP_row_restriction_source hmin hcase
      hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
      hFourSixS hFourSixT ω η μ ν μsum νsum δ δ' σ
      hnotationRows j hj0 hj x hxPU hxNotP
  have hsum :
      μsum j x = (Nat.card W1 : ℂ) * μ 0 j x := by
    calc
      μsum j x =
          ((Finset.range (Nat.card W1)).sum (fun i => μ i j)) x := by
            rw [hμsum j hj]
      _ = (Finset.range (Nat.card W1)).sum (fun i => μ i j x) := by
            simp
      _ = (Finset.range (Nat.card W1)).sum (fun _ => μ 0 j x) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hrows i (Finset.mem_range.mp hi)
      _ = (Nat.card W1 : ℂ) * μ 0 j x := by
            simp
  have hcard_ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := W1)).ne'
  rw [hsum]
  rw [← mul_assoc, inv_mul_cancel₀ hcard_ne, one_mul]

private theorem hypothesis_13_1_muColumn_nonbase_not_irreducible_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hTypePDef : Section8.typePDefinitionData Smax P U W1 W2)
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction Smax}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τS)
    (j : J) (_hj : j ≠ j0) :
    ¬ Section1.IsIrreducibleCharacterOnGroup (Section10.muColumn μsel j) := by
  
  intro hIrr
  have hNotation' := hNotation
  rcases hTypePDef with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1Hall, _hW1comp, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, hω, _hσiso, _hσvirt, _hσprincipal, _h45, _h48,
        _htauA0, _hfull⟩
  have hself :
      Section1.scalarProduct Smax (Section10.muColumn μsel j)
        (Section10.muColumn μsel j) = 1 :=
    Section10.scalarProduct_irreducible_self hIrr
  have hcol :
      Section1.scalarProduct Smax (Section10.muColumn μsel j)
        (Section10.muColumn μsel j) = (Fintype.card I : ℂ) :=
    Section10.scalarProduct_muColumn_self_of_section10FourSixNotationSupportedData
      hNotation' j
  have hcardI : Fintype.card I = Nat.card W1 := by
    calc
      Fintype.card I = Nat.card (W1.subgroupOf Smax) := hω.card_left
      _ = Nat.card W1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (H := W1) (K := Smax) _hW1Hall.1).toEquiv
  have hW1card_ne : Nat.card W1 ≠ 1 := by
    intro hcard
    exact hW1ne ((Subgroup.card_eq_one (H := W1)).1 hcard)
  have hcardI_ne : Fintype.card I ≠ 1 := by
    intro hcard
    exact hW1card_ne (hcardI ▸ hcard)
  have hcardCast : (Fintype.card I : ℂ) = 1 := hcol ▸ hself
  have hcardNat : Fintype.card I = 1 := by
    exact_mod_cast hcardCast
  exact hcardI_ne hcardNat

private theorem hypothesis_13_1_nat_prime_card_of_hasPrimeOrder
    {G : Type u} [Group G] [Finite G]
    {A : Subgroup G}
    (hA : section16HasPrimeOrder A) :
    Nat.Prime (Nat.card A) := by
  rcases hA with ⟨p, hp⟩
  rw [hp]
  exact p.property

private theorem hypothesis_13_1_typePDefinitionData_W1_card_eq_relIndex
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (htype : Section8.typePDefinitionData M MF U W1 W2) :
    Nat.card W1 = (ambientDerivedSubgroup M).relIndex M := by
  rcases htype with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleDer, _hUnil,
      _hW1norm, _hDerComp, _hMFnotcyc, _hsecond, _hfitting,
      _hfittingle, _hW2le, _hW2cyc, _hW2ne, _hcentralizer,
      _hnormHat⟩
  have hDerNorm : section10NormalIn (ambientDerivedSubgroup M) M :=
    section12_normalIn_ambientDerivedSubgroup
  have hcompLocal : (W1.subgroupOf M).IsComplement'
      ((ambientDerivedSubgroup M).subgroupOf M) :=
    section12_complementIn_of_normal_isComplement' hMcomp hDerNorm
  have hcardLocal : Fintype.card (W1.subgroupOf M) = Fintype.card W1 := by
    simpa [Nat.card_eq_fintype_card] using
      (section12_card_subgroupOf_eq hMcomp.2.1)
  have hrel : (ambientDerivedSubgroup M).relIndex M = Nat.card W1 := by
    simpa [Subgroup.relIndex, Nat.card_eq_fintype_card, hcardLocal] using
      hcompLocal.index_eq_card
  exact hrel.symm

private theorem
    hypothesis_13_1_typeIIToIVSourceCondition_of_typePDefinitionData_alignment
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 U' W1' W2' : Subgroup G}
    (hcur : Section8.typePDefinitionData M MF U W1 W2)
    (hbranch : Section8.typePDefinitionData M MF U' W1' W2')
    (hcond : Section8.typeIIToIVSourceCondition M U' W1') :
    Section8.typeIIToIVSourceCondition M U W1 := by
  have hW1card : Nat.card W1 = (ambientDerivedSubgroup M).relIndex M :=
    hypothesis_13_1_typePDefinitionData_W1_card_eq_relIndex hcur
  have hW1'card : Nat.card W1' = (ambientDerivedSubgroup M).relIndex M :=
    hypothesis_13_1_typePDefinitionData_W1_card_eq_relIndex hbranch
  rcases hcond with ⟨hU'ne, hW1'prime, hTI⟩
  refine ⟨?_, ?_, hTI⟩
  · intro hUbot
    rcases hcur with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer,
        _hUnil, _hW1norm, hDerComp, _hMFnotcyc, _hsecond,
        _hfitting, _hfittingle, _hW2le, _hW2cyc, _hW2ne,
        _hcentralizer, _hnormHat⟩
    rcases hbranch with
      ⟨_hMF', _hW1cyc', _hW1ne', _hW1Hall', _hMcomp', _hU'leDer,
        _hUnil', _hW1norm', hDerComp', _hMFnotcyc', _hsecond',
        _hfitting', _hfittingle', _hW2le', _hW2cyc', _hW2ne',
        _hcentralizer', _hnormHat'⟩
    rcases hDerComp with ⟨_hMFleDer, _hUleDer', hDerEq, _hMFUdisj⟩
    rcases hDerComp' with
      ⟨_hMFleDer', hU'leDer, _hDerEq', hMFU'disj⟩
    have hDerLeMF : ambientDerivedSubgroup M ≤ MF := by
      rw [hDerEq, hUbot]
      simp
    have hU'leMF : U' ≤ MF := hU'leDer.trans hDerLeMF
    have hU'leBot : U' ≤ (⊥ : Subgroup G) := by
      intro x hx
      exact (Subgroup.disjoint_def.mp hMFU'disj) (hU'leMF hx) hx
    exact hU'ne (le_bot_iff.mp hU'leBot)
  · rcases hW1'prime with ⟨r, hcardPrime⟩
    exact ⟨r, by
      calc
        Nat.card W1 = (ambientDerivedSubgroup M).relIndex M := hW1card
        _ = Nat.card W1' := hW1'card.symm
        _ = r.val := hcardPrime⟩

private theorem hypothesis_13_1_normalizer_le_of_conjBy_eq
    {G : Type u} [Group G]
    {M A B : Subgroup G} {d : G}
    (hdM : d ∈ M)
    (hEq : B = A.conjBy d)
    (hNormB : Subgroup.normalizer (B : Set G) ≤ M) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  intro n hn
  let a : G := d * n * d⁻¹
  have hAn : A.conjBy n = A :=
    section11_conjBy_eq_of_mem_normalizer (G := G) hn
  have haNormB : a ∈ Subgroup.normalizer (B : Set G) := by
    apply section10_mem_normalizer_of_conjBy_eq (G := G)
    calc
      B.conjBy a = (A.conjBy d).conjBy a := by rw [hEq]
      _ = A.conjBy (a * d) := Subgroup.conjBy_conjBy A d a
      _ = A.conjBy (d * n) := by
        congr 1
        simp [a, mul_assoc]
      _ = (A.conjBy n).conjBy d :=
        (Subgroup.conjBy_conjBy A n d).symm
      _ = A.conjBy d := by rw [hAn]
      _ = B := hEq.symm
  have haM : a ∈ M := hNormB haNormB
  have hnEq : n = d⁻¹ * a * d := by simp [a, mul_assoc]
  rw [hnEq]
  exact M.mul_mem (M.mul_mem (M.inv_mem hdM) haM) hdM

private theorem hypothesis_13_1_hypothesis_9_2_of_case_typeP
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    Section9.hypothesis_9_2_statement
      Smax P U W1 W2 (Nat.card W1) := by
  classical
  letI : IsMinCE G := hmin
  have hPDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  have hcaseData := hcase
  rcases hcaseData with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, hSmax, _hTmax,
      hMF, _hTMF, _hSnotI, _hTnotI, _hSeq, _hTeq, _hSdisj,
      _hTdisj, _hW2le, _hW1le, _hST, _hcover, _hOneTypeII,
      hSTypes, _hTTypes, _hCommon⟩
  rcases hSTypes with hII | hrest
  · rcases Section8.theorem_8_8_typeII_to_source_public
        (G := G) (M := Smax) (MF := P) hSmax hMF hII with
      ⟨V, W1', W2', U1, U0, hPV, hCondV, hVcomm, hVnorm, hF⟩
    have hCond : Section8.typeIIToIVSourceCondition Smax U W1 :=
      hypothesis_13_1_typeIIToIVSourceCondition_of_typePDefinitionData_alignment
        hPDef hPV hCondV
    rcases Section11.theorem_11_exists_conj_eq_of_typeP_complements
        (G := G) (M := Smax) (MF := P)
        (U := U) (W1 := W1) (W2 := W2)
        (V := V) (W1' := W1') (W2' := W2') hSmax hPDef hPV with
      ⟨d, hUconj⟩
    have hdM : (d : G) ∈ Smax :=
      (section12_ambientDerivedSubgroup_le (G := G) (E := Smax)) d.property
    have hUcomm : IsMulCommutative U := by
      rw [hUconj]
      haveI : IsMulCommutative V := hVcomm
      unfold Subgroup.conjBy
      infer_instance
    have hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ Smax := by
      intro hNormU
      exact hVnorm
        (hypothesis_13_1_normalizer_le_of_conjBy_eq hdM hUconj hNormU)
    let D : Subgroup G := ambientDerivedSubgroup Smax
    have hDconj : D.conjBy (d : G)⁻¹ = D := by
      apply section11_conjBy_eq_of_mem_normalizer
      exact Subgroup.le_normalizer (D.inv_mem d.property)
    have hMFcopy := hMF
    rcases hMFcopy.1 with
      ⟨hPleS, hPnormalS, _hPnil, _hPHall⟩
    have hSleNormP : Smax ≤ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPleS).1 hPnormalS
    have hPconj : P.conjBy (d : G)⁻¹ = P := by
      apply section11_conjBy_eq_of_mem_normalizer
      exact hSleNormP (Smax.inv_mem hdM)
    have hFconj :
        Section8.typeFData (D.conjBy (d : G)⁻¹)
          (P.conjBy (d : G)⁻¹) V U1 U0 := by
      simpa [D, hDconj, hPconj] using hF
    have hFback :=
      Section8.theorem_8_18_typeFData_conj_back
        (G := G) ((d : G)⁻¹) hFconj
    have hFselected :
        Section8.typeFData (ambientDerivedSubgroup Smax) P U
          (U1.conjBy (d : G)) (U0.conjBy (d : G)) := by
      simpa [D, hUconj] using hFback
    refine
      { maximal := hSmax
        mf := hMF
        typeP := hSTypeP
        typePDefinitionData := hPDef
        typeIIToIVSourceCondition := hCond
        typeIISource := ?_
        typeIIISource := ?_
        typeIVSource := ?_
        typeCases := Or.inl hII
        q_eq := rfl }
    · intro _hII
      exact ⟨hUcomm, hUnorm, U1.conjBy (d : G), U0.conjBy (d : G),
        hFselected⟩
    · intro hIII
      exact False.elim
        (Section8.section16_not_typeIII_or_typeIV_of_typeII
          hSmax hMF hII (Or.inl hIII))
    · intro hIV
      exact False.elim
        (Section8.section16_not_typeIII_or_typeIV_of_typeII
          hSmax hMF hII (Or.inr hIV))
  · rcases hrest with hIII | hrest
    · rcases Section8.theorem_8_8_typeIII_to_source_public
          (G := G) (M := Smax) (MF := P) hSmax hMF hIII with
        ⟨V, W1', W2', hPV, hCondV, _hVcomm, _hVnorm⟩
      have hCond : Section8.typeIIToIVSourceCondition Smax U W1 :=
        hypothesis_13_1_typeIIToIVSourceCondition_of_typePDefinitionData_alignment
          hPDef hPV hCondV
      exact Section11.theorem_11_hypothesis_9_2_of_typeP_typeIIIIV
        (G := G) hSmax hMF hPDef hCond (Or.inl hIII)
    · rcases hrest with hIV | hV
      · rcases Section8.theorem_8_8_typeIV_to_source_public
            (G := G) (M := Smax) (MF := P) hSmax hMF hIV with
          ⟨V, W1', W2', hPV, hCondV, _hVcomm, _hVnorm⟩
        have hCond : Section8.typeIIToIVSourceCondition Smax U W1 :=
          hypothesis_13_1_typeIIToIVSourceCondition_of_typePDefinitionData_alignment
            hPDef hPV hCondV
        exact Section11.theorem_11_hypothesis_9_2_of_typeP_typeIIIIV
          (G := G) hSmax hMF hPDef hCond (Or.inr hIV)
      · have hVsource : Section8.typeVDefinitionData Smax P :=
          Section8.theorem_8_8_typeV_to_source_public
            (G := G) hSmax hMF hV
        exact False.elim
          (Section10.theorem_10_10 ⟨Smax, P, hSmax, hMF, hVsource⟩)

private theorem
    hypothesis_13_1_inducedFromNonkernelFamily_of_nonkernelInducedFamily_typeP_selected
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hMFleMs : MF ≤ Ms)
    (hS : nonkernelInducedFamily M (MF ⊔ U) MF S) :
    Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup M) (Ms.subgroupOf M) S := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer,
      _hUnil, _hW1norm, hDerComp, _hMFnotcyc, _hSecond, _hFit,
      _hFitLe, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hDerEq : ambientDerivedSubgroup M = MF ⊔ U := hDerComp.2.2.1
  have hCarrier : (MF ⊔ U).subgroupOf M = derivedSubgroup M := by
    rw [← hDerEq]
    exact section12_ambientDerivedSubgroup_subgroupOf_eq
  intro X hX
  rcases (hS.2.2 X).mp hX with ⟨B, hBirr, hBnotMF, hXeq⟩
  let Q : Subgroup M → Prop := fun K ↦
    ∃ B : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup B ∧
        ¬ Section1.subgroupInKernel' B ((Ms.subgroupOf M).subgroupOf K) ∧
          X = Section1.inducedCF K B
  have hQ : Q ((MF ⊔ U).subgroupOf M) := by
    refine ⟨B, hBirr, ?_, hXeq⟩
    intro hBkerMs
    apply hBnotMF
    exact Section9.subgroupInKernel'_mono_sec9
      (Subgroup.subgroupOf_mono ((MF ⊔ U).subgroupOf M)
        (Subgroup.subgroupOf_mono M hMFleMs)) hBkerMs
  exact hCarrier ▸ hQ

private theorem hypothesis_13_1_hypothesis_5_2_b_of_selected_fullData
    {G : Type u} [Group G] [Finite G]
    {M Ms W1 W2 : Subgroup G} {Abook : Set G}
    (d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 Abook)
    (S : Finset (Section1.ClassFunction M))
    (hInd : Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup M) (Ms.subgroupOf M) S) :
    Section5.hypothesis_5_2_b_statement S d52.tau := by
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  have hCtx :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := d52.W)
      (H := Ms.subgroupOf M)
      (A := Section8.section8SubgroupSetPreimage M Abook)
      (i0 := d52.i0)
      (j0 := d52.j0)
      (ω := d52.omega)
      (σL := d52.sigmaM)
      (σ := d52.sigma)
      (piChar := d52.piChar)
      (xChar := d52.xChar)
      (deltaSign := d52.deltaSign)
      (τ := d52.tau)
      (H_A := d52.H_A)
      d52.fullHypothesis
  rcases hCtx with
    ⟨_h46, _hTauCyclic, _h48, _hTauIso, _hTauPunctured, _hTauVirtual,
      hAllFamilies, _hTable⟩
  exact hAllFamilies S hInd

private theorem hypothesis_13_1_typePFourSixTauSourceData_of_selected_fullData
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G}
    {Abook A0book A1book : Set G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hNotation :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book)
    (hAbook :
      Abook = Section8.section8CentralizerUnion (ambientDerivedSubgroup M) Ms)
    (hA0book :
      A0book = Abook ∪
        section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
    (hMFleMs : MF ≤ Ms)
    (hMsleDer : Ms ≤ ambientDerivedSubgroup M)
    (hW2prime : Nat.Prime (Nat.card W2))
    (d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 Abook)
    (hA0M : Section2.Hypothesis2 A0book M d52.H_A0)
    (hTauA0 : ∀ α : Section1.ClassFunction M,
      d52.tau α = Section2.dadeTransform d52.H_A0 hA0M.subset_L α) :
    typePFourSixTauSourceData M MF U W1 W2 d52.tau := by
  classical
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  let Apre : Set M := Section8.section8SubgroupSetPreimage M Abook
  let A0local : Set M :=
    Section4Scratch.a0Set (W2.subgroupOf M) d52.W Apre
  have hA0pre :
      Section8.section8SubgroupSetPreimage M A0book =
        Section8.section8CyclicA0Set M W1 W2 Abook :=
    Section8.theorem_8_15_subgroupSetPreimage_typeP_A0_eq hP hA0book
  rcases d52.fullHypothesis with
    ⟨h46, _hW2K, _h31, hSigmaIso, hSigmaVirt, _hSigmaClass,
      hSigmaPrincipal, _h22A, hOmega, h43b, _h43c, _h43d, h45a, h45b,
      _hTauCyclic, h48raw, hTauIso, _hTauPunctured, _hTauVirtual,
      _hBaseColumn, _hBaseRow, _hConjugate⟩
  let deltaSignInt : d52.J → ℤ :=
    fun j => if d52.deltaSign j = 1 then 1 else -1
  have hDeltaSign : d52.deltaSign = fun j => (deltaSignInt j : ℂ) := by
    funext j
    rcases h43b.2.1 j with hj | hj
    · simp [deltaSignInt, hj]
    · simp [deltaSignInt, hj]
  have hW2leM : W2 ≤ M := by
    rcases hP with
      ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer,
        _hUnil, _hW1norm, hDerComp, _hMFnotcyc, _hSecond, _hFit,
        _hFitLe, hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
    intro x hx
    exact section12_ambientDerivedSubgroup_le (hDerComp.1 (hW2le hx).1)
  have hW2primeLocal : Nat.Prime (Nat.card (W2.subgroupOf M)) := by
    rw [natCard_subgroupOf_eq W2 M hW2leM]
    exact hW2prime
  have hGalois : Section10.section10BaseRowGaloisData
      d52.i0 d52.j0 d52.piChar deltaSignInt :=
    Section10.section10BaseRowGaloisData_of_hypothesis_4_6_supported_statement
      M d52.fullHypothesis hDeltaSign hW2primeLocal
  have h48 :
      Section4Scratch.theorem_4_8_statement (W2.subgroupOf M) d52.W Apre
        d52.j0 d52.omega d52.sigma d52.piChar
        (fun j => (deltaSignInt j : ℂ)) d52.tau := by
    simpa [Apre, ← hDeltaSign] using h48raw
  have hA0sub :
      Section8.section8SubgroupSetPreimage M A0book ⊆ A0local := by
    rw [hA0pre]
    exact Section8.section8CyclicA0Set_subset_section4_a0Set
      (M := M) (W1 := W1) (W2 := W2) (A := Abook) (W := d52.W)
      d52.W_eq
  have hNotation10 :
      Section10.section10FourSixNotationSupportedData
        M W1 W2 d52.W Apre A0local d52.i0 d52.j0 d52.piChar
        deltaSignInt d52.omega d52.sigma d52.tau := by
    refine ⟨MF, Ms, Abook, A0book, A1book,
      ⟨rfl, hA0sub, hNotation, d52.H_A0, hA0M,
        fun α _hα => hTauA0 α⟩,
      d52.W_eq, rfl, (by simpa [Apre] using h46), hOmega,
      hSigmaIso, hSigmaVirt, hSigmaPrincipal, d52.sigma_agrees_cyclicTI,
      ⟨d52.xChar, h45a, h45b⟩, h48, hTauIso,
      d52.sigmaM, d52.xChar, d52.H_A, d52.H_A0, ?_, hGalois⟩
    simpa [Apre, ← hDeltaSign] using d52.fullHypothesis
  have hPrimeCarrier :
      Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) d52.W Apre =
        Section8.section8CyclicA0Set M W1 W2 Abook := by
    simp [Apre, Section4Scratch.primeDadeA0Set,
      Section8.section8CyclicA0Set, d52.W_eq]
  have hCyclicDade :
      ∃ hCyclicA0 : Section2.hypothesis_2_2_statement
          (Section4Scratch.subgroupImageSet M
            (Section4Scratch.primeDadeA0Set
              (W1.subgroupOf M) (W2.subgroupOf M) d52.W Apre))
          M d52.H_A0,
        ∀ α : Section1.ClassFunction M,
          Section2.CFOn M
              (Section4Scratch.subgroupImageSet M
                (Section4Scratch.primeDadeA0Set
                  (W1.subgroupOf M) (W2.subgroupOf M) d52.W Apre)) α →
            d52.tau α =
              Section2.dadeTransform d52.H_A0 hCyclicA0.subset_L α := by
    rw [hPrimeCarrier]
    refine ⟨d52.cyclicA0Hypothesis, ?_⟩
    intro α hα
    exact d52.tau_cyclicA0 α hα
  rcases hCyclicDade with ⟨hCyclicA0, hTauCyclicA0⟩
  have hMsSharp :
      ∀ l : M,
        (l : G) ∈ section16NonidentityElements ((Ms : Subgroup G) : Set G) →
          (l : G) ∈ A0book := by
    intro l hl
    rw [hA0book]
    left
    rw [hAbook]
    refine ⟨(l : G), hl, ?_⟩
    refine ⟨⟨hMsleDer hl.1, ?_⟩, hl.2⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  exact
    ⟨d52.I, d52.instFintypeI, d52.instDecidableEqI,
      d52.J, d52.instFintypeJ, d52.instDecidableEqJ,
      d52.W, Apre, A0local, d52.i0, d52.j0, d52.piChar,
      deltaSignInt, d52.omega, d52.sigma, hNotation10,
      d52.sigma_agrees_cyclicTI, d52.H_A0, hCyclicA0, hTauCyclicA0,
      Ms, Abook, A0book, A1book, d52.H_A0, hA0M, hNotation,
      hAbook, hA0book, hMFleMs, hMsSharp, hTauA0⟩

private theorem hypothesis_13_1_typeP_family_dade_setup_of_case_branch
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (h92 : Section9.hypothesis_9_2_statement
      M MF U W1 W2 (Nat.card W1))
    (hW2prime : Nat.Prime (Nat.card W2)) :
    ∃ (Mfam : Finset (Section1.ClassFunction M))
      (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
        Section5.hypothesis_5_2_b_statement Mfam τM ∧
        nonkernelInducedFamily M (MF ⊔ U) MF Mfam ∧
        dadeIsometryRelativeToAZero M MF Mfam τM ∧
        typePFourSixTauSourceData M MF U W1 W2 τM := by
  classical
  letI : IsMinCE G := hmin
  rcases hypothesis_13_1_typeP_induced_family_source
      hmin h92.maximal h92.typeP with ⟨Mfam, hMfam⟩
  have hP := h92.typePDefinitionData
  have hPcopy := hP
  rcases hPcopy with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer,
      _hUnil, _hW1norm, hDerComp, _hMFnotcyc, _hSecond, _hFit,
      _hFitLe, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hMFleDer : MF ≤ ambientDerivedSubgroup M := hDerComp.1
  have hLateSetup :
      (section16TypeIII M MF ∨ section16TypeIV M MF) →
        ∃ (Mfam : Finset (Section1.ClassFunction M))
          (τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G),
            Section5.hypothesis_5_2_b_statement Mfam τM ∧
            nonkernelInducedFamily M (MF ⊔ U) MF Mfam ∧
            dadeIsometryRelativeToAZero M MF Mfam τM ∧
            typePFourSixTauSourceData M MF U W1 W2 τM := by
    intro hLate
    have hLateSource :
        Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF := by
      rcases hLate with hIII | hIV
      · rcases h92.typeIIISource hIII with ⟨hcomm, hnorm⟩
        exact Or.inl ⟨U, W1, W2, hP, h92.typeIIToIVSourceCondition,
          hcomm, hnorm⟩
      · rcases h92.typeIVSource hIV with ⟨hncomm, hnorm⟩
        exact Or.inr ⟨U, W1, W2, hP, h92.typeIIToIVSourceCondition,
          hncomm, hnorm⟩
    have hLateSource' :
        Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF :=
      hLateSource.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
    rcases Section11.theorem_11_exists_notation_8_10_source_data_of_typeP_typeIIIIV
        (G := G) h92.maximal h92.mf hP h92.typeIIToIVSourceCondition hLate with
      ⟨Abook, A0book, A1book, hNotation, hWitness⟩
    rcases Section8.section8Hypothesis52FullData_baseRow_of_late_notation_source_data
        hNotation hWitness hLateSource' with
      ⟨d52, _hBaseRow, hA0M, hTauA0⟩
    have hWitnessCopy := hWitness
    rcases hWitnessCopy with
      ⟨_hP, _hTypes, hAbook, hA0book, _hLateSets⟩
    have hFourSix : typePFourSixTauSourceData M MF U W1 W2 d52.tau :=
      hypothesis_13_1_typePFourSixTauSourceData_of_selected_fullData
        hP hNotation hAbook hA0book hMFleDer le_rfl hW2prime
        d52 hA0M hTauA0
    have hInd : Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup M) ((ambientDerivedSubgroup M).subgroupOf M) Mfam :=
      hypothesis_13_1_inducedFromNonkernelFamily_of_nonkernelInducedFamily_typeP_selected
        hP hMFleDer hMfam
    have h52b : Section5.hypothesis_5_2_b_statement Mfam d52.tau :=
      hypothesis_13_1_hypothesis_5_2_b_of_selected_fullData d52 Mfam hInd
    exact ⟨Mfam, d52.tau, h52b, hMfam, h52b, hFourSix⟩
  rcases h92.typeCases with hII | hIII | hIV
  · rcases h92.typeIISource hII with
      ⟨hUcomm, hUnorm, U1, U0, hF⟩
    rcases Section8.section8Hypothesis52FullData_baseRow_dadeRelative_of_typeII_source_data
        h92.maximal h92.mf hII hP h92.typeIIToIVSourceCondition
        hUcomm hUnorm ⟨U1, U0, hF⟩ with
      ⟨d52, _hBaseRow, _H, _hAMG, _hTauAMG, hA0M, hTauA0⟩
    let Abook : Set G :=
      Section8.section8CentralizerUnion (ambientDerivedSubgroup M) MF
    let A0book : Set G :=
      Abook ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G)
    let A1book : Set G := Section8.a1Set MF
    have hNotation :
        Section8.notation_8_10_source_data
          M MF MF Abook A0book A1book := by
      simpa [Abook, A0book, A1book] using
        (Section8.notation_8_10_source_data_of_typeII_source_fields
          h92.maximal h92.mf hII hP h92.typeIIToIVSourceCondition
          hUcomm hUnorm ⟨U1, U0, hF⟩)
    have hAbook :
        Abook = Section8.section8CentralizerUnion
          (ambientDerivedSubgroup M) MF := rfl
    have hA0book :
        A0book = Abook ∪
          section16ConjugatesOfSetBySet
            (section16HatW W1 W2) (M : Set G) := rfl
    have hFourSix : typePFourSixTauSourceData M MF U W1 W2 d52.tau :=
      hypothesis_13_1_typePFourSixTauSourceData_of_selected_fullData
        hP hNotation hAbook hA0book le_rfl hMFleDer hW2prime
        d52 hA0M hTauA0
    have hInd : Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup M) (MF.subgroupOf M) Mfam :=
      hypothesis_13_1_inducedFromNonkernelFamily_of_nonkernelInducedFamily_typeP_selected
        hP le_rfl hMfam
    have h52b : Section5.hypothesis_5_2_b_statement Mfam d52.tau :=
      hypothesis_13_1_hypothesis_5_2_b_of_selected_fullData d52 Mfam hInd
    exact ⟨Mfam, d52.tau, h52b, hMfam, h52b, hFourSix⟩
  · exact hLateSetup (Or.inl hIII)
  · exact hLateSetup (Or.inr hIV)

private theorem hypothesis_13_1_families_and_dade_setup_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    ∃ (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G),
        Section5.hypothesis_5_2_b_statement Sfam τS ∧
        Section5.hypothesis_5_2_b_statement Tfam τT ∧
        nonkernelInducedFamily Smax (P ⊔ U) P Sfam ∧
        nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam ∧
        dadeIsometryRelativeToAZero Smax P Sfam τS ∧
        dadeIsometryRelativeToAZero Tmax Q Tfam τT ∧
        typePFourSixTauSourceData Smax P U W1 W2 τS ∧
        typePFourSixTauSourceData Tmax Q V W2 W1 τT := by
  have h92S : Section9.hypothesis_9_2_statement
      Smax P U W1 W2 (Nat.card W1) :=
    hypothesis_13_1_hypothesis_9_2_of_case_typeP hmin hcase hSTypeP
  have h92T : Section9.hypothesis_9_2_statement
      Tmax Q V W2 W1 (Nat.card W2) :=
    hypothesis_13_1_hypothesis_9_2_of_case_typeP hmin
      (hypothesis_13_1_case_b_data_swap hcase) hTTypeP
  have hW1prime : Nat.Prime (Nat.card W1) :=
    hypothesis_13_1_nat_prime_card_of_hasPrimeOrder
      h92S.typeIIToIVSourceCondition.2.1
  have hW2prime : Nat.Prime (Nat.card W2) :=
    hypothesis_13_1_nat_prime_card_of_hasPrimeOrder
      h92T.typeIIToIVSourceCondition.2.1
  rcases hypothesis_13_1_typeP_family_dade_setup_of_case_branch
      hmin h92S hW2prime with
    ⟨Sfam, τS, hS52, hSnonker, hSdade, hFourSixS⟩
  rcases hypothesis_13_1_typeP_family_dade_setup_of_case_branch
      hmin h92T hW1prime with
    ⟨Tfam, τT, hT52, hTnonker, hTdade, hFourSixT⟩
  exact ⟨Sfam, Tfam, τS, τT, hS52, hT52, hSnonker, hTnonker,
    hSdade, hTdade, hFourSixS, hFourSixT⟩

private theorem hypothesis_13_1_H0_eq_bot_of_typeIIIIV
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 : Subgroup G} {hp : Nat.Primes}
    (hmin : IsMinCE G)
    (h92 : Section9.hypothesis_9_2_statement
      M MF U W1 W2 (Nat.card W1))
    (hLate : section16TypeIII M MF ∨ section16TypeIV M MF)
    (hho : Section9.hoReductionData M MF U W2 H0 hp) :
    H0 = ⊥ := by
  classical
  letI : IsMinCE G := hmin
  rcases hho with
    ⟨hH0MF, hMFM, hH0NormalM, _hH0NormalMF, hH0LtMF, hElem,
      hTypeData⟩
  rcases hTypeData hLate with ⟨hW2card, hChief, hNotCent⟩
  have hW2prime : Nat.Prime (Nat.card W2) := by
    rw [hW2card]
    exact hp.property
  rcases Section11.theorem_11_exists_hypothesis_10_1_supported_of_typeP_typeIIIIV
      (G := G) h92.maximal h92.mf h92.typePDefinitionData
        h92.typeIIToIVSourceCondition hLate hW2prime with
    ⟨S, tau, h10⟩
  have hPcopy := h92.typePDefinitionData
  rcases hPcopy with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleD, _hUnil,
      _hW1norm, hDerComp, _hMFnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hMFleD : MF ≤ ambientDerivedSubgroup M := hDerComp.1
  have hH0M : H0 ≤ M := hH0MF.trans hMFM
  have hNormalIn : section10NormalIn H0 M := ⟨hH0M, hH0NormalM⟩
  rcases hElem with ⟨hH0NormalMF, hElemAbelian⟩
  have hQuot :
      ∃ hH0H : (H0.subgroupOf MF).Normal,
        letI : (H0.subgroupOf MF).Normal := hH0H
        Nontrivial (MF ⧸ H0.subgroupOf MF) ∧
          IsElementaryAbelian hp.val (MF ⧸ H0.subgroupOf MF) := by
    refine ⟨hH0NormalMF, ?_⟩
    letI : (H0.subgroupOf MF).Normal := hH0NormalMF
    constructor
    · have hH0neTop : H0.subgroupOf MF ≠ ⊤ := by
        intro htop
        have hMFleH0 : MF ≤ H0 := (Subgroup.subgroupOf_eq_top).1 htop
        exact hH0LtMF.not_ge hMFleH0
      exact (QuotientGroup.nontrivial_iff
        (N := H0.subgroupOf MF)).2 hH0neTop
    · exact hElemAbelian
  have hComm : ¬ ⁅U, MF⁆ ≤ H0 := by
    intro hle
    exact hNotCent
      ((Section9.quotientCentralizedBy_iff_commutator_le_sec9).2 hle)
  have hOddM : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order
      (Subgroup.card_subgroup_dvd_card M)
  let C : Subgroup G := subgroupCentralizerIn U MF
  have h11 :
      Section11.hypothesis_11_2_data
        M MF MF U C H0 W1 W2 S tau hp.val (Nat.card W1) :=
    ⟨h10, rfl, hLate, hMFleD, hUleD, rfl, hH0MF, hNormalIn,
      hp.property, hQuot, hChief, hComm, hW2card.symm, rfl,
      h92.typePDefinitionData, hOddM, h92⟩
  exact
    (Section11.theorem_11_7
      M MF MF U C H0 W1 W2 S tau hp.val (Nat.card W1) h11).2.2

private theorem hypothesis_13_1_H0_eq_bot_of_typeII
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 : Subgroup G} {hp : Nat.Primes}
    (hmin : IsMinCE G)
    (h92 : Section9.hypothesis_9_2_statement
      M MF U W1 W2 (Nat.card W1))
    (hII : section16TypeII M MF)
    (hW1prime : Nat.Prime (Nat.card W1))
    (hW2prime : Nat.Prime (Nat.card W2))
    (hho : Section9.hoReductionData M MF U W2 H0 hp) :
    H0 = ⊥ := by
  
  classical
  letI : IsMinCE G := hmin
  have hquotCard :
      Nat.card (MF ⧸ H0.subgroupOf MF) = hp.val ^ Nat.card W1 :=
    Section9.theorem_9_6_typeII_quotient_cardinality_source_core_sec9
      M MF U W1 W2 H0 hp h92 hho hII
  have hMFcard : Nat.card MF = Nat.card W2 ^ Nat.card W1 :=
    ((Section9.theorem_9_3 M MF U W1 W2 (Nat.card W1) h92).1 hII).2
  have hquotDvdMF : Nat.card (MF ⧸ H0.subgroupOf MF) ∣ Nat.card MF :=
    Subgroup.card_quotient_dvd_card (s := H0.subgroupOf MF)
  have hpPowDvd : hp.val ^ Nat.card W1 ∣ Nat.card W2 ^ Nat.card W1 := by
    rw [hquotCard, hMFcard] at hquotDvdMF
    exact hquotDvdMF
  have hW1card_ne : Nat.card W1 ≠ 0 := hW1prime.pos.ne'
  have hpDvdPow : hp.val ∣ Nat.card W2 ^ Nat.card W1 :=
    (dvd_pow_self hp.val hW1card_ne).trans hpPowDvd
  have hp_eq_W2 : hp.val = Nat.card W2 :=
    Nat.prime_eq_prime_of_dvd_pow hp.property hW2prime hpDvdPow
  rcases hho with
    ⟨hH0leMF, _hMFleM, _hH0normalM, hH0normalMF, _hH0ltMF,
      _hElementary, _hLate⟩
  letI : (H0.subgroupOf MF).Normal := hH0normalMF
  have hlagrange :
      Nat.card MF =
        Nat.card (MF ⧸ H0.subgroupOf MF) * Nat.card (H0.subgroupOf MF) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (s := H0.subgroupOf MF)
  have hpow_mul :
      Nat.card W2 ^ Nat.card W1 =
        Nat.card W2 ^ Nat.card W1 * Nat.card (H0.subgroupOf MF) := by
    calc
      Nat.card W2 ^ Nat.card W1 = Nat.card MF := hMFcard.symm
      _ = Nat.card (MF ⧸ H0.subgroupOf MF) * Nat.card (H0.subgroupOf MF) :=
        hlagrange
      _ = Nat.card W2 ^ Nat.card W1 * Nat.card (H0.subgroupOf MF) := by
        rw [hquotCard, hp_eq_W2]
  have hpowPos : 0 < Nat.card W2 ^ Nat.card W1 :=
    pow_pos hW2prime.pos _
  have hH0card : Nat.card (H0.subgroupOf MF) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hpowPos ?_
    simpa using hpow_mul.symm
  have hH0sub_bot : H0.subgroupOf MF = ⊥ :=
    Subgroup.eq_bot_of_card_eq (H0.subgroupOf MF) hH0card
  exact (Subgroup.subgroupOf_eq_bot.mp hH0sub_bot).eq_bot_of_le hH0leMF

private theorem hypothesis_13_1_kernelInducedFamily_bot_of_nonkernel
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hTypePDef : Section8.typePDefinitionData M MF U W1 W2)
    (S : Finset (Section1.ClassFunction M))
    (hS : nonkernelInducedFamily M (MF ⊔ U) MF S) :
    Section9.kernelInducedFamily M (ambientDerivedSubgroup M) MF
      (⊥ : Subgroup G) S := by
  rcases hTypePDef with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleDer, _hUnil,
      _hW1norm, hDerComp, _hMFnoncyc, _hSecond, _hFit, _hFitLe,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  rw [hDerComp.2.2.1]
  rcases hS with ⟨_hMFUleM, hMFle, hmem⟩
  refine ⟨bot_le, hMFle, ?_⟩
  intro chi
  constructor
  · intro hchi
    rcases (hmem chi).mp hchi with ⟨theta, hthetaIrr, hthetaNotKer, hchiEq⟩
    refine ⟨theta, hthetaIrr, hthetaNotKer, ?_, hchiEq⟩
    intro a
    have haM : (((a : (MF ⊔ U).subgroupOf M) : M) : G) ∈
        (⊥ : Subgroup G) := by
      simpa [Subgroup.mem_subgroupOf] using a.property
    have ha : (a : (MF ⊔ U).subgroupOf M) = 1 := by
      apply Subtype.ext
      simpa [Subgroup.mem_bot] using haM
    simp [ha, Section1.degree]
  · rintro ⟨theta, hthetaIrr, hthetaNotKer, _hthetaBot, hchiEq⟩
    rw [hmem chi]
    exact ⟨theta, hthetaIrr, hthetaNotKer, hchiEq⟩

private theorem hypothesis_13_1_kernelInducedSubfamily_of_le
    {G : Type u} [Group G] [Finite G]
    {M MF Y : Subgroup G}
    (S : Finset (Section1.ClassFunction M))
    (hSbot : Section9.kernelInducedFamily M
      (ambientDerivedSubgroup M) MF (⊥ : Subgroup G) S)
    (hYle : Y ≤ ambientDerivedSubgroup M) :
    ∃ SY : Finset (Section1.ClassFunction M),
      SY ⊆ S ∧
        Section9.kernelInducedFamily M (ambientDerivedSubgroup M) MF Y SY := by
  classical
  let SY := Section9.kernelInducedSubfamily_sec9 M
    (ambientDerivedSubgroup M) MF Y S
  refine ⟨SY, Section9.kernelInducedSubfamily_subset_sec9
    M (ambientDerivedSubgroup M) MF Y S, ?_⟩
  exact Section9.kernelInducedFamily_subfamily_of_le_sec9
    M (ambientDerivedSubgroup M) MF (⊥ : Subgroup G) Y S
    hYle bot_le hSbot

private theorem hypothesis_13_1_quotientCentralizerIn_bot_eq_early
    {G : Type u} [Group G]
    {MF U C : Subgroup G}
    (hC : Section9.quotientCentralizerIn MF ⊥ U C) :
    C = subgroupCentralizerIn U MF := by
  ext x
  constructor
  · intro hxC
    have hxU : x ∈ U := hC.1 hxC
    refine ⟨hxU, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (by
      intro h hhMF
      exact (commutatorElement_eq_one_iff_mul_comm.mp
        (Subgroup.mem_bot.mp ((hC.2 x hxU).mp hxC h hhMF))).symm)
  · intro hxC
    have hxU : x ∈ U := hxC.1
    exact (hC.2 x hxU).mpr (by
      intro h hhMF
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (((Subgroup.mem_centralizer_iff.mp hxC.2) h hhMF).symm))

private theorem hypothesis_13_1_typeII_quotientChiefFactorData_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {hp : Nat.Primes} {u : ℕ}
    (hmin : IsMinCE G)
    (h92 : Section9.hypothesis_9_2_statement
      M MF U W1 W2 (Nat.card W1))
    (hII : section16TypeII M MF)
    (hho : Section9.hoReductionData M MF U W2 (⊥ : Subgroup G) hp)
    (hC : Section9.quotientCentralizerIn MF ⊥ U C)
    (hBarU : Section9.quotientBarUCardinality U C u)
    (hSbot : Section9.kernelInducedFamily M (ambientDerivedSubgroup M) MF
      (⊥ : Subgroup G) S) :
    Section9.quotientChiefFactorData_9_6 M MF ⊥ W1 hp := by
  classical
  letI : IsMinCE G := hmin
  rcases h92.typeIISource hII with ⟨hUcomm, hUnorm, hF⟩
  rcases Section8.section8Hypothesis52FullData_dadeRelative_of_typeII_source_data
      h92.maximal h92.mf hII h92.typePDefinitionData
        h92.typeIIToIVSourceCondition hUcomm hUnorm hF with
    ⟨d52, H, hAMG, hTau⟩
  let Cprime : Subgroup G := (_root_.commutator C).map C.subtype
  have hCprimeLe : Cprime ≤ C := by
    exact Subgroup.map_subtype_le (_root_.commutator C)
  have h95 : Section9.notation_9_5_data
      M MF U W1 W2 ⊥ C Cprime d52.tau S :=
    { hypothesis92 := h92
      hoReduction := ⟨hp, hho⟩
      quotientCentralizer := hC
      quotientBarU := ⟨u, hBarU⟩
      Cprime_le_C := hCprimeLe
      Cprime_eq_commutator := rfl
      dade := ⟨H, hAMG, hTau⟩
      kernelInduced := hSbot }
  rcases Section9.theorem_9_6_source_core_sec9
      M MF U W1 W2 ⊥ C Cprime d52.tau S hp h95 hho with
    ⟨_hUC, hchief, hWbar, hcard⟩
  exact Section9.quotientChiefFactorData_9_6_of_source_facts
    M MF U W1 W2 ⊥ hp h92 hho hchief hWbar hcard

private theorem
    hypothesis_13_1_reducible_member_inducedFromLinearHC_of_case_9_7_a
    {G : Type u} [Group G] [Finite G]
    {M MF U H0 C Uprime : Subgroup G}
    {p q a u : ℕ}
    {SH0 SH0C SH0U : Finset (Section1.ClassFunction M)}
    {chi : Section1.ClassFunction M}
    (hchar : Section9.case_9_7_a_characterData M MF U H0 C Uprime
      p q a u SH0 SH0C SH0U)
    (hchi : chi ∈ SH0)
    (hred : ¬ Section1.IsIrreducibleCharacterOnGroup chi) :
    Section9.inducedFromLinearCharacterOfHC M MF C chi := by
  /-
  Checked character-by-character projection of PF `(9.8)(b)`: the named
  reducible subfamily contains every reducible member of `SH0`, and each of
  its members is induced from a linear character of `MF ⊔ C`.
  -/
  rcases hchar with
    ⟨_hdegree, _hunderlying, _hBarU, hreducibles, _hexists, _hinitial⟩
  rcases hreducibles with ⟨R, _hRcard, hRdata, _hRsub, hRlinear⟩
  exact hRlinear chi (hRdata.2.2 chi hchi hred)

private theorem
    hypothesis_13_1_reducible_member_inducedFromLinearHC_of_case_9_7_b
    {G : Type u} [Group G] [Finite G]
    {M MF H0 C : Subgroup G}
    {p q u : ℕ}
    {SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)}
    {chi : Section1.ClassFunction M}
    (hchar : Section9.case_9_7_b_characterData M MF H0 C
      p q u SH0 SH0C SH0Cprime)
    (hSCsub : SH0C ⊆ SH0Cprime)
    (hchi : chi ∈ SH0)
    (hred : ¬ Section1.IsIrreducibleCharacterOnGroup chi) :
    Section9.inducedFromLinearCharacterOfHC M MF C chi := by
  /-
  Checked character-by-character projection of PF `(9.9)(b)`: reducibility
  puts `chi` in the named subfamily inside `SH0C`; monotonicity moves it to
  `SH0Cprime`, where PF `(9.9)(a)` supplies linear induction from `MF ⊔ C`.
  -/
  rcases hchar with
    ⟨_hdegree, hlinear, hreducibles, _hnoIrreducible⟩
  rcases hreducibles with ⟨R, _hRcard, hRdata, hRsub⟩
  have hchiR : chi ∈ R := hRdata.2.2 chi hchi hred
  exact (hlinear chi (hSCsub (hRsub hchiR))).2

private theorem hypothesis_13_1_inducedFromLinearHC_to_fitting
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G}
    (hTypePDef : Section8.typePDefinitionData M MF U W1 W2)
    (hC : C = subgroupCentralizerIn U MF)
    {chi : Section1.ClassFunction M}
    (hlinear : Section9.inducedFromLinearCharacterOfHC M MF C chi) :
    ∃ theta : Section1.ClassFunction
        ((section8FittingSubgroup M).subgroupOf M),
      Section1.IsIrreducibleCharacterOnGroup theta ∧
        Section1.degree theta = 1 ∧
        chi = Section1.inducedCF
          ((section8FittingSubgroup M).subgroupOf M) theta := by
  /-
  Checked PF `(8.5.a)` transport from the Section 9 subgroup `MF ⊔ C` to
  the source Fitting subgroup.  The linear degree is retained for the later
  PF `(13.18)` identity-degree calculation.
  -/
  have hFitEq : section8FittingSubgroup M = MF ⊔ C := by
    calc
      section8FittingSubgroup M = MF ⊔ subgroupCentralizerIn U MF :=
        Section8.theorem_8_5_a M MF U W1 W2 hTypePDef
      _ = MF ⊔ C := by rw [hC]
  rw [hFitEq]
  rcases hlinear with ⟨theta, hthetaIrr, hthetaDegree, hchi⟩
  exact ⟨theta, hthetaIrr, hthetaDegree, hchi⟩

private theorem hypothesis_13_1_typeP_reducibleFamilyMember_to_fitting
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    {chi : Section1.ClassFunction Smax}
    (hchi : chi ∈ Sfam)
    (hReducible : ¬ Section1.IsIrreducibleCharacterOnGroup chi) :
    ∃ θ : Section1.ClassFunction
        ((section8FittingSubgroup Smax).subgroupOf Smax),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.degree θ = 1 ∧
        chi = Section1.inducedCF
          ((section8FittingSubgroup Smax).subgroupOf Smax) θ := by
  
  classical
  letI : IsMinCE G := hmin
  have h92 : Section9.hypothesis_9_2_statement
      Smax P U W1 W2 (Nat.card W1) :=
    hypothesis_13_1_hypothesis_9_2_of_case_typeP hmin hcase hSTypeP
  have h92T : Section9.hypothesis_9_2_statement
      Tmax Q V W2 W1 (Nat.card W2) :=
    hypothesis_13_1_hypothesis_9_2_of_case_typeP hmin
      (hypothesis_13_1_case_b_data_swap hcase) hTTypeP
  have hW1prime : Nat.Prime (Nat.card W1) :=
    hypothesis_13_1_nat_prime_card_of_hasPrimeOrder
      h92.typeIIToIVSourceCondition.2.1
  have hW2prime : Nat.Prime (Nat.card W2) :=
    hypothesis_13_1_nat_prime_card_of_hasPrimeOrder
      h92T.typeIIToIVSourceCondition.2.1
  have hTypePDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    h92.typePDefinitionData
  have hSbot : Section9.kernelInducedFamily Smax
      (ambientDerivedSubgroup Smax) P (⊥ : Subgroup G) Sfam :=
    hypothesis_13_1_kernelInducedFamily_bot_of_nonkernel
      hTypePDef Sfam hSnonker
  rcases Section9.theorem_9_4 Smax P U W1 W2 (Nat.card W1) h92 with
    ⟨H0, hp, hho⟩
  have hH0bot : H0 = (⊥ : Subgroup G) := by
    rcases h92.typeCases with hII | hIII | hIV
    · exact hypothesis_13_1_H0_eq_bot_of_typeII
        hmin h92 hII hW1prime hW2prime hho
    · exact hypothesis_13_1_H0_eq_bot_of_typeIIIIV
        hmin h92 (Or.inl hIII) hho
    · exact hypothesis_13_1_H0_eq_bot_of_typeIIIIV
        hmin h92 (Or.inr hIV) hho
  subst H0
  have hUW1normP : U ⊔ W1 ≤ Subgroup.normalizer (P : Set G) :=
    (Section9.theorem_9_3_action_normalizes_and_solvable_sec9
      Smax P U W1 W2 (Nat.card W1) h92).1
  have hUnormP : U ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_left.trans hUW1normP
  letI : Subgroup.Normalizes U P := ⟨hUnormP⟩
  have hbotNormal : ((⊥ : Subgroup G).subgroupOf P).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have hbotInvariant :
      IsInvariant U P ((⊥ : Subgroup G).subgroupOf P) := by
    simpa [Subgroup.bot_subgroupOf] using
      (isInvariant_of_characteristic (A := U) (G := P) (⊥ : Subgroup P))
  rcases Section9.exists_quotientCentralizerIn_normal_of_invariant_sec9
      hbotNormal hbotInvariant with ⟨C, hC, hCnormal⟩
  let u : ℕ := Nat.card (U ⧸ C.subgroupOf U)
  have hBarU : Section9.quotientBarUCardinality U C u :=
    ⟨hC.1, hCnormal, rfl⟩
  have h96 : Section9.quotientChiefFactorData_9_6
      Smax P (⊥ : Subgroup G) W1 hp := by
    rcases h92.typeCases with hII | hIII | hIV
    · exact hypothesis_13_1_typeII_quotientChiefFactorData_bot
        hmin h92 hII hho hC hBarU hSbot
    · have hLate : section16TypeIII Smax P ∨ section16TypeIV Smax P :=
        Or.inl hIII
      rcases Section9.theorem_9_6_typeIIIIV_cardinality_source_core_sec9
          Smax P U W1 W2 (⊥ : Subgroup G) hp h92 hho hLate with
        ⟨hFixedCard, hQuotCard⟩
      exact Section9.quotientChiefFactorData_9_6_of_source_facts
        Smax P U W1 W2 (⊥ : Subgroup G) hp h92 hho
          ((hho.2.2.2.2.2.2 hLate).2.1) hFixedCard hQuotCard
    · have hLate : section16TypeIII Smax P ∨ section16TypeIV Smax P :=
        Or.inr hIV
      rcases Section9.theorem_9_6_typeIIIIV_cardinality_source_core_sec9
          Smax P U W1 W2 (⊥ : Subgroup G) hp h92 hho hLate with
        ⟨hFixedCard, hQuotCard⟩
      exact Section9.quotientChiefFactorData_9_6_of_source_facts
        Smax P U W1 W2 (⊥ : Subgroup G) hp h92 hho
          ((hho.2.2.2.2.2.2 hLate).2.1) hFixedCard hQuotCard
  have h97 :
      (∃ a : ℕ, Section9.case_9_7_a_data Smax P U W1 W2 ⊥ C
        hp.val (Nat.card W1) a) ∨
      Section9.case_9_7_b_data Smax P U W1 W2 ⊥ C
        hp.val (Nat.card W1) u :=
    Section9.theorem_9_7_source_core_sec9
      Smax P U W1 W2 ⊥ C hp.val (Nat.card W1) u h92
        ⟨hp, rfl, hho, h96⟩ hC hBarU
  have hTypePFields := hTypePDef
  rcases hTypePFields with
    ⟨_hP, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleD, _hUnil,
      _hW1norm, _hDerComp, _hPnotcyc, _hsecond, _hfitting,
      _hfittingle, _hW2le, _hW2cyc, _hW2ne, _hcentralizer,
      _hnormHat⟩
  have hCleD : C ≤ ambientDerivedSubgroup Smax := hC.1.trans hUleD
  have hbotCLeD : (⊥ : Subgroup G) ⊔ C ≤ ambientDerivedSubgroup Smax :=
    sup_le bot_le hCleD
  rcases hypothesis_13_1_kernelInducedSubfamily_of_le
      Sfam hSbot hbotCLeD with ⟨SC, _hSCsubS, hSC⟩
  let Uprime : Subgroup G := (_root_.commutator U).map U.subtype
  have hUprimeLeU : Uprime ≤ U := by
    exact Subgroup.map_subtype_le (_root_.commutator U)
  have hbotUprimeLeD :
      (⊥ : Subgroup G) ⊔ Uprime ≤ ambientDerivedSubgroup Smax :=
    sup_le bot_le (hUprimeLeU.trans hUleD)
  rcases hypothesis_13_1_kernelInducedSubfamily_of_le
      Sfam hSbot hbotUprimeLeD with ⟨SUprime, _hSUprimeSubS, hSUprime⟩
  let Cprime : Subgroup G := (_root_.commutator C).map C.subtype
  have hCprimeLeC : Cprime ≤ C := by
    exact Subgroup.map_subtype_le (_root_.commutator C)
  have hbotCprimeLeD :
      (⊥ : Subgroup G) ⊔ Cprime ≤ ambientDerivedSubgroup Smax :=
    sup_le bot_le (hCprimeLeC.trans hCleD)
  rcases hypothesis_13_1_kernelInducedSubfamily_of_le
      Sfam hSbot hbotCprimeLeD with
    ⟨SCprime, _hSCprimeSubS, hSCprime⟩
  have hSCsubSCprime : SC ⊆ SCprime :=
    Section9.kernelInducedFamily_subset_of_le_sec9
      Smax (ambientDerivedSubgroup Smax) P
        ((⊥ : Subgroup G) ⊔ Cprime) ((⊥ : Subgroup G) ⊔ C)
        SCprime SC (sup_le_sup le_rfl hCprimeLeC) hSCprime hSC
  have hCeq : C = subgroupCentralizerIn U P :=
    hypothesis_13_1_quotientCentralizerIn_bot_eq_early hC
  rcases h97 with ⟨a, hcaseA⟩ | hcaseB
  · have hcharA : Section9.case_9_7_a_characterData
        Smax P U ⊥ C Uprime hp.val (Nat.card W1) a u Sfam SC SUprime :=
      Section9.theorem_9_8_source_core_sec9
        Smax P U W1 W2 ⊥ C Uprime hp.val (Nat.card W1) a u
          Sfam SC SUprime hcaseA hBarU rfl hSbot hSC hSUprime
    exact hypothesis_13_1_inducedFromLinearHC_to_fitting hTypePDef hCeq
      (hypothesis_13_1_reducible_member_inducedFromLinearHC_of_case_9_7_a
        hcharA hchi hReducible)
  · have hcharB : Section9.case_9_7_b_characterData
        Smax P ⊥ C hp.val (Nat.card W1) u Sfam SC SCprime :=
      Section9.theorem_9_9_source_core_sec9
        Smax P U W1 W2 ⊥ C Cprime hp.val (Nat.card W1) u
          Sfam SC SCprime hcaseB rfl hSbot hSC hSCprime
    exact hypothesis_13_1_inducedFromLinearHC_to_fitting hTypePDef hCeq
      (hypothesis_13_1_reducible_member_inducedFromLinearHC_of_case_9_7_b
        hcharB hSCsubSCprime hchi hReducible)

private theorem hypothesis_13_1_selected_xChar_not_subgroupInKernel_early
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction Smax}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τS)
    (xChar : J → Section1.ClassFunction (derivedSubgroup Smax))
    (h45a : Section4Scratch.theorem_4_5_a_statement
      (derivedSubgroup Smax) μsel xChar) :
    ∀ j : J, j ≠ j0 →
      ¬ Section1.subgroupInKernel' (xChar j)
        ((P.subgroupOf Smax).subgroupOf (derivedSubgroup Smax)) := by
  classical
  rcases hSTypeP with ⟨hMF, hCommon⟩
  rcases hCommon with
    ⟨_hHallD, hPleAmbient, hCompMFU, _hUnil, _hW1norm, _hW1cyc,
      _hW1card, _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2leP, _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6,
      _hW2Second⟩
  have hDerEq : ambientDerivedSubgroup Smax = P ⊔ U := hCompMFU.2.2.1
  have hPleDer : P.subgroupOf Smax ≤ derivedSubgroup Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxPU : (x : G) ∈ (P ⊔ U : Subgroup G) :=
      (le_sup_left : P ≤ P ⊔ U) hxP
    have hxDerG : (x : G) ∈ ambientDerivedSubgroup Smax := by
      simpa [hDerEq] using hxPU
    have hxDerSub : x ∈ (ambientDerivedSubgroup Smax).subgroupOf Smax := by
      simpa [Subgroup.mem_subgroupOf] using hxDerG
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := Smax)]
      using hxDerSub
  rcases hNotation with
    ⟨_MFsrc, Ms, _Abook, _A0book, _A1book, hSource,
      _hW, _hA0, h46, _hωNotation, _hIsoNotation, _hVirtNotation,
      _hPrinNotation, _hSigmaAgree, _h45Notation, _h48Notation,
      _hTauIsoNotation, hPackage⟩
  rcases hSource with
    ⟨_hApre, _hA0sub, hSourceNotation, _hTauSource⟩
  rcases hPackage with
    ⟨σM, _xCharFull, _H_A, _H_A0, hSupported, _hGalois⟩
  rcases hSupported with
    ⟨_h46Full, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨hω, h43b, h43c, _h43d, _h45aFull, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  have hMFsrcEq : _MFsrc = P :=
    section16MFSubgroup_unique hSourceNotation.2.1 hMF
  subst _MFsrc
  have hPleMs : P ≤ Ms := by
    rcases hSourceNotation.2.2.1.to_literal with hEarly | hLate
    · rw [hEarly.2]
    · rw [hLate.2]
      exact hPleAmbient
  have hPleMsSub : P.subgroupOf Smax ≤ Ms.subgroupOf Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using hPleMs hxP
  have h46P :
      Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        Wsec
        (P.subgroupOf Smax)
        A := by
    rcases h46 with ⟨h42, _hKnormal, _hW2leK, _hKleK, hUnionK, hAsub⟩
    refine ⟨h42, Section12.section16MFSubgroup_subgroupOf_normal hMF, ?_,
      hPleDer, ?_, hAsub⟩
    · intro x hx
      have hxW2 : (x : G) ∈ W2 := by
        simpa [Subgroup.mem_subgroupOf] using hx
      simpa [Subgroup.mem_subgroupOf] using hW2leP hxW2
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨h, hxcentral⟩
      let k : {k : Ms.subgroupOf Smax // (k : Smax) ≠ 1} :=
        ⟨⟨(h.1 : Smax), hPleMsSub h.1.2⟩, by simpa using h.2⟩
      exact hUnionK (Set.mem_iUnion.mpr ⟨k, by simpa [k] using hxcentral⟩)
  have h47full :
      Section4Scratch.theorem_4_7_full_statement
        (derivedSubgroup Smax)
        (P.subgroupOf Smax)
        A
        j0 μsel xChar :=
    Section4Scratch.theorem_4_7_full
      (K := derivedSubgroup Smax)
      (W1 := W1.subgroupOf Smax)
      (W2 := W2.subgroupOf Smax)
      (W := Wsec)
      (H := P.subgroupOf Smax)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ωsec)
      (σ := σM)
      (piChar := μsel)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      h46P h45a hω h43b h43c
  intro j hj
  exact (h47full.2 j hj).1

/- The selected/natural column transport needed by the PF `(13.3)(c)`
coherence argument.  This exposes only the concrete Section `(4.6)` package
and the two complete-column equalities; the entrywise convention leaves remain
private to PF `(13.1)`. -/
public theorem hypothesis_13_1_selectedColumnTransportData_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
            ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
              ∃ Wsec : Subgroup Smax, ∃ A A0 : Set Smax, ∃ i0 : I, ∃ j0 : J,
                ∃ μsel : I → J → Section1.ClassFunction Smax,
                  ∃ δSign : J → ℤ,
                    ∃ ωsec : I → J → Section1.ClassFunction Wsec,
                      ∃ σsec : Section1.ClassFunction Wsec →ₗ[ℂ]
                          Section1.ClassFunction G,
                        @Section10.section10FourSixNotationSupportedData G _ _ I J
                            instI instJ decI decJ Smax W1 W2 Wsec
                            A A0 i0 j0 μsel δSign ωsec σsec τS ∧
                          ∃ row : ℕ → I, ∃ col : ℕ → J,
                            row 0 = i0 ∧
                            col 0 = j0 ∧
                            (∀ j, 0 < j → j < Nat.card W2 → col j ≠ j0) ∧
                            (∀ j k, j < Nat.card W2 → k < Nat.card W2 →
                              col j = col k → j = k) ∧
                            (∀ jSel : J, ∃ k, k < Nat.card W2 ∧
                              col k = jSel) ∧
                            (∀ j, 0 < j → j < Nat.card W2 →
                              δSign (col j) = δ j) ∧
                            (∀ j, 0 < j → j < Nat.card W2 →
                              Section10.muColumn μsel (col j) = μsum j) ∧
                            ∀ j, 0 < j → j < Nat.card W2 →
                              Section4Scratch.omegaColumnSigma σsec ωsec
                                  (col j) =
                                (Finset.range (Nat.card W1)).sum
                                  (fun i => η i j) := by
  classical
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  have hnotationAlign := hnotation
  rcases hnotation with
    ⟨hω, _hσ, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      hμsum, _hνsum, _hbaseS, _hbaseT, _hμzeroDegree, _hνzeroDegree⟩
  have hFourSixSAlign := hFourSixS
  rcases hFourSixS with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hSelNotation, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      hSTypeP ω hω τS Wsec A A0 i0 j0 μsel δSign ωsec σsec
      hSelNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, hcol_inj, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport⟩
  let χ : ℕ → ℕ → Section1.ClassFunction Smax :=
    fun i j => μsel (row i) (col j)
  let δsel : ℕ → ℤ := fun j => δSign (col j)
  let ωsel : ℕ → ℕ → Section1.ClassFunction Wsec :=
    fun i j => ωsec (row i) (col j)
  have hSelected :
      hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω hω τS
        χ δsel Wsec ωsel σsec :=
    hypothesis_13_1_selectedTypePFourSixTableData_of_package
      hSTypeP ω hω τS hSelNotation row col hrow0 hcol0 hcol_ne hrow_inj
      hrow_surj hcol_surj hIndTransport hExactTransport
  have hMuAlign :
      ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
        μ i j = μsel (row i) (col j) := by
    intro i j hi hj0 hj
    exact
      hypothesis_13_1_dadeDifferencePointwiseMuAlignment_s_side_source
        hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
        hDadeS hDadeT hFourSixSAlign hFourSixT
        ω η μ ν μsum νsum δ δ' σ hnotationAlign
        χ δsel Wsec ωsel σsec hSelected i j hi hj0 hj
  have hSigmaAlign :
      ∀ i j, i < Nat.card W1 → 0 < j → j < Nat.card W2 →
        σ (ω i j) = σsec (ωsec (row i) (col j)) := by
    intro i j hi hj0 hj
    exact
      hypothesis_13_1_dadeDifferencePointwiseSigmaOmegaAlignment_s_side_source
        hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
        hDadeS hDadeT hFourSixSAlign hFourSixT
        ω η μ ν μsum νsum δ δ' σ hnotationAlign
        χ δsel Wsec ωsel σsec hSelected i j hi hj0 hj
  have hDeltaAlign : ∀ j, 0 < j → j < Nat.card W2 →
      δSign (col j) = δ j := by
    intro j hj0 hj
    exact
      (hypothesis_13_1_dadeDifferencePointwiseDeltaAlignment_selectedColumn_source
        ω η μ ν μsum νsum δ δ' σ hnotationAlign hSelNotation row col hrow0
        hcol0 hcol_ne hrow_inj hIndTransport j hj0 hj).symm
  let rowSub : {i : ℕ // i < Nat.card W1} → I := fun i => row i.1
  have hrowSub_inj : Function.Injective rowSub := by
    intro i k hik
    apply Subtype.ext
    exact hrow_inj i.1 k.1 i.2 k.2 hik
  have hrowSub_surj : Function.Surjective rowSub := by
    intro iSel
    rcases hrow_surj iSel with ⟨k, hk, hrowk⟩
    exact ⟨⟨k, hk⟩, hrowk⟩
  let eI : {i : ℕ // i < Nat.card W1} ≃ I :=
    Equiv.ofBijective rowSub ⟨hrowSub_inj, hrowSub_surj⟩
  let eRange :
      {i : ℕ // i < Nat.card W1} ≃
        {i : ℕ // i ∈ Finset.range (Nat.card W1)} :=
    { toFun := fun i => ⟨i.1, (Finset.mem_range).2 i.2⟩
      invFun := fun i => ⟨i.1, (Finset.mem_range).1 i.2⟩
      left_inv := by intro i; cases i; rfl
      right_inv := by intro i; cases i; rfl }
  have hcolumn : ∀ j, 0 < j → j < Nat.card W2 →
      Section10.muColumn μsel (col j) = μsum j := by
    intro j hj0 hj
    ext g
    calc
      Section10.muColumn μsel (col j) g =
          (∑ i : I, μsel i (col j) g) := by
            simp [Section10.muColumn]
      _ = ∑ i : {i : ℕ // i < Nat.card W1},
          μsel (row i.1) (col j) g := by
            exact (Fintype.sum_equiv eI
              (fun i : {i : ℕ // i < Nat.card W1} =>
                μsel (row i.1) (col j) g)
              (fun i : I => μsel i (col j) g)
              (by intro i; rfl)).symm
      _ = ∑ i : {i : ℕ // i < Nat.card W1}, μ i.1 j g := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact congrFun (hMuAlign i.1 j i.2 hj0 hj).symm g
      _ = ∑ i : {i : ℕ // i ∈ Finset.range (Nat.card W1)}, μ i.1 j g := by
            exact Fintype.sum_equiv eRange
              (fun i : {i : ℕ // i < Nat.card W1} => μ i.1 j g)
              (fun i : {i : ℕ // i ∈ Finset.range (Nat.card W1)} => μ i.1 j g)
              (by intro i; rfl)
      _ = (Finset.range (Nat.card W1)).sum (fun i => μ i j g) := by
            simpa using
              (Finset.sum_attach (s := Finset.range (Nat.card W1))
                (f := fun i => μ i j g))
      _ = μsum j g := by simp [hμsum j hj]
  have homegaColumn : ∀ j, 0 < j → j < Nat.card W2 →
      Section4Scratch.omegaColumnSigma σsec ωsec (col j) =
        (Finset.range (Nat.card W1)).sum (fun i => η i j) := by
    intro j hj0 hj
    ext g
    calc
      Section4Scratch.omegaColumnSigma σsec ωsec (col j) g =
          (∑ i : I, σsec (ωsec i (col j)) g) := by
            simp [Section4Scratch.omegaColumnSigma]
      _ = ∑ i : {i : ℕ // i < Nat.card W1},
          σsec (ωsec (row i.1) (col j)) g := by
            exact (Fintype.sum_equiv eI
              (fun i : {i : ℕ // i < Nat.card W1} =>
                σsec (ωsec (row i.1) (col j)) g)
              (fun i : I => σsec (ωsec i (col j)) g)
              (by intro i; rfl)).symm
      _ = ∑ i : {i : ℕ // i < Nat.card W1}, σ (ω i.1 j) g := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact congrFun (hSigmaAlign i.1 j i.2 hj0 hj).symm g
      _ = ∑ i : {i : ℕ // i ∈ Finset.range (Nat.card W1)},
          σ (ω i.1 j) g := by
            exact Fintype.sum_equiv eRange
              (fun i : {i : ℕ // i < Nat.card W1} => σ (ω i.1 j) g)
              (fun i : {i : ℕ // i ∈ Finset.range (Nat.card W1)} =>
                σ (ω i.1 j) g)
              (by intro i; rfl)
      _ = (Finset.range (Nat.card W1)).sum (fun i => σ (ω i j) g) := by
            simpa using
              (Finset.sum_attach (s := Finset.range (Nat.card W1))
                (f := fun i => σ (ω i j) g))
      _ = (Finset.range (Nat.card W1)).sum (fun i => η i j g) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact congrFun (hη i j (Finset.mem_range.mp hi) hj).symm g
      _ = ((Finset.range (Nat.card W1)).sum (fun i => η i j)) g := by simp
  exact ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
    δSign, ωsec, σsec, hSelNotation, row, col, hrow0, hcol0, hcol_ne,
    hcol_inj, hcol_surj, hDeltaAlign, hcolumn, homegaColumn⟩

private theorem hypothesis_13_1_muSum_fittingData_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            μsum j ∈ Sfam ∧
              (∃ θ : Section1.ClassFunction
                  ((section8FittingSubgroup Smax).subgroupOf Smax),
                Section1.IsIrreducibleCharacterOnGroup θ ∧
                  Section1.degree θ = 1 ∧
                  μsum j = Section1.inducedCF
                    ((section8FittingSubgroup Smax).subgroupOf Smax) θ) ∧
              Section1.degree (μsum j) =
                (Nat.card W1 : ℂ) * Section1.degree (μ 0 j) := by
  
  classical
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  have hnotationAlign := hnotation
  rcases hnotation with
    ⟨hω, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      hμsum, _hνsum, _hbaseS, _hbaseT, _hμzeroDegree, _hνzeroDegree⟩
  have hFourSixSAlign := hFourSixS
  rcases hFourSixS with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hNotation, _hSigmaAgree, ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      hSTypeP ω hω τS Wsec A A0 i0 j0 μsel δSign ωsec σsec hNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, _hcol_inj, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport⟩
  let χ : ℕ → ℕ → Section1.ClassFunction Smax :=
    fun i j => μsel (row i) (col j)
  let δsel : ℕ → ℤ := fun j => δSign (col j)
  let ωsel : ℕ → ℕ → Section1.ClassFunction Wsec :=
    fun i j => ωsec (row i) (col j)
  have hSelected :
      hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω hω τS
        χ δsel Wsec ωsel σsec :=
    hypothesis_13_1_selectedTypePFourSixTableData_of_package
      hSTypeP ω hω τS hNotation row col hrow0 hcol0 hcol_ne hrow_inj
      hrow_surj hcol_surj hIndTransport hExactTransport
  have hAlign :
      ∀ i, i < Nat.card W1 → μ i j = μsel (row i) (col j) := by
    intro i hi
    exact
      hypothesis_13_1_dadeDifferencePointwiseMuAlignment_s_side_source
        hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
        hDadeS hDadeT hFourSixSAlign hFourSixT
        ω η μ ν μsum νsum δ δ' σ hnotationAlign χ δsel Wsec ωsel σsec
        hSelected i j hi hj0 hj
  let rowSub : {i : ℕ // i < Nat.card W1} → I := fun i => row i.1
  have hrowSub_inj : Function.Injective rowSub := by
    intro i k hik
    apply Subtype.ext
    exact hrow_inj i.1 k.1 i.2 k.2 hik
  have hrowSub_surj : Function.Surjective rowSub := by
    intro iSel
    rcases hrow_surj iSel with ⟨k, hk, hrowk⟩
    exact ⟨⟨k, hk⟩, hrowk⟩
  let eI : {i : ℕ // i < Nat.card W1} ≃ I :=
    Equiv.ofBijective rowSub ⟨hrowSub_inj, hrowSub_surj⟩
  have hcolumn :
      Section10.muColumn μsel (col j) = μsum j := by
    ext g
    have hsumI :
        (∑ i : I, μsel i (col j) g) =
          ∑ i : {i : ℕ // i < Nat.card W1}, μsel (row i.1) (col j) g := by
      exact (Fintype.sum_equiv eI
        (fun i : {i : ℕ // i < Nat.card W1} => μsel (row i.1) (col j) g)
        (fun i : I => μsel i (col j) g)
        (by intro i; rfl)).symm
    have hentrySum :
        (∑ i : {i : ℕ // i < Nat.card W1}, μsel (row i.1) (col j) g) =
          ∑ i : {i : ℕ // i < Nat.card W1}, μ i.1 j g := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact congrFun (hAlign i.1 i.2).symm g
    have hrangeSum :
        (∑ i : {i : ℕ // i < Nat.card W1}, μ i.1 j g) =
          (Finset.range (Nat.card W1)).sum (fun i => μ i j g) := by
      let eRange :
          {i : ℕ // i < Nat.card W1} ≃
            {i : ℕ // i ∈ Finset.range (Nat.card W1)} :=
        { toFun := fun i => ⟨i.1, (Finset.mem_range).2 i.2⟩
          invFun := fun i => ⟨i.1, (Finset.mem_range).1 i.2⟩
          left_inv := by
            intro i
            cases i
            rfl
          right_inv := by
            intro i
            cases i
            rfl }
      calc
        (∑ i : {i : ℕ // i < Nat.card W1}, μ i.1 j g) =
            ∑ i : {i : ℕ // i ∈ Finset.range (Nat.card W1)}, μ i.1 j g := by
          exact Fintype.sum_equiv eRange
            (fun i : {i : ℕ // i < Nat.card W1} => μ i.1 j g)
            (fun i : {i : ℕ // i ∈ Finset.range (Nat.card W1)} => μ i.1 j g)
            (by intro i; rfl)
        _ = (Finset.range (Nat.card W1)).sum (fun i => μ i j g) := by
          simpa using
            (Finset.sum_attach (s := Finset.range (Nat.card W1))
              (f := fun i => μ i j g))
    calc
      Section10.muColumn μsel (col j) g =
          (∑ i : I, μsel i (col j) g) := by
            simp [Section10.muColumn]
      _ = (Finset.range (Nat.card W1)).sum (fun i => μ i j g) := by
            rw [hsumI, hentrySum, hrangeSum]
      _ = μsum j g := by
            simp [hμsum j hj]
  
  have hTypePDef :
      Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  have hSTypePForDerived := hSTypeP
  rcases hSTypePForDerived.2 with
    ⟨_hHallD, _hPleD, hCompPU, _hUnil, _hW1norm, _hW1cyc,
      _hW1card, _hPnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6,
      _hW2Second⟩
  have hDerEq : ambientDerivedSubgroup Smax = P ⊔ U := hCompPU.2.2.1
  have hSnonkerDerived :
      nonkernelInducedFamily Smax (ambientDerivedSubgroup Smax) P Sfam := by
    simpa [hDerEq] using hSnonker
  rcases hSnonkerDerived with ⟨_hDerLe, _hPLeDer, hSfamMem⟩
  have hNotationForMem := hNotation
  rcases hNotationForMem with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin,
      _hSigmaAgreeCyclic, h45, _h48, _hTauIso, _hFull⟩
  rcases h45 with ⟨xChar, h45a, _h45b⟩
  have hxNotKernel :
      ¬ Section1.subgroupInKernel' (xChar (col j))
        ((P.subgroupOf Smax).subgroupOf (derivedSubgroup Smax)) :=
    hypothesis_13_1_selected_xChar_not_subgroupInKernel_early
      hSTypeP hNotation xChar h45a (col j) (hcol_ne j hj0 hj)
  have hSelectedMem : Section10.muColumn μsel (col j) ∈ Sfam := by
    have hWitness :
        ∃ θ : Section1.ClassFunction (derivedSubgroup Smax),
          Section1.IsIrreducibleCharacterOnGroup θ ∧
            ¬ Section1.subgroupInKernel' θ
              ((P.subgroupOf Smax).subgroupOf (derivedSubgroup Smax)) ∧
            Section10.muColumn μsel (col j) =
              Section1.inducedCF (derivedSubgroup Smax) θ := by
      refine ⟨xChar (col j), h45a.2.1 (col j), hxNotKernel, ?_⟩
      simpa [Section10.muColumn, Section4Scratch.piColumn] using
        (h45a.2.2 (col j)).symm
    apply (hSfamMem (Section10.muColumn μsel (col j))).2
    have transportWitness :
        ∀ (H H' K : Subgroup Smax), H = H' →
          (∃ θ : Section1.ClassFunction H,
            Section1.IsIrreducibleCharacterOnGroup θ ∧
              ¬ Section1.subgroupInKernel' θ (K.subgroupOf H) ∧
              Section10.muColumn μsel (col j) =
                Section1.inducedCF H θ) →
          ∃ θ : Section1.ClassFunction H',
            Section1.IsIrreducibleCharacterOnGroup θ ∧
              ¬ Section1.subgroupInKernel' θ (K.subgroupOf H') ∧
              Section10.muColumn μsel (col j) =
                Section1.inducedCF H' θ := by
      intro H H' K hHH' h
      subst H'
      exact h
    exact transportWitness
      (derivedSubgroup Smax)
      ((ambientDerivedSubgroup Smax).subgroupOf Smax)
      (P.subgroupOf Smax)
      (section12_ambientDerivedSubgroup_subgroupOf_eq
        (G := G) (E := Smax)).symm hWitness
  have hSelectedReducible :
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section10.muColumn μsel (col j)) :=
    hypothesis_13_1_muColumn_nonbase_not_irreducible_source
      hTypePDef hNotation (col j) (hcol_ne j hj0 hj)
  rcases hypothesis_13_1_typeP_reducibleFamilyMember_to_fitting
      hmin hcase hSTypeP hTTypeP Sfam hSnonker hSelectedMem
        hSelectedReducible with
    ⟨θ, hθirr, hθdegree, hθind⟩
  have hdegreeRows : ∀ i : I,
      Section1.degree (μsel i (col j)) =
        Section1.degree (μsel i0 (col j)) := by
    intro i
    exact
      Section10.degree_mu_eq_base_of_section10FourSixNotationSupportedData
        hNotation i (col j)
  have hdegreeColumn :
      Section1.degree (Section10.muColumn μsel (col j)) =
        (Fintype.card I : ℂ) * Section1.degree (μsel i0 (col j)) :=
    Section10.degree_muColumn_eq_card_mul_of_degree_eq hdegreeRows
  have hcardI : Fintype.card I = Nat.card W1 := by
    calc
      Fintype.card I = Fintype.card {i : ℕ // i < Nat.card W1} :=
        Fintype.card_congr eI.symm
      _ = Nat.card W1 := by
        simpa using Fintype.card_of_subtype (Finset.range (Nat.card W1))
          (by intro i; simp)
  have hbaseAlign : μ 0 j = μsel i0 (col j) := by
    have hzero := hAlign 0 (Nat.card_pos : 0 < Nat.card W1)
    simpa [hrow0] using hzero
  have hvisibleDegree :
      Section1.degree (μsum j) =
        (Nat.card W1 : ℂ) * Section1.degree (μ 0 j) := by
    calc
      Section1.degree (μsum j) =
          Section1.degree (Section10.muColumn μsel (col j)) := by rw [hcolumn]
      _ = (Fintype.card I : ℂ) * Section1.degree (μsel i0 (col j)) :=
        hdegreeColumn
      _ = (Nat.card W1 : ℂ) * Section1.degree (μ 0 j) := by
        rw [hcardI, hbaseAlign]
  exact ⟨by simpa [hcolumn] using hSelectedMem,
    ⟨θ, hθirr, hθdegree, hcolumn.symm.trans hθind⟩,
    hvisibleDegree⟩

private theorem hypothesis_13_1_muSum_zero_on_PU_nonP_muSum_supported_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            Section1.supportedOn (μsum j)
              (((P.subgroupOf Smax : Subgroup Smax) : Set Smax)) := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  rcases hypothesis_13_1_muSum_fittingData_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj with
    ⟨_hmem, ⟨θ, _hθirr, _hθdegree, hθind⟩, _hdegree⟩
  have hTypePDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  have hFitEq : section8FittingSubgroup Smax = P := by
    calc
      section8FittingSubgroup Smax = P ⊔ subgroupCentralizerIn U P :=
        Section8.theorem_8_5_a Smax P U W1 W2 hTypePDef
      _ = P := by rw [hCentralizerBot, sup_bot_eq]
  have hSuppFit :
      Section1.supportedOn (μsum j)
        ((((section8FittingSubgroup Smax).subgroupOf Smax : Subgroup Smax) :
          Set Smax)) := by
    haveI : ((section8FittingSubgroup Smax).subgroupOf Smax).Normal :=
      section8FittingSubgroup_normal_in Smax
    rw [hθind]
    exact Section10.inducedCF_supportedOn_subgroup
      ((section8FittingSubgroup Smax).subgroupOf Smax) θ
  rw [Section1.supportedOn_iff] at hSuppFit ⊢
  intro x hxNotP
  exact hSuppFit x (by
    intro hxFit
    apply hxNotP
    simpa [Subgroup.mem_subgroupOf, hFitEq] using hxFit)

public theorem hypothesis_13_1_muSum_inducedFrom_fitting_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∃ θ : Section1.ClassFunction
                ((section8FittingSubgroup Smax).subgroupOf Smax),
              Section1.IsIrreducibleCharacterOnGroup θ ∧
                μsum j = Section1.inducedCF
                  ((section8FittingSubgroup Smax).subgroupOf Smax) θ := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  rcases (hypothesis_13_1_muSum_fittingData_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj).2.1 with
    ⟨θ, hθirr, _hθdegree, hθind⟩
  exact ⟨θ, hθirr, hθind⟩


public theorem hypothesis_13_1_muSum_mem_sourceFamily
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 → μsum j ∈ Sfam := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  exact
    (hypothesis_13_1_muSum_fittingData_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj).1

private theorem hypothesis_13_1_typeP_card_W1_mul_join_index_eq_P_index
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    Nat.card W1 * Subgroup.index ((P ⊔ W1).subgroupOf Smax) =
      Subgroup.index (P.subgroupOf Smax) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup Smax
  rcases hSTypeP with ⟨hP, hCommon⟩
  have hCompDW1 : section12ComplementIn Smax D W1 := by
    simpa [D] using
      Section8.theorem_8_8_typeCommon_W1_complement (G := G) hCommon
  rcases hCommon with
    ⟨_hHallD, hPleD, _hCompPU, _hUnil, _hW1norm, _hW1cyc,
      _hW1card, _hPnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6,
      _hW2second⟩
  have hPleS : P ≤ Smax := hPleD.trans hCompDW1.1
  have hW1leS : W1 ≤ Smax := hCompDW1.2.1
  let H : Subgroup G := P ⊔ W1
  have hHleS : H ≤ Smax := sup_le hPleS hW1leS
  have hPsub_le_Hsub : P.subgroupOf Smax ≤ H.subgroupOf Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [H, Subgroup.mem_subgroupOf] using
      ((le_sup_left : P ≤ P ⊔ W1) hxP)
  have hPnormal : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hP
  have hP_H_normal : (P.subgroupOf H).Normal := by
    have hHleNormP : H ≤ Subgroup.normalizer (P : Set G) := by
      intro x hxH
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPleS).1 hPnormal
        (hHleS hxH)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (le_sup_left : P ≤ H)).2 hHleNormP
  have hCompPW1 : section12ComplementIn H P W1 := by
    refine ⟨le_sup_left, le_sup_right, rfl, ?_⟩
    rw [Subgroup.disjoint_def]
    intro x hxP hxW1
    exact hCompDW1.2.2.2.le_bot ⟨hPleD hxP, hxW1⟩
  have hPW1local :
      (P.subgroupOf H).IsComplement' (W1.subgroupOf H) :=
    Section12.section12ComplementIn_left_normal_isComplement'
      hCompPW1 hP_H_normal
  have hrel :
      (P.subgroupOf Smax).relIndex (H.subgroupOf Smax) = Nat.card W1 := by
    have hsub :
        (P.subgroupOf H).index =
          (P.subgroupOf Smax).relIndex (H.subgroupOf Smax) := by
      simpa [H, Subgroup.relIndex] using
        (Subgroup.relIndex_subgroupOf
          (H := P) (K := H) (L := Smax) hHleS).symm
    rw [← hsub]
    calc
      (P.subgroupOf H).index = Nat.card (W1.subgroupOf H) :=
        hPW1local.symm.index_eq_card
      _ = Nat.card W1 := natCard_subgroupOf_eq W1 H le_sup_right
  have hmul := Subgroup.relIndex_mul_index hPsub_le_Hsub
  simpa [H, hrel] using hmul

private theorem hypothesis_13_1_betaSupportSet_PU_identity_degree_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            Section1.degree (μ 0 j) =
              (Subgroup.index ((P ⊔ W1).subgroupOf Smax) : ℂ) := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  rcases hypothesis_13_1_muSum_fittingData_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj with
    ⟨_hmem, ⟨θ, _hθirr, hθdegree, hθind⟩, hcolumnDegree⟩
  have hTypePDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  have hFitEq : section8FittingSubgroup Smax = P := by
    calc
      section8FittingSubgroup Smax = P ⊔ subgroupCentralizerIn U P :=
        Section8.theorem_8_5_a Smax P U W1 W2 hTypePDef
      _ = P := by rw [hCentralizerBot, sup_bot_eq]
  have hsumDegree :
      Section1.degree (μsum j) = (P.subgroupOf Smax).index := by
    calc
      Section1.degree (μsum j) =
          ((section8FittingSubgroup Smax).subgroupOf Smax).index *
            Section1.degree θ := by
        rw [hθind, Section1.degree_inducedClassFunction]
      _ = ((section8FittingSubgroup Smax).subgroupOf Smax).index := by
        rw [hθdegree]
        simp
      _ = (P.subgroupOf Smax).index := by rw [hFitEq]
  have hindexNat :=
    hypothesis_13_1_typeP_card_W1_mul_join_index_eq_P_index hSTypeP
  have hindexComplex :
      (Nat.card W1 : ℂ) *
          (Subgroup.index ((P ⊔ W1).subgroupOf Smax) : ℂ) =
        (Subgroup.index (P.subgroupOf Smax) : ℂ) := by
    exact_mod_cast hindexNat
  have hmul :
      (Nat.card W1 : ℂ) * Section1.degree (μ 0 j) =
        (Nat.card W1 : ℂ) *
          (Subgroup.index ((P ⊔ W1).subgroupOf Smax) : ℂ) := by
    calc
      (Nat.card W1 : ℂ) * Section1.degree (μ 0 j) =
          Section1.degree (μsum j) := hcolumnDegree.symm
      _ = (Subgroup.index (P.subgroupOf Smax) : ℂ) := by
        exact_mod_cast hsumDegree
      _ = (Nat.card W1 : ℂ) *
          (Subgroup.index ((P ⊔ W1).subgroupOf Smax) : ℂ) :=
        hindexComplex.symm
  have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card W1).ne'
  exact mul_left_cancel₀ hW1ne hmul

private theorem hypothesis_13_1_muSum_zero_on_PU_nonP_seqInd_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) →
                (x : G) ∉ (P : Set G) →
                  μsum j x = 0 := by
  /-
  Checked induced-character support glue over the `seqInd_on` row-source
  boundary.
  -/
  classical
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxPU hxNotP
  have hμsumSupp :
      Section1.supportedOn (μsum j)
        (((P.subgroupOf Smax : Subgroup Smax) : Set Smax)) :=
    hypothesis_13_1_muSum_zero_on_PU_nonP_muSum_supported_source hmin hcase
        hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
        hFourSixS hFourSixT hCentralizerBot
        ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  have hxNotP' :
      x ∉ (((P.subgroupOf Smax : Subgroup Smax) : Set Smax)) := by
    intro hxP'
    exact hxNotP (by simpa [Subgroup.mem_subgroupOf] using hxP')
  exact (Section1.supportedOn_iff.mp hμsumSupp) x hxNotP'

private theorem hypothesis_13_1_mu_zero_on_PU_nonP_column_relation_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) →
                (x : G) ∉ (P : Set G) →
                  μ 0 j x = (Nat.card W1 : ℂ)⁻¹ * μsum j x ∧
                    μsum j x = 0 := by
  
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxPU hxNotP
  exact ⟨
    hypothesis_13_1_mu_zero_on_PU_nonP_restriction_source hmin hcase
      hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
      hFourSixS hFourSixT ω η μ ν μsum νsum δ δ' σ hnotation
      j hj0 hj x hxPU hxNotP,
    hypothesis_13_1_muSum_zero_on_PU_nonP_seqInd_source hmin hcase
      hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
      hFourSixS hFourSixT hCentralizerBot
      ω η μ ν μsum νsum δ δ' σ hnotation
      j hj0 hj x hxPU hxNotP⟩

private theorem hypothesis_13_1_mu_zero_on_PU_nonP_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) →
                (x : G) ∉ (P : Set G) →
                  μ 0 j x = 0 := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxPU hxNotP
  rcases
      hypothesis_13_1_mu_zero_on_PU_nonP_column_relation_source hmin hcase
        hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
        hFourSixS hFourSixT hCentralizerBot
        ω η μ ν μsum νsum δ δ' σ hnotation
        j hj0 hj x hxPU hxNotP with
    ⟨hμ, hμsum⟩
  rw [hμ, hμsum, mul_zero]

private theorem hypothesis_13_1_betaSupportSet_PU_identity_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) = 1 →
                (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                  (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                    μ 0 j) x = 0 := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hx1
  have hxS : x = 1 := by
    ext
    exact hx1
  have hInd :
      Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) x =
        (Subgroup.index ((P ⊔ W1).subgroupOf Smax) : ℂ) :=
    hypothesis_13_1_inducedPrincipal_identity_value
      ((P ⊔ W1).subgroupOf Smax) x hxS
  have hμdeg :
      Section1.degree (μ 0 j) =
        (Subgroup.index ((P ⊔ W1).subgroupOf Smax) : ℂ) :=
    hypothesis_13_1_betaSupportSet_PU_identity_degree_source hmin hcase
      hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
      hFourSixS hFourSixT hCentralizerBot
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  have hμx :
      μ 0 j x = (Subgroup.index ((P ⊔ W1).subgroupOf Smax) : ℂ) := by
    subst hxS
    simpa [Section1.degree_apply] using hμdeg
  simp [hInd, hμx]

private theorem hypothesis_13_1_betaSupportSet_PU_nonP_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) →
                (x : G) ∉ (P : Set G) →
                  (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                      μ 0 j) x = 0 := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxPU hxNotP
  have hxConj :
      x ∉ section16ConjugatesOfSetBySet
        (((P ⊔ W1).subgroupOf Smax : Subgroup Smax) : Set Smax) Set.univ :=
    hypothesis_13_1_PU_nonP_not_mem_PW1_conjugates_source hmin hcase hSTypeP
      x hxPU hxNotP
  have hInd :
      Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) x = 0 :=
    hypothesis_13_1_inducedCF_eq_zero_of_not_mem_conjugates
      ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) hxConj
  have hμ :
      μ 0 j x = 0 :=
    hypothesis_13_1_mu_zero_on_PU_nonP_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
      hCentralizerBot ω η μ ν μsum νsum δ δ' σ hnotation
      j hj0 hj x hxPU hxNotP
  simp [hInd, hμ]

private theorem hypothesis_13_1_betaSupportSet_PU_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) →
                (x : G) ∉ section16NonidentityElements (P : Set G) →
                  (x : G) ∉ section16ConjugatesOfSetBySet
                    ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
                    (Smax : Set G) →
                    (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                        μ 0 j) x = 0 := by
  
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxPU hxP _hxV
  by_cases hx1 : (x : G) = 1
  · exact
      hypothesis_13_1_betaSupportSet_PU_identity_s_side_source hmin hcase
        hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
        hFourSixS hFourSixT hCentralizerBot
        ω η μ ν μsum νsum δ δ' σ hnotation
        j hj0 hj x hx1
  · have hxNotP : (x : G) ∉ (P : Set G) := by
      intro hxPmem
      exact hxP ⟨hxPmem, hx1⟩
    exact
      hypothesis_13_1_betaSupportSet_PU_nonP_s_side_source hmin hcase
        hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
        hFourSixS hFourSixT hCentralizerBot
        ω η μ ν μsum νsum δ δ' σ hnotation
        j hj0 hj x hxPU hxNotP

private theorem hypothesis_13_1_section2_normalizesSet_subgroup_of_normal
    {L : Type*} [Group L]
    (K : Subgroup L) [K.Normal] (g : L) :
    Section2.normalizesSet (K : Set L) g := by
  intro x
  constructor
  · intro hx
    have hx' : g⁻¹ * (g * x * g⁻¹) * g ∈ K := by
      simpa [mul_assoc] using
        (show K.Normal from inferInstance).conj_mem (g * x * g⁻¹) hx g⁻¹
    simpa [Section2.conjBy, mul_assoc] using hx'
  · intro hx
    simpa [Section2.conjBy] using
      (show K.Normal from inferInstance).conj_mem x hx g

private theorem hypothesis_13_1_exists_centralizer_coset_conj_of_coprime
    {L : Type*} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal] (g : L)
    (hcop : Nat.Coprime (orderOf g) (Nat.card K))
    (y : K) :
    ∃ r u : K,
      (u : L) ∈ Section2.centralizerIn K g ∧
        (u : L) * g = (r : L)⁻¹ * ((y : L) * g) * (r : L) := by
  classical
  rcases Section2.proposition_2_1 g K
      (hypothesis_13_1_section2_normalizesSet_subgroup_of_normal K g)
      hcop with
    ⟨reps, _hcard, hreps, _hdisj, hcover⟩
  have hygCoset : (y : L) * g ∈ Section2.subgroupCosetByElement K g := by
    exact ⟨(y : L), y.2, rfl⟩
  have hygPiece :
      (y : L) * g ∈ {z | ∃ r ∈ reps, z ∈ Section2.conjugateCosetPiece K g r} := by
    simpa [hcover] using hygCoset
  rcases hygPiece with ⟨r, hr, hpiece⟩
  have hrK : r ∈ K := hreps r hr
  rcases hpiece with ⟨s, hs, hsEq⟩
  rcases hs with ⟨u, huCent, rfl⟩
  have huK : u ∈ K := (Subgroup.mem_inf.mp huCent).1
  refine ⟨⟨r, hrK⟩, ⟨u, huK⟩, huCent, ?_⟩
  simpa [Section2.conjBy, mul_assoc] using
    congrArg (fun t : L => r⁻¹ * t * r) hsEq.symm

private theorem hypothesis_13_1_betaSupportSet_outside_PU_hatW_partition_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    ∀ x : Smax,
      (x : G) ∉ ((P ⊔ U : Subgroup G) : Set G) →
        (x : G) ∈ section16ConjugatesOfSetBySet
            (section16HatW W1 W2) (Smax : Set G) ∨
          (x : G) ∈ section16ConjugatesOfSetBySet
            (section16NonidentityElements (W1 : Set G)) (Smax : Set G) := by
  /-
  Source PF `(13.18)` `PVSbeta`, outside-`P ⊔ U` coset-cover core:
  the local `PU`/`W1` partition and centralizer-coset partition put every
  outside element either in the Type-P `hat W` support or in the `W1#`
  class support.
  -/
  classical
  intro x hxNotPU
  let D : Subgroup G := ambientDerivedSubgroup Smax
  let Dsub : Subgroup Smax := D.subgroupOf Smax
  let W1sub : Subgroup Smax := W1.subgroupOf Smax
  have hTypePDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  rcases hTypePDef with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, hCompMW1, _hUleD, _hUnil,
      _hW1normU, hCompDU, _hPnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, hCentralizer, _hNormHatW⟩
  have hTypePDef' : Section8.typePDefinitionData Smax P U W1 W2 :=
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, hCompMW1, _hUleD, _hUnil,
      _hW1normU, hCompDU, _hPnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, hCentralizer, _hNormHatW⟩
  have hDleS : D ≤ Smax := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := Smax))
  have hW1leS : W1 ≤ Smax := hCompMW1.2.1
  have hDnorm : Dsub.Normal := by
    simpa [D, Dsub] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax)).2
  letI : Dsub.Normal := hDnorm
  have hsupTop : Dsub ⊔ W1sub = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := D) (A' := W1) (B := Smax) hDleS hW1leS]
    exact Subgroup.subgroupOf_eq_top.2 (by
      intro z hz
      rw [hCompMW1.2.2.1] at hz
      simpa [D] using hz)
  have hxTop : x ∈ Dsub ⊔ W1sub := by
    simp [hsupTop]
  rcases (Subgroup.mem_sup_of_normal_left (s := Dsub) (t := W1sub) (x := x)).1
      hxTop with
    ⟨d, hdDsub, w, hwW1sub, hdw⟩
  have hdD : (d : G) ∈ D := by
    simpa [Dsub, Subgroup.mem_subgroupOf] using hdDsub
  have hwW1 : (w : G) ∈ W1 := by
    simpa [W1sub, Subgroup.mem_subgroupOf] using hwW1sub
  have hPleD : P ≤ D := by
    simpa [D] using hCompDU.1
  have hw_ne : w ≠ 1 := by
    intro hw_one
    have hxD : (x : G) ∈ D := by
      have hx_eq_d : x = d := by
        simpa [hw_one] using hdw.symm
      simpa [hx_eq_d] using hdD
    have hxPU : (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G) := by
      simpa [D, hCompDU.2.2.1] using hxD
    exact hxNotPU hxPU
  have hw_neG : (w : G) ≠ 1 := by
    intro hwG
    exact hw_ne (Subtype.ext hwG)
  have hcopW1D :
      Nat.Coprime (Nat.card W1) (Nat.card D) :=
    Section10.typePDefinitionData_W1_card_coprime_ambientDerived hTypePDef'
  have hW1sub_card : Nat.card W1sub = Nat.card W1 := by
    simpa [W1sub] using
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := W1) (K := Smax) hW1leS).toEquiv
  have hDsub_card : Nat.card Dsub = Nat.card D := by
    simpa [Dsub] using
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := D) (K := Smax) hDleS).toEquiv
  have hcopW1subDsub :
      Nat.Coprime (Nat.card W1sub) (Nat.card Dsub) := by
    rw [hW1sub_card, hDsub_card]
    exact hcopW1D
  have horder_dvd : orderOf w ∣ Nat.card W1sub :=
    Subgroup.orderOf_dvd_natCard W1sub hwW1sub
  have hcopOrderDsub : Nat.Coprime (orderOf w) (Nat.card Dsub) :=
    Nat.Coprime.coprime_dvd_left horder_dvd hcopW1subDsub
  rcases
      hypothesis_13_1_exists_centralizer_coset_conj_of_coprime
        (K := Dsub) (g := w) hcopOrderDsub ⟨d, hdDsub⟩ with
    ⟨r, u, huCent, huConj⟩
  have huConj_x :
      (u : Smax) * w = (r : Smax)⁻¹ * x * (r : Smax) := by
    simpa [hdw] using huConj
  have hxConj :
      x = (r : Smax) * ((u : Smax) * w) * (r : Smax)⁻¹ := by
    calc
      x = (r : Smax) * ((r : Smax)⁻¹ * x * (r : Smax)) *
          (r : Smax)⁻¹ := by group
      _ = (r : Smax) * ((u : Smax) * w) * (r : Smax)⁻¹ := by
        rw [← huConj_x]
  by_cases hu_one : (u : Smax) = 1
  · right
    refine ⟨(w : G), ⟨hwW1, hw_neG⟩, (r : G), (r : Smax).property, ?_⟩
    have hxConjW : x = (r : Smax) * w * (r : Smax)⁻¹ := by
      simpa [hu_one] using hxConj
    exact congrArg Subtype.val hxConjW
  · left
    have huD : (u : G) ∈ D := by
      exact u.property
    have huElemCent : (u : Smax) ∈ Section2.elementCentralizer w :=
      (Subgroup.mem_inf.mp huCent).2
    have hcommS : w * (u : Smax) = (u : Smax) * w := by
      unfold Section2.elementCentralizer at huElemCent
      rw [Subgroup.mem_centralizer_iff] at huElemCent
      exact huElemCent w (by simp)
    have hcommG : (w : G) * (u : G) = (u : G) * (w : G) :=
      congrArg Subtype.val hcommS
    have huCentD : (u : G) ∈ elementCentralizerIn D (w : G) := by
      refine ⟨huD, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcommG.symm
    have huW2 : (u : G) ∈ W2 := by
      simpa [D, hCentralizer (w : G) hwW1 hw_neG] using huCentD
    have hu_neG : (u : G) ≠ 1 := by
      intro huG
      exact hu_one (Subtype.ext huG)
    have hW2leD : W2 ≤ D := by
      intro z hz
      exact hPleD ((hW2le hz).1)
    have hbaseHat :
        (((u : Smax) * w : Smax) : G) ∈ section16HatW W1 W2 := by
      refine ⟨?_, ?_⟩
      · exact (W1 ⊔ W2).mul_mem
          ((show W2 ≤ W1 ⊔ W2 from le_sup_right) huW2)
          ((show W1 ≤ W1 ⊔ W2 from le_sup_left) hwW1)
      · intro hmem
        rcases hmem with hbaseW1 | hbaseW2
        · have huW1 : (u : G) ∈ W1 := by
            have hmul :
                (((u : Smax) * w : Smax) : G) * (w : G)⁻¹ ∈ W1 :=
              W1.mul_mem hbaseW1 (W1.inv_mem hwW1)
            simpa [mul_assoc] using hmul
          have huBot : (u : G) ∈ (⊥ : Subgroup G) :=
            hCompMW1.2.2.2.le_bot ⟨huD, huW1⟩
          exact hu_neG (Subgroup.mem_bot.mp huBot)
        · have hwW2 : (w : G) ∈ W2 := by
            have hmul :
                (u : G)⁻¹ * (((u : Smax) * w : Smax) : G) ∈ W2 :=
              W2.mul_mem (W2.inv_mem huW2) hbaseW2
            simpa [mul_assoc] using hmul
          have hwD : (w : G) ∈ D := hW2leD hwW2
          have hwBot : (w : G) ∈ (⊥ : Subgroup G) :=
            hCompMW1.2.2.2.le_bot ⟨hwD, hwW1⟩
          exact hw_neG (Subgroup.mem_bot.mp hwBot)
    refine ⟨(((u : Smax) * w : Smax) : G), hbaseHat, (r : G),
      (r : Smax).property, ?_⟩
    exact congrArg Subtype.val hxConj

private theorem hypothesis_13_1_betaSupportSet_outside_PU_class_partition_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (_hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (_hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (_hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (_hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ x : Smax,
      (x : G) ∉ ((P ⊔ U : Subgroup G) : Set G) →
        (x : G) ∈ section16ConjugatesOfSetBySet
            ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (Smax : Set G) ∨
          (x : G) ∈ section16ConjugatesOfSetBySet
            (section16NonidentityElements (W1 : Set G)) (Smax : Set G) := by
  /-
  Checked display-set wrapper for the outside-`P ⊔ U` class partition:
  the source core is stated with the native Type-P `section16HatW W1 W2`,
  while the beta support statement displays the same set as `W \ (W1 ∪ W2)`.
  -/
  intro x hxNotPU
  have hcaseFull := hcase
  rcases hcase with
    ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSMF, _hTMF,
      _hSnotTypeI, _hTnotTypeI, _hSeq, _hTeq, _hSinf, _hTinf,
      _hSW2leSecond, _hTW1leSecond, _hST, _hCover, _hTypeII,
      _hSType, _hTType, _hAligned⟩
  rcases hprod with ⟨_hW1leW, _hW2leW, hWeq, _hdisj, _hcent⟩
  rcases
      hypothesis_13_1_betaSupportSet_outside_PU_hatW_partition_s_side_source
        hmin hcaseFull hSTypeP hTTypeP x hxNotPU with
    hxHat | hxW1
  · left
    rcases hxHat with ⟨z, hzHat, y, hyS, hxy⟩
    refine ⟨z, ?_, y, hyS, hxy⟩
    simpa [section16HatW, hWeq] using hzHat
  · exact Or.inr hxW1

private theorem hypothesis_13_1_betaSupportSet_outside_PU_classSupport_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ x : Smax,
      (x : G) ∉ ((P ⊔ U : Subgroup G) : Set G) →
        (x : G) ∉ section16ConjugatesOfSetBySet
          ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (Smax : Set G) →
          (x : G) ∈ section16ConjugatesOfSetBySet
            (section16NonidentityElements (W1 : Set G)) (Smax : Set G) := by
  /-
  Checked logic around the outside-`P ⊔ U` support step: a lower source
  partition gives either `V_S` membership or `W1#` class-support membership;
  the branch hypothesis excludes the first alternative.
  -/
  intro x hxNotPU hxV
  rcases
      hypothesis_13_1_betaSupportSet_outside_PU_class_partition_s_side_source
        hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
        hDadeS hDadeT hFourSixS hFourSixT x hxNotPU with
    hxHat | hxW1
  · exact False.elim (hxV hxHat)
  · exact hxW1

private theorem hypothesis_13_1_inducedPrincipal_W1_D_conjugator_mem_P_source
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 : Subgroup G}
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2) :
    ∀ x : Smax,
      (x : G) ∈ section16NonidentityElements (W1 : Set G) →
        ∀ d : Smax,
          (d : G) ∈ ambientDerivedSubgroup Smax →
            d * x * d⁻¹ ∈ ((P ⊔ W1).subgroupOf Smax : Subgroup Smax) →
              d ∈ (P.subgroupOf Smax : Subgroup Smax) := by
  /-
  Source PF `(13.18)` `gammaW1`, derived-component core: after the
  `Smax = Smax' ⋊ W1` decomposition, a derived-subgroup conjugator that
  sends an element of `W1#` into `P ⊔ W1` has trivial `U`-component, hence
  lies in `P`.
  -/
  classical
  intro x hxW1 d hdD hdConj
  let D : Subgroup G := ambientDerivedSubgroup Smax
  let H : Subgroup G := P ⊔ W1
  rcases hTypeP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, hCompMW1, _hUleD, _hUnil,
      hW1normU, hCompDU, _hPnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, hCentralizer, _hNormHatW⟩
  have hDleS : D ≤ Smax := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := Smax))
  have hPleD : P ≤ D := by
    simpa [D] using hCompDU.1
  have hUleD : U ≤ D := by
    simpa [D] using hCompDU.2.1
  have hPleS : P ≤ Smax := hPleD.trans hDleS
  have hPnormS : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hSleNormP : Smax ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleS).1 hPnormS
  have hW1leNormP : W1 ≤ Subgroup.normalizer (P : Set G) :=
    hCompMW1.2.1.trans hSleNormP
  have hUleNormP : U ≤ Subgroup.normalizer (P : Set G) :=
    hUleD.trans (hDleS.trans hSleNormP)
  have hPW1set : ((H : Set G)) = (W1 : Set G) * (P : Set G) := by
    simpa [H, sup_comm] using
      (Subgroup.coe_mul_of_left_le_normalizer_right W1 P hW1leNormP)
  have hPUset : ((D : Set G)) = (P : Set G) * (U : Set G) := by
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left P U hUleNormP
    simpa [D, hCompDU.2.2.1] using hmul
  have hdConjG : (d : G) * (x : G) * (d : G)⁻¹ ∈ H := by
    simpa [H, Subgroup.mem_subgroupOf] using hdConj
  have hdProd : (d : G) ∈ (P : Set G) * (U : Set G) := by
    rw [← hPUset]
    simpa [D] using hdD
  rcases hdProd with ⟨p, hpP, u, huU, hpu⟩
  have hpH : p ∈ H := by
    exact (show P ≤ H from le_sup_left) hpP
  have huConjH : u * (x : G) * u⁻¹ ∈ H := by
    have hmem : p⁻¹ * ((d : G) * (x : G) * (d : G)⁻¹) * p ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hpH) hdConjG) hpH
    have heq :
        p⁻¹ * ((d : G) * (x : G) * (d : G)⁻¹) * p =
          u * (x : G) * u⁻¹ := by
      calc
        p⁻¹ * ((d : G) * (x : G) * (d : G)⁻¹) * p =
            p⁻¹ * ((p * u) * (x : G) * (p * u)⁻¹) * p := by rw [← hpu]
        _ = u * (x : G) * u⁻¹ := by simp [mul_assoc]
    simpa [heq] using hmem
  have huConjProd : u * (x : G) * u⁻¹ ∈ (W1 : Set G) * (P : Set G) := by
    rw [← hPW1set]
    exact huConjH
  rcases huConjProd with ⟨w, hwW1, p', hp'P, hwp'⟩
  let p'' : G := w * p' * w⁻¹
  have hp''P : p'' ∈ P := by
    have hwNormP : w ∈ Subgroup.normalizer (P : Set G) := hW1leNormP hwW1
    simpa [p''] using (Subgroup.mem_normalizer_iff.mp hwNormP p').1 hp'P
  have hp''D : p'' ∈ D := hPleD hp''P
  have hux_eq : u * (x : G) * u⁻¹ = p'' * w := by
    calc
      u * (x : G) * u⁻¹ = w * p' := hwp'.symm
      _ = (w * p' * w⁻¹) * w := by simp [mul_assoc]
      _ = p'' * w := rfl
  let c : G := u * (x : G) * u⁻¹ * (x : G)⁻¹
  have hxNormU : (x : G) ∈ Subgroup.normalizer (U : Set G) :=
    (mem_subgroupNormalizerIn.mp (hW1normU hxW1.1)).1
  have hx_u_inv_U : (x : G) * u⁻¹ * (x : G)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hxNormU u⁻¹).1 (U.inv_mem huU)
  have hcU : c ∈ U := by
    simpa [c, mul_assoc] using U.mul_mem huU hx_u_inv_U
  have hcD : c ∈ D := hUleD hcU
  have hcx_eq : c * (x : G) = p'' * w := by
    calc
      c * (x : G) = u * (x : G) * u⁻¹ := by simp [c, mul_assoc]
      _ = p'' * w := hux_eq
  have hmix : p''⁻¹ * c = w * (x : G)⁻¹ := by
    calc
      p''⁻¹ * c = p''⁻¹ * (c * (x : G)) * (x : G)⁻¹ := by simp [mul_assoc]
      _ = p''⁻¹ * (p'' * w) * (x : G)⁻¹ := by rw [hcx_eq]
      _ = w * (x : G)⁻¹ := by simp
  have hmixD : p''⁻¹ * c ∈ D := D.mul_mem (D.inv_mem hp''D) hcD
  have hmixW1 : p''⁻¹ * c ∈ W1 := by
    rw [hmix]
    exact W1.mul_mem hwW1 (W1.inv_mem hxW1.1)
  have hmixOne : p''⁻¹ * c = 1 :=
    Subgroup.disjoint_def.mp hCompMW1.2.2.2 hmixD hmixW1
  have hc_eq_p'' : c = p'' := by
    simpa [mul_assoc] using congrArg (fun t : G => p'' * t) hmixOne
  have hcP : c ∈ P := by
    simpa [hc_eq_p''] using hp''P
  have hcOne : c = 1 :=
    Subgroup.disjoint_def.mp hCompDU.2.2.2 hcP hcU
  have huxu : u * (x : G) * u⁻¹ = (x : G) := by
    have h := congrArg (fun t : G => t * (x : G)) hcOne
    simpa [c, mul_assoc] using h
  have hcomm : u * (x : G) = (x : G) * u := by
    have h := congrArg (fun t : G => t * u) huxu
    simpa [mul_assoc] using h
  have huCent : u ∈ elementCentralizerIn D (x : G) := by
    refine ⟨hUleD huU, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have huW2 : u ∈ W2 := by
    simpa [D, hCentralizer (x : G) hxW1.1 hxW1.2] using huCent
  have huP : u ∈ P := (hW2le huW2).1
  have huOne : u = 1 :=
    Subgroup.disjoint_def.mp hCompDU.2.2.2 huP huU
  change (d : G) ∈ P
  have hd_eq_p : (d : G) = p := by
    simpa [huOne] using hpu.symm
  simpa [hd_eq_p] using hpP

private theorem hypothesis_13_1_inducedPrincipal_W1_conjugator_mem_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    ∀ x : Smax,
      (x : G) ∈ section16NonidentityElements (W1 : Set G) →
        ∀ y : Smax,
          y * x * y⁻¹ ∈ ((P ⊔ W1).subgroupOf Smax : Subgroup Smax) →
            y ∈ ((P ⊔ W1).subgroupOf Smax : Subgroup Smax) := by
  
  classical
  intro x hxW1 y hyConj
  let D : Subgroup G := ambientDerivedSubgroup Smax
  let H : Subgroup Smax := (P ⊔ W1).subgroupOf Smax
  let Dsub : Subgroup Smax := D.subgroupOf Smax
  let W1sub : Subgroup Smax := W1.subgroupOf Smax
  have hTypePDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  rcases hTypePDef with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hCompMW1, _hUleD, _hUnil,
      _hW1normU, _hCompDU, _hPnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormHatW⟩
  have hTypePDef' : Section8.typePDefinitionData Smax P U W1 W2 :=
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hCompMW1, _hUleD, _hUnil,
      _hW1normU, _hCompDU, _hPnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormHatW⟩
  have hDnorm : Dsub.Normal := by
    simpa [D, Dsub] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax)).2
  letI : Dsub.Normal := hDnorm
  have hDleS : D ≤ Smax := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := Smax))
  have hW1leS : W1 ≤ Smax := hCompMW1.2.1
  have hsupTop : Dsub ⊔ W1sub = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := D) (A' := W1) (B := Smax) hDleS hW1leS]
    exact Subgroup.subgroupOf_eq_top.2 (by
      intro z hz
      rw [hCompMW1.2.2.1] at hz
      simpa [D] using hz)
  have hyTop : y ∈ Dsub ⊔ W1sub := by
    simp [hsupTop]
  rcases (Subgroup.mem_sup_of_normal_left (s := Dsub) (t := W1sub) (x := y)).1
      hyTop with
    ⟨d, hdDsub, w, hwW1sub, hdyw⟩
  let x' : Smax := w * x * w⁻¹
  have hwW1 : (w : G) ∈ W1 := by
    simpa [W1sub, Subgroup.mem_subgroupOf] using hwW1sub
  have hx'W1 : (x' : G) ∈ section16NonidentityElements (W1 : Set G) := by
    refine ⟨?_, ?_⟩
    · exact W1.mul_mem (W1.mul_mem hwW1 hxW1.1) (W1.inv_mem hwW1)
    · intro hx'one
      exact hxW1.2 (by
        calc
          (x : G) = (w : G)⁻¹ * (x' : G) * (w : G) := by
            simp [x', mul_assoc]
          _ = 1 := by simp [hx'one])
  have hdConj : d * x' * d⁻¹ ∈ H := by
    have hrewrite : d * x' * d⁻¹ = y * x * y⁻¹ := by
      calc
        d * x' * d⁻¹ = d * (w * x * w⁻¹) * d⁻¹ := by rfl
        _ = (d * w) * x * (d * w)⁻¹ := by simp [mul_assoc]
        _ = y * x * y⁻¹ := by rw [hdyw]
    simpa [H, hrewrite] using hyConj
  have hdD : (d : G) ∈ D := by
    simpa [Dsub, Subgroup.mem_subgroupOf] using hdDsub
  have hdPsub : d ∈ (P.subgroupOf Smax : Subgroup Smax) :=
    hypothesis_13_1_inducedPrincipal_W1_D_conjugator_mem_P_source
      hTypePDef' x' hx'W1 d hdD hdConj
  have hdH : d ∈ H := by
    change (d : G) ∈ P ⊔ W1
    exact (show P ≤ P ⊔ W1 from le_sup_left)
      (by simpa [Subgroup.mem_subgroupOf] using hdPsub)
  have hwH : w ∈ H := by
    change (w : G) ∈ P ⊔ W1
    exact (show W1 ≤ P ⊔ W1 from le_sup_right) hwW1
  have hmulH : d * w ∈ H := H.mul_mem hdH hwH
  simpa [hdyw] using hmulH

private theorem hypothesis_13_1_inducedPrincipal_W1_conjugator_card_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    ∀ x : Smax,
      (x : G) ∈ section16NonidentityElements (W1 : Set G) →
        Nat.card {y : Smax //
          y * x * y⁻¹ ∈ ((P ⊔ W1).subgroupOf Smax : Subgroup Smax)} =
            Nat.card ((P ⊔ W1).subgroupOf Smax) := by
  /-
  Checked cardinality wrapper around the quotient-TI core: the hard source
  step identifies the conjugator predicate with membership in `P ⊔ W1`.
  -/
  intro x hxW1
  classical
  let H : Subgroup Smax := (P ⊔ W1).subgroupOf Smax
  have hxH : x ∈ H := by
    change (x : G) ∈ P ⊔ W1
    exact (show W1 ≤ P ⊔ W1 from le_sup_right) hxW1.1
  have hiff : ∀ y : Smax, y * x * y⁻¹ ∈ H ↔ y ∈ H := by
    intro y
    constructor
    · exact
        hypothesis_13_1_inducedPrincipal_W1_conjugator_mem_source
          hmin hcase hSTypeP x hxW1 y
    · intro hyH
      exact H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH)
  let e : {y : Smax // y * x * y⁻¹ ∈ H} ≃ H := {
    toFun := fun y => ⟨y, (hiff y).1 y.property⟩
    invFun := fun y => ⟨y, (hiff y).2 y.property⟩
    left_inv := by
      intro y
      ext
      rfl
    right_inv := by
      intro y
      ext
      rfl }
  exact Nat.card_congr e

private theorem hypothesis_13_1_inducedPrincipal_W1_representative_value_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (_hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (_hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (_hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (_hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ section16NonidentityElements (W1 : Set G) →
                Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                  (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) x = 1 := by
  /-
  Checked counting wrapper for the representative induced-principal value on
  `W1#`; the remaining source input is the exact `gammaW1` conjugator count.
  -/
  intro _ω _η _μ _ν _μsum _νsum _δ _δ' _σ _hnotation _j _hj0 _hj x hxW1
  exact
    hypothesis_13_1_inducedCF_principal_eq_one_of_conjugator_card
      ((P ⊔ W1).subgroupOf Smax) x
      (hypothesis_13_1_inducedPrincipal_W1_conjugator_card_source
        hmin hcase hSTypeP x hxW1)

private theorem hypothesis_13_1_typePFourSixBaseRowW1Value_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U : Subgroup G}
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (hω : hypothesis_13_1_omegaNotationData W W1 W2
      (Nat.card W2) (Nat.card W1) ω)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS) :
    ∃ (χ : ℕ → ℕ → Section1.ClassFunction Smax)
      (δ : ℕ → ℤ)
      (Wsel : Subgroup Smax)
      (_ωsel : ℕ → ℕ → Section1.ClassFunction Wsel)
      (_σsel : Section1.ClassFunction Wsel →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω hω τS
          χ δ Wsel _ωsel _σsel ∧
        ∀ j, 0 < j → j < Nat.card W2 →
          ∀ x : Smax,
            (x : G) ∈ section16NonidentityElements (W1 : Set G) →
              χ 0 j x = ((δ j : ℤ) : ℂ) := by
  classical
  rcases hcase with
    ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSMF, _hTMF,
      _hSnotTypeI, _hTnotTypeI, _hSeq, _hTeq, _hSinf, _hTinf,
      _hSW2leSecond, _hTW1leSecond, _hST, _hCover, _hTypeII,
      _hSType, _hTType, _hAligned⟩
  rcases hprod with ⟨hW1leW, _hW2leW, hWeq, hdisj, _hcent⟩
  rcases hFourSixS with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hNotation, _hSigmaAgree, ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      hSTypeP ω hω τS Wsec A A0 i0 j0 μsel δSign ωsec σsec hNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, _hcol_inj, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport⟩
  have hNotationFull := hNotation
  rcases hNotationFull with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource10,
      hWsec_eq, _hA0eq, _h46, _hωsecData, _hIso, _hVirt, _hPrin,
      _hσAgreeCyc, _h45, _h48, _hTauIso, hFull⟩
  subst Wsec
  rcases hFull with ⟨_σM, _xCharD, _H_A, _H_A0, hSupported46, _hGalois⟩
  rcases hSupported46 with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨hωsec, _h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  let χ : ℕ → ℕ → Section1.ClassFunction Smax := fun i j => μsel (row i) (col j)
  let δ : ℕ → ℤ := fun j => δSign (col j)
  let ωselN : ℕ → ℕ →
      Section1.ClassFunction ((W1 ⊔ W2 : Subgroup G).subgroupOf Smax) :=
    fun i j => ωsec (row i) (col j)
  have hSelected :
      hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω hω τS
        χ δ ((W1 ⊔ W2 : Subgroup G).subgroupOf Smax) ωselN σsec :=
    hypothesis_13_1_selectedTypePFourSixTableData_of_package
      hSTypeP ω hω τS hNotation row col hrow0 hcol0 hcol_ne hrow_inj
      hrow_surj hcol_surj hIndTransport hExactTransport
  refine ⟨χ, δ, (W1 ⊔ W2 : Subgroup G).subgroupOf Smax, ωselN, σsec,
    hSelected, ?_⟩
  intro j hj0 hj x hxW1
  rcases hxW1 with ⟨hxW1mem, hxne⟩
  have hxW : (x : G) ∈ W := hW1leW hxW1mem
  have hxWsupG : (x : G) ∈ (W1 ⊔ W2 : Subgroup G) := by
    simpa [hWeq] using hxW
  have hxWsel : x ∈ ((W1 ⊔ W2 : Subgroup G).subgroupOf Smax : Subgroup Smax) := by
    simpa [Subgroup.mem_subgroupOf] using hxWsupG
  have hxnotW2G : (x : G) ∉ W2 := by
    intro hxW2
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hdisj hxW1mem hxW2
    exact hxne (by simpa using hxBot)
  have hxnotW2 :
      x ∉ ((W2.subgroupOf Smax : Subgroup Smax) : Set Smax) := by
    intro hxW2
    exact hxnotW2G (by simpa [Subgroup.mem_subgroupOf] using hxW2)
  let xWsel : (W1 ⊔ W2 : Subgroup G).subgroupOf Smax := ⟨x, hxWsel⟩
  let xW1 :
      (W1.subgroupOf Smax).subgroupOf
        ((W1 ⊔ W2 : Subgroup G).subgroupOf Smax) :=
    ⟨xWsel, by simpa [xWsel, Subgroup.mem_subgroupOf] using hxW1mem⟩
  have hωone : ωsec i0 (col j) xWsel = 1 := by
    have hker := hωsec.right_kernel (col j) xW1
    have hdeg := hωsec.degree_one i0 (col j)
    simpa [xW1, hdeg] using hker
  have h43cValue := h43c.1 i0 (col j) x ⟨hxWsel, hxnotW2⟩
  calc
    χ 0 j x = μsel i0 (col j) x := by
      simp [χ, hrow0]
    _ = (((δSign (col j) : ℤ) : ℂ) * ωsec i0 (col j) xWsel) := by
      simpa [xWsel] using h43cValue
    _ = ((δ j : ℤ) : ℂ) := by
      simp [δ, hωone]

private theorem hypothesis_13_1_int_sign_eq_one_of_mod_dvd
    {q : ℕ} {d : ℤ}
    (hq2 : 2 < q)
    (hsign : d = 1 ∨ d = -1)
    (hmod : (q : ℤ) ∣ d - 1) :
    d = 1 := by
  rcases hsign with h | h
  · exact h
  · exfalso
    subst d
    norm_num at hmod
    have hmodNat : q ∣ 2 := by
      exact_mod_cast hmod
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hmodNat
    omega


private theorem hypothesis_13_1_W1_card_gt_two_of_case_b
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q) :
    2 < Nat.card W1 := by
  classical
  rcases hcase with
    ⟨_hprod, _hcyc, hW1ne, _hW2ne, _hnorm, _hrest⟩
  have hodd : Odd (Nat.card W1) :=
    Odd.of_dvd_nat hmin.odd_order (Subgroup.card_subgroup_dvd_card W1)
  have hcard_ne_one : Nat.card W1 ≠ 1 := by
    intro hcard
    exact hW1ne ((Subgroup.card_eq_one (H := W1)).mp hcard)
  have hpos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
  rcases hodd with ⟨k, hk⟩
  omega

private theorem
    hypothesis_13_1_le_normalizer_subgroupCentralizerIn_of_le_normalizers
    {G : Type u} [Group G]
    {X U P : Subgroup G}
    (hXnormU : X ≤ Subgroup.normalizer (U : Set G))
    (hXnormP : X ≤ Subgroup.normalizer (P : Set G)) :
    X ≤ Subgroup.normalizer ((subgroupCentralizerIn U P : Subgroup G) : Set G) := by
  have hXnormCentralizer :
      X ≤ Subgroup.normalizer
        ((Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro p hp
      have hp' : n⁻¹ * p * n ∈ P :=
        (Subgroup.mem_normalizer_iff''.mp (hXnormP hn) p).1 hp
      have hcomm : (n⁻¹ * p * n) * c = c * (n⁻¹ * p * n) :=
        hc (n⁻¹ * p * n) hp'
      calc
        p * (n * c * n⁻¹) = n * ((n⁻¹ * p * n) * c) * n⁻¹ := by group
        _ = n * (c * (n⁻¹ * p * n)) * n⁻¹ := by rw [hcomm]
        _ = (n * c * n⁻¹) * p := by group
    · intro hc
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro p hp
      have hp' : n * p * n⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hXnormP hn) p).1 hp
      have hcomm :
          (n * p * n⁻¹) * (n * c * n⁻¹) =
            (n * c * n⁻¹) * (n * p * n⁻¹) :=
        hc (n * p * n⁻¹) hp'
      calc
        p * c = n⁻¹ * ((n * p * n⁻¹) * (n * c * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * c * n⁻¹) * (n * p * n⁻¹)) * n := by rw [hcomm]
        _ = c * p := by group
  intro x hx
  have hxinf :
      x ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer
          ((Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    ⟨hXnormU hx, hXnormCentralizer hx⟩
  simpa [subgroupCentralizerIn] using
    (Subgroup.inf_normalizer_le_normalizer_inf (G := G)
      (H := U) (K := Subgroup.centralizer (P : Set G)) hxinf)

private theorem hypothesis_13_1_fittingSubgroup_index_eq_card_W1_mul_quotient
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G} {ubar : ℕ}
    (hPDef : Section8.typePDefinitionData Smax P U W1 W2)
    (h92 : Section9.hypothesis_9_2_statement Smax P U W1 W2 (Nat.card W1))
    (hC : C = subgroupCentralizerIn U P)
    (hBarU : Section9.quotientBarUCardinality U C ubar) :
    ((section8FittingSubgroup Smax).subgroupOf Smax).index =
      Nat.card W1 * ubar := by
  have hFitEq : section8FittingSubgroup Smax = P ⊔ C := by
    calc
      section8FittingSubgroup Smax = P ⊔ subgroupCentralizerIn U P :=
        Section8.theorem_8_5_a Smax P U W1 W2 hPDef
      _ = P ⊔ C := by rw [← hC]
  rw [hFitEq]
  exact
    Section9.HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9
      Smax P U W1 W2 C (Nat.card W1) ubar h92 hBarU

private theorem hypothesis_13_1_W1_card_dvd_quotient_sub_one
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G} {ubar : ℕ}
    (h92 : Section9.hypothesis_9_2_statement Smax P U W1 W2 (Nat.card W1))
    (hC : C = subgroupCentralizerIn U P)
    (hBarU : Section9.quotientBarUCardinality U C ubar) :
    Nat.card W1 ∣ ubar - 1 := by
  classical
  rcases hBarU with ⟨hCU, hnormal, hcardBarU⟩
  have hPDef := h92.typePDefinitionData
  rcases hPDef with
    ⟨hPF, _hW1cyc, _hW1ne, hW1hall, _hMcomp, _hUleD, _hUnil,
      hW1normUSource, _hDerComp, _hPnotcyc, _hSecond, _hFit,
      _hFitLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNorm⟩
  have hW1normU : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1normUSource hw)).1
  rcases hPF with
    ⟨⟨hPS, hPnormalS, _hPnil, _hPHallS⟩, _hPmax⟩
  have hSleNormP : Smax ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPS).1 hPnormalS
  have hW1normP : W1 ≤ Subgroup.normalizer (P : Set G) :=
    hW1hall.1.trans hSleNormP
  have hW1normC : W1 ≤ Subgroup.normalizer (C : Set G) := by
    rw [hC]
    exact
      hypothesis_13_1_le_normalizer_subgroupCentralizerIn_of_le_normalizers
        hW1normU hW1normP
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : (C.subgroupOf U).Normal := hnormal
  have hCinv : IsInvariant W1 U (C.subgroupOf U) :=
    isInvariant_subgroupOf_of_le_normalizer hW1normU hW1normC hCU
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  letI : MulAction.QuotientAction W1 (C.subgroupOf U) :=
    quotientAction_of_isInvariant (A := W1) (C.subgroupOf U) hCinv
  have hfixBot : fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) = ⊥ :=
    Section9.theorem_9_7_fixedPointSubgroup_W1_barU_eq_bot_of_isInvariant_sec9
      h92 hnormal hW1normU hCinv
  have hprime : Nat.Prime (Nat.card W1) :=
    Section9.nat_card_W1_prime_of_hypothesis_9_2_sec9
      Smax P U W1 W2 h92
  letI : Fact (Nat.Prime (Nat.card W1)) := ⟨hprime⟩
  have hfree :
      ∀ a : W1, a ≠ 1 →
        ∀ x : U ⧸ C.subgroupOf U, a • x = x → x = 1 := by
    intro a ha x hax
    have hxfix : x ∈ fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) := by
      change ∀ b : W1, b • x = x
      intro b
      have hbz : b ∈ Subgroup.zpowers a :=
        mem_zpowers_of_prime_card (G := W1) (p := Nat.card W1) rfl
          (g := a) (g' := b) ha
      rcases Subgroup.mem_zpowers_iff.mp hbz with ⟨k, hk⟩
      have hxfixa : x ∈ MulAction.fixedBy (U ⧸ C.subgroupOf U) a := by
        rw [MulAction.mem_fixedBy]
        exact hax
      have hxpow := MulAction.mem_fixedBy_zpow hxfixa k
      rw [MulAction.mem_fixedBy] at hxpow
      simpa [hk] using hxpow
    have hxbot : x ∈ (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
      simpa [hfixBot] using hxfix
    simpa using hxbot
  have hdvd : Nat.card W1 ∣ Nat.card (U ⧸ C.subgroupOf U) - 1 :=
    Section6.natCard_actor_dvd_group_card_sub_one hfree
  rw [hcardBarU] at hdvd
  exact hdvd

private theorem hypothesis_13_1_naturalBaseRowSignModOne_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            (Nat.card W1 : ℤ) ∣ δ j - 1 := by
  classical
  letI : IsMinCE G := hmin
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  have hPDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  have hPDefForNormalizer := hPDef
  rcases hPDefForNormalizer with
    ⟨hPF, _hW1cyc, _hW1ne, hW1hall, _hMcomp, hUleD, _hUnil,
      _hW1normUSource, _hDerComp, _hPnotcyc, _hSecond, _hFit,
      _hFitLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNorm⟩
  rcases hPF with
    ⟨⟨hPS, hPnormalS, _hPnil, _hPHallS⟩, _hPmax⟩
  have hSleNormP : Smax ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPS).1 hPnormalS
  have hUnormP : U ≤ Subgroup.normalizer (P : Set G) :=
    hUleD.trans (section12_ambientDerivedSubgroup_le.trans hSleNormP)
  let C : Subgroup G := subgroupCentralizerIn U P
  have hCU : C ≤ U := by
    dsimp [C]
    exact inf_le_left
  have hUnormC : U ≤ Subgroup.normalizer (C : Set G) := by
    dsimp [C]
    exact
      hypothesis_13_1_le_normalizer_subgroupCentralizerIn_of_le_normalizers
        Subgroup.le_normalizer hUnormP
  have hnormal : (C.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCU).2 hUnormC
  letI : (C.subgroupOf U).Normal := hnormal
  let ubar : ℕ := Nat.card (U ⧸ C.subgroupOf U)
  have hBarU : Section9.quotientBarUCardinality U C ubar :=
    ⟨hCU, hnormal, rfl⟩
  have h92 : Section9.hypothesis_9_2_statement
      Smax P U W1 W2 (Nat.card W1) :=
    hypothesis_13_1_hypothesis_9_2_of_case_typeP hmin hcase hSTypeP
  have hFitIndex :
      ((section8FittingSubgroup Smax).subgroupOf Smax).index =
        Nat.card W1 * ubar :=
    hypothesis_13_1_fittingSubgroup_index_eq_card_W1_mul_quotient
      hPDef h92 rfl hBarU
  have hW1dvdUbar : Nat.card W1 ∣ ubar - 1 :=
    hypothesis_13_1_W1_card_dvd_quotient_sub_one h92 rfl hBarU
  rcases hypothesis_13_1_muSum_fittingData_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj with
    ⟨_hMuSumMem, ⟨θ, _hθirr, hθdegree, hθind⟩, hMuSumDegree⟩
  have hDegreeMuSum :
      Section1.degree (μsum j) =
        (Nat.card W1 : ℂ) * (ubar : ℂ) := by
    rw [hθind, Section1.degree_inducedClassFunction, hθdegree, hFitIndex]
    norm_num [Nat.cast_mul]
  have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := W1)).ne'
  have hDegreeMuZero : Section1.degree (μ 0 j) = (ubar : ℂ) := by
    apply mul_left_cancel₀ hW1ne
    calc
      (Nat.card W1 : ℂ) * Section1.degree (μ 0 j) =
          Section1.degree (μsum j) := hMuSumDegree.symm
      _ = (Nat.card W1 : ℂ) * (ubar : ℂ) := hDegreeMuSum
  have hω : hypothesis_13_1_omegaNotationData W W1 W2
      (Nat.card W2) (Nat.card W1) ω := hnotation.1
  have hFourSixSSelected := hFourSixS
  rcases hFourSixSSelected with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hNotation, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      hSTypeP ω hω τS Wsec A A0 i0 j0 μsel δSign ωsec σsec hNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, _hcol_inj, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport⟩
  let χ : ℕ → ℕ → Section1.ClassFunction Smax :=
    fun i k => μsel (row i) (col k)
  let δsel : ℕ → ℤ := fun k => δSign (col k)
  let ωsel : ℕ → ℕ → Section1.ClassFunction Wsec :=
    fun i k => ωsec (row i) (col k)
  have hSelected :
      hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω hω τS
        χ δsel Wsec ωsel σsec :=
    hypothesis_13_1_selectedTypePFourSixTableData_of_package
      hSTypeP ω hω τS hNotation row col hrow0 hcol0 hcol_ne hrow_inj
      hrow_surj hcol_surj hIndTransport hExactTransport
  have hW1pos : 0 < Nat.card W1 := Nat.card_pos
  rcases
      hypothesis_13_1_dadeDifferencePointwiseVisibleAlignment_s_side_source
        hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
        hDadeS hDadeT hFourSixS hFourSixT
        ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsec ωsel σsec
        hSelected 0 j hW1pos hj0 hj with
    ⟨hMuAlign, hDeltaAlign, _hSigmaAlign⟩
  have hSelectedDegree :
      Section1.degree (μsel i0 (col j)) = (ubar : ℂ) := by
    calc
      Section1.degree (μsel i0 (col j)) =
          Section1.degree (χ 0 j) := by simp [χ, hrow0]
      _ = Section1.degree (μ 0 j) :=
        congrArg Section1.degree hMuAlign.symm
      _ = (ubar : ℂ) := hDegreeMuZero
  have hNotationFull := hNotation
  rcases hNotationFull with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource10,
      _hWsecEq, _hA0eq, _h46, _hωsecData, _hIso, _hVirt, _hPrin,
      _hσAgreeCyc, _h45, _h48, _hTauIso, hFull⟩
  rcases hFull with
    ⟨_σM, _xCharD, _H_A, _H_A0, hSupported46, _hGalois⟩
  rcases hSupported46 with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨_hωsec, _h43b, _h43c, h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  rcases h43d i0 (col j) with ⟨a, h43dEq⟩
  have hW1cardSub : Nat.card (W1.subgroupOf Smax) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 Smax hW1hall.1
  have hEqC :
      (ubar : ℂ) = ((δSign (col j) : ℤ) : ℂ) +
        ((a : ℂ) * (Nat.card W1 : ℂ)) := by
    calc
      (ubar : ℂ) = Section1.degree (μsel i0 (col j)) :=
        hSelectedDegree.symm
      _ = ((δSign (col j) : ℤ) : ℂ) +
          ((a : ℂ) * (Nat.card (W1.subgroupOf Smax) : ℂ)) := h43dEq
      _ = ((δSign (col j) : ℤ) : ℂ) +
          ((a : ℂ) * (Nat.card W1 : ℂ)) := by rw [hW1cardSub]
  have hEqZ :
      (ubar : ℤ) = δSign (col j) + a * (Nat.card W1 : ℤ) := by
    exact_mod_cast hEqC
  have hW1dvdUbarZCast :
      (Nat.card W1 : ℤ) ∣ ((ubar - 1 : ℕ) : ℤ) := by
    exact_mod_cast hW1dvdUbar
  have hubarPos : 0 < ubar := by
    dsimp [ubar]
    exact Nat.card_pos
  have hW1dvdUbarZ :
      (Nat.card W1 : ℤ) ∣ (ubar : ℤ) - 1 := by
    simpa only [Nat.cast_sub hubarPos, Nat.cast_one] using hW1dvdUbarZCast
  have hSelectedMod :
      (Nat.card W1 : ℤ) ∣ δSign (col j) - 1 := by
    rcases hW1dvdUbarZ with ⟨b, hb⟩
    refine ⟨b - a, ?_⟩
    calc
      δSign (col j) - 1 =
          ((ubar : ℤ) - 1) - a * (Nat.card W1 : ℤ) := by
        nlinarith [hEqZ]
      _ = (Nat.card W1 : ℤ) * b - a * (Nat.card W1 : ℤ) := by
        rw [hb]
      _ = (Nat.card W1 : ℤ) * (b - a) := by ring
  have hSelectedModNatural :
      (Nat.card W1 : ℤ) ∣ δsel j - 1 := by
    simpa [δsel] using hSelectedMod
  rw [hDeltaAlign]
  exact hSelectedModNatural

private theorem hypothesis_13_1_naturalBaseRowSignOne_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 → δ j = 1 := by
  /-
  Checked final sign selection for PF `(13.3)(c)`: the visible notation
  supplies `δ_j = ±1`, while the source congruence rules out the negative
  sign because the relevant column factor has order greater than `2`.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  have hsign : δ j = 1 ∨ δ j = -1 := hnotation.2.2.2.1 j hj
  have hW1_gt_two : 2 < Nat.card W1 :=
    hypothesis_13_1_W1_card_gt_two_of_case_b hmin hcase
  have hmod : (Nat.card W1 : ℤ) ∣ δ j - 1 :=
    hypothesis_13_1_naturalBaseRowSignModOne_source hmin hcase hSTypeP
      hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
      hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  exact hypothesis_13_1_int_sign_eq_one_of_mod_dvd hW1_gt_two hsign hmod

private theorem hypothesis_13_1_naturalBaseSignZero_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax : Subgroup G}
    {p q : ℕ}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation : hypothesis_13_1_characterNotationDataFor
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ) :
    δ 0 = 1 := by
  rcases hnotation with
    ⟨hω, _hσ, _hη, hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, hbaseS, _hbaseT, _hμzeroDegree, _hνzeroDegree⟩
  rcases hω with ⟨_h31, hqpos, hppos, _ωFin, _hωFin, _hωNat⟩
  rcases hδ 0 hppos with hδ0 | hδ0
  · exact hδ0
  · rcases Section10.exists_pos_nat_degree_of_irreducible_character
        (hμirr 0 0 hqpos hppos) with
      ⟨n, hnpos, hdegree⟩
    have hbaseAtOne := congrFun hbaseS (1 : Smax)
    change (((δ 0 : ℤ) : ℂ) * Section1.degree (μ 0 0)) = 1 at hbaseAtOne
    rw [hδ0, hdegree] at hbaseAtOne
    have hreal := congrArg Complex.re hbaseAtOne
    norm_num at hreal
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    linarith


public theorem hypothesis_13_1_signNormalizationFor_of_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
            ω η μ ν μsum νsum δ δ' σ →
          theorem_13_3_signNormalizationFor p q δ δ' := by
  rcases hsource with
    ⟨_hcaseSource, _hSTypePSource, _hTTypePSource, hp, hq, _hC, _hD, _hc, _hd,
      _hU, _hV,
      hSnonker, hTnonker, hDadeS, hDadeT, _hnotationData,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hmin, hFourSixS, hFourSixT⟩
  subst p
  subst q
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  have hnotationSwap :
      hypothesis_13_1_characterNotationDataFor Tmax Smax W W2 W1
        (Nat.card W1) (Nat.card W2)
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ :=
    hypothesis_13_1_characterNotationDataFor_swap_local hnotation
  constructor
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      exact hypothesis_13_1_naturalBaseSignZero_source hnotation
    · exact
        hypothesis_13_1_naturalBaseRowSignOne_source hmin hcase hSTypeP
          hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
          hFourSixS hFourSixT ω η μ ν μsum νsum δ δ' σ hnotation
          j (Nat.pos_of_ne_zero hj0) hj
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      exact hypothesis_13_1_naturalBaseSignZero_source hnotationSwap
    · exact
        hypothesis_13_1_naturalBaseRowSignOne_source hmin
          (hypothesis_13_1_case_b_data_swap hcase) hTTypeP hSTypeP
          Tfam Sfam τT τS hTnonker hSnonker hDadeT hDadeS
          hFourSixT hFourSixS
          (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
          (fun i j => μ j i) νsum μsum δ' δ σ hnotationSwap
          i (Nat.pos_of_ne_zero hi0) hi

private theorem hypothesis_13_1_mu_zero_row_W1_representative_value_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ section16NonidentityElements (W1 : Set G) →
                μ 0 j x = 1 := by
  /-
  Checked glue for PF `(13.18)` `PVSbeta`, representative zero-row value on
  `W1#`: selected `(4.6)` gives the value `1`, and the existing pointwise
  visible-alignment source transfers it to the visible `μ`.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxW1
  have hω : hypothesis_13_1_omegaNotationData W W1 W2
      (Nat.card W2) (Nat.card W1) ω := hnotation.1
  rcases
      hypothesis_13_1_typePFourSixBaseRowW1Value_source
        hcase hSTypeP ω hω τS hFourSixS with
    ⟨χ, δsel, Wsel, ωsel, σsel, hSelected, hχW1⟩
  have hSignOne :=
    hypothesis_13_1_naturalBaseRowSignOne_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation
  have hAlign :=
    hypothesis_13_1_dadeDifferencePointwiseVisibleAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation χ δsel Wsel ωsel σsel
      hSelected
  have hrow0lt : 0 < Nat.card W1 := Nat.card_pos (α := W1)
  rcases hAlign 0 j hrow0lt hj0 hj with ⟨hμ, hδ, _hσ⟩
  have hδone : δ j = 1 := hSignOne j hj0 hj
  calc
    μ 0 j x = χ 0 j x := by rw [hμ]
    _ = ((δsel j : ℤ) : ℂ) := hχW1 j hj0 hj x hxW1
    _ = 1 := by
      rw [← hδ, hδone]
      norm_num

private theorem hypothesis_13_1_betaSupportSet_W1_representative_value_eq_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ section16NonidentityElements (W1 : Set G) →
                Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                  (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) x =
                    μ 0 j x := by
  /-
  Checked equality wrapper for the `W1#` representative step: both sides
  have source value `1`.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxW1
  have hInd :
      Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) x = 1 :=
    hypothesis_13_1_inducedPrincipal_W1_representative_value_source hmin hcase
      hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
      hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxW1
  have hμ : μ 0 j x = 1 :=
    hypothesis_13_1_mu_zero_row_W1_representative_value_source hmin hcase
      hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
      hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxW1
  rw [hInd, hμ]

private theorem hypothesis_13_1_betaSupportSet_W1_representative_zero_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ section16NonidentityElements (W1 : Set G) →
                (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                  (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                    μ 0 j) x = 0 := by
  /-
  Checked arithmetic wrapper for the `W1#` representative step: after the
  source value equality, the beta difference vanishes pointwise.
  -/
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxW1
  have hval :
      Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
        (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) x =
          μ 0 j x :=
    hypothesis_13_1_betaSupportSet_W1_representative_value_eq_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS
      hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxW1
  change
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) x -
        μ 0 j x = 0
  rw [hval]
  simp

private theorem hypothesis_13_1_betaSupportSet_W1_classSupport_zero_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∈ section16ConjugatesOfSetBySet
                (section16NonidentityElements (W1 : Set G)) (Smax : Set G) →
                (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                  (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                    μ 0 j) x = 0 := by
  
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxClass
  have hSTypePDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_case_typeP hmin hcase hSTypeP
  have hW1leS : W1 ≤ Smax := by
    rcases hSTypePDef with
      ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, _hComp, _hUleD, _hUnil,
        _hW1normU, _hDerComp, _hPnotCyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormHatW⟩
    exact hW1hall.1
  let βS : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) - μ 0 j
  have hβclass : Section1.IsClassFunction βS :=
    hypothesis_13_1_betaPreimage_isClassFunction hnotation j hj
  rcases hxClass with ⟨w, hwW1, s, hsS, hx_eq⟩
  let wS : Smax := ⟨w, hW1leS hwW1.1⟩
  let sS : Smax := ⟨s, hsS⟩
  have hx_eq_S : x = sS * wS * sS⁻¹ := by
    ext
    simpa [wS, sS] using hx_eq
  have hβw : βS wS = 0 :=
    hypothesis_13_1_betaSupportSet_W1_representative_zero_s_side_source hmin
      hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS
      hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj wS
      (by simpa [wS] using hwW1)
  change βS x = 0
  calc
    βS x = βS (sS * wS * sS⁻¹) := by rw [hx_eq_S]
    _ = βS wS := hβclass sS wS
    _ = 0 := hβw

private theorem hypothesis_13_1_betaSupportSet_outside_PU_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            ∀ x : Smax,
              (x : G) ∉ ((P ⊔ U : Subgroup G) : Set G) →
                (x : G) ∉ section16NonidentityElements (P : Set G) →
                  (x : G) ∉ section16ConjugatesOfSetBySet
                    ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
                    (Smax : Set G) →
                    (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                        μ 0 j) x = 0 := by
  
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxNotPU _hxP hxV
  have hxClass :
      (x : G) ∈ section16ConjugatesOfSetBySet
        (section16NonidentityElements (W1 : Set G)) (Smax : Set G) :=
    hypothesis_13_1_betaSupportSet_outside_PU_classSupport_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT x hxNotPU hxV
  exact
    hypothesis_13_1_betaSupportSet_W1_classSupport_zero_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxClass

private theorem hypothesis_13_1_betaSupportSet_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j, 0 < j → j < Nat.card W2 →
            Section1.supportedOn
              (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                  μ 0 j)
              (subgroupSetPreimage Smax
                (theorem_13_18_betaSupportSet Smax W W1 W2 P)) := by
  
  intro ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  rw [Section1.supportedOn_iff]
  intro x hx
  have hxP :
      (x : G) ∉ section16NonidentityElements (P : Set G) := by
    intro hxPmem
    exact hx (by
      change (x : G) ∈ theorem_13_18_betaSupportSet Smax W W1 W2 P
      exact Or.inl hxPmem)
  have hxV :
      (x : G) ∉ section16ConjugatesOfSetBySet
        ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (Smax : Set G) := by
    intro hxVmem
    exact hx (by
      change (x : G) ∈ theorem_13_18_betaSupportSet Smax W W1 W2 P
      exact Or.inr hxVmem)
  by_cases hxPU : (x : G) ∈ ((P ⊔ U : Subgroup G) : Set G)
  · exact
      hypothesis_13_1_betaSupportSet_PU_s_side_source hmin hcase hSTypeP hTTypeP
        Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
        hCentralizerBot ω η μ ν μsum νsum δ δ' σ hnotation
        j hj0 hj x hxPU hxP hxV
  · exact
      hypothesis_13_1_betaSupportSet_outside_PU_s_side_source hmin hcase hSTypeP hTTypeP
        Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
        ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj x hxPU hxP hxV

private theorem hypothesis_13_1_conjugateBetaTauDataFor_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (_hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (_hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (_hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          ∀ j k, 0 < j → j < Nat.card W2 → 0 < k → k < Nat.card W2 →
            μ 0 k = Section1.conjugateCharacter (μ 0 j) →
              Section1.conjugateCharacter
                  (τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                      μ 0 j)) =
                τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                  (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                    μ 0 k) := by
  
  intro ω η μ ν μsum νsum δ δ' σ hnotation j k hj0 hj hk0 hk hμ
  have hFourSixSBook := hFourSixS
  rcases hFourSixSBook with
    ⟨_I, _instI, _decI, _J, _instJ, _decJ, _Wsec, _A, _A0, _i0, _j0,
      _μsel, _δSign, _ωsec, _σsec, _hNotation, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, hBook⟩⟩
  rcases hBook with
    ⟨_Ms, _Abook, _A0book, _A1book, R, hA0MG, _h810, _hAbook,
      _hA0book, _hPLeMs, _hPUsub, hτDade⟩
  have hτj :
      τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
            μ 0 j) =
        Section2.dadeTransform R hA0MG.subset_L
          (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
              μ 0 j) :=
    hτDade _
  have hτk :
      τS (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
            μ 0 k) =
        Section2.dadeTransform R hA0MG.subset_L
          (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
              μ 0 k) :=
    hτDade _
  rw [hτj, hτk, hypothesis_13_1_conjugateCharacter_dadeTransform]
  apply congrArg (fun β : Section1.ClassFunction Smax =>
    Section2.dadeTransform R hA0MG.subset_L β)
  have hIndConj :
      Section1.conjugateCharacter
          (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) =
        Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) := by
    ext x
    simp [Section1.conjugateCharacter, Section1.inducedCF,
      Section1.inducedClassFunction, Section1.principalCharacter]
  ext x
  simpa [Section1.conjugateCharacter, Pi.sub_apply, hμ]
    using congrFun hIndConj x

private theorem hypothesis_13_1_conjugateBetaTauDataFor_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2 P Q τS τT
      (Nat.card W2) (Nat.card W1) := by
  intro ω η μ ν μsum νsum δ δ' σ hnotation
  refine ⟨?_, ?_⟩
  · exact
      hypothesis_13_1_conjugateBetaTauDataFor_s_side_source hmin hcase
        hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
        hFourSixS hFourSixT ω η μ ν μsum νsum δ δ' σ hnotation
  · intro i k hi0 hi hk0 hk hν
    have hnotationSwap :
        hypothesis_13_1_characterNotationDataFor Tmax Smax W W2 W1
          (Nat.card W1) (Nat.card W2)
          (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
          (fun i j => μ j i) νsum μsum δ' δ σ :=
      hypothesis_13_1_characterNotationDataFor_swap_local hnotation
    exact
      hypothesis_13_1_conjugateBetaTauDataFor_s_side_source hmin
        (hypothesis_13_1_case_b_data_swap hcase) hTTypeP hSTypeP Tfam Sfam
        τT τS hTnonker hSnonker hDadeT hDadeS hFourSixT hFourSixS
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ hnotationSwap
        i k hi0 hi hk0 hk hν

private theorem hypothesis_13_1_cfNormSq_mu_zero_row_eq_one
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax : Subgroup G}
    {ω : ℕ → ℕ → Section1.ClassFunction W}
    {η : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ)
    (j : ℕ) (hj : j < Nat.card W2) :
    Section5.cfNormSq (μ 0 j) = 1 := by
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  have hself :
      Section1.scalarProduct Smax (μ 0 j) (μ 0 j) = (1 : ℂ) :=
    Section1.scalarProduct_irreducibleCharacter_self (hμirr 0 j hqpos hj)
  unfold Section5.cfNormSq
  rw [hself]
  norm_num

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_cfIndMod_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    ∀ s : Smax,
      Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
          (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) s =
        Section1.inducedCF
          (((P ⊔ W1).subgroupOf Smax).map
            (QuotientGroup.mk' (P.subgroupOf Smax)))
          (Section1.principalCharacter
            (((P ⊔ W1).subgroupOf Smax).map
              (QuotientGroup.mk' (P.subgroupOf Smax))))
          (QuotientGroup.mk' (P.subgroupOf Smax) s) := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  intro s
  exact
    Section1.inducedCF_principal_quotientImageSubgroup_mk
      ((P ⊔ W1).subgroupOf Smax) (P.subgroupOf Smax) (by
        intro x hx
        change (x : G) ∈ P ⊔ W1
        exact (show P ≤ P ⊔ W1 from le_sup_left)
          (by simpa [Subgroup.mem_subgroupOf] using hx))
      s

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_Dgamma_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    ∃ gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax),
      ∀ s : Smax,
        Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) s =
          gamma (QuotientGroup.mk' (P.subgroupOf Smax) s) := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  let H : Subgroup Smax := (P ⊔ W1).subgroupOf Smax
  let A : Subgroup Smax := P.subgroupOf Smax
  let Hbar : Subgroup (Smax ⧸ A) := H.map (QuotientGroup.mk' A)
  let θbar : Section1.ClassFunction Hbar := Section1.principalCharacter Hbar
  let γ : Section1.ClassFunction (Smax ⧸ A) :=
    Section1.inducedCF Hbar θbar
  refine ⟨γ, ?_⟩
  intro s
  exact
    by
      simpa [H, A, θbar, γ] using
        hypothesis_13_1_betaNorm_inducedPrincipal_cfIndMod_source hSTypeP s

private theorem section13_quotient_sum_lift_real
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (F : G ⧸ A → ℝ) :
    (∑ x : G, F (QuotientGroup.mk' A x)) =
      (Nat.card A : ℝ) * (∑ q : G ⧸ A, F q) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (G ⧸ A) := Fintype.ofFinite (G ⧸ A)
  calc
    (∑ x : G, F (QuotientGroup.mk' A x)) =
        ∑ q : G ⧸ A, ∑ x : {x : G // QuotientGroup.mk' A x = q},
          F (QuotientGroup.mk' A x) := by
      exact
        (Fintype.sum_fiberwise
          (g := fun x : G => QuotientGroup.mk' A x)
          (f := fun x : G => F (QuotientGroup.mk' A x))).symm
    _ = ∑ q : G ⧸ A, ∑ _x : {x : G // QuotientGroup.mk' A x = q}, F q := by
      refine Finset.sum_congr rfl ?_
      intro q _hq
      refine Finset.sum_congr rfl ?_
      intro x _hx
      simp [x.2]
    _ = ∑ q : G ⧸ A, (Nat.card A : ℝ) * F q := by
      refine Finset.sum_congr rfl ?_
      intro q _hq
      have hfiber :
          Nat.card {x : G // QuotientGroup.mk' A x = q} = Nat.card A := by
        calc
          Nat.card {x : G // QuotientGroup.mk' A x = q} =
              Nat.card (A × ({q} : Set (G ⧸ A))) := by
            exact Nat.card_congr
              (QuotientGroup.preimageMkEquivSubgroupProdSet A ({q}))
          _ = Nat.card A := by
            simp
      calc
        (∑ _x : {x : G // QuotientGroup.mk' A x = q}, F q) =
            (Fintype.card {x : G // QuotientGroup.mk' A x = q} : ℝ) * F q := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        _ = (Nat.card {x : G // QuotientGroup.mk' A x = q} : ℝ) * F q := by
          rw [Nat.card_eq_fintype_card]
        _ = (Nat.card A : ℝ) * F q := by
          rw [hfiber]
    _ = (Nat.card A : ℝ) * (∑ q : G ⧸ A, F q) := by
      rw [Finset.mul_sum]

private theorem section13_cfNormSq_inflation_quotient_eq
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal]
    (gamma : Section1.ClassFunction (G ⧸ A)) :
    Section5.cfNormSq (fun g : G => gamma (QuotientGroup.mk' A g)) =
      Section5.cfNormSq gamma := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (G ⧸ A) := Fintype.ofFinite (G ⧸ A)
  rw [Section5.cfNormSq_eq_inv_card_mul_sum_normSq]
  rw [Section5.cfNormSq_eq_inv_card_mul_sum_normSq]
  rw [section13_quotient_sum_lift_real A
    (fun q : G ⧸ A => Complex.normSq (gamma q))]
  have hcardG : Nat.card G = Nat.card (G ⧸ A) * Nat.card A :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup A
  rw [hcardG, Nat.cast_mul]
  have hA : (Nat.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := A)).ne'
  have hQ : (Nat.card (G ⧸ A) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G ⧸ A)).ne'
  field_simp [hA, hQ]

private theorem section13_cfNormSq_of_quotient_principal_count_data
    {Q : Type u} [Group Q] [Finite Q] [DecidableEq Q]
    (gamma : Section1.ClassFunction Q)
    (u q : ℕ)
    (hQcard : Nat.card Q = u * q)
    (hu : 0 < u)
    (hq : 0 < q)
    (hgamma1 : Complex.normSq (gamma 1) = (u : ℝ) ^ (2 : ℕ))
    (hsum_nonid :
      (∑ x ∈ Finset.univ.erase (1 : Q), Complex.normSq (gamma x)) =
        (u : ℝ) * ((q : ℝ) - 1)) :
    Section5.cfNormSq gamma = ((u - 1 : ℕ) : ℝ) / (q : ℝ) + 1 := by
  classical
  rw [Section5.cfNormSq_eq_inv_card_mul_sum_normSq]
  have hsum :
      (∑ x : Q, Complex.normSq (gamma x)) =
        Complex.normSq (gamma 1) +
          ∑ x ∈ Finset.univ.erase (1 : Q), Complex.normSq (gamma x) := by
    simp
  rw [hsum, hgamma1, hsum_nonid, hQcard, Nat.cast_mul]
  have hu_ne : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hucast : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hu), Nat.cast_one]
  rw [hucast]
  field_simp [hu_ne, hq_ne]
  ring

private theorem section13_nonidentity_normSq_sum_of_support
    {Q : Type u} [Group Q] [Finite Q] [DecidableEq Q]
    (gamma : Section1.ClassFunction Q)
    (support : Finset Q)
    (u q : ℕ)
    (hq : 0 < q)
    (hsub : support ⊆ Finset.univ.erase (1 : Q))
    (hcard : support.card = u * (q - 1))
    (hzero :
      ∀ x, x ∈ Finset.univ.erase (1 : Q) → x ∉ support → gamma x = 0)
    (hone : ∀ x, x ∈ support → gamma x = 1) :
    (∑ x ∈ Finset.univ.erase (1 : Q), Complex.normSq (gamma x)) =
      (u : ℝ) * ((q : ℝ) - 1) := by
  classical
  have hsum_support :
      (∑ x ∈ Finset.univ.erase (1 : Q), Complex.normSq (gamma x)) =
        ∑ x ∈ support, Complex.normSq (gamma x) := by
    symm
    exact
      Finset.sum_subset hsub (by
        intro x hxerase hxnot
        simp [hzero x hxerase hxnot])
  have hsupport_sum :
      (∑ x ∈ support, Complex.normSq (gamma x)) =
        (support.card : ℝ) := by
    calc
      (∑ x ∈ support, Complex.normSq (gamma x)) =
          ∑ x ∈ support, (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [hone x hx]
      _ = (support.card : ℝ) := by
            simp
  calc
    (∑ x ∈ Finset.univ.erase (1 : Q), Complex.normSq (gamma x)) =
        (support.card : ℝ) := by rw [hsum_support, hsupport_sum]
    _ = (u * (q - 1) : ℕ) := by rw [hcard]
    _ = (u : ℝ) * ((q : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_iff.mpr hq),
          Nat.cast_one]

private theorem section13_support_package_of_one_values
    {Q : Type u} [Group Q] [Finite Q] [DecidableEq Q]
    (gamma : Section1.ClassFunction Q)
    (u q : ℕ)
    (hcard :
      ((Finset.univ.erase (1 : Q)).filter (fun x => gamma x = 1)).card =
        u * (q - 1))
    (hvalues :
      ∀ x, x ∈ Finset.univ.erase (1 : Q) → gamma x = 0 ∨ gamma x = 1) :
    ∃ support : Finset Q,
      support ⊆ Finset.univ.erase (1 : Q) ∧
        support.card = u * (q - 1) ∧
          (∀ x, x ∈ Finset.univ.erase (1 : Q) →
            x ∉ support → gamma x = 0) ∧
            (∀ x, x ∈ support → gamma x = 1) := by
  classical
  let support : Finset Q :=
    (Finset.univ.erase (1 : Q)).filter (fun x => gamma x = 1)
  refine ⟨support, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).1
  · simpa [support] using hcard
  · intro x hxnonid hxnot
    have hx_ne_one : gamma x ≠ 1 := by
      intro hxone
      exact hxnot (by simp [support, hxnonid, hxone])
    rcases hvalues x hxnonid with hxzero | hxone
    · exact hxzero
    · exact False.elim (hx_ne_one hxone)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_card_structural_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    ∀ (C : Subgroup G),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          C ≤ U →
            ∀ hnormal : (C.subgroupOf U).Normal,
            letI : (C.subgroupOf U).Normal := hnormal
            Nat.card (Smax ⧸ P.subgroupOf Smax) =
              Nat.card (U ⧸ C.subgroupOf U) * Nat.card W1 := by
  
  classical
  let D : Subgroup G := ambientDerivedSubgroup Smax
  rcases hSTypeP with ⟨hP, hCommon⟩
  intro C _hC hCbot _hCU hCnormal
  letI : (C.subgroupOf U).Normal := hCnormal
  have hPnormal : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hP
  letI : (P.subgroupOf Smax).Normal := hPnormal
  have hCompDW1 : section12ComplementIn Smax D W1 := by
    simpa [D] using
      Section8.theorem_8_8_typeCommon_W1_complement (G := G) hCommon
  rcases hCommon with
    ⟨_hHallD, hPleD, hCompPU, _hUnil, _hW1norm, _hW1cyc, _hW1card,
      _hPnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6, _hW2second⟩
  have hDleS : D ≤ Smax := hCompDW1.1
  have hPleS : P ≤ Smax := hPleD.trans hDleS
  have hP_D_normal : (P.subgroupOf D).Normal := by
    have hDleNormP : D ≤ Subgroup.normalizer (P : Set G) := by
      intro x hxD
      exact
        (Subgroup.normal_subgroupOf_iff_le_normalizer hPleS).1 hPnormal
          (hDleS hxD)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCompPU.1).2 hDleNormP
  have hCompPUlocal :
      (P.subgroupOf D).IsComplement' (U.subgroupOf D) :=
    Section12.section12ComplementIn_left_normal_isComplement' hCompPU hP_D_normal
  have hDnormal : (D.subgroupOf Smax).Normal := by
    simpa [D] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax)).2
  have hCompDW1local :
      (D.subgroupOf Smax).IsComplement' (W1.subgroupOf Smax) :=
    Section12.section12ComplementIn_left_normal_isComplement' hCompDW1 hDnormal
  have hPsub_le_Dsub : P.subgroupOf Smax ≤ D.subgroupOf Smax := by
    intro x hx
    exact hPleD hx
  have hrel :
      (P.subgroupOf Smax).relIndex (D.subgroupOf Smax) = Nat.card U := by
    have hsub :
        (P.subgroupOf D).index =
          (P.subgroupOf Smax).relIndex (D.subgroupOf Smax) := by
      simpa [D, Subgroup.relIndex] using
        (Subgroup.relIndex_subgroupOf
          (H := P) (K := D) (L := Smax) hDleS).symm
    rw [← hsub]
    calc
      (P.subgroupOf D).index = Nat.card (U.subgroupOf D) :=
        hCompPUlocal.symm.index_eq_card
      _ = Nat.card U := natCard_subgroupOf_eq U D hCompPU.2.1
  have hDindex : (D.subgroupOf Smax).index = Nat.card W1 := by
    calc
      (D.subgroupOf Smax).index = Nat.card (W1.subgroupOf Smax) :=
        hCompDW1local.symm.index_eq_card
      _ = Nat.card W1 := natCard_subgroupOf_eq W1 Smax hCompDW1.2.1
  have hPindex : (P.subgroupOf Smax).index = Nat.card U * Nat.card W1 := by
    rw [← hrel, ← hDindex]
    exact (Subgroup.relIndex_mul_index hPsub_le_Dsub).symm
  have hquotC : Nat.card (U ⧸ C.subgroupOf U) = Nat.card U := by
    rw [hCbot]
    simpa [Subgroup.index_eq_card] using
      (Subgroup.index_bot (G := U))
  rw [hquotC]
  simpa [Subgroup.index_eq_card] using hPindex

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_card_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            Nat.card (Smax ⧸ P.subgroupOf Smax) = u * Nat.card W1 := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  intro C u hC hCbot hBarU
  rcases hBarU with ⟨hCU, hCnormal, hUquot⟩
  letI : (C.subgroupOf U).Normal := hCnormal
  have hstruct :
      Nat.card (Smax ⧸ P.subgroupOf Smax) =
        Nat.card (U ⧸ C.subgroupOf U) * Nat.card W1 :=
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_card_structural_source
      hSTypeP C hC hCbot hCU hCnormal
  rw [hUquot] at hstruct
  exact hstruct

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_join_subgroupOf_index_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            Subgroup.index ((P ⊔ W1).subgroupOf Smax) = u := by
  
  classical
  let D : Subgroup G := ambientDerivedSubgroup Smax
  rcases hSTypeP with ⟨hP, hCommon⟩
  intro C u hC hCbot hBarU
  have hPnormal : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hP
  letI : (P.subgroupOf Smax).Normal := hPnormal
  have hquot :
      Nat.card (Smax ⧸ P.subgroupOf Smax) = u * Nat.card W1 :=
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_card_source
      ⟨hP, hCommon⟩ C u hC hCbot hBarU
  have hPindex : (P.subgroupOf Smax).index = u * Nat.card W1 := by
    simpa [Subgroup.index_eq_card] using hquot
  have hCompDW1 : section12ComplementIn Smax D W1 := by
    simpa [D] using
      Section8.theorem_8_8_typeCommon_W1_complement (G := G) hCommon
  rcases hCommon with
    ⟨_hHallD, hPleD, _hCompPU, _hUnil, _hW1norm, _hW1cyc, _hW1card,
      _hPnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6, _hW2second⟩
  have hPleS : P ≤ Smax := hPleD.trans hCompDW1.1
  have hW1leS : W1 ≤ Smax := hCompDW1.2.1
  let H : Subgroup G := P ⊔ W1
  have hHleS : H ≤ Smax := sup_le hPleS hW1leS
  have hPsub_le_Hsub : P.subgroupOf Smax ≤ H.subgroupOf Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [H, Subgroup.mem_subgroupOf] using
      ((le_sup_left : P ≤ P ⊔ W1) hxP)
  have hP_H_normal : (P.subgroupOf H).Normal := by
    have hHleNormP : H ≤ Subgroup.normalizer (P : Set G) := by
      intro x hxH
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPleS).1 hPnormal
        (hHleS hxH)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : P ≤ H)).2
      hHleNormP
  have hCompPW1 : section12ComplementIn H P W1 := by
    refine ⟨le_sup_left, le_sup_right, rfl, ?_⟩
    rw [Subgroup.disjoint_def]
    intro x hxP hxW1
    exact hCompDW1.2.2.2.le_bot ⟨hPleD hxP, hxW1⟩
  have hPW1_local :
      (P.subgroupOf H).IsComplement' (W1.subgroupOf H) :=
    Section12.section12ComplementIn_left_normal_isComplement' hCompPW1 hP_H_normal
  have hrel :
      (P.subgroupOf Smax).relIndex (H.subgroupOf Smax) = Nat.card W1 := by
    have hsub :
        (P.subgroupOf H).index =
          (P.subgroupOf Smax).relIndex (H.subgroupOf Smax) := by
      simpa [H, Subgroup.relIndex] using
        (Subgroup.relIndex_subgroupOf
          (H := P) (K := H) (L := Smax) hHleS).symm
    rw [← hsub]
    calc
      (P.subgroupOf H).index = Nat.card (W1.subgroupOf H) :=
        hPW1_local.symm.index_eq_card
      _ = Nat.card W1 := natCard_subgroupOf_eq W1 H le_sup_right
  have hmul :
      (P.subgroupOf Smax).relIndex (H.subgroupOf Smax) *
          (H.subgroupOf Smax).index =
        (P.subgroupOf Smax).index :=
    Subgroup.relIndex_mul_index hPsub_le_Hsub
  rw [hrel, hPindex] at hmul
  rw [Nat.mul_comm u (Nat.card W1)] at hmul
  have hW1pos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
  exact Nat.eq_of_mul_eq_mul_left hW1pos hmul

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_Hbar_index_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            Subgroup.index Hbar = u := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  intro C u hC hCbot hBarU
  let H : Subgroup Smax := (P ⊔ W1).subgroupOf Smax
  let q : Smax →* Smax ⧸ P.subgroupOf Smax :=
    QuotientGroup.mk' (P.subgroupOf Smax)
  have hker_le : q.ker ≤ H := by
    intro x hx
    change (x : G) ∈ P ⊔ W1
    have hxPsub : x ∈ P.subgroupOf Smax := by
      simpa [q, QuotientGroup.ker_mk'] using hx
    exact (le_sup_left : P ≤ P ⊔ W1) hxPsub
  have hidx_map :
      (((P ⊔ W1).subgroupOf Smax).map q).index =
        ((P ⊔ W1).subgroupOf Smax).index :=
    ((P ⊔ W1).subgroupOf Smax).index_map_eq
      (QuotientGroup.mk'_surjective (P.subgroupOf Smax)) hker_le
  have hidxH :
      Subgroup.index ((P ⊔ W1).subgroupOf Smax) = u :=
    hypothesis_13_1_betaNorm_inducedPrincipal_join_subgroupOf_index_source
      hSTypeP C u hC hCbot hBarU
  simpa [q] using hidx_map.trans hidxH

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_gamma_identity_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
              Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
            Complex.normSq (gamma 1) = (u : ℝ) ^ (2 : ℕ) := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : Fintype (Smax ⧸ P.subgroupOf Smax) := Fintype.ofFinite _
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
    Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
  have hgamma :
      gamma 1 = (u : ℂ) := by
    have hidx :
        Subgroup.index Hbar = u :=
      hypothesis_13_1_betaNorm_inducedPrincipal_quotient_Hbar_index_source
        hSTypeP C u hC hCbot hBarU
    have hvalue :
        gamma 1 = (Subgroup.index Hbar : ℂ) :=
      hypothesis_13_1_inducedPrincipal_identity_value Hbar 1 rfl
    simpa [hidx] using hvalue
  change Complex.normSq (gamma 1) = (u : ℝ) ^ (2 : ℕ)
  simp [hgamma, Complex.normSq_natCast, pow_two]

private theorem hypothesis_13_1_typeP_nested_isComplement'
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrob : section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    (P.subgroupOf Smax).IsComplement'
      ((U ⊔ W1).subgroupOf Smax) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup Smax
  let K : Subgroup G := U ⊔ W1
  rcases hSTypeP with ⟨hP, hCommon⟩
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hP
  have hCompDW1 : section12ComplementIn Smax D W1 := by
    simpa [D] using
      Section8.theorem_8_8_typeCommon_W1_complement (G := G) hCommon
  rcases hCommon with
    ⟨_hHallD, hPleD, hCompPU, _hUnil, _hW1norm, _hW1cyc, _hW1card,
      _hPnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6, _hW2second⟩
  have hPleS : P ≤ Smax := hPleD.trans hCompDW1.1
  have hUleD : U ≤ D := hCompPU.2.1
  have hUleS : U ≤ Smax := hUleD.trans hCompDW1.1
  have hW1leS : W1 ≤ Smax := hCompDW1.2.1
  have hKleS : K ≤ Smax := sup_le hUleS hW1leS
  have hFrobK :
      IsFrobeniusGroupWithKernelComplement
        (U.subgroupOf K) (W1.subgroupOf K) := by
    simpa [section12FrobeniusJoinWithKernel, K] using hFrob
  have hdisj :
      Disjoint (P.subgroupOf Smax) (K.subgroupOf Smax) := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxK
    let xK : K := ⟨(x : G), by
      simpa [Subgroup.mem_subgroupOf] using hxK⟩
    rcases hFrobK.isComplement'.2 xK with ⟨uw, huw⟩
    rcases uw with ⟨u, w⟩
    have huwG : (u : G) * (w : G) = (x : G) := by
      simpa [xK] using congrArg (fun z : K => (z : G)) huw
    have hxD : (x : G) ∈ D := hPleD hxP
    have huD : (u : G) ∈ D := hUleD u.property
    have hwD : (w : G) ∈ D := by
      have hmem : (u : G)⁻¹ * (x : G) ∈ D :=
        D.mul_mem (D.inv_mem huD) hxD
      have heq : (u : G)⁻¹ * (x : G) = (w : G) := by
        rw [← huwG]
        simp
      simpa [heq] using hmem
    have hwW1 : (w : G) ∈ W1 := w.property
    have hwBot : (w : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hCompDW1.2.2.2) hwD hwW1
    have hwOne : (w : G) = 1 := by simpa using hwBot
    have hxU : (x : G) ∈ U := by
      have huU : (u : G) ∈ U := u.property
      have hxEq : (x : G) = (u : G) := by
        rw [← huwG, hwOne]
        simp
      simpa [hxEq] using huU
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hCompPU.2.2.2) hxP hxU
    apply Subtype.ext
    simpa using hxBot
  have hsupAmbient : P ⊔ K = Smax := by
    calc
      P ⊔ K = (P ⊔ U) ⊔ W1 := by simp [K, sup_assoc]
      _ = D ⊔ W1 := by rw [← hCompPU.2.2.1]
      _ = Smax := hCompDW1.2.2.1.symm
  have hsupTop :
      P.subgroupOf Smax ⊔ K.subgroupOf Smax = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := P) (A' := K) (B := Smax)
      hPleS hKleS]
    exact Subgroup.subgroupOf_eq_top.2 (by simp [hsupAmbient])
  exact isComplement'_of_disjoint_sup_eq_top_of_normal
    (P.subgroupOf Smax) (K.subgroupOf Smax) hdisj hsupTop

private theorem section13_frobenius_complement_tiNormalizer
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G}
    (hFrob : IsFrobeniusGroupWithKernelComplement K R) :
    section16TISubsetWithNormalizer
      (Section7.puncturedSubgroupSet R) R := by
  let X : Set G := Section7.puncturedSubgroupSet R
  have hRnorm :
      ∀ g : G, g ∈ R → ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X := by
    intro g hg x
    constructor
    · intro hx
      refine ⟨R.mul_mem (R.mul_mem hg hx.1) (R.inv_mem hg), ?_⟩
      intro hconj
      apply hx.2
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by simp [hconj]
    · intro hx
      refine ⟨?_, ?_⟩
      · have hmem :
            g⁻¹ * (g * x * g⁻¹) * g ∈ R :=
          R.mul_mem (R.mul_mem (R.inv_mem hg) hx.1) hg
        have heq : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        simpa only [heq] using hmem
      · intro hxone
        apply hx.2
        simp [hxone]
  have hconj_eq :
      ∀ g : G, g ∈ R → section16ConjugateSet X g = X := by
    intro g hg
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hRnorm g hg x).1 hx
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by group⟩
      have hpre := (hRnorm g⁻¹ (R.inv_mem hg) y).1 hy
      simpa only [inv_inv] using hpre
  constructor
  · intro g
    by_cases hg : g ∈ R
    · exact Or.inl (hconj_eq g hg)
    · right
      intro y hy
      rcases hy.2 with ⟨x, hx, hxy⟩
      have hyConj : y ∈ R.conjBy g := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨x, hx.1, by simpa [MulAut.conj_apply] using hxy.symm⟩
      have hyBot : y ∈ (⊥ : Subgroup G) :=
        (Subgroup.disjoint_def.mp (hFrob.disjoint_conjBy g hg)) hy.1.1 hyConj
      simpa using hyBot
  · apply le_antisymm
    · intro g hgNorm
      rcases Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.complement_ne_bot with
        ⟨r, hrne⟩
      have hrX : (r : G) ∈ X := ⟨r.property, by simpa using hrne⟩
      have hgNorm' : ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X := by
        change ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X at hgNorm
        exact hgNorm
      have hgrX : g * (r : G) * g⁻¹ ∈ X :=
        (hgNorm' (r : G)).1 hrX
      by_contra hg
      have hgrConj : g * (r : G) * g⁻¹ ∈ R.conjBy g := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨r, r.property, by simp [MulAut.conj_apply]⟩
      have hgrBot : g * (r : G) * g⁻¹ ∈ (⊥ : Subgroup G) :=
        (Subgroup.disjoint_def.mp (hFrob.disjoint_conjBy g hg))
          hgrX.1 hgrConj
      have hgrOne : g * (r : G) * g⁻¹ = 1 := by
        simpa using hgrBot
      apply hrne
      apply Subtype.ext
      calc
        (r : G) = g⁻¹ * (g * (r : G) * g⁻¹) * g := by group
        _ = 1 := by simp [hgrOne]
    · intro g hg
      change g ∈ Subgroup.normalizer X
      change ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X
      exact hRnorm g hg

private theorem section13_top_tiNormalizer
    {G : Type u} [Group G] [Finite G] :
    section16TISubsetWithNormalizer
      (Section7.puncturedSubgroupSet (⊤ : Subgroup G)) ⊤ := by
  let X : Set G := Section7.puncturedSubgroupSet (⊤ : Subgroup G)
  have hnorm : ∀ g x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X := by
    intro g x
    constructor
    · intro hx
      refine ⟨by simp, ?_⟩
      intro hconj
      apply hx.2
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by simp [hconj]
    · intro hx
      refine ⟨by simp, ?_⟩
      intro hxone
      apply hx.2
      simp [hxone]
  have hconj : ∀ g : G, section16ConjugateSet X g = X := by
    intro g
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hnorm g x).1 hx
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by group⟩
      have hpre := (hnorm g⁻¹ y).1 hy
      simpa only [inv_inv] using hpre
  constructor
  · intro g
    exact Or.inl (hconj g)
  · apply top_unique
    intro g _hg
    change ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X
    exact hnorm g

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_Hbar_tiNormalizer_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet Hbar) Hbar := by
  
  classical
  let D : Subgroup G := ambientDerivedSubgroup Smax
  let K : Subgroup G := U ⊔ W1
  have hSTypeP0 := hSTypeP
  rcases hSTypeP with ⟨hP, hCommon⟩
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hP
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro _C _u _hC _hCbot _hBarU
  have hCompDW1 : section12ComplementIn Smax D W1 := by
    simpa [D] using
      Section8.theorem_8_8_typeCommon_W1_complement (G := G) hCommon
  rcases hCommon with
    ⟨_hHallD, hPleD, hCompPU, _hUnil, _hW1norm, _hW1cyc, _hW1card,
      _hPnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6, _hW2second⟩
  have hPleS : P ≤ Smax := hPleD.trans hCompDW1.1
  have hUleS : U ≤ Smax := hCompPU.2.1.trans hCompDW1.1
  have hW1leS : W1 ≤ Smax := hCompDW1.2.1
  have hKleS : K ≤ Smax := sup_le hUleS hW1leS
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  change section16TISubsetWithNormalizer
    (Section7.puncturedSubgroupSet Hbar) Hbar
  rcases hFrobAlt with hUbot | hFrob
  · have hD_eq : D = P := by
      calc
        D = P ⊔ U := hCompPU.2.2.1
        _ = P := by simp [hUbot]
    have hS_eq : Smax = P ⊔ W1 := by
      calc
        Smax = D ⊔ W1 := hCompDW1.2.2.1
        _ = P ⊔ W1 := by rw [hD_eq]
    have hsubTop : (P ⊔ W1).subgroupOf Smax = ⊤ :=
      Subgroup.subgroupOf_eq_top.2 (by
        intro x hx
        simpa [hS_eq] using hx)
    have hHbarTop : Hbar = ⊤ := by
      apply top_unique
      intro y _hy
      rcases QuotientGroup.mk'_surjective (N := P.subgroupOf Smax) y with
        ⟨s, rfl⟩
      refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
      simp [hsubTop]
    rw [hHbarTop]
    exact section13_top_tiNormalizer
  · have hcomp :
        (P.subgroupOf Smax).IsComplement' (K.subgroupOf Smax) := by
      simpa [K] using hypothesis_13_1_typeP_nested_isComplement' hSTypeP0 hFrob
    let e : Smax ⧸ P.subgroupOf Smax ≃* K :=
      hcomp.symm.QuotientMulEquiv.trans
        (Subgroup.subgroupOfEquivOfLe hKleS)
    have hHbar :
        Hbar = (W1.subgroupOf K).map e.symm.toMonoidHom := by
      simpa [Hbar, e] using
        quotient_sup_image_eq_complement_map
          hPleS hKleS (le_sup_right : W1 ≤ K) hcomp
    have hFrobK :
        IsFrobeniusGroupWithKernelComplement
          (U.subgroupOf K) (W1.subgroupOf K) := by
      simpa [section12FrobeniusJoinWithKernel, K] using hFrob
    have hFrobQ :
        IsFrobeniusGroupWithKernelComplement
          ((U.subgroupOf K).map e.symm.toMonoidHom)
          ((W1.subgroupOf K).map e.symm.toMonoidHom) :=
      hFrobK.map_mulEquiv e.symm
    rw [hHbar]
    exact section13_frobenius_complement_tiNormalizer hFrobQ

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_one_values_card_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
              Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
            let nonidentity : Finset (Smax ⧸ P.subgroupOf Smax) :=
              Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax)
            (nonidentity.filter (fun x => gamma x = 1)).card =
              u * (Nat.card W1 - 1) := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : Fintype (Smax ⧸ P.subgroupOf Smax) := Fintype.ofFinite _
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
    Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
  let nonidentity : Finset (Smax ⧸ P.subgroupOf Smax) :=
    Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax)
  have hTINorm :
      section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet Hbar) Hbar :=
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_Hbar_tiNormalizer_source
      hSTypeP hFrobAlt C u hC hCbot hBarU
  have hfilter_conj :
      (nonidentity.filter (fun x => gamma x = 1)).card =
        Nat.card
          (section16ConjugatesOfSetBySet
            (Section7.puncturedSubgroupSet Hbar) Set.univ) := by
    let X : Set (Smax ⧸ P.subgroupOf Smax) :=
      section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Hbar) Set.univ
    let F : Type u := {x : Smax ⧸ P.subgroupOf Smax // x ∈ nonidentity.filter (fun x => gamma x = 1)}
    let Xsub : Type u := {x : Smax ⧸ P.subgroupOf Smax // x ∈ X}
    have htoX : ∀ x : F, (x.1 : Smax ⧸ P.subgroupOf Smax) ∈ X := by
      intro x
      have hxmem : x.1 ∈ nonidentity := (Finset.mem_filter.mp x.2).1
      have hxgamma : gamma x.1 = 1 := (Finset.mem_filter.mp x.2).2
      have hxne : (x.1 : Smax ⧸ P.subgroupOf Smax) ≠ 1 := (Finset.mem_erase.mp hxmem).1
      by_contra hxnotX
      have hxnotH :
          (x.1 : Smax ⧸ P.subgroupOf Smax) ∉
            section16ConjugatesOfSetBySet (Hbar : Set (Smax ⧸ P.subgroupOf Smax))
              Set.univ := by
        intro hxH
        rcases hxH with ⟨z, hzH, t, ht, hxz⟩
        have hz_ne : z ≠ 1 := by
          intro hz1
          exact hxne (by simp [hxz, hz1])
        exact hxnotX ⟨z, ⟨hzH, hz_ne⟩, t, ht, hxz⟩
      have hzero : gamma x.1 = 0 := by
        simpa [gamma] using
          hypothesis_13_1_inducedCF_eq_zero_of_not_mem_conjugates
            Hbar (Section1.principalCharacter Hbar) hxnotH
      norm_num [hzero] at hxgamma
    have hfromX :
        ∀ x : Xsub, (x.1 : Smax ⧸ P.subgroupOf Smax) ∈
          nonidentity.filter (fun x => gamma x = 1) := by
      intro x
      rcases x.2 with ⟨z, hzH, t, ht, hxz⟩
      have hxne : (x.1 : Smax ⧸ P.subgroupOf Smax) ≠ 1 := by
        intro hx1
        have hz1 : z = 1 := by
          have hxz1 : t * z * t⁻¹ = 1 := by
            simpa [hx1] using hxz.symm
          have h := congrArg (fun y : Smax ⧸ P.subgroupOf Smax => t⁻¹ * y * t) hxz1
          simpa [mul_assoc] using h
        exact hzH.2 hz1
      have hxmem : (x.1 : Smax ⧸ P.subgroupOf Smax) ∈ nonidentity := by
        exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_univ _⟩
      have hgamma : gamma x.1 = 1 := by
        have hcard :
            Nat.card {y : Smax ⧸ P.subgroupOf Smax //
              y * (t * z * t⁻¹) * y⁻¹ ∈ Hbar} = Nat.card Hbar :=
          hypothesis_13_1_conjugator_card_conj_eq_of_ti_normalizer
            Hbar hTINorm (x := z) (t := t) hzH
        simpa [gamma, hxz] using
          hypothesis_13_1_inducedCF_principal_eq_one_of_conjugator_card
            Hbar (t * z * t⁻¹) hcard
      exact Finset.mem_filter.mpr ⟨hxmem, hgamma⟩
    let e : F ≃ Xsub :=
      { toFun := fun x => ⟨x.1, htoX x⟩
        invFun := fun x => ⟨x.1, hfromX x⟩
        left_inv := by
          intro x
          rfl
        right_inv := by
          intro x
          rfl }
    calc
      (nonidentity.filter (fun x => gamma x = 1)).card = Nat.card F := by
        have hcardF :
            Nat.card F = (nonidentity.filter (fun x => gamma x = 1)).card := by
          rw [Nat.card_eq_fintype_card]
          simpa [F] using
            (Fintype.card_coe (nonidentity.filter (fun x => gamma x = 1)))
        exact hcardF.symm
      _ = Nat.card Xsub := Nat.card_congr e
      _ = Nat.card X := rfl
  have hconjCard :
      Nat.card
          (section16ConjugatesOfSetBySet
            (Section7.puncturedSubgroupSet Hbar) Set.univ) =
        Nat.card (Section7.puncturedSubgroupSet Hbar) * Hbar.index := by
    have hcard :=
      hypothesis_13_1_card_conjugatesOfSetBySet_eq_card_mul_index_of_ti
        (X := Section7.puncturedSubgroupSet Hbar)
        (by intro h; exact h.2 rfl) hTINorm.1
    simpa [hTINorm.2] using hcard
  have hidx : Hbar.index = u :=
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_Hbar_index_source
      hSTypeP C u hC hCbot hBarU
  have htotal :
      Nat.card (Smax ⧸ P.subgroupOf Smax) = u * Nat.card W1 :=
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_card_source
      hSTypeP C u hC hCbot hBarU
  have hu_pos : 0 < u := by
    rcases hBarU with ⟨_hCU, hCnormal, hUquot⟩
    letI : (C.subgroupOf U).Normal := hCnormal
    rw [← hUquot]
    exact Nat.card_pos (α := U ⧸ C.subgroupOf U)
  have hHbar_card : Nat.card Hbar = Nat.card W1 := by
    have hmul := Hbar.card_mul_index
    rw [hidx, htotal] at hmul
    rw [Nat.mul_comm u (Nat.card W1)] at hmul
    exact Nat.eq_of_mul_eq_mul_right hu_pos hmul
  have hfinal :
      (nonidentity.filter (fun x => gamma x = 1)).card =
        u * (Nat.card W1 - 1) := by
    rw [hfilter_conj, hconjCard,
      hypothesis_13_1_natCard_puncturedSubgroupSet Hbar, hHbar_card, hidx,
      Nat.mul_comm]
  simpa [Hbar, gamma, nonidentity] using hfinal

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_conjugacy_support_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            let nonidentity : Finset (Smax ⧸ P.subgroupOf Smax) :=
              Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax)
            ∀ x, x ∈ nonidentity →
              x ∉ section16ConjugatesOfSetBySet (Hbar : Set (Smax ⧸ P.subgroupOf Smax))
                  Set.univ ∨
                Nat.card {y : Smax ⧸ P.subgroupOf Smax // y * x * y⁻¹ ∈ Hbar} =
                  Nat.card Hbar := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  dsimp only
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  have hTINorm :
      section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet Hbar) Hbar :=
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_Hbar_tiNormalizer_source
      hSTypeP hFrobAlt C u hC hCbot hBarU
  intro x hx
  by_cases hxconj :
      x ∈ section16ConjugatesOfSetBySet (Hbar : Set (Smax ⧸ P.subgroupOf Smax))
        Set.univ
  · right
    rcases hxconj with ⟨z, hzH, t, _ht, hzx⟩
    have hxne : x ≠ 1 := by
      simpa using (Finset.mem_erase.mp hx).1
    have hz_ne : z ≠ 1 := by
      intro hz1
      apply hxne
      simp [hzx, hz1]
    have hzsharp : z ∈ Section7.puncturedSubgroupSet Hbar :=
      ⟨hzH, hz_ne⟩
    simpa [hzx, Hbar] using
      hypothesis_13_1_conjugator_card_conj_eq_of_ti_normalizer
        Hbar hTINorm (x := z) (t := t) hzsharp
  · left
    simpa [Hbar] using hxconj

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_nonidentity_values_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
              Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
            let nonidentity : Finset (Smax ⧸ P.subgroupOf Smax) :=
              Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax)
            ∀ x, x ∈ nonidentity → gamma x = 0 ∨ gamma x = 1 := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  dsimp only
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
    Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
  intro x hx
  rcases
      hypothesis_13_1_betaNorm_inducedPrincipal_quotient_conjugacy_support_source
        hSTypeP hFrobAlt C u hC hCbot hBarU x (by simpa using hx) with
    hxnot | hcard
  · left
    simpa [gamma] using
      hypothesis_13_1_inducedCF_eq_zero_of_not_mem_conjugates
        Hbar (Section1.principalCharacter Hbar) hxnot
  · right
    simpa [gamma] using
      hypothesis_13_1_inducedCF_principal_eq_one_of_conjugator_card
        Hbar x hcard

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_one_values_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
              Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
            let nonidentity : Finset (Smax ⧸ P.subgroupOf Smax) :=
              Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax)
            (nonidentity.filter (fun x => gamma x = 1)).card =
                u * (Nat.card W1 - 1) ∧
              ∀ x, x ∈ nonidentity → gamma x = 0 ∨ gamma x = 1 := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  constructor
  · exact
      hypothesis_13_1_betaNorm_inducedPrincipal_quotient_one_values_card_source
        hSTypeP hFrobAlt C u hC hCbot hBarU
  · exact
      hypothesis_13_1_betaNorm_inducedPrincipal_quotient_nonidentity_values_source
        hSTypeP hFrobAlt C u hC hCbot hBarU

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_support_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
              Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
            ∃ support : Finset (Smax ⧸ P.subgroupOf Smax),
              support ⊆ Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax) ∧
                support.card = u * (Nat.card W1 - 1) ∧
                  (∀ x,
                    x ∈ Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax) →
                      x ∉ support → gamma x = 0) ∧
                    (∀ x, x ∈ support → gamma x = 1) := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
    Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
  rcases
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_one_values_source
      hSTypeP hFrobAlt C u hC hCbot hBarU with
    ⟨hcard, hvalues⟩
  exact
    section13_support_package_of_one_values gamma u (Nat.card W1)
      hcard hvalues

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_nonidentity_sum_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
              Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
            (∑ x ∈ Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax),
                Complex.normSq (gamma x)) =
              (u : ℝ) * ((Nat.card W1 : ℝ) - 1) := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
    Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
  rcases
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_support_source
      hSTypeP hFrobAlt C u hC hCbot hBarU with
    ⟨support, hsub, hcard, hzero, hone⟩
  exact
    section13_nonidentity_normSq_sum_of_support gamma support u (Nat.card W1)
      (Nat.card_pos (α := W1)) hsub hcard hzero hone

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_count_data_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) :=
      Classical.decEq _
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
              Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
            Nat.card (Smax ⧸ P.subgroupOf Smax) = u * Nat.card W1 ∧
              Complex.normSq (gamma 1) = (u : ℝ) ^ (2 : ℕ) ∧
                (∑ x ∈ Finset.univ.erase (1 : Smax ⧸ P.subgroupOf Smax),
                    Complex.normSq (gamma x)) =
                  (u : ℝ) * ((Nat.card W1 : ℝ) - 1) := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
    Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
  exact
    ⟨hypothesis_13_1_betaNorm_inducedPrincipal_quotient_card_source
        hSTypeP C u hC hCbot hBarU,
      hypothesis_13_1_betaNorm_inducedPrincipal_quotient_gamma_identity_source
        hSTypeP C u hC hCbot hBarU,
      hypothesis_13_1_betaNorm_inducedPrincipal_quotient_nonidentity_sum_source
        hSTypeP hFrobAlt C u hC hCbot hBarU⟩

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_count_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
              ((P ⊔ W1).subgroupOf Smax).map
                (QuotientGroup.mk' (P.subgroupOf Smax))
            Section5.cfNormSq
                (Section1.inducedCF Hbar (Section1.principalCharacter Hbar)) =
                ((u - 1 : ℕ) : ℝ) /
                    (Nat.card W1 : ℝ) + 1 := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  letI : DecidableEq (Smax ⧸ P.subgroupOf Smax) := Classical.decEq _
  intro C u hC hCbot hBarU
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  let gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
    Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
  rcases
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_count_data_source
      hSTypeP hFrobAlt C u hC hCbot hBarU with
    ⟨hQcard, hgamma1, hsum_nonid⟩
  exact
    section13_cfNormSq_of_quotient_principal_count_data
      gamma u (Nat.card W1) hQcard
      (Section9.quotientBarUCardinality_card_pos_sec9 U C u hBarU)
      (Nat.card_pos (α := W1)) hgamma1 hsum_nonid

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_quotient_norm_count_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    letI : (P.subgroupOf Smax).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
            ∀ gamma : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax),
              (∀ s : Smax,
                Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) s =
                  gamma (QuotientGroup.mk' (P.subgroupOf Smax) s)) →
                Section5.cfNormSq
                    (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) =
                  ((u - 1 : ℕ) : ℝ) /
                      (Nat.card W1 : ℝ) + 1 := by
  
  classical
  letI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  intro C u hC hCbot hBarU gamma hgamma
  let phi : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))
  have hphi : phi = fun s : Smax => gamma (QuotientGroup.mk' (P.subgroupOf Smax) s) := by
    funext s
    exact hgamma s
  rw [show
      Section5.cfNormSq
          (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) =
        Section5.cfNormSq phi by rfl]
  rw [hphi]
  rw [section13_cfNormSq_inflation_quotient_eq (P.subgroupOf Smax) gamma]
  let Hbar : Subgroup (Smax ⧸ P.subgroupOf Smax) :=
    ((P ⊔ W1).subgroupOf Smax).map
      (QuotientGroup.mk' (P.subgroupOf Smax))
  let gamma0 : Section1.ClassFunction (Smax ⧸ P.subgroupOf Smax) :=
    Section1.inducedCF Hbar (Section1.principalCharacter Hbar)
  have hgamma0 :
      ∀ s : Smax,
        Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) s =
          gamma0 (QuotientGroup.mk' (P.subgroupOf Smax) s) := by
    intro s
    exact
      by
        simpa [Hbar, gamma0] using
          hypothesis_13_1_betaNorm_inducedPrincipal_cfIndMod_source
            hSTypeP s
  have hgamma_eq : gamma = gamma0 := by
    funext q
    rcases QuotientGroup.mk'_surjective (N := P.subgroupOf Smax) q with
      ⟨s, rfl⟩
    exact (hgamma s).symm.trans (hgamma0 s)
  rw [hgamma_eq]
  exact
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_count_source
      hSTypeP hFrobAlt C u hC hCbot hBarU

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_cardQuotient_core_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hFrobAlt : U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1) :
    ∀ (C : Subgroup G) (u : ℕ),
      C = subgroupCentralizerIn U P →
        C = ⊥ →
          Section9.quotientBarUCardinality U C u →
          Section5.cfNormSq
              (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) =
            ((u - 1 : ℕ) : ℝ) /
                (Nat.card W1 : ℝ) + 1 := by
  
  intro C u hC hCbot hBarU
  rcases hypothesis_13_1_betaNorm_inducedPrincipal_Dgamma_source hSTypeP with
    ⟨gamma, hgamma⟩
  exact
    hypothesis_13_1_betaNorm_inducedPrincipal_quotient_norm_count_source
      hSTypeP hFrobAlt C u hC hCbot hBarU gamma hgamma

private theorem hypothesis_13_1_typeP_U_le_normalizer_MF
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (htype : Section8.typePData M MF U W1 W2) :
    U ≤ Subgroup.normalizer (MF : Set G) := by
  rcases htype with ⟨hMF, hCommon⟩
  rcases hCommon with
    ⟨_hHallD, _hMFleD, hCompMFU, _hUnil, _hW1norm, _hW1cyc,
      _hW1card, _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      _hW2le, _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6,
      _hW2Second⟩
  rcases hMF with ⟨⟨hMFM, hMFNormalM, _hMFnil, _hMFHall⟩, _hmax⟩
  have hDleM : ambientDerivedSubgroup M ≤ M := section12_ambientDerivedSubgroup_le
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFNormalM
  exact hCompMFU.2.1.trans (hDleM.trans hM_le_norm_MF)

private theorem hypothesis_13_1_subgroupCentralizerIn_subgroupOf_normal_of_le_normalizer
    {G : Type u} [Group G]
    {U P : Subgroup G}
    (hUnormP : U ≤ Subgroup.normalizer (P : Set G)) :
    ((subgroupCentralizerIn U P).subgroupOf U).Normal := by
  classical
  let C : Subgroup G := subgroupCentralizerIn U P
  have hCU : C ≤ U := inf_le_left
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hCU).2 ?_
  intro u huU
  have huNormP : u ∈ Subgroup.normalizer (P : Set G) := hUnormP huU
  have huInvNormP : u⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem huNormP
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hxC
    refine ⟨U.mul_mem (U.mul_mem huU hxC.1) (U.inv_mem huU), ?_⟩
    change u * x * u⁻¹ ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have hp_conj : u⁻¹ * p * u ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp huInvNormP p).1 hpP
    have hcomm : (u⁻¹ * p * u) * x = x * (u⁻¹ * p * u) :=
      Subgroup.mem_centralizer_iff.mp hxC.2 (u⁻¹ * p * u) hp_conj
    calc
      p * (u * x * u⁻¹) = u * ((u⁻¹ * p * u) * x) * u⁻¹ := by group
      _ = u * (x * (u⁻¹ * p * u)) * u⁻¹ := by rw [hcomm]
      _ = (u * x * u⁻¹) * p := by group
  · intro hxC
    have hUinvInv : (u⁻¹)⁻¹ ∈ U := by simpa using huU
    have hx' : u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹ ∈ C := by
      refine ⟨?_, ?_⟩
      · exact U.mul_mem (U.mul_mem (U.inv_mem huU) hxC.1) hUinvInv
      · change u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹ ∈
          Subgroup.centralizer (P : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro p hpP
        have hp_conj : u * p * u⁻¹ ∈ P := by
          simpa using (Subgroup.mem_normalizer_iff.mp huNormP p).1 hpP
        have hcomm : (u * p * u⁻¹) * (u * x * u⁻¹) =
            (u * x * u⁻¹) * (u * p * u⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hxC.2 (u * p * u⁻¹) hp_conj
        calc
          p * (u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹) =
              u⁻¹ * ((u * p * u⁻¹) * (u * x * u⁻¹)) * u := by group
          _ = u⁻¹ * ((u * x * u⁻¹) * (u * p * u⁻¹)) * u := by rw [hcomm]
          _ = (u⁻¹ * (u * x * u⁻¹) * (u⁻¹)⁻¹) * p := by group
    simpa [C, mul_assoc] using hx'

private theorem hypothesis_13_1_quotientBarUCardinality_of_typeP_card
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U C : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hC : C = subgroupCentralizerIn U P)
    {u c : ℕ}
    (hU : Nat.card U = u * c)
    (hc : c = Nat.card C) :
    Section9.quotientBarUCardinality U C u := by
  classical
  subst C
  have hCU : subgroupCentralizerIn U P ≤ U := inf_le_left
  have hUnormP : U ≤ Subgroup.normalizer (P : Set G) :=
    hypothesis_13_1_typeP_U_le_normalizer_MF (M := Smax) (MF := P)
      (U := U) (W1 := W1) (W2 := W2) hSTypeP
  have hnormal :
      ((subgroupCentralizerIn U P).subgroupOf U).Normal :=
    hypothesis_13_1_subgroupCentralizerIn_subgroupOf_normal_of_le_normalizer
      hUnormP
  refine ⟨hCU, hnormal, ?_⟩
  letI : ((subgroupCentralizerIn U P).subgroupOf U).Normal := hnormal
  have hcard_sub :
      Nat.card ((subgroupCentralizerIn U P).subgroupOf U) =
        Nat.card (subgroupCentralizerIn U P) :=
    natCard_subgroupOf_eq (subgroupCentralizerIn U P) U hCU
  have hlag : Nat.card U =
      Nat.card (U ⧸ (subgroupCentralizerIn U P).subgroupOf U) *
        Nat.card ((subgroupCentralizerIn U P).subgroupOf U) := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((subgroupCentralizerIn U P).subgroupOf U)
  rw [hcard_sub, ← hc] at hlag
  rw [hU] at hlag
  have hcpos : 0 < c := by
    rw [hc]
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hcpos hlag.symm


private theorem hypothesis_13_1_betaNorm_inducedPrincipal_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (_hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (_hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (_hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (_hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (_hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (_hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (C : Subgroup G) (u c : ℕ),
      C = subgroupCentralizerIn U P →
        Nat.card U = u * c →
          c = Nat.card C →
            Section5.cfNormSq
                (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                  (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) =
              ((u - 1 : ℕ) : ℝ) / (Nat.card W1 : ℝ) + 1 := by
  intro C u c hC hU hc
  have hSmax : Smax ∈ section9MaximalSubgroups G := by
    rcases _hcase with
      ⟨_hprod, _hWcyc, _hW1ne, _hW2ne, _hnorm, hSmax, _hTmax, _hSF, _hTF,
        _hSnotI, _hTnotI, _hSeq, _hTeq, _hSdisj, _hTdisj, _hW2le, _hW1le,
        _hST, _hcover, _hTypeII, _hSType, _hTType, _hCommon⟩
    exact hSmax
  have hTypePDef : Section8.typePDefinitionData Smax P U W1 W2 :=
    hypothesis_13_1_typePDefinitionData_of_maximal_typeP _hmin hSmax hSTypeP
  have hFrobAlt :
      U = ⊥ ∨ section12FrobeniusJoinWithKernel U W1 := by
    by_cases hU : U = ⊥
    · exact Or.inl hU
    · exact Or.inr
        (Section8.typePDefinitionData_frobeniusJoinWithKernel hTypePDef hU)
  have hCbot : C = ⊥ := hC.trans hCentralizerBot
  have hBarU : Section9.quotientBarUCardinality U C u :=
    hypothesis_13_1_quotientBarUCardinality_of_typeP_card hSTypeP hC hU hc
  exact
    hypothesis_13_1_betaNorm_inducedPrincipal_cardQuotient_core_source
      hSTypeP hFrobAlt C u hC hCbot hBarU

private theorem hypothesis_13_1_subgroupInKernel_inducedCF_of_source
    {G : Type u} [Group G] [Finite G]
    (H A : Subgroup G)
    [Finite H]
    [hA : A.Normal]
    (hAH : A ≤ H)
    (θ : Section1.ClassFunction H)
    (hθker : Section1.subgroupInKernel' θ (A.subgroupOf H)) :
    Section1.subgroupInKernel' (Section1.inducedCF H θ) A := by
  classical
  intro a
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hindex : (Subgroup.index H : ℂ) * Nat.card H = Nat.card G := by
    exact_mod_cast H.index_mul_card
  have hxA : ∀ x : G, x * (a : G) * x⁻¹ ∈ A := by
    intro x
    simpa using hA.conj_mem (a : G) a.2 x
  have hxH : ∀ x : G, x * (a : G) * x⁻¹ ∈ H :=
    fun x => hAH (hxA x)
  have hsum :
      (∑ x : G,
          if hx : x * (a : G) * x⁻¹ ∈ H then
            θ ⟨x * (a : G) * x⁻¹, hx⟩
          else
            0) = ∑ _x : G, Section1.degree θ := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [dif_pos (hxH x)]
    exact hθker ⟨⟨x * (a : G) * x⁻¹, hxH x⟩,
      Subgroup.mem_subgroupOf.mpr (hxA x)⟩
  calc
    Section1.inducedCF H θ a
        = (Nat.card H : ℂ)⁻¹ * ((Nat.card G : ℂ) * Section1.degree θ) := by
          unfold Section1.inducedCF Section1.inducedClassFunction
          rw [hsum]
          simp [Finset.card_univ]
    _ = ((Nat.card H : ℂ)⁻¹ * (Nat.card G : ℂ)) * Section1.degree θ := by
          ring
    _ = (Subgroup.index H : ℂ) * Section1.degree θ := by
          apply congrArg (fun z => z * Section1.degree θ)
          rw [← hindex]
          field_simp [hcardH]
    _ = Section1.degree (Section1.inducedCF H θ) := by
          rw [Section1.degree_inducedClassFunction H θ]

public theorem hypothesis_13_1_subgroupInKernel_of_irreducible_constituent_of_kernel_character
    {K : Type u} [Group K] [Finite K]
    (B : Subgroup K)
    (φ χ : Section1.ClassFunction K)
    (hφirr : Section1.IsIrreducibleCharacterOnGroup φ)
    (hχchar : Section1.IsCharacter χ)
    (hχker : Section1.subgroupInKernel' χ B)
    (hsp : Section1.scalarProduct K φ χ ≠ 0) :
    Section1.subgroupInKernel' φ B := by
  classical
  rcases hφirr with ⟨_nφ, φρ, hφρirr, hφeq⟩
  rcases hχchar with ⟨_Vχ, _haddχ, _hmodχ, _hfdχ, χρ, hχeq⟩
  have hsp_swap : Section1.scalarProduct K χ φ ≠ 0 :=
    (Section1.scalarProduct_ne_zero_swap (G := K) φ χ).mp hsp
  have hhom_ne : Module.finrank ℂ (Representation.IntertwiningMap φρ χρ) ≠ 0 := by
    intro hzero
    apply hsp_swap
    rw [hχeq, hφeq, Section1.scalarProduct_representation_char_eq_finrank φρ χρ]
    exact_mod_cast hzero
  have hexists : ∃ f : Representation.IntertwiningMap φρ χρ, f ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hsub : Subsingleton (Representation.IntertwiningMap φρ χρ) := by
      refine ⟨fun f g => ?_⟩
      rw [hnone f, hnone g]
    exact hhom_ne (Module.finrank_zero_of_subsingleton)
  rcases hexists with ⟨f, hfne⟩
  letI : Representation.IsIrreducible φρ := hφρirr
  have hfinj : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero f with hfinj | hfzero
    · exact hfinj
    · exact (hfne hfzero).elim
  have hχρker : Section1.subgroupInRepresentationKernel χρ B :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel χρ B).mp
      (by simpa [hχeq] using hχker)
  have hφρker : Section1.subgroupInRepresentationKernel φρ B := by
    intro b
    apply LinearMap.ext
    intro v
    apply hfinj
    calc
      f (φρ (b : K) v) = χρ (b : K) (f v) := by
        simpa using
          (Representation.IntertwiningMap.isIntertwining
            (ρ := φρ) (σ := χρ) f (b : K) v)
      _ = f v := by
        rw [hχρker b]
        rfl
  rw [hφeq]
  exact (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel φρ B).mpr
    hφρker

private theorem hypothesis_13_1_betaNorm_selected_xChar_not_subgroupInKernel_source
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction Smax}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τS)
    (xChar : J → Section1.ClassFunction (derivedSubgroup Smax))
    (h45a : Section4Scratch.theorem_4_5_a_statement
      (derivedSubgroup Smax) μsel xChar) :
    ∀ j : J, j ≠ j0 →
      ¬ Section1.subgroupInKernel' (xChar j)
        ((P.subgroupOf Smax).subgroupOf (derivedSubgroup Smax)) := by
  classical
  rcases hSTypeP with ⟨hMF, hCommon⟩
  rcases hCommon with
    ⟨_hHallD, hPleAmbient, hCompMFU, _hUnil, _hW1norm, _hW1cyc,
      _hW1card, _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2leP, _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6,
      _hW2Second⟩
  have hDerEq : ambientDerivedSubgroup Smax = P ⊔ U := hCompMFU.2.2.1
  have hPleDer : P.subgroupOf Smax ≤ derivedSubgroup Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxPU : (x : G) ∈ (P ⊔ U : Subgroup G) :=
      (le_sup_left : P ≤ P ⊔ U) hxP
    have hxDerG : (x : G) ∈ ambientDerivedSubgroup Smax := by
      simpa [hDerEq] using hxPU
    have hxDerSub : x ∈ (ambientDerivedSubgroup Smax).subgroupOf Smax := by
      simpa [Subgroup.mem_subgroupOf] using hxDerG
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := Smax)]
      using hxDerSub
  rcases hNotation with
    ⟨_MFsrc, Ms, _Abook, _A0book, _A1book, hSource,
      _hW, _hA0, h46, _hωNotation, _hIsoNotation, _hVirtNotation,
      _hPrinNotation, _hSigmaAgree, _h45Notation, _h48Notation,
      _hTauIsoNotation, hPackage⟩
  rcases hSource with
    ⟨_hApre, _hA0sub, hSourceNotation, _hTauSource⟩
  rcases hPackage with
    ⟨σM, _xCharFull, _H_A, _H_A0, hSupported, _hGalois⟩
  rcases hSupported with
    ⟨_h46Full, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hSupportedRest⟩
  rcases hSupportedRest with
    ⟨hω, h43b, h43c, _h43d, _h45aFull, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  have hMFsrcEq : _MFsrc = P :=
    section16MFSubgroup_unique hSourceNotation.2.1 hMF
  subst _MFsrc
  have hPleMs : P ≤ Ms := by
    rcases hSourceNotation.2.2.1.to_literal with hEarly | hLate
    · rw [hEarly.2]
    · rw [hLate.2]
      exact hPleAmbient
  have hPleMsSub : P.subgroupOf Smax ≤ Ms.subgroupOf Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using hPleMs hxP
  have h46P :
      Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        Wsec
        (P.subgroupOf Smax)
        A := by
    rcases h46 with ⟨h42, _hKnormal, _hW2leK, _hKleK, hUnionK, hAsub⟩
    refine ⟨h42, Section12.section16MFSubgroup_subgroupOf_normal hMF, ?_,
      hPleDer, ?_, hAsub⟩
    · intro x hx
      have hxW2 : (x : G) ∈ W2 := by
        simpa [Subgroup.mem_subgroupOf] using hx
      simpa [Subgroup.mem_subgroupOf] using hW2leP hxW2
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨h, hxcentral⟩
      let k : {k : Ms.subgroupOf Smax // (k : Smax) ≠ 1} :=
        ⟨⟨(h.1 : Smax), hPleMsSub h.1.2⟩, by
          simpa using h.2⟩
      exact hUnionK (Set.mem_iUnion.mpr ⟨k, by simpa [k] using hxcentral⟩)
  have h47full :
      Section4Scratch.theorem_4_7_full_statement
        (derivedSubgroup Smax)
        (P.subgroupOf Smax)
        A
        j0 μsel xChar :=
    Section4Scratch.theorem_4_7_full
      (K := derivedSubgroup Smax)
      (W1 := W1.subgroupOf Smax)
      (W2 := W2.subgroupOf Smax)
      (W := Wsec)
      (H := P.subgroupOf Smax)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ωsec)
      (σ := σM)
      (piChar := μsel)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      h46P h45a hω h43b h43c
  intro j hj
  exact (h47full.2 j hj).1

private theorem hypothesis_13_1_betaNorm_selected_mu_zero_row_not_subgroupInKernel
    {G : Type u} [Group G] [Finite G]
    {W1 W2 Smax P U : Subgroup G}
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Wsec : Subgroup Smax} {A A0 : Set Smax} {i0 : I} {j0 : J}
    {μsel : I → J → Section1.ClassFunction Smax}
    {δSign : J → ℤ}
    {ωsec : I → J → Section1.ClassFunction Wsec}
    {σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G}
    (hNotation : Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsec
      A A0 i0 j0 μsel δSign ωsec σsec τS) :
    ∀ j : J, j ≠ j0 →
      ¬ Section1.subgroupInKernel' (μsel i0 j) (P.subgroupOf Smax) := by
  classical
  have hSTypePCopy := hSTypeP
  have hDerEq : ambientDerivedSubgroup Smax = P ⊔ U := by
    rcases hSTypeP with ⟨_hMF, hCommon⟩
    rcases hCommon with
      ⟨_hHallD, _hMFleD, hCompMFU, _hUnil, _hWleftNorm, _hWleftCyc,
        _hWleftCard, _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD,
        _hWrightLeMF, _hWrightNe, _hWrightCyc, _hCentralizer, _hHatW,
        _hT6, _hWrightSecond⟩
    exact hCompMFU.2.2.1
  have hPleDer : P.subgroupOf Smax ≤ derivedSubgroup Smax := by
    intro x hx
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxPU : (x : G) ∈ (P ⊔ U : Subgroup G) := by
      exact (le_sup_left : P ≤ P ⊔ U) hxP
    have hxDerG : (x : G) ∈ ambientDerivedSubgroup Smax := by
      simpa [hDerEq] using hxPU
    have hxDerSub : x ∈ (ambientDerivedSubgroup Smax).subgroupOf Smax := by
      simpa [Subgroup.mem_subgroupOf] using hxDerG
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := Smax)]
      using hxDerSub
  have hNotationFull := hNotation
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin,
      _hσAgreeCyc, h45, _h48, _hTauIso, _hFull⟩
  rcases h45 with ⟨xChar, h45a, _h45b⟩
  have hnotker :=
    hypothesis_13_1_betaNorm_selected_xChar_not_subgroupInKernel_source
      hSTypePCopy hNotationFull xChar h45a
  rcases h45a with ⟨hres, _hirrX, _hindX⟩
  intro j hj hker
  apply hnotker j hj
  have hresKer :
      Section1.subgroupInKernel'
        (Section1.subgroupRestriction (derivedSubgroup Smax) (μsel i0 j))
        ((P.subgroupOf Smax).subgroupOf (derivedSubgroup Smax)) :=
    by
      intro a
      let aP : P.subgroupOf Smax := ⟨a.1, by
        -- a.2 : a.1 ∈ (P.subgroupOf Smax).subgroupOf (derivedSubgroup Smax)
        -- = (P.subgroupOf Smax).comap (derivedSubgroup Smax).subtype
        have ha_smax : (derivedSubgroup Smax).subtype a.1 ∈ P.subgroupOf Smax :=
          (Subgroup.mem_comap (f := (derivedSubgroup Smax).subtype)).mp a.2
        dsimp at ha_smax ⊢
        exact ha_smax⟩
      simpa [Section1.subgroupRestriction, Section1.degree, aP] using hker aP
  exact Section1.subgroupInKernel'_of_eq (hres i0 j) hresKer

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_mu_left_orthogonal_core_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) (j : ℕ),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          0 < j →
            j < Nat.card W2 →
              Section1.scalarProduct Smax
                  (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)))
                  (μ 0 j) = 0 := by
  classical
  intro ω η μ ν μsum νsum δ δ' σ j hnotation hj0 hj
  have hnotationFull := hnotation
  have hnotationAlign := hnotation
  rcases hnotation with
    ⟨hωData, _hσmap, _hη, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  have hωSelected := hωData
  rcases hωData with ⟨_h31, hqpos, _hppos, _ωFin, _hωFin, _hωNat⟩
  have hFourSixSAlign := hFourSixS
  rcases hFourSixS with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, μsel,
      δSign, ωsec, σsec, hSelNotation, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hypothesis_13_1_typePFourSixTableIndexing_source
      hSTypeP ω hωSelected τS Wsec A A0 i0 j0 μsel δSign ωsec σsec
      hSelNotation with
    ⟨row, col, hrow0, hcol0, hcol_ne, _hcol_inj, hrow_inj, hrow_surj,
      hcol_surj, hIndTransport, hExactTransport⟩
  let χ : ℕ → ℕ → Section1.ClassFunction Smax :=
    fun i j => μsel (row i) (col j)
  let δsel : ℕ → ℤ := fun j => δSign (col j)
  let ωsel : ℕ → ℕ → Section1.ClassFunction Wsec :=
    fun i j => ωsec (row i) (col j)
  have hSelected :
      hypothesis_13_1_selectedTypePFourSixTableData hSTypeP ω hωSelected τS
        χ δsel Wsec ωsel σsec :=
    hypothesis_13_1_selectedTypePFourSixTableData_of_package
      hSTypeP ω hωSelected τS hSelNotation row col hrow0 hcol0 hcol_ne
      hrow_inj hrow_surj hcol_surj hIndTransport hExactTransport
  have hAlign0 : μ 0 j = μsel (row 0) (col j) :=
    hypothesis_13_1_dadeDifferencePointwiseMuAlignment_s_side_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixSAlign hFourSixT
      ω η μ ν μsum νsum δ δ' σ hnotationAlign χ δsel Wsec ωsel σsec
      hSelected 0 j hqpos hj0 hj
  let H : Subgroup Smax := (P ⊔ W1).subgroupOf Smax
  have hP_le_H : P ≤ P ⊔ W1 := le_sup_left
  have hP_sub_H :
      P.subgroupOf Smax ≤ H := by
    intro x hx
    change (x : G) ∈ P ⊔ W1
    exact hP_le_H hx
  haveI : (P.subgroupOf Smax).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hSTypeP.1
  have hIndChar : Section1.IsCharacter
      (Section1.inducedCF H (Section1.principalCharacter H)) := by
    exact Section1.isCharacter_inducedCF_of_isCharacter H
      (Section1.principalCharacter H)
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
        (Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := H)))
  by_contra hne
  have hsp_ne :
      Section1.scalarProduct Smax
          (Section1.inducedCF H (Section1.principalCharacter H)) (μ 0 j) ≠ 0 := by
    exact hne
  have hsp_ne_swap :
      Section1.scalarProduct Smax (μ 0 j)
          (Section1.inducedCF H (Section1.principalCharacter H)) ≠ 0 :=
    (Section1.scalarProduct_ne_zero_swap (G := Smax)
      (Section1.inducedCF H (Section1.principalCharacter H)) (μ 0 j)).mp hsp_ne
  have hmu_kernel :
      Section1.subgroupInKernel' (μ 0 j) (P.subgroupOf Smax) :=
    hypothesis_13_1_subgroupInKernel_of_irreducible_constituent_of_kernel_character
      (P.subgroupOf Smax)
      (μ 0 j)
      (Section1.inducedCF H (Section1.principalCharacter H))
      (hμirr 0 j hqpos hj)
      hIndChar
      (by
        have hprincipalKernel :
            Section1.subgroupInKernel'
              (Section1.principalCharacter H) ((P.subgroupOf Smax).subgroupOf H) := by
          intro a
          rfl
        exact hypothesis_13_1_subgroupInKernel_inducedCF_of_source
          H (P.subgroupOf Smax) hP_sub_H
          (Section1.principalCharacter H) hprincipalKernel)
      hsp_ne_swap
  have hsel_kernel :
      Section1.subgroupInKernel' (μsel (row 0) (col j)) (P.subgroupOf Smax) :=
    Section1.subgroupInKernel'_of_eq hAlign0 hmu_kernel
  exact
    (hypothesis_13_1_betaNorm_selected_mu_zero_row_not_subgroupInKernel
      hSTypeP hSelNotation (col j) (hcol_ne j hj0 hj))
      (by simpa [hrow0] using hsel_kernel)

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_mu_left_orthogonal_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) (j : ℕ),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          0 < j →
            j < Nat.card W2 →
              Section1.scalarProduct Smax
                  (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)))
                  (μ 0 j) = 0 := by
  /-
  Checked wrapper around the S-side Type-P scalar-product source boundary.
  -/
  exact
    hypothesis_13_1_betaNorm_inducedPrincipal_mu_left_orthogonal_core_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
      hDadeS hDadeT hFourSixS hFourSixT

private theorem hypothesis_13_1_betaNorm_inducedPrincipal_mu_orthogonal_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
      (η : ℕ → ℕ → Section1.ClassFunction G)
      (μ : ℕ → ℕ → Section1.ClassFunction Smax)
      (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
      (μsum : ℕ → Section1.ClassFunction Smax)
      (νsum : ℕ → Section1.ClassFunction Tmax)
      (δ δ' : ℕ → ℤ)
      (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) (j : ℕ),
        hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
            (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
          0 < j →
            j < Nat.card W2 →
              Section1.scalarProduct Smax
                  (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)))
                  (μ 0 j) = 0 ∧
                Section1.scalarProduct Smax (μ 0 j)
                  (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                    (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))) = 0 := by
  intro ω η μ ν μsum νsum δ δ' σ j hnotation hj0 hj
  let γ : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))
  have hleft : Section1.scalarProduct Smax γ (μ 0 j) = 0 := by
    simpa [γ] using
      hypothesis_13_1_betaNorm_inducedPrincipal_mu_left_orthogonal_s_side_source
        hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
        hDadeS hDadeT hFourSixS hFourSixT
        ω η μ ν μsum νsum δ δ' σ j hnotation hj0 hj
  have hstar :
      star (Section1.scalarProduct Smax (μ 0 j) γ) = 0 := by
    simpa [hleft] using Section1.scalarProduct_star_swap (G := Smax) γ (μ 0 j)
  have hright : Section1.scalarProduct Smax (μ 0 j) γ = 0 := by
    simpa using congrArg star hstar
  exact ⟨hleft, hright⟩

private theorem hypothesis_13_1_betaNorm_difference_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (C : Subgroup G) (u c : ℕ),
      C = subgroupCentralizerIn U P →
          Nat.card U = u * c →
            c = Nat.card C →
              ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
                (η : ℕ → ℕ → Section1.ClassFunction G)
                (μ : ℕ → ℕ → Section1.ClassFunction Smax)
                (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
                (μsum : ℕ → Section1.ClassFunction Smax)
                (νsum : ℕ → Section1.ClassFunction Tmax)
                (δ δ' : ℕ → ℤ)
                (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) (j : ℕ),
                  hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
                      (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
                    0 < j →
                      j < Nat.card W2 →
                        Section5.cfNormSq
                          (Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                              μ 0 j) =
                            ((u - 1 : ℕ) : ℝ) / (Nat.card W1 : ℝ) + 2 := by
  intro C u c hC hU hc ω η μ ν μsum νsum δ δ' σ j hnotation hj0 hj
  let γ : Section1.ClassFunction Smax :=
    Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
      (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax))
  have horth :
      Section1.scalarProduct Smax γ (μ 0 j) = 0 ∧
        Section1.scalarProduct Smax (μ 0 j) γ = 0 := by
    simpa [γ] using
      hypothesis_13_1_betaNorm_inducedPrincipal_mu_orthogonal_s_side_source
        hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
        hDadeS hDadeT hFourSixS hFourSixT
        ω η μ ν μsum νsum δ δ' σ j hnotation hj0 hj
  have hγnorm :
      Section5.cfNormSq γ =
        ((u - 1 : ℕ) : ℝ) / (Nat.card W1 : ℝ) + 1 := by
    simpa [γ] using
      hypothesis_13_1_betaNorm_inducedPrincipal_s_side_source
        hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker
        hDadeS hDadeT hFourSixS hFourSixT hCentralizerBot C u c hC hU hc
  have hμnorm : Section5.cfNormSq (μ 0 j) = 1 :=
    hypothesis_13_1_cfNormSq_mu_zero_row_eq_one hnotation j hj
  change Section5.cfNormSq (γ - μ 0 j) =
    ((u - 1 : ℕ) : ℝ) / (Nat.card W1 : ℝ) + 2
  calc
    Section5.cfNormSq (γ - μ 0 j) =
        Section5.cfNormSq γ + Section5.cfNormSq (μ 0 j) :=
      Section5.cfNormSq_sub_eq_add_of_orthogonal horth.1 horth.2
    _ = (((u - 1 : ℕ) : ℝ) / (Nat.card W1 : ℝ) + 1) + 1 := by
      rw [hγnorm, hμnorm]
    _ = ((u - 1 : ℕ) : ℝ) / (Nat.card W1 : ℝ) + 2 := by
      ring

private theorem hypothesis_13_1_betaNorm_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (C : Subgroup G) (u c : ℕ),
      C = subgroupCentralizerIn U P →
          Nat.card U = u * c →
            c = Nat.card C →
              ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
                (η : ℕ → ℕ → Section1.ClassFunction G)
                (μ : ℕ → ℕ → Section1.ClassFunction Smax)
                (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
                (μsum : ℕ → Section1.ClassFunction Smax)
                (νsum : ℕ → Section1.ClassFunction Tmax)
                (δ δ' : ℕ → ℤ)
                (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
                (βS : Section1.ClassFunction Smax) (j : ℕ),
                  hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
                      (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
                    0 < j →
                      j < Nat.card W2 →
                        βS = Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                              μ 0 j →
                          Section5.cfNormSq βS =
                            ((u - 1 : ℕ) : ℝ) / (Nat.card W1 : ℝ) + 2 := by
  /-
  Checked wrapper around `norm_beta`: rewrite an externally supplied `βS`
  to the actual beta expression before applying the source norm computation.
  -/
  intro C u c hC hU hc ω η μ ν μsum νsum δ δ' σ βS j hnotation hj0 hj hβS
  rw [hβS]
  exact
    hypothesis_13_1_betaNorm_difference_s_side_source hmin hcase hSTypeP
      hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS
      hFourSixT hCentralizerBot C u c hC hU hc
      ω η μ ν μsum νsum δ δ' σ j hnotation hj0 hj

private theorem hypothesis_13_1_betaSupportNormDataFor_s_side_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hCentralizerBot : subgroupCentralizerIn U P = ⊥) :
    ∀ (C : Subgroup G) (u c : ℕ),
      C = subgroupCentralizerIn U P →
          Nat.card U = u * c →
            c = Nat.card C →
              ∀ (ω : ℕ → ℕ → Section1.ClassFunction W)
                (η : ℕ → ℕ → Section1.ClassFunction G)
                (μ : ℕ → ℕ → Section1.ClassFunction Smax)
                (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
                (μsum : ℕ → Section1.ClassFunction Smax)
                (νsum : ℕ → Section1.ClassFunction Tmax)
                (δ δ' : ℕ → ℤ)
                (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
                (βS : Section1.ClassFunction Smax) (j : ℕ),
                  hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
                      (Nat.card W2) (Nat.card W1) ω η μ ν μsum νsum δ δ' σ →
                    0 < j →
                      j < Nat.card W2 →
                        βS = Section1.inducedCF ((P ⊔ W1).subgroupOf Smax)
                            (Section1.principalCharacter ((P ⊔ W1).subgroupOf Smax)) -
                              μ 0 j →
                          Section1.supportedOn βS
                              (subgroupSetPreimage Smax
                                (theorem_13_18_betaSupportSet Smax W W1 W2 P)) ∧
                            Section5.cfNormSq βS =
                              ((u - 1 : ℕ) : ℝ) / (Nat.card W1 : ℝ) + 2 := by
  intro C u c hC hU hc ω η μ ν μsum νsum δ δ' σ βS j hnotation hj0 hj hβS
  constructor
  · rw [hβS]
    exact
      hypothesis_13_1_betaSupportSet_s_side_source hmin hcase hSTypeP hTTypeP
        Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
        hCentralizerBot ω η μ ν μsum νsum δ δ' σ hnotation j hj0 hj
  · exact
      hypothesis_13_1_betaNorm_s_side_source hmin hcase hSTypeP hTTypeP
        Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT
        hCentralizerBot C u c hC hU hc
        ω η μ ν μsum νsum δ δ' σ βS j hnotation hj0 hj hβS

public theorem hypothesis_13_1_betaSupportNormDataFor_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT)
    (hSCentralizerBot : subgroupCentralizerIn U P = ⊥)
    (hTCentralizerBot : subgroupCentralizerIn V Q = ⊥) :
    ∀ (C D : Subgroup G) (u v c d : ℕ),
      C = subgroupCentralizerIn U P →
        D = subgroupCentralizerIn V Q →
          Nat.card U = u * c →
            Nat.card V = v * d →
              c = Nat.card C →
                d = Nat.card D →
                  hypothesis_13_1_betaSupportNormDataFor Smax Tmax W W1 W2
                    P Q (Nat.card W2) (Nat.card W1) u v := by
  intro C D u v c d hC hD hU hV hc hd
  refine ⟨?_, ?_⟩
  · intro ω η μ ν μsum νsum δ δ' σ βS j hnotation hj0 hj hβS
    exact
      hypothesis_13_1_betaSupportNormDataFor_s_side_source hmin hcase
        hSTypeP hTTypeP Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT
        hFourSixS hFourSixT hSCentralizerBot C u c hC hU hc
        ω η μ ν μsum νsum δ δ' σ βS j hnotation hj0 hj hβS
  · intro ω η μ ν μsum νsum δ δ' σ βT i hnotation hi0 hi hβT
    have hnotationSwap :
        hypothesis_13_1_characterNotationDataFor Tmax Smax W W2 W1
          (Nat.card W1) (Nat.card W2)
          (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
          (fun i j => μ j i) νsum μsum δ' δ σ :=
      hypothesis_13_1_characterNotationDataFor_swap_local hnotation
    exact
      hypothesis_13_1_betaSupportNormDataFor_s_side_source hmin
        (hypothesis_13_1_case_b_data_swap hcase) hTTypeP hSTypeP Tfam Sfam
        τT τS hTnonker hSnonker hDadeT hDadeS hFourSixT hFourSixS
        hTCentralizerBot D v d hD hV hd
        (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
        (fun i j => μ j i) νsum μsum δ' δ σ βT i hnotationSwap hi0 hi hβT

private theorem hypothesis_13_1_analysis_tail_without_source_choice_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2 τS τT
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2 P Q τS τT
      (Nat.card W2) (Nat.card W1) := by
  exact ⟨
    hypothesis_13_1_dadeDifferenceDataFor_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT,
    hypothesis_13_1_zeroBaseDegreeDataFor_source hmin hcase hSTypeP hTTypeP
      τS τT hFourSixS hFourSixT,
    hypothesis_13_1_conjugateIndexDataFor_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT,
    hypothesis_13_1_conjugateBetaTauDataFor_source hmin hcase hSTypeP hTTypeP
      Sfam Tfam τS τT hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT⟩

private theorem hypothesis_13_1_not_typeIII_or_typeIV_of_typeII_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hII : Section8.typeIIDefinitionData M MF) :
    ¬ (Section8.typeIIIDefinitionData M MF ∨
      Section8.typeIVDefinitionData M MF) := by
  rcases hII with
    ⟨U, W1, W2, _U1, _U0, hPU, _hUcond, _hUcomm, hUnorm, _hF⟩
  intro hlate
  rcases hlate with hIII | hIV
  · rcases hIII with
      ⟨V, W1', W2', hPV, _hVcond, _hVcomm, hVnorm⟩
    rcases Section11.theorem_11_exists_conj_eq_of_typeP_complements
        (G := G) (M := M) (MF := MF)
        (U := V) (W1 := W1') (W2 := W2')
        (V := U) (W1' := W1) (W2' := W2) hM hPV hPU with
      ⟨d, hVconj⟩
    have hdM : (d : G) ∈ M :=
      (section12_ambientDerivedSubgroup_le (G := G) (E := M)) d.property
    exact hUnorm
      (hypothesis_13_1_normalizer_le_of_conjBy_eq hdM hVconj hVnorm)
  · rcases hIV with
      ⟨V, W1', W2', hPV, _hVcond, _hVcomm, hVnorm⟩
    rcases Section11.theorem_11_exists_conj_eq_of_typeP_complements
        (G := G) (M := M) (MF := MF)
        (U := V) (W1 := W1') (W2 := W2')
        (V := U) (W1' := W1) (W2' := W2) hM hPV hPU with
      ⟨d, hVconj⟩
    have hdM : (d : G) ∈ M :=
      (section12_ambientDerivedSubgroup_le (G := G) (E := M)) d.property
    exact hUnorm
      (hypothesis_13_1_normalizer_le_of_conjBy_eq hdM hVconj hVnorm)

private theorem hypothesis_13_1_not_typeIV_of_typeIII_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hIII : Section8.typeIIIDefinitionData M MF) :
    ¬ Section8.typeIVDefinitionData M MF := by
  rcases hIII with ⟨U, W1, W2, hPU, _hUcond, hUcomm, _hUnorm⟩
  rintro ⟨V, W1', W2', hPV, _hVcond, hVnotcomm, _hVnorm⟩
  rcases Section11.theorem_11_exists_conj_eq_of_typeP_complements
      (G := G) (M := M) (MF := MF)
      (U := V) (W1 := W1') (W2 := W2')
      (V := U) (W1' := W1) (W2' := W2) hM hPV hPU with
    ⟨d, hVconj⟩
  have hVcomm : IsMulCommutative V := by
    rw [hVconj]
    haveI : IsMulCommutative U := hUcomm
    unfold Subgroup.conjBy
    infer_instance
  exact hVnotcomm hVcomm

private theorem hypothesis_13_1_sourceChoiceData_source
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinCE G) :
    hypothesis_13_1_sourceChoiceData G := by
  classical
  letI : IsMinCE G := hmin
  intro M MF hM _hMF htypes
  rcases htypes with hI | hII | hIII | hIV | hV
  · exact ⟨MF, Section8.msChoiceSource_of_typeIDefinitionData hI⟩
  · have hIIcopy := hII
    rcases hIIcopy with
      ⟨U, W1, W2, _U1, _U0, hP, _hcond, _hcomm, _hnorm, _hF⟩
    have hnotI : ¬ Section8.typeIDefinitionData M MF :=
      Section8.not_typeIDefinitionData_of_typeP_source_data hP
    have hnotLate :=
      hypothesis_13_1_not_typeIII_or_typeIV_of_typeII_source hM hII
    have hnotIII : ¬ Section8.typeIIIDefinitionData M MF := by
      intro hIII
      exact hnotLate (Or.inl hIII)
    have hnotIV : ¬ Section8.typeIVDefinitionData M MF := by
      intro hIV
      exact hnotLate (Or.inr hIV)
    have hnotV : ¬ Section8.typeVDefinitionData M MF := by
      rintro ⟨V, V1, V2, hPV, hVbot, _hAlt⟩
      subst V
      exact Section8.not_typeIIDefinitionData_of_typeP_bot hPV hII
    exact ⟨MF, Or.inr (Or.inl
      ⟨hnotI, hII, hnotIII, hnotIV, hnotV, rfl⟩)⟩
  · have hIIIcopy := hIII
    rcases hIIIcopy with
      ⟨U, W1, W2, hP, _hcond, _hcomm, _hnorm⟩
    have hnotI : ¬ Section8.typeIDefinitionData M MF :=
      Section8.not_typeIDefinitionData_of_typeP_source_data hP
    have hnotII : ¬ Section8.typeIIDefinitionData M MF := by
      intro hII
      exact
        (hypothesis_13_1_not_typeIII_or_typeIV_of_typeII_source hM hII)
          (Or.inl hIII)
    have hnotIV : ¬ Section8.typeIVDefinitionData M MF :=
      hypothesis_13_1_not_typeIV_of_typeIII_source hM hIII
    have hnotV : ¬ Section8.typeVDefinitionData M MF := by
      rintro ⟨V, V1, V2, hPV, hVbot, _hAlt⟩
      subst V
      exact Section8.not_typeIIIDefinitionData_of_typeP_bot hPV hIII
    exact ⟨ambientDerivedSubgroup M, Or.inr (Or.inr (Or.inl
      ⟨hnotI, hnotII, hIII, hnotIV, hnotV, rfl⟩))⟩
  · have hIVcopy := hIV
    rcases hIVcopy with
      ⟨U, W1, W2, hP, _hcond, _hnotcomm, _hnorm⟩
    have hnotI : ¬ Section8.typeIDefinitionData M MF :=
      Section8.not_typeIDefinitionData_of_typeP_source_data hP
    have hnotII : ¬ Section8.typeIIDefinitionData M MF := by
      intro hII
      exact
        (hypothesis_13_1_not_typeIII_or_typeIV_of_typeII_source hM hII)
          (Or.inr hIV)
    have hnotIII : ¬ Section8.typeIIIDefinitionData M MF := by
      intro hIII
      exact hypothesis_13_1_not_typeIV_of_typeIII_source hM hIII hIV
    have hnotV : ¬ Section8.typeVDefinitionData M MF := by
      rintro ⟨V, V1, V2, hPV, hVbot, _hAlt⟩
      subst V
      exact Section8.not_typeIVDefinitionData_of_typeP_bot hPV hIV
    exact ⟨ambientDerivedSubgroup M, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hnotI, hnotII, hnotIII, hIV, hnotV, rfl⟩)))⟩
  · have hVcopy := hV
    rcases hVcopy with ⟨U, W1, W2, hP, hUbot, _hAlt⟩
    subst U
    have hnotI : ¬ Section8.typeIDefinitionData M MF :=
      Section8.not_typeIDefinitionData_of_typeP_source_data hP
    have hnotII : ¬ Section8.typeIIDefinitionData M MF :=
      Section8.not_typeIIDefinitionData_of_typeP_bot hP
    have hnotIII : ¬ Section8.typeIIIDefinitionData M MF :=
      Section8.not_typeIIIDefinitionData_of_typeP_bot hP
    have hnotIV : ¬ Section8.typeIVDefinitionData M MF :=
      Section8.not_typeIVDefinitionData_of_typeP_bot hP
    exact ⟨MF, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hnotI, hnotII, hnotIII, hnotIV, hV, rfl⟩)))⟩

private theorem hypothesis_13_1_source_choice_tail_without_notation_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2 τS τT
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2 P Q τS τT
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_sourceChoiceData G := by
  rcases hypothesis_13_1_analysis_tail_without_source_choice_source
      hmin hcase hSTypeP hTTypeP Sfam Tfam τS τT
      hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT with
    ⟨hdadeDiff, hzeroBase, hconjIndex, hconjBeta⟩
  exact ⟨hdadeDiff, hzeroBase, hconjIndex, hconjBeta,
    hypothesis_13_1_sourceChoiceData_source hmin⟩

private theorem hypothesis_13_1_notation_and_source_choice_tail_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (hSnonker : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonker : nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hFourSixS : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hFourSixT : typePFourSixTauSourceData Tmax Q V W2 W1 τT) :
    hypothesis_13_1_characterNotationData Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2 τS τT
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2 P Q τS τT
      (Nat.card W2) (Nat.card W1) ∧
    hypothesis_13_1_sourceChoiceData G := by
  have hnotation :
      hypothesis_13_1_characterNotationData Smax Tmax W W1 W2
        (Nat.card W2) (Nat.card W1) :=
    hypothesis_13_1_characterNotationData_source hmin _hcase _hSTypeP _hTTypeP
      τS τT hFourSixS hFourSixT
  rcases hypothesis_13_1_source_choice_tail_without_notation_source
      hmin _hcase _hSTypeP _hTTypeP Sfam Tfam τS τT
      hSnonker hTnonker hDadeS hDadeT hFourSixS hFourSixT with
    ⟨hdadeDiff, hzeroBase, hconjIndex, hconjBeta, hsourceChoice⟩
  exact ⟨hnotation, hdadeDiff, hzeroBase, hconjIndex, hconjBeta,
    hsourceChoice⟩


public theorem hypothesis_13_1_source_tail_setup_of_case_b_typeP
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (_hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hSTypeP : Section8.typePData Smax P U W1 W2)
    (_hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    ∃ (Sfam : Finset (Section1.ClassFunction Smax))
      (Tfam : Finset (Section1.ClassFunction Tmax))
      (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G),
        Section5.hypothesis_5_2_b_statement Sfam τS ∧
        Section5.hypothesis_5_2_b_statement Tfam τT ∧
        nonkernelInducedFamily Smax (P ⊔ U) P Sfam ∧
        nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam ∧
        dadeIsometryRelativeToAZero Smax P Sfam τS ∧
        dadeIsometryRelativeToAZero Tmax Q Tfam τT ∧
        hypothesis_13_1_characterNotationData Smax Tmax W W1 W2
          (Nat.card W2) (Nat.card W1) ∧
        hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2 τS τT
          (Nat.card W2) (Nat.card W1) ∧
        hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2
          (Nat.card W2) (Nat.card W1) ∧
        hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2
          (Nat.card W2) (Nat.card W1) ∧
        hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2 P Q τS τT
          (Nat.card W2) (Nat.card W1) ∧
        hypothesis_13_1_sourceChoiceData G ∧
        typePFourSixTauSourceData Smax P U W1 W2 τS ∧
        typePFourSixTauSourceData Tmax Q V W2 W1 τT := by
  rcases hypothesis_13_1_families_and_dade_setup_source
      hmin _hcase _hSTypeP _hTTypeP with
    ⟨Sfam, Tfam, τS, τT, hS52, hT52, hSnonker, hTnonker, hSdade, hTdade,
      hFourSixS, hFourSixT⟩
  rcases hypothesis_13_1_notation_and_source_choice_tail_source
      hmin _hcase _hSTypeP _hTTypeP Sfam Tfam τS τT
      hSnonker hTnonker hSdade hTdade hFourSixS hFourSixT with
    ⟨hnotation, hdadeDiff, hzeroBase, hconjIndex, hconjBeta, hsourceChoice⟩
  exact ⟨Sfam, Tfam, τS, τT, hS52, hT52, hSnonker, hTnonker, hSdade, hTdade,
    hnotation, hdadeDiff, hzeroBase, hconjIndex, hconjBeta, hsourceChoice,
    hFourSixS, hFourSixT⟩
end CFSG.Section13
