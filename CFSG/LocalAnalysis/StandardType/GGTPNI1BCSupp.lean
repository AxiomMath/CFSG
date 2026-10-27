module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1BC
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGU
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
import CFSG.LocalAnalysis.StandardType.GGLieModelPSULabel
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDField

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal Polynomial
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (quasisimple_or_solvable_spSupported)

theorem tpbcc_fixSubgroup_conj_eq_centralizer {G : Type} [Group G] (x : G) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem tpbcc_map_centralizer_singleton {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc e g * e x = e (g * x) := (map_mul e g x).symm
      _ = e (x * g) := by
        rw [show g * x = x * g from Subgroup.mem_centralizer_singleton_iff.mp hg]
      _ = e x * e g := map_mul e x g
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    apply e.injective
    rw [map_mul, map_mul]
    simp only [MulEquiv.apply_symm_apply]
    exact show y * e x = e x * y from Subgroup.mem_centralizer_singleton_iff.mp hy

theorem tpbcc_prime_ne_zero {K : Type} [Field K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K 2] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm

theorem tpbcc_component_eq_derived {p m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hchar : CharP K 2) (hK : Nat.card K = 2 ^ n)
    {x : StatedSp (m + 1) K} {J : Subgroup (StatedSp (m + 1) K)}
    (H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x)) (hprojinj : Function.Injective (proj (m + 1) K))
    (hxp : x ^ p = 1) (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x})) :
    ∃ O : reciprocalOrbits (spEnd x),
      J = ⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ := by
  classical
  haveI : CharP K 2 := hchar
  let e : StatedSp (m + 1) K ≃* StatedProj (StatedSp (m + 1) K) :=
    MulEquiv.ofBijective (proj (m + 1) K)
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo (r := m + 1))
  let A : reciprocalOrbits (spEnd x) → Subgroup (StatedSp (m + 1) K) :=
    fun O => spSupported x (O : Set K[X])
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  have hcent : (Subgroup.centralizer ({x} : Set (StatedSp (m + 1) K))).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set (StatedProj (StatedSp (m + 1) K))) :=
    tpbcc_map_centralizer_singleton e x
  have hJmapA : CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj (e x))) := by
    rw [tpbcc_fixSubgroup_conj_eq_centralizer (e x), ← hcent]
    exact ⟨Subgroup.map_mono hJ.1, CFSG.Assembly.IsSubnormal.map e.toMonoidHom hJ.2.1,
      CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective J e.toMonoidHom e.injective).symm hJ.2.2⟩
  have hJmap : CFSG.Open.IsComponentOf (J.map e.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj (e x))) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJmapA
  have hker : (proj (m + 1) K).ker ≤ Subgroup.center (StatedSp (m + 1) K) := by
    rw [ker_proj]
    exact spScalars_le_center
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcksq : Squarefree (minpoly K (spEnd x)) :=
    (altPrimaryData_spLin (tpbcc_prime_ne_zero hp hp2) hxp).squarefree
  have hc : ∀ i j : reciprocalOrbits (spEnd x), i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b :=
    fun i j hij a ha b hb =>
      H.directProduct.1 i i.2 j j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  have hjoin : (⨆ i, A i) = Subgroup.centralizer ({x} : Set (StatedSp (m + 1) K)) :=
    H.directProduct.2.2
  have htame : ∀ i : reciprocalOrbits (spEnd x),
      CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i) :=
    fun i => quasisimple_or_solvable_spSupported hp3 (Nat.le_self_pow (by omega) 2) hcksq H i
  obtain ⟨i, -, hKi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family
      e.toMonoidHom e.surjective hker x A hc hjoin htame (J.map e.toMonoidHom) hJmap
  exact ⟨i, Subgroup.map_injective e.injective hKi⟩

private theorem tpbcA_hasLabel_of_lieModel_PSL {X : Type} [Group X] {r f : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSL r 2 f) : GGHasLabel ⟨.A, r - 1, f⟩ X := by
  have hS : StatedClassicalModel X .PSL r 2 f := h.statedClassicalModel (by decide)
  have hr2 : 2 ≤ r := hS.1.2.2.1
  have hr : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_two hr2
  dsimp only [GGHasLabel, LargeEvenRawDatum]
  rw [show r - 1 + 1 = r from Nat.succ_pred_eq_of_pos hr]
  exact recipeLinear_of_statedClassicalModel hS

private theorem tpbcA_rankA_inLambda2 {r f : ℕ} (h : StatedLieAdmissible .PSL r 2 f) :
    LargeEvenInLambda2 ⟨.A, r - 1, f⟩ := by
  have hf : 1 ≤ f := h.2.1
  have hr : 2 ≤ r := h.2.2.1
  have h22 : (r, 2 ^ f) ≠ (2, 2) := h.2.2.2.1
  dsimp only [LargeEvenInLambda2]
  refine ⟨hf, Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hr), ?_⟩
  intro h1
  have hr2 : r = 2 := by
    have hp : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_two hr
    have hsucc : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hp
    rw [h1] at hsucc
    norm_num at hsucc
    exact hsucc.symm
  by_contra h2
  have hf1 : f = 1 := le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_le h2)) hf
  exact h22 (by simp [hr2, hf1])

private theorem tpbcA_rankTwA_inLambda2 {r f : ℕ} (h : StatedLieAdmissible .PSU r 2 f) :
    LargeEvenInLambda2 ⟨.twA, r - 1, f⟩ := by
  have hf : 1 ≤ f := h.2.1
  have hr : 3 ≤ r := h.2.2.1
  have h32 : (r, 2 ^ f) ≠ (3, 2) := h.2.2.2
  dsimp only [LargeEvenInLambda2]
  refine ⟨hf, Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hr), ?_⟩
  intro h1
  have hr2 : r = 3 := by
    have hp : 0 < r := Nat.lt_of_lt_of_le (by norm_num : 0 < 3) hr
    have hsucc : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hp
    rw [h1] at hsucc
    norm_num at hsucc
    exact hsucc.symm
  by_contra h2
  have hf1 : f = 1 := le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_le h2)) hf
  exact h32 (by simp [hr2, hf1])

private theorem tpbcA_no_labelIso_of_tags {t t' : LargeEvenLieTag}
    (h1 : t ≠ .B) (h2 : t ≠ .C) (h3 : t ≠ .D) (h4 : t ≠ .twD)
    (h5 : t' ≠ .D) (h6 : t' ≠ .twD) (h7 : t ≠ t') {r f m n : ℕ} :
    ¬ GGLabelIso ⟨t, r, f⟩ ⟨t', m, n⟩ := by
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h7 (congrArg LargeEvenLabel.tag h)
  · exact h2 (h.1.resolve_left h1)
  · exact h3 (congrArg LargeEvenLabel.tag h.1)
  · exact h5 (congrArg LargeEvenLabel.tag h.2)
  · exact h4 (congrArg LargeEvenLabel.tag h.1)
  · exact h6 (congrArg LargeEvenLabel.tag h.2)
  · exact h4 (congrArg LargeEvenLabel.tag h.1)
  · exact h6 (congrArg LargeEvenLabel.tag h.1)

theorem tpbcc_support_eq_fixed {p m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hchar : CharP K 2) (hK : Nat.card K = 2 ^ n)
    {x : StatedSp (m + 1) K} {J : Subgroup (StatedSp (m + 1) K)}
    (H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x)) (hprojinj : Function.Injective (proj (m + 1) K))
    (hxp : x ^ p = 1) (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x}))
    (O : reciprocalOrbits (spEnd x))
    (hJO : J = ⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆)
    (hlab : GGHasLabel ⟨.C, m, n⟩ (↥J ⧸ Subgroup.center ↥J)) :
    (O : Set K[X]) = {X - 1} := by
  classical
  haveI : CharP K 2 := hchar
  obtain ⟨h, hh, hO⟩ := O.2
  have hOset : (O : Set K[X]) = ({h, reciprocalPolynomial h} : Set K[X]) := hO.symm
  have hΛC : LargeEvenInLambda2 ⟨.C, m, n⟩ := by
    dsimp only [LargeEvenInLambda2]
    refine ⟨hn, le_trans (by norm_num : 2 ≤ 3) hm, ?_⟩
    intro h2
    rw [h2] at hm
    exact absurd hm (by norm_num)
  by_cases h1 : h = X - 1
  · rw [hOset, h1, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
  by_cases hself : reciprocalPolynomial h = h
  ·
    exfalso
    have hSD : SpSelfDualBlock 2 n p x ⟨h, hh⟩ := H.selfDual ⟨h, hh⟩ h1 hself
    obtain ⟨d, hd, hpd, σ, hσpow, hσne, hσσ, hσroot, hHf1, hE, hEbar, Hf, hHfsym, hHfsep,
      htrace, he, φ, hφ⟩ := hSD.exists_half
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    haveI : Finite (AdjoinRoot h) := hE.finite
    let τ : AdjoinRoot h ≃+* AdjoinRoot h :=
      RingEquiv.ofBijective hE.bar (Function.Involutive.bijective hE.bar_bar)
    have hτ : ∀ y, τ (τ y) = y := fun y => hE.bar_bar y
    have hOself : (O : Set K[X]) = {h} := by
      rw [hOset, hself, Set.pair_eq_singleton]
    have hqA : CFSG.Assembly.IsQuasisimple
        ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ := by
      rw [← hJO]; exact hJ.2.2
    have hq : CFSG.IsQuasisimple
        ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mpr hqA
    obtain ⟨e', he'⟩ := he
    obtain ⟨eU⟩ :=
      CFSG.LieType.SemisimpleCentralizers.HeldUCD.nonempty_mulEquiv_heldGU τ hτ Hf e' he'
    have hcn : Nat.card ↥hE.fixedField = 2 ^ (n * d) := hE.card_fixedField
    have hEc : Nat.card (AdjoinRoot h) = Nat.card ↥hE.fixedField ^ 2 := by
      rw [hE.card, hE.card_fixedField, ← pow_mul]
      congr 1
      ring
    have hτQ : ∀ y, τ y = y ^ Nat.card ↥hE.fixedField := by
      intro y
      change hE.bar y = y ^ Nat.card ↥hE.fixedField
      rw [hEbar, hσpow, hE.card_fixedField, ← pow_mul]
    have hd1 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · exfalso
        rw [h0, mul_zero] at hd
        have hpos := (irreducible_of_mem_primaryFactors hh).natDegree_pos
        rw [hd] at hpos
        exact Nat.lt_irrefl 0 hpos
      · exact h0
    have hnfield : 1 ≤ n * d :=
      Nat.succ_le_of_lt (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hn) hd1)
    have φ' : spSupported x (O : Set K[X]) ≃*
        CFSG.LieType.SemisimpleCentralizers.Held.heldGU (primaryMultiplicity (spEnd x) h)
          (AdjoinRoot h) τ hτ := by
      rw [hOself]
      exact φ.trans eU
    obtain ⟨t, mm, htm, hmodel⟩ :=
      ggNbrLSideSp_typeGU (K := ↥hE.fixedField) (E := AdjoinRoot h) (τ := τ) (hτ := hτ)
        (r := primaryMultiplicity (spEnd x) h) (n := n * d) hcn hnfield hEc hτQ φ' hq
    rcases htm with ⟨ht, hm⟩ | ⟨ht, hm⟩
    · subst ht; subst hm
      have hHas : GGHasLabel ⟨.twA, primaryMultiplicity (spEnd x) h - 1, n * d⟩
          (↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ⧸
            Subgroup.center ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆) :=
        ggHasLabel_of_lieModel_PSU hmodel
      rw [← hJO] at hHas
      have hΛA : LargeEvenInLambda2 ⟨.twA, primaryMultiplicity (spEnd x) h - 1, n * d⟩ :=
        tpbcA_rankTwA_inLambda2 hmodel.admissible
      exact tpbcA_no_labelIso_of_tags (t := .twA) (t' := .C) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (ggLabelRigidInput_holds _ _ _ hΛA hΛC hHas hlab)
    · subst ht; subst hm
      have hHas : GGHasLabel ⟨.A, 2 - 1, n * d⟩
          (↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ⧸
            Subgroup.center ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆) :=
        tpbcA_hasLabel_of_lieModel_PSL hmodel
      rw [← hJO] at hHas
      have hΛA : LargeEvenInLambda2 ⟨.A, 2 - 1, n * d⟩ :=
        tpbcA_rankA_inLambda2 hmodel.admissible
      exact tpbcA_no_labelIso_of_tags (t := .A) (t' := .C) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (ggLabelRigidInput_holds _ _ _ hΛA hΛC hHas hlab)
  ·
    exfalso
    have hne : (h : K[X]) ≠ reciprocalPolynomial h := fun e => hself e.symm
    have hP : SpPairedBlock 2 n p x ⟨h, hh⟩ := H.paired ⟨h, hh⟩ hne
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
    have hqA : CFSG.Assembly.IsQuasisimple
        ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ := by
      rw [← hJO]; exact hJ.2.2
    have hq : CFSG.IsQuasisimple
        ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ :=
      (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mpr hqA
    have φ' : spSupported x (O : Set K[X]) ≃*
        GL (Fin (primaryMultiplicity (spEnd x) h)) (AdjoinRoot h) := by
      rw [hOset]
      exact φ
    have hdeg : 1 ≤ h.natDegree := by
      have hpos : 0 < h.natDegree :=
        natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible
          (irreducible_of_mem_primaryFactors hh))
      exact Nat.succ_le_of_lt hpos
    have hKfield : Nat.card (AdjoinRoot h) = 2 ^ (n * h.natDegree) := by
      rw [hP.card_field, pow_mul]
    have hnfield : 1 ≤ n * h.natDegree :=
      Nat.succ_le_of_lt (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hn) hdeg)
    have hmodel := ggNbrLSideSp_typeGL (K := AdjoinRoot h)
      (r := primaryMultiplicity (spEnd x) h) (n := n * h.natDegree) hKfield hnfield φ' hq
    have hHas : GGHasLabel ⟨.A, primaryMultiplicity (spEnd x) h - 1, n * h.natDegree⟩
        (↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ⧸
          Subgroup.center ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆) :=
      tpbcA_hasLabel_of_lieModel_PSL hmodel
    rw [← hJO] at hHas
    have hΛA : LargeEvenInLambda2 ⟨.A, primaryMultiplicity (spEnd x) h - 1, n * h.natDegree⟩ :=
      tpbcA_rankA_inLambda2 hmodel.admissible
    exact tpbcA_no_labelIso_of_tags (t := .A) (t' := .C) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (ggLabelRigidInput_holds _ _ _ hΛA hΛC hHas hlab)

end CFSG.StandardType

end
