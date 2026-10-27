module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixI.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_15
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Order

namespace CFSG
end CFSG
open CFSG

attribute [local instance] IsMulCommutative.instCommGroup

/-!
# Peterfalvi Appendix I, Proposition 1

Source: Peterfalvi--Sandling, *Character Theory for the Odd Order Theorem*,
Part II, Appendix I, printed pages 135--136.
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixI

/-- Same-characteristic branch of the p-group lemma. Fixed-point counting for
a `p`-group action produces a nonidentity global fixed point; constant
stabilizer cardinality and faithfulness then force the actor to be trivial. -/
private theorem peterfalvi_appendixI_proposition_1_pGroup_fixedPointFree_samePrime
    {p : ℕ} [Fact p.Prime]
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian p E]
    [MulDistribMulAction P E] [FaithfulSMul P E]
    (hP : IsPGroup p P)
    (hstab : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (MulAction.stabilizer P a) =
        Nat.card (MulAction.stabilizer P b)) :
    ∀ x : P, x ≠ 1 → ∀ e : E, x • e = e → e = 1 := by
  classical
  by_cases hE : Nontrivial E
  · letI : Nontrivial E := hE
    have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
    obtain ⟨n, hEcard⟩ := hEp.exists_card_eq
    have hn_ne_zero : n ≠ 0 := by
      intro hn
      have hcard_one : Nat.card E = 1 := by simpa [hn] using hEcard
      exact (Finite.one_lt_card_iff_nontrivial.mpr hE).ne hcard_one.symm
    have hp_dvd_E : p ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self p hn_ne_zero
    have hone_fixed : (1 : E) ∈ MulAction.fixedPoints P E := by simp
    obtain ⟨a, ha_fixed, hne⟩ :=
      hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hp_dvd_E hone_fixed
    have ha_ne : a ≠ 1 := fun ha => hne ha.symm
    have hstab_a_top : MulAction.stabilizer P a = ⊤ := by
      ext y
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
      exact ha_fixed y
    have hstab_top : ∀ b : E, b ≠ 1 → MulAction.stabilizer P b = ⊤ := by
      intro b hb
      apply (Subgroup.card_eq_iff_eq_top (H := MulAction.stabilizer P b)).1
      calc
        Nat.card (MulAction.stabilizer P b) =
            Nat.card (MulAction.stabilizer P a) := hstab b a hb ha_ne
        _ = Nat.card P := by simp [hstab_a_top]
    have htrivial : ∀ y : P, ∀ b : E, y • b = b := by
      intro y b
      by_cases hb : b = 1
      · simp [hb]
      · have hy : y ∈ MulAction.stabilizer P b := by simp [hstab_top b hb]
        exact MulAction.mem_stabilizer_iff.mp hy
    letI : Subsingleton P :=
      ⟨fun y z => FaithfulSMul.eq_of_smul_eq_smul (α := E) fun b =>
        (htrivial y b).trans (htrivial z b).symm⟩
    intro x hx
    exact False.elim (hx (Subsingleton.elim x 1))
  · letI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    intro _ _ e _
    exact Subsingleton.elim e 1

open scoped Pointwise

private theorem peterfalvi_appendixI_proposition_1_fixedPointSubgroup_subgroup_eq_bot_of_disjoint
    {A M : Type*} [Group A] [Group M] [MulDistribMulAction A M]
    (U : Subgroup M) [IsInvariant A M U]
    (hdisj : Disjoint U (fixedPointSubgroup A M)) :
    fixedPointSubgroup A (↥U) = ⊥ := by
  apply bot_unique
  intro x hx
  have hxM : (x : M) ∈ fixedPointSubgroup A M := by
    rw [FixedPoints.mem_subgroup] at hx ⊢
    intro a
    exact congrArg Subtype.val (hx a)
  have hxbot : (x : M) ∈ (⊥ : Subgroup M) :=
    (Subgroup.disjoint_def.mp hdisj) x.2 hxM
  simpa using hxbot

private theorem peterfalvi_appendixI_proposition_1_fixedPointSubgroup_sup_eq_bot_of_disjoint
    {A M : Type*} [Group A] [Finite A]
    [Group M] [Finite M] [IsMulCommutative M] [MulDistribMulAction A M]
    (U W : Subgroup M) [IsInvariant A M U] [IsInvariant A M W]
    [IsInvariant A M (U ⊔ W)]
    (hdisj : Disjoint U W)
    (hfixU : fixedPointSubgroup A (↥U) = ⊥)
    (hfixW : fixedPointSubgroup A W = ⊥) :
    fixedPointSubgroup A (↥(U ⊔ W)) = ⊥ := by
  apply bot_unique
  intro x hx
  rw [FixedPoints.mem_subgroup] at hx
  obtain ⟨u, hu, w, hw, huw⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := U) (t := W) (x := (x : M))).1 x.2
  have hunique :
      ∀ {u1 u2 w1 w2 : M}, u1 ∈ U → u2 ∈ U → w1 ∈ W → w2 ∈ W →
        u1 * w1 = u2 * w2 → u1 = u2 ∧ w1 = w2 := by
    intro u1 u2 w1 w2 hu1 hu2 hw1 hw2 heq
    have hcross : u1 * u2⁻¹ ∈ U ∧ u1 * u2⁻¹ ∈ W := by
      refine ⟨U.mul_mem hu1 (U.inv_mem hu2), ?_⟩
      have : u1 * u2⁻¹ = w2 * w1⁻¹ := by
        calc
          u1 * u2⁻¹ = (u2 * w2) * (w1⁻¹ * u2⁻¹) := by rw [← heq]; simp [mul_assoc]
          _ = (u2 * u2⁻¹) * (w2 * w1⁻¹) := by ac_rfl
          _ = w2 * w1⁻¹ := by simp
      rw [this]
      exact W.mul_mem hw2 (W.inv_mem hw1)
    have hu_eq : u1 = u2 := by
      have hone : u1 * u2⁻¹ = 1 :=
        (Subgroup.disjoint_def.mp hdisj) hcross.1 hcross.2
      calc
        u1 = (u1 * u2⁻¹) * u2 := by simp [mul_assoc]
        _ = u2 := by simp [hone]
    refine ⟨hu_eq, ?_⟩
    calc
      w1 = u1⁻¹ * (u2 * w2) := by rw [← heq]; simp
      _ = w2 := by simp [hu_eq]
  have hparts (a : A) : a • u = u ∧ a • w = w := by
    have hau := (IsInvariant.invariant (A := A) (G := M) (H := U) a u).1 hu
    have haw := (IsInvariant.invariant (A := A) (G := M) (H := W) a w).1 hw
    apply hunique hau hu haw hw
    calc
      (a • u) * (a • w) = a • (u * w) := by simp [smul_mul']
      _ = a • (x : M) := by rw [huw]
      _ = x := congrArg Subtype.val (hx a)
      _ = u * w := huw.symm
  have hu_mem : (⟨u, hu⟩ : U) ∈ fixedPointSubgroup A U := by
    rw [FixedPoints.mem_subgroup]
    intro a
    exact Subtype.ext (hparts a).1
  have hw_mem : (⟨w, hw⟩ : W) ∈ fixedPointSubgroup A W := by
    rw [FixedPoints.mem_subgroup]
    intro a
    exact Subtype.ext (hparts a).2
  have hu_one : u = 1 := by
    have : (⟨u, hu⟩ : U) = 1 := by simpa [hfixU] using hu_mem
    exact congrArg Subtype.val this
  have hw_one : w = 1 := by
    have : (⟨w, hw⟩ : W) = 1 := by simpa [hfixW] using hw_mem
    exact congrArg Subtype.val this
  apply Subtype.ext
  simp [← huw, hu_one, hw_one]

private theorem peterfalvi_appendixI_proposition_1_disjoint_sup_fixedPointSubgroup
    {A M : Type*} [Group A] [Finite A]
    [Group M] [Finite M] [IsMulCommutative M] [MulDistribMulAction A M]
    (U W : Subgroup M) [IsInvariant A M U] [IsInvariant A M W]
    [IsInvariant A M (U ⊔ W)]
    (hUW : Disjoint U W)
    (hU : Disjoint U (fixedPointSubgroup A M))
    (hW : Disjoint W (fixedPointSubgroup A M)) :
    Disjoint (U ⊔ W) (fixedPointSubgroup A M) := by
  have hfixU : fixedPointSubgroup A (↥U) = ⊥ :=
    peterfalvi_appendixI_proposition_1_fixedPointSubgroup_subgroup_eq_bot_of_disjoint U hU
  have hfixW : fixedPointSubgroup A (↥W) = ⊥ :=
    peterfalvi_appendixI_proposition_1_fixedPointSubgroup_subgroup_eq_bot_of_disjoint W hW
  have hfixSup : fixedPointSubgroup A (↥(U ⊔ W)) = ⊥ :=
    peterfalvi_appendixI_proposition_1_fixedPointSubgroup_sup_eq_bot_of_disjoint U W hUW hfixU hfixW
  rw [Subgroup.disjoint_def]
  intro x hxSup hxFix
  let xs : ↥(U ⊔ W) := ⟨x, hxSup⟩
  have hxsFix : xs ∈ fixedPointSubgroup A (↥(U ⊔ W)) := by
    rw [FixedPoints.mem_subgroup] at hxFix ⊢
    intro a
    exact Subtype.ext (hxFix a)
  have hxsOne : xs = 1 := by simpa [hfixSup] using hxsFix
  change x = 1
  exact congrArg Subtype.val hxsOne
/-- Peterfalvi's finite fixed-space induction, isolated from the rank-two setup. -/
private theorem peterfalvi_appendixI_proposition_1_fixedPointSubgroup_family_iSupIndep_of_pairwise_disjoint
    {A M ι : Type*} [CommGroup A] [Finite A]
    [Group M] [Finite M] [IsMulCommutative M] [MulDistribMulAction A M]
    [Fintype ι]
    (T : ι → Subgroup A)
    (F : ι → Subgroup M)
    (hF : ∀ i, F i = fixedPointSubgroup (T i) M)
    (hpair : Pairwise (fun i j => Disjoint (F i) (F j))) :
    iSupIndep F := by
  classical
  letI : CommGroup M := IsMulCommutative.instCommGroup
  have hF_inv (i j : ι) : IsInvariant (T i) M (F j) := by
    have hforward : ∀ a : T i, ∀ x : M, x ∈ F j → a • x ∈ F j := by
      intro a x hx
      rw [hF j, FixedPoints.mem_subgroup] at hx ⊢
      intro b
      calc
        (b : A) • ((a : A) • x) = ((b : A) * (a : A)) • x := by simp [mul_smul]
        _ = ((a : A) * (b : A)) • x := by rw [mul_comm]
        _ = (a : A) • ((b : A) • x) := by simp [mul_smul]
        _ = (a : A) • x := by
          have haction : (b : A) • x = x := by
            calc
              (b : A) • x = (b : ↥(T j)) • x := rfl
              _ = x := hx b
          simp [haction]
    refine ⟨?_⟩
    intro a x
    constructor
    · exact hforward a x
    · intro hx
      have hx' := hforward a⁻¹ (a • x) hx
      simpa [inv_smul_smul] using hx'
  have hnormalizer (X Y : Subgroup M) : Y ≤ Subgroup.normalizer (X : Set M) := by
    intro y hy
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hyx : y * x * y⁻¹ = x := by
        calc
          y * x * y⁻¹ = (y * x) * y⁻¹ := rfl
          _ = (x * y) * y⁻¹ := by rw [mul_comm y x]
          _ = x * (y * y⁻¹) := by rw [mul_assoc]
          _ = x * 1 := by rw [mul_inv_cancel y]
          _ = x := by rw [mul_one x]
      rw [hyx]
      exact hx
    · intro hx
      have hyx' : x = y * x * y⁻¹ := by
        calc
          x = x * 1 := (mul_one x).symm
          _ = x * (y * y⁻¹) := by rw [mul_inv_cancel y]
          _ = x * y * y⁻¹ := by rw [mul_assoc]
          _ = y * x * y⁻¹ := by rw [mul_comm x y]
      rw [hyx']
      exact hx
  have hsup_inv : ∀ (s : Finset ι) (i : ι), IsInvariant (T i) M (s.sup F) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro i
        refine ⟨?_⟩
        intro a x
        constructor
        · intro hx
          have hxone : x = 1 := by simpa using hx
          simp [hxone]
        · intro hx
          have hxone : a • x = 1 := by simpa [hx]
          rw [smul_eq_iff_eq_inv_smul] at hxone
          simpa using hxone
    | @insert j s hj ih =>
        intro i
        letI : IsInvariant (T i) M (F j) := hF_inv i j
        letI : IsInvariant (T i) M (s.sup F) := ih i
        have hinv : IsInvariant (T i) M (F j ⊔ s.sup F) :=
          isInvariant_sup_of_le_normalizer (A := T i) (G := M)
            (X := F j) (Y := s.sup F) (hnormalizer (F j) (s.sup F))
        simpa [Finset.sup_insert, hj] using hinv
  have hind : ∀ s : Finset ι,
      s.SupIndep F ∧
        ∀ i, i ∉ s → Disjoint (s.sup F) (fixedPointSubgroup (T i) M) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        refine ⟨by simp, ?_⟩
        intro i hi
        simp
    | @insert i s hi ih =>
        rcases ih with ⟨hsind, hsfix⟩
        have hdisj : Disjoint (F i) (s.sup F) := by
          rw [disjoint_comm]
          simpa only [← hF i] using hsfix i hi
        refine ⟨hsind.insert hdisj, ?_⟩
        intro j hj
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self i s)
        have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
        letI : IsInvariant (T j) M (F i) := hF_inv j i
        letI : IsInvariant (T j) M (s.sup F) := hsup_inv s j
        letI : IsInvariant (T j) M (F i ⊔ s.sup F) :=
          isInvariant_sup_of_le_normalizer (A := T j) (G := M)
            (X := F i) (Y := s.sup F) (hnormalizer (F i) (s.sup F))
        have hfix_i : Disjoint (F i) (fixedPointSubgroup (T j) M) := by
          simpa only [← hF j] using hpair hji.symm
        have hfix_sup :
            Disjoint (F i ⊔ s.sup F) (fixedPointSubgroup (T j) M) :=
          peterfalvi_appendixI_proposition_1_disjoint_sup_fixedPointSubgroup (U := F i) (W := s.sup F)
            hdisj hfix_i (hsfix j hjs)
        simpa only [Finset.sup_insert] using hfix_sup
  exact (hind Finset.univ).1.iSupIndep_of_univ

/-- Rank-two fixed-space block decomposition, indexed by the nonzero
hyperplane fixed spaces as in Peterfalvi's proof. -/
private theorem peterfalvi_appendixI_proposition_1_hyperplane_fixed_iSupIndep_and_iSup_top
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {R E : Type*} [Group R] [Finite R] [Group E] [Finite E]
    [IsElementaryAbelian p R] [IsElementaryAbelian q E]
    [MulDistribMulAction R E]
    (hp_ne_q : p ≠ q) (hncyc : ¬ IsCyclic R)
    (hfix_top : fixedPointSubgroup (↥(⊤ : Subgroup R)) E = ⊥) :
    let Ω := {Y : Subgroup R //
      Y.index = p ∧ fixedPointSubgroup (↥Y) E ≠ ⊥}
    let F : Ω → Subgroup E := fun Y => fixedPointSubgroup (↥Y.1) E
    iSupIndep F ∧ iSup F = ⊤ := by
  classical
  letI : CommGroup R := IsMulCommutative.instCommGroup
  let Ω := {Y : Subgroup R //
    Y.index = p ∧ fixedPointSubgroup (↥Y) E ≠ ⊥}
  let F : Ω → Subgroup E := fun Y => fixedPointSubgroup (↥Y.1) E
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hcyc (Y : Ω) : IsCyclic (R ⧸ Y.1) := by
    have hcard : Nat.card (R ⧸ Y.1) = p := by
      simpa [Subgroup.index_eq_card] using Y.2.1
    exact isCyclic_of_prime_card (α := R ⧸ Y.1) hcard
  have hpair : Pairwise (fun Y Z : Ω => Disjoint (F Y) (F Z)) := by
    intro Y Z hYZ
    exact theorem_3_6_hyperplane_fixed_disjoint
      (K := R) (V := E) (q := p) hfix_top Y.1 Z.1
      (hcyc Y) (hcyc Z) Y.2.2 Z.2.2 (fun h => hYZ (Subtype.ext h))
  have hind : iSupIndep F :=
    peterfalvi_appendixI_proposition_1_fixedPointSubgroup_family_iSupIndep_of_pairwise_disjoint
      (T := fun Y : Ω => Y.1) (F := F) (fun _ => rfl) hpair
  have hsup_all :
      (⨆ (Y : Subgroup R) (_ : IsCyclic (R ⧸ Y)),
        fixedPointSubgroup (↥Y) E) = ⊤ :=
    theorem_3_6_hyperplane_fixed_iSup_top
      (K := R) (V := E) (q := p) (p := q) hp_ne_q hncyc
  have hsup_eq :
      iSup F =
        (⨆ (Y : Subgroup R) (_ : IsCyclic (R ⧸ Y)),
          fixedPointSubgroup (↥Y) E) := by
    apply le_antisymm
    · refine iSup_le ?_
      intro Y
      exact le_iSup_of_le Y.1 (le_iSup_of_le (hcyc Y) le_rfl)
    · refine iSup_le ?_
      intro Y
      refine iSup_le ?_
      intro hYcyc
      by_cases hfix : fixedPointSubgroup (↥Y) E = ⊥
      · simp [hfix]
      · have hY_ne_top : Y ≠ ⊤ := by
          intro hYtop
          subst Y
          exact hfix hfix_top
        have hYindex : Y.index = p := by
          simpa [Subgroup.index_eq_card] using
            theorem_3_6_cyclic_quotient_card_eq_prime
              (q := p) Y hYcyc hY_ne_top
        let YΩ : Ω := ⟨Y, hYindex, hfix⟩
        simpa [F, YΩ] using (le_iSup F YΩ)
  exact ⟨hind, hsup_eq.trans hsup_all⟩
private theorem peterfalvi_appendixI_proposition_1_fixedPointFree_of_crossBlock_stabilizer
    {q : ℕ} [Fact q.Prime]
    {P E ι : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian q E]
    [MulDistribMulAction P E] [FaithfulSMul P E]
    (U : ι → Subgroup E)
    (hnonzero : ∀ i, U i ≠ ⊥)
    (hspan : ⨆ i, U i = ⊤)
    (htwo : ∃ i j : ι, i ≠ j)
    (hcross : ∀ {i j : ι}, i ≠ j → ∀ {a b : E},
      a ∈ U i → b ∈ U j → a ≠ 1 → b ≠ 1 →
        a * b ≠ 1 ∧
          MulAction.stabilizer P (a * b) =
            MulAction.stabilizer P a ⊓ MulAction.stabilizer P b)
    (hstab : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (MulAction.stabilizer P a) =
        Nat.card (MulAction.stabilizer P b)) :
    ∀ x : P, x ≠ 1 → ∀ e : E, x • e = e → e = 1 := by
  classical
  obtain ⟨i₀, j₀, hij⟩ := htwo
  obtain ⟨aU, haU_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hnonzero i₀)
  obtain ⟨bU, hbU_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hnonzero j₀)
  let a : E := aU
  let b : E := bU
  have ha_mem : a ∈ U i₀ := aU.2
  have hb_mem : b ∈ U j₀ := bU.2
  have ha : a ≠ 1 := by
    intro ha1
    exact haU_ne (Subtype.ext (by simpa [a] using ha1))
  have hb : b ≠ 1 := by
    intro hb1
    exact hbU_ne (Subtype.ext (by simpa [b] using hb1))
  have hpair {i j : ι} (hij' : i ≠ j) {u v : E}
      (hu_mem : u ∈ U i) (hv_mem : v ∈ U j)
      (hu : u ≠ 1) (hv : v ≠ 1) :
      MulAction.stabilizer P u = MulAction.stabilizer P v := by
    obtain ⟨huv, hmul⟩ := hcross hij' hu_mem hv_mem hu hv
    have hleu : MulAction.stabilizer P (u * v) ≤ MulAction.stabilizer P u := by
      rw [hmul]
      exact inf_le_left
    have hlev : MulAction.stabilizer P (u * v) ≤ MulAction.stabilizer P v := by
      rw [hmul]
      exact inf_le_right
    have heu : MulAction.stabilizer P (u * v) = MulAction.stabilizer P u :=
      Subgroup.eq_of_le_of_card_ge hleu (by rw [hstab (u * v) u huv hu])
    have hev : MulAction.stabilizer P (u * v) = MulAction.stabilizer P v :=
      Subgroup.eq_of_le_of_card_ge hlev (by rw [hstab (u * v) v huv hv])
    exact heu.symm.trans hev
  have hab : MulAction.stabilizer P a = MulAction.stabilizer P b :=
    hpair hij ha_mem hb_mem ha hb
  have hstab_all : ∀ i (u : E), u ∈ U i → u ≠ 1 →
      MulAction.stabilizer P u = MulAction.stabilizer P a := by
    intro i u hu_mem hu
    by_cases hi : i = i₀
    · subst i
      exact (hpair hij hu_mem hb_mem hu hb).trans hab.symm
    · exact hpair hi hu_mem ha_mem hu ha
  have hstab_a_bot : MulAction.stabilizer P a = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    apply FaithfulSMul.eq_of_smul_eq_smul (α := E)
    intro e
    let K : Subgroup E := fixedPointSubgroup (Subgroup.zpowers g) E
    have hUiK : ∀ i, U i ≤ K := by
      intro i u hu
      rw [FixedPoints.mem_subgroup]
      intro z
      by_cases hu1 : u = 1
      · simp [hu1]
      · have hgu : g ∈ MulAction.stabilizer P u := by
          rw [hstab_all i u hu hu1]
          exact hg
        exact MulAction.mem_stabilizer_iff.mp
          (Subgroup.zpowers_le.mpr hgu z.2)
    have htopK : (⊤ : Subgroup E) ≤ K := by
      rw [← hspan]
      exact iSup_le hUiK
    have heK : e ∈ K := htopK (Subgroup.mem_top e)
    have hge : g • e = e := by
      rw [FixedPoints.mem_subgroup] at heK
      exact heK ⟨g, Subgroup.mem_zpowers g⟩
    simpa using hge
  intro x hx e hxe
  by_contra he
  have hxmem : x ∈ MulAction.stabilizer P e :=
    MulAction.mem_stabilizer_iff.mpr hxe
  have hstab_e_bot : MulAction.stabilizer P e = ⊥ := by
    apply Subgroup.card_eq_one.mp
    calc
      Nat.card (MulAction.stabilizer P e) =
          Nat.card (MulAction.stabilizer P a) := hstab e a he ha
      _ = 1 := by rw [hstab_a_bot]; exact Nat.card_unique
  rw [hstab_e_bot] at hxmem
  exact hx (Subgroup.mem_bot.mp hxmem)

private theorem peterfalvi_appendixI_proposition_1_crossBlock_stabilizer_of_odd_permuted_iSupIndep
    {P E ι : Type*} [Group P] [Finite P] [Group E] [IsMulCommutative E]
    [MulDistribMulAction P E] [MulAction P ι]
    (hPodd : Odd (Nat.card P))
    (U : ι → Subgroup E)
    (hindep : iSupIndep U)
    (hperm : ∀ (g : P) (i : ι) {e : E}, e ∈ U i → g • e ∈ U (g • i)) :
    ∀ {i j : ι}, i ≠ j → ∀ {a b : E},
      a ∈ U i → b ∈ U j → a ≠ 1 → b ≠ 1 →
        a * b ≠ 1 ∧
          MulAction.stabilizer P (a * b) =
            MulAction.stabilizer P a ⊓ MulAction.stabilizer P b := by
  classical
  intro i j hij a b ha_mem hb_mem ha hb
  have hdisj : Disjoint (U i) (U j) := hindep.pairwiseDisjoint hij
  have hab_ne : a * b ≠ 1 := by
    intro hab
    have habinv : a = b⁻¹ := by
      calc
        a = a * b * b⁻¹ := by simp
        _ = b⁻¹ := by rw [hab]; simp
    have ha_j : a ∈ U j := by
      rw [habinv]
      exact (U j).inv_mem hb_mem
    have ha_bot : a ∈ (⊥ : Subgroup E) := by
      rw [← disjoint_iff.mp hdisj]
      exact ⟨ha_mem, ha_j⟩
    exact ha (Subgroup.mem_bot.mp ha_bot)
  refine ⟨hab_ne, ?_⟩
  ext g
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_inf]
  constructor
  · intro hg
    have hga_mem : g • a ∈ U (g • i) := hperm g i ha_mem
    have hgb_mem : g • b ∈ U (g • j) := hperm g j hb_mem
    have hga_ne : g • a ≠ 1 := by
      intro hga
      apply ha
      calc
        a = g⁻¹ • (g • a) := (inv_smul_smul g a).symm
        _ = g⁻¹ • 1 := by rw [hga]
        _ = 1 := by simp
    have hgb_ne : g • b ≠ 1 := by
      intro hgb
      apply hb
      calc
        b = g⁻¹ • (g • b) := (inv_smul_smul g b).symm
        _ = g⁻¹ • 1 := by rw [hgb]
        _ = 1 := by simp
    have hprod : (g • a) * (g • b) = a * b := by simpa using hg
    have hindices : g • i ≠ g • j := by
      intro heq
      apply hij
      have := congrArg (fun z : ι => g⁻¹ • z) heq
      simpa using this
    have hgi : g • i = i ∨ g • i = j := by
      by_contra hk
      simp only [not_or] at hk
      let Rest : Subgroup E := ⨆ l, ⨆ _ : l ≠ g • i, U l
      have ha_rest : a ∈ Rest := by
        apply (show U i ≤ Rest from ?_) ha_mem
        dsimp [Rest]
        exact le_iSup_of_le i (le_iSup_of_le (Ne.symm hk.1) le_rfl)
      have hb_rest : b ∈ Rest := by
        apply (show U j ≤ Rest from ?_) hb_mem
        dsimp [Rest]
        exact le_iSup_of_le j (le_iSup_of_le (Ne.symm hk.2) le_rfl)
      have hgb_rest : g • b ∈ Rest := by
        apply (show U (g • j) ≤ Rest from ?_) hgb_mem
        dsimp [Rest]
        exact le_iSup_of_le (g • j) (le_iSup_of_le (Ne.symm hindices) le_rfl)
      have hga_eq : g • a = a * b * (g • b)⁻¹ := by
        calc
          g • a = (g • a) * (g • b) * (g • b)⁻¹ := by simp
          _ = a * b * (g • b)⁻¹ := by rw [hprod]
      have hga_rest : g • a ∈ Rest := by
        rw [hga_eq]
        exact Rest.mul_mem (Rest.mul_mem ha_rest hb_rest) (Rest.inv_mem hgb_rest)
      have hga_bot : g • a ∈ (⊥ : Subgroup E) := by
        rw [← disjoint_iff.mp (iSupIndep_def.mp hindep (g • i))]
        exact ⟨hga_mem, hga_rest⟩
      exact hga_ne (Subgroup.mem_bot.mp hga_bot)
    have hgj : g • j = i ∨ g • j = j := by
      have hprod' : (g • b) * (g • a) = a * b := by
        calc
          (g • b) * (g • a) = (g • a) * (g • b) := mul_comm (g • b) (g • a)
          _ = a * b := hprod
      -- Repeat the support isolation with the two acted-on summands reversed.
      by_contra h
      simp only [not_or] at h
      let Rest : Subgroup E := ⨆ l, ⨆ _ : l ≠ g • j, U l
      have ha_rest : a ∈ Rest :=
        (show U i ≤ Rest from by
          dsimp [Rest]
          exact le_iSup_of_le i (le_iSup_of_le (Ne.symm h.1) le_rfl)) ha_mem
      have hb_rest : b ∈ Rest :=
        (show U j ≤ Rest from by
          dsimp [Rest]
          exact le_iSup_of_le j (le_iSup_of_le (Ne.symm h.2) le_rfl)) hb_mem
      have hga_rest : g • a ∈ Rest :=
        (show U (g • i) ≤ Rest from by
          dsimp [Rest]
          exact le_iSup_of_le (g • i) (le_iSup_of_le hindices le_rfl)) hga_mem
      have hgb_eq : g • b = a * b * (g • a)⁻¹ := by
        calc
          g • b = (g • b) * (g • a) * (g • a)⁻¹ := by simp
          _ = a * b * (g • a)⁻¹ := by rw [hprod']
      have hgb_rest : g • b ∈ Rest := by
        rw [hgb_eq]
        exact Rest.mul_mem (Rest.mul_mem ha_rest hb_rest) (Rest.inv_mem hga_rest)
      have hgb_bot : g • b ∈ (⊥ : Subgroup E) := by
        rw [← disjoint_iff.mp (iSupIndep_def.mp hindep (g • j))]
        exact ⟨hgb_mem, hgb_rest⟩
      exact hgb_ne (Subgroup.mem_bot.mp hgb_bot)
    have hindices : g • i ≠ g • j := by
      intro h
      apply hij
      have := congrArg (fun z : ι => g⁻¹ • z) h
      simpa using this
    have hcases :
        (g • i = i ∧ g • j = j) ∨ (g • i = j ∧ g • j = i) := by
      rcases hgi with hgi | hgi
      · left
        refine ⟨hgi, hgj.resolve_left ?_⟩
        intro hgj_i
        exact hindices (hgi.trans hgj_i.symm)
      · right
        refine ⟨hgi, hgj.resolve_right ?_⟩
        intro hgj_j
        exact hindices (hgi.trans hgj_j.symm)
    have hnot_swap : ¬ (g • i = j ∧ g • j = i) := by
      rintro ⟨hgi_j, hgj_i⟩
      have hg_sq_fix : g ^ 2 • i = i := by
        rw [pow_two, mul_smul, hgi_j, hgj_i]
      have hg_sq_mem : g ^ 2 ∈ MulAction.stabilizer P i :=
        MulAction.mem_stabilizer_iff.mpr hg_sq_fix
      have hgodd : Odd (orderOf g) :=
        Odd.of_dvd_nat hPodd (orderOf_dvd_natCard g)
      obtain ⟨m, hm⟩ := hgodd
      have hg_zpowers : g ∈ Subgroup.zpowers (g ^ 2) := by
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨Int.ofNat (m + 1), ?_⟩
        calc
          (g ^ 2) ^ (↑m + 1 : ℤ) = (g ^ 2) ^ ((m + 1 : ℕ) : ℤ) := by
            norm_num
          _ = (g ^ 2) ^ (m + 1) := by rw [zpow_natCast]
          _ = g ^ (2 * (m + 1)) := by rw [pow_mul]
          _ = g ^ (2 * m + 2) := by ring_nf
          _ = g ^ (orderOf g + 1) := by rw [hm]
          _ = g := by rw [pow_add, pow_orderOf_eq_one, one_mul, pow_one]
      have hg_mem : g ∈ MulAction.stabilizer P i :=
        (Subgroup.zpowers_le.mpr hg_sq_mem) hg_zpowers
      have hgi_i : g • i = i := MulAction.mem_stabilizer_iff.mp hg_mem
      exact hij (hgi_i.symm.trans hgi_j)
    obtain ⟨hgi_i, hgj_j⟩ := hcases.resolve_right hnot_swap
    have hga_i : g • a ∈ U i := by simpa [hgi_i] using hga_mem
    have hgb_j : g • b ∈ U j := by simpa [hgj_j] using hgb_mem
    have hcross_eq : (g • a)⁻¹ * a = (g • b) * b⁻¹ := by
      calc
        (g • a)⁻¹ * a = (g • a)⁻¹ * (a * b) * b⁻¹ := by group
        _ = (g • a)⁻¹ * ((g • a) * (g • b)) * b⁻¹ := by rw [hprod]
        _ = (g • b) * b⁻¹ := by group
    have hcross_bot : (g • a)⁻¹ * a ∈ (⊥ : Subgroup E) := by
      rw [← disjoint_iff.mp hdisj]
      exact ⟨(U i).mul_mem ((U i).inv_mem hga_i) ha_mem, by
        rw [hcross_eq]
        exact (U j).mul_mem hgb_j ((U j).inv_mem hb_mem)⟩
    have hga : g • a = a :=
      inv_mul_eq_one.mp (Subgroup.mem_bot.mp hcross_bot)
    have hgb : g • b = b := by
      rw [hga] at hprod
      exact mul_left_cancel hprod
    exact ⟨hga, hgb⟩
  · rintro ⟨hga, hgb⟩
    simp [hga, hgb]

/-- Stabilizer intersection for Peterfalvi's preliminary direct-sum argument. -/
private theorem peterfalvi_appendixI_proposition_1_stabilizer_mul_eq_inf
    {P E : Type*} [Group P] [Group E]
    [MulDistribMulAction P E]
    (U V : Subgroup E) [IsInvariant P E U] [IsInvariant P E V]
    (hcompl : IsCompl U V) {a b : E} (haU : a ∈ U) (hbV : b ∈ V) :
    MulAction.stabilizer P (a * b) =
      MulAction.stabilizer P a ⊓ MulAction.stabilizer P b := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_inf]
  constructor
  · intro hg
    have hgaU : g • a ∈ U :=
      (IsInvariant.invariant (A := P) (G := E) (H := U) g a).mp haU
    have hgbV : g • b ∈ V :=
      (IsInvariant.invariant (A := P) (G := E) (H := V) g b).mp hbV
    have hprod : (g • a) * (g • b) = a * b := by simpa using hg
    have hcross : (g • a)⁻¹ * a = (g • b) * b⁻¹ := by
      calc
        (g • a)⁻¹ * a = (g • a)⁻¹ * (a * b) * b⁻¹ := by group
        _ = (g • a)⁻¹ * ((g • a) * (g • b)) * b⁻¹ := by rw [hprod]
        _ = (g • b) * b⁻¹ := by group
    have hcrossBot : (g • a)⁻¹ * a ∈ (⊥ : Subgroup E) := by
      rw [← hcompl.inf_eq_bot]
      exact ⟨U.mul_mem (U.inv_mem hgaU) haU, by
        rw [hcross]
        exact V.mul_mem hgbV (V.inv_mem hbV)⟩
    have hga : g • a = a :=
      inv_mul_eq_one.mp (Subgroup.mem_bot.mp hcrossBot)
    have hgb : g • b = b := by
      rw [hga] at hprod
      exact mul_left_cancel hprod
    exact ⟨hga, hgb⟩
  · rintro ⟨hga, hgb⟩
    simp [hga, hgb]

/-- Peterfalvi's preliminary direct-sum argument for two invariant complementary summands. -/
private theorem peterfalvi_appendixI_proposition_1_fixedPointFree_of_invariant_isCompl
    {q : ℕ} [Fact q.Prime]
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian q E]
    [MulDistribMulAction P E] [FaithfulSMul P E]
    (U V : Subgroup E) [IsInvariant P E U] [IsInvariant P E V]
    (hU : U ≠ ⊥) (hV : V ≠ ⊥) (hcompl : IsCompl U V)
    (hstab : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (MulAction.stabilizer P a) =
        Nat.card (MulAction.stabilizer P b)) :
    ∀ x : P, x ≠ 1 → ∀ e : E, x • e = e → e = 1 := by
  classical
  obtain ⟨aU, haU_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  obtain ⟨bV, hbV_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
  let a : E := aU
  let b : E := bV
  have haU : a ∈ U := aU.2
  have hbV : b ∈ V := bV.2
  have ha : a ≠ 1 := by
    intro ha1
    exact haU_ne (Subtype.ext (by simpa [a] using ha1))
  have hb : b ≠ 1 := by
    intro hb1
    exact hbV_ne (Subtype.ext (by simpa [b] using hb1))
  have hne_mul {u v : E} (huU : u ∈ U) (hvV : v ∈ V)
      (hu : u ≠ 1) : u * v ≠ 1 := by
    intro huv
    apply hu
    have huV : u ∈ V := by
      have : u = v⁻¹ := by
        calc
          u = u * v * v⁻¹ := by simp
          _ = v⁻¹ := by rw [huv]; simp
      rw [this]
      exact V.inv_mem hvV
    exact Subgroup.mem_bot.mp (by
      rw [← hcompl.inf_eq_bot]
      exact ⟨huU, huV⟩)
  have hpair {u v : E} (huU : u ∈ U) (hvV : v ∈ V)
      (hu : u ≠ 1) (hv : v ≠ 1) :
      MulAction.stabilizer P u = MulAction.stabilizer P v := by
    have huv : u * v ≠ 1 := hne_mul huU hvV hu
    have hmul :=
      peterfalvi_appendixI_proposition_1_stabilizer_mul_eq_inf (P := P) (E := E) U V hcompl huU hvV
    have hleu : MulAction.stabilizer P (u * v) ≤ MulAction.stabilizer P u := by
      rw [hmul]
      exact inf_le_left
    have hlev : MulAction.stabilizer P (u * v) ≤ MulAction.stabilizer P v := by
      rw [hmul]
      exact inf_le_right
    have heu : MulAction.stabilizer P (u * v) = MulAction.stabilizer P u :=
      Subgroup.eq_of_le_of_card_ge hleu (by rw [hstab (u * v) u huv hu])
    have hev : MulAction.stabilizer P (u * v) = MulAction.stabilizer P v :=
      Subgroup.eq_of_le_of_card_ge hlev (by rw [hstab (u * v) v huv hv])
    exact heu.symm.trans hev
  have hab := hpair haU hbV ha hb
  have hstab_U : ∀ u : E, u ∈ U → u ≠ 1 →
      MulAction.stabilizer P u = MulAction.stabilizer P a := by
    intro u huU hu
    exact (hpair huU hbV hu hb).trans hab.symm
  have hstab_V : ∀ v : E, v ∈ V → v ≠ 1 →
      MulAction.stabilizer P v = MulAction.stabilizer P a := by
    intro v hvV hv
    exact (hpair haU hvV ha hv).symm
  have hstab_a_bot : MulAction.stabilizer P a = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    apply FaithfulSMul.eq_of_smul_eq_smul (α := E)
    intro e
    have hfixU : ∀ u : E, u ∈ U → g • u = u := by
      intro u hu
      by_cases hu1 : u = 1
      · simp [hu1]
      · exact MulAction.mem_stabilizer_iff.mp (by
          rw [hstab_U u hu hu1]
          exact hg)
    have hfixV : ∀ v : E, v ∈ V → g • v = v := by
      intro v hv
      by_cases hv1 : v = 1
      · simp [hv1]
      · exact MulAction.mem_stabilizer_iff.mp (by
          rw [hstab_V v hv hv1]
          exact hg)
    have hmem : e ∈ U ⊔ V := by
      rw [hcompl.sup_eq_top]
      exact Subgroup.mem_top e
    letI : IsMulCommutative E :=
      (inferInstance : IsElementaryAbelian q E).toIsMulCommutative
    letI : V.Normal := Subgroup.normal_of_isMulCommutative V
    obtain ⟨u, hu, v, hv, huv⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    calc
      g • e = g • (u * v) := by rw [huv]
      _ = (g • u) * (g • v) :=
        map_mul (MulDistribMulAction.toMulAut P E g) u v
      _ = u * v := by rw [hfixU u hu, hfixV v hv]
      _ = (1 : P) • e := by simp [huv]
  intro x hx e hxe
  by_contra he
  have hxmem : x ∈ MulAction.stabilizer P e :=
    MulAction.mem_stabilizer_iff.mpr hxe
  have hstab_e_bot : MulAction.stabilizer P e = ⊥ := by
    apply Subgroup.card_eq_one.mp
    calc
      Nat.card (MulAction.stabilizer P e) =
          Nat.card (MulAction.stabilizer P a) := hstab e a he ha
      _ = 1 := by rw [hstab_a_bot]; exact Nat.card_unique
  rw [hstab_e_bot] at hxmem
  exact hx (Subgroup.mem_bot.mp hxmem)

/-- Transfer the preliminary direct-sum argument from complementary subrepresentations to invariant subgroups of E. -/
private theorem peterfalvi_appendixI_proposition_1_fixedPointFree_of_isCompl_subrepresentations
    {q : ℕ} [Fact q.Prime]
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian q E]
    [MulDistribMulAction P E] [FaithfulSMul P E]
    (ρ : Representation (ZMod q) P (Additive E))
    (hρ : ρ = Theory.Representation.ofElementaryAbelianAction
      (A := P) (G := E) (p := q))
    (W C : Subrepresentation ρ)
    (hW : W ≠ ⊥) (hC : C ≠ ⊥) (hcompl : IsCompl W C)
    (hstab : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (MulAction.stabilizer P a) =
        Nat.card (MulAction.stabilizer P b)) :
    ∀ x : P, x ≠ 1 → ∀ e : E, x • e = e → e = 1 := by
  classical
  letI : CommGroup E := IsMulCommutative.instCommGroup
  let η : Subgroup E ≃o Submodule (ZMod q) (Additive E) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := q))
  let U : Subgroup E := η.symm W.toSubmodule
  let V : Subgroup E := η.symm C.toSubmodule
  have hU : U ≠ ⊥ := by
    intro hUbot
    apply hW
    apply Subrepresentation.toSubmodule_injective
    have himage := congrArg η hUbot
    calc
      W.toSubmodule = η U := by simp [U]
      _ = η (⊥ : Subgroup E) := himage
      _ = (⊥ : Submodule (ZMod q) (Additive E)) := η.map_bot
      _ = (⊥ : Subrepresentation ρ).toSubmodule := rfl
  have hV : V ≠ ⊥ := by
    intro hVbot
    apply hC
    apply Subrepresentation.toSubmodule_injective
    have himage := congrArg η hVbot
    calc
      C.toSubmodule = η V := by simp [V]
      _ = η (⊥ : Subgroup E) := himage
      _ = (⊥ : Submodule (ZMod q) (Additive E)) := η.map_bot
      _ = (⊥ : Subrepresentation ρ).toSubmodule := rfl
  have hcompl_sub : IsCompl W.toSubmodule C.toSubmodule := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      have himage := congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
      have : (⊥ : Subrepresentation ρ).toSubmodule = (⊥ : Submodule (ZMod q) (Additive E)) := rfl
      simpa using (himage.trans this)
    · rw [codisjoint_iff]
      have himage := congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
      have : (⊤ : Subrepresentation ρ).toSubmodule = (⊤ : Submodule (ZMod q) (Additive E)) := rfl
      simpa using (himage.trans this)
  have hcompl_UV : IsCompl U V := by
    apply (OrderIso.isCompl_iff (f := η) (x := U) (y := V)).2
    simpa [U, V] using hcompl_sub
  letI : IsInvariant P E U := by
    refine ⟨?_⟩
    intro g e
    constructor
    · intro he
      have heW : Additive.ofMul e ∈ W.toSubmodule := by
        simpa [U, η] using he
      have hsmul := W.apply_mem_toSubmodule g heW
      simpa [hρ, U, η] using hsmul
    · intro hge
      have hgeW : Additive.ofMul (g • e) ∈ W.toSubmodule := by
        simpa [U, η] using hge
      have hsmul := W.apply_mem_toSubmodule g⁻¹ hgeW
      simpa [hρ, U, η, inv_smul_smul] using hsmul
  letI : IsInvariant P E V := by
    refine ⟨?_⟩
    intro g e
    constructor
    · intro he
      have heC : Additive.ofMul e ∈ C.toSubmodule := by
        simpa [V, η] using he
      have hsmul := C.apply_mem_toSubmodule g heC
      simpa [hρ, V, η] using hsmul
    · intro hge
      have hgeC : Additive.ofMul (g • e) ∈ C.toSubmodule := by
        simpa [V, η] using hge
      have hsmul := C.apply_mem_toSubmodule g⁻¹ hgeC
      simpa [hρ, V, η, inv_smul_smul] using hsmul
  exact
    peterfalvi_appendixI_proposition_1_fixedPointFree_of_invariant_isCompl
      (q := q) (P := P) (E := E) U V hU hV hcompl_UV hstab

private theorem peterfalvi_appendixI_proposition_1_irreducible_noncyclic_centerLine
    {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hp_ne_two : p ≠ 2) (hncyc : ¬ IsCyclic P) :
    ∃ (R : Subgroup P) (z : P),
      R.Normal ∧ Nat.card R = p ^ 2 ∧ IsElementaryAbelian p R ∧
        z ∈ R ∧ z ≠ 1 ∧ z ∈ Subgroup.center P ∧
          Nat.card (Subgroup.zpowers z) = p := by
  classical
  letI : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨R, hRnormal, hRcard, hRelem⟩ :=
    lemma_4_5_a (p := p) (R := P) hp_ne_two hncyc
  letI : R.Normal := hRnormal
  have hR_nontrivial : Nontrivial R :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hRcard]
      exact one_lt_pow' (Fact.out : Nat.Prime p).one_lt two_ne_zero)
  letI : Nontrivial R := hR_nontrivial
  obtain ⟨zR, hzR_ne, hz_center⟩ :=
    exists_nontrivial_center_mem_normal (G := P) (p := p) R
  let z : P := zR
  have hzR : z ∈ R := zR.2
  have hz_ne : z ≠ 1 := by
    intro hz
    exact hzR_ne (Subtype.ext (by simpa [z] using hz))
  letI : IsElementaryAbelian p R := hRelem
  have hzR_pow : zR ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p R) zR
  have hz_pow : z ^ p = 1 := by
    simpa [z] using congrArg Subtype.val hzR_pow
  have hz_order : orderOf z = p := orderOf_eq_prime hz_pow hz_ne
  have hz_card : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, hz_order]
  exact ⟨R, z, hRnormal, hRcard, hRelem, hzR, hz_ne, hz_center, hz_card⟩

private theorem peterfalvi_appendixI_proposition_1_invariants_eq_bot_of_irreducible_not_le_ker
    {F T V : Type*} [Field F] [Group T]
    [AddCommGroup V] [Module F V]
    (ρ : Representation F T V) [Representation.IsIrreducible ρ]
    (K : Subgroup T) [K.Normal] (hKker : ¬ K ≤ ρ.ker) :
    Representation.invariants (ρ.comp K.subtype) = ⊥ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp K.subtype)
      apply_mem_toSubmodule := Representation.le_comap_invariants ρ K }
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS
  · calc
      Representation.invariants (ρ.comp K.subtype) = S.toSubmodule := rfl
      _ = (⊥ : Subrepresentation ρ).toSubmodule := congrArg Subrepresentation.toSubmodule hS
      _ = (⊥ : Submodule F V) := rfl
  · have hStop : Representation.invariants (ρ.comp K.subtype) = (⊤ : Submodule F V) := by
      calc
        Representation.invariants (ρ.comp K.subtype) = S.toSubmodule := rfl
        _ = (⊤ : Subrepresentation ρ).toSubmodule := congrArg Subrepresentation.toSubmodule hS
        _ = (⊤ : Submodule F V) := rfl
    exfalso
    apply hKker
    intro k hk
    rw [MonoidHom.mem_ker]
    ext v
    have hv : v ∈ Representation.invariants (ρ.comp K.subtype) := by
      rw [hStop]
      simp
    exact hv ⟨k, hk⟩

private theorem peterfalvi_appendixI_proposition_1_fixedPointSubgroup_centerLine_eq_bot
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian q E]
    [MulDistribMulAction P E] [FaithfulSMul P E]
    (z : P) (hz_ne : z ≠ 1) (hz_center : z ∈ Subgroup.center P)
    (hirr : Representation.IsIrreducible
      (Theory.Representation.ofElementaryAbelianAction (A := P) (G := E) (p := q))) :
    fixedPointSubgroup (Subgroup.zpowers z) E = ⊥ := by
  classical
  letI : CommGroup E := IsMulCommutative.instCommGroup
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := P) (G := E) (p := q)
  letI : Representation.IsIrreducible ρ := by simpa [ρ] using hirr
  let Z : Subgroup P := Subgroup.zpowers z
  have hZ_le_center : Z ≤ Subgroup.center P :=
    Subgroup.zpowers_le.mpr hz_center
  have hZnormal : Z.Normal := by
    constructor
    intro x hx g
    have hcomm : g * x = x * g :=
      Subgroup.mem_center_iff.mp (hZ_le_center hx) g
    have hconj : g * x * g⁻¹ = x := by rw [hcomm]; simp
    rw [hconj]
    exact hx
  letI : Z.Normal := hZnormal
  have hρinj : Function.Injective ρ := by
    intro a b hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α := E)
    intro e
    have h := DFunLike.congr_fun hab (Additive.ofMul e)
    exact Additive.ofMul.injective (by simpa [ρ] using h)
  have hZ_not_ker : ¬ Z ≤ ρ.ker := by
    intro hZker
    have hzker : z ∈ ρ.ker := hZker (Subgroup.mem_zpowers z)
    apply hz_ne
    apply hρinj
    rw [MonoidHom.mem_ker] at hzker
    simpa using hzker
  have hInv : Representation.invariants (ρ.comp Z.subtype) = ⊥ :=
    peterfalvi_appendixI_proposition_1_invariants_eq_bot_of_irreducible_not_le_ker ρ Z hZ_not_ker
  apply bot_unique
  intro e he
  rw [FixedPoints.mem_subgroup] at he
  have heInv : Additive.ofMul (e : E) ∈
      Representation.invariants (ρ.comp Z.subtype) := by
    rw [Representation.mem_invariants]
    intro zZ
    have hez : (zZ : P) • (e : E) = e := he zZ
    simpa [ρ] using congrArg Additive.ofMul hez
  have hezero : Additive.ofMul (e : E) = 0 := by
    have : Additive.ofMul (e : E) ∈
        (⊥ : Submodule (ZMod q) (Additive E)) := by
      simpa [hInv] using heInv
    simpa using this
  change (e : E) = 1
  apply Additive.ofMul.injective
  simpa using hezero

/-- Cross-characteristic branch of the fixed-point-free core. -/
private theorem peterfalvi_appendixI_proposition_1_pGroup_fixedPointFree_crossPrime
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian q E]
    [MulDistribMulAction P E] [FaithfulSMul P E]
    (hP : IsPGroup p P)
    (hp_ne_two : p ≠ 2)
    (hp_ne_q : p ≠ q)
    (hstab : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (MulAction.stabilizer P a) =
        Nat.card (MulAction.stabilizer P b)) :
    ∀ x : P, x ≠ 1 → ∀ e : E, x • e = e → e = 1 := by
  classical
  by_cases hE : Nontrivial E
  · letI : Nontrivial E := hE
    let ρ : Representation (ZMod q) P (Additive E) :=
      Theory.Representation.ofElementaryAbelianAction (A := P) (G := E) (p := q)
    obtain ⟨n, hcardP⟩ := hP.exists_card_eq
    have hp_not_dvd_q : ¬ p ∣ q := by
      intro hpq
      exact hp_ne_q
        ((Nat.prime_dvd_prime_iff_eq
          (Fact.out : p.Prime) (Fact.out : q.Prime)).mp hpq)
    have hcop : Nat.Coprime q (Nat.card P) := by
      rw [hcardP]
      exact
        ((Fact.out : p.Prime).coprime_pow_of_not_dvd
          (m := n) hp_not_dvd_q)
    have hring : ringChar (ZMod q) = q := ringChar.eq (ZMod q) q
    have hchar :
        ringChar (ZMod q) = 0 ∨
          Nat.Prime (ringChar (ZMod q)) ∧
            (ringChar (ZMod q)).Coprime (Nat.card P) := by
      right
      rw [hring]
      exact ⟨Fact.out, hcop⟩
    have hsemi : ρ.IsCompletelyReducible :=
      Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
        ρ hchar
    letI : ComplementedLattice (Subrepresentation ρ) := by
      exact
        (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
          (ρ := ρ)).2 hsemi
    by_cases hirr : Representation.IsIrreducible ρ
    · letI : Representation.IsIrreducible ρ := hirr
      by_cases hPcyc : IsCyclic P
      · letI : IsCyclic P := hPcyc
        letI : IsMulCommutative P := IsCyclic.isMulCommutative
        intro x hx e hxe
        by_contra he
        let H : Subgroup P := Subgroup.zpowers x
        letI : H.Normal := Subgroup.normal_of_isMulCommutative H
        let S : Subrepresentation ρ := {
          toSubmodule := ρ.fixedSubspace H
          apply_mem_toSubmodule := by
            intro g v hv
            change ∀ h : H, ρ h (ρ g v) = ρ g v
            intro h
            have hvh : ρ h v = v := hv h
            calc
              ρ h (ρ g v) = ((ρ h) * (ρ g)) v := rfl
              _ = ρ ((h : P) * g) v := by rw [← ρ.map_mul]
              _ = ρ (g * (h : P)) v := by rw [mul_comm]
              _ = ((ρ g) * (ρ h)) v := by rw [ρ.map_mul]
              _ = ρ g (ρ h v) := rfl
              _ = ρ g v := by rw [hvh] }
        have hvfix : Additive.ofMul e ∈ ρ.fixedSubspace H := by
          change ∀ h : H, ρ h (Additive.ofMul e) = Additive.ofMul e
          intro h
          have hzp_le :
              Subgroup.zpowers x ≤ MulAction.stabilizer P e :=
            Subgroup.zpowers_le.mpr hxe
          have hhfix : (h : P) • e = e :=
            MulAction.mem_stabilizer_iff.mp (hzp_le h.2)
          simpa [ρ, Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using hhfix
        have hS_ne : S ≠ ⊥ := by
          intro hS
          have hfix_bot : ρ.fixedSubspace H = ⊥ := by
            calc
              ρ.fixedSubspace H = S.toSubmodule := rfl
              _ = (⊥ : Subrepresentation ρ).toSubmodule := congrArg Subrepresentation.toSubmodule hS
              _ = (⊥ : Submodule (ZMod q) (Additive E)) := rfl
          have hvbot : Additive.ofMul e ∈ (⊥ : Submodule (ZMod q) (Additive E)) := by
            rw [← hfix_bot]
            exact hvfix
          have hveq : Additive.ofMul e = 0 := by simpa using hvbot
          exact he (by simpa using hveq)
        have hS_top : S = ⊤ := by
          rcases (inferInstance : Representation.IsIrreducible ρ).eq_bot_or_eq_top S with
            hbot | htop
          · exact False.elim (hS_ne hbot)
          · exact htop
        have hfix_top : ρ.fixedSubspace H = ⊤ := by
          calc
            ρ.fixedSubspace H = S.toSubmodule := rfl
            _ = (⊤ : Subrepresentation ρ).toSubmodule := congrArg Subrepresentation.toSubmodule hS_top
            _ = (⊤ : Submodule (ZMod q) (Additive E)) := rfl
        have hxrep : ρ x = 1 := by
          ext v
          have hv : v ∈ ρ.fixedSubspace H := by simp [hfix_top]
          simpa using hv ⟨x, Subgroup.mem_zpowers x⟩
        apply hx
        apply FaithfulSMul.eq_of_smul_eq_smul (α := E)
        intro a
        have ha := DFunLike.congr_fun hxrep (Additive.ofMul a)
        simpa [ρ, Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using ha
      · have hnoncyclicEndpoint :
            ∀ x : P, x ≠ 1 → ∀ e : E, x • e = e → e = 1 := by
          obtain ⟨R, z, hRnormal, hRcard, hRelem, hzR, hz_ne, hz_center, _hzcard⟩ :=
            peterfalvi_appendixI_proposition_1_irreducible_noncyclic_centerLine
              (p := p) hP hp_ne_two hPcyc
          letI : R.Normal := hRnormal
          letI : IsElementaryAbelian p R := hRelem
          have hRnoncyc : ¬ IsCyclic R :=
            IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hRcard
          have hfix_z : fixedPointSubgroup (Subgroup.zpowers z) E = ⊥ :=
            peterfalvi_appendixI_proposition_1_fixedPointSubgroup_centerLine_eq_bot
              (p := p) (q := q) z hz_ne hz_center (inferInstance : Representation.IsIrreducible ρ)
          have hfix_top : fixedPointSubgroup (↥(⊤ : Subgroup R)) E = ⊥ := by
            apply bot_unique
            intro e he
            have hez : e ∈ fixedPointSubgroup (Subgroup.zpowers z) E := by
              rw [FixedPoints.mem_subgroup] at he ⊢
              intro w
              have hwR : (w : P) ∈ R :=
                (Subgroup.zpowers_le.mpr hzR) w.2
              have hwe := he ⟨⟨w, hwR⟩, by simp⟩
              have hwe' : (w : P) • e = e := by simpa using hwe
              calc
                w • e = (w : P) • e := rfl
                _ = e := hwe'
            simpa [hfix_z] using hez
          let Ω := {Y : Subgroup R //
            Y.index = p ∧ fixedPointSubgroup (↥Y) E ≠ ⊥}
          let F : Ω → Subgroup E := fun Y => fixedPointSubgroup (↥Y.1) E
          obtain ⟨hFindep, hFspan⟩ :=
            peterfalvi_appendixI_proposition_1_hyperplane_fixed_iSupIndep_and_iSup_top
              (R := R) (E := E) (p := p) (q := q) hp_ne_q hRnoncyc hfix_top
          letI : Fintype Ω := Fintype.ofFinite Ω
          have hΩ_nonempty : Nonempty Ω := by
            by_contra hΩ
            have hbot : iSup F = ⊥ := by
              apply bot_unique
              refine iSup_le ?_
              intro Y
              exact False.elim (hΩ ⟨Y⟩)
            exact top_ne_bot (hFspan.symm.trans hbot)
          have hfaithR :
              actionCentralizerIn (A := R) (G := E) (⊤ : Subgroup R) = ⊥ := by
            rw [actionCentralizerIn, top_inf_eq,
              fixingSubgroupOf_univ_eq_ker_toMulAut, MonoidHom.ker_eq_bot_iff]
            intro a b hab
            apply FaithfulSMul.eq_of_smul_eq_smul (α := E)
            intro e
            exact DFunLike.congr_fun hab e
          have htwo : ∃ Y Z : Ω, Y ≠ Z := by
            by_contra hYZ
            push Not at hYZ
            let Y : Ω := Classical.choice hΩ_nonempty
            have hFYtop : F Y = ⊤ := by
              apply top_unique
              rw [← hFspan]
              refine iSup_le ?_
              intro Z
              rw [hYZ Z Y]
            have hYcyc : IsCyclic (R ⧸ Y.1) := by
              have hcard : Nat.card (R ⧸ Y.1) = p := by
                simpa [Subgroup.index_eq_card] using Y.2.1
              exact isCyclic_of_prime_card (α := R ⧸ Y.1) hcard
            exact theorem_3_6_hyperplane_fixed_singleton_false
              hfaithR hYcyc hRnoncyc (by simpa [F] using hFYtop)
          letI : MulDistribMulAction P R :=
            MulDistribMulAction.compHom R ConjAct.toConjAct.toMonoidHom
          let ρR : P →* MulAut R := MulDistribMulAction.toMulAut P R
          let ρE : P →* MulAut E := MulDistribMulAction.toMulAut P E
          have hρ_transport (g : P) (r : R) (e : E) :
              ((ρR g) r) • ((ρE g) e) = (ρE g) (r • e) := by
            change ((g • r : R) : P) • (g • e) = g • ((r : P) • e)
            change (g * (r : P) * g⁻¹) • (g • e) = g • ((r : P) • e)
            simp [mul_smul]
          have hF_map_le (g : P) (Y : Ω) :
              (F Y).map (ρE g : E →* E) ≤
                fixedPointSubgroup (↥(Y.1.map (ρR g : R →* R))) E := by
            intro e he
            rcases Subgroup.mem_map.mp he with ⟨x, hx, rfl⟩
            change ∀ r : Y.1.map (ρR g : R →* R),
              (r : R) • ((ρE g) x) = (ρE g) x
            have hxfix : ∀ y : Y.1, (y : R) • x = x := by
              have hx' : x ∈ fixedPointSubgroup (↥Y.1) E := by
                simpa [F] using hx
              simpa [FixedPoints.mem_subgroup] using hx'
            intro r
            rcases Subgroup.mem_map.mp r.2 with ⟨y, hy, hyr⟩
            calc
              (r : R) • ((ρE g) x) = ((ρR g) y) • ((ρE g) x) := by
                simpa using congrArg (fun t : R => t • ((ρE g) x)) hyr.symm
              _ = (ρE g) (y • x) := hρ_transport g y x
              _ = (ρE g) x := by rw [hxfix ⟨y, hy⟩]
          letI : MulAction P Ω := {
            smul := fun g Y => by
              refine ⟨Y.1.map (ρR g : R →* R), ?_⟩
              have hindex : (Y.1.map (ρR g : R →* R)).index = p := by
                calc
                  (Y.1.map (ρR g : R →* R)).index = Y.1.index := by simp
                  _ = p := Y.2.1
              have hmap_ne_bot : (F Y).map (ρE g : E →* E) ≠ ⊥ := by
                intro hbot
                exact Y.2.2 <|
                  (Subgroup.map_eq_bot_iff_of_injective
                    (H := F Y) (f := (ρE g : E →* E)) (ρE g).injective).1 hbot
              have hfix_ne_bot :
                  fixedPointSubgroup (↥(Y.1.map (ρR g : R →* R))) E ≠ ⊥ := by
                intro hbot
                exact hmap_ne_bot
                  (le_bot_iff.mp ((hF_map_le g Y).trans (le_of_eq hbot)))
              exact ⟨hindex, hfix_ne_bot⟩
            one_smul := by
              intro Y
              apply Subtype.ext
              change Y.1.map (ρR 1 : R →* R) = Y.1
              ext x
              constructor
              · intro hx
                rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                simpa [ρR] using hy
              · intro hx
                exact Subgroup.mem_map.mpr ⟨x, hx, by simp [ρR]⟩
            mul_smul := by
              intro g h Y
              apply Subtype.ext
              change Y.1.map (ρR (g * h) : R →* R) =
                (Y.1.map (ρR h : R →* R)).map (ρR g : R →* R)
              ext x
              constructor
              · intro hx
                rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                exact Subgroup.mem_map.mpr
                  ⟨(ρR h) y, Subgroup.mem_map_of_mem (ρR h : R →* R) hy,
                    by simp [ρR, mul_smul]⟩
              · intro hx
                rcases Subgroup.mem_map.mp hx with ⟨w, hw, hwx⟩
                rcases Subgroup.mem_map.mp hw with ⟨y, hy, hyw⟩
                refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
                calc
                  (ρR (g * h)) y = (ρR g) ((ρR h) y) := by simp [ρR, mul_smul]
                  _ = (ρR g) w := by simpa using congrArg (ρR g) hyw
                  _ = x := hwx
          }
          have hperm : ∀ (g : P) (Y : Ω) {e : E},
              e ∈ F Y → g • e ∈ F (g • Y) := by
            intro g Y e he
            apply hF_map_le g Y
            exact Subgroup.mem_map.mpr ⟨e, he, rfl⟩
          obtain ⟨n, hPcard⟩ := hP.exists_card_eq
          have hPodd : Odd (Nat.card P) := by
            rw [hPcard]
            exact ((Fact.out : p.Prime).odd_of_ne_two hp_ne_two).pow
          exact peterfalvi_appendixI_proposition_1_fixedPointFree_of_crossBlock_stabilizer
            (q := q) F (fun Y => Y.2.2) hFspan htwo
              (peterfalvi_appendixI_proposition_1_crossBlock_stabilizer_of_odd_permuted_iSupIndep
                hPodd F hFindep hperm) hstab
        exact hnoncyclicEndpoint
    · have hex : ∃ W : Subrepresentation ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
        by_contra h
        apply hirr
        change IsSimpleOrder (Subrepresentation ρ)
        apply IsSimpleOrder.of_forall_eq_top
        intro W hWbot
        by_contra hWtop
        exact h ⟨W, hWbot, hWtop⟩
      obtain ⟨W, hWbot, hWtop⟩ := hex
      obtain ⟨C, hcompl⟩ := exists_isCompl W
      have hCbot : C ≠ ⊥ := by
        intro hC
        apply hWtop
        have hsup := hcompl.sup_eq_top
        rw [hC, sup_bot_eq] at hsup
        exact hsup
      exact
        peterfalvi_appendixI_proposition_1_fixedPointFree_of_isCompl_subrepresentations
          (q := q) (P := P) (E := E) ρ rfl W C hWbot hCbot hcompl hstab
  · letI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    intro _ _ e _
    exact Subsingleton.elim e 1
/-- Fixed-point-free core of the p-group lemma. This is the two-branch
argument in Peterfalvi's proof: invariant block decomposition in the reducible
case, and the normal elementary-abelian subgroup of order `p^2` in the
irreducible noncyclic case. -/
private theorem peterfalvi_appendixI_proposition_1_pGroup_fixedPointFree_core
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian q E]
    [MulDistribMulAction P E] [FaithfulSMul P E]
    (hP : IsPGroup p P)
    (hp_ne_two : p ≠ 2)
    (hstab : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (MulAction.stabilizer P a) =
        Nat.card (MulAction.stabilizer P b)) :
    ∀ x : P, x ≠ 1 → ∀ e : E, x • e = e → e = 1 := by
  by_cases hpq : p = q
  · subst q
    exact
      peterfalvi_appendixI_proposition_1_pGroup_fixedPointFree_samePrime
        (p := p) hP hstab
  · exact
      peterfalvi_appendixI_proposition_1_pGroup_fixedPointFree_crossPrime
        (p := p) (q := q) hP hp_ne_two hpq hstab
/-- The p-group lemma used in Appendix I, Proposition 1. An odd p-group acting
faithfully on an elementary abelian q-group, with all nonzero-vector
stabilizers of the same order, is cyclic and fixed-point-free. -/
public theorem peterfalvi_appendixI_proposition_1_pGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    [IsElementaryAbelian q E]
    [MulDistribMulAction P E] [FaithfulSMul P E]
    (hP : IsPGroup p P)
    (hp_ne_two : p ≠ 2)
    (hstab : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (MulAction.stabilizer P a) =
        Nat.card (MulAction.stabilizer P b)) :
    IsCyclic P ∧
      ∀ x : P, x ≠ 1 → ∀ e : E, x • e = e → e = 1 := by
  classical
  have hfixed :=
    peterfalvi_appendixI_proposition_1_pGroup_fixedPointFree_core
      (p := p) (q := q) hP hp_ne_two hstab
  refine ⟨?_, hfixed⟩
  by_cases hE : Nontrivial E
  · letI : Nontrivial E := hE
    have hregular : ActsRegularly P E := by
      intro x hx
      rw [Subgroup.eq_bot_iff_forall]
      intro e he
      have hxe : x • e = e := he ⟨x, Subgroup.mem_zpowers x⟩
      simpa using hfixed x hx e hxe
    obtain ⟨n, hcardP⟩ := hP.exists_card_eq
    have hPodd : Odd (Nat.card P) := by
      rw [hcardP]
      exact ((Fact.out : p.Prime).odd_of_ne_two hp_ne_two).pow
    have htop_p : IsPGroup p (⊤ : Subgroup P) := hP.to_subgroup ⊤
    have htop_cyclic : IsCyclic (⊤ : Subgroup P) :=
      isCyclic_of_odd_regular_pSubgroup
        (p := p) (H := E) (R := P) Fact.out hPodd hregular htop_p
    exact (Subgroup.topEquiv : (⊤ : Subgroup P) ≃* P).isCyclic.mp htop_cyclic
  · letI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    letI : Subsingleton P :=
      ⟨fun _ _ => FaithfulSMul.eq_of_smul_eq_smul (α := E) fun _ =>
        Subsingleton.elim _ _⟩
    exact isCyclic_of_subsingleton

private theorem peterfalvi_appendixI_proposition_1_sylow_map_le_pCore
    {H : Type*} [Group H] [Finite H]
    {N : Subgroup H} (hN : N.Normal) (hnil : Group.IsNilpotent N)
    (p : ℕ) [Fact p.Prime] (P : Sylow p N) :
    (P : Subgroup N).map N.subtype ≤ pCore p H := by
  have hP_normal :=
    Group.IsNilpotent.sylow_normal hnil p P
  have hP_char :=
    Sylow.characteristic_of_normal P hP_normal
  letI : (P : Subgroup N).Characteristic := hP_char
  have hmap_normal : ((P : Subgroup N).map N.subtype).Normal := by
    infer_instance
  have hmap_p := P.isPGroup'.map N.subtype
  exact le_sSup ⟨hmap_normal, hmap_p⟩

private theorem peterfalvi_appendixI_proposition_1_pCore
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    [IsElementaryAbelian q E] [MulDistribMulAction D E] [FaithfulSMul D E]
    (hDodd : Odd (Nat.card D))
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, d • a = b)
    (hpD : p ∣ Nat.card D) :
    IsCyclic (pCore p D) ∧
      ∀ x : pCore p D, x ≠ 1 → ∀ e : E, (x : D) • e = e → e = 1 := by
  have hp_ne_two : p ≠ 2 := Odd.ne_two_of_dvd_nat hDodd hpD
  apply peterfalvi_appendixI_proposition_1_pGroup
    (p := p) (q := q) (P := pCore p D)
    (pCore_isPGroup (G := D) (p := p)) hp_ne_two
  intro a b ha hb
  obtain ⟨d, hd⟩ := htrans a b ha hb
  let φ : MulAut (pCore p D) := MulAut.conjNormal d
  have hmap :
      (MulAction.stabilizer (pCore p D) a).map φ.toMonoidHom =
        MulAction.stabilizer (pCore p D) b := by
    ext x
    rw [Subgroup.mem_map_equiv]
    change (((φ.symm x : pCore p D) : D) • a = a) ↔ (x : D) • b = b
    simp only [φ, MulAut.conjNormal_symm_apply]
    constructor
    · intro hx
      have h := congrArg (fun z : E => d • z) hx
      simpa [mul_smul, hd] using h
    · intro hx
      have hdinv : d⁻¹ • b = a := by
        rw [← hd]
        simp
      have h := congrArg (fun z : E => d⁻¹ • z) hx
      simpa [mul_smul, hd, hdinv] using h
  exact Nat.card_congr
    ((MulEquiv.subgroupMap φ (MulAction.stabilizer (pCore p D) a)).trans
      (MulEquiv.subgroupCongr hmap)).toEquiv


private theorem peterfalvi_appendixI_proposition_1_fitting_cyclic
    {q : ℕ} [Fact q.Prime]
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    [IsElementaryAbelian q E] [MulDistribMulAction D E] [FaithfulSMul D E]
    (hDodd : Odd (Nat.card D))
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, d • a = b) :
    IsCyclic (fittingSubgroup D) := by
  have hZ : IsZGroup (fittingSubgroup D) := by
    rw [isZGroup_iff]
    intro p hp P
    letI : Fact p.Prime := ⟨hp⟩
    rcases P.isPGroup'.card_eq_or_dvd with hPcard | hpP
    · apply isCyclic_of_card_dvd_prime (p := p)
      simp [hPcard]
    · have hpD : p ∣ Nat.card D :=
        hpP.trans ((Subgroup.card_subgroup_dvd_card (P : Subgroup (fittingSubgroup D))).trans
          (Subgroup.card_subgroup_dvd_card (fittingSubgroup D)))
      have hpcore_cyclic : IsCyclic (pCore p D) :=
        (peterfalvi_appendixI_proposition_1_pCore (q := q) hDodd htrans hpD).1
      letI : IsCyclic (pCore p D) := hpcore_cyclic
      have hle :
          (P : Subgroup (fittingSubgroup D)).map (fittingSubgroup D).subtype ≤
            pCore p D :=
        peterfalvi_appendixI_proposition_1_sylow_map_le_pCore
          (inferInstance : (fittingSubgroup D).Normal)
          (inferInstance : Group.IsNilpotent (fittingSubgroup D)) p P
      have hmap_cyclic :
          IsCyclic ((P : Subgroup (fittingSubgroup D)).map
            (fittingSubgroup D).subtype) :=
        Subgroup.isCyclic_of_le hle
      exact (MulEquiv.isCyclic
        (Subgroup.equivMapOfInjective
          (P : Subgroup (fittingSubgroup D))
          (fittingSubgroup D).subtype
          (fittingSubgroup D).subtype_injective)).mpr hmap_cyclic
  letI : IsZGroup (fittingSubgroup D) := hZ
  exact inferInstance

private theorem peterfalvi_appendixI_proposition_1_fitting_fixedPointFree
    {q : ℕ} [Fact q.Prime]
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    [IsElementaryAbelian q E] [MulDistribMulAction D E] [FaithfulSMul D E]
    (hDodd : Odd (Nat.card D))
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, d • a = b) :
    ∀ x : fittingSubgroup D, x ≠ 1 →
      ∀ e : E, (x : D) • e = e → e = 1 := by
  intro x hx e hxe
  have hxcard : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    intro hcard
    have hxorder : orderOf x = 1 := by
      simpa [Nat.card_zpowers] using hcard
    exact hx (orderOf_eq_one_iff.mp hxorder)
  obtain ⟨p, hp, hp_dvd_zx⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card (Subgroup.zpowers x)) hxcard
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers x) p hp_dvd_zx
  let yF : fittingSubgroup D := y
  have hyF_order : orderOf yF = p := by
    simpa [yF] using hy_order
  have hyfix : (yF : D) • e = e := by
    have hxmem : x ∈ MulAction.stabilizer (fittingSubgroup D) e := hxe
    have hzp_le :
        Subgroup.zpowers x ≤ MulAction.stabilizer (fittingSubgroup D) e :=
      Subgroup.zpowers_le.mpr hxmem
    exact hzp_le y.property
  have hyPgroup : IsPGroup p (Subgroup.zpowers yF) := by
    refine IsPGroup.of_card (p := p) (G := Subgroup.zpowers yF) (n := 1) ?_
    simp [Nat.card_zpowers, hyF_order]
  obtain ⟨P, hyP⟩ :=
    IsPGroup.exists_le_sylow
      (G := fittingSubgroup D) (p := p) hyPgroup
  have hPcore :
      (P : Subgroup (fittingSubgroup D)).map (fittingSubgroup D).subtype ≤
        pCore p D :=
    peterfalvi_appendixI_proposition_1_sylow_map_le_pCore
      (inferInstance : (fittingSubgroup D).Normal)
      (inferInstance : Group.IsNilpotent (fittingSubgroup D)) p P
  have hyF_mem_P : yF ∈ (P : Subgroup (fittingSubgroup D)) :=
    hyP (Subgroup.mem_zpowers yF)
  have hyD_mem_core : (yF : D) ∈ pCore p D :=
    hPcore ⟨yF, hyF_mem_P, rfl⟩
  let yp : pCore p D := ⟨(yF : D), hyD_mem_core⟩
  have hyp_ne : yp ≠ 1 := by
    intro hyp
    have hyD_one : (yF : D) = 1 :=
      congrArg (fun z : pCore p D => (z : D)) hyp
    have hyF_one : yF = 1 := Subtype.ext hyD_one
    rw [hyF_one, orderOf_one] at hyF_order
    exact hp.ne_one hyF_order.symm
  have hpD : p ∣ Nat.card D :=
    hp_dvd_zx.trans
      ((Subgroup.card_subgroup_dvd_card (Subgroup.zpowers x)).trans
        (Subgroup.card_subgroup_dvd_card (fittingSubgroup D)))
  exact (peterfalvi_appendixI_proposition_1_pCore (q := q) hDodd htrans hpD).2 yp hyp_ne e hyfix

private theorem peterfalvi_appendixI_proposition_1_conjNormal_ker_eq_centralizer
    {R : Type*} [Group R] {A : Subgroup R} [A.Normal] :
    (MulAut.conjNormal (H := A)).ker = Subgroup.centralizer (A : Set R) := by
  let phi : R →* MulAut A := MulAut.conjNormal (H := A)
  ext x
  rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
  constructor
  · intro hx a ha
    have hx_apply : phi x ⟨a, ha⟩ = ⟨a, ha⟩ := by
      change (MulAut.conjNormal (H := A) x) ⟨a, ha⟩ = ⟨a, ha⟩
      rw [hx]
      rfl
    have hconj : x * a * x⁻¹ = a := by
      simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using
        congrArg Subtype.val hx_apply
    have h := congrArg (fun t : R => t * x) hconj
    simpa [mul_assoc] using h.symm
  · intro hx
    ext a
    have hcomm : (a : R) * x = x * a := hx a a.2
    have hconj : x * (a : R) * x⁻¹ = a := by
      calc
        x * (a : R) * x⁻¹ = ((a : R) * x) * x⁻¹ := by rw [hcomm]
        _ = a := by simp [mul_assoc]
    simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj

private theorem peterfalvi_appendixI_proposition_1_fitting_quotient_commutative
    {D : Type*} [Group D] [Finite D]
    (hDodd : Odd (Nat.card D))
    (hFcyclic : IsCyclic (fittingSubgroup D)) :
    IsMulCommutative (D ⧸ fittingSubgroup D) := by
  letI : Group.IsSolvable D := odd_order_theorem D hDodd
  letI : IsCyclic (fittingSubgroup D) := hFcyclic
  haveI : IsMulCommutative (fittingSubgroup D) :=
    IsCyclic.isMulCommutative
  have hcent_eq :
      Subgroup.centralizer (fittingSubgroup D : Set D) = fittingSubgroup D := by
    apply le_antisymm
    · exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
        (G := D) (inferInstance : Group.IsSolvable D)
    · exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  let phi : D →* MulAut (fittingSubgroup D) :=
    MulAut.conjNormal (H := fittingSubgroup D)
  have hker : phi.ker = fittingSubgroup D := by
    simpa [phi, peterfalvi_appendixI_proposition_1_conjNormal_ker_eq_centralizer] using hcent_eq
  have hAutComm : IsMulCommutative (MulAut (fittingSubgroup D)) := by
    refine ⟨⟨fun alpha beta => ?_⟩⟩
    apply (IsCyclic.mulAutMulEquiv (fittingSubgroup D)).injective
    simpa only [map_mul] using
      (mul_comm
        ((IsCyclic.mulAutMulEquiv (fittingSubgroup D)) alpha)
        ((IsCyclic.mulAutMulEquiv (fittingSubgroup D)) beta))
  letI : IsMulCommutative (MulAut (fittingSubgroup D)) := hAutComm
  letI : CommGroup (MulAut (fittingSubgroup D)) := IsMulCommutative.instCommGroup
  let equivRange :
      D ⧸ fittingSubgroup D ≃* phi.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange phi)
  refine ⟨⟨fun x y => ?_⟩⟩
  apply equivRange.injective
  simpa only [map_mul] using (mul_comm (equivRange x) (equivRange y))

/-- Peterfalvi Appendix I, Proposition 1. If a finite odd-order group acts
faithfully and transitively on the nonzero elements of an elementary abelian
q-group, then its Fitting subgroup is cyclic and fixed-point-free, and the
quotient by the Fitting subgroup is abelian. -/
public theorem peterfalvi_appendixI_proposition_1
    {q : ℕ} [Fact q.Prime]
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    [IsElementaryAbelian q E] [MulDistribMulAction D E] [FaithfulSMul D E]
    (hDodd : Odd (Nat.card D))
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, d • a = b) :
    IsCyclic (fittingSubgroup D) ∧
      (∀ x : fittingSubgroup D, x ≠ 1 →
        ∀ e : E, (x : D) • e = e → e = 1) ∧
      IsMulCommutative (D ⧸ fittingSubgroup D) := by
  have hcyclic :=
    peterfalvi_appendixI_proposition_1_fitting_cyclic (q := q) hDodd htrans
  exact
    ⟨hcyclic,
      peterfalvi_appendixI_proposition_1_fitting_fixedPointFree
        (q := q) hDodd htrans,
      peterfalvi_appendixI_proposition_1_fitting_quotient_commutative
        hDodd hcyclic⟩

end PFAppendixI
end CFSG.BenderSuzuki









