module

public import CFSG.Mathlib.LinearAlgebra.RootSystem.OrbitFolding

public section

namespace CFSG.RootPairing

open TauCeti

open TauCeti

section Support

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : _root_.RootPairing ι ℤ X Y}
  (b : P.Base)

lemma coeff_eq_of_sum_eq {f g : ι → ℤ}
    (h : ∑ j ∈ b.support, f j • P.root j = ∑ j ∈ b.support, g j • P.root j) {j : ι}
    (hj : j ∈ b.support) : f j = g j :=
  (linearIndepOn_finset_iffₛ.mp b.linearIndepOn_root) f g h j hj

variable [Finite ι] [P.IsReduced] [Module.IsTorsionFree ℤ X]

omit [Finite ι] in
lemma mem_of_root_eq_sum_of_pairwise_orthogonal {S : Finset ι} (hS : S ⊆ b.support)
    (horth : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → P.pairing a a' = 0) {i : ι} {f : ι → ℤ}
    (hf0 : ∀ j, 0 ≤ f j) (hfS : ∀ j ∈ b.support, j ∉ S → f j = 0)
    (hi : P.root i = ∑ j ∈ b.support, f j • P.root j) : i ∈ S := by
  classical
  obtain ⟨a, ha, hfa⟩ : ∃ a ∈ S, 0 < f a := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    apply P.ne_zero i
    rw [hi]
    refine Finset.sum_eq_zero fun j hj => ?_
    by_cases hjS : j ∈ S
    · rw [le_antisymm (hcon j hjS) (hf0 j), zero_smul]
    · rw [hfS j hj hjS, zero_smul]
  have haB := hS ha
  have hpair : P.pairing i a = 2 * f a := by
    have : P.pairing i a = ∑ j ∈ b.support, f j * P.pairing j a := by
      have h := congrArg (fun x => P.toLinearMap x (P.coroot a)) hi
      simpa only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
        P.root_coroot_eq_pairing, smul_eq_mul] using h
    rw [this, Finset.sum_eq_single a]
    · rw [P.pairing_same, mul_comm]
    · intro j hj hja
      by_cases hjS : j ∈ S
      · rw [horth j hjS a ha hja, mul_zero]
      · rw [hfS j hj hjS, zero_mul]
    · exact fun h => absurd haB h
  have honly : ∀ a' ∈ b.support, a' ≠ a → f a' = 0 := by
    intro a' ha'B ha'a
    by_contra hne
    have hfa' : 0 < f a' := lt_of_le_of_ne (hf0 a') (Ne.symm hne)
    have hj : P.root (P.reflectionPerm a i) =
        ∑ k ∈ b.support, (Function.update f a (-f a)) k • P.root k := by
      rw [P.root_reflectionPerm, P.reflection_apply_root, hi, hpair]
      rw [← Finset.sum_erase_add _ _ haB, ← Finset.sum_erase_add _ _ haB]
      have hrest : ∑ k ∈ b.support.erase a, (Function.update f a (-f a)) k • P.root k =
          ∑ k ∈ b.support.erase a, f k • P.root k :=
        Finset.sum_congr rfl fun k hk => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      rw [hrest, Function.update_self, two_mul, add_smul, neg_smul]
      abel
    obtain ⟨h, -, hsign, hh⟩ := b.exists_root_eq_sum_int (P.reflectionPerm a i)
    have hha := coeff_eq_of_sum_eq b (hh.symm.trans hj) haB
    have hha' := coeff_eq_of_sum_eq b (hh.symm.trans hj) ha'B
    rw [Function.update_self] at hha
    rw [Function.update_of_ne ha'a] at hha'
    rcases hsign with hpos | hneg
    · have := hpos.le a
      simp only [Pi.zero_apply] at this
      omega
    · have := hneg.le a'
      simp only [Pi.zero_apply] at this
      omega
  have hia : P.root i = f a • P.root a := by
    rw [hi, Finset.sum_eq_single a (fun j hj hja => by rw [honly j hj hja, zero_smul])
      (fun h => absurd haB h)]
  have hdep : ¬ LinearIndependent ℤ ![P.root i, P.root a] := by
    intro hli
    have := hli.eq_zero_of_pair (s := 1) (t := -f a) (by rw [hia]; simp)
    exact one_ne_zero this.1
  rcases RootPairing.IsReduced.eq_or_eq_neg i a hdep with h | h
  · rw [P.root.injective h]; exact ha
  · exfalso
    rw [hia] at h
    have h2 : (f a + 1) • P.root a = 0 := by rw [add_smul, h, one_smul, neg_add_cancel]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · omega
    · exact P.ne_zero a h3

end Support

section Folded

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : _root_.RootPairing ι ℤ X Y}
  (σ : P.Aut)

@[expose] def fixedLattice : Submodule ℤ X where
  carrier := {x | σ • x = x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [smul_add, hx, hy]
  zero_mem' := smul_zero σ
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [smul_comm, hx]

lemma mem_fixedLattice {x : X} : x ∈ fixedLattice σ ↔ σ • x = x := Iff.rfl

lemma coroot'_indexEquiv_of_mem {x : X} (hx : x ∈ fixedLattice σ) (i : ι) :
    P.coroot' (σ.indexEquiv i) x = P.coroot' i x := by
  have h := RootPairing.coroot'_smul P σ (σ.indexEquiv i) x
  rwa [(mem_fixedLattice σ).mp hx, Equiv.symm_apply_apply] at h

variable [DecidableEq ι] (hσ3 : σ ^ 3 = 1)

include hσ3 in
lemma orbitFinset_eq_of_mem {i j : ι} (h : j ∈ orbitFinset σ i) :
    orbitFinset σ j = orbitFinset σ i := by
  have h3 := indexEquiv_cube σ hσ3
  rcases (mem_orbitFinset σ).mp h with rfl | rfl | rfl
  · rfl
  · ext k
    simp only [mem_orbitFinset, h3]
    tauto
  · ext k
    simp only [mem_orbitFinset, h3]
    tauto

@[expose] def orbitSetoid : Setoid ι where
  r i j := j ∈ orbitFinset σ i
  iseqv :=
    { refl := mem_orbitFinset_self σ
      symm := fun {i j} h => by
        rw [orbitFinset_eq_of_mem σ hσ3 h]
        exact mem_orbitFinset_self σ i
      trans := fun {i j k} hij hjk => by
        rw [← orbitFinset_eq_of_mem σ hσ3 hij]
        exact hjk }

abbrev FoldedIndex := Quotient (orbitSetoid σ hσ3)

instance decidableOrbitRel : DecidableRel (orbitSetoid σ hσ3).r :=
  fun i j => inferInstanceAs (Decidable (j ∈ orbitFinset σ i))

instance : DecidableEq (FoldedIndex σ hσ3) :=
  @Quotient.decidableEq _ _ (decidableOrbitRel σ hσ3)

@[expose] def orbitSum (i : ι) : X := ∑ γ ∈ orbitFinset σ i, P.root γ

include hσ3 in
lemma orbitSum_mem_fixedLattice (i : ι) : orbitSum σ i ∈ fixedLattice σ := by
  rw [mem_fixedLattice, orbitSum, Finset.smul_sum]
  simp_rw [← RootPairing.Equiv.root_indexEquiv_eq_smul]
  exact sum_orbitFinset_comp σ hσ3 i P.root

include hσ3 in
lemma orbitSum_eq_of_mem {i j : ι} (h : j ∈ orbitFinset σ i) : orbitSum σ j = orbitSum σ i := by
  rw [orbitSum, orbitSum, orbitFinset_eq_of_mem σ hσ3 h]

omit [DecidableEq ι] in
lemma coroot'_weylGroupToPerm_apply (w : P.weylGroup) (i : ι) (x : X) :
    P.coroot' (P.weylGroupToPerm w i) x = P.coroot' i (w⁻¹ • x) := by
  have h := P.coroot'_weylGroupToPerm_smul w i (w⁻¹ • x)
  rwa [smul_inv_smul] at h

lemma coroot'_eq_of_mem_orbitFinset {i j : ι} (hj : j ∈ orbitFinset σ i) {x : X}
    (hx : x ∈ fixedLattice σ) : P.coroot' j x = P.coroot' i x := by
  rcases (mem_orbitFinset σ).mp hj with rfl | rfl | rfl
  · rfl
  · exact coroot'_indexEquiv_of_mem σ hx i
  · rw [coroot'_indexEquiv_of_mem σ hx, coroot'_indexEquiv_of_mem σ hx]

omit [DecidableEq ι] in
lemma indexEquiv_reflectionPerm_self (i : ι) :
    σ.indexEquiv (P.reflectionPerm i i) = P.reflectionPerm (σ.indexEquiv i) (σ.indexEquiv i) := by
  apply P.root.injective
  rw [RootPairing.Equiv.root_indexEquiv_eq_smul, P.root_reflectionPerm, P.reflection_apply_self,
    P.root_reflectionPerm, P.reflection_apply_self, smul_neg,
    RootPairing.Equiv.root_indexEquiv_eq_smul]

lemma orbitFinset_reflectionPerm_self (i : ι) :
    orbitFinset σ (P.reflectionPerm i i) =
      (orbitFinset σ i).image fun j => P.reflectionPerm j j := by
  simp only [orbitFinset, Finset.image_insert, Finset.image_singleton,
    indexEquiv_reflectionPerm_self]

omit [DecidableEq ι] in
lemma reflectionPerm_self_injective :
    Function.Injective fun j : ι => P.reflectionPerm j j := by
  intro i j h
  apply P.root.injective
  have := congrArg P.root h
  simp only [P.root_reflectionPerm, P.reflection_apply_self, neg_inj] at this
  exact this

lemma orbitSum_reflectionPerm_self (i : ι) :
    orbitSum σ (P.reflectionPerm i i) = -orbitSum σ i := by
  rw [orbitSum, orbitSum, orbitFinset_reflectionPerm_self,
    Finset.sum_image fun _ _ _ _ h => reflectionPerm_self_injective h, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [P.root_reflectionPerm, P.reflection_apply_self]

omit [DecidableEq ι] in
lemma coroot'_reflectionPerm_self (i : ι) (x : X) :
    P.coroot' (P.reflectionPerm i i) x = -P.coroot' i x := by
  change P.toLinearMap x (P.coroot (P.reflectionPerm i i)) = -P.toLinearMap x (P.coroot i)
  rw [P.coroot_reflectionPerm, P.coreflection_apply_self, map_neg]

@[expose] def foldedRoot : FoldedIndex σ hσ3 → fixedLattice σ :=
  Quotient.lift (fun i => ⟨orbitSum σ i, orbitSum_mem_fixedLattice σ hσ3 i⟩)
    fun _ _ h => Subtype.ext (orbitSum_eq_of_mem σ hσ3 h).symm

@[expose] def foldedCoroot : FoldedIndex σ hσ3 → Module.Dual ℤ (fixedLattice σ) :=
  Quotient.lift (fun i => (P.coroot' i).comp (fixedLattice σ).subtype)
    fun i j h => by
      ext ⟨x, hx⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rcases (mem_orbitFinset σ).mp h with rfl | rfl | rfl
      · rfl
      · exact (coroot'_indexEquiv_of_mem σ hx i).symm
      · rw [coroot'_indexEquiv_of_mem σ hx, coroot'_indexEquiv_of_mem σ hx]

end Folded

section FoldedReflection

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : _root_.RootPairing ι ℤ X Y}
  [Finite ι] [Module.IsTorsionFree ℤ X] [DecidableEq ι] (b : P.Base) (σ : P.Aut)
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1)

include hσ hσ3 in
lemma pairing_eq_zero_of_mem_orbitFinset {i j : ι} (hj : j ∈ orbitFinset σ i) (hji : j ≠ i) :
    P.pairing j i = 0 ∧ P.pairing i j = 0 := by
  have hi : σ.indexEquiv i ≠ i := by
    intro h
    rcases (mem_orbitFinset σ).mp hj with rfl | rfl | rfl
    · exact hji rfl
    · exact hji h
    · exact hji (by rw [h, h])
  rcases (mem_orbitFinset σ).mp hj with rfl | rfl | rfl
  · exact absurd rfl hji
  · exact ⟨(isOrthogonal_indexEquiv b σ hσ hσ3 hi).2, (isOrthogonal_indexEquiv b σ hσ hσ3 hi).1⟩
  · exact ⟨(isOrthogonal_indexEquiv_sq b σ hσ hσ3 hi).2,
      (isOrthogonal_indexEquiv_sq b σ hσ hσ3 hi).1⟩

include hσ hσ3 in
lemma coroot'_orbitSum_self (i : ι) : P.coroot' i (orbitSum σ i) = 2 := by
  rw [orbitSum, map_sum, ← Finset.add_sum_erase _ _ (mem_orbitFinset_self σ i),
    P.root_coroot'_eq_pairing, P.pairing_same]
  rw [Finset.sum_eq_zero fun j hj => ?_, add_zero]
  rw [P.root_coroot'_eq_pairing]
  exact (pairing_eq_zero_of_mem_orbitFinset b σ hσ hσ3 (Finset.mem_of_mem_erase hj)
    (Finset.ne_of_mem_erase hj)).1

include hσ hσ3 in
lemma orbitReflection_smul_of_mem (i : ι) {x : X} (hx : x ∈ fixedLattice σ) :
    orbitReflection σ i • x = x - P.coroot' i x • orbitSum σ i := by
  have hc : ∀ j ∈ orbitFinset σ i, P.coroot' j x = P.coroot' i x := by
    intro j hj
    rcases (mem_orbitFinset σ).mp hj with rfl | rfl | rfl
    · rfl
    · exact coroot'_indexEquiv_of_mem σ hx i
    · rw [coroot'_indexEquiv_of_mem σ hx, coroot'_indexEquiv_of_mem σ hx]
  by_cases hi : σ.indexEquiv i = i
  · have hO : orbitFinset σ i = {i} := by simp [orbitFinset, hi]
    rw [orbitReflection_of_eq σ hi, RootPairing.weylGroup.ofIdx_smul,
      RootPairing.Equiv.reflection_smul, P.reflection_apply, orbitSum, hO, Finset.sum_singleton]
  have hi2 : σ.indexEquiv (σ.indexEquiv i) ≠ i := by
    intro h
    have := congrArg σ.indexEquiv h
    rw [indexEquiv_cube σ hσ3] at this
    exact hi this.symm
  have hi12 : σ.indexEquiv (σ.indexEquiv i) ≠ σ.indexEquiv i :=
    fun h => hi (σ.indexEquiv.injective h)
  have hm1 : σ.indexEquiv i ∈ orbitFinset σ i := (mem_orbitFinset σ).mpr (Or.inr (Or.inl rfl))
  have hm2 : σ.indexEquiv (σ.indexEquiv i) ∈ orbitFinset σ i :=
    (mem_orbitFinset σ).mpr (Or.inr (Or.inr rfl))
  have p1 := pairing_eq_zero_of_mem_orbitFinset b σ hσ hσ3 hm1 hi
  have p2 := pairing_eq_zero_of_mem_orbitFinset b σ hσ hσ3 hm2 hi2
  have hm2' : σ.indexEquiv (σ.indexEquiv i) ∈ orbitFinset σ (σ.indexEquiv i) := by
    rw [orbitFinset_eq_of_mem σ hσ3 hm1]; exact hm2
  have p12 := pairing_eq_zero_of_mem_orbitFinset b σ hσ hσ3 hm2' hi12
  have hsum : orbitSum σ i = P.root i + P.root (σ.indexEquiv i) +
      P.root (σ.indexEquiv (σ.indexEquiv i)) := by
    rw [orbitSum, orbitFinset, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton,
      add_assoc]
    · simpa using hi12.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hi h.symm, fun h => hi2 h.symm⟩
  rw [hsum, orbitReflection, mul_smul, mul_smul]
  simp only [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    P.reflection_apply, map_sub, map_smul, P.root_coroot'_eq_pairing, smul_eq_mul]
  rw [hc _ hm1, hc _ hm2, p1.1, p2.1, p12.1]
  simp only [mul_zero, sub_zero, smul_add]
  abel

omit [Finite ι] [Module.IsTorsionFree ℤ X] in
lemma orbitFinset_weylGroupToPerm {w : P.weylGroup} (hw : w ∈ fixedWeylGroup σ) (i : ι) :
    orbitFinset σ (P.weylGroupToPerm w i) = (orbitFinset σ i).image (P.weylGroupToPerm w) := by
  simp only [orbitFinset, Finset.image_insert, Finset.image_singleton,
    weylGroupToPerm_comm_of_mem_fixedWeylGroup σ hw]

omit [Finite ι] [Module.IsTorsionFree ℤ X] in
lemma smul_orbitSum {w : P.weylGroup} (hw : w ∈ fixedWeylGroup σ) (i : ι) :
    w • orbitSum σ i = orbitSum σ (P.weylGroupToPerm w i) := by
  rw [orbitSum, orbitSum, orbitFinset_weylGroupToPerm σ hw,
    Finset.sum_image fun _ _ _ _ h => (P.weylGroupToPerm w).injective h, Finset.smul_sum]
  exact Finset.sum_congr rfl fun γ _ => P.weylGroup_apply_root w γ

omit [Finite ι] [Module.IsTorsionFree ℤ X] [DecidableEq ι] in
lemma smul_mem_fixedLattice {w : P.weylGroup} (hw : w ∈ fixedWeylGroup σ) {x : X}
    (hx : x ∈ fixedLattice σ) : w • x ∈ fixedLattice σ := by
  rw [mem_fixedLattice] at hx ⊢
  have hcomm := (mem_fixedWeylGroup σ).mp hw
  calc σ • (w • x) = (σ * (w : P.Aut)) • x := (mul_smul _ _ _).symm
    _ = ((w : P.Aut) * σ) • x := by rw [hcomm]
    _ = w • x := by rw [mul_smul, hx]; rfl

include hσ hσ3 in
lemma pairwise_orthogonal_orbitFinset (k : ι) :
    ∀ a ∈ orbitFinset σ k, ∀ a' ∈ orbitFinset σ k, a ≠ a' → P.pairing a a' = 0 := by
  intro a ha a' ha' haa'
  have ha'k : a' ∈ orbitFinset σ a := by rw [orbitFinset_eq_of_mem σ hσ3 ha]; exact ha'
  exact (pairing_eq_zero_of_mem_orbitFinset b σ hσ hσ3 ha'k (Ne.symm haa')).2

end FoldedReflection

section Weights

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : _root_.RootPairing ι ℤ X Y)
  [DecidableEq ι] (b : P.Base) (hsc : P.corootSpan ℤ = ⊤)

omit [DecidableEq ι] in
include hsc in
lemma span_simpleCoroot_eq_top :
    Submodule.span ℤ (Set.range fun k : b.support => P.coroot k) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← hsc]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  have hsub : (AddSubmonoid.closure (P.coroot '' b.support) : Set Y) ⊆
      Submodule.span ℤ (Set.range fun k : b.support => P.coroot k) := by
    refine (AddSubmonoid.closure_le (S := (Submodule.span ℤ _).toAddSubmonoid)).mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  rcases b.coroot_mem_or_neg_mem j with h | h
  · exact hsub h
  · simpa using Submodule.neg_mem _ (hsub h)

noncomputable def simpleCorootBasis : Module.Basis b.support ℤ Y :=
  Module.Basis.mk b.linearIndepOn_coroot (span_simpleCoroot_eq_top P b hsc).ge

omit [DecidableEq ι] in
lemma simpleCorootBasis_apply (k : b.support) : simpleCorootBasis P b hsc k = P.coroot k :=
  Module.Basis.mk_apply _ _ _

noncomputable def fundamentalWeight (k : ι) : X :=
  if hk : k ∈ b.support then
    P.toLinearMap.toPerfPair.symm ((simpleCorootBasis P b hsc).coord ⟨k, hk⟩)
  else 0

lemma coroot'_fundamentalWeight {k k' : ι} (hk : k ∈ b.support) (hk' : k' ∈ b.support) :
    P.coroot' k' (fundamentalWeight P b hsc k) = if k' = k then 1 else 0 := by
  rw [fundamentalWeight, dif_pos hk]
  change P.toLinearMap (P.toLinearMap.toPerfPair.symm _) (P.coroot k') = _
  rw [← LinearMap.toPerfPair_apply, LinearEquiv.apply_symm_apply,
    ← simpleCorootBasis_apply P b hsc ⟨k', hk'⟩, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp only [Subtype.mk.injEq, eq_comm]

omit [DecidableEq ι] in
include hsc in
lemma eq_of_forall_coroot'_eq {x x' : X}
    (h : ∀ k ∈ b.support, P.coroot' k x = P.coroot' k x') : x = x' := by
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).1
  refine (simpleCorootBasis P b hsc).ext fun k => ?_
  rw [simpleCorootBasis_apply]
  exact h k k.2

end Weights

section OrbitSupport

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : _root_.RootPairing ι ℤ X Y}
  [DecidableEq ι] (b : P.Base) (σ : P.Aut)
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) (hsc : P.corootSpan ℤ = ⊤)

include hσ in
lemma orbitFinset_subset_support {k : ι} (hk : k ∈ b.support) : orbitFinset σ k ⊆ b.support := by
  intro m hm
  rcases (mem_orbitFinset σ).mp hm with rfl | rfl | rfl
  · exact hk
  · exact hσ _ hk
  · exact hσ _ (hσ _ hk)

include hσ in
lemma orbitSum_eq_sum_indicator {k : ι} (hk : k ∈ b.support) :
    orbitSum σ k = ∑ m ∈ b.support, (if m ∈ orbitFinset σ k then (1 : ℤ) else 0) • P.root m := by
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (orbitFinset_subset_support b σ hσ hk),
    orbitSum]

lemma orbitSum_eq_sum_of_coeff {l : ι} {f : ι → ι → ℤ}
    (hf : ∀ γ ∈ orbitFinset σ l, P.root γ = ∑ m ∈ b.support, f γ m • P.root m) :
    orbitSum σ l = ∑ m ∈ b.support, (∑ γ ∈ orbitFinset σ l, f γ m) • P.root m := by
  rw [orbitSum, Finset.sum_congr rfl hf, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => (Finset.sum_smul).symm

omit [DecidableEq ι] in
include hσ hσ3 in
lemma indexEquiv_symm_mem_support {k : ι} (hk : k ∈ b.support) :
    σ.indexEquiv.symm k ∈ b.support := by
  have : σ.indexEquiv.symm k = σ.indexEquiv (σ.indexEquiv k) := by
    rw [Equiv.symm_apply_eq, indexEquiv_cube σ hσ3]
  rw [this]
  exact hσ _ (hσ _ hk)

include hσ hσ3 in
lemma smul_fundamentalWeight (k : ι) :
    σ • fundamentalWeight P b hsc k = fundamentalWeight P b hsc (σ.indexEquiv k) := by
  by_cases hk : k ∈ b.support
  · apply eq_of_forall_coroot'_eq P b hsc
    intro k' hk'
    rw [RootPairing.coroot'_smul,
      coroot'_fundamentalWeight P b hsc hk (indexEquiv_symm_mem_support b σ hσ hσ3 hk'),
      coroot'_fundamentalWeight P b hsc (hσ k hk) hk']
    simp only [Equiv.symm_apply_eq]
  · have hk' : σ.indexEquiv k ∉ b.support := fun h => hk (by
      simpa using indexEquiv_symm_mem_support b σ hσ hσ3 h)
    rw [fundamentalWeight, dif_neg hk, fundamentalWeight, dif_neg hk', smul_zero]

@[expose] noncomputable def orbitWeight (k : ι) : X :=
  ∑ m ∈ orbitFinset σ k, fundamentalWeight P b hsc m

include hσ hσ3 in
lemma orbitWeight_mem_fixedLattice (k : ι) : orbitWeight b σ hsc k ∈ fixedLattice σ := by
  rw [mem_fixedLattice, orbitWeight, Finset.smul_sum,
    Finset.sum_congr rfl fun m _ => smul_fundamentalWeight b σ hσ hσ3 hsc m]
  exact sum_orbitFinset_comp σ hσ3 k (fundamentalWeight P b hsc)

include hσ in
lemma coroot'_orbitWeight {k m : ι} (hk : k ∈ b.support) (hm : m ∈ b.support) :
    P.coroot' m (orbitWeight b σ hsc k) = if m ∈ orbitFinset σ k then 1 else 0 := by
  rw [orbitWeight, map_sum, Finset.sum_congr rfl fun m' hm' =>
    coroot'_fundamentalWeight P b hsc (orbitFinset_subset_support b σ hσ hk hm') hm,
    Finset.sum_ite_eq]

include hσ3 in
lemma mem_orbitFinset_symm {k m : ι} (h : k ∈ orbitFinset σ m) : m ∈ orbitFinset σ k := by
  rw [orbitFinset_eq_of_mem σ hσ3 h]
  exact mem_orbitFinset_self σ m

end OrbitSupport

section FoldedInjective

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : _root_.RootPairing ι ℤ X Y}
  [Finite ι] [P.IsReduced] [Module.IsTorsionFree ℤ X] [DecidableEq ι] (b : P.Base) (σ : P.Aut)
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1)

omit [Finite ι] [P.IsReduced] [Module.IsTorsionFree ℤ X] [DecidableEq ι] in
lemma exists_coeff_nonneg_of_isPos {i : ι} (hi : b.IsPos i) :
    ∃ f : ι → ℤ, (∀ j, 0 ≤ f j) ∧ P.root i = ∑ j ∈ b.support, f j • P.root j := by
  obtain ⟨f, -, hsign, hf⟩ := b.exists_root_eq_sum_int i
  rcases hsign with hpos | hneg
  · exact ⟨f, fun j => hpos.le j, hf⟩
  · exfalso
    have h1 := (b.isPos_iff).mp hi
    rw [b.height_eq_sum hf] at h1
    have : ∑ j ∈ b.support, f j ≤ 0 := Finset.sum_nonpos fun j _ => hneg.le j
    omega

include hσ hσ3 in
lemma mem_orbitFinset_of_smul_orbitSum_eq {k l : ι} (hk : k ∈ b.support) (hl : b.IsPos l)
    {a d : ℤ} (ha : a ≠ 0) (h : a • orbitSum σ l = d • orbitSum σ k) : l ∈ orbitFinset σ k := by
  have hpos : ∀ γ ∈ orbitFinset σ l, b.IsPos γ := by
    intro γ hγ
    rcases (mem_orbitFinset σ).mp hγ with rfl | rfl | rfl
    · exact hl
    · exact (isPos_indexEquiv_iff b σ hσ _).mpr hl
    · exact (isPos_indexEquiv_iff b σ hσ _).mpr ((isPos_indexEquiv_iff b σ hσ _).mpr hl)
  choose! f hf0 hf using fun γ (hγ : γ ∈ orbitFinset σ l) =>
    exists_coeff_nonneg_of_isPos b (hpos γ hγ)
  have h' : ∑ m ∈ b.support, (a * ∑ γ ∈ orbitFinset σ l, f γ m) • P.root m =
      ∑ m ∈ b.support, (d * if m ∈ orbitFinset σ k then 1 else 0) • P.root m := by
    simp only [mul_smul, ← Finset.smul_sum]
    rw [← orbitSum_eq_sum_of_coeff b σ hf, ← orbitSum_eq_sum_indicator b σ hσ hk]
    exact h
  refine mem_of_root_eq_sum_of_pairwise_orthogonal b (orbitFinset_subset_support b σ hσ hk)
    (pairwise_orthogonal_orbitFinset b σ hσ hσ3 k) (hf0 l (mem_orbitFinset_self σ l))
    (fun m hm hmk => ?_) (hf l (mem_orbitFinset_self σ l))
  have h0 := coeff_eq_of_sum_eq b h' hm
  rw [if_neg hmk, mul_zero] at h0
  exact (Finset.sum_eq_zero_iff_of_nonneg fun γ hγ => hf0 γ hγ m).mp
    ((mul_eq_zero.mp h0).resolve_left ha) l (mem_orbitFinset_self σ l)

include hσ hσ3 in
lemma mem_orbitFinset_or_of_smul_orbitSum_eq {k l : ι} (hk : k ∈ b.support) {a d : ℤ}
    (ha : a ≠ 0) (h : a • orbitSum σ l = d • orbitSum σ k) :
    l ∈ orbitFinset σ k ∨ P.reflectionPerm l l ∈ orbitFinset σ k := by
  let _ := P.indexNeg
  rcases RootPairing.Base.IsPos.or_neg b l with hl | hl
  · exact Or.inl (mem_orbitFinset_of_smul_orbitSum_eq b σ hσ hσ3 hk hl ha h)
  · refine Or.inr (mem_orbitFinset_of_smul_orbitSum_eq b σ hσ hσ3 hk hl ha (d := -d) ?_)
    rw [orbitSum_reflectionPerm_self, smul_neg, h, neg_smul]

omit [P.IsReduced] in
include hσ hσ3 in
lemma orbitSum_ne_zero (i : ι) : orbitSum σ i ≠ 0 := by
  intro h
  have := coroot'_orbitSum_self b σ hσ hσ3 i
  rw [h, map_zero] at this
  exact absurd this (by norm_num)

include hσ hσ3 in
theorem orbitSum_eq_or_eq_neg_of_smul_eq {l l' : ι} {a d : ℤ} (ha : a ≠ 0)
    (h : a • orbitSum σ l = d • orbitSum σ l') :
    orbitSum σ l = orbitSum σ l' ∨ orbitSum σ l = -orbitSum σ l' := by
  obtain ⟨u, hu, hk⟩ := exists_mem_fixedWeylGroup_mem_support b σ hσ hσ3 l'
  have h' : a • orbitSum σ (P.weylGroupToPerm u l) = d • orbitSum σ (P.weylGroupToPerm u l') := by
    rw [← smul_orbitSum σ hu, ← smul_orbitSum σ hu, ← smul_comm u a, h, smul_comm u d]
  have hneg : ∀ j, orbitSum σ (P.weylGroupToPerm u j) = u • orbitSum σ j := fun j =>
    (smul_orbitSum σ hu j).symm
  rcases mem_orbitFinset_or_of_smul_orbitSum_eq b σ hσ hσ3 hk ha h' with hm | hm
  · left
    have := orbitSum_eq_of_mem σ hσ3 hm
    rw [hneg, hneg] at this
    exact smul_left_cancel u this
  · right
    have := orbitSum_eq_of_mem σ hσ3 hm
    rw [orbitSum_reflectionPerm_self, hneg, hneg, ← smul_neg] at this
    rw [← neg_neg (orbitSum σ l), smul_left_cancel u this]

include hσ hσ3 in
theorem mem_orbitFinset_of_orbitSum_eq {l l' : ι} (h : orbitSum σ l = orbitSum σ l') :
    l ∈ orbitFinset σ l' := by
  obtain ⟨u, hu, hk⟩ := exists_mem_fixedWeylGroup_mem_support b σ hσ hσ3 l'
  have h' : (1 : ℤ) • orbitSum σ (P.weylGroupToPerm u l) =
      (1 : ℤ) • orbitSum σ (P.weylGroupToPerm u l') := by
    rw [← smul_orbitSum σ hu, ← smul_orbitSum σ hu, h]
  have himage : ∀ j, P.weylGroupToPerm u j ∈ orbitFinset σ (P.weylGroupToPerm u l') →
      j ∈ orbitFinset σ l' := by
    intro j hj
    rw [orbitFinset_weylGroupToPerm σ hu, Finset.mem_image] at hj
    obtain ⟨j', hj', hjj'⟩ := hj
    rwa [← (P.weylGroupToPerm u).injective hjj']
  rcases mem_orbitFinset_or_of_smul_orbitSum_eq b σ hσ hσ3 hk one_ne_zero h' with hm | hm
  · exact himage l hm
  · exfalso
    have h1 := orbitSum_eq_of_mem σ hσ3 hm
    rw [orbitSum_reflectionPerm_self, one_smul, one_smul] at *
    rw [← h'] at h1
    have h2 : (2 : ℤ) • orbitSum σ (P.weylGroupToPerm u l) = 0 := by
      rw [two_smul]; nth_rewrite 1 [← neg_neg (orbitSum σ _), h1]; exact neg_add_cancel _
    exact orbitSum_ne_zero b σ hσ hσ3 _ ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

end FoldedInjective

section FoldedCoroot

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : _root_.RootPairing ι ℤ X Y}
  [Finite ι] [DecidableEq ι] (b : P.Base) (σ : P.Aut)
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) (hsc : P.corootSpan ℤ = ⊤)

variable [Module.IsTorsionFree ℤ X] [P.flip.IsReduced] [Module.IsTorsionFree ℤ Y]

include hσ hσ3 hsc in
lemma mem_orbitFinset_of_smul_coroot'_eq {k l : ι} (hk : k ∈ b.support) {c : ι → ℤ}
    (hc0 : ∀ m, 0 ≤ c m) (hc : P.coroot l = ∑ m ∈ b.support, c m • P.coroot m) {a d : ℤ}
    (ha : a ≠ 0) (h : ∀ x ∈ fixedLattice σ, a * P.coroot' l x = d * P.coroot' k x) :
    l ∈ orbitFinset σ k := by
  have hval : ∀ x : X, P.coroot' l x = ∑ m ∈ b.support, c m * P.coroot' m x := by
    intro x
    change P.toLinearMap x (P.coroot l) = _
    rw [hc, map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_zsmul, smul_eq_mul]; rfl
  have horb : ∀ k'' ∈ b.support, a * ∑ m ∈ orbitFinset σ k'', c m =
      d * if k ∈ orbitFinset σ k'' then 1 else 0 := by
    intro k'' hk''
    have h1 := h _ (orbitWeight_mem_fixedLattice b σ hσ hσ3 hsc k'')
    rw [hval, coroot'_orbitWeight b σ hσ hsc hk'' hk] at h1
    rw [← h1]
    congr 1
    calc ∑ m ∈ orbitFinset σ k'', c m
        = ∑ m ∈ b.support, if m ∈ orbitFinset σ k'' then c m else 0 := by
          rw [Finset.sum_ite_mem,
            Finset.inter_eq_right.mpr (orbitFinset_subset_support b σ hσ hk'')]
      _ = ∑ m ∈ b.support, c m * P.coroot' m (orbitWeight b σ hsc k'') :=
          Finset.sum_congr rfl fun m hm => by
            rw [coroot'_orbitWeight b σ hσ hsc hk'' hm]
            split_ifs <;> simp
  refine mem_of_root_eq_sum_of_pairwise_orthogonal (P := P.flip) b.flip
    (by rw [RootPairing.Base.flip_support]; exact orbitFinset_subset_support b σ hσ hk)
    (fun a ha a' ha' haa' => by
      rw [RootPairing.pairing_flip]
      exact pairwise_orthogonal_orbitFinset b σ hσ hσ3 k a' ha' a ha (Ne.symm haa'))
    hc0 (fun m hm hmk => ?_) (by rw [RootPairing.Base.flip_support]; exact hc)
  rw [RootPairing.Base.flip_support] at hm
  have h0 := horb m hm
  rw [if_neg fun hkm => hmk (mem_orbitFinset_symm σ hσ3 hkm), mul_zero] at h0
  exact (Finset.sum_eq_zero_iff_of_nonneg fun m' _ => hc0 m').mp
    ((mul_eq_zero.mp h0).resolve_left ha) m (mem_orbitFinset_self σ m)

include hσ hσ3 hsc in
lemma mem_orbitFinset_or_of_smul_coroot'_eq {k l : ι} (hk : k ∈ b.support) {a d : ℤ}
    (ha : a ≠ 0) (h : ∀ x ∈ fixedLattice σ, a * P.coroot' l x = d * P.coroot' k x) :
    l ∈ orbitFinset σ k ∨ P.reflectionPerm l l ∈ orbitFinset σ k := by
  obtain ⟨c, -, hsign, hc⟩ := b.flip.exists_root_eq_sum_int l
  have hc' : P.coroot l = ∑ m ∈ b.support, c m • P.coroot m := by
    simpa [RootPairing.Base.flip_support] using hc
  rcases hsign with hpos | hneg
  · exact Or.inl (mem_orbitFinset_of_smul_coroot'_eq b σ hσ hσ3 hsc hk (fun m => hpos.le m) hc'
      ha h)
  · refine Or.inr (mem_orbitFinset_of_smul_coroot'_eq b σ hσ hσ3 hsc hk (c := -c)
      (fun m => neg_nonneg.mpr (hneg.le m)) ?_ ha (d := -d) fun x hx => ?_)
    · rw [P.coroot_reflectionPerm, P.coreflection_apply_self, hc', ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun m _ => by rw [Pi.neg_apply, neg_smul]
    · rw [coroot'_reflectionPerm_self, mul_neg, h x hx, neg_mul]

variable [P.IsReduced]

include hσ hσ3 hsc in
theorem coroot'_eq_or_eq_neg_of_smul_eq {l l' : ι} {a d : ℤ} (ha : a ≠ 0)
    (h : ∀ x ∈ fixedLattice σ, a * P.coroot' l x = d * P.coroot' l' x) :
    (∀ x ∈ fixedLattice σ, P.coroot' l x = P.coroot' l' x) ∨
      ∀ x ∈ fixedLattice σ, P.coroot' l x = -P.coroot' l' x := by
  obtain ⟨u, hu, hk⟩ := exists_mem_fixedWeylGroup_mem_support b σ hσ hσ3 l'
  have hu' : u⁻¹ ∈ fixedWeylGroup σ := (fixedWeylGroup σ).inv_mem hu
  have h' : ∀ x ∈ fixedLattice σ, a * P.coroot' (P.weylGroupToPerm u l) x =
      d * P.coroot' (P.weylGroupToPerm u l') x := by
    intro x hx
    rw [coroot'_weylGroupToPerm_apply, coroot'_weylGroupToPerm_apply]
    exact h _ (smul_mem_fixedLattice σ hu' hx)
  have hback : ∀ j, ∀ x, P.coroot' j x = P.coroot' (P.weylGroupToPerm u j) (u • x) := fun j x =>
    (P.coroot'_weylGroupToPerm_smul u j x).symm
  rcases mem_orbitFinset_or_of_smul_coroot'_eq b σ hσ hσ3 hsc hk ha h' with hm | hm
  · left
    intro x hx
    rw [hback l, hback l']
    exact coroot'_eq_of_mem_orbitFinset σ hm (smul_mem_fixedLattice σ hu hx)
  · right
    intro x hx
    have := coroot'_eq_of_mem_orbitFinset σ hm (smul_mem_fixedLattice σ hu hx)
    rw [hback l, hback l', ← this, coroot'_reflectionPerm_self, neg_neg]

include hσ hσ3 hsc in
theorem mem_orbitFinset_of_coroot'_eq {l l' : ι}
    (h : ∀ x ∈ fixedLattice σ, P.coroot' l x = P.coroot' l' x) : l ∈ orbitFinset σ l' := by
  obtain ⟨u, hu, hk⟩ := exists_mem_fixedWeylGroup_mem_support b σ hσ hσ3 l'
  have hu' : u⁻¹ ∈ fixedWeylGroup σ := (fixedWeylGroup σ).inv_mem hu
  have h' : ∀ x ∈ fixedLattice σ, (1 : ℤ) * P.coroot' (P.weylGroupToPerm u l) x =
      1 * P.coroot' (P.weylGroupToPerm u l') x := by
    intro x hx
    rw [one_mul, one_mul, coroot'_weylGroupToPerm_apply, coroot'_weylGroupToPerm_apply]
    exact h _ (smul_mem_fixedLattice σ hu' hx)
  have himage : ∀ j, P.weylGroupToPerm u j ∈ orbitFinset σ (P.weylGroupToPerm u l') →
      j ∈ orbitFinset σ l' := by
    intro j hj
    rw [orbitFinset_weylGroupToPerm σ hu, Finset.mem_image] at hj
    obtain ⟨j', hj', hjj'⟩ := hj
    rwa [← (P.weylGroupToPerm u).injective hjj']
  rcases mem_orbitFinset_or_of_smul_coroot'_eq b σ hσ hσ3 hsc hk one_ne_zero h' with hm | hm
  · exact himage l hm
  · exfalso
    set k := P.weylGroupToPerm u l'
    have hx := orbitSum_mem_fixedLattice σ hσ3 k
    have h1 := coroot'_eq_of_mem_orbitFinset σ hm hx
    have h2 := h' _ hx
    rw [coroot'_reflectionPerm_self, coroot'_orbitSum_self b σ hσ hσ3 k] at h1
    rw [one_mul, one_mul, coroot'_orbitSum_self b σ hσ hσ3 k] at h2
    omega

end FoldedCoroot

section FoldedPairing

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : _root_.RootPairing ι ℤ X Y}
  [Finite ι] [DecidableEq ι] [P.IsReduced] [P.flip.IsReduced] [Module.IsTorsionFree ℤ X]
  [Module.IsTorsionFree ℤ Y] (b : P.Base) (σ : P.Aut)
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) (hsc : P.corootSpan ℤ = ⊤)

omit [P.flip.IsReduced] [Module.IsTorsionFree ℤ Y] in
include hσ in
lemma foldedRoot_injective : Function.Injective (foldedRoot σ hσ3) := by
  rintro ⟨l⟩ ⟨l'⟩ h
  have h' : orbitSum σ l = orbitSum σ l' := congrArg Subtype.val h
  exact (Quotient.sound (mem_orbitFinset_of_orbitSum_eq b σ hσ hσ3 h')).symm

include hσ hsc in
lemma foldedCoroot_injective : Function.Injective (foldedCoroot σ hσ3) := by
  rintro ⟨l⟩ ⟨l'⟩ h
  have h' : ∀ x ∈ fixedLattice σ, P.coroot' l x = P.coroot' l' x := fun x hx =>
    LinearMap.congr_fun h ⟨x, hx⟩
  exact (Quotient.sound (mem_orbitFinset_of_coroot'_eq b σ hσ hσ3 hsc h')).symm

omit [P.IsReduced] [P.flip.IsReduced] [Module.IsTorsionFree ℤ Y] in
include hσ in
lemma foldedCoroot_foldedRoot (O : FoldedIndex σ hσ3) :
    foldedCoroot σ hσ3 O (foldedRoot σ hσ3 O) = 2 := by
  induction O using Quotient.inductionOn with
  | h i => exact coroot'_orbitSum_self b σ hσ hσ3 i

variable [Module.Finite ℤ X]

@[expose] noncomputable def foldedPairing :
    _root_.RootPairing (FoldedIndex σ hσ3) ℤ (fixedLattice σ) (Module.Dual ℤ (fixedLattice σ)) :=
  _root_.RootPairing.mk' (Module.Dual.eval ℤ (fixedLattice σ))
    ⟨foldedRoot σ hσ3, foldedRoot_injective b σ hσ hσ3⟩
    ⟨foldedCoroot σ hσ3, foldedCoroot_injective b σ hσ hσ3 hsc⟩
    (fun O => by
      rw [Module.Dual.eval_apply]
      exact foldedCoroot_foldedRoot b σ hσ hσ3 O)
    (fun O => by
      rintro _ ⟨O', rfl⟩
      induction O using Quotient.inductionOn with | h l => ?_
      induction O' using Quotient.inductionOn with | h l' => ?_
      refine ⟨⟦P.weylGroupToPerm (orbitReflection σ l) l'⟧, Subtype.ext ?_⟩
      rw [Module.preReflection_apply, LinearMap.flip_apply, Module.Dual.eval_apply,
        Submodule.coe_sub, Submodule.coe_smul]
      change orbitSum σ (P.weylGroupToPerm (orbitReflection σ l) l') =
        orbitSum σ l' - P.coroot' l (orbitSum σ l') • orbitSum σ l
      rw [← smul_orbitSum σ (orbitReflection_mem_fixedWeylGroup b σ hσ hσ3 l),
        orbitReflection_smul_of_mem b σ hσ hσ3 l (orbitSum_mem_fixedLattice σ hσ3 l')])
    (fun O => by
      rintro _ ⟨O', rfl⟩
      induction O using Quotient.inductionOn with | h l => ?_
      induction O' using Quotient.inductionOn with | h l' => ?_
      refine ⟨⟦(P.weylGroupToPerm (orbitReflection σ l)).symm l'⟧, LinearMap.ext fun x => ?_⟩
      rw [Module.preReflection_apply, Module.Dual.eval_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul]
      change P.coroot' ((P.weylGroupToPerm (orbitReflection σ l)).symm l') x =
        P.coroot' l' x - P.coroot' l' (orbitSum σ l) * P.coroot' l x
      have hw := P.coroot'_weylGroupToPerm_smul (orbitReflection σ l)
        ((P.weylGroupToPerm (orbitReflection σ l)).symm l') x
      rw [Equiv.apply_symm_apply] at hw
      rw [← hw, orbitReflection_smul_of_mem b σ hσ hσ3 l x.2, map_sub, map_zsmul,
        smul_eq_mul, mul_comm])

instance : (foldedPairing b σ hσ hσ3 hsc).IsReduced := by
  refine ⟨fun O O' h => ?_⟩
  induction O using Quotient.inductionOn with | h l => ?_
  induction O' using Quotient.inductionOn with | h l' => ?_
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, hst, hne⟩ := h
  have hst' : s • orbitSum σ l + t • orbitSum σ l' = 0 := congrArg Subtype.val hst
  have hs : s ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hst'
    exact hne rfl ((smul_eq_zero.mp hst').resolve_right (orbitSum_ne_zero b σ hσ hσ3 l'))
  have h' : s • orbitSum σ l = (-t) • orbitSum σ l' := by
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact hst'
  rcases orbitSum_eq_or_eq_neg_of_smul_eq b σ hσ hσ3 hs h' with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

instance : (foldedPairing b σ hσ hσ3 hsc).flip.IsReduced := by
  refine ⟨fun O O' h => ?_⟩
  induction O using Quotient.inductionOn with | h l => ?_
  induction O' using Quotient.inductionOn with | h l' => ?_
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, hst, hne⟩ := h
  have hst' : ∀ x ∈ fixedLattice σ, s * P.coroot' l x + t * P.coroot' l' x = 0 := fun x hx =>
    LinearMap.congr_fun hst ⟨x, hx⟩
  have hs : s ≠ 0 := by
    rintro rfl
    have := hst' _ (orbitSum_mem_fixedLattice σ hσ3 l')
    rw [coroot'_orbitSum_self b σ hσ hσ3 l', zero_mul, zero_add] at this
    exact hne rfl (by omega)
  have h' : ∀ x ∈ fixedLattice σ, s * P.coroot' l x = (-t) * P.coroot' l' x := fun x hx => by
    have := hst' x hx
    linarith
  rcases coroot'_eq_or_eq_neg_of_smul_eq b σ hσ hσ3 hsc hs h' with h1 | h1
  · exact Or.inl (LinearMap.ext fun x => h1 x x.2)
  · exact Or.inr (LinearMap.ext fun x => h1 x x.2)

end FoldedPairing

end CFSG.RootPairing
