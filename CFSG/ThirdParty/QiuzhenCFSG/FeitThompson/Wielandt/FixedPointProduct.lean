module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.MatrixTrace

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed-point product infrastructure for Wielandt

This file contains the checked fixed-point product, Frobenius-action,
elementary-abelian finrank/cardinality, and trace-congruence infrastructure
used by the Wielandt fixed-point theorem. The homocyclic source-existence
ladder remains in `FeitThompson.Wielandt`.
-/

noncomputable section

open scoped IsMulCommutative

namespace CFSG.Wielandt

universe u

/-- Transport the Frobenius join package to the concrete overgroup supplied by a
complement relation. -/
public theorem section12FrobeniusJoinWithKernel_subgroupOf_complementIn
    {G : Type u} [Group G] [Finite G]
    (UE U E : Subgroup G)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E) :
    IsFrobeniusGroupWithKernelComplement (U.subgroupOf UE) (E.subgroupOf UE) := by
  have hUEeq : UE = U ⊔ E := hcomp.2.2.1
  subst UE
  simpa [section12FrobeniusJoinWithKernel] using hfrob

/-- If a subgroup action agrees with the restriction of a larger subgroup action,
the two fixed-point subgroups agree. -/
public theorem fixedPointSubgroup_eq_subgroupOf_of_compatible
    {G M : Type u} [Group G] [Group M]
    (A B : Subgroup G)
    [MulDistribMulAction A M] [MulDistribMulAction B M]
    (hBA : B ≤ A)
    (hcompat : ∀ (b : B) (m : M), b • m = (⟨(b : G), hBA b.2⟩ : A) • m) :
    fixedPointSubgroup (↥B) M =
      letI : MulDistribMulAction (↥(B.subgroupOf A)) M :=
        MulDistribMulAction.compHom M (B.subgroupOf A).subtype
      fixedPointSubgroup (↥(B.subgroupOf A)) M := by
  ext m
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hm b
    let bB : B := ⟨(b : G), b.2⟩
    have hb := hm bB
    have hb_eq : (⟨(b : A), by
        show ((b : A) : G) ∈ B
        exact b.2⟩ : B.subgroupOf A) = b := by
      ext
      rfl
    rw [← hb_eq]
    simpa [bB, MulAction.compHom_smul_def, hcompat bB m] using hb
  · intro hm b
    have hb :
        (⟨⟨(b : G), hBA b.2⟩, by
          show ((⟨(b : G), hBA b.2⟩ : A) : G) ∈ B
          exact b.2⟩ : B.subgroupOf A) • m = m :=
      hm ⟨⟨(b : G), hBA b.2⟩, by
        show ((⟨(b : G), hBA b.2⟩ : A) : G) ∈ B
        exact b.2⟩
    simpa [MulAction.compHom_smul_def, hcompat b m] using hb

/-- Invariance descends from an actor to a compatible subgroup actor. -/
public theorem isInvariant_of_compatible_le_actor
    {G M : Type u} [Group G] [Group M]
    (A B : Subgroup G)
    [MulDistribMulAction A M] [MulDistribMulAction B M]
    (hBA : B ≤ A)
    (hcompat : ∀ (b : B) (m : M), b • m = (⟨(b : G), hBA b.2⟩ : A) • m)
    {N : Subgroup M}
    (hAinv : IsInvariant A M N) :
    IsInvariant B M N := by
  refine ⟨?_⟩
  intro b m
  have hA :=
    IsInvariant.invariant (A := A) (G := M) (H := N)
      (⟨(b : G), hBA b.2⟩ : A) m
  constructor
  · intro hm
    simpa [hcompat b m] using hA.1 hm
  · intro hm
    exact hA.2 (by simpa [hcompat b m] using hm)

/-- If a subgroup has only trivial fixed points, then the full actor has only
trivial fixed points. -/
public theorem fixedPointSubgroup_top_eq_bot_of_subgroup_fixed_bot
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    (K : Subgroup A)
    (hKbot :
      letI : MulDistribMulAction (↥K) M := MulDistribMulAction.compHom M K.subtype
      fixedPointSubgroup (↥K) M = ⊥) :
    fixedPointSubgroup A M = ⊥ := by
  classical
  apply le_antisymm
  · intro m hm
    have hmK :
        m ∈
          (let : MulDistribMulAction (↥K) M := MulDistribMulAction.compHom M K.subtype
          fixedPointSubgroup (↥K) M) := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro k
      have hmA := (FixedPoints.mem_subgroup (M := A) (a := m)).1 hm (k : A)
      simpa [MulAction.compHom_smul_def] using hmA
    have hm_bot : m ∈ (⊥ : Subgroup M) := by
      simpa [hKbot] using hmK
    exact hm_bot
  · exact bot_le

/-- Conjugating an actor subgroup transports fixed-point subgroups. -/
public noncomputable def fixedPointSubgroup_conjByEquiv
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    (R : Subgroup A) (a : A) :
    (letI : MulDistribMulAction (↥R) M := MulDistribMulAction.compHom M R.subtype;
      fixedPointSubgroup (↥R) M) ≃
      (letI : MulDistribMulAction (↥(R.conjBy a)) M :=
        MulDistribMulAction.compHom M (R.conjBy a).subtype;
      fixedPointSubgroup (↥(R.conjBy a)) M) := by
  classical
  let : MulDistribMulAction (↥R) M := MulDistribMulAction.compHom M R.subtype
  let : MulDistribMulAction (↥(R.conjBy a)) M :=
    MulDistribMulAction.compHom M (R.conjBy a).subtype
  refine
    { toFun := fun x => ⟨a • x.1, ?_⟩
      invFun := fun y => ⟨a⁻¹ • y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro r
    have hr := r.2
    change (r : A) ∈ R.map (MulAut.conj a).toMonoidHom at hr
    rw [Subgroup.mem_map] at hr
    rcases hr with ⟨r0, hr0R, hr_eq⟩
    have hx := (FixedPoints.mem_subgroup (M := R) (a := x.1)).1 x.2 ⟨r0, hr0R⟩
    have hxA : r0 • x.1 = x.1 := by
      simpa [MulAction.compHom_smul_def] using hx
    have hrA : (r : A) = a * r0 * a⁻¹ := by
      simpa [MulAut.conj_apply] using hr_eq.symm
    calc
      r • (a • x.1) = (r : A) • (a • x.1) := by rfl
      _ = ((r : A) * a) • x.1 := by rw [mul_smul]
      _ = ((a * r0 * a⁻¹) * a) • x.1 := by rw [hrA]
      _ = (a * r0) • x.1 := by
            have hmul : (a * r0 * a⁻¹) * a = a * r0 := by group
            rw [hmul]
      _ = a • (r0 • x.1) := by rw [mul_smul]
      _ = a • x.1 := by rw [hxA]
  · rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro r
    let rConj : R.conjBy a :=
      ⟨a * (r : A) * a⁻¹, by
        change a * (r : A) * a⁻¹ ∈ R.map (MulAut.conj a).toMonoidHom
        rw [Subgroup.mem_map]
        exact ⟨(r : A), r.2, rfl⟩⟩
    have hy := (FixedPoints.mem_subgroup (M := R.conjBy a) (a := y.1)).1 y.2 rConj
    have hyA : (a * (r : A) * a⁻¹) • y.1 = y.1 := by
      simpa [rConj, MulAction.compHom_smul_def] using hy
    calc
      r • (a⁻¹ • y.1) = (r : A) • (a⁻¹ • y.1) := by rfl
      _ = ((r : A) * a⁻¹) • y.1 := by rw [mul_smul]
      _ = (a⁻¹ * (a * (r : A) * a⁻¹)) • y.1 := by
            have hmul : (r : A) * a⁻¹ = a⁻¹ * (a * (r : A) * a⁻¹) := by group
            rw [hmul]
      _ = a⁻¹ • ((a * (r : A) * a⁻¹) • y.1) := by rw [mul_smul]
      _ = a⁻¹ • y.1 := by rw [hyA]
  · intro x
    ext
    simp
  · intro y
    ext
    simp

public abbrev FrobeniusProductIndex {A : Type u} [Group A] (K : Subgroup A) :=
  Fin 3 ⊕ K

@[expose, implicit_reducible] public def frobeniusProductSubgroup {A : Type u} [Group A]
    (K R : Subgroup A) : FrobeniusProductIndex K → Subgroup A
  | Sum.inl 0 => ⊤
  | Sum.inl 1 => ⊥
  | Sum.inl 2 => K
  | Sum.inr k => R.conjBy (k : A)

@[expose] public def frobeniusProductLeftCoeff {A : Type u} [Group A]
    (K : Subgroup A) : FrobeniusProductIndex K → ℕ
  | Sum.inl 0 => 1
  | Sum.inl 1 => Nat.card K
  | Sum.inl 2 => 0
  | Sum.inr _ => 0

@[expose] public def frobeniusProductRightCoeff {A : Type u} [Group A]
    (K : Subgroup A) : FrobeniusProductIndex K → ℕ
  | Sum.inl 0 => 0
  | Sum.inl 1 => 0
  | Sum.inl 2 => 1
  | Sum.inr _ => 1

public theorem frobenius_mem_conjBy_of_mem_kernel_eq_one
    {A : Type u} [Group A]
    (K R : Subgroup A)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    {a : A} (haK : a ∈ K) {k : K}
    (haRk : a ∈ R.conjBy (k : A)) :
    a = 1 := by
  rcases Subgroup.mem_map.mp haRk with ⟨r, hrR, hr_eq⟩
  have hrK : r ∈ K := by
    have hconj : (k : A)⁻¹ * a * (k : A) ∈ K := by
      simpa using hfrob.normal.conj_mem a haK (k : A)⁻¹
    have hcalc : (k : A)⁻¹ * a * (k : A) = r := by
      have hrA : (k : A) * r * (k : A)⁻¹ = a := by
        simpa [MulAut.conj_apply] using hr_eq
      have := congrArg (fun t : A => (k : A)⁻¹ * t * (k : A)) hrA
      simpa [mul_assoc] using this.symm
    simpa [hcalc] using hconj
  have hr_bot : r ∈ (⊥ : Subgroup A) :=
    (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint) hrK hrR
  have hr_one : r = 1 := by simpa using hr_bot
  have hrA : (k : A) * r * (k : A)⁻¹ = a := by
    simpa [MulAut.conj_apply] using hr_eq
  simpa [hr_one] using hrA.symm

public theorem frobenius_existsUnique_conjBy_of_not_mem_kernel
    {A : Type u} [Group A] [Finite A]
    (K R : Subgroup A)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    {a : A} (haK : a ∉ K) :
    ∃! k : K, a ∈ R.conjBy (k : A) := by
  classical
  have hbij :=
    frobeniusConjPair_bijective K R hfrob hfrob.kernel_ne_bot hfrob.complement_ne_bot
  obtain ⟨xr, hxr⟩ := hbij.2 ⟨a, haK⟩
  refine ⟨xr.1, ?_, ?_⟩
  · have haeq : (xr.1 : A) * (xr.2.1 : A) * (xr.1 : A)⁻¹ = a := by
      simpa using congrArg Subtype.val hxr
    change a ∈ R.map (MulAut.conj (xr.1 : A)).toMonoidHom
    rw [Subgroup.mem_map]
    exact ⟨(xr.2.1 : A), xr.2.1.2, by simpa [MulAut.conj_apply] using haeq⟩
  · intro k hk
    rcases Subgroup.mem_map.mp hk with ⟨r, hrR, hr_eq⟩
    have hrA : (k : A) * r * (k : A)⁻¹ = a := by
      simpa [MulAut.conj_apply] using hr_eq
    have hr_ne_one_A : r ≠ 1 := by
      intro hr_one
      apply haK
      have ha_eq : a = 1 := by
        simp [hr_one] at hrA
        exact hrA.symm
      simp [ha_eq]
    let rp : {r : R // r ≠ 1} := ⟨⟨r, hrR⟩, by
      intro hsub
      exact hr_ne_one_A (congrArg Subtype.val hsub)⟩
    let pair : K × {r : R // r ≠ 1} := ⟨k, rp⟩
    have hpair_image :
        (⟨(pair.1 : A) * (pair.2.1 : A) * (pair.1 : A)⁻¹, by
          intro hmemK
          have hr_memK : (pair.2.1 : A) ∈ K := by
            have hxconj :=
              hfrob.normal.conj_mem
                ((pair.1 : A) * (pair.2.1 : A) * (pair.1 : A)⁻¹) hmemK
                (pair.1 : A)⁻¹
            simpa [mul_assoc] using hxconj
          have hr_eq_one : (pair.2.1 : A) = 1 := by
            have hr_bot : (pair.2.1 : A) ∈ (⊥ : Subgroup A) :=
              (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint)
                hr_memK pair.2.1.property
            simpa using hr_bot
          exact pair.2.2 (Subtype.ext hr_eq_one)⟩ : {g : A // g ∉ K}) =
        (⟨a, haK⟩ : {g : A // g ∉ K}) := by
      apply Subtype.ext
      dsimp [pair, rp]
      exact hrA
    have hpair_eq : pair = xr := hbij.1 (hpair_image.trans hxr.symm)
    exact congrArg Prod.fst hpair_eq

public theorem frobeniusProduct_coeff_sum_eq
    {A : Type u} [Group A] [Finite A]
    (K R : Subgroup A) [Fintype K]
    [∀ (a : A) (i : FrobeniusProductIndex K),
      Decidable (a ∈ frobeniusProductSubgroup K R i)]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    ∀ a : A,
      (∑ i : FrobeniusProductIndex K,
          if a ∈ frobeniusProductSubgroup K R i then
            frobeniusProductLeftCoeff K i
          else 0) =
        ∑ i : FrobeniusProductIndex K,
          if a ∈ frobeniusProductSubgroup K R i then
        frobeniusProductRightCoeff K i
          else 0 := by
  classical
  intro a
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [frobeniusProductSubgroup, frobeniusProductLeftCoeff, frobeniusProductRightCoeff]
  by_cases ha1 : a = 1
  · subst a
    simp
  · by_cases haK : a ∈ K
    · have hnone : ∀ k : K, ¬ a ∈ R.conjBy (k : A) := by
        intro k hk
        exact ha1 (frobenius_mem_conjBy_of_mem_kernel_eq_one K R hfrob haK hk)
      simp [ha1, haK, hnone]
    · have hnot_bot : ¬ a ∈ (⊥ : Subgroup A) := by
        intro ha_bot
        have ha_eq : a = 1 := by
          exact Subgroup.mem_bot.mp ha_bot
        exact haK (by simp [ha_eq])
      obtain ⟨k0, hk0, huniq⟩ :=
        frobenius_existsUnique_conjBy_of_not_mem_kernel K R hfrob haK
      have hcard :
          (Finset.univ.filter (fun x : K =>
            a ∈ frobeniusProductSubgroup K R (Sum.inr x))).card = 1 := by
        rw [← Fintype.card_subtype]
        exact Fintype.card_eq_one_iff.mpr ⟨⟨k0, by simpa [frobeniusProductSubgroup] using hk0⟩, fun y => by
          apply Subtype.ext
          exact huniq y.1 (by simpa [frobeniusProductSubgroup] using y.2)⟩
      have hsumR :
          (∑ a₂ : K,
            if a ∈ frobeniusProductSubgroup K R (Sum.inr a₂) then (1 : ℕ) else 0) = 1 := by
        rw [← Finset.sum_filter, Finset.sum_const, hcard]
        simp
      simp [ha1, haK]
      exact hsumR.symm

/-- Rewrite a sum over a finite subgroup as a filtered sum over the ambient
group. -/
public theorem subgroup_sum_eq_sum_ite
    {G M : Type*} [Group G] [Fintype G] [AddCommMonoid M]
    (A : Subgroup G) [DecidablePred (fun g : G => g ∈ A)] (F : G → M) :
    (∑ a : A, F (a : G)) = ∑ g : G, if g ∈ A then F g else 0 := by
  classical
  calc
    (∑ a : A, F (a : G)) =
        ∑ g ∈ (Finset.univ.filter fun g : G => g ∈ A), F g := by
          symm
          exact Finset.sum_subtype
            (s := Finset.univ.filter (fun g : G => g ∈ A))
            (p := fun g : G => g ∈ A)
            (h := by intro x; simp)
            (f := F)
    _ = ∑ g : G, if g ∈ A then F g else 0 := by
          exact Finset.sum_filter (s := Finset.univ) (p := fun g : G => g ∈ A) (f := F)

/-- A pointwise equality of subgroup coefficients gives the corresponding
weighted equality after summing any additive-valued class over the subgroups. -/
public theorem subgroup_weighted_sum_eq_of_coeff_sum_eq
    {G ι M : Type*} [Group G] [Fintype G] [Fintype ι] [AddCommMonoid M]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (m n : ι → ℕ)
    (F : G → M)
    (hcoeff : ∀ g : G,
      (∑ i : ι, if g ∈ A i then m i else 0) =
        ∑ i : ι, if g ∈ A i then n i else 0) :
    (∑ i : ι, m i • ∑ a : A i, F (a : G)) =
      ∑ i : ι, n i • ∑ a : A i, F (a : G) := by
  classical
  calc
    (∑ i : ι, m i • ∑ a : A i, F (a : G)) =
        ∑ i : ι, m i • ∑ g : G, if g ∈ A i then F g else 0 := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [subgroup_sum_eq_sum_ite (A i) F]
    _ = ∑ i : ι, ∑ g : G, if g ∈ A i then m i • F g else 0 := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro g _hg
          by_cases hgA : g ∈ A i <;> simp [hgA]
    _ = ∑ g : G, ∑ i : ι, if g ∈ A i then m i • F g else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ g : G, (∑ i : ι, if g ∈ A i then m i else 0) • F g := by
          apply Finset.sum_congr rfl
          intro g _hg
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hgA : g ∈ A i <;> simp [hgA]
    _ = ∑ g : G, (∑ i : ι, if g ∈ A i then n i else 0) • F g := by
          apply Finset.sum_congr rfl
          intro g _hg
          rw [hcoeff g]
    _ = ∑ g : G, ∑ i : ι, if g ∈ A i then n i • F g else 0 := by
          apply Finset.sum_congr rfl
          intro g _hg
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hgA : g ∈ A i <;> simp [hgA]
    _ = ∑ i : ι, ∑ g : G, if g ∈ A i then n i • F g else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i : ι, n i • ∑ g : G, if g ∈ A i then F g else 0 := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro g _hg
          by_cases hgA : g ∈ A i <;> simp [hgA]
    _ = ∑ i : ι, n i • ∑ a : A i, F (a : G) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [subgroup_sum_eq_sum_ite (A i) F]

public theorem fixedPointSubgroup_top_subgroup_eq
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M] :
    letI : MulDistribMulAction (↥(⊤ : Subgroup A)) M :=
      MulDistribMulAction.compHom M (⊤ : Subgroup A).subtype
    fixedPointSubgroup (↥(⊤ : Subgroup A)) M = fixedPointSubgroup A M := by
  let : MulDistribMulAction (↥(⊤ : Subgroup A)) M :=
    MulDistribMulAction.compHom M (⊤ : Subgroup A).subtype
  ext x
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hx a
    have ha : (⟨a, by simp⟩ : (⊤ : Subgroup A)) • x = x := hx ⟨a, by simp⟩
    simpa [MulAction.compHom_smul_def] using ha
  · intro hx a
    have ha : (a : A) • x = x := hx (a : A)
    simpa [MulAction.compHom_smul_def] using ha

public theorem fixedPointSubgroup_bot_subgroup_eq_top
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M] :
    letI : MulDistribMulAction (↥(⊥ : Subgroup A)) M :=
      MulDistribMulAction.compHom M (⊥ : Subgroup A).subtype
    fixedPointSubgroup (↥(⊥ : Subgroup A)) M = ⊤ := by
  let : MulDistribMulAction (↥(⊥ : Subgroup A)) M :=
    MulDistribMulAction.compHom M (⊥ : Subgroup A).subtype
  ext x
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro _hx
    simp
  · intro _hx a
    have haA : (a : A) = 1 := Subgroup.mem_bot.mp a.property
    have ha : a = 1 := by
      ext
      exact haA
    rw [ha]
    simp [MulAction.compHom_smul_def]

public theorem natCard_conjBy_eq {A : Type u} [Group A] (R : Subgroup A) (a : A) :
    Nat.card (R.conjBy a) = Nat.card R := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := R) (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective)

/-- The Frobenius product relation implies the usual cardinality identity when
the kernel has trivial fixed points. The source-specific Wielandt theorem only
has to supply the product relation. -/
public theorem fixedPointSubgroup_card_identity_kernel_fixed_bot_of_frobenius_of_product_card_eq
    {A M : Type u} [Group A] [Finite A] [Group M] [Finite M] [Nontrivial M]
    (K R : Subgroup A)
    [MulDistribMulAction A M]
    (hKbot :
      letI : MulDistribMulAction (↥K) M := MulDistribMulAction.compHom M K.subtype
      fixedPointSubgroup (↥K) M = ⊥)
    (hprod :
      letI : Fintype K := Fintype.ofFinite K
      (∏ i : FrobeniusProductIndex K,
          letI : MulDistribMulAction (↥(frobeniusProductSubgroup K R i)) M :=
            MulDistribMulAction.compHom M (frobeniusProductSubgroup K R i).subtype
          Nat.card (fixedPointSubgroup (↥(frobeniusProductSubgroup K R i)) M) ^
            (frobeniusProductLeftCoeff K i * Nat.card (frobeniusProductSubgroup K R i))) =
        ∏ i : FrobeniusProductIndex K,
          letI : MulDistribMulAction (↥(frobeniusProductSubgroup K R i)) M :=
            MulDistribMulAction.compHom M (frobeniusProductSubgroup K R i).subtype
          Nat.card (fixedPointSubgroup (↥(frobeniusProductSubgroup K R i)) M) ^
            (frobeniusProductRightCoeff K i * Nat.card (frobeniusProductSubgroup K R i))) :
    letI : MulDistribMulAction (↥R) M := MulDistribMulAction.compHom M R.subtype
    Nat.card M = Nat.card (fixedPointSubgroup (↥R) M) ^ Nat.card R := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : MulDistribMulAction (↥R) M := MulDistribMulAction.compHom M R.subtype
  let c : Subgroup A → ℕ := fun B =>
    let : MulDistribMulAction (↥B) M := MulDistribMulAction.compHom M B.subtype
    Nat.card (fixedPointSubgroup (↥B) M)
  have hprod_c :
      (∏ i : FrobeniusProductIndex K,
          c (frobeniusProductSubgroup K R i) ^
            (frobeniusProductLeftCoeff K i * Nat.card (frobeniusProductSubgroup K R i))) =
        ∏ i : FrobeniusProductIndex K,
          c (frobeniusProductSubgroup K R i) ^
            (frobeniusProductRightCoeff K i * Nat.card (frobeniusProductSubgroup K R i)) := by
    simpa [c] using hprod
  have hAfix : fixedPointSubgroup A M = ⊥ :=
    fixedPointSubgroup_top_eq_bot_of_subgroup_fixed_bot K hKbot
  have hTopC : c ⊤ = 1 := by
    dsimp [c]
    rw [fixedPointSubgroup_top_subgroup_eq, hAfix]
    simp
  have hBotC : c ⊥ = Nat.card M := by
    dsimp [c]
    rw [fixedPointSubgroup_bot_subgroup_eq_top]
    simp
  have hKC : c K = 1 := by
    dsimp [c]
    rw [hKbot]
    simp
  have hConjC : ∀ k : K, c (R.conjBy (k : A)) = c R := by
    intro k
    dsimp [c]
    exact (Nat.card_congr (fixedPointSubgroup_conjByEquiv R (k : A))).symm
  have hprod' : Nat.card M ^ Nat.card K = ∏ _k : K, c R ^ Nat.card R := by
    simpa [Fintype.prod_sum_type, Fin.prod_univ_three,
      frobeniusProductSubgroup, frobeniusProductLeftCoeff, frobeniusProductRightCoeff,
      hTopC, hBotC, hKC, hConjC, natCard_conjBy_eq] using hprod_c
  have hprod'' : Nat.card M ^ Nat.card K = (c R ^ Nat.card R) ^ Nat.card K := by
    simpa using hprod'
  exact pow_left_injective Nat.card_pos.ne' hprod''

/-- A conjugate of the complement by an element of the kernel still lies in the
same overgroup supplied by `section12ComplementIn`. -/
public theorem section12ComplementIn_conj_complement_le
    {G : Type u} [Group G]
    (UE U E : Subgroup G) :
    section12ComplementIn UE U E →
      ∀ u : U, E.conjBy (u : G) ≤ UE := by
  intro hcomp u x hx
  rw [Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨e, heE, hxe⟩
  rw [← hxe]
  exact UE.mul_mem (UE.mul_mem (hcomp.1 u.property) (hcomp.2.1 heE))
    (UE.inv_mem (hcomp.1 u.property))

/-- Fixed points of a normal actor subgroup are invariant under the full actor. -/
public theorem fixedPointSubgroup_invariant_of_normal
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    (B : Subgroup A) [B.Normal] :
    IsInvariant A M (fixedPointSubgroup (↥B) M) := by
  refine ⟨?_⟩
  intro g x
  constructor
  · intro hx
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro b
    have hxfix :
        ((⟨g⁻¹ * (b : A) * g, by
          simpa using (inferInstance : B.Normal).conj_mem (b : A) b.2 g⁻¹⟩ : B) : A) • x = x :=
      hx ⟨g⁻¹ * (b : A) * g, by
        simpa using (inferInstance : B.Normal).conj_mem (b : A) b.2 g⁻¹⟩
    calc
      (b : A) • (g • x) = g • (((g⁻¹ * (b : A) * g) : A) • x) := by
        simp [mul_smul, mul_assoc]
      _ = g • x := by rw [hxfix]
  · intro hx
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx ⊢
    intro b
    have hxfix :
        ((⟨g * (b : A) * g⁻¹, by
          exact (inferInstance : B.Normal).conj_mem (b : A) b.2 g⟩ : B) : A) • (g • x) =
            g • x :=
      hx ⟨g * (b : A) * g⁻¹, by
        exact (inferInstance : B.Normal).conj_mem (b : A) b.2 g⟩
    calc
      (b : A) • x = g⁻¹ • (((g * (b : A) * g⁻¹) : A) • (g • x)) := by
        simp [mul_smul, mul_assoc]
      _ = g⁻¹ • (g • x) := by rw [hxfix]
      _ = x := by simp

/-- Cardinality of a Frobenius join written as the product of kernel and
complement cardinalities. -/
public theorem section12ComplementIn_nat_card_eq_mul
    {G : Type u} [Group G] [Finite G]
    (UE U E : Subgroup G)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E) :
    Nat.card UE = Nat.card U * Nat.card E := by
  classical
  have hUnorm : (U.subgroupOf UE).Normal := by
    have hUnormSup : (U.subgroupOf (U ⊔ E)).Normal :=
      IsFrobeniusGroupWithKernelComplement.normal hfrob
    have hUEeq : UE = U ⊔ E := hcomp.2.2.1
    subst UE
    simpa using hUnormSup
  have hdisjSub : Disjoint (U.subgroupOf UE) (E.subgroupOf UE) := by
    have hdisj := hcomp.2.2.2
    rw [disjoint_iff] at hdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ E := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : U.subgroupOf UE ⊔ E.subgroupOf UE = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := E) (B := UE) hcomp.1 hcomp.2.1]
    rw [← hcomp.2.2.1]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hcompSub : (U.subgroupOf UE).IsComplement' (E.subgroupOf UE) := by
    let : (U.subgroupOf UE).Normal := hUnorm
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf UE) (E.subgroupOf UE) hdisjSub hsupTop
  have hmul := hcompSub.card_mul_card
  simpa [natCard_subgroupOf_eq U UE hcomp.1,
    natCard_subgroupOf_eq E UE hcomp.2.1] using hmul.symm

/-- Replacing the complement by a conjugate under the kernel keeps the same
Frobenius overgroup. -/
public theorem section12ComplementIn_sup_conj_complement_eq
    {G : Type u} [Group G]
    (UE U E : Subgroup G)
    (hcomp : section12ComplementIn UE U E)
    (u : U) :
    U ⊔ E.conjBy (u : G) = UE := by
  apply le_antisymm
  · exact sup_le hcomp.1 (section12ComplementIn_conj_complement_le UE U E hcomp u)
  · rw [hcomp.2.2.1]
    apply sup_le
    · exact le_sup_left
    · intro e he
      have hconj : (u : G) * e * (u : G)⁻¹ ∈ E.conjBy (u : G) := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        exact ⟨e, he, rfl⟩
      have hmem : (u : G)⁻¹ * ((u : G) * e * (u : G)⁻¹) * (u : G) ∈
          U ⊔ E.conjBy (u : G) := by
        exact (U ⊔ E.conjBy (u : G)).mul_mem
          ((U ⊔ E.conjBy (u : G)).mul_mem
            (Subgroup.mem_sup_left (U.inv_mem u.2))
            (Subgroup.mem_sup_right hconj))
          (Subgroup.mem_sup_left u.2)
      have hmul : (u : G)⁻¹ * ((u : G) * e * (u : G)⁻¹) * (u : G) = e := by
        group
      simpa [hmul] using hmem

/-- Fixed points of a complement and of its conjugate are equivalent when the
conjugate action is compatible with the ambient action. -/
public noncomputable def fixedPointSubgroup_conj_complement_equiv
    {G M : Type u} [Group G] [Group M]
    {UE U E : Subgroup G}
    [MulDistribMulAction UE M]
    (hcomp : section12ComplementIn UE U E)
    (u : U)
    [MulDistribMulAction (E.conjBy (u : G)) M]
    (hEcompat : ∀ (e : E.conjBy (u : G)) (m : M),
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m) :
    fixedPointSubgroup (↥(E.subgroupOf UE)) M ≃
      fixedPointSubgroup (↥(E.conjBy (u : G))) M := by
  let uUE : UE := ⟨(u : G), hcomp.1 u.2⟩
  refine
    { toFun := fun x =>
        ⟨uUE • x.1, ?_⟩
      invFun := fun y =>
        ⟨uUE⁻¹ • y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro e
    have he := e.2
    change (e : G) ∈ E.map (MulAut.conj (u : G)).toMonoidHom at he
    rw [Subgroup.mem_map] at he
    rcases he with ⟨e0, he0E, heq⟩
    let eUE : UE := ⟨e0, hcomp.2.1 he0E⟩
    have hx := (FixedPoints.mem_subgroup (M := E.subgroupOf UE) (a := x.1)).1 x.2
      ⟨eUE, by
        show (eUE : UE) ∈ E.subgroupOf UE
        exact he0E⟩
    have hxUE : (eUE : UE) • x.1 = x.1 := by
      change (eUE : UE) • (x.1 : M) = x.1 at hx
      exact hx
    have heUE_eq :
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) = uUE * eUE * uUE⁻¹ := by
      ext
      simpa [uUE, eUE] using heq.symm
    calc
      e • (uUE • x.1) =
          (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
            UE) • (uUE • x.1) := by
            rw [hEcompat e (uUE • x.1)]
      _ = (uUE * eUE * uUE⁻¹) • (uUE • x.1) := by rw [heUE_eq]
      _ = uUE • (eUE • x.1) := by simp [mul_smul, mul_assoc]
      _ = uUE • x.1 := by rw [hxUE]
  · rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro e
    let eG : G := (e : UE)
    have heE : eG ∈ E := e.2
    let eConj : E.conjBy (u : G) :=
      ⟨(u : G) * eG * (u : G)⁻¹, by
        change (u : G) * eG * (u : G)⁻¹ ∈
          E.map (MulAut.conj (u : G)).toMonoidHom
        rw [Subgroup.mem_map]
        exact ⟨eG, heE, rfl⟩⟩
    have hy := (FixedPoints.mem_subgroup (M := E.conjBy (u : G)) (a := y.1)).1 y.2 eConj
    have heConj_eq :
        (⟨(eConj : G),
            section12ComplementIn_conj_complement_le UE U E hcomp u eConj.2⟩ : UE) =
          uUE * e * uUE⁻¹ := by
      ext
      rfl
    have hyUE : (uUE * e * uUE⁻¹) • y.1 = y.1 := by
      calc
        (uUE * e * uUE⁻¹) • y.1 =
            (⟨(eConj : G),
              section12ComplementIn_conj_complement_le UE U E hcomp u eConj.2⟩ : UE) • y.1 := by
              rw [heConj_eq]
        _ = eConj • y.1 := by rw [hEcompat eConj y.1]
        _ = y.1 := hy
    calc
      e • (uUE⁻¹ • y.1) = uUE⁻¹ • ((uUE * (e : UE) * uUE⁻¹) • y.1) := by
        change (e : UE) • (uUE⁻¹ • y.1) =
          uUE⁻¹ • ((uUE * (e : UE) * uUE⁻¹) • y.1)
        simp [mul_smul, mul_assoc]
      _ = uUE⁻¹ • y.1 := by rw [hyUE]
  · intro x
    ext
    simp [uUE]
  · intro y
    ext
    simp [uUE]

/-- If the kernel fixes everything, fixed points of every conjugate complement
are exactly the fixed points of the whole overgroup. -/
public theorem fixedPointSubgroup_conj_complement_eq_of_kernel_fixed_top
    {G M : Type u} [Group G] [Group M]
    {UE U E : Subgroup G}
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hcomp : section12ComplementIn UE U E)
    (u : U)
    [MulDistribMulAction (E.conjBy (u : G)) M]
    (hUcompat : ∀ (u0 : U) (m : M),
      u0 • m = (⟨(u0 : G), hcomp.1 u0.2⟩ : UE) • m)
    (hEcompat : ∀ (e : E.conjBy (u : G)) (m : M),
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    (hUtop : fixedPointSubgroup (↥U) M = ⊤) :
    fixedPointSubgroup (↥(E.conjBy (u : G))) M = fixedPointSubgroup (↥UE) M := by
  ext m
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hm a
    let aG : G := (a : UE)
    have haUE : aG ∈ UE := a.2
    have hjoin : UE = U ⊔ E.conjBy (u : G) :=
      (section12ComplementIn_sup_conj_complement_eq UE U E hcomp u).symm
    have ha_closure :
        aG ∈ Subgroup.closure ((U : Set G) ∪ (E.conjBy (u : G) : Set G)) := by
      simpa [aG, Subgroup.sup_eq_closure, hjoin] using haUE
    refine Subgroup.closure_induction
      (p := fun g _ => ∀ hgUE : g ∈ UE, (⟨g, hgUE⟩ : UE) • m = m)
      ?mem ?one ?mul ?inv ha_closure haUE
    · intro g hg hgUE
      rcases hg with hgU | hgE
      · have hgm : (⟨g, hgU⟩ : U) • m = m := by
          have hmU : m ∈ fixedPointSubgroup (↥U) M := by simp [hUtop]
          exact (FixedPoints.mem_subgroup (M := U) (a := m)).1 hmU ⟨g, hgU⟩
        simpa [hUcompat ⟨g, hgU⟩ m] using hgm
      · have hgm : (⟨g, hgE⟩ : E.conjBy (u : G)) • m = m :=
          hm ⟨g, hgE⟩
        simpa [hEcompat ⟨g, hgE⟩ m] using hgm
    · intro hgUE
      have hone : (⟨1, hgUE⟩ : UE) = 1 := by
        ext
        rfl
      simp [hone]
    · intro x y hx hy hx_fix hy_fix hxyUE
      have hxUE : x ∈ UE := by
        simpa [Subgroup.sup_eq_closure, hjoin] using hx
      have hyUE : y ∈ UE := by
        simpa [Subgroup.sup_eq_closure, hjoin] using hy
      have hx_eq := hx_fix hxUE
      have hy_eq := hy_fix hyUE
      have hmul_eq : (⟨x, hxUE⟩ : UE) * ⟨y, hyUE⟩ = ⟨x * y, hxyUE⟩ := by
        ext
        rfl
      calc
        (⟨x * y, hxyUE⟩ : UE) • m =
            ((⟨x, hxUE⟩ : UE) * ⟨y, hyUE⟩) • m := by rw [hmul_eq]
        _ = (⟨x, hxUE⟩ : UE) • ((⟨y, hyUE⟩ : UE) • m) := by rw [mul_smul]
        _ = (⟨x, hxUE⟩ : UE) • m := by rw [hy_eq]
        _ = m := hx_eq
    · intro x hx hx_fix hxinvUE
      have hxUE : x ∈ UE := by
        simpa [Subgroup.sup_eq_closure, hjoin] using hx
      have hx_eq := hx_fix hxUE
      have hxinv_eq : (⟨x⁻¹, hxinvUE⟩ : UE) = (⟨x, hxUE⟩ : UE)⁻¹ := by
        ext
        rfl
      rw [hxinv_eq]
      exact inv_smul_eq_iff.mpr hx_eq.symm
  · intro hm e
    have hUE := hm
      (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ : UE)
    simpa [hEcompat e m] using hUE

/-- If a compatible subgroup actor has no fixed points, neither does the
ambient actor. -/
public theorem fixedPointSubgroup_eq_bot_of_fixedPointSubgroup_subgroup_eq_bot
    {G M : Type u} [Group G] [Group M]
    {UE U : Subgroup G}
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hUle : U ≤ UE)
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hUle u.2⟩ : UE) • m)
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    fixedPointSubgroup (↥UE) M = ⊥ := by
  apply le_antisymm
  · intro m hm
    have hmU : m ∈ fixedPointSubgroup (↥U) M := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hm ⊢
      intro u
      calc
        u • m = (⟨(u : G), hUle u.2⟩ : UE) • m := hUcompat u m
        _ = m := hm ⟨(u : G), hUle u.2⟩
    simpa [hUbot] using hmU
  · exact bot_le


/-- A nontrivial solvable group with no proper nontrivial normal invariant
subgroups for the actor action is elementary abelian. -/
public theorem chiefFactor_elementaryAbelian_of_nontrivial
    {A M : Type u} [Group A] [Group M] [Finite M] [MulDistribMulAction A M]
    [Nontrivial M]
    (hsolvM : Group.IsSolvable M)
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant A M N → N ≠ ⊥ → N = ⊤) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p M := by
  classical
  have hcommM : IsMulCommutative M := by
    have hcomm_lt : commutator M < (⊤ : Subgroup M) := by
      let : Group.IsSolvable M := hsolvM
      exact Group.IsSolvable.commutator_lt_top_of_nontrivial (G := M)
    have htop_inv : IsInvariant A M (⊤ : Subgroup M) := by
      refine ⟨?_⟩
      intro a g
      simp
    let : IsInvariant A M (⊤ : Subgroup M) := htop_inv
    have hcomm_inv : IsInvariant A M (commutator M) := by
      simpa [_root_.commutator_def] using
        (isInvariant_commutator (A := A) (G := M)
          (H := (⊤ : Subgroup M)) (K := (⊤ : Subgroup M)))
    have hcomm_eq_bot : commutator M = ⊥ := by
      by_contra hne
      have htop : commutator M = (⊤ : Subgroup M) :=
        hminv (commutator M) inferInstance hcomm_inv hne
      exact (ne_of_lt hcomm_lt) htop
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun a b ↦ ?_
    have htop_le_cent :
        (⊤ : Subgroup M) ≤ Subgroup.centralizer ((⊤ : Subgroup M) : Set M) := by
      have htop_comm_bot : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊥ := by
        simpa [_root_.commutator_def] using hcomm_eq_bot
      exact
        (Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := (⊤ : Subgroup M)) (H₂ := (⊤ : Subgroup M))).1 htop_comm_bot
    have ha_cent : a ∈ Subgroup.centralizer ((⊤ : Subgroup M) : Set M) :=
      htop_le_cent trivial
    exact ((Subgroup.mem_centralizer_iff.mp ha_cent) b trivial).symm
  let : IsMulCommutative M := hcommM
  let : CommGroup M := IsMulCommutative.instCommGroup
  have hnilM : Group.IsNilpotent M := by
    refine ⟨1, ?_⟩
    have hcenter : Subgroup.center M = ⊤ := by
      ext x
      constructor
      · intro _hx
        simp
      · intro _hx
        rw [Subgroup.mem_center_iff]
        intro y
        simpa using (IsMulCommutative.is_comm (M := M)).comm y x
    simpa [Subgroup.upperCentralSeries_one] using hcenter
  have hM_card_gt_one : 1 < Nat.card M :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨p, hp_prime, hp_dvd_cardM⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card M) (Nat.ne_of_gt hM_card_gt_one)
  let : Fact p.Prime := ⟨hp_prime⟩
  let P : Sylow p M := default
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := M) (p := p) P hp_dvd_cardM
  have hP_normal : (P : Subgroup M).Normal :=
    Group.IsNilpotent.sylow_normal hnilM p P
  let : (P : Subgroup M).Characteristic := Sylow.characteristic_of_normal P hP_normal
  have hP_inv : IsInvariant A M (P : Subgroup M) :=
    isInvariant_of_characteristic (A := A) (G := M) (P : Subgroup M)
  have hP_top : (P : Subgroup M) = ⊤ :=
    hminv (P : Subgroup M) hP_normal hP_inv hP_ne_bot
  have htop_p : IsPGroup p (⊤ : Subgroup M) :=
    P.isPGroup'.of_equiv (MulEquiv.subgroupCongr hP_top)
  have hMpgroup : IsPGroup p M := htop_p.of_equiv Subgroup.topEquiv
  let : Fact (IsPGroup p M) := ⟨hMpgroup⟩
  let Ω : Subgroup M := omega₁ (G := M) (p := p)
  let : Ω.Characteristic := by
    simpa [Ω] using omega₁_characteristic (G := M) (p := p)
  have hΩ_inv : IsInvariant A M Ω :=
    isInvariant_of_characteristic (A := A) (G := M) Ω
  have hΩ_ne_bot : Ω ≠ ⊥ := by
    let : Fintype M := Fintype.ofFinite M
    obtain ⟨x, hx_order⟩ := _root_.exists_prime_orderOf_dvd_card (G := M) p <| by
      simpa [Nat.card_eq_fintype_card] using hp_dvd_cardM
    have hx_ne_one : x ≠ (1 : M) := by
      intro hx
      have : 1 = p := by simpa [hx] using hx_order
      exact hp_prime.ne_one this.symm
    have hx_pow : x ^ p = 1 := by
      simpa [hx_order] using pow_orderOf_eq_one x
    have hx_mem : x ∈ Ω := by
      change x ∈ Subgroup.closure {y : M | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [Ω, omega₁, omega, pow_one] using hx_pow
    intro hΩ_bot
    have hx_bot : x ∈ (⊥ : Subgroup M) := by
      simpa [hΩ_bot] using hx_mem
    exact hx_ne_one (by simpa using hx_bot)
  have hΩ_top : Ω = ⊤ := hminv Ω inferInstance hΩ_inv hΩ_ne_bot
  have hpow : ∀ x : M, x ^ p = 1 := by
    intro x
    have hxΩ : x ∈ Ω := by simp [hΩ_top]
    have hx' : x ∈ Subgroup.closure {y : M | y ^ (p ^ 1) = 1} := by
      simpa [Ω, omega₁, omega] using hxΩ
    refine
      Subgroup.closure_induction (k := {y : M | y ^ (p ^ 1) = 1})
        (p := fun z _hz => z ^ p = 1) (x := x) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simpa [pow_one] using hy
    · simp
    · intro a b _ha _hb ha hb
      calc
        (a * b) ^ p = a ^ p * b ^ p := by simpa using mul_pow a b p
        _ = 1 := by simp [ha, hb]
    · intro a _ha ha
      simp [ha]
  refine ⟨p, hp_prime, ?_⟩
  exact
    { toIsMulCommutative := hcommM
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hpow }

/-- A solvable actor-chief factor is either subsingleton or nontrivial
elementary abelian. -/
public theorem chiefFactor_elementaryAbelian_or_subsingleton
    {A M : Type u} [Group A] [Group M] [Finite M] [MulDistribMulAction A M]
    (hsolvM : Group.IsSolvable M)
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant A M N → N ≠ ⊥ → N = ⊤) :
    Subsingleton M ∨ Nontrivial M ∧ ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p M := by
  by_cases hsub : Subsingleton M
  · exact Or.inl hsub
  · let : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    exact Or.inr ⟨inferInstance,
      chiefFactor_elementaryAbelian_of_nontrivial
        (A := A) (M := M) hsolvM hminv⟩

/-- Fixed-point subgroup cardinalities factor over invariant normal quotients.

This is the actor-level quotient step used in Wielandt-style induction
arguments. -/
public theorem fixedPointSubgroup_card_eq_mul_quotient_action
    {A M : Type u} [Group A] [Finite A] [Group M] [Finite M]
    [MulDistribMulAction A M]
    {N : Subgroup M} [N.Normal]
    (hNinv : IsInvariant A M N)
    (hsolvM : Group.IsSolvable M)
    (hcopA : Nat.Coprime (Nat.card A) (Nat.card M)) :
    letI : IsInvariant A M N := hNinv
    letI : MulDistribMulAction A (M ⧸ N) :=
      quotientMulDistribMulAction (A := A) (G := M) N hNinv
    Nat.card (fixedPointSubgroup A M) =
      Nat.card (fixedPointSubgroup A N) *
        Nat.card (fixedPointSubgroup A (M ⧸ N)) := by
  let : IsInvariant A M N := hNinv
  let : MulDistribMulAction A (M ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := M) N hNinv
  have hcopTop : Nat.Coprime (Nat.card (⊤ : Subgroup A)) (Nat.card M) := by
    simpa using hcopA
  have hfactor :=
    fixedPointSubgroup_card_eq_mul_quotient_of_solvable_coprime
      (G := A) (M := M) (R := (⊤ : Subgroup A)) (N := N)
      hNinv hsolvM hcopTop
  simpa [fixedPointSubgroup_top_subgroup_eq] using hfactor


/-- Arithmetic lift for product identities whose factors split over a normal
subgroup and quotient. -/
public theorem fixedPointSubgroup_product_lift_card_factors
    {ι : Type*} [Fintype ι]
    (aN aQ bN bQ dN dQ m n : ℕ)
    (cN cQ e : ι → ℕ)
    (hN : aN ^ m * bN ^ n = (∏ i, cN i ^ e i) * dN ^ n)
    (hQ : aQ ^ m * bQ ^ n = (∏ i, cQ i ^ e i) * dQ ^ n) :
    (aN * aQ) ^ m * (bN * bQ) ^ n =
      (∏ i, (cN i * cQ i) ^ e i) * (dN * dQ) ^ n := by
  classical
  calc
    (aN * aQ) ^ m * (bN * bQ) ^ n =
        (aN ^ m * bN ^ n) * (aQ ^ m * bQ ^ n) := by
          rw [Nat.mul_pow, Nat.mul_pow]
          ac_rfl
    _ = ((∏ i, cN i ^ e i) * dN ^ n) *
        ((∏ i, cQ i ^ e i) * dQ ^ n) := by
          rw [hN, hQ]
    _ = ((∏ i, cN i ^ e i) * (∏ i, cQ i ^ e i)) *
        (dN ^ n * dQ ^ n) := by
          ac_rfl
    _ = (∏ i, cN i ^ e i * cQ i ^ e i) * (dN * dQ) ^ n := by
          rw [← Finset.prod_mul_distrib, ← Nat.mul_pow]
    _ = (∏ i, (cN i * cQ i) ^ e i) * (dN * dQ) ^ n := by
          congr 1
          apply Finset.prod_congr rfl
          intro i _hi
          rw [Nat.mul_pow]

/-- Lift a product identity across pointwise factorizations of every factor. -/
public theorem product_pow_eq_lift_factors
    {ι : Type*} [Fintype ι]
    (aN aQ eL eR : ι → ℕ)
    (hN : (∏ i, aN i ^ eL i) = ∏ i, aN i ^ eR i)
    (hQ : (∏ i, aQ i ^ eL i) = ∏ i, aQ i ^ eR i) :
    (∏ i, (aN i * aQ i) ^ eL i) =
      ∏ i, (aN i * aQ i) ^ eR i := by
  classical
  calc
    (∏ i, (aN i * aQ i) ^ eL i) =
        ∏ i, aN i ^ eL i * aQ i ^ eL i := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [Nat.mul_pow]
    _ = (∏ i, aN i ^ eL i) * ∏ i, aQ i ^ eL i := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ i, aN i ^ eR i) * ∏ i, aQ i ^ eR i := by
          rw [hN, hQ]
    _ = ∏ i, aN i ^ eR i * aQ i ^ eR i := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ i, (aN i * aQ i) ^ eR i := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [Nat.mul_pow]

/-- Cardinality of fixed points for the restricted action on an invariant
subgroup. This packages the local instances needed in downstream theorem
statements. -/
public noncomputable def fixedPointSubgroup_card_subgroup_of_invariant
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    (N : Subgroup M) (hNinv : IsInvariant A M N) : ℕ :=
  letI : IsInvariant A M N := hNinv
  Nat.card (fixedPointSubgroup A N)

/-- Cardinality of fixed points for the induced action on a quotient by an
invariant normal subgroup. -/
public noncomputable def fixedPointSubgroup_card_quotient_of_invariant
    {A M : Type u} [Group A] [Group M] [MulDistribMulAction A M]
    (N : Subgroup M) [N.Normal] (hNinv : IsInvariant A M N) : ℕ :=
  letI : IsInvariant A M N := hNinv
  letI : MulDistribMulAction A (M ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := M) N hNinv
  Nat.card (fixedPointSubgroup A (M ⧸ N))

/-- Lift a family fixed-point product identity from an invariant normal subgroup
and its quotient to the ambient group. -/
public theorem fixedPointSubgroup_product_card_eq_lift_invariant_normal
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι]
    (A : ι → Subgroup G)
    (eL eR : ι → ℕ)
    {N : Subgroup V} [N.Normal]
    (hAinv : ∀ i : ι,
      letI : MulDistribMulAction (↥(A i)) V :=
        MulDistribMulAction.compHom V (A i).subtype
      IsInvariant (↥(A i)) V N)
    (hsolvV : Group.IsSolvable V)
    (hcopA : ∀ i : ι, Nat.Coprime (Nat.card (A i)) (Nat.card V))
    (hNid :
      (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_subgroup_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ eL i) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_subgroup_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ eR i)
    (hQid :
      (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_quotient_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ eL i) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_quotient_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ eR i) :
    (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ eL i) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ eR i := by
  classical
  let cV : ι → ℕ := fun i =>
    let : MulDistribMulAction (↥(A i)) V :=
      MulDistribMulAction.compHom V (A i).subtype
    Nat.card (fixedPointSubgroup (↥(A i)) V)
  let cN : ι → ℕ := fun i =>
    let : MulDistribMulAction (↥(A i)) V :=
      MulDistribMulAction.compHom V (A i).subtype
    fixedPointSubgroup_card_subgroup_of_invariant (A := ↥(A i)) (M := V)
      N (hAinv i)
  let cQ : ι → ℕ := fun i =>
    let : MulDistribMulAction (↥(A i)) V :=
      MulDistribMulAction.compHom V (A i).subtype
    fixedPointSubgroup_card_quotient_of_invariant (A := ↥(A i)) (M := V)
      N (hAinv i)
  have hfactor : ∀ i : ι, cV i = cN i * cQ i := by
    intro i
    let : MulDistribMulAction (↥(A i)) V :=
      MulDistribMulAction.compHom V (A i).subtype
    let : IsInvariant (↥(A i)) V N := hAinv i
    let : MulDistribMulAction (↥(A i)) (V ⧸ N) :=
      quotientMulDistribMulAction (A := ↥(A i)) (G := V) N (hAinv i)
    simpa [cV, cN, cQ, fixedPointSubgroup_card_subgroup_of_invariant,
      fixedPointSubgroup_card_quotient_of_invariant] using
      fixedPointSubgroup_card_eq_mul_quotient_action
        (A := ↥(A i)) (M := V) (N := N) (hAinv i) hsolvV (hcopA i)
  have hNid' : (∏ i : ι, cN i ^ eL i) = ∏ i : ι, cN i ^ eR i := by
    simpa [cN] using hNid
  have hQid' : (∏ i : ι, cQ i ^ eL i) = ∏ i : ι, cQ i ^ eR i := by
    simpa [cQ] using hQid
  change (∏ i : ι, cV i ^ eL i) = ∏ i : ι, cV i ^ eR i
  calc
    (∏ i : ι, cV i ^ eL i) =
        ∏ i : ι, (cN i * cQ i) ^ eL i := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [hfactor i]
    _ = ∏ i : ι, (cN i * cQ i) ^ eR i :=
          product_pow_eq_lift_factors cN cQ eL eR hNid' hQid'
    _ = ∏ i : ι, cV i ^ eR i := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [hfactor i]

/-- The invariant-normal lift specialized to the coefficient exponents used in
Wielandt's product theorem. -/
public theorem fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_lift_invariant_normal
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι]
    (A : ι → Subgroup G)
    (m n : ι → ℕ)
    {N : Subgroup V} [N.Normal]
    (hAinv : ∀ i : ι,
      letI : MulDistribMulAction (↥(A i)) V :=
        MulDistribMulAction.compHom V (A i).subtype
      IsInvariant (↥(A i)) V N)
    (hsolvV : Group.IsSolvable V)
    (hcopA : ∀ i : ι, Nat.Coprime (Nat.card (A i)) (Nat.card V))
    (hNid :
      (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_subgroup_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_subgroup_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ (n i * Nat.card (A i)))
    (hQid :
      (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_quotient_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_quotient_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ (n i * Nat.card (A i))) :
    (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
  exact
    fixedPointSubgroup_product_card_eq_lift_invariant_normal
      (A := A) (eL := fun i => m i * Nat.card (A i))
      (eR := fun i => n i * Nat.card (A i))
      hAinv hsolvV hcopA hNid hQid

/-- Invariance under a full actor restricts to invariance under any subgroup
actor with the restricted action. -/
public theorem isInvariant_subgroup_actor_of_isInvariant
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (A : Subgroup G) {N : Subgroup V}
    (hNinv : IsInvariant G V N) :
    letI : MulDistribMulAction A V := MulDistribMulAction.compHom V A.subtype
    IsInvariant A V N := by
  let : MulDistribMulAction A V := MulDistribMulAction.compHom V A.subtype
  refine ⟨?_⟩
  intro a v
  change v ∈ N ↔ (a : G) • v ∈ N
  exact IsInvariant.invariant (A := G) (G := V) (H := N) (a : G) v

/-- The coefficient-product quotient lift in the form used by induction on a
fully invariant normal subgroup. -/
public theorem fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_lift_global_invariant_normal
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hsolvV : Group.IsSolvable V)
    (A : ι → Subgroup G)
    (m n : ι → ℕ)
    {N : Subgroup V} [N.Normal]
    (hGinv : IsInvariant G V N)
    (hNid :
      letI : IsInvariant G V N := hGinv
      letI : MulDistribMulAction G N := inferInstance
      (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) N :=
          MulDistribMulAction.compHom N (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) N) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) N :=
          MulDistribMulAction.compHom N (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) N) ^ (n i * Nat.card (A i)))
    (hQid :
      letI : IsInvariant G V N := hGinv
      letI : MulDistribMulAction G (V ⧸ N) :=
        quotientMulDistribMulAction (A := G) (G := V) N hGinv
      (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) (V ⧸ N) :=
          MulDistribMulAction.compHom (V ⧸ N) (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) (V ⧸ N)) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) (V ⧸ N) :=
          MulDistribMulAction.compHom (V ⧸ N) (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) (V ⧸ N)) ^ (n i * Nat.card (A i))) :
    (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
  classical
  let hAinv : ∀ i : ι,
      let : MulDistribMulAction (↥(A i)) V :=
        MulDistribMulAction.compHom V (A i).subtype
      IsInvariant (↥(A i)) V N := fun i =>
    isInvariant_subgroup_actor_of_isInvariant (A i) hGinv
  have hcopA : ∀ i : ι, Nat.Coprime (Nat.card (A i)) (Nat.card V) := by
    intro i
    exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card (A i)) hcop.symm
  have hNid' :
      (∏ i : ι,
        let : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_subgroup_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        let : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_subgroup_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ (n i * Nat.card (A i)) := by
    simpa [fixedPointSubgroup_card_subgroup_of_invariant, hAinv] using hNid
  have hQid' :
      (∏ i : ι,
        let : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_quotient_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        let : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        fixedPointSubgroup_card_quotient_of_invariant (A := ↥(A i)) (M := V)
          N (hAinv i) ^ (n i * Nat.card (A i)) := by
    simpa [fixedPointSubgroup_card_quotient_of_invariant, hAinv] using hQid
  exact
    fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_lift_invariant_normal
      (A := A) (m := m) (n := n) hAinv hsolvV hcopA hNid' hQid'

set_option backward.isDefEq.respectTransparency false in
/-- Strong-induction wrapper for Wielandt's coefficient-product theorem.

If the theorem is known for every solvable coprime action with no proper
nontrivial invariant normal subgroup, then it holds in general. The nonminimal
step is exactly the invariant-normal quotient lift. -/
public theorem fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_of_minimal_invariant
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hsolv : Group.IsSolvable V)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (m n : ι → ℕ)
    (hcoeff : ∀ g : G,
      (∑ i : ι, if g ∈ A i then m i else 0) =
        ∑ i : ι, if g ∈ A i then n i else 0)
    (hminimal :
      ∀ {M : Type u} [Group M] [Finite M] [MulDistribMulAction G M],
        Nat.Coprime (Nat.card M) (Nat.card G) →
        Group.IsSolvable M →
        (∀ N : Subgroup M, N.Normal → IsInvariant G M N → N ≠ ⊥ → N = ⊤) →
        (∀ g : G,
          (∑ i : ι, if g ∈ A i then m i else 0) =
            ∑ i : ι, if g ∈ A i then n i else 0) →
        (∏ i : ι,
            letI : MulDistribMulAction (↥(A i)) M :=
              MulDistribMulAction.compHom M (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) M) ^ (m i * Nat.card (A i))) =
          ∏ i : ι,
            letI : MulDistribMulAction (↥(A i)) M :=
              MulDistribMulAction.compHom M (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) M) ^ (n i * Nat.card (A i))) :
    (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ (M : Type u) [Group M] [Finite M] [MulDistribMulAction G M],
      Nat.card M = k →
      Nat.Coprime (Nat.card M) (Nat.card G) →
      Group.IsSolvable M →
      (∏ i : ι,
          let : MulDistribMulAction (↥(A i)) M :=
            MulDistribMulAction.compHom M (A i).subtype
          Nat.card (fixedPointSubgroup (↥(A i)) M) ^ (m i * Nat.card (A i))) =
        ∏ i : ι,
          let : MulDistribMulAction (↥(A i)) M :=
            MulDistribMulAction.compHom M (A i).subtype
          Nat.card (fixedPointSubgroup (↥(A i)) M) ^ (n i * Nat.card (A i))
  have hP : ∀ k, P k := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih M _ _ _ hcard hcopM hsolvM
    by_cases hminv :
        ∀ N : Subgroup M, N.Normal → IsInvariant G M N → N ≠ ⊥ → N = ⊤
    · exact hminimal hcopM hsolvM hminv hcoeff
    · push Not at hminv
      rcases hminv with ⟨N, hNnormal, hNinv, hNne_bot, hNne_top⟩
      let : N.Normal := hNnormal
      let : IsInvariant G M N := hNinv
      let : MulDistribMulAction G (M ⧸ N) :=
        quotientMulDistribMulAction (A := G) (G := M) N hNinv
      have hNlt : Nat.card N < k := by
        have hN_lt_top : N < ⊤ := lt_top_iff_ne_top.mpr hNne_top
        have hlt : Nat.card N < Nat.card M := by
          simpa using natCard_lt_of_subgroup_lt hN_lt_top
        simpa [hcard] using hlt
      have hQlt : Nat.card (M ⧸ N) < k := by
        have hlt := natCard_quotient_lt_natCard_of_ne_bot N hNne_bot
        simpa [hcard] using hlt
      have hsolvN : Group.IsSolvable N := by
        let : Group.IsSolvable M := hsolvM
        infer_instance
      have hsolvQ : Group.IsSolvable (M ⧸ N) := by
        let : Group.IsSolvable M := hsolvM
        infer_instance
      have hcopN : Nat.Coprime (Nat.card N) (Nat.card G) := by
        exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card N) hcopM
      have hcopQ : Nat.Coprime (Nat.card (M ⧸ N)) (Nat.card G) := by
        exact Nat.Coprime.of_dvd_left (Subgroup.card_quotient_dvd_card (s := N)) hcopM
      have hNid :
          let : IsInvariant G M N := hNinv
          let : MulDistribMulAction G N := inferInstance
          (∏ i : ι,
            let : MulDistribMulAction (↥(A i)) N :=
              MulDistribMulAction.compHom N (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) N) ^ (m i * Nat.card (A i))) =
          ∏ i : ι,
            let : MulDistribMulAction (↥(A i)) N :=
              MulDistribMulAction.compHom N (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) N) ^ (n i * Nat.card (A i)) := by
        exact ih (Nat.card N) hNlt N rfl hcopN hsolvN
      have hQid :
          let : IsInvariant G M N := hNinv
          let : MulDistribMulAction G (M ⧸ N) :=
            quotientMulDistribMulAction (A := G) (G := M) N hNinv
          (∏ i : ι,
            let : MulDistribMulAction (↥(A i)) (M ⧸ N) :=
              MulDistribMulAction.compHom (M ⧸ N) (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) (M ⧸ N)) ^ (m i * Nat.card (A i))) =
          ∏ i : ι,
            let : MulDistribMulAction (↥(A i)) (M ⧸ N) :=
              MulDistribMulAction.compHom (M ⧸ N) (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) (M ⧸ N)) ^ (n i * Nat.card (A i)) := by
        exact ih (Nat.card (M ⧸ N)) hQlt (M ⧸ N) rfl hcopQ hsolvQ
      exact
        fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_lift_global_invariant_normal
          (G := G) (V := M) (ι := ι) hcopM hsolvM A m n hNinv hNid hQid
  exact hP (Nat.card V) V rfl hcop hsolv

/-- Reduce the minimal-invariant case of Wielandt's coefficient-product theorem
to the nontrivial elementary-abelian case. -/
public theorem
    fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_minimal_of_elementaryAbelian
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hsolv : Group.IsSolvable V)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (m n : ι → ℕ)
    (hcoeff : ∀ g : G,
      (∑ i : ι, if g ∈ A i then m i else 0) =
        ∑ i : ι, if g ∈ A i then n i else 0)
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (helem :
      ∀ {M : Type u} [Group M] [Finite M] [MulDistribMulAction G M] [Nontrivial M]
        {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M],
        Nat.Coprime (Nat.card M) (Nat.card G) →
        (∀ N : Subgroup M, N.Normal → IsInvariant G M N → N ≠ ⊥ → N = ⊤) →
        (∀ g : G,
          (∑ i : ι, if g ∈ A i then m i else 0) =
            ∑ i : ι, if g ∈ A i then n i else 0) →
        (∏ i : ι,
            let : MulDistribMulAction (↥(A i)) M :=
              MulDistribMulAction.compHom M (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) M) ^ (m i * Nat.card (A i))) =
          ∏ i : ι,
            let : MulDistribMulAction (↥(A i)) M :=
              MulDistribMulAction.compHom M (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) M) ^ (n i * Nat.card (A i))) :
    (∏ i : ι,
        let : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        let : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
  classical
  rcases chiefFactor_elementaryAbelian_or_subsingleton
      (A := G) (M := V) hsolv hminv with hsub | ⟨hNontriv, p, hp, hElem⟩
  · let : Subsingleton V := hsub
    have hcard : ∀ i : ι,
        let : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) = 1 := by
      intro i
      let : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    calc
      (∏ i : ι,
          let : MulDistribMulAction (↥(A i)) V :=
            MulDistribMulAction.compHom V (A i).subtype
          Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
          ∏ i : ι, (1 : ℕ) ^ (m i * Nat.card (A i)) := by
            apply Finset.prod_congr rfl
            intro i _hi
            exact congrArg (fun c : ℕ => c ^ (m i * Nat.card (A i))) (hcard i)
      _ = 1 := by simp
      _ = ∏ i : ι, (1 : ℕ) ^ (n i * Nat.card (A i)) := by simp
      _ = ∏ i : ι,
          let : MulDistribMulAction (↥(A i)) V :=
            MulDistribMulAction.compHom V (A i).subtype
          Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
            symm
            apply Finset.prod_congr rfl
            intro i _hi
            have hci := hcard i
            dsimp only at hci ⊢
            rw [hci]
  · let : Nontrivial V := hNontriv
    let : Fact p.Prime := ⟨hp⟩
    let : IsElementaryAbelian p V := hElem
    exact helem (M := V) (p := p) hcop hminv hcoeff

/-- Strong-induction reduction of Wielandt's coefficient-product theorem to
the nontrivial elementary-abelian minimal-invariant case. -/
public theorem fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_of_elementaryAbelian_minimal
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hsolv : Group.IsSolvable V)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (m n : ι → ℕ)
    (hcoeff : ∀ g : G,
      (∑ i : ι, if g ∈ A i then m i else 0) =
        ∑ i : ι, if g ∈ A i then n i else 0)
    (helem :
      ∀ {M : Type u} [Group M] [Finite M] [MulDistribMulAction G M] [Nontrivial M]
        {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M],
        Nat.Coprime (Nat.card M) (Nat.card G) →
        (∀ N : Subgroup M, N.Normal → IsInvariant G M N → N ≠ ⊥ → N = ⊤) →
        (∀ g : G,
          (∑ i : ι, if g ∈ A i then m i else 0) =
            ∑ i : ι, if g ∈ A i then n i else 0) →
        (∏ i : ι,
            letI : MulDistribMulAction (↥(A i)) M :=
              MulDistribMulAction.compHom M (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) M) ^ (m i * Nat.card (A i))) =
          ∏ i : ι,
            letI : MulDistribMulAction (↥(A i)) M :=
              MulDistribMulAction.compHom M (A i).subtype
            Nat.card (fixedPointSubgroup (↥(A i)) M) ^ (n i * Nat.card (A i))) :
    (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
  classical
  exact
    fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_of_minimal_invariant
      (G := G) (V := V) (ι := ι) hcop hsolv A m n hcoeff
      (by
        intro M _ _ _ hcopM hsolvM hminvM hcoeffM
        exact
          fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_minimal_of_elementaryAbelian
            (G := G) (V := M) (ι := ι) hcopM hsolvM A m n hcoeffM hminvM
            (fun {M} _ _ _ _ {p} _ _ hcopM hminvM hcoeffM =>
              helem (M := M) (p := p) hcopM hminvM hcoeffM))

/-- Product over conjugates of a complement, expressed for an explicit family of
compatible subgroup actions. -/
@[expose] public noncomputable def fixedPointSubgroup_conjBy_action_product
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (U E : Subgroup G)
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M) : ℕ :=
  let : Fintype U := Fintype.ofFinite U
  ∏ u : U,
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) ^
      Nat.card (E.conjBy (u : G))

/-- Unfold the conjugate fixed-point product without exposing the definition
body downstream. -/
public theorem fixedPointSubgroup_conjBy_action_product_eq_prod
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (U E : Subgroup G)
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M) :
    fixedPointSubgroup_conjBy_action_product U E hEact =
      letI : Fintype U := Fintype.ofFinite U
      ∏ u : U,
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) ^
          Nat.card (E.conjBy (u : G)) := by
  classical
  rfl

/-- Factor a conjugate fixed-point product when each conjugate fixed-point
cardinality factors. -/
public theorem fixedPointSubgroup_conjBy_action_product_factor
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (U E : Subgroup G)
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (cN cQ : U → ℕ)
    (hfactor : ∀ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) = cN u * cQ u) :
    letI : Fintype U := Fintype.ofFinite U
    fixedPointSubgroup_conjBy_action_product U E hEact =
      ∏ u : U, (cN u * cQ u) ^ Nat.card (E.conjBy (u : G)) := by
  classical
  let : Fintype U := Fintype.ofFinite U
  dsimp [fixedPointSubgroup_conjBy_action_product]
  apply Finset.prod_congr rfl
  intro u _hu
  rw [hfactor u]

/-- Lift the Frobenius fixed-point product identity from a normal subgroup and
the corresponding quotient, assuming all relevant cardinalities factor. -/
public theorem fixedPointSubgroup_action_product_identity_lift_from_card_factors
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (aN aQ bN bQ dN dQ : ℕ)
    (cN cQ : U → ℕ)
    (hUEfactor :
      Nat.card (fixedPointSubgroup (↥UE) M) = aN * aQ)
    (hMfactor : Nat.card M = bN * bQ)
    (hUfactor :
      Nat.card (fixedPointSubgroup (↥U) M) = dN * dQ)
    (hEfactor : ∀ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) = cN u * cQ u)
    (hN :
      letI : Fintype U := Fintype.ofFinite U
      aN ^ Nat.card UE * bN ^ Nat.card U =
        (∏ u : U, cN u ^ Nat.card (E.conjBy (u : G))) * dN ^ Nat.card U)
    (hQ :
      letI : Fintype U := Fintype.ofFinite U
      aQ ^ Nat.card UE * bQ ^ Nat.card U =
        (∏ u : U, cQ u ^ Nat.card (E.conjBy (u : G))) * dQ ^ Nat.card U) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      fixedPointSubgroup_conjBy_action_product U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  let : Fintype U := Fintype.ofFinite U
  have hlift :=
    fixedPointSubgroup_product_lift_card_factors
      (aN := aN) (aQ := aQ) (bN := bN) (bQ := bQ)
      (dN := dN) (dQ := dQ) (m := Nat.card UE) (n := Nat.card U)
      (cN := cN) (cQ := cQ)
      (e := fun u : U => Nat.card (E.conjBy (u : G))) hN hQ
  have hprod :=
    fixedPointSubgroup_conjBy_action_product_factor
      U E hEact cN cQ hEfactor
  rw [hUEfactor, hMfactor, hUfactor, hprod]
  exact hlift

/-- For the representation attached to an elementary-abelian action, the
invariant subspace for a subgroup is the additive form of the fixed-point
subgroup. -/
public noncomputable def fixedPointSubgroup_fixedSubspaceEquiv
    {A M : Type u} [Group A] [Group M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (H : Subgroup A) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
      Representation (ZMod p) A (Additive M)).fixedSubspace H) ≃
      Additive ↥(fixedPointSubgroup (↥H) M) := by
  let : CommGroup M := IsMulCommutative.instCommGroup
  refine
    { toFun := fun x =>
        Additive.ofMul ⟨Additive.toMul x.1, by
          rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
          intro h
          exact Additive.ofMul.injective (by
            change Additive.ofMul ((h : A) • Additive.toMul x.1) = x.1
            have hx := x.2 h
            change
              (Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
                Representation (ZMod p) A (Additive M)) (h : A) x.1 = x.1 at hx
            rw [Theory.Representation.ofElementaryAbelianAction_apply] at hx
            exact hx)⟩
      invFun := fun y =>
        ⟨Additive.ofMul ((Additive.toMul y : ↥(fixedPointSubgroup (↥H) M)) : M), by
          intro h
          let yH : fixedPointSubgroup (↥H) M := Additive.toMul y
          have hy := yH.2 h
          change (h : A) • (yH : M) = (yH : M) at hy
          change
            (Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
              Representation (ZMod p) A (Additive M)) (h : A) (Additive.ofMul (yH : M)) =
                Additive.ofMul (yH : M)
          rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
          exact congrArg Additive.ofMul hy⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl }

/-- Fixed-point subgroup cardinality as a prime power given by the fixed
subspace dimension of the associated elementary-abelian representation. -/
public theorem fixedPointSubgroup_card_eq_prime_pow_finrank
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M] :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    Nat.card (fixedPointSubgroup A M) =
      p ^ Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
          Representation (ZMod p) A (Additive M)).fixedSubspace
          (⊤ : Subgroup A)) := by
  classical
  let : CommGroup M := IsMulCommutative.instCommGroup
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p)
  have h_equiv : ↥(ρ.fixedSubspace (⊤ : Subgroup A)) ≃
      Additive ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M) :=
    fixedPointSubgroup_fixedSubspaceEquiv
      (A := A) (M := M) (p := p) (⊤ : Subgroup A)
  have h_top : fixedPointSubgroup (↥(⊤ : Subgroup A)) M = fixedPointSubgroup A M := by
    ext x
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    constructor
    · intro hx a
      exact hx ⟨a, by simp⟩
    · intro hx a
      change (a : A) • x = x
      exact hx (a : A)
  have h_add_card : Nat.card (Additive ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M)) =
      Nat.card (fixedPointSubgroup A M) := by
    calc
      Nat.card (Additive ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M)) =
          Nat.card ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M) := by
            exact Nat.card_congr
              { toFun := Additive.toMul
                invFun := Additive.ofMul
                left_inv := by intro x; rfl
                right_inv := by intro x; rfl }
      _ = Nat.card (fixedPointSubgroup A M) := by rw [h_top]
  have h_sub_card : Nat.card ↥(ρ.fixedSubspace (⊤ : Subgroup A)) =
      Nat.card (fixedPointSubgroup A M) := by
    calc
      Nat.card ↥(ρ.fixedSubspace (⊤ : Subgroup A)) =
          Nat.card (Additive ↥(fixedPointSubgroup (↥(⊤ : Subgroup A)) M)) :=
            Nat.card_congr h_equiv
      _ = Nat.card (fixedPointSubgroup A M) := h_add_card
  have hnat := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := ↥(ρ.fixedSubspace (⊤ : Subgroup A)))
  simpa [ρ, Nat.card_eq_fintype_card, ZMod.card, h_sub_card] using hnat

/-- Recover the fixed-subspace dimension from a fixed-point subgroup cardinality
written as a power of the elementary prime. -/
public theorem fixedSubspace_finrank_eq_of_fixedPointSubgroup_card_eq
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (n : ℕ)
    (hcard : Nat.card (fixedPointSubgroup A M) = p ^ n) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
          Representation (ZMod p) A (Additive M)).fixedSubspace
          (⊤ : Subgroup A)) = n := by
  let : CommGroup M := IsMulCommutative.instCommGroup
  apply Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt
  have hfixed :=
    fixedPointSubgroup_card_eq_prime_pow_finrank
      (A := A) (M := M) (p := p)
  exact hfixed.symm.trans hcard

/-- If an actor has only trivial fixed points, its associated fixed subspace has
dimension zero. -/
public theorem fixedSubspace_finrank_eq_zero_of_fixedPointSubgroup_eq_bot
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (hfix : fixedPointSubgroup A M = ⊥) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
          Representation (ZMod p) A (Additive M)).fixedSubspace
          (⊤ : Subgroup A)) = 0 := by
  let : CommGroup M := IsMulCommutative.instCommGroup
  apply fixedSubspace_finrank_eq_of_fixedPointSubgroup_card_eq
  simp [hfix]

/-- If an actor fixes everything, its associated fixed subspace has full
dimension. -/
public theorem fixedSubspace_finrank_eq_full_of_fixedPointSubgroup_eq_top
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (hfix : fixedPointSubgroup A M = ⊤) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
          Representation (ZMod p) A (Additive M)).fixedSubspace
          (⊤ : Subgroup A)) =
      Module.finrank (ZMod p) (Additive M) := by
  let : CommGroup M := IsMulCommutative.instCommGroup
  apply fixedSubspace_finrank_eq_of_fixedPointSubgroup_card_eq
  have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive M)
  have hMcard :
      Nat.card M = p ^ Module.finrank (ZMod p) (Additive M) := by
    calc
      Nat.card M = Nat.card (Additive M) := (Nat.card_congr Additive.toMul).symm
      _ = p ^ Module.finrank (ZMod p) (Additive M) := by
        simpa [ZMod.card] using hnat
  rw [hfix]
  simp [hMcard]

/-- Equal fixed-point subgroup cardinalities give equal fixed-subspace
dimensions for elementary-abelian actions. -/
public theorem fixedSubspace_finrank_eq_of_fixedPointSubgroup_nat_card_eq
    {A B M : Type u} [Group A] [Group B] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    [MulDistribMulAction A M] [MulDistribMulAction B M]
    (hcard : Nat.card (fixedPointSubgroup A M) =
      Nat.card (fixedPointSubgroup B M)) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
          Representation (ZMod p) A (Additive M)).fixedSubspace
          (⊤ : Subgroup A)) =
      Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := B) (G := M) (p := p) :
          Representation (ZMod p) B (Additive M)).fixedSubspace
          (⊤ : Subgroup B)) := by
  let : CommGroup M := IsMulCommutative.instCommGroup
  apply Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt
  calc
    p ^ Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
          Representation (ZMod p) A (Additive M)).fixedSubspace
          (⊤ : Subgroup A)) =
        Nat.card (fixedPointSubgroup A M) := by
          exact (fixedPointSubgroup_card_eq_prime_pow_finrank
            (A := A) (M := M) (p := p)).symm
    _ = Nat.card (fixedPointSubgroup B M) := hcard
    _ = p ^ Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := B) (G := M) (p := p) :
          Representation (ZMod p) B (Additive M)).fixedSubspace
          (⊤ : Subgroup B)) := by
          exact fixedPointSubgroup_card_eq_prime_pow_finrank
            (A := B) (M := M) (p := p)

/-- Convert a cardinality formula for fixed points into a dimension formula for
the associated fixed subspace. -/
public theorem full_finrank_eq_fixedSubspace_finrank_mul_of_fixedPoint_card_pow
    {A M : Type u} [Group A] [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [MulDistribMulAction A M]
    (n : ℕ)
    (hcard : Nat.card M = Nat.card (fixedPointSubgroup A M) ^ n) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    Module.finrank (ZMod p) (Additive M) =
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
            Representation (ZMod p) A (Additive M)).fixedSubspace
            (⊤ : Subgroup A)) * n := by
  let : CommGroup M := IsMulCommutative.instCommGroup
  apply Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt
  calc
    p ^ Module.finrank (ZMod p) (Additive M) = Nat.card M := by
      have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive M)
      calc
        p ^ Module.finrank (ZMod p) (Additive M) = Nat.card (Additive M) := by
          simpa [ZMod.card] using hnat.symm
        _ = Nat.card M := Nat.card_congr Additive.toMul
    _ = Nat.card (fixedPointSubgroup A M) ^ n := hcard
    _ = (p ^ Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
            Representation (ZMod p) A (Additive M)).fixedSubspace
            (⊤ : Subgroup A))) ^ n := by
          rw [fixedPointSubgroup_card_eq_prime_pow_finrank
            (A := A) (M := M) (p := p)]
    _ = p ^ (Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction (A := A) (G := M) (p := p) :
            Representation (ZMod p) A (Additive M)).fixedSubspace
            (⊤ : Subgroup A)) * n) := by
          rw [pow_mul]

/-- Fixed-subspace rank identity in the branch where the kernel fixes all of
the acted-on elementary-abelian group. -/
public theorem fixedSubspace_finrank_identity_kernel_fixed_top
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUtop : fixedPointSubgroup (↥U) M = ⊤) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p) :
          Representation (ZMod p) UE (Additive M)).fixedSubspace
          (⊤ : Subgroup UE)) * Nat.card UE +
      Module.finrank (ZMod p) (Additive M) * Nat.card U =
    (∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p) :
            Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G))) +
        Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p) :
            Representation (ZMod p) U (Additive M)).fixedSubspace
            (⊤ : Subgroup U)) * Nat.card U := by
    classical
    let : CommGroup M := IsMulCommutative.instCommGroup
    let : Fintype U := Fintype.ofFinite U
    let rUE : ℕ := Module.finrank (ZMod p)
      ↥((Theory.Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p) :
        Representation (ZMod p) UE (Additive M)).fixedSubspace
        (⊤ : Subgroup UE))
    let rM : ℕ := Module.finrank (ZMod p) (Additive M)
    let rU : ℕ := Module.finrank (ZMod p)
      ↥((Theory.Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p) :
        Representation (ZMod p) U (Additive M)).fixedSubspace
        (⊤ : Subgroup U))
    let rE : U → ℕ := fun u =>
      let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction
            (A := E.conjBy (u : G)) (G := M) (p := p) :
          Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
          (⊤ : Subgroup (E.conjBy (u : G))))
    have hUrank : rU = rM := by
      simpa [rU, rM] using
        (fixedSubspace_finrank_eq_full_of_fixedPointSubgroup_eq_top
          (A := U) (M := M) (p := p) hUtop)
    have hErank : ∀ u : U, rE u = rUE := by
      intro u
      let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      have hfix :
          fixedPointSubgroup (↥(E.conjBy (u : G))) M =
            fixedPointSubgroup (↥UE) M :=
        fixedPointSubgroup_conj_complement_eq_of_kernel_fixed_top
          (UE := UE) (U := U) (E := E) (M := M)
          hcomp u hUcompat (hEcompat u) hUtop
      have hcard :
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) =
            Nat.card (fixedPointSubgroup (↥UE) M) := by
        rw [hfix]
      simpa [rE, rUE] using
        (fixedSubspace_finrank_eq_of_fixedPointSubgroup_nat_card_eq
          (A := ↥(E.conjBy (u : G))) (B := ↥UE) (M := M) (p := p) hcard)
    have hEcard : ∀ u : U, Nat.card (E.conjBy (u : G)) = Nat.card E := by
      intro u
      exact natCard_conjBy_eq E (u : G)
    have hUEcard : Nat.card UE = Nat.card U * Nat.card E :=
      section12ComplementIn_nat_card_eq_mul UE U E hcomp hfrob
    have hsum :
        (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) =
          rUE * Nat.card UE := by
      calc
        (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) =
            ∑ _u : U, rUE * Nat.card E := by
              apply Finset.sum_congr rfl
              intro u _hu
              rw [hErank u, hEcard u]
        _ = Nat.card U * (rUE * Nat.card E) := by
              simp [Nat.card_eq_fintype_card]
        _ = rUE * Nat.card UE := by
              rw [hUEcard]
              ring
    have hmain :
        rUE * Nat.card UE + rM * Nat.card U =
          (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) + rU * Nat.card U := by
      rw [hsum, hUrank]
    simpa [rUE, rM, rU, rE] using hmain

/-- Convert a complement fixed-point cardinality identity into the corresponding
fixed-subspace rank identity. -/
public theorem fixedSubspace_complement_finrank_identity_of_card_identity
    {G M : Type u} [Group G] [Group M] [Finite M]
    (UE E : Subgroup G)
    [MulDistribMulAction UE M]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hcard :
      letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
        MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
      Nat.card M =
        Nat.card (fixedPointSubgroup (↥(E.subgroupOf UE)) M) ^ Nat.card E) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
      MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
    Module.finrank (ZMod p) (Additive M) =
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
            (A := E.subgroupOf UE) (G := M) (p := p) :
              Representation (ZMod p) (E.subgroupOf UE) (Additive M)).fixedSubspace
          (⊤ : Subgroup (E.subgroupOf UE))) *
        Nat.card E := by
  classical
  let : CommGroup M := IsMulCommutative.instCommGroup
  let : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
    MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
  exact
    full_finrank_eq_fixedSubspace_finrank_mul_of_fixedPoint_card_pow
      (A := E.subgroupOf UE) (M := M) (p := p) (n := Nat.card E) hcard

/-- Reduced fixed-subspace rank identity in the kernel-fixed-bot branch, once
the complement fixed-subspace rank identity is known. -/
public theorem fixedSubspace_finrank_identity_kernel_fixed_bot_reduced_of_complement_finrank
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hbase :
      letI : CommGroup M := IsMulCommutative.instCommGroup
      letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
        MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
      Module.finrank (ZMod p) (Additive M) =
        Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
              (A := E.subgroupOf UE) (G := M) (p := p) :
                Representation (ZMod p) (E.subgroupOf UE) (Additive M)).fixedSubspace
            (⊤ : Subgroup (E.subgroupOf UE))) *
          Nat.card E) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p) (Additive M) * Nat.card U =
    ∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p) :
                Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G)) := by
  classical
  let : CommGroup M := IsMulCommutative.instCommGroup
  let : Fintype U := Fintype.ofFinite U
  let : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
    MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
  let rM : ℕ := Module.finrank (ZMod p) (Additive M)
  let rE0 : ℕ := Module.finrank (ZMod p)
    ↥((Theory.Representation.ofElementaryAbelianAction
        (A := E.subgroupOf UE) (G := M) (p := p) :
          Representation (ZMod p) (E.subgroupOf UE) (Additive M)).fixedSubspace
      (⊤ : Subgroup (E.subgroupOf UE)))
  let rE : U → ℕ := fun u =>
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    Module.finrank (ZMod p)
      ↥((Theory.Representation.ofElementaryAbelianAction
          (A := E.conjBy (u : G)) (G := M) (p := p) :
            Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
        (⊤ : Subgroup (E.conjBy (u : G))))
  have hbase' : rM = rE0 * Nat.card E := by
    simpa [rM, rE0] using hbase
  have hErank : ∀ u : U, rE u = rE0 := by
    intro u
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    have hequiv :=
      fixedPointSubgroup_conj_complement_equiv
        (UE := UE) (U := U) (E := E) (M := M) hcomp u (hEcompat u)
    have hcard :
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) =
          Nat.card (fixedPointSubgroup (↥(E.subgroupOf UE)) M) :=
      Nat.card_congr hequiv.symm
    simpa [rE, rE0] using
      (fixedSubspace_finrank_eq_of_fixedPointSubgroup_nat_card_eq
        (A := ↥(E.conjBy (u : G))) (B := ↥(E.subgroupOf UE)) (M := M) (p := p)
        hcard)
  have hEcard : ∀ u : U, Nat.card (E.conjBy (u : G)) = Nat.card E := by
    intro u
    exact natCard_conjBy_eq E (u : G)
  have hsum :
      (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) =
        Nat.card U * (rE0 * Nat.card E) := by
    calc
      (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) =
          ∑ _u : U, rE0 * Nat.card E := by
            apply Finset.sum_congr rfl
            intro u _hu
            rw [hErank u, hEcard u]
      _ = Nat.card U * (rE0 * Nat.card E) := by
            simp [Nat.card_eq_fintype_card]
  have hmain :
      rM * Nat.card U =
        ∑ u : U, rE u * Nat.card (E.conjBy (u : G)) := by
    rw [hsum, hbase']
    ring
  simpa [rM, rE] using hmain

/-- Combine the two kernel fixed-point branches for the minimal invariant
elementary-abelian rank identity, assuming the kernel-fixed-bot branch has
already been supplied. -/
public theorem fixedSubspace_finrank_identity_minimal_invariant_of_kernel_fixed_bot_case
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant UE M N → N ≠ ⊥ → N = ⊤)
    (hbotRank :
      fixedPointSubgroup (↥U) M = ⊥ →
        letI : CommGroup M := IsMulCommutative.instCommGroup
        letI : Fintype U := Fintype.ofFinite U
        Module.finrank (ZMod p) (Additive M) * Nat.card U =
        ∑ u : U,
          letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
          Module.finrank (ZMod p)
              ↥((Theory.Representation.ofElementaryAbelianAction
                  (A := E.conjBy (u : G)) (G := M) (p := p) :
                    Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
                (⊤ : Subgroup (E.conjBy (u : G)))) *
            Nat.card (E.conjBy (u : G))) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p) :
          Representation (ZMod p) UE (Additive M)).fixedSubspace
          (⊤ : Subgroup UE)) * Nat.card UE +
      Module.finrank (ZMod p) (Additive M) * Nat.card U =
    (∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p) :
                Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G))) +
      Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p) :
          Representation (ZMod p) U (Additive M)).fixedSubspace
          (⊤ : Subgroup U)) * Nat.card U := by
  classical
  let : CommGroup M := IsMulCommutative.instCommGroup
  let : Fintype U := Fintype.ofFinite U
  have hUnorm : (U.subgroupOf UE).Normal := by
    have hUnormSup : (U.subgroupOf (U ⊔ E)).Normal :=
      IsFrobeniusGroupWithKernelComplement.normal hfrob
    have hUEeq : UE = U ⊔ E := hcomp.2.2.1
    subst UE
    simpa using hUnormSup
  have hUeq :
      fixedPointSubgroup (↥U) M =
        let : MulDistribMulAction (↥(U.subgroupOf UE)) M :=
          MulDistribMulAction.compHom M (U.subgroupOf UE).subtype
        fixedPointSubgroup (↥(U.subgroupOf UE)) M :=
    fixedPointSubgroup_eq_subgroupOf_of_compatible
      UE U hcomp.1 hUcompat
  have hUinv : IsInvariant UE M (fixedPointSubgroup (↥U) M) := by
    rw [hUeq]
    exact fixedPointSubgroup_invariant_of_normal (A := UE) (M := M)
      (U.subgroupOf UE)
  by_cases hUbot : fixedPointSubgroup (↥U) M = ⊥
  · have hUrank :
        Module.finrank (ZMod p)
            ↥((Theory.Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p) :
              Representation (ZMod p) U (Additive M)).fixedSubspace
              (⊤ : Subgroup U)) = 0 := by
      simpa using
        (fixedSubspace_finrank_eq_zero_of_fixedPointSubgroup_eq_bot
          (A := U) (M := M) (p := p) hUbot)
    have hUEbot : fixedPointSubgroup (↥UE) M = ⊥ :=
      fixedPointSubgroup_eq_bot_of_fixedPointSubgroup_subgroup_eq_bot
        (UE := UE) (U := U) hcomp.1 hUcompat hUbot
    have hUErank :
        Module.finrank (ZMod p)
            ↥((Theory.Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p) :
              Representation (ZMod p) UE (Additive M)).fixedSubspace
              (⊤ : Subgroup UE)) = 0 := by
      simpa using
        (fixedSubspace_finrank_eq_zero_of_fixedPointSubgroup_eq_bot
          (A := UE) (M := M) (p := p) hUEbot)
    have hcore := hbotRank hUbot
    rw [hUErank, hUrank]
    simpa using hcore
  · have hUtop : fixedPointSubgroup (↥U) M = ⊤ :=
      hminv (fixedPointSubgroup (↥U) M) inferInstance hUinv hUbot
    exact
      fixedSubspace_finrank_identity_kernel_fixed_top
        (p := p) UE U E hEact hcomp hfrob hUcompat hEcompat hUtop

/-- A prime-power product identity follows from equality of the exponents. -/
public theorem prime_power_product_identity_of_exponent_sum
    {ι : Type*} [Fintype ι]
    (p a b d m n : ℕ) (c e : ι → ℕ)
    (h : a * m + b * n = (∑ i : ι, c i * e i) + d * n) :
    (p ^ a) ^ m * (p ^ b) ^ n =
      (∏ i : ι, (p ^ c i) ^ e i) * (p ^ d) ^ n := by
  classical
  have hprod : (∏ i : ι, (p ^ c i) ^ e i) = p ^ (∑ i : ι, c i * e i) := by
    calc
      (∏ i : ι, (p ^ c i) ^ e i) = ∏ i : ι, p ^ (c i * e i) := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [pow_mul]
      _ = p ^ (∑ i : ι, c i * e i) := by
        simpa using
          (Finset.prod_pow_eq_pow_sum (Finset.univ) (fun i : ι => c i * e i) p)
  calc
    (p ^ a) ^ m * (p ^ b) ^ n = p ^ (a * m) * p ^ (b * n) := by
      rw [pow_mul, pow_mul]
    _ = p ^ (a * m + b * n) := by rw [← Nat.pow_add]
    _ = p ^ ((∑ i : ι, c i * e i) + d * n) := by rw [h]
    _ = p ^ (∑ i : ι, c i * e i) * p ^ (d * n) := by rw [Nat.pow_add]
    _ = (∏ i : ι, (p ^ c i) ^ e i) * (p ^ d) ^ n := by rw [hprod, pow_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Turn a fixed-subspace dimension identity for an elementary-abelian action
into the corresponding fixed-point cardinality product identity. -/
public theorem fixedPointSubgroup_product_identity_action_elementaryAbelian_of_finrank_identity
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hrank :
      letI : CommGroup M := IsMulCommutative.instCommGroup
      letI : Fintype U := Fintype.ofFinite U
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p) :
            Representation (ZMod p) UE (Additive M)).fixedSubspace
            (⊤ : Subgroup UE)) * Nat.card UE +
        Module.finrank (ZMod p) (Additive M) * Nat.card U =
      (∑ u : U,
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        Module.finrank (ZMod p)
            ↥((Theory.Representation.ofElementaryAbelianAction
                (A := E.conjBy (u : G)) (G := M) (p := p) :
                  Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
              (⊤ : Subgroup (E.conjBy (u : G)))) *
          Nat.card (E.conjBy (u : G))) +
        Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p) :
            Representation (ZMod p) U (Additive M)).fixedSubspace
            (⊤ : Subgroup U)) * Nat.card U) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      fixedPointSubgroup_conjBy_action_product U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  let : CommGroup M := IsMulCommutative.instCommGroup
  let : Fintype U := Fintype.ofFinite U
  let rUE : ℕ := Module.finrank (ZMod p)
    ↥((Theory.Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p) :
      Representation (ZMod p) UE (Additive M)).fixedSubspace
      (⊤ : Subgroup UE))
  let rM : ℕ := Module.finrank (ZMod p) (Additive M)
  let rU : ℕ := Module.finrank (ZMod p)
    ↥((Theory.Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p) :
      Representation (ZMod p) U (Additive M)).fixedSubspace
      (⊤ : Subgroup U))
  let rE : U → ℕ := fun u =>
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    Module.finrank (ZMod p)
      ↥((Theory.Representation.ofElementaryAbelianAction
          (A := E.conjBy (u : G)) (G := M) (p := p) :
            Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
        (⊤ : Subgroup (E.conjBy (u : G))))
  have hUEcard : Nat.card (fixedPointSubgroup (↥UE) M) = p ^ rUE := by
    simpa [rUE] using
      (fixedPointSubgroup_card_eq_prime_pow_finrank
        (A := UE) (M := M) (p := p))
  have hMcard : Nat.card M = p ^ rM := by
    have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive M)
    calc
      Nat.card M = Nat.card (Additive M) := (Nat.card_congr Additive.toMul).symm
      _ = p ^ rM := by simpa [rM, ZMod.card] using hnat
  have hUcard : Nat.card (fixedPointSubgroup (↥U) M) = p ^ rU := by
    simpa [rU] using
      (fixedPointSubgroup_card_eq_prime_pow_finrank
        (A := U) (M := M) (p := p))
  have hEcard : ∀ u : U,
      let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) = p ^ rE u := by
    intro u
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    simpa [rE] using
      (fixedPointSubgroup_card_eq_prime_pow_finrank
        (A := E.conjBy (u : G)) (M := M) (p := p))
  have hprod : fixedPointSubgroup_conjBy_action_product U E hEact =
      ∏ u : U, (p ^ rE u) ^ Nat.card (E.conjBy (u : G)) := by
    dsimp [fixedPointSubgroup_conjBy_action_product]
    apply Finset.prod_congr rfl
    intro u _hu
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    rw [hEcard u]
  have hrank' : rUE * Nat.card UE + rM * Nat.card U =
      (∑ u : U, rE u * Nat.card (E.conjBy (u : G))) + rU * Nat.card U := by
    simpa [rUE, rM, rU, rE] using hrank
  rw [hUEcard, hMcard, hUcard, hprod]
  exact
    prime_power_product_identity_of_exponent_sum
      (p := p) (a := rUE) (b := rM) (d := rU)
      (m := Nat.card UE) (n := Nat.card U)
      (c := rE) (e := fun u : U => Nat.card (E.conjBy (u : G))) hrank'

/-- Lift the explicit Frobenius-action fixed-point product identity from an
invariant normal subgroup and the corresponding quotient. -/
public theorem fixedPointSubgroup_product_identity_action_lift_from_invariant_normal
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hsolvM : Group.IsSolvable M)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    {N : Subgroup M} [N.Normal]
    (hUEinv : IsInvariant UE M N)
    (hN :
      let hUinv : IsInvariant U M N :=
        isInvariant_of_compatible_le_actor UE U hcomp.1 hUcompat hUEinv
      letI : IsInvariant U M N := hUinv
      let hEuinv : ∀ u : U, IsInvariant (E.conjBy (u : G)) M N := fun u =>
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        isInvariant_of_compatible_le_actor UE (E.conjBy (u : G))
          (section12ComplementIn_conj_complement_le UE U E hcomp u)
          (hEcompat u) hUEinv
      let hEactN : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) N := fun u => by
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
        infer_instance
      letI : Fintype U := Fintype.ofFinite U
      Nat.card (fixedPointSubgroup (↥UE) N) ^ Nat.card UE *
          Nat.card N ^ Nat.card U =
        fixedPointSubgroup_conjBy_action_product U E hEactN *
          Nat.card (fixedPointSubgroup (↥U) N) ^ Nat.card U)
    (hQ :
      letI : IsInvariant UE M N := hUEinv
      letI : MulDistribMulAction UE (M ⧸ N) :=
        quotientMulDistribMulAction (A := UE) (G := M) N hUEinv
      let hUinv : IsInvariant U M N :=
        isInvariant_of_compatible_le_actor UE U hcomp.1 hUcompat hUEinv
      letI : IsInvariant U M N := hUinv
      letI : MulDistribMulAction U (M ⧸ N) :=
        quotientMulDistribMulAction (A := U) (G := M) N hUinv
      let hEuinv : ∀ u : U, IsInvariant (E.conjBy (u : G)) M N := fun u =>
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        isInvariant_of_compatible_le_actor UE (E.conjBy (u : G))
          (section12ComplementIn_conj_complement_le UE U E hcomp u)
          (hEcompat u) hUEinv
      let hEactQ : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) (M ⧸ N) := fun u => by
        letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        letI : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
        exact quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := M) N (hEuinv u)
      letI : Fintype U := Fintype.ofFinite U
      Nat.card (fixedPointSubgroup (↥UE) (M ⧸ N)) ^ Nat.card UE *
          Nat.card (M ⧸ N) ^ Nat.card U =
        fixedPointSubgroup_conjBy_action_product U E hEactQ *
          Nat.card (fixedPointSubgroup (↥U) (M ⧸ N)) ^ Nat.card U) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      fixedPointSubgroup_conjBy_action_product U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  let : Fintype U := Fintype.ofFinite U
  let : IsInvariant UE M N := hUEinv
  let : MulDistribMulAction UE (M ⧸ N) :=
    quotientMulDistribMulAction (A := UE) (G := M) N hUEinv
  let hUinv : IsInvariant U M N :=
    isInvariant_of_compatible_le_actor UE U hcomp.1 hUcompat hUEinv
  let : IsInvariant U M N := hUinv
  let : MulDistribMulAction U (M ⧸ N) :=
    quotientMulDistribMulAction (A := U) (G := M) N hUinv
  let hEuinv : ∀ u : U, IsInvariant (E.conjBy (u : G)) M N := fun u =>
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    isInvariant_of_compatible_le_actor UE (E.conjBy (u : G))
      (section12ComplementIn_conj_complement_le UE U E hcomp u)
      (hEcompat u) hUEinv
  let hEactN : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) N := fun u => by
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    let : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
    infer_instance
  let hEactQ : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) (M ⧸ N) := fun u => by
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    let : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
    exact quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := M) N (hEuinv u)
  have hUEfactor :
      Nat.card (fixedPointSubgroup (↥UE) M) =
        Nat.card (fixedPointSubgroup (↥UE) N) *
          Nat.card (fixedPointSubgroup (↥UE) (M ⧸ N)) :=
    fixedPointSubgroup_card_eq_mul_quotient_action
      (A := UE) (M := M) (N := N) hUEinv hsolvM hcop.symm
  have hMfactor : Nat.card M = Nat.card N * Nat.card (M ⧸ N) := by
    simpa [Nat.mul_comm] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := M) (s := N))
  have hcopU : Nat.Coprime (Nat.card U) (Nat.card M) := by
    exact Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hcomp.1) hcop.symm
  have hUfactor :
      Nat.card (fixedPointSubgroup (↥U) M) =
        Nat.card (fixedPointSubgroup (↥U) N) *
          Nat.card (fixedPointSubgroup (↥U) (M ⧸ N)) :=
    fixedPointSubgroup_card_eq_mul_quotient_action
      (A := U) (M := M) (N := N) hUinv hsolvM hcopU
  have hEfactor : ∀ u : U,
      let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) =
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N) *
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (M ⧸ N)) := by
    intro u
    let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
    let : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
    let : MulDistribMulAction (E.conjBy (u : G)) (M ⧸ N) := hEactQ u
    have hcopEu : Nat.Coprime (Nat.card (E.conjBy (u : G))) (Nat.card M) := by
      exact Nat.Coprime.of_dvd_left
        (Subgroup.card_dvd_of_le
          (section12ComplementIn_conj_complement_le UE U E hcomp u))
        hcop.symm
    exact
      fixedPointSubgroup_card_eq_mul_quotient_action
        (A := E.conjBy (u : G)) (M := M) (N := N) (hEuinv u) hsolvM hcopEu
  have hNprod :
      Nat.card (fixedPointSubgroup (↥UE) N) ^ Nat.card UE * Nat.card N ^ Nat.card U =
        (∏ u : U,
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N) ^
            Nat.card (E.conjBy (u : G))) *
          Nat.card (fixedPointSubgroup (↥U) N) ^ Nat.card U := by
    simpa [fixedPointSubgroup_conjBy_action_product, hEactN] using hN
  have hQprod :
      Nat.card (fixedPointSubgroup (↥UE) (M ⧸ N)) ^ Nat.card UE *
          Nat.card (M ⧸ N) ^ Nat.card U =
        (∏ u : U,
          Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (M ⧸ N)) ^
            Nat.card (E.conjBy (u : G))) *
          Nat.card (fixedPointSubgroup (↥U) (M ⧸ N)) ^ Nat.card U := by
    simpa [fixedPointSubgroup_conjBy_action_product, hEactQ] using hQ
  exact
    fixedPointSubgroup_action_product_identity_lift_from_card_factors
      UE U E hEact
      (aN := Nat.card (fixedPointSubgroup (↥UE) N))
      (aQ := Nat.card (fixedPointSubgroup (↥UE) (M ⧸ N)))
      (bN := Nat.card N)
      (bQ := Nat.card (M ⧸ N))
      (dN := Nat.card (fixedPointSubgroup (↥U) N))
      (dQ := Nat.card (fixedPointSubgroup (↥U) (M ⧸ N)))
      (cN := fun u : U =>
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        let : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) N))
      (cQ := fun u : U =>
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        let : IsInvariant (E.conjBy (u : G)) M N := hEuinv u
        let : MulDistribMulAction (E.conjBy (u : G)) (M ⧸ N) := hEactQ u
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) (M ⧸ N)))
      hUEfactor hMfactor hUfactor hEfactor hNprod hQprod

/-- Chief-factor product identity from the nontrivial elementary-abelian
minimal case. The only mathematical branch supplied externally is the
elementary-abelian case; the subsingleton case is formal. -/
public theorem fixedPointSubgroup_product_identity_action_chiefFactor_of_elementaryAbelian
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hsolvM : Group.IsSolvable M)
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant UE M N → N ≠ ⊥ → N = ⊤)
    (hElemCase :
      ∀ {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M] [Nontrivial M],
        letI : Fintype U := Fintype.ofFinite U
        Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
            Nat.card M ^ Nat.card U =
          fixedPointSubgroup_conjBy_action_product U E hEact *
            Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      fixedPointSubgroup_conjBy_action_product U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  rcases chiefFactor_elementaryAbelian_or_subsingleton
      (A := UE) (M := M) hsolvM hminv with hsub | ⟨hNontriv, p, hp, hElem⟩
  · let : Subsingleton M := hsub
    have hMcard : Nat.card M = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hUEcard : Nat.card (fixedPointSubgroup (↥UE) M) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hUcard : Nat.card (fixedPointSubgroup (↥U) M) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hEcard : ∀ u : U,
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) = 1 := by
      intro u
      let : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    dsimp [fixedPointSubgroup_conjBy_action_product]
    rw [hUEcard, hMcard, hUcard]
    let : Fintype U := Fintype.ofFinite U
    have hprod : (∏ u : U,
        Nat.card (fixedPointSubgroup (↥(E.conjBy (u : G))) M) ^
          Nat.card (E.conjBy (u : G))) = 1 := by
      refine Finset.prod_eq_one ?_
      intro u _hu
      rw [hEcard u]
      simp
    rw [hprod]
    simp
  · let : Fact p.Prime := ⟨hp⟩
    let : Nontrivial M := hNontriv
    let : IsElementaryAbelian p M := hElem
    exact hElemCase (p := p)

/-- Solvable fixed-point product identity from the chief-factor case, by
induction on the acted-on group cardinality. -/
public theorem fixedPointSubgroup_product_identity_action_of_chiefFactor
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hsolvM : Group.IsSolvable M)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    (hchief :
      ∀ (M' : Type u) [Group M'] [Finite M']
        [MulDistribMulAction UE M'] [MulDistribMulAction U M']
        (hEact' : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M'),
        Group.IsSolvable M' →
        Nat.Coprime (Nat.card M') (Nat.card UE) →
        (∀ (u : U) (m : M'),
          u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m) →
        (∀ (u : U) (e : E.conjBy (u : G)) (m : M'),
          letI : MulDistribMulAction (↥(E.conjBy (u : G))) M' := hEact' u
          e • m =
            (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
              UE) • m) →
        (∀ N : Subgroup M', N.Normal → IsInvariant UE M' N → N ≠ ⊥ → N = ⊤) →
        letI : Fintype U := Fintype.ofFinite U
        Nat.card (fixedPointSubgroup (↥UE) M') ^ Nat.card UE *
            Nat.card M' ^ Nat.card U =
          fixedPointSubgroup_conjBy_action_product U E hEact' *
            Nat.card (fixedPointSubgroup (↥U) M') ^ Nat.card U) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      fixedPointSubgroup_conjBy_action_product U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (M' : Type u) [Group M'] [Finite M']
      [MulDistribMulAction UE M'] [MulDistribMulAction U M']
      (hEact' : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M'),
      Nat.card M' = n →
      Group.IsSolvable M' →
      Nat.Coprime (Nat.card M') (Nat.card UE) →
      (∀ (u : U) (m : M'),
        u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m) →
      (∀ (u : U) (e : E.conjBy (u : G)) (m : M'),
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M' := hEact' u
        e • m =
          (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
            UE) • m) →
      let : Fintype U := Fintype.ofFinite U
      Nat.card (fixedPointSubgroup (↥UE) M') ^ Nat.card UE *
          Nat.card M' ^ Nat.card U =
        fixedPointSubgroup_conjBy_action_product U E hEact' *
          Nat.card (fixedPointSubgroup (↥U) M') ^ Nat.card U
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih M' _ _ _ _ hEact' hn hsolvM' hcop' hUcompat' hEcompat'
    by_cases hminv :
        ∀ N : Subgroup M', N.Normal → IsInvariant UE M' N → N ≠ ⊥ → N = ⊤
    · exact hchief M' hEact' hsolvM' hcop' hUcompat' hEcompat' hminv
    · push Not at hminv
      rcases hminv with ⟨N, hNnormal, hNinv, hNne_bot, hNne_top⟩
      let : N.Normal := hNnormal
      let : IsInvariant UE M' N := hNinv
      let : MulDistribMulAction UE (M' ⧸ N) :=
        quotientMulDistribMulAction (A := UE) (G := M') N hNinv
      let hUinv : IsInvariant U M' N :=
        isInvariant_of_compatible_le_actor UE U hcomp.1 hUcompat' hNinv
      let : IsInvariant U M' N := hUinv
      let : MulDistribMulAction U (M' ⧸ N) :=
        quotientMulDistribMulAction (A := U) (G := M') N hUinv
      let hEuinv : ∀ u : U, IsInvariant (E.conjBy (u : G)) M' N := fun u =>
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M' := hEact' u
        isInvariant_of_compatible_le_actor UE (E.conjBy (u : G))
          (section12ComplementIn_conj_complement_le UE U E hcomp u)
          (hEcompat' u) hNinv
      let hEactN : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) N := fun u => by
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M' := hEact' u
        let : IsInvariant (E.conjBy (u : G)) M' N := hEuinv u
        infer_instance
      let hEactQ : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) (M' ⧸ N) := fun u => by
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M' := hEact' u
        let : IsInvariant (E.conjBy (u : G)) M' N := hEuinv u
        exact quotientMulDistribMulAction (A := E.conjBy (u : G)) (G := M') N (hEuinv u)
      have hNlt : Nat.card N < n := by
        have hN_lt_top : N < ⊤ := lt_top_iff_ne_top.mpr hNne_top
        have hlt : Nat.card N < Nat.card M' := by
          simpa using natCard_lt_of_subgroup_lt hN_lt_top
        simpa [hn] using hlt
      have hQlt : Nat.card (M' ⧸ N) < n := by
        have hlt := natCard_quotient_lt_natCard_of_ne_bot N hNne_bot
        simpa [hn] using hlt
      have hsolvN : Group.IsSolvable N := by
        let : Group.IsSolvable M' := hsolvM'
        infer_instance
      have hsolvQ : Group.IsSolvable (M' ⧸ N) := by
        let : Group.IsSolvable M' := hsolvM'
        infer_instance
      have hcopN : Nat.Coprime (Nat.card N) (Nat.card UE) := by
        exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card N) hcop'
      have hcopQ : Nat.Coprime (Nat.card (M' ⧸ N)) (Nat.card UE) := by
        exact Nat.Coprime.of_dvd_left (Subgroup.card_quotient_dvd_card (s := N)) hcop'
      have hUcompatN : ∀ (u : U) (m : N),
          u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m := by
        intro u m
        apply Subtype.ext
        change (u • (m : M') : M') =
          ((⟨(u : G), hcomp.1 u.2⟩ : UE) • (m : M') : M')
        exact hUcompat' u (m : M')
      have hEcompatN : ∀ (u : U) (e : E.conjBy (u : G)) (m : N),
          let : MulDistribMulAction (↥(E.conjBy (u : G))) N := hEactN u
          e • m =
            (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
              UE) • m := by
        intro u e m
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M' := hEact' u
        let : IsInvariant (E.conjBy (u : G)) M' N := hEuinv u
        apply Subtype.ext
        change (e • (m : M') : M') =
          ((⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
            UE) • (m : M') : M')
        exact hEcompat' u e (m : M')
      have hUcompatQ : ∀ (u : U) (q : M' ⧸ N),
          u • q = (⟨(u : G), hcomp.1 u.2⟩ : UE) • q := by
        intro u q
        refine QuotientGroup.induction_on q ?_
        intro m
        calc
          u • ((m : M') : M' ⧸ N) = ((u • m : M') : M' ⧸ N) := by
            exact MulAction.Quotient.smul_coe (X := U) (H := N) (b := u) (g := m)
          _ = (((⟨(u : G), hcomp.1 u.2⟩ : UE) • m : M') : M' ⧸ N) := by
            rw [hUcompat' u m]
          _ = (⟨(u : G), hcomp.1 u.2⟩ : UE) • ((m : M') : M' ⧸ N) := by
            exact (MulAction.Quotient.smul_coe (X := UE) (H := N)
              (b := (⟨(u : G), hcomp.1 u.2⟩ : UE)) (g := m)).symm
      have hEcompatQ : ∀ (u : U) (e : E.conjBy (u : G)) (q : M' ⧸ N),
          let : MulDistribMulAction (↥(E.conjBy (u : G))) (M' ⧸ N) := hEactQ u
          e • q =
            (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
              UE) • q := by
        intro u e q
        let : MulDistribMulAction (↥(E.conjBy (u : G))) M' := hEact' u
        let : IsInvariant (E.conjBy (u : G)) M' N := hEuinv u
        let : MulDistribMulAction (↥(E.conjBy (u : G))) (M' ⧸ N) := hEactQ u
        refine QuotientGroup.induction_on q ?_
        intro m
        calc
          e • ((m : M') : M' ⧸ N) = ((e • m : M') : M' ⧸ N) := by
            exact MulAction.Quotient.smul_coe
              (X := E.conjBy (u : G)) (H := N) (b := e) (g := m)
          _ = (((⟨(e : G),
                section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
                UE) • m : M') : M' ⧸ N) := by
            rw [hEcompat' u e m]
          _ = (⟨(e : G),
                section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
                UE) • ((m : M') : M' ⧸ N) := by
            exact (MulAction.Quotient.smul_coe (X := UE) (H := N)
              (b := (⟨(e : G),
                section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ : UE))
              (g := m)).symm
      have hNid :
          let : Fintype U := Fintype.ofFinite U
          Nat.card (fixedPointSubgroup (↥UE) N) ^ Nat.card UE *
              Nat.card N ^ Nat.card U =
            fixedPointSubgroup_conjBy_action_product U E hEactN *
              Nat.card (fixedPointSubgroup (↥U) N) ^ Nat.card U := by
        exact ih (Nat.card N) hNlt N hEactN rfl hsolvN hcopN hUcompatN hEcompatN
      have hQid :
          let : Fintype U := Fintype.ofFinite U
          Nat.card (fixedPointSubgroup (↥UE) (M' ⧸ N)) ^ Nat.card UE *
              Nat.card (M' ⧸ N) ^ Nat.card U =
            fixedPointSubgroup_conjBy_action_product U E hEactQ *
              Nat.card (fixedPointSubgroup (↥U) (M' ⧸ N)) ^ Nat.card U := by
        exact ih (Nat.card (M' ⧸ N)) hQlt (M' ⧸ N) hEactQ rfl
          hsolvQ hcopQ hUcompatQ hEcompatQ
      exact
        fixedPointSubgroup_product_identity_action_lift_from_invariant_normal
          UE U E hEact' hcomp hsolvM' hcop' hUcompat' hEcompat'
          (N := N) hNinv hNid hQid
  exact hP (Nat.card M) M hEact rfl hsolvM hcop hUcompat hEcompat

/-- Products of prime powers are equal when their summed exponents are equal. -/
public theorem prime_power_product_eq_of_sum_eq
    {ι : Type*} [Fintype ι]
    (p : ℕ) (r eL eR : ι → ℕ)
    (h : (∑ i : ι, r i * eL i) = ∑ i : ι, r i * eR i) :
    (∏ i : ι, (p ^ r i) ^ eL i) =
      ∏ i : ι, (p ^ r i) ^ eR i := by
  classical
  have hL : (∏ i : ι, (p ^ r i) ^ eL i) = p ^ (∑ i : ι, r i * eL i) := by
    calc
      (∏ i : ι, (p ^ r i) ^ eL i) = ∏ i : ι, p ^ (r i * eL i) := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [pow_mul]
      _ = p ^ (∑ i : ι, r i * eL i) := by
        simpa using
          (Finset.prod_pow_eq_pow_sum (Finset.univ) (fun i : ι => r i * eL i) p)
  have hR : (∏ i : ι, (p ^ r i) ^ eR i) = p ^ (∑ i : ι, r i * eR i) := by
    calc
      (∏ i : ι, (p ^ r i) ^ eR i) = ∏ i : ι, p ^ (r i * eR i) := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [pow_mul]
      _ = p ^ (∑ i : ι, r i * eR i) := by
        simpa using
          (Finset.prod_pow_eq_pow_sum (Finset.univ) (fun i : ι => r i * eR i) p)
  rw [hL, hR, h]

/-- Turn a fixed-subspace dimension identity for an elementary-abelian action
into the broad Wielandt fixed-point product identity. -/
public theorem fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_elementaryAbelian_of_finrank_sum_eq
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι]
    (A : ι → Subgroup G)
    (m n : ι → ℕ)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hrank :
      letI : CommGroup V := IsMulCommutative.instCommGroup
      (∑ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Module.finrank (ZMod p)
            ↥((Theory.Representation.ofElementaryAbelianAction
                (A := ↥(A i)) (G := V) (p := p) :
                  Representation (ZMod p) (↥(A i)) (Additive V)).fixedSubspace
              (⊤ : Subgroup (↥(A i)))) *
          (m i * Nat.card (A i))) =
      ∑ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Module.finrank (ZMod p)
            ↥((Theory.Representation.ofElementaryAbelianAction
                (A := ↥(A i)) (G := V) (p := p) :
                  Representation (ZMod p) (↥(A i)) (Additive V)).fixedSubspace
              (⊤ : Subgroup (↥(A i)))) *
          (n i * Nat.card (A i))) :
    (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
  classical
  let : CommGroup V := IsMulCommutative.instCommGroup
  let r : ι → ℕ := fun i =>
    let : MulDistribMulAction (↥(A i)) V :=
      MulDistribMulAction.compHom V (A i).subtype
    Module.finrank (ZMod p)
      ↥((Theory.Representation.ofElementaryAbelianAction
          (A := ↥(A i)) (G := V) (p := p) :
            Representation (ZMod p) (↥(A i)) (Additive V)).fixedSubspace
        (⊤ : Subgroup (↥(A i))))
  let eL : ι → ℕ := fun i => m i * Nat.card (A i)
  let eR : ι → ℕ := fun i => n i * Nat.card (A i)
  have hcard : ∀ i : ι,
      let : MulDistribMulAction (↥(A i)) V :=
        MulDistribMulAction.compHom V (A i).subtype
      Nat.card (fixedPointSubgroup (↥(A i)) V) = p ^ r i := by
    intro i
    let : MulDistribMulAction (↥(A i)) V :=
      MulDistribMulAction.compHom V (A i).subtype
    simpa [r] using
      (fixedPointSubgroup_card_eq_prime_pow_finrank
        (A := ↥(A i)) (M := V) (p := p))
  have hrank' : (∑ i : ι, r i * eL i) = ∑ i : ι, r i * eR i := by
    simpa [r, eL, eR] using hrank
  calc
    (∏ i : ι,
        let : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
        ∏ i : ι, (p ^ r i) ^ eL i := by
          apply Finset.prod_congr rfl
          intro i _hi
          let : MulDistribMulAction (↥(A i)) V :=
            MulDistribMulAction.compHom V (A i).subtype
          exact congrArg (fun c : ℕ => c ^ eL i) (hcard i)
    _ = ∏ i : ι, (p ^ r i) ^ eR i :=
          prime_power_product_eq_of_sum_eq p r eL eR hrank'
    _ = ∏ i : ι,
        let : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
          symm
          apply Finset.prod_congr rfl
          intro i _hi
          let : MulDistribMulAction (↥(A i)) V :=
            MulDistribMulAction.compHom V (A i).subtype
          have hci := hcard i
          dsimp only at hci ⊢
          rw [hci]


public theorem nat_eq_of_modEq_prime_power_all {p x y : ℕ}
    (hp : 1 < p)
    (hmod : ∀ e : ℕ, x ≡ y [MOD p ^ e]) :
    x = y := by
  let e := max x y
  have hx_lt : x < p ^ e :=
    lt_of_le_of_lt (le_max_left x y) (Nat.lt_pow_self hp)
  have hy_lt : y < p ^ e :=
    lt_of_le_of_lt (le_max_right x y) (Nat.lt_pow_self hp)
  have hx_mod : x % (p ^ e) = x := Nat.mod_eq_of_lt hx_lt
  have hy_mod : y % (p ^ e) = y := Nat.mod_eq_of_lt hy_lt
  have hxy_mod : x % (p ^ e) = y % (p ^ e) := hmod e
  rw [hx_mod, hy_mod] at hxy_mod
  exact hxy_mod

/-- Convert subgroup trace-sum formulae in `ZMod q` into the natural
prime-power congruence used in Wielandt's argument. -/
public theorem subgroup_weighted_sum_nat_modEq_of_coeff_sum_eq
    {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (m n r : ι → ℕ)
    (q : ℕ)
    (F : G → ZMod q)
    (hcoeff : ∀ g : G,
      (∑ i : ι, if g ∈ A i then m i else 0) =
        ∑ i : ι, if g ∈ A i then n i else 0)
    (htrace : ∀ i : ι,
      (∑ a : A i, F (a : G)) = (r i * Nat.card (A i) : ZMod q)) :
    (∑ i : ι, r i * (m i * Nat.card (A i))) ≡
      (∑ i : ι, r i * (n i * Nat.card (A i))) [MOD q] := by
  classical
  have hweighted :=
    subgroup_weighted_sum_eq_of_coeff_sum_eq
      (A := A) (m := m) (n := n) (F := F) hcoeff
  have hleft :
      (∑ i : ι, ((r i * (m i * Nat.card (A i)) : ℕ) : ZMod q)) =
        ∑ i : ι, m i • ∑ a : A i, F (a : G) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [htrace i, nsmul_eq_mul]
    norm_num
    ring
  have hright :
      (∑ i : ι, n i • ∑ a : A i, F (a : G)) =
        ∑ i : ι, ((r i * (n i * Nat.card (A i)) : ℕ) : ZMod q) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [htrace i, nsmul_eq_mul]
    norm_num
    ring
  have hcast :
      (∑ i : ι, ((r i * (m i * Nat.card (A i)) : ℕ) : ZMod q)) =
        ∑ i : ι, ((r i * (n i * Nat.card (A i)) : ℕ) : ZMod q) :=
    hleft.trans (hweighted.trans hright)
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
    simpa [Nat.cast_sum] using hcast)


end CFSG.Wielandt
