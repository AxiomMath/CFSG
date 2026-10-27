module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H1
public import Mathlib.GroupTheory.Complement

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

/-!
# Reconstruction coordinates for Peterfalvi, Part II, Chapter IV, Section 1

The point fixed by `M` is represented by `none`; the remaining points are
represented by `x : Q` through `x⁻¹ • (t • a)`, as in the textbook's
identification of `X` with `Q ∪ {a}`.
-/

@[expose] public def rankOneCoordinate
    {L X : Type*} [Group L] [MulAction L X]
    (Q : Subgroup L) (t : L) (a : X) : Option Q → X
  | none => a
  | some x => (x : L)⁻¹ • (t • a)

@[simp] public theorem rankOneCoordinate_none
    {L X : Type*} [Group L] [MulAction L X]
    (Q : Subgroup L) (t : L) (a : X) :
    rankOneCoordinate Q t a none = a := rfl

@[simp] public theorem rankOneCoordinate_some
    {L X : Type*} [Group L] [MulAction L X]
    (Q : Subgroup L) (t : L) (a : X) (x : Q) :
    rankOneCoordinate Q t a (some x) = (x : L)⁻¹ • (t • a) := rfl

private theorem rankOne_QD_decomposition
    {L : Type*} [Group L] (M Q D : Subgroup L)
    (hQ_le_M : Q ≤ M) (hD_le_M : D ≤ M)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M) :
    ∀ m : M, ∃ q : Q.subgroupOf M, ∃ d : D.subgroupOf M,
      (q : M) * (d : M) = m := by
  let QM : Subgroup M := Q.subgroupOf M
  let DM : Subgroup M := D.subgroupOf M
  have hdisj : Disjoint QM DM := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hQ_disjoint_D hxQ hxD
  have hsup : QM ⊔ DM = (⊤ : Subgroup M) := by
    calc
      QM ⊔ DM = (Q ⊔ D).subgroupOf M :=
        (Subgroup.subgroupOf_sup hQ_le_M hD_le_M).symm
      _ = M.subgroupOf M := by rw [hQ_sup_D]
      _ = ⊤ := Subgroup.subgroupOf_self M
  letI : QM.Normal := hQ_normal_in_M
  have hmul : (QM : Set M) * (DM : Set M) = Set.univ := by
    rw [← Subgroup.normal_mul QM DM, hsup]
    exact Subgroup.coe_top
  have hcomp : QM.IsComplement' DM :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  intro m
  obtain ⟨⟨q, d⟩, hqd⟩ := hcomp.2 m
  exact ⟨q, d, hqd⟩

private theorem rankOne_coordinate_ne_base
    {L X : Type*} [Group L] [MulAction L X]
    (M Q : Subgroup L) (t : L) (a : X)
    (hM : M = MulAction.stabilizer L a) (hQ_le_M : Q ≤ M)
    (ht_not_mem_M : t ∉ M) :
    ∀ x : Q, rankOneCoordinate Q t a (some x) ≠ a := by
  intro x hx
  have hxfix : (x : L) • a = a := by
    rw [hM] at hQ_le_M
    exact (MulAction.mem_stabilizer_iff.mp (hQ_le_M x.property))
  have htfix : t • a = a := by
    calc
      t • a = (x : L) • ((x : L)⁻¹ • (t • a)) := by simp
      _ = (x : L) • a := by simpa [rankOneCoordinate] using congrArg (fun z => (x : L) • z) hx
      _ = a := hxfix
  exact ht_not_mem_M (by rw [hM, MulAction.mem_stabilizer_iff]; exact htfix)

private theorem rankOne_coordinate_injective
    {L X : Type*} [Group L] [MulAction L X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (hM : M = MulAction.stabilizer L a) (ht_involution : IsInvolution t)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_le_M : Q ≤ M) (hQ_disjoint_D : Disjoint Q D) :
    Function.Injective fun x : Q => rankOneCoordinate Q t a (some x) := by
  subst M
  intro x y hxy
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have hfix : ((x : L) * (y : L)⁻¹) • (t • a) = t • a := by
    calc
      ((x : L) * (y : L)⁻¹) • (t • a) =
          (x : L) • ((y : L)⁻¹ • (t • a)) := by rw [mul_smul]
      _ = (x : L) • ((x : L)⁻¹ • (t • a)) := by
        rw [show (y : L)⁻¹ • (t • a) = (x : L)⁻¹ • (t • a) by
          simpa [rankOneCoordinate] using hxy.symm]
      _ = t • a := by simp
  have hxyQ : (x : L) * (y : L)⁻¹ ∈ Q :=
    Q.mul_mem x.property (Q.inv_mem y.property)
  have hxyD : (x : L) * (y : L)⁻¹ ∈ D := by
    rw [hD_eq, rightConjugate_stabilizer a t, htinv]
    exact ⟨hQ_le_M hxyQ, hfix⟩
  have hone : (x : L) * (y : L)⁻¹ = 1 :=
    Subgroup.disjoint_def.mp hQ_disjoint_D hxyQ hxyD
  apply Subtype.ext
  exact mul_inv_eq_one.mp hone

private theorem rankOne_coordinate_surjective
    {L X : Type*} [Group L] [MulAction L X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M) :
    Function.Surjective (rankOneCoordinate Q t a) := by
  have hQ_le_M : Q ≤ M := rankOneSplit_Q_le_M hQ_sup_D
  have hD_le_M : D ≤ M := rankOneSplit_D_le_M hD_eq
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have ht_ne : t • a ≠ a := by
    intro htfix
    exact ht_not_mem_M (by rw [hM, MulAction.mem_stabilizer_iff]; exact htfix)
  letI : MulAction.IsMultiplyPretransitive L X 2 := htwo_transitive
  haveI : MulAction.IsPretransitive L X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hstab_pre :
      MulAction.IsPretransitive
        (MulAction.stabilizer L a) (SubMulAction.ofStabilizer L a) :=
    (MulAction.is_one_pretransitive_iff
      (G := MulAction.stabilizer L a)
      (α := SubMulAction.ofStabilizer L a)).mp
        ((SubMulAction.ofStabilizer.isMultiplyPretransitive
          (G := L) (α := X) (a := a) (n := 1)).mp htwo_transitive)
  intro y
  by_cases hy : y = a
  · exact ⟨none, by simp [rankOneCoordinate, hy]⟩
  · obtain ⟨m, hm⟩ := hstab_pre.exists_smul_eq
        (⟨t • a, ht_ne⟩ : SubMulAction.ofStabilizer L a)
        (⟨y, hy⟩ : SubMulAction.ofStabilizer L a)
    have hmX : (m : L) • (t • a) = y := by
      have hm' := congrArg Subtype.val hm
      change (m : L) • (t • a) = y at hm'
      exact hm'
    let mM : M := ⟨m, by rw [hM]; exact m.property⟩
    obtain ⟨q, d, hqd⟩ :=
      rankOne_QD_decomposition M Q D hQ_le_M hD_le_M hQ_normal_in_M
        hQ_disjoint_D hQ_sup_D mM
    have hdD : ((d : M) : L) ∈ D := d.property
    have hdfix : ((d : M) : L) • (t • a) = t • a := by
      have hdright : ((d : M) : L) ∈ rightConjugate M t := by
        have hdInf : ((d : M) : L) ∈ M ⊓ rightConjugate M t := by
          simpa only [hD_eq] using hdD
        exact hdInf.2
      have hdstab : ((d : M) : L) ∈ MulAction.stabilizer L (t • a) := by
        rw [← htinv, ← rightConjugate_stabilizer a t, ← hM]
        exact hdright
      exact MulAction.mem_stabilizer_iff.mp hdstab
    let qQ : Q := ⟨((q : Q.subgroupOf M) : M), q.property⟩
    refine ⟨some qQ⁻¹, ?_⟩
    change ((qQ⁻¹ : Q) : L)⁻¹ • (t • a) = y
    rw [Subgroup.coe_inv, inv_inv]
    calc
      (qQ : L) • (t • a) = (qQ : L) • (((d : M) : L) • (t • a)) := by rw [hdfix]
      _ = ((((q : Q.subgroupOf M) : M) : L) * (((d : D.subgroupOf M) : M) : L)) •
          (t • a) := by rw [mul_smul]
      _ = (mM : L) • (t • a) := by
        have hqdL :
            (((q : Q.subgroupOf M) : M) : L) * (((d : D.subgroupOf M) : M) : L) =
              (mM : L) := by
          exact congrArg (fun z : M => (z : L)) hqd
        rw [hqdL]
      _ = y := hmX

public noncomputable def rankOneCoordinateEquiv
    {L X : Type*} [Group L] [MulAction L X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M) :
    Option Q ≃ X := by
  apply Equiv.ofBijective (rankOneCoordinate Q t a)
  constructor
  · intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            exact False.elim
              (rankOne_coordinate_ne_base M Q t a hM (rankOneSplit_Q_le_M hQ_sup_D)
                ht_not_mem_M y hxy.symm)
    | some x =>
        cases y with
        | none =>
            exact False.elim
              (rankOne_coordinate_ne_base M Q t a hM (rankOneSplit_Q_le_M hQ_sup_D)
                ht_not_mem_M x hxy)
        | some y =>
            exact congrArg some
              (rankOne_coordinate_injective M Q D t a hM ht_involution hD_eq
                (rankOneSplit_Q_le_M hQ_sup_D) hQ_disjoint_D hxy)
  · exact rankOne_coordinate_surjective M Q D t a htwo_transitive hM ht_involution
      ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D

public theorem exists_rankOneCoordinateEquiv
    {L X : Type*} [Group L] [MulAction L X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M) :
    ∃ c : Option Q ≃ X, ∀ z : Option Q,
      c z = rankOneCoordinate Q t a z := by
  refine ⟨rankOneCoordinateEquiv M Q D t a htwo_transitive hM
    ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D
    hQ_sup_D, ?_⟩
  intro z
  rfl

public noncomputable def rankOnePointEquiv
    {Q Q' X X' : Type*} [Group Q] [Group Q']
    (c : Option Q ≃ X) (c' : Option Q' ≃ X') (qIso : Q ≃* Q') : X ≃ X' :=
  c.symm.trans ((Equiv.optionCongr qIso.toEquiv).trans c')

@[simp]
public theorem rankOnePointEquiv_apply_none
    {Q Q' X X' : Type*} [Group Q] [Group Q']
    (c : Option Q ≃ X) (c' : Option Q' ≃ X') (qIso : Q ≃* Q') :
    rankOnePointEquiv c c' qIso (c none) = c' none := by
  simp [rankOnePointEquiv]

@[simp]
public theorem rankOnePointEquiv_apply_some
    {Q Q' X X' : Type*} [Group Q] [Group Q']
    (c : Option Q ≃ X) (c' : Option Q' ≃ X') (qIso : Q ≃* Q') (x : Q) :
    rankOnePointEquiv c c' qIso (c (some x)) = c' (some (qIso x)) := by
  simp [rankOnePointEquiv]

public theorem iSup_rightConjugate_eq_normalClosure
    {L : Type*} [Group L] (Q : Subgroup L) :
    (⨆ l : L, rightConjugate Q l) = Subgroup.normalClosure (Q : Set L) := by
  apply le_antisymm
  · refine iSup_le fun l => ?_
    intro x hx
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using
      Subgroup.normalClosure_normal.conj_mem'
        q (Subgroup.subset_normalClosure hq) l
  · rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨q, hq, hqx⟩
    rcases isConj_iff.mp hqx with ⟨l, rfl⟩
    apply (le_iSup (fun l : L => rightConjugate Q l) l⁻¹)
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨q, hq, ?_⟩
    simp [mul_assoc]

public theorem rankOne_bruhat_decomposition
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M) :
    ∀ l : L, l ∈ M ∨
      ∃ m : L, m ∈ M ∧ ∃ q : L, q ∈ Q ∧ l = m * t * q := by
  let c : Option Q ≃ X :=
    rankOneCoordinateEquiv M Q D t a htwo_transitive hM ht_involution
      ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D
  intro l
  by_cases hlM : l ∈ M
  · exact Or.inl hlM
  · right
    obtain ⟨z, hz⟩ := c.surjective (l⁻¹ • a)
    cases z with
    | none =>
        exfalso
        apply hlM
        rw [hM, MulAction.mem_stabilizer_iff]
        have hlinv : l⁻¹ • a = a := by
          change a = l⁻¹ • a at hz
          exact hz.symm
        calc
          l • a = l • (l⁻¹ • a) := by rw [hlinv]
          _ = a := by simp
    | some q =>
        let m : L := l * (q : L)⁻¹ * t
        have hmfix : m • a = a := by
          calc
            m • a = l • ((q : L)⁻¹ • (t • a)) := by
              simp [m, mul_smul]
            _ = l • (l⁻¹ • a) := by
              change (q : L)⁻¹ • (t • a) = l⁻¹ • a at hz
              rw [hz]
            _ = a := by simp
        have hmM : m ∈ M := by
          rw [hM, MulAction.mem_stabilizer_iff]
          exact hmfix
        have htt : t * t = 1 := by
          simpa [pow_two] using ht_involution.sq_eq_one
        refine ⟨m, hmM, q, q.property, ?_⟩
        simp [m, htt, mul_assoc]

public theorem rankOneNormalClosure_le_generated
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M) :
    (⨆ l : L, rightConjugate Q l) ≤
      Subgroup.closure ((Q : Set L) ∪ ({t} : Set L)) := by
  let A : Subgroup L := Subgroup.closure ((Q : Set L) ∪ ({t} : Set L))
  have hQ_le_M : Q ≤ M := rankOneSplit_Q_le_M hQ_sup_D
  have hQ_le_A : Q ≤ A := fun _ hx => Subgroup.subset_closure (Or.inl hx)
  have htA : t ∈ A := Subgroup.subset_closure (Or.inr rfl)
  refine iSup_le fun l => ?_
  rcases rankOne_bruhat_decomposition M Q D t a htwo_transitive hM ht_involution
      ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D l with
    hlM | ⟨m, hmM, q, hqQ, rfl⟩
  · intro y hy
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hy
    rcases hy with ⟨x, hxQ, rfl⟩
    have hxM : x ∈ M := hQ_le_M hxQ
    have hconjM :
        (⟨l, hlM⟩ : M)⁻¹ * (⟨x, hxM⟩ : M) * (⟨l, hlM⟩ : M) ∈
          Q.subgroupOf M :=
      hQ_normal_in_M.conj_mem' ⟨x, hxM⟩ hxQ ⟨l, hlM⟩
    apply hQ_le_A
    simpa [Subgroup.mem_subgroupOf, MulAut.conj_apply, mul_assoc] using hconjM
  · intro y hy
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hy
    rcases hy with ⟨x, hxQ, rfl⟩
    have hxM : x ∈ M := hQ_le_M hxQ
    have hmConjQ : m⁻¹ * x * m ∈ Q := by
      have hconjM :
          (⟨m, hmM⟩ : M)⁻¹ * (⟨x, hxM⟩ : M) * (⟨m, hmM⟩ : M) ∈
            Q.subgroupOf M :=
        hQ_normal_in_M.conj_mem' ⟨x, hxM⟩ hxQ ⟨m, hmM⟩
      simpa [Subgroup.mem_subgroupOf] using hconjM
    have htqA : t * q ∈ A := A.mul_mem htA (hQ_le_A hqQ)
    have hconjA : rightConjugateElem (m⁻¹ * x * m) (t * q) ∈ A :=
      A.mul_mem (A.mul_mem (A.inv_mem htqA) (hQ_le_A hmConjQ)) htqA
    simpa [A, rightConjugateElem, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hconjA

public theorem rankOneNormalClosure_subgroupOf_generated
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M) :
    let A : Subgroup L := Subgroup.closure ((Q : Set L) ∪ ({t} : Set L))
    let N : Subgroup L := ⨆ l : L, rightConjugate Q l
    N.subgroupOf A = Subgroup.normalClosure (Q.subgroupOf A : Set A) := by
  dsimp only
  let A : Subgroup L := Subgroup.closure ((Q : Set L) ∪ ({t} : Set L))
  let N : Subgroup L := ⨆ l : L, rightConjugate Q l
  let QA : Subgroup A := Q.subgroupOf A
  let C : Subgroup A := Subgroup.normalClosure (QA : Set A)
  let K : Subgroup L := C.map A.subtype
  have hQ_le_M : Q ≤ M := rankOneSplit_Q_le_M hQ_sup_D
  have hQ_le_A : Q ≤ A := fun _ hx => Subgroup.subset_closure (Or.inl hx)
  have htA : t ∈ A := Subgroup.subset_closure (Or.inr rfl)
  have hQ_le_K : Q ≤ K := by
    intro x hxQ
    change x ∈ C.map A.subtype
    rw [Subgroup.mem_map]
    let xA : A := ⟨x, hQ_le_A hxQ⟩
    refine ⟨xA, ?_, rfl⟩
    exact Subgroup.subset_normalClosure (show xA ∈ QA from hxQ)
  have hN_le_K : N ≤ K := by
    refine iSup_le fun l => ?_
    rcases rankOne_bruhat_decomposition M Q D t a htwo_transitive hM ht_involution
        ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D l with
      hlM | ⟨m, hmM, q, hqQ, rfl⟩
    · intro y hy
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hy
      rcases hy with ⟨x, hxQ, rfl⟩
      have hxM : x ∈ M := hQ_le_M hxQ
      have hconjM :
          (⟨l, hlM⟩ : M)⁻¹ * (⟨x, hxM⟩ : M) * (⟨l, hlM⟩ : M) ∈
            Q.subgroupOf M :=
        hQ_normal_in_M.conj_mem' ⟨x, hxM⟩ hxQ ⟨l, hlM⟩
      apply hQ_le_K
      simpa [Subgroup.mem_subgroupOf, MulAut.conj_apply, mul_assoc] using hconjM
    · intro y hy
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hy
      rcases hy with ⟨x, hxQ, rfl⟩
      have hxM : x ∈ M := hQ_le_M hxQ
      have hmConjQ : m⁻¹ * x * m ∈ Q := by
        have hconjM :
            (⟨m, hmM⟩ : M)⁻¹ * (⟨x, hxM⟩ : M) * (⟨m, hmM⟩ : M) ∈
              Q.subgroupOf M :=
          hQ_normal_in_M.conj_mem' ⟨x, hxM⟩ hxQ ⟨m, hmM⟩
        simpa [Subgroup.mem_subgroupOf] using hconjM
      let tqA : A := ⟨t * q, A.mul_mem htA (hQ_le_A hqQ)⟩
      let xA : A := ⟨m⁻¹ * x * m, hQ_le_A hmConjQ⟩
      have hxC : xA ∈ C :=
        Subgroup.subset_normalClosure (show xA ∈ QA from hmConjQ)
      have hconjC : tqA⁻¹ * xA * tqA ∈ C :=
        Subgroup.normalClosure_normal.conj_mem' xA hxC tqA
      change
        (MulEquiv.toMonoidHom (MulAut.conj (m * t * q)⁻¹)) x ∈ C.map A.subtype
      rw [Subgroup.mem_map]
      refine ⟨tqA⁻¹ * xA * tqA, hconjC, ?_⟩
      simp [tqA, xA, mul_inv_rev, mul_assoc]
  apply le_antisymm
  · intro x hx
    have hxK : (x : L) ∈ K := hN_le_K hx
    change (x : L) ∈ C.map A.subtype at hxK
    rw [Subgroup.mem_map] at hxK
    rcases hxK with ⟨y, hyC, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    simpa [C, hyx'] using hyC
  · have hN_eq : N = Subgroup.normalClosure (Q : Set L) :=
      iSup_rightConjugate_eq_normalClosure Q
    letI : N.Normal := hN_eq.symm ▸ Subgroup.normalClosure_normal
    letI : (N.subgroupOf A).Normal := (inferInstance : N.Normal).subgroupOf A
    apply Subgroup.normalClosure_le_normal
    intro x hx
    change (x : L) ∈ N
    rw [hN_eq]
    exact Subgroup.subset_normalClosure hx

public theorem rankOneCoordinate_smul_Q
    {L X : Type*} [Group L] [MulAction L X]
    (M Q : Subgroup L) (t : L) (a : X)
    (hM : M = MulAction.stabilizer L a) (hQ_le_M : Q ≤ M)
    (q x : Q) :
    (q : L) • rankOneCoordinate Q t a (some x) =
      rankOneCoordinate Q t a (some (x * q⁻¹)) := by
  have _ := hM
  have _ := hQ_le_M
  change (q : L) • ((x : L)⁻¹ • (t • a)) =
    (((x * q⁻¹ : Q) : L)⁻¹) • (t • a)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_smul]

public theorem rankOneCoordinate_smul_Q_none
    {L X : Type*} [Group L] [MulAction L X]
    (M Q : Subgroup L) (t : L) (a : X)
    (hM : M = MulAction.stabilizer L a) (hQ_le_M : Q ≤ M)
    (q : Q) :
    (q : L) • rankOneCoordinate Q t a none = rankOneCoordinate Q t a none := by
  change (q : L) • a = a
  rw [hM] at hQ_le_M
  exact MulAction.mem_stabilizer_iff.mp (hQ_le_M q.property)

private theorem rankOne_D_fixes_t_base
    {L X : Type*} [Group L] [MulAction L X]
    (M D : Subgroup L) (t : L) (a : X)
    (hM : M = MulAction.stabilizer L a) (ht_involution : IsInvolution t)
    (hD_eq : D = M ⊓ rightConjugate M t) :
    ∀ d : L, d ∈ D → d • (t • a) = t • a := by
  intro d hd
  have hdright : d ∈ rightConjugate M t := by
    rw [hD_eq] at hd
    exact hd.2
  have hdstab : d ∈ MulAction.stabilizer L (t • a) := by
    rw [← ht_involution.inv_eq_self, ← rightConjugate_stabilizer a t, ← hM]
    exact hdright
  exact MulAction.mem_stabilizer_iff.mp hdstab

public theorem rankOneCoordinate_smul_t_none
    {L X : Type*} [Group L] [MulAction L X]
    (Q : Subgroup L) (t : L) (a : X) :
    t • rankOneCoordinate Q t a none = rankOneCoordinate Q t a (some 1) := by
  change t • a = ((1 : Q) : L)⁻¹ • (t • a)
  simp

public theorem rankOneCoordinate_smul_t_one
    {L X : Type*} [Group L] [MulAction L X]
    (Q : Subgroup L) (t : L) (a : X) (ht_involution : IsInvolution t) :
    t • rankOneCoordinate Q t a (some 1) = rankOneCoordinate Q t a none := by
  change t • (((1 : Q) : L)⁻¹ • (t • a)) = a
  rw [show ((1 : Q) : L)⁻¹ = 1 by simp, one_smul]
  simpa [pow_two, mul_smul] using congrArg (fun z : L => z • a) ht_involution.2

public theorem rankOneCoordinate_smul_t
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L) (a : X)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 →
      t * x * t = g x * h x * t * f x)
    (x : Q) (hx : x ≠ 1) :
    t • rankOneCoordinate Q t a (some x) =
      rankOneCoordinate Q t a
        (some ⟨f x, (hf_mem x x.property (by simpa using hx)).1⟩) := by
  have hxL : (x : L) ≠ 1 := by simpa using hx
  have hxinvQ : (x : L)⁻¹ ∈ Q := Q.inv_mem x.property
  have hxinv1 : (x : L)⁻¹ ≠ 1 := by simpa
  have hQ_le_M : Q ≤ M := rankOneSplit_Q_le_M hQ_sup_D
  have hfInvFix : f (x : L)⁻¹ • a = a := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [← hM]
    exact hQ_le_M (hf_mem (x : L)⁻¹ hxinvQ hxinv1).1
  have hhInvFix : h (x : L)⁻¹ • (t • a) = t • a :=
    rankOne_D_fixes_t_base M D t a hM ht_involution hD_eq
      (h (x : L)⁻¹) (hh_mem (x : L)⁻¹ hxinvQ hxinv1)
  have hfg : f x = (g (x : L)⁻¹)⁻¹ := by
    simpa using
      (claim_H1 M Q D t f g h htwo_transitive ⟨a, hM⟩ ht_involution ht_not_mem_M
      hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq (x : L)⁻¹ hxinvQ hxinv1)
  have hgf : g (x : L)⁻¹ = (f x)⁻¹ := by
    calc
      g (x : L)⁻¹ = ((g (x : L)⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (f x)⁻¹ := by rw [hfg]
  calc
    t • rankOneCoordinate Q t a (some x) =
        (t * (x : L)⁻¹ * t) • a := by simp [rankOneCoordinate, mul_smul]
    _ = (g (x : L)⁻¹ * h (x : L)⁻¹ * t * f (x : L)⁻¹) • a := by
      rw [hcanonical_eq (x : L)⁻¹ hxinvQ hxinv1]
    _ = g (x : L)⁻¹ • (h (x : L)⁻¹ • (t • (f (x : L)⁻¹ • a))) := by
      simp only [mul_smul]
    _ = g (x : L)⁻¹ • (h (x : L)⁻¹ • (t • a)) := by rw [hfInvFix]
    _ = g (x : L)⁻¹ • (t • a) := by rw [hhInvFix]
    _ = (f x)⁻¹ • (t • a) := by rw [hgf]
    _ = rankOneCoordinate Q t a
        (some ⟨f x, (hf_mem x x.property hxL).1⟩) := rfl

@[expose] public def IsActionTransport
    {L L' X X' : Type*} [Group L] [Group L'] [MulAction L X] [MulAction L' X']
    (e : X ≃ X') (l : L) (l' : L') : Prop :=
  ∀ x : X, e (l • x) = l' • e x

public theorem exists_rankOnePointEquiv
    {L L' X X' : Type*}
    [Group L] [Finite L] [MulAction L X] [Finite X]
    [Group L'] [Finite L'] [MulAction L' X'] [Finite X']
    (M Q D : Subgroup L) (t : L) (f g h : L → L) (a : X)
    (M' Q' D' : Subgroup L') (t' : L') (f' g' h' : L' → L') (a' : X')
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 →
      t * x * t = g x * h x * t * f x)
    (htwo_transitive' : MulAction.IsMultiplyPretransitive L' X' 2)
    (hM' : M' = MulAction.stabilizer L' a')
    (ht_involution' : IsInvolution t') (ht_not_mem_M' : t' ∉ M')
    (hD_eq' : D' = M' ⊓ rightConjugate M' t')
    (hQ_normal_in_M' : (Q'.subgroupOf M').Normal)
    (hQ_disjoint_D' : Disjoint Q' D') (hQ_sup_D' : Q' ⊔ D' = M')
    (hf_mem' : ∀ x : L', x ∈ Q' → x ≠ 1 → f' x ∈ Q' ∧ f' x ≠ 1)
    (hg_mem' : ∀ x : L', x ∈ Q' → x ≠ 1 → g' x ∈ Q' ∧ g' x ≠ 1)
    (hh_mem' : ∀ x : L', x ∈ Q' → x ≠ 1 → h' x ∈ D')
    (hcanonical_eq' : ∀ x : L', x ∈ Q' → x ≠ 1 →
      t' * x * t' = g' x * h' x * t' * f' x)
    (qIso : Q ≃* Q')
    (hf_compat : ∀ x : L, ∀ hx : x ∈ Q, ∀ hx1 : x ≠ 1,
      ((qIso ⟨f x, (hf_mem x hx hx1).1⟩ : Q') : L') =
        f' ((qIso ⟨x, hx⟩ : Q') : L')) :
    ∃ e : X ≃ X',
      e a = a' ∧
        (∀ q : Q, IsActionTransport e (q : L) ((qIso q : Q') : L')) ∧
          IsActionTransport e t t' := by
  let c : Option Q ≃ X :=
    rankOneCoordinateEquiv M Q D t a htwo_transitive hM ht_involution
      ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D
  let c' : Option Q' ≃ X' :=
    rankOneCoordinateEquiv M' Q' D' t' a' htwo_transitive' hM' ht_involution'
      ht_not_mem_M' hD_eq' hQ_normal_in_M' hQ_disjoint_D' hQ_sup_D'
  let e : X ≃ X' := rankOnePointEquiv c c' qIso
  refine ⟨e, ?_, ?_, ?_⟩
  · change e (c none) = c' none
    exact rankOnePointEquiv_apply_none c c' qIso
  · intro q x
    obtain ⟨z, rfl⟩ := c.surjective x
    cases z with
    | none =>
        calc
          e ((q : L) • c none) = e (c none) := by
            rw [show (q : L) • c none = c none by
              exact rankOneCoordinate_smul_Q_none M Q t a hM
                (rankOneSplit_Q_le_M hQ_sup_D) q]
          _ = c' none := rankOnePointEquiv_apply_none c c' qIso
          _ = ((qIso q : Q') : L') • c' none := by
            symm
            exact rankOneCoordinate_smul_Q_none M' Q' t' a' hM'
              (rankOneSplit_Q_le_M hQ_sup_D') (qIso q)
          _ = ((qIso q : Q') : L') • e (c none) := by
            rw [rankOnePointEquiv_apply_none c c' qIso]
    | some x =>
        calc
          e ((q : L) • c (some x)) = e (c (some (x * q⁻¹))) := by
            rw [show (q : L) • c (some x) = c (some (x * q⁻¹)) by
              exact rankOneCoordinate_smul_Q M Q t a hM
                (rankOneSplit_Q_le_M hQ_sup_D) q x]
          _ = c' (some (qIso (x * q⁻¹))) :=
            rankOnePointEquiv_apply_some c c' qIso (x * q⁻¹)
          _ = c' (some (qIso x * (qIso q)⁻¹)) := by simp
          _ = ((qIso q : Q') : L') • c' (some (qIso x)) := by
            symm
            exact rankOneCoordinate_smul_Q M' Q' t' a' hM'
              (rankOneSplit_Q_le_M hQ_sup_D') (qIso q) (qIso x)
          _ = ((qIso q : Q') : L') • e (c (some x)) := by
            rw [rankOnePointEquiv_apply_some c c' qIso x]
  · intro x
    obtain ⟨z, rfl⟩ := c.surjective x
    cases z with
    | none =>
        calc
          e (t • c none) = e (c (some 1)) := by
            rw [show t • c none = c (some 1) by
              exact rankOneCoordinate_smul_t_none Q t a]
          _ = c' (some (qIso 1)) :=
            rankOnePointEquiv_apply_some c c' qIso 1
          _ = c' (some 1) := by simp
          _ = t' • c' none := by
            symm
            exact rankOneCoordinate_smul_t_none Q' t' a'
          _ = t' • e (c none) := by
            rw [rankOnePointEquiv_apply_none c c' qIso]
    | some x =>
        by_cases hx : x = 1
        · subst x
          calc
            e (t • c (some 1)) = e (c none) := by
              rw [show t • c (some 1) = c none by
                exact rankOneCoordinate_smul_t_one Q t a ht_involution]
            _ = c' none := rankOnePointEquiv_apply_none c c' qIso
            _ = t' • c' (some 1) := by
              symm
              exact rankOneCoordinate_smul_t_one Q' t' a' ht_involution'
            _ = t' • e (c (some 1)) := by
              rw [rankOnePointEquiv_apply_some c c' qIso 1]
              simp
        · have hxL : (x : L) ≠ 1 := by simpa using hx
          have hx' : qIso x ≠ 1 := (map_ne_one_iff qIso qIso.injective).2 hx
          have hxL' : ((qIso x : Q') : L') ≠ 1 := by simpa using hx'
          let fx : Q := ⟨f x, (hf_mem x x.property hxL).1⟩
          let fx' : Q' :=
            ⟨f' ((qIso x : Q') : L'),
              (hf_mem' ((qIso x : Q') : L') (qIso x).property hxL').1⟩
          have hfx : qIso fx = fx' := by
            apply Subtype.ext
            exact hf_compat (x : L) x.property hxL
          calc
            e (t • c (some x)) = e (c (some fx)) := by
              rw [show t • c (some x) = c (some fx) by
                exact rankOneCoordinate_smul_t M Q D t f g h a htwo_transitive hM
                  ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D
                  hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x hx]
            _ = c' (some (qIso fx)) :=
              rankOnePointEquiv_apply_some c c' qIso fx
            _ = c' (some fx') := by rw [hfx]
            _ = t' • c' (some (qIso x)) := by
              symm
              exact rankOneCoordinate_smul_t M' Q' D' t' f' g' h' a'
                htwo_transitive' hM' ht_involution' ht_not_mem_M' hD_eq'
                hQ_normal_in_M' hQ_disjoint_D' hQ_sup_D' hf_mem' hg_mem' hh_mem'
                hcanonical_eq' (qIso x) hx'
            _ = t' • e (c (some x)) := by
              rw [rankOnePointEquiv_apply_some c c' qIso x]

private def rankOneDConjugate
    {L : Type*} [Group L] (M Q D : Subgroup L)
    (hQ_le_M : Q ≤ M) (hD_le_M : D ≤ M)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal) (d : D) (x : Q) : Q :=
  ⟨(d : L) * (x : L) * (d : L)⁻¹, by
    have hconj :
        (⟨d, hD_le_M d.property⟩ : M) *
            (⟨x, hQ_le_M x.property⟩ : M) *
              (⟨d, hD_le_M d.property⟩ : M)⁻¹ ∈ Q.subgroupOf M := by
      simpa only [inv_inv] using
        hQ_normal_in_M.conj_mem' ⟨x, hQ_le_M x.property⟩ x.property
          (⟨d, hD_le_M d.property⟩ : M)⁻¹
    simpa [Subgroup.mem_subgroupOf] using hconj⟩

private theorem rankOneCoordinate_smul_D_none
    {L X : Type*} [Group L] [MulAction L X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (hM : M = MulAction.stabilizer L a) (hD_le_M : D ≤ M) (d : D) :
    (d : L) • rankOneCoordinate Q t a none = rankOneCoordinate Q t a none := by
  change (d : L) • a = a
  apply MulAction.mem_stabilizer_iff.mp
  rw [← hM]
  exact hD_le_M d.property

private theorem rankOneCoordinate_smul_D
    {L X : Type*} [Group L] [MulAction L X]
    (M Q D : Subgroup L) (t : L) (a : X)
    (hM : M = MulAction.stabilizer L a) (ht_involution : IsInvolution t)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_le_M : Q ≤ M) (hD_le_M : D ≤ M)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal) (d : D) (x : Q) :
    (d : L) • rankOneCoordinate Q t a (some x) =
      rankOneCoordinate Q t a
        (some (rankOneDConjugate M Q D hQ_le_M hD_le_M hQ_normal_in_M d x)) := by
  have hdInvFix : (d : L)⁻¹ • (t • a) = t • a :=
    rankOne_D_fixes_t_base M D t a hM ht_involution hD_eq
      (d : L)⁻¹ (D.inv_mem d.property)
  change (d : L) • ((x : L)⁻¹ • (t • a)) =
    ((rankOneDConjugate M Q D hQ_le_M hD_le_M hQ_normal_in_M d x : Q) : L)⁻¹ •
      (t • a)
  rw [show
    ((rankOneDConjugate M Q D hQ_le_M hD_le_M hQ_normal_in_M d x : Q) : L)⁻¹ =
        (d : L) * (x : L)⁻¹ * (d : L)⁻¹ by
      simp [rankOneDConjugate, mul_inv_rev, mul_assoc]]
  simp only [mul_smul]
  rw [hdInvFix]

public theorem rankOnePointEquiv_transport_M
    {L L' X X' : Type*}
    [Group L] [Finite L] [MulAction L X] [Finite X]
    [Group L'] [Finite L'] [MulAction L' X'] [Finite X']
    (M Q D : Subgroup L) (t : L) (a : X)
    (M' Q' D' : Subgroup L') (t' : L') (a' : X')
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hM : M = MulAction.stabilizer L a)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (htwo_transitive' : MulAction.IsMultiplyPretransitive L' X' 2)
    (hM' : M' = MulAction.stabilizer L' a')
    (ht_involution' : IsInvolution t') (ht_not_mem_M' : t' ∉ M')
    (hD_eq' : D' = M' ⊓ rightConjugate M' t')
    (hQ_normal_in_M' : (Q'.subgroupOf M').Normal)
    (hQ_disjoint_D' : Disjoint Q' D') (hQ_sup_D' : Q' ⊔ D' = M')
    (mIso : M ≃* M') (qIso : Q ≃* Q')
    (hQ_compat : ∀ x : Q,
      ((mIso ⟨x, (rankOneSplit_Q_le_M hQ_sup_D) x.property⟩ : M') : L') =
        ((qIso x : Q') : L'))
    (hD_compat :
      (D.subgroupOf M).map mIso.toMonoidHom = D'.subgroupOf M')
    (e : X ≃ X') (he_base : e a = a')
    (he_Q : ∀ q : Q, IsActionTransport e (q : L) ((qIso q : Q') : L'))
    (he_t : IsActionTransport e t t') :
    ∀ m : M, IsActionTransport e (m : L) (mIso m : L') := by
  let c : Option Q ≃ X :=
    rankOneCoordinateEquiv M Q D t a htwo_transitive hM ht_involution
      ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D
  let c' : Option Q' ≃ X' :=
    rankOneCoordinateEquiv M' Q' D' t' a' htwo_transitive' hM' ht_involution'
      ht_not_mem_M' hD_eq' hQ_normal_in_M' hQ_disjoint_D' hQ_sup_D'
  have hQ_le_M : Q ≤ M := rankOneSplit_Q_le_M hQ_sup_D
  have hD_le_M : D ≤ M := rankOneSplit_D_le_M hD_eq
  have hQ'_le_M' : Q' ≤ M' := rankOneSplit_Q_le_M hQ_sup_D'
  have hD'_le_M' : D' ≤ M' := rankOneSplit_D_le_M hD_eq'
  have he_none : e (c none) = c' none := by
    change e a = a'
    exact he_base
  have he_some : ∀ x : Q, e (c (some x)) = c' (some (qIso x)) := by
    intro x
    change e ((x : L)⁻¹ • (t • a)) =
      ((qIso x : Q') : L')⁻¹ • (t' • a')
    calc
      e ((x : L)⁻¹ • (t • a)) =
          ((qIso (x⁻¹) : Q') : L') • e (t • a) := he_Q x⁻¹ (t • a)
      _ = ((qIso (x⁻¹) : Q') : L') • (t' • e a) := by rw [he_t a]
      _ = ((qIso (x⁻¹) : Q') : L') • (t' • a') := by rw [he_base]
      _ = ((qIso x : Q') : L')⁻¹ • (t' • a') := by simp
  have he_D : ∀ d : D,
      IsActionTransport e (d : L)
        ((mIso ⟨d, hD_le_M d.property⟩ : M') : L') := by
    intro d
    let dM : M := ⟨d, hD_le_M d.property⟩
    let dM' : M' := mIso dM
    have hdM' : dM' ∈ D'.subgroupOf M' := by
      rw [← hD_compat, Subgroup.mem_map]
      exact ⟨dM, d.property, rfl⟩
    let d' : D' := ⟨dM', hdM'⟩
    intro z
    obtain ⟨w, rfl⟩ := c.surjective z
    cases w with
    | none =>
        have hd_coord : (d : L) • c none = c none := by
          change (d : L) • rankOneCoordinate Q t a none =
            rankOneCoordinate Q t a none
          exact rankOneCoordinate_smul_D_none M Q D t a hM hD_le_M d
        calc
          e ((d : L) • c none) = e (c none) := by rw [hd_coord]
          _ = c' none := he_none
          _ = (d' : L') • c' none := by
            symm
            change (d' : L') • rankOneCoordinate Q' t' a' none =
              rankOneCoordinate Q' t' a' none
            exact
              rankOneCoordinate_smul_D_none M' Q' D' t' a' hM' hD'_le_M' d'
          _ = ((mIso dM : M') : L') • e (c none) := by
            change (d' : L') • c' none = (d' : L') • e (c none)
            rw [he_none]
    | some x =>
        let y : Q :=
          rankOneDConjugate M Q D hQ_le_M hD_le_M hQ_normal_in_M d x
        let y' : Q' :=
          rankOneDConjugate M' Q' D' hQ'_le_M' hD'_le_M'
            hQ_normal_in_M' d' (qIso x)
        have hy : qIso y = y' := by
          apply Subtype.ext
          let yM : M := ⟨y, hQ_le_M y.property⟩
          let xM : M := ⟨x, hQ_le_M x.property⟩
          have hyM : yM = dM * xM * dM⁻¹ := by
            apply Subtype.ext
            rfl
          calc
            ((qIso y : Q') : L') = ((mIso yM : M') : L') :=
              (hQ_compat y).symm
            _ = ((mIso (dM * xM * dM⁻¹) : M') : L') := by rw [hyM]
            _ = ((mIso dM : M') : L') * ((mIso xM : M') : L') *
                ((mIso dM : M') : L')⁻¹ := by simp
            _ = (d' : L') * ((qIso x : Q') : L') * (d' : L')⁻¹ := by
              rw [hQ_compat x]
            _ = ((y' : Q') : L') := rfl
        have hd_coord : (d : L) • c (some x) = c (some y) := by
          change (d : L) • rankOneCoordinate Q t a (some x) =
            rankOneCoordinate Q t a (some y)
          exact rankOneCoordinate_smul_D M Q D t a hM ht_involution hD_eq
            hQ_le_M hD_le_M hQ_normal_in_M d x
        have hd'_coord :
            (d' : L') • c' (some (qIso x)) = c' (some y') := by
          change (d' : L') • rankOneCoordinate Q' t' a' (some (qIso x)) =
            rankOneCoordinate Q' t' a' (some y')
          exact rankOneCoordinate_smul_D M' Q' D' t' a' hM' ht_involution'
            hD_eq' hQ'_le_M' hD'_le_M' hQ_normal_in_M' d' (qIso x)
        calc
          e ((d : L) • c (some x)) = e (c (some y)) := by rw [hd_coord]
          _ = c' (some (qIso y)) := he_some y
          _ = c' (some y') := by rw [hy]
          _ = (d' : L') • c' (some (qIso x)) := by
            symm
            exact hd'_coord
          _ = ((mIso dM : M') : L') • e (c (some x)) := by
            change (d' : L') • c' (some (qIso x)) =
              (d' : L') • e (c (some x))
            rw [he_some x]
  intro m z
  obtain ⟨qM, dM, hqd⟩ :=
    rankOne_QD_decomposition M Q D hQ_le_M hD_le_M hQ_normal_in_M
      hQ_disjoint_D hQ_sup_D m
  let q : Q := ⟨qM, qM.property⟩
  let d : D := ⟨dM, dM.property⟩
  have hmIso :
      ((mIso m : M') : L') =
        ((qIso q : Q') : L') * ((mIso ⟨d, hD_le_M d.property⟩ : M') : L') := by
    calc
      ((mIso m : M') : L') = ((mIso (qM * dM) : M') : L') := by rw [hqd]
      _ = ((mIso qM : M') : L') * ((mIso dM : M') : L') := by simp
      _ = ((qIso q : Q') : L') * ((mIso ⟨d, hD_le_M d.property⟩ : M') : L') := by
        rw [hQ_compat q]
  calc
    e ((m : L) • z) = e (((q : L) * (d : L)) • z) := by
      have hqdL : (m : L) = (q : L) * (d : L) := by
        exact congrArg (fun w : M => (w : L)) hqd.symm
      rw [hqdL]
    _ = e ((q : L) • ((d : L) • z)) := by rw [mul_smul]
    _ = ((qIso q : Q') : L') • e ((d : L) • z) := he_Q q ((d : L) • z)
    _ = ((qIso q : Q') : L') •
        (((mIso ⟨d, hD_le_M d.property⟩ : M') : L') • e z) := by
      rw [he_D d z]
    _ = (((qIso q : Q') : L') *
        ((mIso ⟨d, hD_le_M d.property⟩ : M') : L')) • e z := by
      rw [mul_smul]
    _ = ((mIso m : M') : L') • e z := by rw [hmIso]

public theorem IsActionTransport.unique
    {L L' X X' : Type*} [Group L] [Group L'] [MulAction L X] [MulAction L' X']
    [FaithfulSMul L' X'] {e : X ≃ X'} {l : L} {l₁' l₂' : L'}
    (h₁ : IsActionTransport e l l₁') (h₂ : IsActionTransport e l l₂') :
    l₁' = l₂' := by
  apply MulAction.toPerm_injective (α := L') (β := X')
  ext x'
  have h₁' := h₁ (e.symm x')
  have h₂' := h₂ (e.symm x')
  simpa using h₁'.symm.trans h₂'

public def actionTransportSubgroup
    {L L' X X' : Type*} [Group L] [Group L'] [MulAction L X] [MulAction L' X']
    (e : X ≃ X') (A' : Subgroup L') : Subgroup L where
  carrier := {l | ∃ l' : A', IsActionTransport e l (l' : L')}
  one_mem' := ⟨1, by intro x; simp⟩
  mul_mem' := by
    rintro l₁ l₂ ⟨l₁', hl₁⟩ ⟨l₂', hl₂⟩
    refine ⟨l₁' * l₂', ?_⟩
    intro x
    simp only [mul_smul]
    rw [hl₁, hl₂]
    simp only [Subgroup.coe_mul, mul_smul]
  inv_mem' := by
    rintro l ⟨l', hl⟩
    refine ⟨l'⁻¹, ?_⟩
    intro x
    calc
      e (l⁻¹ • x) = (l' : L')⁻¹ • ((l' : L') • e (l⁻¹ • x)) := by simp
      _ = (l' : L')⁻¹ • e (l • (l⁻¹ • x)) := by rw [hl]
      _ = (l' : L')⁻¹ • e x := by simp

public noncomputable def actionTransportHom
    {L L' X X' : Type*} [Group L] [Group L'] [MulAction L X] [MulAction L' X']
    [FaithfulSMul L' X'] (e : X ≃ X') (A : Subgroup L) (A' : Subgroup L')
    (hA : A ≤ actionTransportSubgroup e A') : A →* A' where
  toFun l := Classical.choose (hA l.property)
  map_one' := by
    apply Subtype.ext
    exact IsActionTransport.unique
      (l₂' := (1 : L')) (Classical.choose_spec (hA (1 : A).property))
      (by intro x; simp)
  map_mul' l₁ l₂ := by
    apply Subtype.ext
    exact IsActionTransport.unique
      (l₂' := ((Classical.choose (hA l₁.property) : A') : L') *
        ((Classical.choose (hA l₂.property) : A') : L'))
      (Classical.choose_spec (hA (l₁ * l₂).property))
      (by
        intro x
        simp only [Subgroup.coe_mul, mul_smul]
        rw [Classical.choose_spec (hA l₁.property),
          Classical.choose_spec (hA l₂.property)])

public theorem actionTransportHom_spec
    {L L' X X' : Type*} [Group L] [Group L'] [MulAction L X] [MulAction L' X']
    [FaithfulSMul L' X'] (e : X ≃ X') (A : Subgroup L) (A' : Subgroup L')
    (hA : A ≤ actionTransportSubgroup e A') (l : A) :
    IsActionTransport e (l : L) (actionTransportHom e A A' hA l : L') :=
  Classical.choose_spec (hA l.property)

public theorem actionTransportHom_injective
    {L L' X X' : Type*} [Group L] [Group L'] [MulAction L X] [MulAction L' X']
    [FaithfulSMul L X] [FaithfulSMul L' X']
    (e : X ≃ X') (A : Subgroup L) (A' : Subgroup L')
    (hA : A ≤ actionTransportSubgroup e A') :
    Function.Injective (actionTransportHom e A A' hA) := by
  intro l₁ l₂ hl
  apply Subtype.ext
  apply MulAction.toPerm_injective (α := L) (β := X)
  ext x
  change (l₁ : L) • x = (l₂ : L) • x
  apply e.injective
  rw [actionTransportHom_spec e A A' hA l₁,
    actionTransportHom_spec e A A' hA l₂, hl]

public theorem rankOneGeneratedSubgroup_equiv
    {L L' X X' : Type*} [Group L] [Group L'] [MulAction L X] [MulAction L' X']
    [FaithfulSMul L X] [FaithfulSMul L' X']
    (Q : Subgroup L) (t : L) (Q' : Subgroup L') (t' : L')
    (qIso : Q ≃* Q') (e : X ≃ X')
    (hQ : ∀ q : Q, IsActionTransport e (q : L) ((qIso q : Q') : L'))
    (ht : IsActionTransport e t t') :
    ∃ E : Subgroup.closure ((Q : Set L) ∪ ({t} : Set L)) ≃*
        Subgroup.closure ((Q' : Set L') ∪ ({t'} : Set L')),
      (∀ q : Q,
        E ⟨q, Subgroup.subset_closure (Or.inl q.property)⟩ =
          ⟨qIso q, Subgroup.subset_closure (Or.inl (qIso q).property)⟩) ∧
        E ⟨t, Subgroup.subset_closure (Or.inr rfl)⟩ =
          ⟨t', Subgroup.subset_closure (Or.inr rfl)⟩ := by
  let A : Subgroup L := Subgroup.closure ((Q : Set L) ∪ ({t} : Set L))
  let A' : Subgroup L' := Subgroup.closure ((Q' : Set L') ∪ ({t'} : Set L'))
  have hA : A ≤ actionTransportSubgroup e A' := by
    refine (Subgroup.closure_le (K := actionTransportSubgroup e A')).2 ?_
    intro l hl
    rcases hl with hlQ | rfl
    · let q : Q := ⟨l, hlQ⟩
      refine ⟨⟨qIso q, Subgroup.subset_closure (Or.inl (qIso q).property)⟩, ?_⟩
      exact hQ q
    · exact ⟨⟨t', Subgroup.subset_closure (Or.inr rfl)⟩, ht⟩
  let phi : A →* A' := actionTransportHom e A A' hA
  have hphi_injective : Function.Injective phi :=
    actionTransportHom_injective e A A' hA
  have hphi_surjective : Function.Surjective phi := by
    intro l'
    have hpreimage :
        ∀ x : L', x ∈ A' → ∃ l : A, (phi l : L') = x := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x hx => ∃ l : A, (phi l : L') = x)
        (fun x hx => ?_) ?_ (fun x y hx hy ihx ihy => ?_)
        (fun x hx ihx => ?_) hx
      · rcases hx with hxQ | hxt
        · let q' : Q' := ⟨x, hxQ⟩
          let q : Q := qIso.symm q'
          let l : A := ⟨q, Subgroup.subset_closure (Or.inl q.property)⟩
          refine ⟨l, ?_⟩
          have hspec := actionTransportHom_spec e A A' hA l
          have htransport := hQ q
          have heq : (phi l : L') = ((qIso q : Q') : L') :=
            IsActionTransport.unique hspec htransport
          simpa [q, q'] using heq
        · have hxt' : x = t' := Set.mem_singleton_iff.mp hxt
          subst x
          let l : A := ⟨t, Subgroup.subset_closure (Or.inr rfl)⟩
          refine ⟨l, ?_⟩
          exact IsActionTransport.unique
            (actionTransportHom_spec e A A' hA l) ht
      · exact ⟨1, by simp [phi]⟩
      · rcases ihx with ⟨lx, hlx⟩
        rcases ihy with ⟨ly, hly⟩
        refine ⟨lx * ly, ?_⟩
        simpa only [map_mul, Subgroup.coe_mul] using congrArg₂ (· * ·) hlx hly
      · rcases ihx with ⟨lx, hlx⟩
        refine ⟨lx⁻¹, ?_⟩
        simpa only [map_inv, Subgroup.coe_inv] using congrArg Inv.inv hlx
    obtain ⟨l, hl⟩ := hpreimage l' l'.property
    exact ⟨l, Subtype.ext hl⟩
  let E : A ≃* A' := MulEquiv.ofBijective phi ⟨hphi_injective, hphi_surjective⟩
  refine ⟨E, ?_, ?_⟩
  · intro q
    apply Subtype.ext
    exact IsActionTransport.unique
      (actionTransportHom_spec e A A' hA
        ⟨q, Subgroup.subset_closure (Or.inl q.property)⟩)
      (hQ q)
  · apply Subtype.ext
    exact IsActionTransport.unique
      (actionTransportHom_spec e A A' hA
        ⟨t, Subgroup.subset_closure (Or.inr rfl)⟩)
      ht

public theorem exists_equivariant_equiv_of_stabilizer_map_eq
    {L L' X X' : Type*}
    [Group L] [MulAction L X] [MulAction.IsPretransitive L X]
    [Group L'] [MulAction L' X'] [MulAction.IsPretransitive L' X']
    (eL : L ≃* L') (a : X) (a' : X')
    (hstab : (MulAction.stabilizer L a).map eL.toMonoidHom =
      MulAction.stabilizer L' a') :
    ∃ eX : X ≃ X', ∀ l : L, ∀ x : X,
      eX (l • x) = eL l • eX x := by
  classical
  let rep : X → L := fun x =>
    Classical.choose (MulAction.exists_smul_eq L a x)
  have hrep : ∀ x : X, rep x • a = x := fun x =>
    Classical.choose_spec (MulAction.exists_smul_eq L a x)
  have hstab_iff : ∀ l : L,
      l ∈ MulAction.stabilizer L a ↔
        eL l ∈ MulAction.stabilizer L' a' := by
    intro l
    constructor
    · intro hl
      rw [← hstab, Subgroup.mem_map]
      exact ⟨l, hl, rfl⟩
    · intro hl
      rw [← hstab, Subgroup.mem_map] at hl
      rcases hl with ⟨m, hm, hml⟩
      have : m = l := eL.injective hml
      simpa [this] using hm
  have hsame_iff : ∀ l m : L,
      l • a = m • a ↔ eL l • a' = eL m • a' := by
    intro l m
    constructor
    · intro hlm
      have hfix : m⁻¹ * l ∈ MulAction.stabilizer L a := by
        change (m⁻¹ * l) • a = a
        calc
          (m⁻¹ * l) • a = m⁻¹ • (l • a) := by rw [mul_smul]
          _ = m⁻¹ • (m • a) := by rw [hlm]
          _ = a := by simp
      have hfix' := (hstab_iff (m⁻¹ * l)).1 hfix
      change eL (m⁻¹ * l) • a' = a' at hfix'
      have h := congrArg (fun x => eL m • x) hfix'
      simpa [mul_smul] using h
    · intro hlm
      have hfix' : eL (m⁻¹ * l) ∈ MulAction.stabilizer L' a' := by
        change eL (m⁻¹ * l) • a' = a'
        calc
          eL (m⁻¹ * l) • a' = (eL m)⁻¹ • (eL l • a') := by
            simp [mul_smul]
          _ = (eL m)⁻¹ • (eL m • a') := by rw [hlm]
          _ = a' := by simp
      have hfix := (hstab_iff (m⁻¹ * l)).2 hfix'
      change (m⁻¹ * l) • a = a at hfix
      have h := congrArg (fun x => m • x) hfix
      simpa [mul_smul] using h
  let pointMap : X → X' := fun x => eL (rep x) • a'
  have hpointMap_injective : Function.Injective pointMap := by
    intro x y hxy
    calc
      x = rep x • a := (hrep x).symm
      _ = rep y • a := (hsame_iff (rep x) (rep y)).2 hxy
      _ = y := hrep y
  have hpointMap_surjective : Function.Surjective pointMap := by
    intro y
    obtain ⟨l', hl'⟩ := MulAction.exists_smul_eq L' a' y
    let x : X := eL.symm l' • a
    refine ⟨x, ?_⟩
    change eL (rep x) • a' = y
    rw [← hl']
    simpa using (hsame_iff (rep x) (eL.symm l')).1 (by simp [x, hrep])
  let eX : X ≃ X' :=
    Equiv.ofBijective pointMap ⟨hpointMap_injective, hpointMap_surjective⟩
  refine ⟨eX, ?_⟩
  intro l x
  change eL (rep (l • x)) • a' = eL l • (eL (rep x) • a')
  have hsource : rep (l • x) • a = (l * rep x) • a := by
    rw [hrep, mul_smul, hrep]
  simpa [mul_smul] using
    (hsame_iff (rep (l • x)) (l * rep x)).1 hsource

end PFchapter4section1
end CFSG.BenderSuzuki
