module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG

namespace FiveTransitive.CyclicNormalizerOrbitAction

open Subgroup MulAction

theorem normalizer_orbitRel_iff
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (R : Subgroup (Equiv.Perm Y))
    (k : Subgroup.normalizer (R : Set (Equiv.Perm Y)))
    (x y : Y) :
    MulAction.orbitRel R Y x y ↔
      MulAction.orbitRel R Y ((k : Equiv.Perm Y) x)
        ((k : Equiv.Perm Y) y) := by
  have hforward
      (a : Subgroup.normalizer (R : Set (Equiv.Perm Y)))
      {u v : Y}
      (h : MulAction.orbitRel R Y u v) :
      MulAction.orbitRel R Y ((a : Equiv.Perm Y) u)
        ((a : Equiv.Perm Y) v) := by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
    obtain ⟨z, hz⟩ := h
    refine ⟨R.normalizerMonoidHom a z, ?_⟩
    change
      (↑(R.normalizerMonoidHom a z) : Equiv.Perm Y)
          ((a : Equiv.Perm Y) v) =
        (a : Equiv.Perm Y) u
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp only [Equiv.Perm.mul_apply]
    rw [show
      ((a : Equiv.Perm Y)⁻¹) ((a : Equiv.Perm Y) v) = v by
        exact (a : Equiv.Perm Y).symm_apply_apply v]
    change (a : Equiv.Perm Y) (z • v) =
      (a : Equiv.Perm Y) u
    rw [hz]
  constructor
  · exact hforward k
  · intro h
    have h' := hforward k⁻¹ h
    simpa using h'

@[expose] noncomputable def normalizerOrbitHom
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (R : Subgroup (Equiv.Perm Y)) :
    Subgroup.normalizer (R : Set (Equiv.Perm Y)) →*
      Equiv.Perm (MulAction.orbitRel.Quotient R Y) where
  toFun k :=
    Quotient.congr (k : Equiv.Perm Y)
      (normalizer_orbitRel_iff R k)
  map_one' := by
    apply Equiv.ext
    intro q
    induction q using Quotient.inductionOn'
    rfl
  map_mul' a b := by
    apply Equiv.ext
    intro q
    induction q using Quotient.inductionOn'
    rfl

@[simp]
theorem normalizerOrbitHom_apply_mk
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (R : Subgroup (Equiv.Perm Y))
    (k : Subgroup.normalizer (R : Set (Equiv.Perm Y)))
    (x : Y) :
    normalizerOrbitHom R k (Quotient.mk'' x) =
      Quotient.mk'' ((k : Equiv.Perm Y) x) :=
  rfl

@[expose] noncomputable def orbitHomOfLeNormalizer
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (R K : Subgroup (Equiv.Perm Y))
    (hK : K ≤ Subgroup.normalizer (R : Set (Equiv.Perm Y))) :
    K →* Equiv.Perm (MulAction.orbitRel.Quotient R Y) :=
  (normalizerOrbitHom R).comp
    (K.subtype.codRestrict
      (Subgroup.normalizer (R : Set (Equiv.Perm Y)))
      (fun x => hK x.prop))

private noncomputable def cycleFactorsEquivOrbitQuotient
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (g : Equiv.Perm Y)
    (hfree : ∀ x : Y, g x ≠ x) :
    g.cycleFactorsFinset ≃
      MulAction.orbitRel.Quotient (Subgroup.zpowers g) Y := by
  classical
  let a : g.Basis :=
    Classical.choice (Equiv.Perm.Basis.nonempty g)
  let f : g.cycleFactorsFinset →
      MulAction.orbitRel.Quotient (Subgroup.zpowers g) Y :=
    fun c => Quotient.mk'' (a c)
  apply Equiv.ofBijective f
  constructor
  · intro c d hcd
    have hrel :
        MulAction.orbitRel (Subgroup.zpowers g) Y
          (a c) (a d) := by
      exact Quotient.exact hcd
    rw [MulAction.orbitRel_apply,
      MulAction.mem_orbit_iff] at hrel
    obtain ⟨z, hz⟩ := hrel
    obtain ⟨m, hm⟩ :=
      Subgroup.mem_zpowers_iff.mp z.prop
    apply Subtype.ext
    rw [← Equiv.Perm.Basis.cycleOf_eq a c,
      ← Equiv.Perm.Basis.cycleOf_eq a d]
    rw [← hz]
    change
      g.cycleOf ((z : Equiv.Perm Y) (a d)) =
        g.cycleOf (a d)
    rw [← hm, Equiv.Perm.cycleOf_self_apply_zpow]
  · intro q
    induction q using Quotient.inductionOn'
    rename_i x
    have hx : x ∈ g.support :=
      Equiv.Perm.mem_support.mpr (hfree x)
    have hfactor :
        g.cycleOf x ∈ g.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
    let c : g.cycleFactorsFinset :=
      ⟨g.cycleOf x, hfactor⟩
    refine ⟨c, ?_⟩
    apply Quotient.sound
    change a c ∈ MulAction.orbit (Subgroup.zpowers g) x
    rw [MulAction.mem_orbit_iff]
    obtain ⟨m, hm⟩ :=
      Equiv.Perm.Basis.sameCycle a hfactor
    let z : Subgroup.zpowers g :=
      ⟨g ^ m,
        (Subgroup.zpowers g).zpow_mem
          (Subgroup.mem_zpowers g) m⟩
    refine ⟨z⁻¹, ?_⟩
    change (g ^ m)⁻¹ x = a c
    rw [← hm]
    simp [c]

theorem card_orbitQuotient_eq_cycleType_card
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (g : Equiv.Perm Y)
    (hfree : ∀ x : Y, g x ≠ x) :
    Nat.card
        (MulAction.orbitRel.Quotient
          (Subgroup.zpowers g) Y) =
      g.cycleType.card := by
  classical
  calc
    Nat.card
          (MulAction.orbitRel.Quotient
            (Subgroup.zpowers g) Y) =
        Nat.card g.cycleFactorsFinset :=
      Nat.card_congr
        (cycleFactorsEquivOrbitQuotient g hfree).symm
    _ = g.cycleFactorsFinset.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = g.cycleType.card := by
      rw [Equiv.Perm.cycleType_def, Multiset.card_map]
      rfl

private theorem cycleType_prod_eq_prime_pow_card
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {g : Equiv.Perm Y} {p : ℕ}
    (hp : p.Prime) (horder : orderOf g = p) :
    g.cycleType.prod = p ^ g.cycleType.card := by
  obtain ⟨r, hr⟩ :=
    Equiv.Perm.cycleType_prime_order (horder ▸ hp)
  rw [horder] at hr
  rw [hr]
  simp [pow_succ, Nat.mul_comm]

private theorem cycleFactor_ker_card_eq_prime_pow
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {g : Equiv.Perm Y} {p : ℕ}
    (hp : p.Prime) (horder : orderOf g = p)
    (hsum : g.cycleType.sum = Fintype.card Y) :
    Nat.card (Equiv.Perm.OnCycleFactors.toPermHom g).ker =
      p ^ g.cycleType.card := by
  let C := Subgroup.centralizer ({g} : Set (Equiv.Perm Y))
  let K := (Equiv.Perm.OnCycleFactors.toPermHom g).ker
  have hmapCard : Nat.card (K.map C.subtype) = Nat.card K := by
    exact Nat.card_congr
      (K.equivMapOfInjective C.subtype C.subtype_injective).toEquiv.symm
  have hrangeCard :
      Nat.card (Equiv.Perm.OnCycleFactors.kerParam g).range =
        g.cycleType.prod := by
    rw [Nat.card_eq_fintype_card,
      Equiv.Perm.OnCycleFactors.kerParam_range_card,
      hsum]
    simp
  have hrangeEq :
      (Equiv.Perm.OnCycleFactors.kerParam g).range =
        K.map C.subtype := by
    simpa only [C, K] using
      (Equiv.Perm.OnCycleFactors.kerParam_range_eq (g := g))
  calc
    Nat.card K = Nat.card (K.map C.subtype) := hmapCard.symm
    _ = Nat.card (Equiv.Perm.OnCycleFactors.kerParam g).range := by
      rw [hrangeEq]
    _ = g.cycleType.prod := hrangeCard
    _ = p ^ g.cycleType.card :=
      cycleType_prod_eq_prime_pow_card hp horder

private theorem mem_cycle_support_iff_of_mem_zpowers_orbit
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {g c : Equiv.Perm Y} {x y : Y}
    (hc : c ∈ g.cycleFactorsFinset)
    (hxy : y ∈ MulAction.orbit (Subgroup.zpowers g) x) :
    y ∈ c.support ↔ x ∈ c.support := by
  rw [MulAction.mem_orbit_iff] at hxy
  obtain ⟨z, hz⟩ := hxy
  rw [← hz]
  obtain ⟨m, hm⟩ :=
    Subgroup.mem_zpowers_iff.mp z.prop
  change (z : Equiv.Perm Y) x ∈ c.support ↔
    x ∈ c.support
  rw [← hm]
  exact
    Equiv.Perm.zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff
      (g := g) (c := ⟨c, hc⟩)

private theorem normalizerOrbitHom_ker_isSolvable
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {g : Equiv.Perm Y} {p : ℕ}
    (hp : p.Prime)
    (horder : orderOf g = p)
    (hsum : g.cycleType.sum = Fintype.card Y) :
    Group.IsSolvable
      (normalizerOrbitHom (Subgroup.zpowers g)).ker := by
  classical
  let R : Subgroup (Equiv.Perm Y) := Subgroup.zpowers g
  let N : Subgroup (Equiv.Perm Y) :=
    Subgroup.normalizer (R : Set (Equiv.Perm Y))
  let ν :
      N →* Equiv.Perm (MulAction.orbitRel.Quotient R Y) :=
    normalizerOrbitHom R
  let K : Subgroup N := ν.ker
  let κ : K →* MulAut R :=
    R.normalizerMonoidHom.comp K.subtype
  let D : Subgroup K := κ.ker
  let cycleKer :=
    (Equiv.Perm.OnCycleFactors.toPermHom g).ker
  have hbaseMem :
      ∀ d : D,
        (((d : K) : N) : Equiv.Perm Y) ∈
          Subgroup.centralizer ({g} : Set (Equiv.Perm Y)) := by
    intro d
    have hdCentral :
        ((d : K) : N) ∈
          (Subgroup.centralizer
            (R : Set (Equiv.Perm Y))).subgroupOf N := by
      rw [← R.normalizerMonoidHom_ker]
      exact d.prop
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact
      (hdCentral g
        (show g ∈ R from Subgroup.mem_zpowers g)).symm
  let base :
      D →*
        Subgroup.centralizer ({g} : Set (Equiv.Perm Y)) :=
    (N.subtype.comp (K.subtype.comp D.subtype)).codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm Y)))
      hbaseMem
  have hν_apply_mk (d : D) (x : Y) :
      (Quotient.mk'' ((((d : K) : N) : Equiv.Perm Y) x) :
          MulAction.orbitRel.Quotient R Y) =
        Quotient.mk'' x := by
    have hdKer : ν (d : K) = 1 := (d : K).prop
    have happ :=
      congrFun (congrArg DFunLike.coe hdKer)
        (Quotient.mk'' x :
          MulAction.orbitRel.Quotient R Y)
    change
      normalizerOrbitHom R ((d : K) : N)
          (Quotient.mk'' x) =
        (1 : Equiv.Perm
          (MulAction.orbitRel.Quotient R Y))
            (Quotient.mk'' x) at happ
    simpa using happ
  have hbaseKer :
      ∀ d : D, base d ∈ cycleKer := by
    intro d
    rw [Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff]
    intro c hc
    let n : Equiv.Perm Y := (((d : K) : N) : Equiv.Perm Y)
    have hnSupport :
        ∀ x : Y, n x ∈ c.support ↔ x ∈ c.support := by
      intro x
      apply mem_cycle_support_iff_of_mem_zpowers_orbit hc
      have horbit :
          n x ∈
            MulAction.orbitRel.Quotient.orbit
              (Quotient.mk'' x :
                MulAction.orbitRel.Quotient R Y) :=
        MulAction.orbitRel.Quotient.mem_orbit.mpr
          (by simpa only [n] using hν_apply_mk d x)
      simpa only [MulAction.orbitRel.Quotient.orbit_mk, R] using
        horbit
    have hnCommuteG : Commute n g := by
      exact
        Subgroup.mem_centralizer_singleton_iff.mp
          (base d).prop
    apply Equiv.ext
    intro x
    change n (c x) = c (n x)
    by_cases hx : x ∈ c.support
    · have hnx : n x ∈ c.support := (hnSupport x).2 hx
      have hcx :
          c x = g x :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 x hx
      have hcnx :
          c (n x) = g (n x) :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2
          (n x) hnx
      rw [hcx, hcnx]
      exact
        congrFun (congrArg DFunLike.coe hnCommuteG.eq) x
    · have hnx : n x ∉ c.support := by
        simpa only [hnSupport x] using hx
      have hcx : c x = x :=
        not_ne_iff.mp
          (show ¬c x ≠ x by
            simpa only [Equiv.Perm.mem_support] using hx)
      have hcnx : c (n x) = n x :=
        not_ne_iff.mp
          (show ¬c (n x) ≠ n x by
            simpa only [Equiv.Perm.mem_support] using hnx)
      rw [hcx, hcnx]
  let rotateMap : D →* cycleKer :=
    base.codRestrict cycleKer hbaseKer
  have hrotateInjective : Function.Injective rotateMap := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : cycleKer =>
        (((z : Subgroup.centralizer
          ({g} : Set (Equiv.Perm Y))) : Equiv.Perm Y))) hab
  letI : Fact p.Prime := ⟨hp⟩
  have hcycleKerP : IsPGroup p cycleKer := by
    apply IsPGroup.of_card
    exact cycleFactor_ker_card_eq_prime_pow hp horder hsum
  have hDP : IsPGroup p D :=
    hcycleKerP.of_injective rotateMap hrotateInjective
  letI : Group.IsNilpotent D := hDP.isNilpotent
  letI : Group.IsSolvable D :=
    IsNilpotent.to_isSolvable
  letI : Group.IsSolvable (MulAut R) := by
    exact
      Group.isSolvable_of_isSolvable_injective
        (f := (IsCyclic.mulAutMulEquiv R).toMonoidHom)
        (IsCyclic.mulAutMulEquiv R).injective
  have hKsolvable : Group.IsSolvable K := by
    apply Group.isSolvable_of_ker_le_range D.subtype κ
    intro d hd
    exact ⟨⟨d, hd⟩, rfl⟩
  simpa only [R, N, ν, K] using hKsolvable

theorem orbitHomOfLeNormalizer_ker_isSolvable
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {g : Equiv.Perm Y} {p : ℕ}
    (K : Subgroup (Equiv.Perm Y))
    (hK :
      K ≤ Subgroup.normalizer
        (Subgroup.zpowers g : Set (Equiv.Perm Y)))
    (hp : p.Prime)
    (horder : orderOf g = p)
    (hsum : g.cycleType.sum = Fintype.card Y) :
    Group.IsSolvable
      (orbitHomOfLeNormalizer (Subgroup.zpowers g) K hK).ker := by
  classical
  let R : Subgroup (Equiv.Perm Y) := Subgroup.zpowers g
  let N : Subgroup (Equiv.Perm Y) :=
    Subgroup.normalizer (R : Set (Equiv.Perm Y))
  let inclusion : K →* N :=
    K.subtype.codRestrict N (fun x => hK x.prop)
  let ν :
      N →* Equiv.Perm (MulAction.orbitRel.Quotient R Y) :=
    normalizerOrbitHom R
  let orbitMap :
      K →* Equiv.Perm (MulAction.orbitRel.Quotient R Y) :=
    orbitHomOfLeNormalizer R K hK
  let D : Subgroup K := orbitMap.ker
  let toFull :
      D →* ν.ker :=
    (inclusion.comp D.subtype).codRestrict ν.ker (by
      intro d
      change ν (inclusion (d : K)) = 1
      exact d.prop)
  have htoFullInjective : Function.Injective toFull := by
    intro a b hab
    apply Subtype.ext
    apply K.subtype_injective
    exact congrArg
      (fun z : ν.ker => ((z : N) : Equiv.Perm Y)) hab
  letI : Group.IsSolvable ν.ker := by
    simpa only [R, N, ν] using
      normalizerOrbitHom_ker_isSolvable hp horder hsum
  have hDsolvable : Group.IsSolvable D :=
    Group.isSolvable_of_isSolvable_injective
      htoFullInjective
  simpa only [R, orbitMap, D] using hDsolvable

end FiveTransitive.CyclicNormalizerOrbitAction

end CFSG
