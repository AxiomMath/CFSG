module

public import CFSG.Permutation.FiveTransitive.CyclicNormalizerOrbitAction
public import CFSG.Permutation.FiveTransitive.Helpers
public import Mathlib.GroupTheory.IsPerfect
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.SolvableOrbitGoursat

open Subgroup

private theorem simple_subgroup_le_goursatFst_of_solvable
    (A B : Type) [Group A] [Group B] [Finite A] [Finite B]
    [Group.IsSolvable B]
    (I : Subgroup (A × B))
    (hfst : Function.Surjective (Prod.fst ∘ I.subtype))
    (hsnd : Function.Surjective (Prod.snd ∘ I.subtype))
    (Q : Subgroup A) [IsSimpleGroup Q]
    (hQnonsolvable : ¬Group.IsSolvable Q) :
    Q ≤ I.goursatFst := by
  let M : Subgroup A := I.goursatFst
  let N : Subgroup B := I.goursatSnd
  letI : M.Normal := by
    dsimp only [M]
    exact Subgroup.normal_goursatFst hfst
  letI : N.Normal := by
    dsimp only [N]
    exact Subgroup.normal_goursatSnd hsnd
  let K : Subgroup Q := M.comap Q.subtype
  letI : K.Normal := by
    dsimp only [K]
    exact Subgroup.Normal.comap inferInstance Q.subtype
  rcases (inferInstance : K.Normal).eq_bot_or_eq_top with hKbot | hKtop
  · let qmap : Q →* A ⧸ M :=
      (QuotientGroup.mk' M).comp Q.subtype
    have hqmapKer : qmap.ker = ⊥ := by
      ext q
      rw [MonoidHom.mem_ker]
      change
        ((QuotientGroup.mk' M) (q : A) = 1) ↔
          q ∈ (⊥ : Subgroup Q)
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      change q ∈ K ↔ q ∈ (⊥ : Subgroup Q)
      rw [hKbot]
    have hqmapInjective : Function.Injective qmap := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact hqmapKer
    obtain ⟨e, _⟩ := Subgroup.goursat_surjective hfst hsnd
    let qmapB : Q →* B ⧸ N := e.toMonoidHom.comp qmap
    have hqmapBInjective : Function.Injective qmapB :=
      e.injective.comp hqmapInjective
    have hQsolvable : Group.IsSolvable Q :=
      Group.isSolvable_of_isSolvable_injective hqmapBInjective
    exact (hQnonsolvable hQsolvable).elim
  · intro q hq
    have hqK : (⟨q, hq⟩ : Q) ∈ K := by
      rw [hKtop]
      exact Subgroup.mem_top _
    exact hqK

theorem exists_lift_with_solvable_aux_eq_one
    (L A B : Type) [Group L] [Group A] [Group B]
    [Finite L] [Finite A] [Finite B] [Group.IsSolvable B]
    (f : L →* A) (g : L →* B)
    (Q : Subgroup A) [IsSimpleGroup Q]
    (hQ : Q ≤ f.range)
    (hQnonsolvable : ¬Group.IsSolvable Q)
    (q : A) (hq : q ∈ Q) :
    ∃ l : L, f l = q ∧ g l = 1 := by
  let J : Subgroup A := f.range
  let R : Subgroup B := g.range
  let fJ : L →* J := f.rangeRestrict
  let gR : L →* R := g.rangeRestrict
  let pair : L →* J × R := fJ.prod gR
  let I : Subgroup (J × R) := pair.range
  have hfst : Function.Surjective (Prod.fst ∘ I.subtype) := by
    intro j
    obtain ⟨l, hl⟩ := j.prop
    let i : I := ⟨pair l, ⟨l, rfl⟩⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hl
  have hsnd : Function.Surjective (Prod.snd ∘ I.subtype) := by
    intro r
    obtain ⟨l, hl⟩ := r.prop
    let i : I := ⟨pair l, ⟨l, rfl⟩⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hl
  let QJ : Subgroup J := Q.subgroupOf J
  letI : IsSimpleGroup QJ :=
    (Subgroup.subgroupOfEquivOfLe hQ).isSimpleGroup
  have hQJnonsolvable : ¬Group.IsSolvable QJ := by
    intro hsolvable
    letI : Group.IsSolvable QJ := hsolvable
    apply hQnonsolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ).symm.injective
  have hQJle : QJ ≤ I.goursatFst := by
    apply simple_subgroup_le_goursatFst_of_solvable
      J R I hfst hsnd QJ hQJnonsolvable
  let qJ : J := ⟨q, hQ hq⟩
  have hqJ : qJ ∈ QJ := hq
  have hqFirst : qJ ∈ I.goursatFst := hQJle hqJ
  have hpair : (qJ, (1 : R)) ∈ I :=
    I.goursatFst_prod_goursatSnd_le
      ⟨hqFirst, Subgroup.one_mem _⟩
  obtain ⟨l, hl⟩ := hpair
  refine ⟨l, ?_, ?_⟩
  · have hfirst := congrArg (fun z : J × R => z.1) hl
    exact congrArg Subtype.val hfirst
  · have hsecond := congrArg (fun z : J × R => z.2) hl
    exact congrArg Subtype.val hsecond

theorem exists_lift_with_solvable_kernel_small_range
    (L A B C : Type) [Group L] [Group A] [Group B] [Group C]
    [Finite L] [Finite A] [Finite B] [Finite C]
    (f : L →* A) (g : L →* B) (h : B →* C)
    [Group.IsSolvable h.ker]
    (Q : Subgroup A) [IsSimpleGroup Q]
    (hQ : Q ≤ f.range)
    (hQnonsolvable : ¬Group.IsSolvable Q)
    (hsmall : Nat.card (h.comp g).range < Nat.card Q)
    (q : A) (hq : q ∈ Q) :
    ∃ l : L, f l = q ∧ g l = 1 := by
  let D : Subgroup L := (h.comp g).ker
  let fD : D →* A := f.comp D.subtype
  let gDBase : D →* B := g.comp D.subtype
  have hgDmem : ∀ d : D, gDBase d ∈ h.ker := by
    intro d
    exact d.prop
  let gD : D →* h.ker := gDBase.codRestrict h.ker hgDmem
  have hQD : Q ≤ fD.range := by
    intro a ha
    obtain ⟨l, hfl, haux⟩ :=
      FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one
        L A C f (h.comp g) Q hQ hsmall a ha
    let d : D := ⟨l, haux⟩
    exact ⟨d, hfl⟩
  obtain ⟨d, hfd, hgd⟩ :=
    exists_lift_with_solvable_aux_eq_one
      D A h.ker fD gD Q hQD hQnonsolvable q hq
  refine ⟨(d : L), hfd, ?_⟩
  exact congrArg Subtype.val hgd

open MulAction SubMulAction

private theorem alternatingGroup_le_of_invariant_fixed_action_of_solvable_orbit_kernel
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (N : Subgroup P) (F FC : SubMulAction N X) [Fintype F]
    (hFC : FC = Fᶜ)
    (hfive : 5 ≤ Fintype.card F)
    (C : Type) [Group C] [Finite C]
    (orbitMap :
      (MulAction.toPermHom N FC).range →* C)
    (horbitKernel : Group.IsSolvable orbitMap.ker)
    (hAlt :
      alternatingGroup F ≤
        (MulAction.toPermHom N F).range)
    (hsmall :
      Nat.card
          (orbitMap.comp
            (MulAction.toPermHom N FC).rangeRestrict).range <
        Nat.card (alternatingGroup F)) :
    alternatingGroup X ≤ P := by
  classical
  let ρ : N →* Equiv.Perm F := MulAction.toPermHom N F
  let τ : N →* Equiv.Perm FC := MulAction.toPermHom N FC
  letI : Group.IsSolvable orbitMap.ker := horbitKernel
  have hAlt' : alternatingGroup F ≤ ρ.range := by
    simpa only [ρ] using hAlt
  have hsmall' :
      Nat.card (orbitMap.comp τ.rangeRestrict).range <
        Nat.card (alternatingGroup F) := by
    simpa only [τ] using hsmall
  letI : IsSimpleGroup (alternatingGroup F) :=
    alternatingGroup.isSimpleGroup (by
      simpa only [Nat.card_eq_fintype_card] using hfive)
  letI : Group.IsPerfect (alternatingGroup F) := by
    rw [Group.isPerfect_def]
    exact commutator_alternatingGroup_eq_top (by
      simpa only [Nat.card_eq_fintype_card] using hfive)
  have hAltNonsolvable :
      ¬Group.IsSolvable (alternatingGroup F) :=
    Group.IsPerfect.not_isSolvable _
  have hthreeCard : 3 ≤ Fintype.card F := by omega
  let e : Fin 3 ↪ F :=
    Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr (by
        rw [Fintype.card_fin]
        exact hthreeCard))
  have heZeroOne : e 0 ≠ e 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (e.injective h)
  have heZeroTwo : e 0 ≠ e 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (e.injective h)
  have heOneTwo : e 1 ≠ e 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (e.injective h)
  let q : Equiv.Perm F :=
    Equiv.swap (e 0) (e 1) * Equiv.swap (e 0) (e 2)
  have hqThree : q.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same
      heZeroOne heZeroTwo heOneTwo
  have hqAlt : q ∈ alternatingGroup F :=
    hqThree.mem_alternatingGroup
  obtain ⟨n, hnFixed, hnComplementRange⟩ :=
    exists_lift_with_solvable_kernel_small_range
      N (Equiv.Perm F) τ.range C
        ρ τ.rangeRestrict orbitMap
        (alternatingGroup F) hAlt' hAltNonsolvable
        hsmall' q hqAlt
  have hnComplement : τ n = 1 :=
    congrArg Subtype.val hnComplementRange
  let nP : P := n
  let nPerm : Equiv.Perm X := nP
  have hnSupportSubset : (nPerm.support : Set X) ⊆ F := by
    intro x hx
    by_contra hxF
    have hxFC : x ∈ FC := by
      rw [hFC]
      exact hxF
    let y : FC := ⟨x, hxFC⟩
    have happ :=
      congrFun (congrArg DFunLike.coe hnComplement) y
    have hfix : nPerm x = x := congrArg Subtype.val happ
    exact Equiv.Perm.mem_support.mp hx hfix
  let valEmbedding : F ↪ X := Function.Embedding.subtype _
  have hsupportMap :
      Finset.map valEmbedding q.support = nPerm.support := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      apply Equiv.Perm.mem_support.mp hy
      have happ := congrFun (congrArg DFunLike.coe hnFixed) y
      apply Subtype.ext
      exact congrArg Subtype.val
        (happ.symm.trans (Subtype.ext hfix))
    · intro hx
      have hxF : x ∈ F := hnSupportSubset hx
      let y : F := ⟨x, hxF⟩
      rw [Finset.mem_map]
      refine ⟨y, ?_, rfl⟩
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      apply Equiv.Perm.mem_support.mp hx
      have happ := congrFun (congrArg DFunLike.coe hnFixed) y
      exact congrArg Subtype.val (happ.trans hfix)
  have hnSupportCard : nPerm.support.card = 3 := by
    calc
      nPerm.support.card =
          (Finset.map valEmbedding q.support).card := by
            rw [hsupportMap]
      _ = q.support.card := Finset.card_map valEmbedding
      _ = 3 := hqThree.card_support
  have hnNe : nPerm ≠ 1 := by
    intro hnOne
    rw [hnOne, Equiv.Perm.support_one] at hnSupportCard
    norm_num at hnSupportCard
  apply
    FiveTransitive.Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 hdegree nP.prop hnNe
  change nPerm.support.card ≤ 5
  omega

private theorem alternatingGroup_le_of_prime_cyclic_complement_orbits
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (N : Subgroup P) (F FC : SubMulAction N X)
    [Fintype F] [Fintype FC]
    (hFC : FC = Fᶜ)
    (hfive : 5 ≤ Fintype.card F)
    {g : Equiv.Perm FC} {p : ℕ}
    (hp : p.Prime)
    (horder : orderOf g = p)
    (hsum : g.cycleType.sum = Fintype.card FC)
    (hnormalizes :
      (MulAction.toPermHom N FC).range ≤
        Subgroup.normalizer
          (Subgroup.zpowers g : Set (Equiv.Perm FC)))
    (hAlt :
      alternatingGroup F ≤
        (MulAction.toPermHom N F).range)
    (horbits :
      Nat.card
          (MulAction.orbitRel.Quotient
            (Subgroup.zpowers g) FC) <
        Fintype.card F) :
    alternatingGroup X ≤ P := by
  classical
  let Ω :=
    MulAction.orbitRel.Quotient (Subgroup.zpowers g) FC
  letI : Fintype Ω := Fintype.ofFinite Ω
  let orbitMap :
      (MulAction.toPermHom N FC).range →*
        Equiv.Perm Ω :=
    FiveTransitive.CyclicNormalizerOrbitAction.orbitHomOfLeNormalizer
      (Subgroup.zpowers g)
      (MulAction.toPermHom N FC).range
      hnormalizes
  have horbitKernel : Group.IsSolvable orbitMap.ker := by
    simpa only [Ω, orbitMap] using
      (FiveTransitive.CyclicNormalizerOrbitAction.orbitHomOfLeNormalizer_ker_isSolvable
          (MulAction.toPermHom N FC).range
          hnormalizes hp horder hsum)
  have horbits' : Fintype.card Ω < Fintype.card F := by
    simpa only [Ω, Nat.card_eq_fintype_card] using horbits
  have hnontrivialF : Nontrivial F :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial F := hnontrivialF
  have horbitFactorialLe :
      (Fintype.card Ω).factorial ≤
        (Fintype.card F - 1).factorial :=
    Nat.factorial_le (by omega)
  have hfactorialEq :
      (Fintype.card F).factorial =
        Fintype.card F * (Fintype.card F - 1).factorial := by
    have hfSucc :
        Fintype.card F = (Fintype.card F - 1) + 1 := by
      omega
    rw [hfSucc, Nat.factorial_succ]
    simp
  have hfactorialPos :
      0 < (Fintype.card F - 1).factorial :=
    Nat.factorial_pos _
  have htwiceAlt :
      2 * Nat.card (alternatingGroup F) =
        (Fintype.card F).factorial := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using
      (two_mul_nat_card_alternatingGroup (α := F))
  have horbitFactorialLtAlt :
      (Fintype.card Ω).factorial <
        Nat.card (alternatingGroup F) := by
    by_contra hnot
    have hAltLeOrbit :
        Nat.card (alternatingGroup F) ≤
          (Fintype.card Ω).factorial :=
      Nat.le_of_not_gt hnot
    have hAltLePrevious :
        Nat.card (alternatingGroup F) ≤
          (Fintype.card F - 1).factorial :=
      hAltLeOrbit.trans horbitFactorialLe
    have htwiceLe :
        2 * Nat.card (alternatingGroup F) ≤
          2 * (Fintype.card F - 1).factorial :=
      Nat.mul_le_mul_left 2 hAltLePrevious
    have htwiceLt :
        2 * (Fintype.card F - 1).factorial <
          Fintype.card F * (Fintype.card F - 1).factorial :=
      Nat.mul_lt_mul_of_pos_right (by omega) hfactorialPos
    have hcontra := htwiceLe.trans_lt htwiceLt
    rw [htwiceAlt, ← hfactorialEq] at hcontra
    exact Nat.lt_irrefl _ hcontra
  have horbitRangeLe :
      Nat.card
          (orbitMap.comp
            (MulAction.toPermHom N FC).rangeRestrict).range ≤
        (Fintype.card Ω).factorial := by
    calc
      Nat.card
          (orbitMap.comp
            (MulAction.toPermHom N FC).rangeRestrict).range ≤
          Nat.card (Equiv.Perm Ω) :=
        Nat.le_of_dvd Nat.card_pos
          (Subgroup.card_subgroup_dvd_card _)
      _ = (Fintype.card Ω).factorial := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card]
  apply
    alternatingGroup_le_of_invariant_fixed_action_of_solvable_orbit_kernel
      X P hdegree h5 N F FC hFC hfive
        (Equiv.Perm Ω) orbitMap horbitKernel hAlt
  exact horbitRangeLe.trans_lt horbitFactorialLtAlt

theorem alternatingGroup_le_of_prime_cyclic_complement_cycle_count
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (N : Subgroup P) (F FC : SubMulAction N X)
    [Fintype F] [Fintype FC]
    (hFC : FC = Fᶜ)
    (hfive : 5 ≤ Fintype.card F)
    {g : Equiv.Perm FC} {p : ℕ}
    (hp : p.Prime)
    (horder : orderOf g = p)
    (hfree : ∀ x : FC, g x ≠ x)
    (hnormalizes :
      (MulAction.toPermHom N FC).range ≤
        Subgroup.normalizer
          (Subgroup.zpowers g : Set (Equiv.Perm FC)))
    (hAlt :
      alternatingGroup F ≤
        (MulAction.toPermHom N F).range)
    (hcycles : g.cycleType.card < Fintype.card F) :
    alternatingGroup X ≤ P := by
  classical
  have hsupport : g.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ,
      iff_true]
    exact hfree x
  have hsum :
      g.cycleType.sum = Fintype.card FC := by
    rw [g.sum_cycleType, hsupport, Finset.card_univ]
  have horbits :
      Nat.card
          (MulAction.orbitRel.Quotient
            (Subgroup.zpowers g) FC) <
        Fintype.card F := by
    rw [FiveTransitive.CyclicNormalizerOrbitAction.card_orbitQuotient_eq_cycleType_card
      g hfree]
    exact hcycles
  exact
    alternatingGroup_le_of_prime_cyclic_complement_orbits
      X P hdegree h5 N F FC hFC hfive hp horder hsum
        hnormalizes hAlt horbits

end FiveTransitive.SolvableOrbitGoursat

end CFSG
