module

public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.ZMod.Torsion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.BlockElementaryMap
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.CyclicQuotientExtension
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Unbundled
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SolvableDimension
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.PrimitiveRootEigenspaces

namespace CFSG
end CFSG
open CFSG

open _root_.Representation
open Theory.Representation
open MonoidAlgebra
open Module
open Module.End
open Polynomial
open scoped DirectSum
open scoped BigOperators
open scoped TensorProduct
open scoped MonoidAlgebra
open scoped Function
open scoped commutatorElement
/-
**Kind**: Theorem
**Note**: Theorem 2.5
**Stmt**:
Let $P$ be an extraspecial $p$-group of order $p^{2n+1}$ for some prime $p$.
Let $H$ be a cyclic group of order $h$, and $h$ is relatively prime to $p$.
Let $G$ be the semidirect product of $P$ (which is normal) and a cyclic group $H$ of order $h$.
If $C_P(x) = Z(P)$ for all $x \in H^\#$.
Then $h$ divides $p^n + 1$ or $p^n - 1$.
If $h \ne p^n + 1$ in addition.
Let $F$ be a field such that $\char F$ does not divide $|G|$.
Then every finite dimensional, faithful, irreducible $FG$-module $V$ satisfies $C_V(H) \ne 0$.
-/

theorem CFSG.invariants_eq_bot_iff_fixedVectors_eq_zero
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (H : Subgroup G) :
    Representation.invariants (ρ.comp H.subtype) = ⊥ ↔
      {v : V | ∀ h : H, (ρ.comp H.subtype) h v = v} = {0} := by
  constructor
  · intro hbot
    ext v
    constructor
    · intro hv
      have hv' : v ∈ Representation.invariants (ρ.comp H.subtype) := by
        simpa [Representation.mem_invariants] using hv
      have hv0 : v ∈ (⊥ : Submodule F V) := by simpa [hbot] using hv'
      simpa using hv0
    · intro hv0 h
      have hv : v = 0 := by simpa using hv0
      simp [hv]
  · intro hfix
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv' : ∀ h : H, ρ h v = v := by
      simpa [Representation.mem_invariants] using hv
    have hv0 : v ∈ ({0} : Set V) := by
      rw [← hfix]
      exact hv'
    simpa using hv0

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.le_ker_of_forall_simple_submodule_le_ker {G : Type*} [Group G] {F : Type*}
    [Field F] {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule] (H : Subgroup G)
    (hsimple :
      ∀ m : Submodule (MonoidAlgebra F G) ρ.asModule, IsSimpleModule (MonoidAlgebra F G) m →
        H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker) :
    H ≤ ρ.ker := by
  classical
  intro h hh
  rw [MonoidHom.mem_ker]
  ext v
  let v' : ρ.asModule := ρ.asModuleEquiv.symm v
  have hv :
      v' ∈ sSup
        {m : Submodule (MonoidAlgebra F G) ρ.asModule |
          IsSimpleModule (MonoidAlgebra F G) m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    trivial
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_sSup_iff_exists_finset.mp hv
  have hsfix :
      ∀ s : Finset (Submodule (MonoidAlgebra F G) ρ.asModule),
        ↑s ⊆ {m : Submodule (MonoidAlgebra F G) ρ.asModule |
          IsSimpleModule (MonoidAlgebra F G) m} →
        ∀ x : ρ.asModule, x ∈ ⨆ m ∈ s, m → ρ h (ρ.asModuleEquiv x) = ρ.asModuleEquiv x := by
    intro s hs' x hx
    induction s using Finset.induction_on generalizing x with
    | empty =>
        simp at hx
        simp [hx]
    | @insert q t hqt ih =>
        rw [Finset.iSup_insert] at hx
        have hx' : x ∈ q ⊔ ⨆ m ∈ t, m := by
          simpa [hqt] using hx
        obtain ⟨xq, hxq, xt, hxt, rfl⟩ := Submodule.mem_sup.mp hx'
        have hq_simple : IsSimpleModule (MonoidAlgebra F G) q := hs' (Finset.mem_insert_self q t)
        have hq_fix : ρ h (ρ.asModuleEquiv xq) = ρ.asModuleEquiv xq := by
          have hhq : h ∈ (Subrepresentation.ofSubmodule' q).toRepresentation.ker :=
            hsimple q hq_simple hh
          rw [MonoidHom.mem_ker] at hhq
          have hhq' :
              ((Subrepresentation.ofSubmodule' q).toRepresentation h) ⟨xq, hxq⟩ =
                ⟨xq, hxq⟩ := by
            simpa using congrArg (fun f => f ⟨xq, hxq⟩) hhq
          have hhq'' := congrArg Subtype.val hhq'
          change ρ h (ρ.asModuleEquiv xq) = ρ.asModuleEquiv xq
          exact hhq''
        have ht_fix : ρ h (ρ.asModuleEquiv xt) = ρ.asModuleEquiv xt :=
          ih (by
            intro m hm
            exact hs' (Finset.mem_insert_of_mem hm)) xt hxt
        calc
          ρ h (ρ.asModuleEquiv (xq + xt))
              = ρ h (ρ.asModuleEquiv xq + ρ.asModuleEquiv xt) := by simp
          _ = ρ h (ρ.asModuleEquiv xq) + ρ h (ρ.asModuleEquiv xt) := by simp
          _ = ρ.asModuleEquiv xq + ρ.asModuleEquiv xt := by simp [hq_fix, ht_fix]
          _ = ρ.asModuleEquiv (xq + xt) := by simp
  simpa [v'] using hsfix s hs v' hvs

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.exists_simple_submodule_nontrivial_of_not_le_ker {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule] (H : Subgroup G) (hH : ¬ H ≤ ρ.ker) :
    ∃ m : Submodule (MonoidAlgebra F G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra F G) m ∧
      ¬ H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker := by
  by_contra hcontra
  push Not at hcontra
  exact hH (le_ker_of_forall_simple_submodule_le_ker (ρ := ρ) H hcontra)

theorem CFSG.invariants_ofSubmodule'_eq_bot_of_invariants_eq_bot {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (R : Subgroup G)
    (m : Submodule (MonoidAlgebra F G) ρ.asModule)
    (hfix : Representation.invariants (ρ.comp R.subtype) = ⊥) :
    Representation.invariants ((Subrepresentation.ofSubmodule' m).toRepresentation.comp R.subtype) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  apply Subtype.ext
  have hv' : ((v : m) : V) ∈ Representation.invariants (ρ.comp R.subtype) := by
    rw [Representation.mem_invariants] at hv ⊢
    intro r
    exact congrArg Subtype.val (hv r)
  rw [hfix] at hv'
  simpa using hv'

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.irreducible_of_ofSubmodule'_simple {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    {m : Submodule (MonoidAlgebra F G) ρ.asModule}
    (hm : IsSimpleModule (MonoidAlgebra F G) m) :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' m).toRepresentation := by
  rw [Subrepresentation.irreducible_iff_isAtom]
  exact
    ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm.isAtom_iff
      (a := m)).2 <| (isSimpleModule_iff_isAtom).1 hm

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.finiteDimensional_of_irreducible_finite_group
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hirr : Representation.IsIrreducible ρ) :
    FiniteDimensional F V := by
  let : IsSimpleModule (MonoidAlgebra F G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Nontrivial ρ.asModule :=
    Function.Injective.nontrivial (f := ρ.asModuleEquiv.symm)
      (LinearEquiv.injective ρ.asModuleEquiv.symm)
  let : Module.Finite (MonoidAlgebra F G) ρ.asModule := by
    obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
    exact
      Module.Finite.of_surjective
        (LinearMap.toSpanSingleton (MonoidAlgebra F G) ρ.asModule v)
        ((isSimpleModule_iff_toSpanSingleton_surjective.mp inferInstance).2 v hv)
  let : Module.Finite F ρ.asModule :=
    Module.Finite.trans (R := F) (A := MonoidAlgebra F G) (M := ρ.asModule)
  exact Module.Finite.equiv (ρ.asModuleEquiv : ρ.asModule ≃ₗ[F] V)

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.exists_simple_submodule_nontrivial_of_not_le_ker_of_fixedSubspace_eq_bot
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule]
    (R H : Subgroup G) (hfix : Representation.invariants (ρ.comp R.subtype) = ⊥)
    (hH : ¬ H ≤ ρ.ker) :
    ∃ m : Submodule (MonoidAlgebra F G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra F G) m ∧
      (Representation.invariants ((Subrepresentation.ofSubmodule' m).toRepresentation.comp R.subtype) = ⊥) ∧
      ¬ H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker := by
  obtain ⟨m, hm, hHmk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker (ρ := ρ) H hH
  exact ⟨m, hm, invariants_ofSubmodule'_eq_bot_of_invariants_eq_bot ρ R m hfix, hHmk⟩

public theorem CFSG.commutator_le_center_of_isExtraspecial_local
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K] :
    commutator K ≤ Subgroup.center K := by
  let : IsMulCommutative (K ⧸ Subgroup.center K) :=
    (IsExtraspecial.quotient_elementary_abelian q K).toIsMulCommutative
  exact
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Subgroup.center K)).mp
      inferInstance

public theorem CFSG.center_le_of_le_center_ne_bot_of_prime_center_local
    {K : Type*} [Group K] [Finite K] {q : ℕ} [Fact q.Prime]
    (hcenter : Nat.card (Subgroup.center K) = q)
    {S : Subgroup K} (hS_le : S ≤ Subgroup.center K) (hS_ne_bot : S ≠ ⊥) :
    Subgroup.center K ≤ S := by
  have hS_card_dvd : Nat.card S ∣ Nat.card (Subgroup.center K) := by
    rw [← natCard_subgroupOf_eq S (Subgroup.center K) hS_le]
    exact Subgroup.card_subgroup_dvd_card (S.subgroupOf (Subgroup.center K))
  rw [hcenter] at hS_card_dvd
  have hS_card_ne_one : Nat.card S ≠ 1 := by
    intro hS_card
    exact hS_ne_bot ((Subgroup.eq_bot_iff_card (H := S)).2 hS_card)
  have hS_card_eq : Nat.card S = q := by
    rcases (Nat.dvd_prime Fact.out).1 hS_card_dvd with hS_card_one | hS_card_q
    · exact False.elim (hS_card_ne_one hS_card_one)
    · exact hS_card_q
  have hEq : S = Subgroup.center K := by
    apply Subgroup.eq_of_le_of_card_ge hS_le
    rw [hcenter, hS_card_eq]
  exact hEq.symm.le

private theorem CFSG.center_le_of_normal_ne_bot_of_commutator_le_center_of_prime_center_local
    {K : Type*} [Group K] [Finite K] {q : ℕ} [Fact q.Prime]
    (hcomm : commutator K ≤ Subgroup.center K)
    (hcenter : Nat.card (Subgroup.center K) = q)
    {N : Subgroup K} [N.Normal] (hN_ne_bot : N ≠ ⊥) :
    Subgroup.center K ≤ N := by
  by_cases hN_center : N ≤ Subgroup.center K
  · exact
      center_le_of_le_center_ne_bot_of_prime_center_local hcenter hN_center hN_ne_bot
  · let C : Subgroup K := ⁅N, (⊤ : Subgroup K)⁆
    have hC_le_N : C ≤ N := by
      exact Subgroup.commutator_le_left (H₁ := N) (H₂ := (⊤ : Subgroup K))
    have hC_le_center : C ≤ Subgroup.center K := by
      exact
        (Subgroup.commutator_mono (show N ≤ (⊤ : Subgroup K) by exact le_top) le_rfl).trans
          hcomm
    have hC_ne_bot : C ≠ ⊥ := by
      intro hC_eq_bot
      have hN_le_center : N ≤ Subgroup.center K := by
        have hN_le_centralizer : N ≤ Subgroup.centralizer ((⊤ : Subgroup K) : Set K) := by
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hC_eq_bot
        simpa [Subgroup.centralizer_univ] using hN_le_centralizer
      exact hN_center hN_le_center
    exact
      le_trans
        (center_le_of_le_center_ne_bot_of_prime_center_local hcenter hC_le_center hC_ne_bot)
        hC_le_N

private lemma CFSG.commutatorElement_mem_center_of_commutator_le_center_local
    {G : Type*} [Group G] (hcomm : commutator G ≤ Subgroup.center G) (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.center G := by
  exact
    hcomm <|
      Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
        (show x ∈ (⊤ : Subgroup G) by trivial) (show y ∈ (⊤ : Subgroup G) by trivial)

theorem CFSG.ker_eq_bot_of_center_not_le_ker_of_isExtraspecial
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F K V) (hcenter_nontrivial : ¬ Subgroup.center K ≤ ρ.ker) :
    ρ.ker = ⊥ := by
  by_contra hker
  have hcenter_le_ker : Subgroup.center K ≤ ρ.ker := by
    exact
      center_le_of_normal_ne_bot_of_commutator_le_center_of_prime_center_local
        (K := K)
        (hcomm := commutator_le_center_of_isExtraspecial_local (q := q) (K := K))
        (hcenter := IsExtraspecial.center_order_p q K) (N := ρ.ker) hker
  exact hcenter_nontrivial hcenter_le_ker

set_option backward.isDefEq.respectTransparency false in
theorem CFSG.center_apply_eq_smul_id_of_irreducible
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsIrreducible ρ]
    {z : G} (hz : z ∈ Subgroup.center G) :
    ∃ a : F, (ρ z : Module.End F V) = a • 1 := by
  let φ := Representation.IntertwiningMap.centralMul (ρ := ρ) z (by
    rw [Submonoid.mem_center_iff]
    intro g
    exact (Subgroup.mem_center_iff.mp hz) g)
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective φ
  refine ⟨a, ?_⟩
  have hlin :
      ((algebraMap F (Representation.IntertwiningMap ρ ρ) a :
          Representation.IntertwiningMap ρ ρ) : Module.End F V) =
        (φ : Module.End F V) := by
    simpa using congrArg (fun f : Representation.IntertwiningMap ρ ρ => (f : Module.End F V)) ha
  calc
    (ρ z : Module.End F V) = (φ : Module.End F V) := rfl
    _ = ((algebraMap F (Representation.IntertwiningMap ρ ρ) a :
        Representation.IntertwiningMap ρ ρ) : Module.End F V) := hlin.symm
    _ = a • (1 : Module.End F V) := by
      ext v
      simp [Representation.IntertwiningMap.algebraMap_apply, LinearMap.smul_apply]

theorem CFSG.span_range_eq_top_of_irreducible_isAlgClosed
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsIrreducible ρ] :
    Submodule.span F (Set.range (ρ : G → Module.End F V)) = ⊤ := by
  have htop : Algebra.adjoin F (Set.range (ρ : G → Module.End F V)) = ⊤ :=
    jacobson_density_surjective_isAlgClosed_rep ρ
  have hspan :
      Subalgebra.toSubmodule (Algebra.adjoin F (Set.range (ρ : G → Module.End F V))) =
        Submodule.span F (Set.range (ρ : G → Module.End F V)) := by
    simpa [MonoidHom.mclosure_range (ρ : G →* Module.End F V), MonoidHom.coe_mrange] using
      (Algebra.adjoin_eq_span (R := F) (s := Set.range (ρ : G → Module.End F V)))
  calc
    Submodule.span F (Set.range (ρ : G → Module.End F V))
        = Subalgebra.toSubmodule (Algebra.adjoin F (Set.range (ρ : G → Module.End F V))) := by
            simpa using hspan.symm
    _ = ⊤ := by
          simp [htop]

theorem CFSG.trace_eq_zero_of_not_mem_center_of_faithful_irreducible_isExtraspecial
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F K V) [IsIrreducible ρ] (hfaithful : Function.Injective ρ)
    {x : K} (hx : x ∉ Subgroup.center K) :
    LinearMap.trace F V (ρ x : Module.End F V) = 0 := by
  rw [Subgroup.mem_center_iff] at hx
  push Not at hx
  obtain ⟨y, hyx⟩ := hx
  let z : K := ⁅y, x⁆
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    exact hyx <| (commutatorElement_eq_one_iff_mul_comm.mp <| by simpa [z] using hz1)
  have hz_center : z ∈ Subgroup.center K := by
    exact
      commutatorElement_mem_center_of_commutator_le_center_local
        (commutator_le_center_of_isExtraspecial_local (q := q) (K := K)) y x
  obtain ⟨a, ha⟩ := center_apply_eq_smul_id_of_irreducible (ρ := ρ) hz_center
  have ha_ne_one : a ≠ 1 := by
    intro ha1
    have hzρ : (ρ z : Module.End F V) = 1 := by simpa [ha1] using ha
    have hzρ' : ρ z = ρ 1 := by simpa using hzρ
    exact hz_ne_one (hfaithful hzρ')
  have hconj_group : y * x * y⁻¹ = z * x := by
    simp [z, commutatorElement_def, mul_assoc]
  have hρ_conj :
      (ρ (y * x * y⁻¹) : Module.End F V) =
        (ρ y : Module.End F V) * ((ρ x : Module.End F V) * (ρ y⁻¹ : Module.End F V)) := by
    calc
      (ρ (y * x * y⁻¹) : Module.End F V)
          = (ρ (y * x) : Module.End F V) * (ρ y⁻¹ : Module.End F V) := by
              simp
      _ = ((ρ y : Module.End F V) * (ρ x : Module.End F V)) * (ρ y⁻¹ : Module.End F V) := by
            simp
      _ = (ρ y : Module.End F V) * ((ρ x : Module.End F V) * (ρ y⁻¹ : Module.End F V)) := by
            rw [mul_assoc]
  have hρ_zx :
      (ρ (y * x * y⁻¹) : Module.End F V) =
        (ρ z : Module.End F V) * (ρ x : Module.End F V) := by
    rw [hconj_group]
    simp
  have htrace_conj :
      LinearMap.trace F V (ρ (y * x * y⁻¹) : Module.End F V) =
        LinearMap.trace F V (ρ x : Module.End F V) := by
    calc
      LinearMap.trace F V (ρ (y * x * y⁻¹) : Module.End F V) =
          LinearMap.trace F V
            ((ρ y : Module.End F V) * ((ρ x : Module.End F V) * (ρ y⁻¹ : Module.End F V))) := by
              rw [hρ_conj]
      _ = LinearMap.trace F V
            (((ρ x : Module.End F V) * (ρ y⁻¹ : Module.End F V)) * (ρ y : Module.End F V)) := by
              exact
                LinearMap.trace_mul_comm
                  (R := F)
                  (f := (ρ y : Module.End F V))
                  (g := ((ρ x : Module.End F V) * (ρ y⁻¹ : Module.End F V)))
      _ = LinearMap.trace F V (ρ x : Module.End F V) := by
            rw [mul_assoc, ← ρ.map_mul, inv_mul_cancel, map_one, mul_one]
  have htrace_smul :
      LinearMap.trace F V (ρ (y * x * y⁻¹) : Module.End F V) =
        a * LinearMap.trace F V (ρ x : Module.End F V) := by
    calc
      LinearMap.trace F V (ρ (y * x * y⁻¹) : Module.End F V) =
          LinearMap.trace F V (((ρ z : Module.End F V) * (ρ x : Module.End F V))) := by
            rw [hρ_zx]
      _ = LinearMap.trace F V ((a • (1 : Module.End F V)) * (ρ x : Module.End F V)) := by
            rw [ha]
      _ = LinearMap.trace F V (a • (ρ x : Module.End F V)) := by
            rfl
      _ = a * LinearMap.trace F V (ρ x : Module.End F V) := by
            simp
  let t : F := LinearMap.trace F V (ρ x : Module.End F V)
  have ht_eq : t = a * t := by
    simpa [t] using htrace_conj.symm.trans htrace_smul
  have hmul : (1 - a) * t = 0 := by
    calc
      (1 - a) * t = t - a * t := by ring
      _ = 0 := by rw [sub_eq_zero.mpr ht_eq]
  have honea : 1 - a ≠ 0 := sub_ne_zero.mpr ha_ne_one.symm
  exact (mul_eq_zero.mp hmul).resolve_left honea

theorem CFSG.semidirectProduct_center_fixed
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [IsExtraspecial p P]
    {H : Type*} [Group H] {φ : H →* MulAut P}
    (hcentralizer : ∀ x : H, x ≠ 1 → {p | φ x p = p} = Subgroup.center P) :
    ∀ x : H, ∀ z : Subgroup.center P, φ x z = z := by
  intro x z
  by_cases hx : x = 1
  · subst hx
    simp
  · have hzmem : (z : P) ∈ {p : P | φ x p = p} := by
      rw [hcentralizer x hx]
      exact z.property
    simpa using hzmem

theorem CFSG.equiv_of_irreducible_char_eq
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    [IsIrreducible ρ] [IsIrreducible σ]
    (hc : ¬ ringChar F ∣ Nat.card G)
    (hchar : ρ.character = σ.character) :
    Nonempty (Equiv σ ρ) := by
  let : Fintype G := Fintype.ofFinite G
  have hcard_ne_zero : (Nat.card G : F) ≠ 0 := by
    intro hzero
    exact hc ((ringChar.spec F (Nat.card G)).1 hzero)
  let : Invertible (Nat.card G : F) := invertibleOfNonzero hcard_ne_zero
  by_cases hE : Nonempty (Equiv σ ρ)
  · exact hE
  · have horth := Representation.char_orthonormal (ρ := ρ) (σ := σ)
    have hself := Representation.char_orthonormal (ρ := ρ) (σ := ρ)
    rw [hchar] at horth
    have horth' :
        (Nat.card G : F)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = (0 : F) := by
      have horthσ :
          (Nat.card G : F)⁻¹ * ∑ g : G, σ.character g * σ.character g⁻¹ = (0 : F) := by
        simpa [hE] using horth
      simpa [hchar] using horthσ
    have hself' :
        (Nat.card G : F)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = (1 : F) := by
      simpa [show Nonempty (Equiv ρ ρ) from ⟨Representation.Equiv.refl ρ⟩] using hself
    exact False.elim (zero_ne_one (horth'.symm.trans hself'))

theorem CFSG.equiv_of_centerChar_eq_for_faithful_irreducible_isExtraspecial
    {q : ℕ} [Fact q.Prime] {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ρ : Representation F K V} {σ : Representation F K W}
    [IsIrreducible ρ] [IsIrreducible σ]
    (hρfaithful : Function.Injective ρ) (hσfaithful : Function.Injective σ)
    (hc : ¬ ringChar F ∣ Nat.card K)
    (hcenter : ∀ z ∈ Subgroup.center K, ρ.character z = σ.character z) :
    Nonempty (Equiv σ ρ) := by
  refine
    equiv_of_irreducible_char_eq (ρ := ρ) (σ := σ) hc ?_
  ext x
  by_cases hx : x ∈ Subgroup.center K
  · exact hcenter x hx
  · change LinearMap.trace F V (ρ x : Module.End F V) =
      LinearMap.trace F W (σ x : Module.End F W)
    rw [trace_eq_zero_of_not_mem_center_of_faithful_irreducible_isExtraspecial
      (q := q) (ρ := ρ) hρfaithful (x := x) (by simpa using hx)]
    rw [trace_eq_zero_of_not_mem_center_of_faithful_irreducible_isExtraspecial
      (q := q) (ρ := σ) hσfaithful (x := x) (by simpa using hx)]

def CFSG.fixedDiffMap
    {F : Type*} [Field F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    V →ₗ[F] (G → V) where
  toFun := fun v g ↦ ρ g v - v
  map_add' := by
    intro v w
    ext g
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' := by
    intro a v
    ext g
    simp [sub_eq_add_neg, smul_add]

@[simp]
theorem CFSG.fixedDiffMap_apply
    {F : Type*} [Field F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (v : V) (g : G) :
    fixedDiffMap ρ v g = ρ g v - v := rfl

theorem CFSG.fixedDiffMap_ker_eq_bot_iff
    {F : Type*} [Field F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    (fixedDiffMap ρ).ker = ⊥ ↔ {v : V | ∀ g : G, ρ g v = v} = {0} := by
  constructor
  · intro hker
    ext v
    constructor
    · intro hv
      have hvker : v ∈ (fixedDiffMap ρ).ker := by
        rw [LinearMap.mem_ker]
        ext g
        simp [fixedDiffMap, hv g]
      have hv0 : v ∈ (⊥ : Submodule F V) := by simpa [hker] using hvker
      simpa using hv0
    · intro hv0 g
      have : v = 0 := by simpa using hv0
      simp [this]
  · intro hfix
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hvfix : ∀ g : G, ρ g v = v := by
      intro g
      have hvg : fixedDiffMap ρ v g = 0 := by
        exact congrFun (show fixedDiffMap ρ v = 0 by simpa [LinearMap.mem_ker] using hv) g
      simpa [fixedDiffMap] using sub_eq_zero.mp hvg
    have hv0 : v ∈ ({0} : Set V) := by
      rw [← hfix]
      exact hvfix
    simpa using hv0

theorem CFSG.fixedVectors_eq_zero_extendScalars
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    {F' : Type*} [Field F'] [Algebra F F']
    (ρ : Representation F G V)
    (hfix : {v : V | ∀ g : G, ρ g v = v} = {0}) :
    {w : F' ⊗[F] V | ∀ g : G, (extendScalars F' ρ) g w = w} = {0} := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let f : V →ₗ[F] (G → V) := fixedDiffMap ρ
  have hf_inj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    exact (fixedDiffMap_ker_eq_bot_iff ρ).2 hfix
  let f' :
      F' ⊗[F] V →ₗ[F'] (G → F' ⊗[F] V) :=
    (TensorProduct.piRight F F' F' (fun _ : G => V)).toLinearMap.comp (f.baseChange F')
  have hf'_inj : Function.Injective f' := by
    exact (TensorProduct.piRight F F' F' (fun _ : G => V)).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := F') f hf_inj)
  have hf'_apply (w : F' ⊗[F] V) (g : G) :
      f' w g = (extendScalars F' ρ) g w - w := by
    refine TensorProduct.induction_on (motive := fun w =>
      f' w g = (extendScalars F' ρ) g w - w) w ?_ ?_ ?_
    · simp [f', f, fixedDiffMap, Theory.Representation.extendScalars_apply]
    · intro a v
      simp [f', f, fixedDiffMap, Theory.Representation.extendScalars_apply, TensorProduct.tmul_sub]
    · intro x y hx hy
      simp [hx, hy, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  ext w
  constructor
  · intro hw
    show w = 0
    apply hf'_inj
    ext g
    rw [hf'_apply, hw g, sub_self]
    simp
  · intro hw0 g
    have : w = 0 := by simpa using hw0
    simp [this]

theorem CFSG.exists_primitiveRoot_of_isAlgClosed_not_dvd
    {F : Type*} [Field F] [IsAlgClosed F]
    {h : ℕ} (hchar : ¬ ringChar F ∣ h) :
    ∃ ε : F, IsPrimitiveRoot ε h := by
  have hcast_ne_zero : (h : F) ≠ 0 := by
    intro hz
    exact hchar ((ringChar.spec F h).1 hz)
  let : NeZero (h : F) := ⟨hcast_ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot F h

theorem CFSG.finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
    {q : ℕ} [Fact q.Prime] {n : ℕ}
    {K : Type*} [Group K] [Finite K] [IsExtraspecial q K]
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F K V) [IsIrreducible ρ] (hfaithful : Function.Injective ρ)
    (hcard : Nat.card K = q ^ (2 * n + 1))
    (hc : ¬ ringChar F ∣ Nat.card K) :
    Module.finrank F V = q ^ n := by
  classical
  let : Theory.Representation.IsAbsolutelyIrreducible ρ :=
    (Theory.Representation.isAbsolutelyIrreducible_iff_surjective (ρ := ρ)).2
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)).surjective
  let : Fact (IsPGroup q K) := ⟨IsExtraspecial.isPGroup q K⟩
  let : Group.IsNilpotent K := (Fact.out : IsPGroup q K).isNilpotent
  let : Group.IsSolvable K := IsNilpotent.to_isSolvable
  have hdim_dvd_card : Module.finrank F V ∣ Nat.card K := lemma_2_3 ρ
  have hdim_cast_ne_zero : ((Module.finrank F V : ℕ) : F) ≠ 0 := by
    intro hzero
    apply hc
    exact dvd_trans ((ringChar.spec F (Module.finrank F V)).1 hzero) hdim_dvd_card
  let Q := K ⧸ Subgroup.center K
  let repQ : Q → K := Quotient.out
  have hrepQ (x : Q) : ((repQ x : K) : Q) = x := by
    simp [repQ]
  let b : Q → Module.End F V := fun x => ρ (repQ x)
  have hspan_b : Submodule.span F (Set.range b) = ⊤ := by
    have hspan_rho :
        Submodule.span F (Set.range (ρ : K → Module.End F V)) = ⊤ :=
      span_range_eq_top_of_irreducible_isAlgClosed (ρ := ρ)
    have htop_le : (⊤ : Submodule F (Module.End F V)) ≤ Submodule.span F (Set.range b) := by
      rw [← hspan_rho]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, rfl⟩
      let qx : Q := (x : Q)
      have hquot : ((x : K) : Q) = ((repQ qx : K) : Q) := by
        simpa [qx] using (hrepQ qx).symm
      have hcenter : x / repQ qx ∈ Subgroup.center K :=
        (QuotientGroup.eq_iff_div_mem).mp hquot
      obtain ⟨a, ha⟩ := center_apply_eq_smul_id_of_irreducible (ρ := ρ) hcenter
      have hmem : b qx ∈ Submodule.span F (Set.range b) :=
        Submodule.subset_span ⟨qx, rfl⟩
      have hrho :
          (ρ x : Module.End F V) = a • b qx := by
        calc
          (ρ x : Module.End F V) = (ρ ((x / repQ qx) * repQ qx) : Module.End F V) := by
            congr 1
            simp [div_eq_mul_inv, mul_assoc]
          _ = (ρ (x / repQ qx) : Module.End F V) * (ρ (repQ qx) : Module.End F V) := by
            simpa using (ρ.map_mul (x / repQ qx) (repQ qx))
          _ = (a • (1 : Module.End F V)) * (ρ (repQ qx) : Module.End F V) := by
            rw [ha]
          _ = a • b qx := by
            simp [b]
      rw [hrho]
      exact Submodule.smul_mem _ _ hmem
    exact top_unique htop_le
  let l : (Q →₀ F) →ₗ[F] Module.End F V := Finsupp.linearCombination F b
  have hl_surj : Function.Surjective l := by
    exact (span_range_eq_top_iff_surjective_finsuppLinearCombination F).1 hspan_b
  have hl_ker : ∀ c : Q →₀ F, l c = 0 → c = 0 := by
    intro c hc0
    ext s
    let Aq : Module.End F V := ρ ((repQ s)⁻¹)
    let tq : Module.End F V →ₗ[F] F := (LinearMap.trace F V).comp (LinearMap.mulRight F Aq)
    have htq_b (r : Q) : tq (b r) = if r = s then (Module.finrank F V : F) else 0 := by
      dsimp [tq, Aq, b]
      by_cases hrs : r = s
      · subst r
        have htrace_eq : tq (b s) = (Module.finrank F V : F) := by
          have hinv :
              ((ρ ((repQ s)⁻¹) : Module.End F V) * (ρ (repQ s) : Module.End F V)) = 1 := by
            simpa using (ρ.map_mul (repQ s)⁻¹ (repQ s)).symm
          calc
            LinearMap.trace F V ((ρ (repQ s) : Module.End F V) * (ρ ((repQ s)⁻¹) : Module.End F V))
                = LinearMap.trace F V
                    (((ρ ((repQ s)⁻¹) : Module.End F V) * (ρ (repQ s) : Module.End F V))) := by
                      exact
                        LinearMap.trace_mul_comm
                          (R := F)
                          (f := (ρ (repQ s) : Module.End F V))
                          (g := (ρ ((repQ s)⁻¹) : Module.End F V))
            _ = LinearMap.trace F V (1 : Module.End F V) := by
                  rw [hinv]
            _ = (Module.finrank F V : F) := by
                  simp
        simpa [tq, Aq, b] using htrace_eq
      · have hnotcenter : repQ r * (repQ s)⁻¹ ∉ Subgroup.center K := by
          intro hcenter
          have hquot :
              ((repQ r : K) : Q) = ((repQ s : K) : Q) := by
            exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hcenter)
          exact hrs (by simpa [hrepQ r, hrepQ s] using hquot)
        have htrace_eq : tq (b r) = 0 := by
          calc
            LinearMap.trace F V ((ρ (repQ r) : Module.End F V) * (ρ ((repQ s)⁻¹) : Module.End F V))
                = LinearMap.trace F V (ρ (repQ r * (repQ s)⁻¹) : Module.End F V) := by
                    simp
            _ = 0 := by
                  exact
                    trace_eq_zero_of_not_mem_center_of_faithful_irreducible_isExtraspecial
                      (q := q) (ρ := ρ) hfaithful (x := repQ r * (repQ s)⁻¹) hnotcenter
        simpa [tq, Aq, b, hrs] using htrace_eq
    have hsum :
        c.sum (fun r a => a * tq (b r)) = c s * (Module.finrank F V : F) := by
      classical
      rw [Finsupp.sum]
      by_cases hs : s ∈ c.support
      · rw [Finset.sum_eq_single s]
        · simp [htq_b]
        · intro r hr hrs
          simp [htq_b, hrs]
        · intro hsnot
          exact False.elim (hsnot hs)
      · have hcs : c s = 0 := by
          simpa [Finsupp.mem_support_iff] using hs
        rw [Finset.sum_eq_zero]
        · simp [hcs]
        · intro r hr
          by_cases hrs : r = s
          · subst hrs
            exact False.elim (hs hr)
          · simp [htq_b, hrs]
    have hcalc_sum : tq (l c) = c.sum (fun r a => a * tq (b r)) := by
      rw [show l c = c.sum (fun r a => a • b r) by simp [l, Finsupp.linearCombination_apply]]
      simp [Finsupp.sum]
    have hcalc : tq (l c) = c s * (Module.finrank F V : F) := by
      calc
        tq (l c) = c.sum (fun r a => a * tq (b r)) := hcalc_sum
        _ = c s * (Module.finrank F V : F) := hsum
    have hzero : tq (l c) = 0 := by
      simp [hc0]
    have hcoeff : c s * (Module.finrank F V : F) = 0 := by
      simpa [hcalc] using hzero
    exact (mul_eq_zero.mp hcoeff).resolve_right hdim_cast_ne_zero
  have hl_inj : Function.Injective l := by
    intro c d hcd
    have hzero : l (c - d) = 0 := by
      simp [hcd]
    have hsub : c - d = 0 := hl_ker (c - d) hzero
    exact sub_eq_zero.mp hsub
  let e : (Q →₀ F) ≃ₗ[F] Module.End F V := LinearEquiv.ofBijective l ⟨hl_inj, hl_surj⟩
  have hfinrank_finsupp : Module.finrank F (Q →₀ F) = Nat.card Q := by
    let : Fintype Q := Fintype.ofFinite Q
    calc
      Module.finrank F (Q →₀ F) = Module.finrank F (Q → F) := by
        exact LinearEquiv.finrank_eq (Finsupp.linearEquivFunOnFinite F F Q)
      _ = Fintype.card Q := Module.finrank_pi F
      _ = Nat.card Q := by simp
  have hfinrank_end : Module.finrank F (Module.End F V) = Nat.card Q := by
    calc
      Module.finrank F (Module.End F V) = Module.finrank F (Q →₀ F) := by
        exact (LinearEquiv.finrank_eq e).symm
      _ = Nat.card Q := hfinrank_finsupp
  have hcardQ : Nat.card Q = q ^ (2 * n) := by
    have hmul : Nat.card K = Nat.card Q * Nat.card (Subgroup.center K) := by
      simpa [Q] using (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K))
    have hcenter : Nat.card (Subgroup.center K) = q := IsExtraspecial.center_order_p q K
    have hmul' : q ^ (2 * n + 1) = Nat.card Q * q := by
      simpa [hcard, hcenter] using hmul
    have hpow : q ^ (2 * n) * q = Nat.card Q * q := by
      calc
        q ^ (2 * n) * q = q ^ (2 * n + 1) := by
          rw [show 2 * n + 1 = (2 * n) + 1 by omega, pow_succ]
        _ = Nat.card Q * q := hmul'
    exact Nat.eq_of_mul_eq_mul_right (Nat.Prime.pos Fact.out) hpow.symm
  have hsquare : Module.finrank F V * Module.finrank F V = q ^ (2 * n) := by
    calc
      Module.finrank F V * Module.finrank F V = Module.finrank F (Module.End F V) := by
        symm
        simpa [Module.End, mul_comm] using (Module.finrank_linearMap F F V V)
      _ = Nat.card Q := hfinrank_end
      _ = q ^ (2 * n) := hcardQ
  have hdim_dvd_pow : Module.finrank F V ∣ q ^ (2 * n + 1) := by
    simpa [hcard] using hdim_dvd_card
  obtain ⟨m, hm_le, hdim_eq⟩ := (Nat.dvd_prime_pow Fact.out).1 hdim_dvd_pow
  have hpow_eq : q ^ (m + m) = q ^ (n + n) := by
    calc
      q ^ (m + m) = q ^ m * q ^ m := by rw [pow_add]
      _ = Module.finrank F V * Module.finrank F V := by
        symm
        simp [hdim_eq]
      _ = q ^ (2 * n) := hsquare
      _ = q ^ (n + n) := by congr; omega
  have hm_add : m + m = n + n := (Nat.pow_right_injective (Nat.Prime.two_le Fact.out)) hpow_eq
  have hm : m = n := by omega
  simp [hdim_eq, hm]

theorem CFSG.theorem_2_5_exists_generator
    {H : Type*} [Group H] [IsCyclic H] :
    ∃ x : H, ∀ y : H, y ∈ Subgroup.zpowers x :=
  IsCyclic.exists_generator (α := H)

universe uP uF

theorem CFSG.theorem_2_5_exists_faithful_irreducible
    {p : ℕ} [Fact p.Prime]
    {P : Type uP} [Group P] [Finite P] [IsExtraspecial p P]
    {F : Type uF} [Field F] [IsAlgClosed F]
    (hc : ¬ ringChar F ∣ Nat.card P) :
    ∃ (V : Type (max uP uF)) (_ : AddCommGroup V) (_ : Module F V) (_ : FiniteDimensional F V)
      (ρ : Representation F P V), IsIrreducible ρ ∧ Function.Injective ρ := by
  classical
  have hpprime : p.Prime := Fact.out
  let : Fintype P := Fintype.ofFinite P
  let τ : Representation F P (MonoidAlgebra F P) := Representation.ofMulAction F P P
  have hτfaithful : Function.Injective τ := by
    intro x y hxy
    have hval :=
      congrArg
        (fun f : Module.End F (MonoidAlgebra F P) =>
          f (MonoidAlgebra.single (1 : P) (1 : F)))
        hxy
    have hsingle : MonoidAlgebra.single x (1 : F) = MonoidAlgebra.single y (1 : F) := by
      simpa [τ, Representation.ofMulAction_single] using hval
    by_contra hxy_ne
    have hpoint := congrArg (fun f : MonoidAlgebra F P => f.coeff x) hsingle
    have : (1 : F) = 0 := by
      simp [hxy_ne] at hpoint
    exact one_ne_zero this
  have hcard_cast_ne_zero : (Fintype.card P : F) ≠ 0 := by
    intro hz
    exact hc ((ringChar.spec F (Nat.card P)).1 (by simpa [Nat.card_eq_fintype_card] using hz))
  let : NeZero (Fintype.card P : F) := ⟨hcard_cast_ne_zero⟩
  have hcenter_ne_bot : Subgroup.center P ≠ ⊥ := by
    intro hcenter_bot
    have hcenter_card : Nat.card (Subgroup.center P) = 1 :=
      (Subgroup.eq_bot_iff_card (H := Subgroup.center P)).1 hcenter_bot
    rw [IsExtraspecial.center_order_p p P] at hcenter_card
    exact hpprime.ne_one hcenter_card
  have hτker : τ.ker = ⊥ := τ.ker_eq_bot_iff.mpr hτfaithful
  have hcenter_not_le_ker : ¬ Subgroup.center P ≤ τ.ker := by
    intro hle
    have : Subgroup.center P = ⊥ := by
      apply le_antisymm
      · exact hle.trans (by simp [hτker])
      · exact bot_le
    exact hcenter_ne_bot this
  let : FiniteDimensional F (MonoidAlgebra F P) := by infer_instance
  obtain ⟨m, hmSimple, hcenter_not_le_ker_m⟩ :=
    exists_simple_submodule_nontrivial_of_not_le_ker
      (ρ := τ) (H := Subgroup.center P) hcenter_not_le_ker
  let M := Subrepresentation.ofSubmodule' m
  let incl : M.toSubmodule →ₗ[F] MonoidAlgebra F P := {
    toFun := fun v => v.1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  let : FiniteDimensional F M.toSubmodule :=
    FiniteDimensional.of_injective incl (fun v w h => Subtype.ext h)
  let ρ : Representation F P M.toSubmodule := M.toRepresentation
  have hρirr : IsIrreducible ρ := irreducible_of_ofSubmodule'_simple τ hmSimple
  let : IsIrreducible ρ := hρirr
  have hρker : ρ.ker = ⊥ :=
    ker_eq_bot_of_center_not_le_ker_of_isExtraspecial
      (q := p) (ρ := ρ) hcenter_not_le_ker_m
  have hρfaithful : Function.Injective ρ := ρ.ker_eq_bot_iff.mp hρker
  exact ⟨↥M.toSubmodule, inferInstance, inferInstance, inferInstance, ρ, hρirr, hρfaithful⟩

def CFSG.theorem_2_5_rangeInlEquiv
    {P : Type*} [Group P]
    {H : Type*} [Group H]
    {φ : H →* MulAut P} :
    P ≃* (SemidirectProduct.inl : P →* SemidirectProduct P H φ).range where
  toFun := fun p => ⟨SemidirectProduct.inl p, ⟨p, rfl⟩⟩
  invFun := fun x => x.1.left
  left_inv := by
    intro p
    rfl
  right_inv := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨p, rfl⟩
    rfl
  map_mul' := by
    intro p q
    ext <;> simp

theorem CFSG.theorem_2_5_conj_inl
    {P : Type*} [Group P]
    {H : Type*} [Group H]
    {φ : H →* MulAut P}
    (g : SemidirectProduct P H φ) (q : P) :
    g * SemidirectProduct.inl q * g⁻¹ =
      SemidirectProduct.inl (g.left * φ g.right q * g.left⁻¹) := by
  rcases g with ⟨a, b⟩
  ext <;> simp [mul_assoc]

theorem CFSG.theorem_2_5_rangeInl_normal
    {P : Type*} [Group P]
    {H : Type*} [Group H]
    {φ : H →* MulAut P} :
    ((SemidirectProduct.inl : P →* SemidirectProduct P H φ).range).Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom (N := P) (G := H) (φ := φ)]
  infer_instance

noncomputable def CFSG.theorem_2_5_quotientKerRightHomEquiv
    {P : Type*} [Group P]
    {H : Type*} [Group H]
    {φ : H →* MulAut P} :
    (SemidirectProduct P H φ ⧸ (SemidirectProduct.rightHom (N := P) (G := H) (φ := φ)).ker) ≃* H :=
  QuotientGroup.quotientKerEquivOfSurjective
    (SemidirectProduct.rightHom (N := P) (G := H) (φ := φ))
    (SemidirectProduct.rightHom_surjective (N := P) (G := H) (φ := φ))

theorem CFSG.theorem_2_5_exists_extension
    {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    {h : ℕ} {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (hH : Nat.card H = h) (hh : Nat.Coprime h p)
    {φ : H →* MulAut P}
    (hcentralizer : ∀ x : H, x ≠ 1 → {p | φ x p = p} = Subgroup.center P)
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F P V) [IsIrreducible ρ] (hρfaithful : Function.Injective ρ)
    (hcharP : ¬ ringChar F ∣ Nat.card P) :
    ∃ σ : Representation F (SemidirectProduct P H φ) V, σ.comp SemidirectProduct.inl = ρ := by
  classical
  let _ := hH
  let _ := hh
  let G := SemidirectProduct P H φ
  let K : Subgroup G := (SemidirectProduct.inl : P →* G).range
  let eK : P ≃* K := theorem_2_5_rangeInlEquiv (P := P) (H := H) (φ := φ)
  let ρK : Representation F K V := ρ.comp eK.symm.toMonoidHom
  have hρKirr : IsIrreducible ρK := by
    refine (RepEquiv.irreducible_iff_group_iso (ρ := ρK) (σ := ρ) eK.symm ?_).2 inferInstance
    intro k v
    rfl
  let : IsIrreducible ρK := hρKirr
  have hρKfaithful : Function.Injective ρK := by
    intro a b hab
    apply eK.symm.injective
    exact hρfaithful (by simpa [ρK] using hab)
  let : Finite G := Finite.of_equiv (P × H) (SemidirectProduct.equivProd (φ := φ)).symm
  let : K.Normal := by
    simpa [G, K] using theorem_2_5_rangeInl_normal (P := P) (H := H) (φ := φ)
  have hcycK : IsCyclic (G ⧸ K) := by
    let eQ : G ⧸ K ≃* H := by
      let hK :
          K = (SemidirectProduct.rightHom (N := P) (G := H) (φ := φ)).ker := by
        simpa [G, K] using
          (SemidirectProduct.range_inl_eq_ker_rightHom (N := P) (G := H) (φ := φ))
      exact
        (QuotientGroup.quotientMulEquivOfEq hK).trans
          (theorem_2_5_quotientKerRightHomEquiv (P := P) (H := H) (φ := φ))
    exact isCyclic_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective
  have hcenter_fixed : ∀ x : H, ∀ z : Subgroup.center P, φ x z = z :=
    semidirectProduct_center_fixed (p := p) (P := P) (H := H) (φ := φ) hcentralizer
  have E : ∀ g : G, ρK ≃ₗ conjugateRep ρK g := by
    intro g
    let αg : MulAut P := (φ g.right).trans (MulAut.conj g.left)
    let τg : Representation F P V := ρ.comp αg.toMonoidHom
    have hτgirr : IsIrreducible τg := by
      refine (RepEquiv.irreducible_iff_group_iso (ρ := τg) (σ := ρ) αg ?_).2 inferInstance
      intro q v
      rfl
    letI : IsIrreducible τg := hτgirr
    have hτgfaithful : Function.Injective τg := by
      intro a b hab
      apply αg.injective
      exact hρfaithful (by simpa [τg] using hab)
    have hcenter :
        ∀ z ∈ Subgroup.center P, ρ.character z = τg.character z := by
      intro z hz
      have hzcomm : ∀ y : P, y * z = z * y := by
        simpa [Subgroup.mem_center_iff] using hz
      have hαgz : αg z = z := by
        change g.left * φ g.right z * g.left⁻¹ = z
        rw [hcenter_fixed g.right ⟨z, hz⟩, hzcomm g.left]
        simp [mul_assoc]
      change LinearMap.trace F V (ρ z : Module.End F V) =
          LinearMap.trace F V (τg z : Module.End F V)
      simp [τg, hαgz]
    let eτg : Representation.Equiv τg ρ := Classical.choice <|
      equiv_of_centerChar_eq_for_faithful_irreducible_isExtraspecial
        (q := p) (K := P) (ρ := ρ) (σ := τg) hρfaithful hτgfaithful hcharP hcenter
    let ePg : ρ ≃ₗ τg :=
      RepEquiv.mk eτg.symm.toLinearEquiv (by
        intro q
        exact eτg.symm.1.2 q)
    refine
      { toLinearEquiv := ePg.toLinearEquiv
        isIntertwining' := ?_ }
    intro k
    ext v
    let q : P := eK.symm k
    have hk : k = eK q := by
      dsimp [q]
      exact (eK.apply_symm_apply k).symm
    have hconjK :
        (⟨g * (eK q : K).1 * g⁻¹,
          Subgroup.Normal.conj_mem (inferInstance : K.Normal) (eK q) (eK q).property g⟩ : K) =
          eK (αg q) := by
      apply Subtype.ext
      change g * SemidirectProduct.inl q * g⁻¹ = SemidirectProduct.inl (αg q)
      simpa [q, αg] using theorem_2_5_conj_inl (φ := φ) g q
    have hconj_apply : (conjugateRep ρK g) (eK q) = τg q := by
      rw [conjugateRep_apply, hconjK]
      simp [ρK, τg]
    rw [hk]
    rw [show ρK (eK q) = ρ q by simp [ρK]]
    rw [hconj_apply]
    exact ePg.isIntertwining q v
  obtain ⟨σ, hσK⟩ :=
    proposition_2_2_b (F := F) (G := G) (H := K) (V := V) (W := V) hcycK ρK E
  refine ⟨σ, ?_⟩
  ext q v
  have hq := congrArg (fun r : Representation F K V => r (eK q) v) hσK
  calc
    σ (SemidirectProduct.inl q) v = σ (eK q) v := by rfl
    _ = ρK (eK q) v := hq
    _ = ρ q v := by rfl

theorem CFSG.theorem_2_5_generator_linearEquiv
    {h : ℕ} {H : Type*} [Group H] [Finite H] (hH : Nat.card H = h)
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V]
    {P : Type*} [Group P] {φ : H →* MulAut P}
    (σ : Representation F (SemidirectProduct P H φ) V)
    {x : H} (hxgen : ∀ y : H, y ∈ Subgroup.zpowers x) :
    ∃ g : V ≃ₗ[F] V, (g : Module.End F V) = σ (SemidirectProduct.inr x) ∧ g ^ h = 1 := by
  have hxord : orderOf x = h := by
    simpa [hH] using orderOf_eq_card_of_forall_mem_zpowers hxgen
  have hxpow : x ^ h = 1 := by
    simpa [hxord] using pow_orderOf_eq_one x
  let u : LinearMap.GeneralLinearGroup F V := σ.asGroupHom (SemidirectProduct.inr x)
  have hxinr_pow : ((SemidirectProduct.inr x : SemidirectProduct P H φ) ^ h) = 1 := by
    calc
      ((SemidirectProduct.inr x : SemidirectProduct P H φ) ^ h) =
          SemidirectProduct.inr (x ^ h) := by
            simp
      _ = 1 := by simp [hxpow]
  have hu_pow : u ^ h = 1 := by
    simpa [u] using congrArg σ.asGroupHom hxinr_pow
  have htoLinearEquiv_pow (n : ℕ) :
      u.toLinearEquiv ^ n = (u ^ n).toLinearEquiv := by
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        simp [pow_succ, ih, LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
  refine ⟨u.toLinearEquiv, rfl, ?_⟩
  calc
    u.toLinearEquiv ^ h = (u ^ h).toLinearEquiv := htoLinearEquiv_pow h
    _ = 1 := by
      rw [hu_pow]
      rfl

theorem CFSG.theorem_2_5_hE_intertwining_eq_eigenspace
    {F : Type*} [Field F]
    {H : Type*} [Group H]
    {V : Type*} [AddCommGroup V] [Module F V]
    (τ : Representation F H V) (x : H) (μ : F) :
    intertwiningSubmodule (τ x) (μ • τ x) =
      Module.End.eigenspace ((Representation.linHom τ τ) x) μ := by
  ext X
  constructor
  · intro hX
    rw [Module.End.mem_eigenspace_iff]
    ext v
    have hX' := LinearMap.congr_fun hX (τ x⁻¹ v)
    simpa [Representation.linHom_apply, mul_assoc] using hX'
  · intro hX
    rw [Module.End.mem_eigenspace_iff] at hX
    ext v
    have hX' := LinearMap.congr_fun hX (τ x v)
    simpa [Representation.linHom_apply, mul_assoc] using hX'

set_option backward.isDefEq.respectTransparency false in
noncomputable def CFSG.theorem_2_5_hE_phiQ
    {P : Type*} [Group P]
    {H : Type*} [Group H]
    {φ : H →* MulAut P}
    (hcenter_fixed : ∀ x : H, ∀ z : Subgroup.center P, φ x z = z) :
    H →* MulAut (P ⧸ Subgroup.center P) where
  toFun x := by
    let fx : P ⧸ Subgroup.center P →* P ⧸ Subgroup.center P :=
      QuotientGroup.map (Subgroup.center P) (Subgroup.center P) (φ x) <| by
        intro z hz
        have hzfixed : φ x z = z := hcenter_fixed x ⟨z, hz⟩
        simpa [hzfixed] using hz
    let gx : P ⧸ Subgroup.center P →* P ⧸ Subgroup.center P :=
      QuotientGroup.map (Subgroup.center P) (Subgroup.center P) (φ x⁻¹) <| by
        intro z hz
        have hzfixed : (MulEquiv.symm (φ x)) z = z := by
          have hzfixed' : φ x⁻¹ z = z := by
            simpa using hcenter_fixed x⁻¹ ⟨z, hz⟩
          simpa using hzfixed'
        simpa [hzfixed] using hz
    have hleft : Function.LeftInverse gx fx := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro a
      simp [fx, gx]
    have hright : Function.RightInverse gx fx := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro a
      simp [fx, gx]
    exact MulEquiv.ofBijective fx ⟨hleft.injective, hright.surjective⟩
  map_one' := by
    ext q
    refine Quotient.inductionOn' q ?_
    intro a
    simp
  map_mul' x y := by
    ext q
    refine Quotient.inductionOn' q ?_
    intro a
    simp [MonoidHom.map_mul]

theorem CFSG.theorem_2_5_hE_phiQ_fixed_eq_one
    {p : ℕ} [Fact p.Prime]
    {P : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    {h : ℕ} {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (hH : Nat.card H = h) (hh : Nat.Coprime h p)
    {φ : H →* MulAut P}
    (hcentralizer : ∀ x : H, x ≠ 1 → {p | φ x p = p} = Subgroup.center P)
    {y : H} (hy : y ≠ 1)
    {q : P ⧸ Subgroup.center P}
    (hq :
      theorem_2_5_hE_phiQ
          (P := P) (H := H) (φ := φ)
          (semidirectProduct_center_fixed (p := p) (P := P) (H := H) (φ := φ) hcentralizer) y q =
        q) :
    q = 1 := by
  let repQ : P ⧸ Subgroup.center P → P := Quotient.out
  have hrepQ (r : P ⧸ Subgroup.center P) : ((repQ r : P) : P ⧸ Subgroup.center P) = r := by
    simp [repQ]
  let p0 : P := repQ q
  have hquot :
      (((φ y p0 : P) : P ⧸ Subgroup.center P)) = q := by
    let fy : P ⧸ Subgroup.center P →* P ⧸ Subgroup.center P :=
      QuotientGroup.map (Subgroup.center P) (Subgroup.center P) (φ y) <| by
        intro z hz
        have hzfixed :
            φ y z = z :=
          semidirectProduct_center_fixed (p := p) (P := P) (H := H) (φ := φ) hcentralizer y
            ⟨z, hz⟩
        simpa [hzfixed] using hz
    have hfy : fy q = (((φ y p0 : P) : P ⧸ Subgroup.center P)) := by
      rw [(hrepQ q).symm]
      rfl
    calc
      (((φ y p0 : P) : P ⧸ Subgroup.center P)) = fy q := by
            simpa using hfy.symm
      _ =
          theorem_2_5_hE_phiQ
            (P := P) (H := H) (φ := φ)
            (semidirectProduct_center_fixed (p := p) (P := P) (H := H) (φ := φ) hcentralizer) y q := by
              rfl
      _ = q := hq
  have hquot' : (((φ y p0 : P) : P ⧸ Subgroup.center P)) = ((p0 : P) : P ⧸ Subgroup.center P) := by
    simpa [p0, hrepQ q] using hquot
  have hzmem : φ y p0 / p0 ∈ Subgroup.center P :=
    (QuotientGroup.eq_iff_div_mem).mp hquot'
  let z : Subgroup.center P := ⟨φ y p0 / p0, hzmem⟩
  have hzfixed :
      φ y z = z := by
    exact semidirectProduct_center_fixed (p := p) (P := P) (H := H) (φ := φ) hcentralizer y z
  have hstep :
      φ y p0 = z * p0 := by
    calc
      φ y p0 = (φ y p0 / p0) * p0 := by simp [div_eq_mul_inv, mul_assoc]
      _ = z * p0 := rfl
  have hpow : ∀ n : ℕ, φ (y ^ n) p0 = z ^ n * p0 := by
    intro n
    induction n with
    | zero =>
        simp [p0]
    | succ n ih =>
        calc
          φ (y ^ (n + 1)) p0 = φ y (φ (y ^ n) p0) := by
            simp [pow_succ', MonoidHom.map_mul]
          _ = φ y (z ^ n * p0) := by rw [ih]
          _ = φ y (z ^ n) * φ y p0 := by rw [map_mul]
          _ = z ^ n * (z * p0) := by
                simp [hstep, hzfixed, map_pow]
          _ = z ^ (n + 1) * p0 := by
                rw [pow_succ, ← mul_assoc]
  have hyh : y ^ h = 1 := by
    simpa [hH] using (pow_card_eq_one' (x := y))
  have hzh : (z : P) ^ h = 1 := by
    have htop := hpow h
    rw [hyh, MonoidHom.map_one] at htop
    have htop' : p0 = (z : P) ^ h * p0 := by
      simpa using htop
    have hcancel := congrArg (fun t : P => t * p0⁻¹) htop'
    simpa [mul_assoc] using hcancel.symm
  have hz_dvd_h : orderOf (z : P) ∣ h := orderOf_dvd_of_pow_eq_one hzh
  have hz_dvd_p : orderOf (z : P) ∣ p := by
    have hz_card : Nat.card (Subgroup.center P) = p := IsExtraspecial.center_order_p p P
    exact hz_card ▸ Subgroup.orderOf_dvd_natCard (Subgroup.center P) z.property
  have hz_one : orderOf (z : P) = 1 := Nat.eq_one_of_dvd_coprimes hh hz_dvd_h hz_dvd_p
  have hz_eq_one : (z : P) = 1 := orderOf_eq_one_iff.mp hz_one
  have hyfix : φ y p0 = p0 := by
    simp [hstep, hz_eq_one]
  have hp0_center : p0 ∈ Subgroup.center P := by
    have hp0_fix : p0 ∈ {p : P | φ y p = p} := by
      simpa [p0] using hyfix
    rw [hcentralizer y hy] at hp0_fix
    exact hp0_fix
  simpa [p0, hrepQ q] using (QuotientGroup.eq_one_iff p0).2 hp0_center

theorem CFSG.theorem_2_5_hE_char_not_dvd_card
    {p : ℕ} [Fact p.Prime] {n : ℕ}
    {P : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    (hp : Nat.card P = p ^ (2 * n + 1))
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F P V) [IsIrreducible ρ] (hρfaithful : Function.Injective ρ) :
    ¬ ringChar F ∣ Nat.card P := by
  classical
  have hpprime : p.Prime := Fact.out
  intro hcharP
  have hcardP_ne_zero : Nat.card P ≠ 0 := by
    rw [hp]
    exact pow_ne_zero _ hpprime.ne_zero
  have hchar_ne_zero : ringChar F ≠ 0 := by
    intro hzero
    have : Nat.card P = 0 := by
      simpa [hzero] using hcharP
    exact hcardP_ne_zero this
  have hprime_char : Nat.Prime (ringChar F) := by
    rcases CharP.char_is_prime_or_zero F (ringChar F) with hprime | hzero
    · exact hprime
    · exact False.elim (hchar_ne_zero hzero)
  have hchar_dvd_p : ringChar F ∣ p := by
    have : ringChar F ∣ p ^ (2 * n + 1) := by
      simpa [hp] using hcharP
    exact hprime_char.dvd_of_dvd_pow this
  have hchar_eq_p : ringChar F = p := by
    rcases (Nat.dvd_prime hpprime).1 hchar_dvd_p with h1 | hp'
    · exact False.elim (hprime_char.ne_one h1)
    · exact hp'
  have hcenter_ne_one : Nat.card (Subgroup.center P) ≠ 1 := by
    rw [IsExtraspecial.center_order_p p P]
    exact hpprime.ne_one
  have : Nontrivial (Subgroup.center P) := by
    refine (nontrivial_iff_exists_ne (1 : Subgroup.center P)).2 ?_
    by_contra hnone
    push Not at hnone
    have hsub : Subsingleton (Subgroup.center P) := ⟨fun a b => by rw [hnone a, hnone b]⟩
    have hcard1 : Nat.card (Subgroup.center P) = 1 :=
      (Nat.card_eq_one_iff_unique).2 ⟨hsub, ⟨1⟩⟩
    exact hcenter_ne_one hcard1
  obtain ⟨z, hz_ne⟩ := exists_ne (1 : Subgroup.center P)
  let f : ρ.IntertwiningMap ρ :=
    Representation.IntertwiningMap.centralMul ρ (z : P) <| by
      rw [Submonoid.mem_center_iff]
      intro g
      exact (Subgroup.mem_center_iff.mp z.2) g
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  have hρz : (ρ z : Module.End F V) = a • 1 := by
    ext v
    have hv := congrArg (fun g : ρ.IntertwiningMap ρ => g v) ha
    calc
      ρ z v = f v := rfl
      _ = (algebraMap F (ρ.IntertwiningMap ρ) a) v := hv.symm
      _ = a • v := by
        rfl
  have hz_dvd : orderOf (z : P) ∣ p := by
    simpa [IsExtraspecial.center_order_p p P] using
      (Subgroup.orderOf_dvd_natCard (Subgroup.center P) z.2)
  have hz_order : orderOf (z : P) = p := by
    rcases (Nat.dvd_prime hpprime).1 hz_dvd with h1 | hpz
    · have : (z : P) = 1 := orderOf_eq_one_iff.mp h1
      exact False.elim (hz_ne (Subtype.ext this))
    · exact hpz
  have hzpow : (z : P) ^ p = 1 := by
    simpa [hz_order] using pow_orderOf_eq_one (z : P)
  have hpow_map : (ρ z : Module.End F V) ^ p = 1 := by
    simpa using congrArg ρ hzpow
  have hpow' : (a • (1 : Module.End F V)) ^ p = (1 : Module.End F V) := by
    simpa [hρz] using hpow_map
  have : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨v, hv_ne⟩ := exists_ne (0 : V)
  have hv_eq : (a ^ p) • v = v := by
    have hpow'' := congrArg (fun T : Module.End F V => T v) hpow'
    simpa [smul_pow, LinearMap.smul_apply, Module.End.one_apply] using hpow''
  have hapow : a ^ p = 1 := by
    have hsmul0 : (a ^ p - 1) • v = 0 := by
      calc
        (a ^ p - 1) • v = (a ^ p) • v - v := by simp [sub_smul]
        _ = 0 := by simp [hv_eq]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul0).resolve_right hv_ne)
  let : Fact (Nat.Prime (ringChar F)) := ⟨hprime_char⟩
  have hsubpow : (a - 1) ^ ringChar F = a ^ ringChar F - 1 := by
    simpa using (sub_pow_char a 1 (p := ringChar F))
  have ha_eq_one : a = 1 := by
    have hpowchar : a ^ ringChar F = 1 := by
      simpa [hchar_eq_p] using hapow
    have hzero : (a - 1) ^ ringChar F = 0 := by
      rw [hsubpow, hpowchar, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)
  have hρz_one : ρ z = ρ 1 := by
    simp [hρz, ha_eq_one]
  have hz_eq_one : (z : P) = 1 := hρfaithful hρz_one
  exact hz_ne (Subtype.ext hz_eq_one)

set_option backward.isDefEq.respectTransparency false in
theorem CFSG.theorem_2_5_hE_char_not_dvd_h
    {h : ℕ} {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = h)
    {F : Type*} [Field F] {ε : F} (hε : IsPrimitiveRoot ε h) :
    ¬ ringChar F ∣ h := by
  have hh_ne_zero : h ≠ 0 := by
    intro hh0
    have hcardH_ne_zero : Nat.card H ≠ 0 :=
      Nat.pos_iff_ne_zero.mp <| Finite.card_pos_iff.mpr ⟨(1 : H)⟩
    exact hcardH_ne_zero (hH.trans hh0)
  intro hchar
  by_cases hchar0 : ringChar F = 0
  · rcases hchar with ⟨k, hk⟩
    exact hh_ne_zero (by simpa [hchar0] using hk)
  have hprime_char : Nat.Prime (ringChar F) := by
    rcases CharP.char_is_prime_or_zero F (ringChar F) with hprime | hzero
    · exact hprime
    · exact False.elim (hchar0 hzero)
  rcases hchar with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
    have : h = 0 := by rw [hk, hk0', mul_zero]
    exact hh_ne_zero this
  have hk_lt_h : k < h := by
    have hchar_ge_two : 2 ≤ ringChar F := hprime_char.two_le
    rw [hk]
    nlinarith
  let : Fact (Nat.Prime (ringChar F)) := ⟨hprime_char⟩
  have hkpow : ε ^ k = 1 := by
    have hsubpow : (ε ^ k - 1) ^ ringChar F = (ε ^ k) ^ ringChar F - 1 := by
      simpa using (sub_pow_char (ε ^ k) 1 (p := ringChar F))
    have hpow : (ε ^ k) ^ ringChar F = 1 := by
      rw [← pow_mul, Nat.mul_comm, ← hk, hε.pow_eq_one]
    have hzero : (ε ^ k - 1) ^ ringChar F = 0 := by
      rw [hsubpow, hpow, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)
  exact hε.pow_ne_one_of_pos_of_lt hk_pos.ne' hk_lt_h hkpow


set_option maxHeartbeats 800000 in
theorem CFSG.theorem_2_5_hE
    {p : ℕ} [Fact p.Prime] {n : ℕ}
    {P : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    (hp : Nat.card P = p ^ (2 * n + 1))
    {h : ℕ} {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (hH : Nat.card H = h) (hh : Nat.Coprime h p)
    {φ : H →* MulAut P}
    (hcentralizer : ∀ x : H, x ≠ 1 → {p | φ x p = p} = Subgroup.center P)
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F P V) [IsIrreducible ρ] (hρfaithful : Function.Injective ρ)
    (σ : Representation F (SemidirectProduct P H φ) V)
    (hσ : σ.comp SemidirectProduct.inl = ρ)
    {x : H} (hxgen : ∀ y : H, y ∈ Subgroup.zpowers x)
    {ε : F} (hε : IsPrimitiveRoot ε h) :
    ∀ m : ℤ, ¬ m % h = 0 →
      Module.finrank F
          (intertwiningSubmodule (σ <| SemidirectProduct.inr x)
            (ε ^ (0 : ℤ) • (σ <| SemidirectProduct.inr x))) =
        Module.finrank F
          (intertwiningSubmodule (σ <| SemidirectProduct.inr x)
            (ε ^ m • (σ <| SemidirectProduct.inr x))) + 1 := by
  classical
  have hpprime : p.Prime := Fact.out
  have hcharP : ¬ ringChar F ∣ Nat.card P :=
    theorem_2_5_hE_char_not_dvd_card (p := p) (n := n) (P := P) hp ρ hρfaithful
  have hcharH : ¬ ringChar F ∣ h :=
    theorem_2_5_hE_char_not_dvd_h (h := h) (H := H) hH hε
  have hcardP_ne_zero : Nat.card P ≠ 0 := by
    rw [hp]
    exact pow_ne_zero _ hpprime.ne_zero
  have hh_ne_zero : h ≠ 0 := by
    intro hh0
    rw [hh0, Nat.coprime_zero_left] at hh
    exact hpprime.ne_one hh
  let : Fact (IsPGroup p P) := ⟨IsExtraspecial.isPGroup p P⟩
  let : Group.IsNilpotent P := (Fact.out : IsPGroup p P).isNilpotent
  let : Group.IsSolvable P := IsNilpotent.to_isSolvable
  let : Theory.Representation.IsAbsolutelyIrreducible ρ :=
    (Theory.Representation.isAbsolutelyIrreducible_iff_surjective (ρ := ρ)).2
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)).surjective
  have hdim_dvd_card : Module.finrank F V ∣ Nat.card P := lemma_2_3 ρ
  have hdim_cast_ne_zero : ((Module.finrank F V : ℕ) : F) ≠ 0 := by
    intro hzero
    apply hcharP
    exact dvd_trans ((ringChar.spec F (Module.finrank F V)).1 hzero) hdim_dvd_card
  let τ : Representation F H V := σ.comp SemidirectProduct.inr
  let T : Representation F H (Module.End F V) := Representation.linHom τ τ
  let Q := P ⧸ Subgroup.center P
  let : Group Q := by
    dsimp [Q]
    infer_instance
  let : Finite Q := by
    dsimp [Q]
    infer_instance
  let repQ : Q → P := fun q => if q = 1 then 1 else Quotient.out q
  have hrepQ : ∀ q : Q, ((repQ q : P) : Q) = q := by
    intro q
    by_cases hq : q = 1
    · subst q
      have hrepQ1 : repQ (1 : Q) = (1 : P) := by
        simp [repQ]
      rw [hrepQ1]
      rfl
    · simp [repQ, hq, Quotient.out_eq' q]
  let b : Q → Module.End F V := fun q => ρ (repQ q)
  have hspan_b : Submodule.span F (Set.range b) = ⊤ := by
    have hspan_rho :
        Submodule.span F (Set.range (ρ : P → Module.End F V)) = ⊤ :=
      span_range_eq_top_of_irreducible_isAlgClosed (ρ := ρ)
    have htop_le : (⊤ : Submodule F (Module.End F V)) ≤ Submodule.span F (Set.range b) := by
      rw [← hspan_rho]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨p0, rfl⟩
      let q0 : Q := (p0 : Q)
      have hquot : ((p0 : P) : Q) = ((repQ q0 : P) : Q) := by
        simpa [q0] using (hrepQ q0).symm
      have hcenter : p0 / repQ q0 ∈ Subgroup.center P :=
        (QuotientGroup.eq_iff_div_mem).mp hquot
      obtain ⟨a, ha⟩ := center_apply_eq_smul_id_of_irreducible (ρ := ρ) hcenter
      have hmem : b q0 ∈ Submodule.span F (Set.range b) :=
        Submodule.subset_span ⟨q0, rfl⟩
      have hrho :
          (ρ p0 : Module.End F V) = a • b q0 := by
        calc
          (ρ p0 : Module.End F V) = (ρ ((p0 / repQ q0) * repQ q0) : Module.End F V) := by
            congr 1
            simp [div_eq_mul_inv, mul_assoc]
          _ = (ρ (p0 / repQ q0) : Module.End F V) * (ρ (repQ q0) : Module.End F V) := by
              simpa using (ρ.map_mul (p0 / repQ q0) (repQ q0))
          _ = (a • (1 : Module.End F V)) * (ρ (repQ q0) : Module.End F V) := by
              rw [ha]
          _ = a • b q0 := by
              simp [b]
      rw [hrho]
      exact Submodule.smul_mem _ _ hmem
    exact top_unique htop_le
  let l : (Q →₀ F) →ₗ[F] Module.End F V := Finsupp.linearCombination F b
  have hl_surj : Function.Surjective l := by
    exact (span_range_eq_top_iff_surjective_finsuppLinearCombination F).1 hspan_b
  have hl_ker : ∀ c : Q →₀ F, l c = 0 → c = 0 := by
    intro c hc0
    ext s
    let As : Module.End F V := ρ ((repQ s)⁻¹)
    let ts : Module.End F V →ₗ[F] F := (LinearMap.trace F V).comp (LinearMap.mulRight F As)
    have hts_b (r : Q) : ts (b r) = if r = s then (Module.finrank F V : F) else 0 := by
      dsimp [ts, As, b]
      by_cases hrs : r = s
      · subst r
        have htrace_eq : ts (b s) = (Module.finrank F V : F) := by
          have hinv :
              ((ρ ((repQ s)⁻¹) : Module.End F V) * (ρ (repQ s) : Module.End F V)) = 1 := by
            simpa using (ρ.map_mul (repQ s)⁻¹ (repQ s)).symm
          calc
            LinearMap.trace F V ((ρ (repQ s) : Module.End F V) * (ρ ((repQ s)⁻¹) : Module.End F V))
                = LinearMap.trace F V
                    (((ρ ((repQ s)⁻¹) : Module.End F V) * (ρ (repQ s) : Module.End F V))) := by
                      exact
                        LinearMap.trace_mul_comm
                          (R := F)
                          (f := (ρ (repQ s) : Module.End F V))
                          (g := (ρ ((repQ s)⁻¹) : Module.End F V))
            _ = LinearMap.trace F V (1 : Module.End F V) := by
                  rw [hinv]
            _ = (Module.finrank F V : F) := by
                  simp
        simpa [ts, As, b] using htrace_eq
      · have hnotcenter : repQ r * (repQ s)⁻¹ ∉ Subgroup.center P := by
          intro hcenter
          have hquot :
              ((repQ r : P) : Q) = ((repQ s : P) : Q) := by
            exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hcenter)
          exact hrs (by simpa [hrepQ r, hrepQ s] using hquot)
        have htrace_eq : ts (b r) = 0 := by
          calc
            LinearMap.trace F V ((ρ (repQ r) : Module.End F V) * (ρ ((repQ s)⁻¹) : Module.End F V))
                = LinearMap.trace F V (ρ (repQ r * (repQ s)⁻¹) : Module.End F V) := by
                    simp
            _ = 0 := by
                  exact
                    trace_eq_zero_of_not_mem_center_of_faithful_irreducible_isExtraspecial
                      (q := p) (ρ := ρ) hρfaithful (x := repQ r * (repQ s)⁻¹) hnotcenter
        simpa [ts, As, b, hrs] using htrace_eq
    have hsum :
        c.sum (fun r a => a * ts (b r)) = c s * (Module.finrank F V : F) := by
      classical
      rw [Finsupp.sum]
      by_cases hs : s ∈ c.support
      · rw [Finset.sum_eq_single s]
        · simp [hts_b]
        · intro r _ hrs
          simp [hts_b, hrs]
        · intro hsnot
          exact False.elim (hsnot hs)
      · have hcs : c s = 0 := by
          simpa [Finsupp.mem_support_iff] using hs
        rw [Finset.sum_eq_zero]
        · simp [hcs]
        · intro r hr
          by_cases hrs : r = s
          · subst hrs
            exact False.elim (hs hr)
          · simp [hts_b, hrs]
    have hcalc_sum : ts (l c) = c.sum (fun r a => a * ts (b r)) := by
      rw [show l c = c.sum (fun r a => a • b r) by simp [l, Finsupp.linearCombination_apply]]
      simp [Finsupp.sum]
    have hcalc : ts (l c) = c s * (Module.finrank F V : F) := by
      calc
        ts (l c) = c.sum (fun r a => a * ts (b r)) := hcalc_sum
        _ = c s * (Module.finrank F V : F) := hsum
    have hzero : ts (l c) = 0 := by
      simp [hc0]
    have hcoeff : c s * (Module.finrank F V : F) = 0 := by
      simpa [hcalc] using hzero
    exact (mul_eq_zero.mp hcoeff).resolve_right hdim_cast_ne_zero
  have hl_inj : Function.Injective l := by
    intro c d hcd
    have hzero : l (c - d) = 0 := by
      simp [hcd]
    have hsub : c - d = 0 := hl_ker (c - d) hzero
    exact sub_eq_zero.mp hsub
  let e : (Q →₀ F) ≃ₗ[F] Module.End F V := LinearEquiv.ofBijective l ⟨hl_inj, hl_surj⟩
  have e_apply (c : Q →₀ F) :
      e c = Finsupp.linearCombination F (fun q => ρ (repQ q)) c := rfl
  intro m hm
  have : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hh_pos : 0 < h := Nat.pos_of_ne_zero hh_ne_zero
  have hh_ne_one : h ≠ 1 := by
    intro hh1
    apply hm
    simp [hh1]
  have hh2 : h ≥ 2 := by omega
  let hcenter_fixed :
      ∀ x : H, ∀ z : Subgroup.center P, φ x z = z :=
    semidirectProduct_center_fixed (p := p) (P := P) (H := H) (φ := φ) hcentralizer
  let φQ : H →* MulAut Q :=
    theorem_2_5_hE_phiQ (P := P) (H := H) (φ := φ) hcenter_fixed
  let a : MulAut Q := φQ x
  let S : Module.End F (Q →₀ F) := e.symm.conj (T x)
  let GQ : Subgroup (MulAut Q) := Subgroup.zpowers a
  let Ω := MulAction.orbitRel.Quotient GQ Q
  let ω1 : Ω := Quotient.mk'' (1 : Q)
  let Ω' := {ω : Ω // ω ≠ ω1}
  let r : Ω' → Q := fun ω => Quotient.out ω.1
  have hxord : orderOf x = h := by
    simpa [hH] using orderOf_eq_card_of_forall_mem_zpowers hxgen
  have hxpow : x ^ h = 1 := by
    simpa [hxord] using pow_orderOf_eq_one x
  have ha_apply_pow (k : ℕ) (q : Q) : (a ^ k) q = φQ (x ^ k) q := by
    induction k with
    | zero =>
        simp [a, φQ]
    | succ k ih =>
        simp [pow_succ', a, φQ, ih]
  have hω1_out : Quotient.out ω1 = (1 : Q) := by
    have hq :
        (Quotient.mk'' (Quotient.out ω1) : Ω) = Quotient.mk'' (1 : Q) := by
      simp [ω1]
    have hrel : MulAction.orbitRel GQ Q (Quotient.out ω1) (1 : Q) := Quotient.exact hq
    have hmem : Quotient.out ω1 ∈ MulAction.orbit GQ (1 : Q) := (MulAction.orbitRel_apply).1 hrel
    rcases (MulAction.mem_orbit_iff).1 hmem with ⟨g, hg⟩
    simpa [GQ] using hg.symm
  have hS_single (y : H) (q : Q) :
      ∃ c : F, c ≠ 0 ∧ (e.symm.conj (T y)) (Finsupp.single q (1 : F)) =
        c • Finsupp.single ((φQ y) q) 1 := by
    have hbq : e (Finsupp.single q (1 : F)) = b q := by
      simp [e_apply, b]
    have hσq :
        σ (SemidirectProduct.inl (repQ q)) = (ρ (repQ q) : Module.End F V) := by
      simpa using congrArg (fun r : Representation F P V => r (repQ q)) hσ
    have hT :
        T y (b q) = ρ (φ y (repQ q)) := by
      calc
        T y (b q)
            = τ y ∘ₗ b q ∘ₗ τ y⁻¹ := by
                simp [T, τ, Representation.linHom_apply]
        _ = τ y ∘ₗ (ρ (repQ q) : Module.End F V) ∘ₗ τ y⁻¹ := by
                rfl
        _ = (σ (SemidirectProduct.inr y) : Module.End F V) ∘ₗ
              (ρ (repQ q) : Module.End F V) ∘ₗ
              (σ (SemidirectProduct.inr y)⁻¹ : Module.End F V) := by
                simp [τ]
        _ = (σ (SemidirectProduct.inr y) : Module.End F V) ∘ₗ
              σ (SemidirectProduct.inl (repQ q)) ∘ₗ
              (σ (SemidirectProduct.inr y)⁻¹ : Module.End F V) := by
                rw [← hσq]
        _ = σ
              (SemidirectProduct.inr y * SemidirectProduct.inl (repQ q) *
                (SemidirectProduct.inr y)⁻¹) := by
                ext v
                simp [Module.End.mul_apply, mul_assoc]
        _ = σ (SemidirectProduct.inl (φ y (repQ q))) := by
              simpa using
                congrArg σ
                  (theorem_2_5_conj_inl (φ := φ) (g := SemidirectProduct.inr y) (q := repQ q))
        _ = ρ (φ y (repQ q)) := by
              simpa using
                congrArg (fun r : Representation F P V => r (φ y (repQ q))) hσ
    have hquot :
        (((φ y (repQ q) : P) : Q)) = ((repQ ((φQ y) q) : P) : Q) := by
      let fy : Q →* Q :=
        QuotientGroup.map (Subgroup.center P) (Subgroup.center P) (φ y) <| by
          intro z hz
          have hzfixed : φ y z = z := hcenter_fixed y ⟨z, hz⟩
          simpa [hzfixed] using hz
      have hfy : fy q = (((φ y (repQ q) : P) : Q)) := by
        by_cases hq : q = 1
        · subst q
          simp [repQ, fy]
        · have hrepQ' : repQ q = Quotient.out q := by
            simp [repQ, hq]
          calc
            fy q = fy (((Quotient.out q : P) : Q)) := by
              simp
            _ = (((φ y (Quotient.out q) : P) : Q)) := by
              change
                (QuotientGroup.map (Subgroup.center P) (Subgroup.center P) (φ y) (by
                  intro z hz
                  have hzfixed : φ y z = z := hcenter_fixed y ⟨z, hz⟩
                  simpa [hzfixed] using hz) (((Quotient.out q : P) : Q))) =
                  (((φ y (Quotient.out q) : P) : Q))
              rfl
            _ = (((φ y (repQ q) : P) : Q)) := by
              rw [hrepQ']
      calc
        (((φ y (repQ q) : P) : Q)) = fy q := by
          simpa using hfy.symm
        _ = (φQ y) q := by
          rfl
        _ = ((repQ ((φQ y) q) : P) : Q) := (hrepQ ((φQ y) q)).symm
    have hcenter : φ y (repQ q) / repQ ((φQ y) q) ∈ Subgroup.center P := by
      exact (QuotientGroup.eq_iff_div_mem).mp hquot
    obtain ⟨c, hc⟩ := center_apply_eq_smul_id_of_irreducible
      (ρ := ρ) (z := φ y (repQ q) / repQ ((φQ y) q)) hcenter
    have hρ :
        (ρ (φ y (repQ q)) : Module.End F V) = c • b ((φQ y) q) := by
      calc
        (ρ (φ y (repQ q)) : Module.End F V)
            = (ρ ((φ y (repQ q) / repQ ((φQ y) q)) * repQ ((φQ y) q)) : Module.End F V) := by
                congr 1
                simp [div_eq_mul_inv, mul_assoc]
        _ = (ρ (φ y (repQ q) / repQ ((φQ y) q)) : Module.End F V) *
              (ρ (repQ ((φQ y) q)) : Module.End F V) := by
                simpa using (ρ.map_mul (φ y (repQ q) / repQ ((φQ y) q)) (repQ ((φQ y) q)))
        _ = (c • (1 : Module.End F V)) * (ρ (repQ ((φQ y) q)) : Module.End F V) := by
              rw [hc]
        _ = c • b ((φQ y) q) := by
              simp [b]
    have hmain :
        (e.symm.conj (T y)) (Finsupp.single q (1 : F)) =
          c • Finsupp.single ((φQ y) q) 1 := by
      apply e.injective
      calc
        e ((e.symm.conj (T y)) (Finsupp.single q (1 : F))) = T y (e (Finsupp.single q (1 : F))) := by
              simp [LinearEquiv.conj_apply]
        _ = T y (b q) := by rw [hbq]
        _ = ρ (φ y (repQ q)) := hT
        _ = c • b ((φQ y) q) := hρ
        _ = e (c • Finsupp.single ((φQ y) q) 1) := by
              simp [e_apply, b]
    have hc_ne_zero : c ≠ 0 := by
      intro hc0
      have hρ_ne_zero : (ρ (φ y (repQ q)) : Module.End F V) ≠ 0 := by
        intro hzero
        have hzero' :
            (ρ ((φ y (repQ q))⁻¹) : Module.End F V) * (ρ (φ y (repQ q)) : Module.End F V) = 0 := by
          simpa using congrArg
            (fun f : Module.End F V => (ρ ((φ y (repQ q))⁻¹) : Module.End F V) * f) hzero
        have hone : (1 : Module.End F V) = 0 := by
          calc
            (1 : Module.End F V)
                = (ρ ((φ y (repQ q))⁻¹) : Module.End F V) * (ρ (φ y (repQ q)) : Module.End F V) := by
                    simpa using
                      (ρ.map_mul ((φ y (repQ q))⁻¹) (φ y (repQ q)))
            _ = 0 := hzero'
        exact one_ne_zero hone
      have hzero : (ρ (φ y (repQ q)) : Module.End F V) = 0 := by
        calc
          (ρ (φ y (repQ q)) : Module.End F V) = c • b ((φQ y) q) := hρ
          _ = 0 := by simp [hc0]
      exact hρ_ne_zero hzero
    exact ⟨c, hc_ne_zero, hmain⟩
  have hS_one : S (Finsupp.single (1 : Q) (1 : F)) = Finsupp.single (1 : Q) 1 := by
    apply e.injective
    calc
      e (S (Finsupp.single (1 : Q) (1 : F))) = T x (e (Finsupp.single (1 : Q) (1 : F))) := by
            simp [S, LinearEquiv.conj_apply]
      _ = T x (1 : Module.End F V) := by
            simp [e_apply, repQ]
      _ = 1 := by
            ext v
            simp [T, τ, Representation.linHom_apply]
      _ = e (Finsupp.single (1 : Q) (1 : F)) := by
            simp [e_apply, repQ]
  let c : Q → F := fun q =>
    if hq : q = 1 then 1 else Classical.choose (hS_single x q)
  have hc_ne_zero (q : Q) : c q ≠ 0 := by
    by_cases hq : q = 1
    · simp [c, hq]
    · simpa [c, hq] using (Classical.choose_spec (hS_single x q)).1
  have hS_basis (q : Q) :
      S (Finsupp.single q (1 : F)) = c q • Finsupp.single ((a) q) 1 := by
    by_cases hq : q = 1
    · subst q
      simp [c, hS_one, a]
    · simpa [S, a, c, hq] using (Classical.choose_spec (hS_single x q)).2
  let ev : Q → (Q →₀ F) →ₗ[F] F := fun q =>
    { toFun := fun f => f q
      map_add' := by
        intro f g
        simp
      map_smul' := by
        intro t f
        simp }
  have hS_ev (q : Q) : ((ev ((a) q)).comp S) = c q • ev q := by
    apply Finsupp.lhom_ext
    intro r z
    rw [LinearMap.comp_apply]
    rw [show Finsupp.single r z = z • Finsupp.single r (1 : F) by simp]
    rw [map_smul, hS_basis]
    by_cases hrq : r = q
    · subst r
      simp
      change Finsupp.single (a q) (z * c q) (a q) =
        c q * Finsupp.single q z q
      simp [Finsupp.single_eq_same, mul_comm]
    · simp
      change Finsupp.single (a r) (z * c r) (a q) =
        c q * Finsupp.single r z q
      simp [hrq, a.injective.eq_iff]
  have hS_apply (f : Q →₀ F) (q : Q) :
      (S f) ((a) q) = c q * f q := by
    have h := congrArg (fun L : (Q →₀ F) →ₗ[F] F => L f) (hS_ev q)
    change (S f) (a q) = c q * f q
    exact h
  have hS_pow : S ^ h = 1 := by
    have hpow_conj :
        (e.symm.conj (T x)) ^ h = e.symm.conj ((T x) ^ h) := by
      exact (map_pow e.symm.conjRingEquiv (T x) h).symm
    calc
      S ^ h = (e.symm.conj (T x)) ^ h := by rfl
      _ = e.symm.conj ((T x) ^ h) := hpow_conj
      _ = e.symm.conj (T (x ^ h)) := by simp [T.map_pow]
      _ = 1 := by
            ext f
            simp [LinearEquiv.conj_apply, hxpow]
  have hS_pow_single (q : Q) :
      ∀ n : ℕ, ∃ d : F, d ≠ 0 ∧
        (S ^ n) (Finsupp.single q (1 : F)) = d • Finsupp.single (((a) ^ n) q) 1 := by
    intro n
    induction n with
    | zero =>
        refine ⟨1, one_ne_zero, by simp⟩
    | succ n ih =>
        rcases ih with ⟨d, hd_ne_zero, hd⟩
        refine ⟨d * c (((a) ^ n) q), mul_ne_zero hd_ne_zero (hc_ne_zero _), ?_⟩
        calc
          (S ^ (n + 1)) (Finsupp.single q (1 : F))
              = S ((S ^ n) (Finsupp.single q (1 : F))) := by
                  simp [pow_succ']
          _ = S (d • Finsupp.single (((a) ^ n) q) 1) := by rw [hd]
          _ = d • S (Finsupp.single (((a) ^ n) q) 1) := by rw [map_smul]
          _ = d • (c (((a) ^ n) q) • Finsupp.single ((a) (((a) ^ n) q)) 1) := by
                rw [hS_basis]
          _ = (d * c (((a) ^ n) q)) • Finsupp.single (((a) ^ (n + 1)) q) 1 := by
                simp [pow_succ']
  have ha_pow_ne_fix_of_ne_one {q : Q} (hq : q ≠ 1) {k : ℕ} (hk0 : 0 < k) (hkh : k < h) :
      ((a) ^ k) q ≠ q := by
    intro hfix
    have hxk_ne_one : x ^ k ≠ 1 := by
      intro hxk
      have hdiv : orderOf x ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hxk
      rw [hxord] at hdiv
      exact (Nat.not_le_of_gt hkh) (Nat.le_of_dvd hk0 hdiv)
    have hfix' : φQ (x ^ k) q = q := by
      simpa [ha_apply_pow] using hfix
    exact hq <|
      theorem_2_5_hE_phiQ_fixed_eq_one
        (p := p) (P := P) (hH := hH) (hh := hh) (φ := φ) hcentralizer
        (y := x ^ k) hxk_ne_one hfix'
  have hr_ne_one (ω : Ω') : r ω ≠ 1 := by
    intro hr1
    apply ω.2
    have hq : (Quotient.mk'' (r ω) : Ω) = ω.1 := by
      simp [r]
    calc
      ω.1 = Quotient.mk'' (r ω) := hq.symm
      _ = Quotient.mk'' (1 : Q) := by simp [hr1]
      _ = ω1 := rfl
  have hperiod_r (ω : Ω') : Function.minimalPeriod ((a) • ·) (r ω) = h := by
    have hperiodic : (a ^ h) • r ω = r ω := by
      simp [ha_apply_pow, hxpow]
    have hdiv : Function.minimalPeriod ((a) • ·) (r ω) ∣ h :=
      (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).1 hperiodic
    have hpos_period : 0 < Function.minimalPeriod ((a) • ·) (r ω) := by
      exact Nat.pos_of_dvd_of_pos hdiv hh_pos
    have hle : h ≤ Function.minimalPeriod ((a) • ·) (r ω) := by
      by_contra hlt
      have hlt' : Function.minimalPeriod ((a) • ·) (r ω) < h := Nat.lt_of_not_ge hlt
      have hfix :
          ((a) ^ Function.minimalPeriod ((a) • ·) (r ω)) (r ω) = r ω := by
        simpa using
          ((MulAction.pow_smul_eq_iff_minimalPeriod_dvd
            (a := a) (b := r ω)).2 dvd_rfl)
      exact
        ha_pow_ne_fix_of_ne_one (hr_ne_one ω) hpos_period hlt' hfix
    exact le_antisymm (Nat.le_of_dvd hh_pos hdiv) hle
  have hcard_orbit_r (ω : Ω') :
      Nat.card (MulAction.orbit (Subgroup.zpowers a) (r ω)) = h := by
    let : Finite (MulAction.orbit (Subgroup.zpowers a) (r ω)) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    let : Fintype (MulAction.orbit (Subgroup.zpowers a) (r ω)) := Fintype.ofFinite _
    calc
      Nat.card (MulAction.orbit (Subgroup.zpowers a) (r ω))
          = Fintype.card (MulAction.orbit (Subgroup.zpowers a) (r ω)) := by simp
      _
          = Function.minimalPeriod ((a) • ·) (r ω) := by
              symm
              exact MulAction.minimalPeriod_eq_card a (r ω)
      _ = h := hperiod_r ω
  have hcard_orbit_one :
      Nat.card (MulAction.orbit (Subgroup.zpowers a) (1 : Q)) = 1 := by
    let : Finite (MulAction.orbit (Subgroup.zpowers a) (1 : Q)) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    let : Fintype (MulAction.orbit (Subgroup.zpowers a) (1 : Q)) := Fintype.ofFinite _
    have hperiod_one : Function.minimalPeriod ((a) • ·) (1 : Q) = 1 := by
      rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
      simp [Function.IsFixedPt, a]
    calc
      Nat.card (MulAction.orbit (Subgroup.zpowers a) (1 : Q))
          = Fintype.card (MulAction.orbit (Subgroup.zpowers a) (1 : Q)) := by simp
      _
          = Function.minimalPeriod ((a) • ·) (1 : Q) := by
              symm
              exact MulAction.minimalPeriod_eq_card a (1 : Q)
      _ = 1 := hperiod_one
  let : NeZero h := NeZero.of_pos hh_pos
  let : Fintype Q := Fintype.ofFinite Q
  let : Fintype Ω := Fintype.ofFinite Ω
  let : Fintype Ω' := Subtype.fintype (fun ω : Ω => ω ≠ ω1)
  let (ω : Ω) : Finite (MulAction.orbit GQ (Quotient.out ω)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let (ω : Ω) : Fintype (MulAction.orbit GQ (Quotient.out ω)) := Fintype.ofFinite _
  have hcardQ_orbits : Nat.card Q = h * Nat.card Ω' + 1 := by
    let π : Q → Ω := fun q => Quotient.mk'' q
    let SigmaQ : Type _ := Σ ω : Ω, { q : Q // π q = ω }
    let fω : Ω → ℕ := fun ω => Nat.card { q : Q // π q = ω }
    have hfiber_orbit (ω : Ω) : fω ω = Nat.card ω.orbit := by
      dsimp [fω, π]
      exact Nat.card_congr <|
        Equiv.subtypeEquivRight fun q =>
          (MulAction.orbitRel.Quotient.mem_orbit (a := q) (x := ω)).symm
    have hsum_sigma :
        Nat.card SigmaQ = ∑ ω : Ω, fω ω := by
      dsimp [SigmaQ]
      rw [Nat.card_sigma]
    have hsum_split :
        ∑ ω : Ω, fω ω = fω ω1 + ∑ ω : {ω : Ω // ω ≠ ω1}, fω ω.1 := by
      classical
      exact Fintype.sum_eq_add_sum_subtype_ne (f := fω) ω1
    have hω1_card : fω ω1 = 1 := by
      calc
        fω ω1 = Nat.card ω1.orbit := hfiber_orbit ω1
        _ = Nat.card (MulAction.orbit GQ (1 : Q)) := by rfl
        _ = 1 := hcard_orbit_one
    have hsum_const : ∑ ω : {ω : Ω // ω ≠ ω1}, fω ω.1 = ∑ _ : {ω : Ω // ω ≠ ω1}, h := by
      refine Fintype.sum_congr (f := fun ω : {ω : Ω // ω ≠ ω1} => fω ω.1)
        (g := fun _ : {ω : Ω // ω ≠ ω1} => h) ?_
      intro ω
      have horbit_out_card : Nat.card ω.1.orbit = Nat.card (MulAction.orbit GQ (r ω)) := by
        have hq : (Quotient.mk'' (r ω) : Ω) = ω.1 := Quotient.out_eq' ω.1
        rw [← hq, MulAction.orbitRel.Quotient.orbit_mk]
      calc
        fω ω.1 = Nat.card ω.1.orbit := hfiber_orbit ω.1
        _ = Nat.card (MulAction.orbit GQ (r ω)) := horbit_out_card
        _ = h := hcard_orbit_r ω
    have hcard_sigma_Q :
        Nat.card SigmaQ = Nat.card Q := by
      dsimp [SigmaQ]
      exact Nat.card_congr (Equiv.sigmaFiberEquiv π)
    have hsumQ := Eq.trans hcard_sigma_Q.symm hsum_sigma
    calc
      Nat.card Q = fω ω1 + ∑ ω : {ω : Ω // ω ≠ ω1}, fω ω.1 := by
        exact hsumQ.trans hsum_split
      _ = 1 + ∑ _ : {ω : Ω // ω ≠ ω1}, h := by rw [hω1_card, hsum_const]
      _ = 1 + Fintype.card {ω : Ω // ω ≠ ω1} * h := by simp
      _ = h * Nat.card {ω : Ω // ω ≠ ω1} + 1 := by
            rw [Nat.card_eq_fintype_card, Nat.mul_comm, Nat.add_comm]
      _ = h * Nat.card Ω' + 1 := by rfl
  let gS : (Q →₀ F) ≃ₗ[F] (Q →₀ F) :=
    LinearEquiv.ofLinearMap S (S ^ (h - 1))
      (by
        apply LinearMap.ext
        intro v
        have hpow' := congrArg (fun T : Module.End F (Q →₀ F) => T v) hS_pow
        have hlast : S ((S ^ (h - 1)) v) = v := by
          trans (S ^ (1 + (h - 1))) v
          · rw [← LinearMap.comp_apply]
            congr
            rw [pow_add]
            rfl
          have : 1 + (h - 1) = h := by omega
          rw [this]
          simpa using hpow'
        simpa [LinearMap.comp_apply] using hlast)
      (by
        apply LinearMap.ext
        intro v
        have hpow' := congrArg (fun T : Module.End F (Q →₀ F) => T v) hS_pow
        have hlast : (S ^ (h - 1)) (S v) = v := by
          trans (S ^ ((h - 1) + 1)) v
          · rw [pow_add]
            rfl
          have : (h - 1) + 1 = h := by omega
          rw [this]
          simpa using hpow'
        simpa [LinearMap.comp_apply] using hlast)
  have hgS_pow : gS ^ h = 1 := by
    apply LinearEquiv.toLinearMap_injective
    rw [LinearEquiv.toLinearMap_pow]
    change S ^ h = (1 : Module.End F (Q →₀ F))
    exact hS_pow
  let A : Fin h → Submodule F (Q →₀ F) := fun i => Module.End.eigenspace S (ε ^ (i : ℤ))
  let orbitVec : Ω' → Fin h → Q →₀ F := fun ω i =>
    ∑ n ∈ Finset.range h,
      (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) •
        ((S ^ n) (Finsupp.single (r ω) (1 : F)))
  have horbit_eq_of_pow_eq {ω ω' : Ω'} (hneq : ω ≠ ω') {k : ℕ} (hk : k < h) :
      ((a ^ k) (r ω)) ≠ r ω' := by
    intro hk_eq
    apply hneq
    apply Subtype.ext
    calc
      ω.1 = Quotient.mk'' (r ω) := by
            simp [r]
      _ = Quotient.mk'' (((a ^ k) (r ω)) : Q) := by
            apply Quotient.sound
            exact (MulAction.orbitRel_apply).2 <|
              (MulAction.mem_orbit_iff).2 ⟨(⟨a, Subgroup.mem_zpowers a⟩ ^ k)⁻¹, by
                rw [inv_smul_eq_iff]
                change (a ^ k) (r ω) = (a ^ k) • r ω
                rfl⟩
      _ = Quotient.mk'' (r ω') := by simp [hk_eq]
      _ = ω'.1 := by
            simp [r]
  have hpow_ne_one (ω : Ω') (k : ℕ) : ((a ^ k) (r ω)) ≠ (1 : Q) := by
    intro hk1
    apply hr_ne_one ω
    apply (a ^ k).injective
    simpa using hk1
  have horbitVec_mem (ω : Ω') (i : Fin h) :
      orbitVec ω i ∈ A i := by
    rw [Module.End.mem_eigenspace_iff]
    let δ : Q →₀ F := Finsupp.single (r ω) (1 : F)
    have hε_ne_zero : ε ≠ 0 := hε.ne_zero (Nat.ne_zero_of_lt hh_pos)
    have hlast : S ((S ^ (h - 1)) δ) = δ := by
      have hpow' := congrArg (fun T : Module.End F (Q →₀ F) => T δ) hS_pow
      trans (S ^ (1 + (h - 1))) δ
      · rw [← LinearMap.comp_apply]
        congr
        rw [pow_add]
        rfl
      have : (1 + (h - 1)) = h := by omega
      rw [this]
      simpa using hpow'
    have hcoeff0 :
        ε ^ (i : ℤ) * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) = 1 := by
      calc
        ε ^ (i : ℤ) * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ)
            = ε ^ ((i : ℤ) + (((i : ℕ) * (h - 1) : ℕ) : ℤ)) := by
                rw [← zpow_add₀ hε_ne_zero]
        _ = ε ^ (((i : ℕ) * h : ℕ) : ℤ) := by
              congr 1
              have : (i : ℕ) + (i : ℕ) * (h - 1) = (i : ℕ) * h := by
                set i := (i : ℕ)
                trans i * 1 + i * (h - 1)
                · omega
                rw [← mul_add, add_comm]
                congr
                omega
              exact_mod_cast this
        _ = (ε ^ h) ^ (i : ℕ) := by rw [zpow_natCast, pow_mul]; exact pow_right_comm ε (↑i) h
        _ = 1 := by simp [hε.pow_eq_one]
    have hcoeff_succ (n : ℕ) (hn : n < h - 1) :
        ε ^ (i : ℤ) * ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ) =
          ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ) := by
      calc
        ε ^ (i : ℤ) * ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)
            = ε ^ ((i : ℤ) + (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) := by
                rw [← zpow_add₀ hε_ne_zero]
        _ = ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ) := by
              congr 1
              have : (i : ℕ) + (i : ℕ) * (h - 1 - (n + 1)) = (i : ℕ) * (h - 1 - n) := by
                set i := (i : ℕ)
                trans i * 1 + i * (h - 1 - (n + 1))
                · omega
                rw [← mul_add]
                congr
                omega
              exact_mod_cast this
    calc
      S (orbitVec ω i)
          = ∑ n ∈ Finset.range h,
              (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • S ((S ^ n) δ) := by
                  simp [orbitVec, δ, map_sum, map_smul]
      _ =
          (∑ n ∈ Finset.range (h - 1),
            (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ)) + δ := by
              have hh_succ : (h - 1) + 1 = h := by
                simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hh_pos)
              calc
                ∑ n ∈ Finset.range h,
                    (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • S ((S ^ n) δ) =
                    ∑ n ∈ Finset.range ((h - 1) + 1),
                      (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • S ((S ^ n) δ) := by
                        rw [hh_succ]
                _ =
                    (ε ^ (((i : ℕ) * (h - 1 - (h - 1)) : ℕ) : ℤ)) • S ((S ^ (h - 1)) δ) +
                    ∑ n ∈ Finset.range (h - 1),
                      (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • S ((S ^ n) δ) := by
                        simpa using
                          (Finset.sum_range_succ_comm
                            (f := fun n =>
                              (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • S ((S ^ n) δ))
                            (h - 1))
                _ =
                    (∑ n ∈ Finset.range (h - 1),
                      (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ)) + δ := by
                        rw [add_comm]
                        congr 1
                        · refine Finset.sum_congr rfl ?_
                          intro n hn
                          simp [pow_succ', Module.End.mul_apply]
                        · simp [hlast]
      _ =
          ε ^ (i : ℤ) •
            ((ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ)) • δ +
              ∑ n ∈ Finset.range (h - 1),
                (ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) •
                  ((S ^ (n + 1)) δ)) := by
                    calc
                      (∑ n ∈ Finset.range (h - 1),
                          (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ)) + δ
                          =
                          δ + ∑ n ∈ Finset.range (h - 1),
                            (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ) := by
                              ac_rfl
                      _ =
                          ε ^ (i : ℤ) • ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) • δ +
                            ∑ n ∈ Finset.range (h - 1),
                              ε ^ (i : ℤ) •
                                ((ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ)) := by
                                  have hsum_shift :
                                      ∑ n ∈ Finset.range (h - 1),
                                        (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ) =
                                      ∑ n ∈ Finset.range (h - 1),
                                        ε ^ (i : ℤ) •
                                          ((ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) •
                                            ((S ^ (n + 1)) δ)) := by
                                              refine Finset.sum_congr rfl ?_
                                              intro n hn
                                              calc
                                                (ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ) =
                                                    (ε ^ (i : ℤ) *
                                                      ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) •
                                                        ((S ^ (n + 1)) δ) := by
                                                          rw [hcoeff_succ n (Finset.mem_range.mp hn)]
                                                _ =
                                                    ε ^ (i : ℤ) •
                                                      ((ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) •
                                                        ((S ^ (n + 1)) δ)) := by
                                                          rw [mul_smul]
                                  rw [hsum_shift]
                                  congr
                                  calc
                                    δ = (1 : F) • δ := by simp
                                    _ =
                                        (ε ^ (i : ℤ) *
                                          ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ)) • δ := by
                                            rw [hcoeff0]
                                    _ = ε ^ (i : ℤ) • ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) • δ := by
                                            rw [mul_smul]
                      _ =
                          ε ^ (i : ℤ) •
                            ((ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ)) • δ +
                              ∑ n ∈ Finset.range (h - 1),
                                (ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) •
                                  ((S ^ (n + 1)) δ)) := by
                                    rw [← Finset.smul_sum, ← smul_add]
      _ = ε ^ (i : ℤ) • orbitVec ω i := by
            have hh_succ : (h - 1) + 1 = h := by
              simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hh_pos)
            have horbit_expand :
                orbitVec ω i =
                  (ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ)) • δ +
                    ∑ n ∈ Finset.range (h - 1),
                      (ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ) := by
              dsimp [orbitVec, δ]
              calc
                ∑ n ∈ Finset.range h,
                    ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ) •
                      (S ^ n) (Finsupp.single (r ω) (1 : F)) =
                    ∑ n ∈ Finset.range ((h - 1) + 1),
                      ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ) •
                        (S ^ n) (Finsupp.single (r ω) (1 : F)) := by
                          rw [hh_succ]
                _ =
                    ∑ n ∈ Finset.range (h - 1),
                      ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ) •
                        (S ^ (n + 1)) (Finsupp.single (r ω) (1 : F)) +
                    ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) •
                      (S ^ 0) (Finsupp.single (r ω) (1 : F)) := by
                        simpa using
                          (Finset.sum_range_succ'
                            (f := fun n =>
                              ε ^ (((i : ℕ) * (h - 1 - n) : ℕ) : ℤ) •
                                (S ^ n) (Finsupp.single (r ω) (1 : F)))
                            (h - 1))
                _ =
                    (ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ)) • δ +
                      ∑ n ∈ Finset.range (h - 1),
                        (ε ^ (((i : ℕ) * (h - 1 - (n + 1)) : ℕ) : ℤ)) • ((S ^ (n + 1)) δ) := by
                          simp [δ, add_comm]
            rw [horbit_expand]
  have horbitVec_eval_self (ω : Ω') (i : Fin h) :
      orbitVec ω i (r ω) = ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) := by
    dsimp [orbitVec]
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single 0]
    · simp
    · intro n hn hn0
      rcases hS_pow_single (r ω) n with ⟨d, hd_ne_zero, hd⟩
      rw [Finsupp.smul_apply, hd, Finsupp.smul_apply]
      have hneq : ((a ^ n) (r ω)) ≠ r ω :=
        ha_pow_ne_fix_of_ne_one (hr_ne_one ω) (Nat.pos_of_ne_zero hn0) (Finset.mem_range.mp hn)
      simp [hneq]
    · intro h0
      exfalso
      exact h0 (by simpa using hh_pos)
  have horbitVec_eval_other {ω ω' : Ω'} (hneq : ω ≠ ω') (i : Fin h) :
      orbitVec ω i (r ω') = 0 := by
    dsimp [orbitVec]
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero ?_
    intro n hn
    rcases hS_pow_single (r ω) n with ⟨d, hd_ne_zero, hd⟩
    rw [Finsupp.smul_apply, hd, Finsupp.smul_apply]
    have hneq' : ((a ^ n) (r ω)) ≠ r ω' := horbit_eq_of_pow_eq hneq (Finset.mem_range.mp hn)
    simp [hneq']
  have horbitVec_eval_one (ω : Ω') (i : Fin h) :
      orbitVec ω i (1 : Q) = 0 := by
    dsimp [orbitVec]
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero ?_
    intro n hn
    rcases hS_pow_single (r ω) n with ⟨d, hd_ne_zero, hd⟩
    rw [Finsupp.smul_apply, hd, Finsupp.smul_apply]
    simp [hpow_ne_one ω n]
  have hcoeff0_ne_zero (i : Fin h) :
      ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) ≠ 0 := by
    exact zpow_ne_zero _ (hε.ne_zero (Nat.ne_zero_of_lt hh_pos))
  have hlower_nonzero (i : Fin h) (hi : i ≠ 0) :
      Nat.card Ω' ≤ Module.finrank F (A i) := by
    let L : (Ω' →₀ F) →ₗ[F] (Q →₀ F) :=
      Finsupp.linearCombination F fun ω => orbitVec ω i
    let LE : (Ω' →₀ F) →ₗ[F] A i :=
      L.codRestrict (A i) <| by
        intro f
        rw [Finsupp.linearCombination_apply]
        exact Submodule.sum_mem _ fun ω hω => Submodule.smul_mem _ _ (horbitVec_mem ω i)
    have hL_inj : Function.Injective L := by
      have horbitVec_eval_r (ω : Ω') :
          ∀ ω' : Ω', orbitVec ω' i (r ω) =
            if ω' = ω then ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) else 0 := by
        intro ω'
        by_cases hEq : ω' = ω
        · subst hEq
          simp [horbitVec_eval_self]
        · simp [hEq, horbitVec_eval_other hEq i]
      intro f g hfg
      ext ω
      have heval := congrArg (fun v : Q →₀ F => v (r ω)) hfg
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply] at heval
      simp [Finsupp.sum_apply, Finsupp.smul_apply, horbitVec_eval_r] at heval
      have hf :
          f.sum (fun a b => if a = ω then b * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) else 0) =
            f ω * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) := by
        simpa using
          (Finsupp.sum_eq_single (f := f) ω
            (g := fun a b => if a = ω then b * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) else 0)
            (fun a ha hne => by simp [hne])
            (fun _ => by simp))
      have hg :
          g.sum (fun a b => if a = ω then b * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) else 0) =
            g ω * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) := by
        simpa using
          (Finsupp.sum_eq_single (f := g) ω
            (g := fun a b => if a = ω then b * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) else 0)
            (fun a ha hne => by simp [hne])
            (fun _ => by simp))
      have heval' :
          f ω * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) =
            g ω * ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) := by
        exact hf.symm.trans (heval.trans hg)
      have hcoeff_ne_zero :
          ε ^ (((i : ℕ) * (h - 1) : ℕ) : ℤ) ≠ 0 := hcoeff0_ne_zero i
      exact mul_right_cancel₀ hcoeff_ne_zero heval'
    have hLE_inj : Function.Injective LE := by
      intro f g hfg
      apply hL_inj
      exact congrArg Subtype.val hfg
    have hfin := LinearMap.finrank_le_finrank_of_injective (f := LE) hLE_inj
    simpa using hfin
  let orbitBase : Option Ω' → Q →₀ F := fun
    | none => Finsupp.single (1 : Q) (1 : F)
    | some ω => orbitVec ω 0
  have horbitBase_mem : ∀ o, orbitBase o ∈ A 0 := by
    intro o
    cases o with
    | none =>
        rw [Module.End.mem_eigenspace_iff]
        simpa [orbitBase] using hS_one
    | some ω =>
        simpa [orbitBase, A] using horbitVec_mem ω (0 : Fin h)
  have hlower_zero : Nat.card Ω' + 1 ≤ Module.finrank F (A 0) := by
    let L0 : (Option Ω' →₀ F) →ₗ[F] (Q →₀ F) :=
      Finsupp.linearCombination F orbitBase
    let L0E : (Option Ω' →₀ F) →ₗ[F] A 0 :=
      L0.codRestrict (A 0) <| by
        intro f
        rw [Finsupp.linearCombination_apply]
        exact Submodule.sum_mem _ fun o ho => Submodule.smul_mem _ _ (horbitBase_mem o)
    have hL0_inj : Function.Injective L0 := by
      have horbitBase_eval_one :
          ∀ o : Option Ω', orbitBase o (1 : Q) = if o = none then 1 else 0 := by
        intro o
        cases o with
        | none => simp [orbitBase]
        | some ω => simp [orbitBase, horbitVec_eval_one]
      have horbitBase_eval_r (ω : Ω') :
          ∀ o : Option Ω', orbitBase o (r ω) = if o = some ω then 1 else 0 := by
        intro o
        cases o with
        | none =>
            simp [orbitBase, hr_ne_one ω]
        | some ω' =>
            by_cases hEq : ω' = ω
            · subst hEq
              simp [orbitBase, horbitVec_eval_self]
            · simp [orbitBase, hEq, horbitVec_eval_other hEq]
      intro f g hfg
      ext o
      cases o with
      | none =>
          have heval := congrArg (fun v : Q →₀ F => v (1 : Q)) hfg
          rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply] at heval
          rw [Finsupp.sum_fintype _ _ (by intro o; simp),
            Finsupp.sum_fintype _ _ (by intro o; simp)] at heval
          simpa [horbitBase_eval_one] using heval
      | some ω =>
          have heval := congrArg (fun v : Q →₀ F => v (r ω)) hfg
          rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply] at heval
          rw [Finsupp.sum_fintype _ _ (by intro o; simp),
            Finsupp.sum_fintype _ _ (by intro o; simp)] at heval
          have hf_single : (∑ x : Ω', if x = ω then f (some x) else 0) = f (some ω) := by
            simpa using
              (Fintype.sum_eq_single ω (fun x hx => by simp [hx]) :
                (∑ x : Ω', if x = ω then f (some x) else 0) = if ω = ω then f (some ω) else 0)
          have hg_single : (∑ x : Ω', if x = ω then g (some x) else 0) = g (some ω) := by
            simpa using
              (Fintype.sum_eq_single ω (fun x hx => by simp [hx]) :
                (∑ x : Ω', if x = ω then g (some x) else 0) = if ω = ω then g (some ω) else 0)
          simpa [horbitBase_eval_r, hf_single, hg_single] using heval
    have hL0E_inj : Function.Injective L0E := by
      intro f g hfg
      apply hL0_inj
      exact congrArg Subtype.val hfg
    have hfin := LinearMap.finrank_le_finrank_of_injective (f := L0E) hL0E_inj
    simpa using hfin
  have hqsum_nat_A :
      Module.finrank F (Q →₀ F) = ∑ i : Fin h, Module.finrank F (A i) := by
    let : ∀ i : Fin h, Module.Free F (A i) := fun i =>
      Module.Free.of_divisionRing (K := F) (V := A i)
    let : ∀ i : Fin h, Module.Finite F (A i) := fun i =>
      Module.Finite.of_basis (Module.finBasis F (A i))
    let eA : (⨁ i : Fin h, A i) ≃ₗ[F] (Q →₀ F) :=
      LinearEquiv.ofBijective
        (DirectSum.coeLinearMap A)
        (proposition_2_4_a (g := gS) (h := h) (hg := hgS_pow) (hh := hh2) (hε := hε))
    calc
      Module.finrank F (Q →₀ F) = Module.finrank F (⨁ i : Fin h, A i) := by
        rw [LinearEquiv.finrank_eq eA]
      _ = ∑ i : Fin h, Module.finrank F (A i) := by
        simp
  have hqsum_nat :
      Nat.card Q = ∑ i : Fin h, Module.finrank F (A i) := by
    calc
      Nat.card Q = Module.finrank F (Q →₀ F) := by
            simp [Nat.card_eq_fintype_card]
      _ = ∑ i : Fin h, Module.finrank F (A i) := hqsum_nat_A
  let N : ℕ := Nat.card Ω'
  have hsumA : ∑ i : Fin h, Module.finrank F (A i) = h * N + 1 := by
    simpa [N] using hqsum_nat.symm.trans hcardQ_orbits
  have hcard_nonzero : Fintype.card {i : Fin h // i ≠ 0} = h - 1 := by
      calc
        Fintype.card {i : Fin h // i ≠ 0} = Fintype.card (Fin h) - Fintype.card {i : Fin h // i = 0} := by
          simp
      _ = h - 1 := by simp
  have hnonzero_sum_lower :
      (h - 1) * N ≤ ∑ i : {j : Fin h // j ≠ 0}, Module.finrank F (A i.1) := by
    calc
      (h - 1) * N = ∑ i : {j : Fin h // j ≠ 0}, N := by
            simp [N, hcard_nonzero]
      _ ≤ ∑ i : {j : Fin h // j ≠ 0}, Module.finrank F (A i.1) := by
            show (∑ i ∈ (Finset.univ : Finset {j : Fin h // j ≠ 0}), N) ≤
                ∑ i ∈ (Finset.univ : Finset {j : Fin h // j ≠ 0}),
                  Module.finrank F (A i.1)
            exact
              Finset.sum_le_sum (s := (Finset.univ : Finset {j : Fin h // j ≠ 0}))
                (fun i _ => hlower_nonzero i.1 i.2)
  have hsum0 :
      ∑ i : Fin h, Module.finrank F (A i) =
        Module.finrank F (A 0) + ∑ i : {j : Fin h // j ≠ 0}, Module.finrank F (A i.1) := by
          simpa using
            (Fintype.sum_eq_add_sum_subtype_ne
              (f := fun i : Fin h => Module.finrank F (A i)) 0)
  have hzero_eq : Module.finrank F (A 0) = N + 1 := by
    have hzero_lower : N + 1 ≤ Module.finrank F (A 0) := by
      simpa [N] using hlower_zero
    rw [hsum0] at hsumA
    have hmul : h * N = N + (h - 1) * N := by
      nth_rewrite 1 [← Nat.succ_pred_eq_of_pos hh_pos]
      rw [Nat.succ_mul]
      ac_rfl
    rw [hmul] at hsumA
    have hzero_upper : Module.finrank F (A 0) ≤ N + 1 := by
      omega
    exact le_antisymm hzero_upper hzero_lower
  have hfinrank_eq (ii : Fin h) (hii : ii ≠ 0) :
      Module.finrank F (A 0) = Module.finrank F (A ii) + 1 := by
    let B : Type := {j : Fin h // j ≠ ii}
    let j0 : B := ⟨0, hii.symm⟩
    have hcardB : Fintype.card B = h - 1 := by
      simp [B]
    have hcard_rest : Fintype.card {j : B // j ≠ j0} = h - 2 := by
      calc
        Fintype.card {j : B // j ≠ j0} = Fintype.card B - Fintype.card {j : B // j = j0} := by
          simp
        _ = (h - 1) - 1 := by rw [hcardB, Fintype.card_subtype_eq j0]
        _ = h - 2 := by omega
    have hsumii :
        ∑ i : Fin h, Module.finrank F (A i) =
          Module.finrank F (A ii) + ∑ j : B, Module.finrank F (A j.1) := by
            simpa using
              (Fintype.sum_eq_add_sum_subtype_ne
                (f := fun i : Fin h => Module.finrank F (A i)) ii)
    have hsumB :
        ∑ j : B, Module.finrank F (A j.1) =
          Module.finrank F (A 0) + ∑ j : {j : B // j ≠ j0}, Module.finrank F (A j.1.1) := by
            simpa using
              (Fintype.sum_eq_add_sum_subtype_ne
                (f := fun j : B => Module.finrank F (A j.1)) j0)
    have hrest_lower :
        (h - 1) * N + 1 ≤ ∑ j : B, Module.finrank F (A j.1) := by
      rw [hsumB]
      have hsum_rest :
          (h - 2) * N ≤ ∑ j : {j : B // j ≠ j0}, Module.finrank F (A j.1.1) := by
        calc
          (h - 2) * N = ∑ j : {j : B // j ≠ j0}, N := by
                simp [N, hcard_rest]
          _ ≤ ∑ j : {j : B // j ≠ j0}, Module.finrank F (A j.1.1) := by
                show (∑ j ∈ (Finset.univ : Finset {j : B // j ≠ j0}), N) ≤
                    ∑ j ∈ (Finset.univ : Finset {j : B // j ≠ j0}),
                      Module.finrank F (A j.1.1)
                exact
                  Finset.sum_le_sum (s := (Finset.univ : Finset {j : B // j ≠ j0}))
                    (fun j _ =>
                      hlower_nonzero j.1.1 <| by
                        intro hj0
                        exact j.2 <| Subtype.ext <| by simpa [j0] using hj0)
      have hzero_ge : N + 1 ≤ Module.finrank F (A 0) := by
        simpa [N] using hzero_eq.ge
      have hsplit : (h - 1) * N + 1 = (N + 1) + (h - 2) * N := by
        have hh1_pos : 0 < h - 1 := by omega
        rw [← Nat.succ_pred_eq_of_pos hh1_pos, Nat.succ_mul]
        ac_rfl
      rw [hsplit]
      omega
    have hii_lower : N ≤ Module.finrank F (A ii) := by
      simpa [N] using hlower_nonzero ii hii
    rw [hsumii] at hsumA
    have hmul : h * N = N + (h - 1) * N := by
      nth_rewrite 1 [← Nat.succ_pred_eq_of_pos hh_pos]
      rw [Nat.succ_mul]
      ac_rfl
    have hsplit : h * N + 1 = N + ((h - 1) * N + 1) := by
      rw [hmul]
      ac_rfl
    rw [hsplit] at hsumA
    have hii_upper : Module.finrank F (A ii) ≤ N := by
      omega
    have hii_eq : Module.finrank F (A ii) = N := le_antisymm hii_upper hii_lower
    omega
  have hEigenspaceEquiv (μ : F) :
      Module.End.eigenspace S μ ≃ₗ[F] Module.End.eigenspace (T x) μ := by
    refine
      { toFun := fun v =>
          ⟨e v, by
            refine (Module.End.mem_eigenspace_iff).2 ?_
            have hv : S v.1 = μ • v.1 := (Module.End.mem_eigenspace_iff).1 v.2
            have hv' := congrArg e hv
            simpa [S, LinearEquiv.conj_apply] using hv'⟩
        invFun := fun v =>
          ⟨e.symm v, by
            refine (Module.End.mem_eigenspace_iff).2 ?_
            have hv : T x v.1 = μ • v.1 := (Module.End.mem_eigenspace_iff).1 v.2
            have hv' := congrArg e.symm hv
            simpa [S, LinearEquiv.conj_apply] using hv'⟩
        left_inv := by
          intro v
          ext
          simp
        right_inv := by
          intro v
          ext
          simp
        map_add' := by
          intro v w
          ext
          simp
        map_smul' := by
          intro t v
          ext
          simp }
  have hfinrank_intertwine (z : ℤ) :
      Module.finrank F (intertwiningSubmodule (τ x) (ε ^ z • τ x)) =
        Module.finrank F (Module.End.eigenspace S (ε ^ z)) := by
    calc
      Module.finrank F (intertwiningSubmodule (τ x) (ε ^ z • τ x))
          = Module.finrank F (Module.End.eigenspace (T x) (ε ^ z)) := by
              rw [theorem_2_5_hE_intertwining_eq_eigenspace τ x (ε ^ z)]
      _ = Module.finrank F (Module.End.eigenspace S (ε ^ z)) := by
            symm
            exact LinearEquiv.finrank_eq (hEigenspaceEquiv (ε ^ z))
  let ii : Fin h := @Fin.intCast h (by infer_instance) m
  have hii_ne_zero : ii ≠ 0 := by
    intro hii0
    have hval : ii.val = (m % (h : ℤ)).toNat := by
      dsimp [ii]
      exact Fin.val_intCast (n := h) m
    have htoNat : (m % h).toNat = 0 := by
      simpa [hii0] using hval.symm
    have hmod_nonpos : m % (h : ℤ) ≤ 0 := Int.toNat_eq_zero.mp htoNat
    have hmod_nonneg : 0 ≤ m % h := Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hh_ne_zero)
    have hmod : m % (h : ℤ) = 0 := by omega
    exact hm (by simpa using hmod)
  have hAii :
      A ii = Module.End.eigenspace S (ε ^ m) := by
    simpa [A, ii, gS] using
      eigenspace_eq_intCast (hh := hh2) (g := gS) (h := h) (hε := hε) m
  have hmainA :
      Module.finrank F (A 0) = Module.finrank F (Module.End.eigenspace S (ε ^ m)) + 1 := by
    calc
      Module.finrank F (A 0) = Module.finrank F (A ii) + 1 := hfinrank_eq ii hii_ne_zero
      _ = Module.finrank F (Module.End.eigenspace S (ε ^ m)) + 1 := by rw [hAii]
  change Module.finrank F
      (intertwiningSubmodule (τ x) (ε ^ (0 : ℤ) • τ x)) =
    Module.finrank F
      (intertwiningSubmodule (τ x) (ε ^ m • τ x)) + 1
  calc
    Module.finrank F (intertwiningSubmodule (τ x) (ε ^ (0 : ℤ) • τ x))
        = Module.finrank F (Module.End.eigenspace S (ε ^ (0 : ℤ))) := hfinrank_intertwine 0
    _ = Module.finrank F (A 0) := rfl
    _ = Module.finrank F (Module.End.eigenspace S (ε ^ m)) + 1 := hmainA
    _ = Module.finrank F (intertwiningSubmodule (τ x) (ε ^ m • τ x)) + 1 := by
          rw [← hfinrank_intertwine m]

public theorem CFSG.theorem_2_5_a {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
    {P : Type*} [Group P] [IsExtraspecial p P] (hp : Nat.card P = p ^ (2 * n + 1))
    {h : ℕ} {H : Type*} [Group H] [IsCyclic H] (hH : Nat.card H = h) (hh : Nat.Coprime h p)
    {φ : H →* MulAut P}
    (hcentralizer : ∀ x : H, x ≠ 1 → {p | φ x p = p} = Subgroup.center P) :
    (h ∣ p ^ n + 1) ∨ (h ∣ p ^ n - 1)
 := by
  classical
  have hpprime : p.Prime := Fact.out
  have hcardP_ne_zero : Nat.card P ≠ 0 := by
    rw [hp]
    exact pow_ne_zero _ hpprime.ne_zero
  have : Finite P := Nat.finite_of_card_ne_zero hcardP_ne_zero
  have hh_ne_zero : h ≠ 0 := by
    intro hh0
    rw [hh0, Nat.coprime_zero_left] at hh
    exact hpprime.ne_one hh
  have hcardH_ne_zero : Nat.card H ≠ 0 := by
    rw [hH]
    exact hh_ne_zero
  have : Finite H := Nat.finite_of_card_ne_zero hcardH_ne_zero
  by_cases hh1 : h = 1
  · left
    simp [hh1]
  · let F := AlgebraicClosure ℚ
    let : Fact (IsPGroup p P) := ⟨IsExtraspecial.isPGroup p P⟩
    let : Group.IsNilpotent P := (Fact.out : IsPGroup p P).isNilpotent
    let : Group.IsSolvable P := IsNilpotent.to_isSolvable
    have hcharP : ¬ ringChar F ∣ Nat.card P := by
      simp [F, hcardP_ne_zero]
    have hcharH : ¬ ringChar F ∣ h := by
      simp [F, hh_ne_zero]
    obtain ⟨V, _, _, _, ρ, hρirr, hρfaithful⟩ :=
      theorem_2_5_exists_faithful_irreducible (p := p) (P := P) (F := F) hcharP
    let : IsIrreducible ρ := hρirr
    obtain ⟨σ, hσ⟩ :=
      theorem_2_5_exists_extension
        (P := P) (hH := hH) (hh := hh) (φ := φ) hcentralizer (F := F) ρ hρfaithful hcharP
    obtain ⟨x, hxgen⟩ := theorem_2_5_exists_generator (H := H)
    have hh_pos : 0 < h := Nat.pos_of_ne_zero hh_ne_zero
    have hh2 : h ≥ 2 := by
      omega
    obtain ⟨ε, hε⟩ := exists_primitiveRoot_of_isAlgClosed_not_dvd (F := F) hcharH
    obtain ⟨g, hg, hgpow⟩ :=
      theorem_2_5_generator_linearEquiv (hH := hH) (σ := σ) (x := x) hxgen
    have hdim : Module.finrank F V = p ^ n :=
      finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
        (q := p) (K := P) (ρ := ρ) hρfaithful hp hcharP
    have hE :
        ∀ m : ℤ, ¬ m % h = 0 →
          Module.finrank F
              (intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap)) =
            Module.finrank F
              (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) + 1 := by
      intro m hm
      have hg' : σ (SemidirectProduct.inr x) = g.toLinearMap := by
        simpa using hg.symm
      have hEσ :=
        theorem_2_5_hE
          (hp := hp) (hH := hH) (hh := hh) (φ := φ) hcentralizer
          (ρ := ρ) hρfaithful (σ := σ) hσ (x := x) hxgen (ε := ε) hε m hm
      rw [hg'] at hEσ
      simpa using hEσ
    rcases proposition_2_4_j (F := F) (V := V) (hdim := hdim) (g := g) (h := h)
        (hg := hgpow) (hh := hh2) (ε := ε) (hε := hε) hE with
      ⟨i, m, δ, hδ, hq, hbig, hrest⟩
    have hq' : (p : Int) ^ n = (h : Int) * m + δ := by
      simpa using hq
    rcases hδ with hδ | hδ
    · right
      apply Int.natCast_dvd_natCast.mp
      refine ⟨m, ?_⟩
      have hpow_ge_one : 1 ≤ p ^ n := Nat.succ_le_of_lt (pow_pos hpprime.pos _)
      rw [Int.ofNat_sub hpow_ge_one]
      change (p : Int) ^ n - 1 = (h : Int) * m
      calc
        (p : Int) ^ n - 1 = ((h : Int) * m + δ) - 1 := by rw [hq']
        _ = (h : Int) * m := by rw [hδ]; ring
    · left
      apply Int.natCast_dvd_natCast.mp
      refine ⟨m, ?_⟩
      change (p : Int) ^ n + 1 = (h : Int) * m
      calc
        (p : Int) ^ n + 1 = ((h : Int) * m + δ) + 1 := by rw [hq']
        _ = (h : Int) * m := by rw [hδ]; ring

set_option maxHeartbeats 1000000 in
theorem CFSG.theorem_2_5_b_core
    {p : ℕ} [Fact p.Prime] {n : ℕ}
    {P : Type*} [Group P] [IsExtraspecial p P]
    (hp : Nat.card P = p ^ (2 * n + 1))
    {h : ℕ} {H : Type*} [Group H] [IsCyclic H]
    (hH : Nat.card H = h) (hh : Nat.Coprime h p)
    {φ : H →* MulAut P}
    (hcentralizer : ∀ x : H, x ≠ 1 → {p | φ x p = p} = Subgroup.center P)
    {F : Type*} [Field F] (hc : ¬ ringChar F ∣ h * p ^ (2 * n + 1))
    (hhne : h ≠ p ^ n + 1)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {ρ : Representation F (SemidirectProduct P H φ) V} [IsIrreducible ρ]
    (hfaithful : Function.Injective ρ)
    (hcharP : ¬ ringChar F ∣ Nat.card P) :
    {v | ∀ h : H, ρ ⟨1, h⟩ v = v} ≠ {0} := by
  classical
  have hpprime : p.Prime := Fact.out
  have hcardP_ne_zero : Nat.card P ≠ 0 := by
    rw [hp]
    exact pow_ne_zero _ hpprime.ne_zero
  have : Finite P := Nat.finite_of_card_ne_zero hcardP_ne_zero
  have hh_ne_zero : h ≠ 0 := by
    intro hh0
    rw [hh0, Nat.coprime_zero_left] at hh
    exact hpprime.ne_one hh
  have hcardH_ne_zero : Nat.card H ≠ 0 := by
    rw [hH]
    exact hh_ne_zero
  have : Finite H := Nat.finite_of_card_ne_zero hcardH_ne_zero
  let G := SemidirectProduct P H φ
  let eG : G ≃ P × H := by
    dsimp [G]
    exact SemidirectProduct.equivProd (φ := φ)
  let : Finite G := Finite.of_equiv (P × H) eG.symm
  let R : Subgroup G := (SemidirectProduct.inr : H →* G).range
  let C : Subgroup G := (Subgroup.center P).map (SemidirectProduct.inl : P →* G)
  let : Finite R := Subtype.finite
  by_contra hfix
  have : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hh_ne_one : h ≠ 1 := by
    intro hh1
    have hsub : Subsingleton H := (Nat.card_eq_one_iff_unique.mp (hH.trans hh1)).1
    have hfix_univ : {v | ∀ h : H, ρ ⟨1, h⟩ v = v} = (Set.univ : Set V) := by
      ext v
      constructor
      · intro _
        trivial
      · intro _ y
        simp [Subsingleton.elim y 1]
    have huniv_ne : (Set.univ : Set V) ≠ ({0} : Set V) := by
      intro huniv
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hv0 : v = 0 := by
        have : v ∈ ({0} : Set V) := by
          rw [← huniv]
          trivial
        simpa using this
      exact hv hv0
    exact huniv_ne (hfix_univ.symm.trans hfix)
  have hcardG : Nat.card G = h * p ^ (2 * n + 1) := by
    calc
      Nat.card G = Nat.card (P × H) := by
        exact Nat.card_congr eG
      _ = Nat.card P * Nat.card H := Nat.card_prod P H
      _ = p ^ (2 * n + 1) * h := by rw [hp, hH]
      _ = h * p ^ (2 * n + 1) := by ring
  have hcharG :
      ringChar F = 0 ∨ Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G) := by
    by_cases hchar0 : ringChar F = 0
    · exact Or.inl hchar0
    · have hprime_char : Nat.Prime (ringChar F) := by
        rcases CharP.char_is_prime_or_zero F (ringChar F) with hprime | hzero
        · exact hprime
        · exact False.elim (hchar0 hzero)
      have hnotdvdG : ¬ ringChar F ∣ Nat.card G := by
        intro hdivG
        exact hc (by simpa [hcardG] using hdivG)
      exact Or.inr ⟨hprime_char, hprime_char.coprime_iff_not_dvd.mpr hnotdvdG⟩
  let F' := AlgebraicClosure F
  let V' := F' ⊗[F] V
  let ρ' := Theory.Representation.extendScalars F' ρ
  have hρ'faithful : Function.Injective ρ' := by
    exact (Theory.Representation.extendScalars_faithful_iff F' ρ).mp hfaithful
  have hfixRset :
      {v : V | ∀ r : R, (ρ.comp R.subtype) r v = v} = ({0} : Set V) := by
    ext v
    constructor
    · intro hv
      rw [← hfix]
      intro y
      exact hv ⟨SemidirectProduct.inr y, ⟨y, rfl⟩⟩
    · intro hv r
      have hv0 : v = 0 := by simpa using hv
      simp [hv0]
  have hfixR' :
      Representation.invariants (ρ'.comp R.subtype) = ⊥ := by
    let ρR : Representation F R V := ρ.comp R.subtype
    have hfixRset' : {w : V' | ∀ r : R, (ρ'.comp R.subtype) r w = w} = ({0} : Set V') := by
      have hfixRset'' :
          {w : V' | ∀ r : R, (Theory.Representation.extendScalars F' ρR) r w = w} = ({0} : Set V') := by
        exact
          fixedVectors_eq_zero_extendScalars (ρ := ρR) (F' := F')
            (by simpa only [ρR] using hfixRset)
      ext w
      constructor
      · intro hw
        have hw' : ∀ r : R, (Theory.Representation.extendScalars F' ρR) r w = w := by
          intro r
          simpa [ρR, ρ'] using hw r
        have hw0 : w ∈ ({0} : Set V') := by
          rw [← hfixRset'']
          exact hw'
        exact hw0
      · intro hw
        have hw0 : w = 0 := by simpa using hw
        intro r
        simp [hw0]
    exact
      (invariants_eq_bot_iff_fixedVectors_eq_zero (ρ := ρ') (H := R)).2
        hfixRset'
  have hcenterP_ne_bot : (Subgroup.center P) ≠ ⊥ := by
    intro hcenter_bot
    have hcenter_card :
        Nat.card (Subgroup.center P) = 1 :=
      (Subgroup.eq_bot_iff_card (H := Subgroup.center P)).1 hcenter_bot
    rw [IsExtraspecial.center_order_p p P] at hcenter_card
    exact hpprime.ne_one hcenter_card
  have hC_not_le_ker : ¬ C ≤ ρ'.ker := by
    intro hle
    have hker : ρ'.ker = ⊥ := (MonoidHom.ker_eq_bot_iff (f := ρ')).2 hρ'faithful
    have hC_le_bot : C ≤ ⊥ := by
      rw [← hker]
      exact hle
    have hC_bot : C = ⊥ := le_antisymm hC_le_bot bot_le
    have hcenter_le_bot : Subgroup.center P ≤ ⊥ := by
      intro z hz
      have hzC : SemidirectProduct.inl z ∈ C := ⟨z, hz, rfl⟩
      have hzCbot := hC_bot ▸ hzC
      change SemidirectProduct.inl z = 1 at hzCbot
      exact SemidirectProduct.inl_injective (by simpa using hzCbot)
    exact hcenterP_ne_bot (le_antisymm hcenter_le_bot bot_le)
  have hcharG' :
      ringChar F' = 0 ∨ Nat.Prime (ringChar F') ∧ Nat.Coprime (ringChar F') (Nat.card G) := by
    rcases hcharG with hchar0 | ⟨hprime, hcop⟩
    · left
      simpa [F', Algebra.ringChar_eq F F'] using hchar0
    · right
      refine ⟨?_, ?_⟩
      · simpa [F', Algebra.ringChar_eq F F'] using hprime
      · simpa [F', Algebra.ringChar_eq F F'] using hcop
  have hsemisimple :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime (ρ := ρ') hcharG'
  obtain ⟨m, hmSimple, hmFix, hmCker⟩ :=
    @exists_simple_submodule_nontrivial_of_not_le_ker_of_fixedSubspace_eq_bot
      (SemidirectProduct P H φ) inferInstance F' inferInstance V'
      inferInstance inferInstance ρ' hsemisimple R C hfixR' hC_not_le_ker
  let M := Subrepresentation.ofSubmodule' m
  let τ := M.toRepresentation
  have hτirr : IsIrreducible τ := irreducible_of_ofSubmodule'_simple (ρ := ρ') hmSimple
  let : IsIrreducible τ := hτirr
  let : FiniteDimensional F' ↥M.toSubmodule :=
    finiteDimensional_of_irreducible_finite_group (ρ := τ) hτirr
  let τP : Representation F' P ↥M.toSubmodule := τ.comp SemidirectProduct.inl
  have hτPirr : IsIrreducible τP := by
    let G := SemidirectProduct P H φ
    let K : Subgroup G := (SemidirectProduct.inl : P →* G).range
    let eK : P ≃* K := theorem_2_5_rangeInlEquiv (P := P) (H := H) (φ := φ)
    have hcharPAlg : ¬ ringChar F' ∣ Nat.card P := by
      simpa [F', Algebra.ringChar_eq F F'] using hcharP
    have hcharP' :
        ringChar F' = 0 ∨ Nat.Prime (ringChar F') ∧ Nat.Coprime (ringChar F') (Nat.card P) := by
      rcases hcharG' with hchar0 | ⟨hprime_char, _⟩
      · exact Or.inl hchar0
      · exact Or.inr ⟨hprime_char, hprime_char.coprime_iff_not_dvd.mpr hcharPAlg⟩
    have hτP_center_not_le_ker_local : ¬ Subgroup.center P ≤ τP.ker := by
      intro hle
      apply hmCker
      intro g hg
      rcases hg with ⟨z, hz, rfl⟩
      exact hle hz
    have hτPsemisimple :=
      Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
        (ρ := τP) hcharP'
    obtain ⟨mP, hmPSimple, hmP_not_le_ker⟩ :=
      @exists_simple_submodule_nontrivial_of_not_le_ker
        P inferInstance F' inferInstance ↥M.toSubmodule
        inferInstance inferInstance τP hτPsemisimple
        (Subgroup.center P) hτP_center_not_le_ker_local
    let NP : Subrepresentation τP := Subrepresentation.ofSubmodule' mP
    have hNPirr : IsIrreducible NP.toRepresentation := by
      simpa [NP] using
        (irreducible_of_ofSubmodule'_simple (ρ := τP) hmPSimple :
          IsIrreducible (Subrepresentation.ofSubmodule' mP).toRepresentation)
    let : IsIrreducible NP.toRepresentation := hNPirr
    let : FiniteDimensional F' ↥NP.toSubmodule :=
      finiteDimensional_of_irreducible_finite_group (ρ := NP.toRepresentation) hNPirr
    have hNPker : NP.toRepresentation.ker = ⊥ :=
      ker_eq_bot_of_center_not_le_ker_of_isExtraspecial
        (q := p) (ρ := NP.toRepresentation) hmP_not_le_ker
    have hNPfaithful : Function.Injective NP.toRepresentation :=
      (MonoidHom.ker_eq_bot_iff (f := NP.toRepresentation)).1 hNPker
    obtain ⟨σN, hσN⟩ :=
      theorem_2_5_exists_extension
        (P := P) (hH := hH) (hh := hh) (φ := φ) hcentralizer
        (F := F') NP.toRepresentation hNPfaithful hcharPAlg
    have : K.Normal := by
      simpa [G, K] using theorem_2_5_rangeInl_normal (P := P) (H := H) (φ := φ)
    have hcycK : IsCyclic (G ⧸ K) := by
      let eQ : G ⧸ K ≃* H := by
        let hK :
            K = (SemidirectProduct.rightHom (N := P) (G := H) (φ := φ)).ker := by
          simpa [G, K] using
            (SemidirectProduct.range_inl_eq_ker_rightHom (N := P) (G := H) (φ := φ))
        exact
          (QuotientGroup.quotientMulEquivOfEq hK).trans
            (theorem_2_5_quotientKerRightHomEquiv (P := P) (H := H) (φ := φ))
      exact isCyclic_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective
    let τK : Representation F' K ↥M.toSubmodule := τ.comp K.subtype
    let NK : Subrepresentation τK := {
      toSubmodule := NP.toSubmodule
      apply_mem_toSubmodule := by
        intro k v hv
        let q : P := eK.symm k
        have hk : k = eK q := by
          dsimp [q]
          exact (eK.apply_symm_apply k).symm
        rw [hk]
        change τ (SemidirectProduct.inl q) v ∈ NP.toSubmodule
        exact NP.apply_mem_toSubmodule q hv
    }
    have hNKirr : Representation.IsIrreducible NK.toRepresentation := by
      refine
        (RepEquiv.irreducible_iff_group_iso
          (ρ := NP.toRepresentation) (σ := NK.toRepresentation) eK ?_).1 hNPirr
      intro q v
      rfl
    let σNK : Representation F' K ↥NP.toSubmodule := σN.comp K.subtype
    have hσNK : σNK = NK.toRepresentation := by
      apply MonoidHom.ext
      intro k
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      let q : P := eK.symm k
      have hk : k = eK q := by
        dsimp [q]
        exact (eK.apply_symm_apply k).symm
      rw [hk]
      have hq := congrArg (fun r : Representation F' P ↥NP.toSubmodule => r q v) hσN
      have hq' := congrArg (fun w : NP.toSubmodule => (w : M.toSubmodule)) hq
      have heK : K.subtype (eK q) = SemidirectProduct.inl q := rfl
      change (σN (K.subtype (eK q)) v : M.toSubmodule) = τ (K.subtype (eK q)) v
      rw [heK]
      change (σN (SemidirectProduct.inl q) v : M.toSubmodule) =
        τ (SemidirectProduct.inl q) v at hq'
      exact hq'
    have hσNKirr : Representation.IsIrreducible σNK := by
      simpa [hσNK] using hNKirr
    have ENK : ∀ g : G, σNK ≃ₗ conjugateRep σNK g := by
      intro g
      exact (cyclicQuotientRestrictionConjEquiv K σN g).symm
    have hτKirr : IsIrreducible τK := by
      have fNK : σNK ≃ₗ NK.toRepresentation := by
        simpa [hσNK] using (RepEquiv.refl σNK)
      have eτK : τK ≃ₗ σNK :=
        proposition_2_2_a K hcycK σNK ENK τ NK fNK
      exact (RepEquiv.irreducible_euqiv (f := eτK)).2 hσNKirr
    exact
      (RepEquiv.irreducible_iff_group_iso (ρ := τP) (σ := τK) eK (by
        intro q v
        rfl)).2 hτKirr
  let : IsIrreducible τP := hτPirr
  have hτP_center_not_le_ker : ¬ Subgroup.center P ≤ τP.ker := by
    intro hle
    apply hmCker
    intro g hg
    rcases hg with ⟨z, hz, rfl⟩
    exact hle hz
  have hτPker : τP.ker = ⊥ :=
    ker_eq_bot_of_center_not_le_ker_of_isExtraspecial
      (q := p) (ρ := τP) hτP_center_not_le_ker
  have hτPfaithful : Function.Injective τP :=
    (MonoidHom.ker_eq_bot_iff (f := τP)).1 hτPker
  obtain ⟨x, hxgen⟩ := theorem_2_5_exists_generator (H := H)
  have hh_pos : 0 < h := Nat.pos_of_ne_zero hh_ne_zero
  have hh2 : h ≥ 2 := by
    omega
  have hcharH : ¬ ringChar F ∣ h := by
    intro hdiv
    exact hc (dvd_mul_of_dvd_left hdiv _)
  have hcharH' : ¬ ringChar F' ∣ h := by
    simpa [F', Algebra.ringChar_eq F F'] using hcharH
  have hcharP' : ¬ ringChar F' ∣ Nat.card P := by
    simpa [F', Algebra.ringChar_eq F F'] using hcharP
  obtain ⟨ε, hε⟩ := exists_primitiveRoot_of_isAlgClosed_not_dvd (F := F') hcharH'
  obtain ⟨g, hg, hgpow⟩ :=
    theorem_2_5_generator_linearEquiv (hH := hH) (σ := τ) (x := x) hxgen
  have hdim : Module.finrank F' ↥M.toSubmodule = p ^ n :=
    finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
      (q := p) (K := P) (ρ := τP) hτPfaithful hp hcharP'
  have hcardQ : Nat.card (P ⧸ Subgroup.center P) = p ^ (2 * n) := by
    have hmul : Nat.card P =
        Nat.card (P ⧸ Subgroup.center P) * Nat.card (Subgroup.center P) := by
      simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P))
    have hcenter : Nat.card (Subgroup.center P) = p := IsExtraspecial.center_order_p p P
    have hmul' : p ^ (2 * n + 1) = Nat.card (P ⧸ Subgroup.center P) * p := by
      simpa [hp, hcenter] using hmul
    have hpow : p ^ (2 * n) * p = Nat.card (P ⧸ Subgroup.center P) * p := by
      calc
        p ^ (2 * n) * p = p ^ (2 * n + 1) := by
          rw [show 2 * n + 1 = (2 * n) + 1 by omega, pow_succ]
        _ = Nat.card (P ⧸ Subgroup.center P) * p := hmul'
    exact Nat.eq_of_mul_eq_mul_right hpprime.pos hpow.symm
  have hn_pos : 0 < n := by
    by_contra hn_pos
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn_pos
    subst hn0
    let : Nontrivial (P ⧸ Subgroup.center P) := IsExtraspecial.quotient_nontrivial p P
    have hcardQ_ne_one : Nat.card (P ⧸ Subgroup.center P) ≠ 1 := by
      intro hcard1
      have hsub : Subsingleton (P ⧸ Subgroup.center P) := (Nat.card_eq_one_iff_unique.mp hcard1).1
      exact (not_nontrivial_iff_subsingleton.mpr hsub) (by infer_instance)
    exact hcardQ_ne_one (by simpa using hcardQ)
  have hq_ge_two : p ^ n ≥ 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
    calc
      2 ≤ p := hpprime.two_le
      _ ≤ p * p ^ k := by
        exact Nat.le_mul_of_pos_right p (pow_pos hpprime.pos _)
      _ = p ^ (k + 1) := by rw [Nat.mul_comm, pow_succ]
  have hE :
      ∀ m : ℤ, ¬ m % h = 0 →
        Module.finrank F'
            (intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap)) =
          Module.finrank F'
            (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) + 1 := by
    intro m hm
    have hg' : τ (SemidirectProduct.inr x) = g.toLinearMap := by
      simpa using hg.symm
    have hEτ :=
      theorem_2_5_hE
        (hp := hp) (hH := hH) (hh := hh) (φ := φ) hcentralizer
        (ρ := τP) hτPfaithful (σ := τ) rfl (x := x) hxgen (ε := ε) hε m hm
    have hIntertwine (k : ℤ) :
        intertwiningSubmodule (τ (SemidirectProduct.inr x)) (ε ^ k • τ (SemidirectProduct.inr x)) =
          intertwiningSubmodule g.toLinearMap (ε ^ k • g.toLinearMap) := by
      rw [hg']
    have hfin (k : ℤ) :
        Module.finrank F'
            ↥(intertwiningSubmodule (τ (SemidirectProduct.inr x)) (ε ^ k • τ (SemidirectProduct.inr x))) =
          Module.finrank F'
            ↥(intertwiningSubmodule g.toLinearMap (ε ^ k • g.toLinearMap)) := by
      simpa only [hIntertwine k] using
        congrArg
          (fun N : Submodule F' (End F' ↥M.toSubmodule) => Module.finrank F' ↥N)
          (hIntertwine k)
    calc
      Module.finrank F' ↥(intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap))
        = Module.finrank F'
            ↥(intertwiningSubmodule (τ (SemidirectProduct.inr x))
              (ε ^ (0 : ℤ) • τ (SemidirectProduct.inr x))) := by
              symm
              exact hfin 0
      _ = Module.finrank F'
            ↥(intertwiningSubmodule (τ (SemidirectProduct.inr x))
              (ε ^ m • τ (SemidirectProduct.inr x))) + 1 := hEτ
      _ = Module.finrank F' ↥(intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) + 1 := by
            rw [hfin m]
  rcases proposition_2_4_k
      (F := F') (V := ↥M.toSubmodule) (q := p ^ n) (hdim := hdim) (hq := hq_ge_two)
      (g := g) (h := h) (hg := hgpow) (hh := hh2) (ε := ε) (hε := hε) hE with
    ⟨i, n0, δ, hδ, hq, hbig, hrest, hlast⟩
  rcases hlast with ⟨hn0, hi0, hδneg, hhexc⟩ | hpos
  · exact hhne hhexc
  · let E0 : Submodule F' ↥M.toSubmodule :=
        Module.End.eigenspace g.toLinearMap (ε ^ (0 : ℤ))
    have hE0pos : 0 < Module.finrank F' E0 := by
      simpa [E0] using hpos
    have : Nontrivial E0 := (Module.finrank_pos_iff (R := F') (M := E0)).mp hE0pos
    obtain ⟨v, hv_ne⟩ := exists_ne (0 : E0)
    let gR : R := ⟨SemidirectProduct.inr x, ⟨x, rfl⟩⟩
    have hgR : ∀ r : R, r ∈ Subgroup.zpowers gR := by
      intro r
      rcases r.2 with ⟨y, hy⟩
      rcases hxgen y with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      apply Subtype.ext
      simpa [gR, hy, hm] using
        (MonoidHom.map_zpow (SemidirectProduct.inr : H →* G) x m).symm
    have hvx : τ (SemidirectProduct.inr x) v.1 = v.1 := by
      have hv :=
        (Module.End.mem_eigenspace_iff (f := g.toLinearMap) (μ := ε ^ (0 : ℤ)) (x := v.1)).1 v.2
      rw [show ε ^ (0 : ℤ) = (1 : F') by simp, one_smul] at hv
      simpa [hg] using hv
    have hvInv : v.1 ∈ Representation.invariants (τ.comp R.subtype) := by
      rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
        (ρ := τ.comp R.subtype) (g := gR) hgR v.1]
      simpa [gR] using hvx
    have hv0 : v.1 ∈ (⊥ : Submodule F' ↥M.toSubmodule) := by
      rw [← hmFix]
      exact hvInv
    exact hv_ne (by simpa using hv0)

public theorem CFSG.theorem_2_5_b {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
    {P : Type*} [Group P] [IsExtraspecial p P] (hp : Nat.card P = p ^ (2 * n + 1))
    {h : ℕ} {H : Type*} [Group H] [IsCyclic H] (hH : Nat.card H = h) (hh : Nat.Coprime h p)
    {φ : H →* MulAut P}
    (hcentralizer : ∀ x : H, x ≠ 1 → {p | φ x p = p} = Subgroup.center P)
    {F : Type*} [Field F] (hc : ¬ (ringChar F) ∣ h * p ^ (2 * n + 1))
    (hhne : h ≠ p ^ n + 1)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {ρ : Representation F (SemidirectProduct P H φ) V} [IsIrreducible ρ] (hfaithful : Function.Injective ρ) : {v | ∀ h : H, ρ ⟨1, h⟩ v = v} ≠ {0}
 := by
  classical
  let ρP : Representation F P V := ρ.comp SemidirectProduct.inl
  have hρPfaithful : Function.Injective ρP := by
    intro x y hxy
    suffices (⟨x, 1⟩ : (SemidirectProduct P H φ)) = ⟨y, 1⟩ by
      subst hH
      simp_all only [ne_eq, MonoidHom.coe_comp, Function.comp_apply, SemidirectProduct.mk_eq_inl_mul_inr, map_one,
        mul_one, SemidirectProduct.inl_inj, ρP]
    exact hfaithful hxy
  have hcenter_fixed : ∀ x : H, ∀ z : Subgroup.center P, φ x z = z :=
    semidirectProduct_center_fixed (p := p) (P := P) (H := H) (φ := φ) hcentralizer
  have hcharP : ¬ ringChar F ∣ Nat.card P := by
    intro hdivP
    apply hc
    simpa [hp, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      dvd_mul_of_dvd_right hdivP h
  exact
    theorem_2_5_b_core
      (hp := hp) (hH := hH) (hh := hh) (φ := φ) hcentralizer
      (hc := hc) (hhne := hhne) (ρ := ρ) hfaithful hcharP
