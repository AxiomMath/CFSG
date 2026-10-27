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
open scoped IsMulCommutative
/-
**Kind**: Theorem
**Note**: Lemma 2.3
**Stmt**:
Let $G$ be a finite solvable group.
Let $F$ be a field.
Let $M$ be an finite dimensional absolutely irreducible $FG$-module.
Then $\dim M$ divides $|G|$.
-/

section

open scoped Classical
open _root_.Representation

lemma CFSG.quotient_simple_of_coatom
    {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hN : IsCoatom N) :
    IsSimpleGroup (G ⧸ N) := by
  let e : Subgroup (G ⧸ N) ≃o Set.Ici N := QuotientGroup.comapMk'OrderIso N
  have hsimple : IsSimpleOrder (Set.Ici N) :=
    (Set.isSimpleOrder_Ici_iff_isCoatom (a := N)).2 hN
  let : IsSimpleOrder (Set.Ici N) := hsimple
  let : IsSimpleOrder (Subgroup (G ⧸ N)) := e.isSimpleOrder
  refine {
    toNontrivial := ?_
    eq_bot_or_eq_top_of_normal := ?_
  }
  · rw [QuotientGroup.nontrivial_iff]
    exact hN.1
  · intro H _
    simpa using (show H = ⊥ ∨ H = ⊤ from eq_bot_or_eq_top H)

public lemma CFSG.exist_index_p_of_solvable
    (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ H : Subgroup G, H.Normal ∧ H.index.Prime := by
  let N : Subgroup G := commutator G
  have hNlt : N < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := G)
  let A := G ⧸ N
  have hA_nontrivial : Nontrivial A := by
    rw [QuotientGroup.nontrivial_iff]
    exact ne_of_lt hNlt
  let : Nontrivial A := hA_nontrivial
  have hcommA : IsMulCommutative A :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).2 le_rfl
  let : IsMulCommutative A := hcommA
  let : CommGroup A := IsMulCommutative.instCommGroup
  obtain hbot | ⟨M, hM, _⟩ := eq_top_or_exists_le_coatom (⊥ : Subgroup A)
  · exact (bot_ne_top hbot).elim
  refine ⟨Subgroup.comap (QuotientGroup.mk' N) M, ?_, ?_⟩
  · infer_instance
  · have hsimp : IsSimpleGroup (A ⧸ M) := quotient_simple_of_coatom M hM
    have hprime : Nat.Prime (Nat.card (A ⧸ M)) :=
      (CommGroup.is_simple_iff_prime_card (α := A ⧸ M)).1 hsimp
    rw [Subgroup.index_comap_of_surjective M (QuotientGroup.mk'_surjective N)]
    rw [Subgroup.index_eq_card]
    exact hprime

section

variable {F : Type*} [Field F]
variable {G : Type*} [Group G]
variable {H : Subgroup G} [H.Normal]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable (ρ : Representation F H V)

noncomputable def CFSG.conj_equiv_one : ρ ≃ₗ conjugateRep ρ (1 : G) := by
  refine RepEquiv.mk (LinearEquiv.refl _ _) ?_
  intro k
  ext v
  simp [conjugateRep_apply]

public noncomputable def CFSG.conj_equiv_of_mem (h : H) : ρ ≃ₗ conjugateRep ρ h := by
  refine RepEquiv.mk (LinearEquiv.ofBijective (ρ h) (Representation.apply_bijective ρ h)) ?_
  intro k
  ext v
  change (((ρ h) * (ρ k)) v) = (((ρ ⟨(h : G) * k * (h : G)⁻¹,
    Subgroup.Normal.conj_mem (inferInstance : H.Normal) k k.prop (h : G)⟩) * (ρ h)) v)
  rw [← ρ.map_mul, ← ρ.map_mul]
  have hk :
      h * k =
        ⟨(h : G) * k * (h : G)⁻¹,
          Subgroup.Normal.conj_mem (inferInstance : H.Normal) k k.prop (h : G)⟩ * h := by
    apply Subtype.ext
    simp [mul_assoc]
  simp [hk]

noncomputable def CFSG.conj_equiv_mul_left {a g : G}
    (e : ρ ≃ₗ conjugateRep ρ a) :
    conjugateRep ρ g ≃ₗ conjugateRep ρ (a * g) := by
  refine RepEquiv.mk e.toLinearEquiv ?_
  intro k
  ext v
  change e (ρ ⟨(g : G) * k * (g : G)⁻¹,
    Subgroup.Normal.conj_mem (inferInstance : H.Normal) k k.prop (g : G)⟩ v) =
      ρ ⟨(a * g : G) * k * (a * g : G)⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) k k.prop (a * g : G)⟩ (e v)
  simpa [conjugateRep_apply, mul_assoc]
    using RepEquiv.isIntertwining
      (ρ := ρ) (σ := conjugateRep ρ a) e
      ⟨(g : G) * k * (g : G)⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) k k.prop (g : G)⟩ v

noncomputable def CFSG.conj_equiv_pow {a : G}
    (e : ρ ≃ₗ conjugateRep ρ a) : ∀ n : ℕ, ρ ≃ₗ conjugateRep ρ (a ^ n)
  | 0 => by simpa using (conj_equiv_one (ρ := ρ))
  | n + 1 =>
      by
        simpa [pow_succ', mul_assoc] using
          (conj_equiv_pow e n).trans
            (conj_equiv_mul_left (ρ := ρ) (a := a) (g := a ^ n) e)

public noncomputable def CFSG.all_conjugates_of_prime_quotient
    [Finite G] {p : ℕ} (hcard : Nat.card (G ⧸ H) = p) (hp : p.Prime)
    {a : G} (ha : (a : G ⧸ H) ≠ 1) (e : ρ ≃ₗ conjugateRep ρ a) :
    ∀ x : G, ρ ≃ₗ conjugateRep ρ x := by
  intro x
  have : Fact p.Prime := ⟨hp⟩
  have hxpow : (x : G ⧸ H) ∈ Submonoid.powers (a : G ⧸ H) :=
    mem_powers_of_prime_card hcard ha
  rw [Submonoid.mem_powers_iff] at hxpow
  let n : ℕ := Classical.choose hxpow
  have hn : (a : G ⧸ H) ^ n = (x : G ⧸ H) := Classical.choose_spec hxpow
  have hq : (x : G ⧸ H) = ((a : G ⧸ H) ^ n) := hn.symm
  have hmem : x / a ^ n ∈ H := (QuotientGroup.eq_iff_div_mem).mp hq
  let h : H := ⟨x / a ^ n, hmem⟩
  have hx : x = (h : G) * a ^ n := by
    dsimp [h]
    simp [div_eq_mul_inv, mul_assoc]
  let eh : conjugateRep ρ (a ^ n) ≃ₗ conjugateRep ρ ((h : G) * a ^ n) := by
    simpa using
      (conj_equiv_mul_left (ρ := ρ) (a := (h : G)) (g := a ^ n)
        (conj_equiv_of_mem (ρ := ρ) h))
  simpa [hx] using (conj_equiv_pow (ρ := ρ) e n).trans eh

noncomputable def CFSG.conj_assoc_equiv (a b : G) :
    conjugateRep (conjugateRep ρ b) a ≃ₗ conjugateRep ρ (b * a) := by
  refine RepEquiv.mk (LinearEquiv.refl _ _) ?_
  intro k
  ext v
  simp [conjugateRep_apply, mul_assoc]

public noncomputable def CFSG.conj_diff_equiv {g x : G}
    (e : conjugateRep ρ g ≃ₗ conjugateRep ρ x) :
    ρ ≃ₗ conjugateRep ρ (x * g⁻¹) := by
  let τ : Representation F H V := conjugateRep ρ g
  have e' : τ ≃ₗ conjugateRep τ (g⁻¹ * x) := by
    refine e.trans ?_
    simpa [mul_assoc] using
      (conj_assoc_equiv (ρ := ρ) (a := g⁻¹ * x) (b := g)).symm
  let h :=
    conj_equiv_mul_left (ρ := τ) (a := g⁻¹ * x) (g := g⁻¹) e'
  let e1' : conjugateRep ρ (1 : G) ≃ₗ conjugateRep τ g⁻¹ := by
    simpa [mul_assoc] using
      (conj_assoc_equiv (ρ := ρ) (a := g⁻¹) (b := g)).symm
  let e1 : ρ ≃ₗ conjugateRep τ g⁻¹ :=
    (conj_equiv_one (ρ := ρ)).trans e1'
  let e2 : conjugateRep τ ((g⁻¹ * x) * g⁻¹) ≃ₗ conjugateRep ρ (x * g⁻¹) := by
    simpa [τ, mul_assoc] using
      (conj_assoc_equiv (ρ := ρ) (a := (g⁻¹ * x) * g⁻¹) (b := g))
  exact e1.trans (h.trans e2)

noncomputable def CFSG.conjugateAut (g : G) : H ≃* H where
  toFun h := ⟨g⁻¹ * h * g, by
    simpa using Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⁻¹⟩
  invFun h := ⟨g * h * g⁻¹, Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⟩
  left_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

public theorem CFSG.conjugateRep_irreducible (g : G) [IsIrreducible ρ] :
    IsIrreducible (conjugateRep ρ g) := by
  exact
    RepEquiv.irreducible_of_group_iso
      (ρ := ρ) (σ := conjugateRep ρ g) (conjugateAut (G := G) (H := H) g)
      (by
        intro h v
        simp [conjugateAut, conjugateRep_apply, mul_assoc])
      inferInstance

@[expose] public def CFSG.subrepInclusion {ρ' : Representation F H V} (S : Subrepresentation ρ') :
    S.toRepresentation →ₗ ρ' := by
  refine RepMap.mk S.toSubmodule.subtype ?_
  intro h
  ext v
  rfl

omit [H.Normal] in
public theorem CFSG.repMap_range_ne_bot_of_ne_zero
    {V₁ : Type*} [AddCommGroup V₁] [Module F V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module F V₂]
    {ρ₁ : Representation F H V₁} {ρ₂ : Representation F H V₂}
    (f : ρ₁ →ₗ ρ₂) (hf : f ≠ 0) :
    f.range ≠ ⊥ := by
  intro hbot
  apply hf
  apply Theory.Representation.RepMap.toLinearMap_injective
  apply LinearMap.range_eq_bot.mp
  calc
    f.toLinearMap.range = f.range.toSubmodule := rfl
    _ = (⊥ : Subrepresentation ρ₂).toSubmodule :=
      congrArg Subrepresentation.toSubmodule hbot
    _ = (⊥ : Submodule F V₂) := rfl


set_option backward.isDefEq.respectTransparency false in
public noncomputable def CFSG.repEquivOfNeZeroOfSimple
    {V₁ : Type*} [AddCommGroup V₁] [Module F V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module F V₂]
    {ρ₁ : Representation F H V₁} {ρ₂ : Representation F H V₂}
    [IsIrreducible ρ₁]
    (hρ₂ : IsSimpleOrder (Subrepresentation ρ₂))
    (f : ρ₁ →ₗ ρ₂) (hf : f ≠ 0) :
    ρ₁ ≃ₗ ρ₂ := by
  have hfinj : Function.Injective f := by
    rcases (Representation.IsIrreducible.injective_or_eq_zero
      (ρ := ρ₁) (σ := ρ₂) f) with hfinj | hf0
    · exact hfinj
    · exact False.elim (hf hf0)
  have hrange_ne : f.range ≠ ⊥ := repMap_range_ne_bot_of_ne_zero f hf
  have hrange_top : f.range = ⊤ := by
    rcases hρ₂.eq_bot_or_eq_top f.range with hbot | htop
    · exact False.elim (hrange_ne hbot)
    · exact htop
  have hfsurj : Function.Surjective f := by
    exact LinearMap.range_eq_top.mp (by
      calc
        f.toLinearMap.range = f.range.toSubmodule := rfl
        _ = (⊤ : Subrepresentation ρ₂).toSubmodule :=
          congrArg Subrepresentation.toSubmodule hrange_top
        _ = (⊤ : Submodule F V₂) := rfl)
  refine RepEquiv.mk (LinearEquiv.ofBijective f.toLinearMap ⟨hfinj, hfsurj⟩) ?_
  intro h
  ext v
  simpa using (Representation.IntertwiningMap.isIntertwining (ρ := ρ₁) (σ := ρ₂) f h v)

noncomputable def CFSG.subrepresentationOrderIsoOfEquiv
    {V₁ : Type*} [AddCommGroup V₁] [Module F V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module F V₂]
    {ρ₁ : Representation F H V₁} {ρ₂ : Representation F H V₂}
    (e : ρ₁ ≃ₗ ρ₂) :
    Subrepresentation ρ₁ ≃o Subrepresentation ρ₂ where
  toFun S := {
    toSubmodule := S.toSubmodule.map e.toLinearMap
    apply_mem_toSubmodule := by
      intro h w hw
      rcases hw with ⟨v, hv, rfl⟩
      refine ⟨ρ₁ h v, S.apply_mem_toSubmodule h hv, ?_⟩
      change e (ρ₁ h v) = ρ₂ h (e v)
      exact RepEquiv.isIntertwining (ρ := ρ₁) (σ := ρ₂) e h v
  }
  invFun T := {
    toSubmodule := T.toSubmodule.map e.symm.toLinearMap
    apply_mem_toSubmodule := by
      intro h w hw
      rcases hw with ⟨v, hv, rfl⟩
      refine ⟨ρ₂ h v, T.apply_mem_toSubmodule h hv, ?_⟩
      change e.symm (ρ₂ h v) = ρ₁ h (e.symm v)
      exact RepEquiv.isIntertwining (ρ := ρ₂) (σ := ρ₁) e.symm h v
  }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    constructor
    · intro hv
      rcases hv with ⟨w, hw, hwv⟩
      rcases hw with ⟨u, hu, hwu⟩
      have huv : u = v := by
        rw [← hwv, ← hwu]
        exact (e.symm_apply_apply u).symm
      simpa [huv] using hu
    · intro hv
      refine ⟨e v, ?_, e.left_inv v⟩
      exact ⟨v, hv, rfl⟩
  right_inv T := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    constructor
    · intro hv
      rcases hv with ⟨w, hw, hwv⟩
      rcases hw with ⟨u, hu, hwu⟩
      have huv : u = v := by
        rw [← hwv, ← hwu]
        exact (e.apply_symm_apply u).symm
      simpa [huv] using hu
    · intro hv
      refine ⟨e.symm v, ?_, e.right_inv v⟩
      exact ⟨v, hv, rfl⟩
  map_rel_iff' := by
    intro S T
    constructor
    · intro h v hv
      have hev : e v ∈ S.toSubmodule.map e.toLinearMap :=
        ⟨v, hv, rfl⟩
      rcases h hev with ⟨w, hw, hwv⟩
      have hwv' : w = v := by
        exact e.injective hwv
      change v ∈ T.toSubmodule
      simpa [hwv'] using hw
    · intro h v hv
      rcases hv with ⟨w, hw, rfl⟩
      exact ⟨w, h hw, rfl⟩

omit [H.Normal] in
public theorem CFSG.subrep_le_of_nonzero_mem
    {V' : Type*} [AddCommGroup V'] [Module F V']
    {ρ' : Representation F H V'}
    (S T : Subrepresentation ρ') [IsIrreducible S.toRepresentation]
    {v : V'} (hvS : v ∈ S.toSubmodule) (hvT : v ∈ T.toSubmodule) (hv : v ≠ 0) :
    S ≤ T := by
  let U : Subrepresentation S.toRepresentation := {
    toSubmodule := T.toSubmodule.comap S.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro h w hw
      exact T.apply_mem_toSubmodule h hw }
  have hU_ne : U ≠ ⊥ := by
    intro hU
    have hvU : (⟨v, hvS⟩ : S.toSubmodule) ∈ U.toSubmodule := hvT
    have hv0 : v = 0 := by
      have hv0sub : (⟨v, hvS⟩ : S.toSubmodule) = 0 := by
        rw [hU] at hvU
        change (⟨v, hvS⟩ : S.toSubmodule) = 0 at hvU
        exact hvU
      exact Subtype.ext_iff.mp hv0sub
    exact hv hv0
  have hU_top : U = ⊤ := by
    rcases (inferInstance : IsIrreducible S.toRepresentation).eq_bot_or_eq_top U with hbot | htop
    · exact False.elim (hU_ne hbot)
    · exact htop
  intro w hw
  have hwU : (⟨w, hw⟩ : S.toSubmodule) ∈ U.toSubmodule := by
    rw [hU_top]
    trivial
  exact hwU

public abbrev CFSG.coindRep : Representation F G (Representation.coindV H.subtype ρ) :=
  Representation.coind H.subtype ρ

public def CFSG.coindCosetSubrep (q : G ⧸ H) :
    Subrepresentation ((coindRep (ρ := ρ)).comp H.subtype) where
  toSubmodule := {
    carrier := {f | ∀ g : G, ((g : G ⧸ H) ≠ q) → f.1 g = 0}
    zero_mem' := by simp
    add_mem' := by
      intro f g hf hg x hx
      simp [hf x hx, hg x hx]
    smul_mem' := by
      intro a f hf x hx
      simp [hf x hx]
  }
  apply_mem_toSubmodule := by
    intro h f hf g hg
    change f.1 (g * h) = 0
    apply hf
    intro hq
    have hh : ((h : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff (h : G)).2 h.prop
    apply hg
    change ((g : G ⧸ H) * (((h : G)) : G ⧸ H) = q) at hq
    rw [hh, mul_one] at hq
    exact hq

@[expose] public def CFSG.coindEval (g : G) :
    (coindRep (ρ := ρ)).comp H.subtype →ₗ conjugateRep ρ g := by
  refine RepMap.mk ?_ ?_
  · refine
      { toFun := fun f => f.1 g
        map_add' := by intro f₁ f₂; rfl
        map_smul' := by intro a f; rfl }
  · intro h
    ext f
    change f.1 (g * h.val) =
      ρ ⟨(g : G) * h.val * (g : G)⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop (g : G)⟩ (f.1 g)
    simpa [Theory.Representation.conjugateRep_apply, mul_assoc] using
      f.2
        ⟨(g : G) * h.val * (g : G)⁻¹,
          Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop (g : G)⟩
        (g : G)

@[expose] public noncomputable def CFSG.coindBaseFunctionAt (g : G) (v : V) :
    Representation.coindV H.subtype ρ := by
  classical
  refine ⟨fun x => if hx : x * g⁻¹ ∈ H then ρ ⟨x * g⁻¹, hx⟩ v else 0, ?_⟩
  intro h x
  by_cases hx : x * g⁻¹ ∈ H
  · have hhx : ((h : G) * x) * g⁻¹ ∈ H := by
      simpa [mul_assoc] using H.mul_mem h.prop hx
    change (if hhx' : ((h : G) * x) * g⁻¹ ∈ H then ρ ⟨((h : G) * x) * g⁻¹, hhx'⟩ v else 0) =
      ρ h ((if hx' : x * g⁻¹ ∈ H then ρ ⟨x * g⁻¹, hx'⟩ v else 0))
    rw [dif_pos hhx, dif_pos hx]
    have hmul : ⟨((h : G) * x) * g⁻¹, hhx⟩ = h * ⟨x * g⁻¹, hx⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    simp [hmul, ρ.map_mul]
  · have hhx : ((h : G) * x) * g⁻¹ ∉ H := by
      intro hhx
      apply hx
      have : x * g⁻¹ = (h : G)⁻¹ * (((h : G) * x) * g⁻¹) := by
        simp [mul_assoc]
      rw [this]
      exact H.mul_mem (H.inv_mem h.prop) hhx
    simp [hx, hhx]

@[simp] public theorem CFSG.coindEval_base (g : G) (v : V) :
    coindEval (ρ := ρ) g (coindBaseFunctionAt (ρ := ρ) g v) = v := by
  change (if hg : g * g⁻¹ ∈ H then ρ ⟨g * g⁻¹, hg⟩ v else 0) = v
  rw [dif_pos]
  · have hone : ⟨g * g⁻¹, by simp⟩ = (1 : H) := by
      apply Subtype.ext
      simp
    have h1 : (ρ (1 : H) : Module.End F V) = 1 := ρ.map_one
    have hmap : ρ ⟨g * g⁻¹, by simp⟩ = ρ (1 : H) := congrArg ρ hone
    calc
      ρ ⟨g * g⁻¹, by simp⟩ v = ρ (1 : H) v := by
        simpa using congrArg (fun f : Module.End F V => f v) hmap
      _ = v := by simp [h1]
  · simp

public theorem CFSG.coindBaseFunctionAt_mem_coset (g : G) (v : V) :
    coindBaseFunctionAt (ρ := ρ) g v ∈ (coindCosetSubrep (ρ := ρ) (g : G ⧸ H)).toSubmodule := by
  intro x hx
  change (if hx' : x * g⁻¹ ∈ H then ρ ⟨x * g⁻¹, hx'⟩ v else 0) = 0
  rw [dif_neg]
  intro hmem
  apply hx
  exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hmem)

@[simp] public theorem CFSG.coindEval_of_ne_coset
    {g x : G} (hx : (x : G ⧸ H) ≠ (g : G ⧸ H)) (v : V) :
    coindEval (ρ := ρ) x (coindBaseFunctionAt (ρ := ρ) g v) = 0 := by
  change (if hx' : x * g⁻¹ ∈ H then ρ ⟨x * g⁻¹, hx'⟩ v else 0) = 0
  rw [dif_neg]
  intro hmem
  apply hx
  exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hmem)

set_option backward.isDefEq.respectTransparency false in
public noncomputable def CFSG.coindCosetEquiv (g : G) :
    (coindCosetSubrep (ρ := ρ) (g : G ⧸ H)).toRepresentation ≃ₗ conjugateRep ρ g := by
  let S := coindCosetSubrep (ρ := ρ) (g : G ⧸ H)
  let evLin :
      S.toSubmodule →ₗ[F] V :=
    (coindEval (ρ := ρ) g).toLinearMap.comp S.toSubmodule.subtype
  let ev : S.toRepresentation →ₗ conjugateRep ρ g := by
    refine RepMap.mk evLin ?_
    intro h
    ext f
    change
      coindEval (ρ := ρ) g
          (((coindRep (ρ := ρ)).comp H.subtype h) f.1) =
        conjugateRep ρ g h (coindEval (ρ := ρ) g f.1)
    exact
      Representation.IntertwiningMap.isIntertwining
        (ρ := ((coindRep (ρ := ρ)).comp H.subtype))
        (σ := conjugateRep ρ g) (coindEval (ρ := ρ) g) h f.1
  refine RepEquiv.mk (LinearEquiv.ofBijective ev.toLinearMap ⟨?_, ?_⟩) ?_
  · intro f₁ f₂ hfg
    ext x
    by_cases hx : (x : G ⧸ H) = (g : G ⧸ H)
    · have hmem : x * g⁻¹ ∈ H := by
        simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).mp hx
      have hf₁ :
          f₁.1.1 x = ρ ⟨x * g⁻¹, hmem⟩ (f₁.1.1 g) := by
        simpa [coindEval, hmem, div_eq_mul_inv, mul_assoc] using
          f₁.1.2 ⟨x * g⁻¹, hmem⟩ (g : G)
      have hf₂ :
          f₂.1.1 x = ρ ⟨x * g⁻¹, hmem⟩ (f₂.1.1 g) := by
        simpa [coindEval, hmem, div_eq_mul_inv, mul_assoc] using
          f₂.1.2 ⟨x * g⁻¹, hmem⟩ (g : G)
      have hg : f₁.1.1 g = f₂.1.1 g := by
        change coindEval (ρ := ρ) g f₁.1 = coindEval (ρ := ρ) g f₂.1
        exact hfg
      rw [hf₁, hf₂, hg]
    · have hf₁x : f₁.1.1 x = 0 := f₁.2 x hx
      have hf₂x : f₂.1.1 x = 0 := f₂.2 x hx
      rw [hf₁x, hf₂x]
  · intro v
    refine
      ⟨⟨coindBaseFunctionAt (ρ := ρ) g v,
        coindBaseFunctionAt_mem_coset (ρ := ρ) g v⟩, ?_⟩
    change coindEval (ρ := ρ) g (coindBaseFunctionAt (ρ := ρ) g v) = v
    simp
  · intro h
    ext f
    simpa using
      (Representation.IntertwiningMap.isIntertwining
        (ρ := S.toRepresentation) (σ := conjugateRep ρ g) ev h f)

set_option backward.isDefEq.respectTransparency false in
@[expose] public noncomputable def CFSG.coindProj (q : G ⧸ H) :
    ((coindRep (ρ := ρ)).comp H.subtype) →ₗ ((coindRep (ρ := ρ)).comp H.subtype) := by
  classical
  let proj : (G → V) →ₗ[F] (G → V) :=
    { toFun := fun f g => if (g : G ⧸ H) = q then f g else 0
      map_add' := by
        intro f g
        funext x
        by_cases hx : (x : G ⧸ H) = q <;> simp [hx]
      map_smul' := by
        intro a f
        funext x
        by_cases hx : (x : G ⧸ H) = q <;> simp [hx] }
  have hproj :
      ∀ f ∈ Representation.coindV H.subtype ρ, proj f ∈ Representation.coindV H.subtype ρ := by
    intro f hf h x
    by_cases hx : (x : G ⧸ H) = q
    · have hhx : (((h : G) * x : G) : G ⧸ H) = q := by
        have hh : ((h : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff (h : G)).2 h.prop
        change ((h : G ⧸ H) * (x : G ⧸ H)) = q
        rw [hh, one_mul, hx]
      simpa [proj, hx, hhx] using hf h x
    · have hhx : (((h : G) * x : G) : G ⧸ H) ≠ q := by
        intro hhx
        apply hx
        have hh : ((h : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff (h : G)).2 h.prop
        change ((h : G ⧸ H) * (x : G ⧸ H)) = q at hhx
        rwa [hh, one_mul] at hhx
      have hhx' : ((h : G) * x : G) ≠ q := by simpa using hhx
      simp [proj, hx]
      intro hEq
      exact False.elim (hhx' hEq)
  refine RepMap.mk (LinearMap.restrict proj ?_) ?_
  · intro f hf
    exact hproj f hf
  · intro h
    ext f x
    by_cases hx : (x : G ⧸ H) = q
    · have hhx : ((x * (h : G) : G) : G ⧸ H) = q := by
        have hh : ((h : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff (h : G)).2 h.prop
        change ((x : G ⧸ H) * (h : G ⧸ H)) = q
        rw [hh, mul_one, hx]
      simp [LinearMap.restrict_apply, proj, hx, hhx]
    · have hhx : ((x * (h : G) : G) : G ⧸ H) ≠ q := by
        intro hhx
        apply hx
        have hh : ((h : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff (h : G)).2 h.prop
        change ((x : G ⧸ H) * (h : G ⧸ H)) = q at hhx
        rwa [hh, mul_one] at hhx
      simp [LinearMap.restrict_apply, proj, hx]

set_option backward.isDefEq.respectTransparency false in
@[simp] public theorem CFSG.coindProj_apply
    (q : G ⧸ H) (f : Representation.coindV H.subtype ρ) (x : G) :
    (coindProj (ρ := ρ) q f).1 x = if (x : G ⧸ H) = q then f.1 x else 0 := by
  simp [coindProj, LinearMap.restrict_apply]

public theorem CFSG.coindProj_mem_coset
    (q : G ⧸ H) (f : Representation.coindV H.subtype ρ) :
    coindProj (ρ := ρ) q f ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule := by
  intro x hx
  simp [coindProj_apply, hx]

set_option backward.isDefEq.respectTransparency false in
@[expose] public noncomputable def CFSG.coindProjToCoset (q : G ⧸ H) :
    ((coindRep (ρ := ρ)).comp H.subtype) →ₗ (coindCosetSubrep (ρ := ρ) q).toRepresentation := by
  refine RepMap.mk ?_ ?_
  · refine
      { toFun := fun f => ⟨coindProj (ρ := ρ) q f, coindProj_mem_coset (ρ := ρ) q f⟩
        map_add' := by
          intro f g
          ext x
          simp [coindProj_apply]
        map_smul' := by
          intro a f
          ext x
          simp [coindProj_apply] }
  · intro h
    ext f x
    change (coindProj (ρ := ρ) q (((coindRep (ρ := ρ)).comp H.subtype) h f)).1 x =
      (((coindRep (ρ := ρ)).comp H.subtype) h (coindProj (ρ := ρ) q f)).1 x
    have hcomm :=
      Representation.IntertwiningMap.isIntertwining
        (ρ := ((coindRep (ρ := ρ)).comp H.subtype))
        (σ := ((coindRep (ρ := ρ)).comp H.subtype))
        (coindProj (ρ := ρ) q) h f
    simp

@[simp] public theorem CFSG.coindProj_eq_self_of_mem {q : G ⧸ H}
    (f : Representation.coindV H.subtype ρ)
    (hf : f ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule) :
    coindProj (ρ := ρ) q f = f := by
  ext x
  by_cases hx : (x : G ⧸ H) = q
  · simp [coindProj_apply, hx]
  · have hzero : f.1 x = 0 := hf x hx
    simp [coindProj_apply, hx, hzero]


@[simp] theorem CFSG.sum_coindProj_apply [Fintype (G ⧸ H)] (f : Representation.coindV H.subtype ρ) (x : G) :
    (∑ q : G ⧸ H, coindProj (ρ := ρ) q f).1 x = f.1 x := by
  classical
  calc
    (∑ q : G ⧸ H, coindProj (ρ := ρ) q f).1 x
        = ∑ q : G ⧸ H, if (x : G ⧸ H) = q then f.1 x else 0 := by
            simp [coindProj_apply]
    _ = f.1 x := by
      simp

theorem CFSG.mem_iSup_coindCosetSubrep [Fintype (G ⧸ H)] (f : Representation.coindV H.subtype ρ) :
    f ∈ ⨆ q : G ⧸ H, (coindCosetSubrep (ρ := ρ) q).toSubmodule := by
  classical
  rw [← show (∑ q : G ⧸ H, coindProj (ρ := ρ) q f) = f by
    ext x
    simp]
  refine Submodule.sum_mem _ ?_
  intro q _
  exact Submodule.mem_iSup_of_mem q (coindProj_mem_coset (ρ := ρ) q f)

public theorem CFSG.iSup_coindCosetSubrep_eq_top [Fintype (G ⧸ H)] :
    (⨆ q : G ⧸ H, (coindCosetSubrep (ρ := ρ) q).toSubmodule) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr ?_
  intro f
  exact mem_iSup_coindCosetSubrep (ρ := ρ) f

public theorem CFSG.coind_apply_mem_coset_shift
    (x : G) {q : G ⧸ H} (f : Representation.coindV H.subtype ρ)
    (hf : f ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule) :
    coindRep (ρ := ρ) x f ∈ (coindCosetSubrep (ρ := ρ) (q / (x : G ⧸ H))).toSubmodule := by
  intro y hy
  change f.1 (y * x) = 0
  apply hf
  intro hEq
  apply hy
  change ((y : G ⧸ H) * (x : G ⧸ H) = q) at hEq
  simpa [div_eq_mul_inv] using (eq_mul_inv_iff_mul_eq).2 hEq


set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.coindCosetSubrep_irreducible [Finite G] [IsIrreducible ρ] (q : G ⧸ H) :
    IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q).toRepresentation)) := by
  let g : G := Classical.choose (QuotientGroup.mk_surjective q)
  have hg : (g : G ⧸ H) = q := Classical.choose_spec (QuotientGroup.mk_surjective q)
  let e :
      (coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation ≃ₗ conjugateRep ρ g :=
    coindCosetEquiv (ρ := ρ) g
  have hIrr :
      IsSimpleOrder
        (Subrepresentation ((coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation)) := by
    let : IsIrreducible (conjugateRep (ρ := ρ) g) := conjugateRep_irreducible (ρ := ρ) g
    let o :
        Subrepresentation ((coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation) ≃o
          Subrepresentation (conjugateRep (ρ := ρ) g) :=
      subrepresentationOrderIsoOfEquiv
        (V₁ := (coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toSubmodule)
        (V₂ := V)
        (ρ₁ := (coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation)
        (ρ₂ := conjugateRep (ρ := ρ) g)
        e
    exact (OrderIso.isSimpleOrder_iff o).2 inferInstance
  rw [← hg]
  exact hIrr

set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.coindRep_irreducible_of_notall
    [Finite G] [FiniteDimensional F V] [IsIrreducible ρ]
    {p : ℕ} (hcard : Nat.card (G ⧸ H) = p) (hp : p.Prime)
    (hnall : ¬ ∀ x : G, Nonempty (ρ ≃ₗ conjugateRep ρ x)) :
    IsSimpleOrder (Subrepresentation (coindRep (ρ := ρ))) := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let v0 : V := Classical.choose (exists_ne (0 : V))
  have hv0_ne : v0 ≠ 0 := Classical.choose_spec (exists_ne (0 : V))
  let f0 := coindBaseFunctionAt (ρ := ρ) (1 : G) v0
  have hf0_ne : f0 ≠ 0 := by
    intro hf0
    apply hv0_ne
    have h0 := congrArg (coindEval (ρ := ρ) (1 : G)) hf0
    simpa [f0] using h0
  let : Nontrivial (Representation.coindV H.subtype ρ) := ⟨f0, 0, hf0_ne⟩
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top := ?_ }
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    have hSsub_ne : S.toSubmodule ≠ ⊥ := by
      intro hbot
      apply hS
      exact Subrepresentation.toSubmodule_injective hbot
    let SH : Subrepresentation ((coindRep (ρ := ρ)).comp H.subtype) := {
      toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro h f hf
        exact S.apply_mem_toSubmodule h.1 hf
    }
    obtain ⟨fS, hfS, hfS_ne⟩ := SH.toSubmodule.ne_bot_iff.mp hSsub_ne
    let : Nontrivial SH.toSubmodule := ⟨⟨fS, hfS⟩, 0, by simpa using hfS_ne⟩
    let iS : SH.toRepresentation →ₗ ((coindRep (ρ := ρ)).comp H.subtype) := subrepInclusion SH
    obtain ⟨N, hNirr⟩ :=
      @Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
        F ↥H ↥SH.toSubmodule inferInstance inferInstance inferInstance inferInstance inferInstance
        SH.toRepresentation inferInstance
    let : Representation.IsIrreducible N.toRepresentation := hNirr
    let iNS : N.toRepresentation →ₗ SH.toRepresentation := subrepInclusion N
    let iN : N.toRepresentation →ₗ ((coindRep (ρ := ρ)).comp H.subtype) := iS.comp iNS
    have hiN_injective : Function.Injective iN := by
      intro a b hab
      simpa [iN, iS, iNS, subrepInclusion] using hab
    let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
    let n0 : N.toSubmodule := Classical.choose (exists_ne (0 : N.toSubmodule))
    have hn0_ne : n0 ≠ 0 := Classical.choose_spec (exists_ne (0 : N.toSubmodule))
    have hiNn0_ne : iN n0 ≠ 0 := by
      intro h0
      apply hn0_ne
      exact hiN_injective h0
    obtain ⟨g, hg_ne⟩ : ∃ g : G, (iN n0).1 g ≠ 0 := by
      by_contra hnone
      apply hiNn0_ne
      ext x
      by_cases hx : (iN n0).1 x = 0
      · exact hx
      · exact False.elim (hnone ⟨x, hx⟩)
    let q : G ⧸ H := g
    let P (q' : G ⧸ H) :
        N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation :=
      (coindProjToCoset (ρ := ρ) q').comp iN
    have hPq_ne : P q ≠ 0 := by
      intro hP0
      apply hg_ne
      have h0 := congrArg
        (fun f => (((f n0).1 : Representation.coindV H.subtype ρ).1 g)) hP0
      simpa [P, q, coindProjToCoset, coindProj_apply] using h0
    have hP_unique (q' : G ⧸ H) (hq' : q' ≠ q) : P q' = 0 := by
      by_contra hPq'_ne
      let x : G := Classical.choose (QuotientGroup.mk_surjective q')
      have hx : (x : G ⧸ H) = q' := Classical.choose_spec (QuotientGroup.mk_surjective q')
      have :
          IsSimpleOrder
            (Subrepresentation ((coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) (g : G ⧸ H)
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q).toRepresentation)) := by
        simpa [q] using
          (coindCosetSubrep_irreducible (ρ := ρ) (g : G ⧸ H) :
            IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation)))
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q').toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) q'
      let eNq :
          N.toRepresentation ≃ₗ
            (coindCosetSubrep (ρ := ρ) q).toRepresentation :=
        by
          let fq : N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q).toRepresentation := P q
          have hfq_ne : fq ≠ 0 := by simpa [fq] using hPq_ne
          exact
            (show N.toRepresentation ≃ₗ (coindCosetSubrep (ρ := ρ) q).toRepresentation from
              repEquivOfNeZeroOfSimple
                (V₁ := N.toSubmodule)
                (V₂ := (coindCosetSubrep (ρ := ρ) q).toSubmodule)
                (ρ₁ := N.toRepresentation)
                (ρ₂ := (coindCosetSubrep (ρ := ρ) q).toRepresentation)
                (hρ₂ := coindCosetSubrep_irreducible (ρ := ρ) q)
                (f := fq)
                hfq_ne)
      let eNq' :
          N.toRepresentation ≃ₗ
            (coindCosetSubrep (ρ := ρ) q').toRepresentation :=
        by
          let fq' : N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation := P q'
          have hfq'_ne : fq' ≠ 0 := by simpa [fq'] using hPq'_ne
          exact
            (show N.toRepresentation ≃ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation from
              repEquivOfNeZeroOfSimple
                (V₁ := N.toSubmodule)
                (V₂ := (coindCosetSubrep (ρ := ρ) q').toSubmodule)
                (ρ₁ := N.toRepresentation)
                (ρ₂ := (coindCosetSubrep (ρ := ρ) q').toRepresentation)
                (hρ₂ := coindCosetSubrep_irreducible (ρ := ρ) q')
                (f := fq')
                hfq'_ne)
      let eCg : (coindCosetSubrep (ρ := ρ) q).toRepresentation ≃ₗ conjugateRep ρ g := by
        simpa [q] using (coindCosetEquiv (ρ := ρ) g)
      let eCx : (coindCosetSubrep (ρ := ρ) q').toRepresentation ≃ₗ conjugateRep ρ x := by
        rw [← hx]
        exact coindCosetEquiv (ρ := ρ) x
      let eNg : N.toRepresentation ≃ₗ conjugateRep ρ g :=
        eNq.trans eCg
      let eNx : N.toRepresentation ≃ₗ conjugateRep ρ x :=
        eNq'.trans eCx
      have hneqone : ((x * g⁻¹ : G) : G ⧸ H) ≠ 1 := by
        intro h1
        apply hq'
        calc
          q' = (x : G ⧸ H) := hx.symm
          _ = (g : G ⧸ H) := by
                have hxg' : (x : G ⧸ H) * (g : G ⧸ H)⁻¹ = 1 := by
                  simpa [div_eq_mul_inv] using h1
                calc
                  (x : G ⧸ H) = ((x : G ⧸ H) * (g : G ⧸ H)⁻¹) * (g : G ⧸ H) := by
                    simp [mul_assoc]
                  _ = (g : G ⧸ H) := by simp [hxg']
          _ = q := by rfl
      apply hnall
      intro y
      exact ⟨all_conjugates_of_prime_quotient (ρ := ρ) hcard hp hneqone
        (conj_diff_equiv (ρ := ρ) (e := eNg.symm.trans eNx)) y⟩
    have hmem_q (n : N.toSubmodule) : iN n ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule := by
      have hzero_proj (q' : G ⧸ H) (hq' : q' ≠ q) : coindProj (ρ := ρ) q' (iN n) = 0 := by
        have h0 := congrArg (fun f => ((f n).1 : Representation.coindV H.subtype ρ))
          (hP_unique q' hq')
        simpa [P, coindProjToCoset] using h0
      have h_eq : iN n = coindProj (ρ := ρ) q (iN n) := by
        ext x
        by_cases hx : (x : G ⧸ H) = q
        · simp [coindProj_apply, hx]
        · have hxproj : coindProj (ρ := ρ) (x : G ⧸ H) (iN n) = 0 := hzero_proj (x : G ⧸ H) hx
          have hxzero : (iN n).1 x = 0 := by
            have h0 := congrArg (fun f : Representation.coindV H.subtype ρ => f.1 x) hxproj
            simpa [coindProj_apply] using h0
          simp [coindProj_apply, hx, hxzero]
      rw [h_eq]
      exact coindProj_mem_coset (ρ := ρ) q (iN n)
    have hw0_q : iN n0 ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule := hmem_q n0
    have hw0_SH : iN n0 ∈ SH.toSubmodule := by
      exact (iNS n0).2
    have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q).toRepresentation)) :=
      coindCosetSubrep_irreducible (ρ := ρ) q
    have hCq_le : (coindCosetSubrep (ρ := ρ) q).toSubmodule ≤ SH.toSubmodule := by
      exact subrep_le_of_nonzero_mem
        (ρ' := ((coindRep (ρ := ρ)).comp H.subtype))
        (S := coindCosetSubrep (ρ := ρ) q) (T := SH) hw0_q hw0_SH hiNn0_ne
    have hCr_le (r : G ⧸ H) : (coindCosetSubrep (ρ := ρ) r).toSubmodule ≤ SH.toSubmodule := by
      let y : G := Classical.choose (QuotientGroup.mk_surjective (r⁻¹ * q))
      have hy : (y : G ⧸ H) = r⁻¹ * q := Classical.choose_spec (QuotientGroup.mk_surjective (r⁻¹ * q))
      have hy_mem : coindRep (ρ := ρ) y (iN n0) ∈ (coindCosetSubrep (ρ := ρ) r).toSubmodule := by
        have hy_mem' := coind_apply_mem_coset_shift (ρ := ρ) y (iN n0) hw0_q
        simpa [hy, div_eq_mul_inv, mul_assoc] using hy_mem'
      have hy_SH : coindRep (ρ := ρ) y (iN n0) ∈ SH.toSubmodule := by
        exact S.apply_mem_toSubmodule y hw0_SH
      have hy_ne : coindRep (ρ := ρ) y (iN n0) ≠ 0 := by
        intro h0
        apply hiNn0_ne
        exact (Representation.apply_bijective (coindRep (ρ := ρ)) y).1 h0
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) r).toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) r
      exact subrep_le_of_nonzero_mem
        (ρ' := ((coindRep (ρ := ρ)).comp H.subtype))
        (S := coindCosetSubrep (ρ := ρ) r) (T := SH) hy_mem hy_SH hy_ne
    have hsup_le : (⨆ r : G ⧸ H, (coindCosetSubrep (ρ := ρ) r).toSubmodule) ≤ S.toSubmodule := by
      refine iSup_le ?_
      intro r
      exact hCr_le r
    have htop_le : (⊤ : Submodule F (Representation.coindV H.subtype ρ)) ≤ S.toSubmodule := by
      simpa [iSup_coindCosetSubrep_eq_top (ρ := ρ)] using hsup_le
    apply Subrepresentation.toSubmodule_injective
    exact le_antisymm le_top htop_le

/-- If no element outside a normal subgroup carries an irreducible representation to an
equivalent conjugate, then its coinduction is irreducible. This is the general
finite-index criterion underlying the prime-index specialization above. -/
public theorem CFSG.coindRep_irreducible_of_noNontrivialConj
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) [FiniteDimensional F V] [Representation.IsIrreducible ρ]
    (hnconj :
      ∀ x : G, (x : G ⧸ H) ≠ 1 →
        ¬ Nonempty (ρ ≃ₗ Theory.Representation.conjugateRep ρ x)) :
    IsSimpleOrder (Subrepresentation (coindRep (ρ := ρ))) := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let v0 : V := Classical.choose (exists_ne (0 : V))
  have hv0_ne : v0 ≠ 0 := Classical.choose_spec (exists_ne (0 : V))
  let f0 := coindBaseFunctionAt (ρ := ρ) (1 : G) v0
  have hf0_ne : f0 ≠ 0 := by
    intro hf0
    apply hv0_ne
    have h0 := congrArg (coindEval (ρ := ρ) (1 : G)) hf0
    simpa [f0] using h0
  let : Nontrivial (Representation.coindV H.subtype ρ) := ⟨f0, 0, hf0_ne⟩
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top := ?_ }
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    have hSsub_ne : S.toSubmodule ≠ ⊥ := by
      intro hbot
      apply hS
      exact Subrepresentation.toSubmodule_injective hbot
    let SH : Subrepresentation ((coindRep (ρ := ρ)).comp H.subtype) := {
      toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro h f hf
        exact S.apply_mem_toSubmodule h.1 hf
    }
    obtain ⟨fS, hfS, hfS_ne⟩ := SH.toSubmodule.ne_bot_iff.mp hSsub_ne
    let : Nontrivial SH.toSubmodule := ⟨⟨fS, hfS⟩, 0, by simpa using hfS_ne⟩
    let iS : SH.toRepresentation →ₗ ((coindRep (ρ := ρ)).comp H.subtype) := subrepInclusion SH
    obtain ⟨N, hNirr⟩ :=
      @Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
        F ↥H ↥SH.toSubmodule inferInstance inferInstance inferInstance inferInstance inferInstance
        SH.toRepresentation inferInstance
    let : Representation.IsIrreducible N.toRepresentation := hNirr
    let iNS : N.toRepresentation →ₗ SH.toRepresentation := subrepInclusion N
    let iN : N.toRepresentation →ₗ ((coindRep (ρ := ρ)).comp H.subtype) := iS.comp iNS
    have hiN_injective : Function.Injective iN := by
      intro a b hab
      simpa [iN, iS, iNS, subrepInclusion] using hab
    let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
    let n0 : N.toSubmodule := Classical.choose (exists_ne (0 : N.toSubmodule))
    have hn0_ne : n0 ≠ 0 := Classical.choose_spec (exists_ne (0 : N.toSubmodule))
    have hiNn0_ne : iN n0 ≠ 0 := by
      intro h0
      apply hn0_ne
      exact hiN_injective (by simpa using h0)
    obtain ⟨g, hg_ne⟩ : ∃ g : G, (iN n0).1 g ≠ 0 := by
      by_contra hnone
      apply hiNn0_ne
      ext x
      by_cases hx : (iN n0).1 x = 0
      · exact hx
      · exact False.elim (hnone ⟨x, hx⟩)
    let q : G ⧸ H := g
    let P (q' : G ⧸ H) :
        N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation :=
      (coindProjToCoset (ρ := ρ) q').comp iN
    have hPq_ne : P q ≠ 0 := by
      intro hP0
      apply hg_ne
      have h0 := congrArg
        (fun f => (((f n0).1 : Representation.coindV H.subtype ρ).1 g)) hP0
      simpa [P, q, coindProjToCoset, coindProj_apply] using h0
    have hP_unique (q' : G ⧸ H) (hq' : q' ≠ q) : P q' = 0 := by
      by_contra hPq'_ne
      let x : G := Classical.choose (QuotientGroup.mk_surjective q')
      have hx : (x : G ⧸ H) = q' := Classical.choose_spec (QuotientGroup.mk_surjective q')
      have :
          IsSimpleOrder
            (Subrepresentation ((coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) (g : G ⧸ H)
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q).toRepresentation)) := by
        simpa [q] using
          (coindCosetSubrep_irreducible (ρ := ρ) (g : G ⧸ H) :
            IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) ((g : G ⧸ H))).toRepresentation)))
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q').toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) q'
      let eNq :
          N.toRepresentation ≃ₗ
            (coindCosetSubrep (ρ := ρ) q).toRepresentation := by
          let fq : N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q).toRepresentation := P q
          have hfq_ne : fq ≠ 0 := by simpa [fq] using hPq_ne
          exact
            (show N.toRepresentation ≃ₗ (coindCosetSubrep (ρ := ρ) q).toRepresentation from
              repEquivOfNeZeroOfSimple
                (V₁ := N.toSubmodule)
                (V₂ := (coindCosetSubrep (ρ := ρ) q).toSubmodule)
                (ρ₁ := N.toRepresentation)
                (ρ₂ := (coindCosetSubrep (ρ := ρ) q).toRepresentation)
                (hρ₂ := coindCosetSubrep_irreducible (ρ := ρ) q)
                (f := fq)
                hfq_ne)
      let eNq' :
          N.toRepresentation ≃ₗ
            (coindCosetSubrep (ρ := ρ) q').toRepresentation := by
          let fq' : N.toRepresentation →ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation := P q'
          have hfq'_ne : fq' ≠ 0 := by simpa [fq'] using hPq'_ne
          exact
            (show N.toRepresentation ≃ₗ (coindCosetSubrep (ρ := ρ) q').toRepresentation from
              repEquivOfNeZeroOfSimple
                (V₁ := N.toSubmodule)
                (V₂ := (coindCosetSubrep (ρ := ρ) q').toSubmodule)
                (ρ₁ := N.toRepresentation)
                (ρ₂ := (coindCosetSubrep (ρ := ρ) q').toRepresentation)
                (hρ₂ := coindCosetSubrep_irreducible (ρ := ρ) q')
                (f := fq')
                hfq'_ne)
      let eCg :
          (coindCosetSubrep (ρ := ρ) q).toRepresentation ≃ₗ
            Theory.Representation.conjugateRep ρ g := by
        simpa [q] using (coindCosetEquiv (ρ := ρ) g)
      let eCx :
          (coindCosetSubrep (ρ := ρ) q').toRepresentation ≃ₗ
            Theory.Representation.conjugateRep ρ x := by
        rw [← hx]
        exact coindCosetEquiv (ρ := ρ) x
      let eNg : N.toRepresentation ≃ₗ Theory.Representation.conjugateRep ρ g := eNq.trans eCg
      let eNx : N.toRepresentation ≃ₗ Theory.Representation.conjugateRep ρ x := eNq'.trans eCx
      have hneqone : ((x * g⁻¹ : G) : G ⧸ H) ≠ 1 := by
        intro h1
        apply hq'
        calc
          q' = (x : G ⧸ H) := hx.symm
          _ = (g : G ⧸ H) := by
                have hxg' : (x : G ⧸ H) * (g : G ⧸ H)⁻¹ = 1 := by
                  simpa [div_eq_mul_inv] using h1
                calc
                  (x : G ⧸ H) = ((x : G ⧸ H) * (g : G ⧸ H)⁻¹) * (g : G ⧸ H) := by
                    simp [mul_assoc]
                  _ = (g : G ⧸ H) := by simp [hxg']
          _ = q := by rfl
      exact False.elim <|
        hnconj (x * g⁻¹) hneqone
          ⟨conj_diff_equiv (ρ := ρ) (e := eNg.symm.trans eNx)⟩
    have hmem_q (n : N.toSubmodule) : iN n ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule := by
      have hzero_proj (q' : G ⧸ H) (hq' : q' ≠ q) : coindProj (ρ := ρ) q' (iN n) = 0 := by
        have h0 := congrArg (fun f => ((f n).1 : Representation.coindV H.subtype ρ))
          (hP_unique q' hq')
        simpa [P, coindProjToCoset] using h0
      have h_eq : iN n = coindProj (ρ := ρ) q (iN n) := by
        ext x
        by_cases hx : (x : G ⧸ H) = q
        · simp [coindProj_apply, hx]
        · have hxproj : coindProj (ρ := ρ) (x : G ⧸ H) (iN n) = 0 := hzero_proj (x : G ⧸ H) hx
          have hxzero : (iN n).1 x = 0 := by
            have h0 := congrArg (fun f : Representation.coindV H.subtype ρ => f.1 x) hxproj
            simpa [coindProj_apply] using h0
          simp [coindProj_apply, hx, hxzero]
      rw [h_eq]
      exact coindProj_mem_coset (ρ := ρ) q (iN n)
    have hw0_q : iN n0 ∈ (coindCosetSubrep (ρ := ρ) q).toSubmodule := hmem_q n0
    have hw0_SH : iN n0 ∈ SH.toSubmodule := by
      change (((iS (iNS n0)) : Representation.coindV H.subtype ρ)) ∈ SH.toSubmodule
      exact (iNS n0).2
    have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) q).toRepresentation)) :=
      coindCosetSubrep_irreducible (ρ := ρ) q
    have hCq_le : (coindCosetSubrep (ρ := ρ) q).toSubmodule ≤ SH.toSubmodule := by
      exact subrep_le_of_nonzero_mem
        (ρ' := ((coindRep (ρ := ρ)).comp H.subtype))
        (S := coindCosetSubrep (ρ := ρ) q) (T := SH) hw0_q hw0_SH hiNn0_ne
    have hCr_le (r : G ⧸ H) : (coindCosetSubrep (ρ := ρ) r).toSubmodule ≤ SH.toSubmodule := by
      let y : G := Classical.choose (QuotientGroup.mk_surjective (r⁻¹ * q))
      have hy : (y : G ⧸ H) = r⁻¹ * q := Classical.choose_spec (QuotientGroup.mk_surjective (r⁻¹ * q))
      have hy_mem : coindRep (ρ := ρ) y (iN n0) ∈ (coindCosetSubrep (ρ := ρ) r).toSubmodule := by
        have hy_mem' := coind_apply_mem_coset_shift (ρ := ρ) y (iN n0) hw0_q
        simpa [hy, div_eq_mul_inv, mul_assoc] using hy_mem'
      have hy_SH : coindRep (ρ := ρ) y (iN n0) ∈ SH.toSubmodule := by
        exact S.apply_mem_toSubmodule y hw0_SH
      have hy_ne : coindRep (ρ := ρ) y (iN n0) ≠ 0 := by
        intro h0
        apply hiNn0_ne
        exact (Representation.apply_bijective (coindRep (ρ := ρ)) y).1 h0
      have : IsSimpleOrder (Subrepresentation ((coindCosetSubrep (ρ := ρ) r).toRepresentation)) :=
        coindCosetSubrep_irreducible (ρ := ρ) r
      exact subrep_le_of_nonzero_mem
        (ρ' := ((coindRep (ρ := ρ)).comp H.subtype))
        (S := coindCosetSubrep (ρ := ρ) r) (T := SH) hy_mem hy_SH hy_ne
    have hsup_le : (⨆ r : G ⧸ H, (coindCosetSubrep (ρ := ρ) r).toSubmodule) ≤ S.toSubmodule := by
      refine iSup_le ?_
      intro r
      exact hCr_le r
    have htop_le : (⊤ : Submodule F (Representation.coindV H.subtype ρ)) ≤ S.toSubmodule := by
      simpa [iSup_coindCosetSubrep_eq_top (ρ := ρ)] using hsup_le
    apply Subrepresentation.toSubmodule_injective
    exact le_antisymm le_top htop_le


set_option backward.isDefEq.respectTransparency false in
private noncomputable def CFSG.coindMapFromRepMapAux
    {F : Type*} [Field F] {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] {W : Type*}
    [AddCommGroup W] [Module F W] (σ : Representation F G W)
    (ρ : Representation F H V) (π : σ.comp H.subtype →ₗ ρ) :
    σ →ₗ coindRep ρ := by
  let lift : W →ₗ[F] Representation.coindV H.subtype ρ :=
    { toFun := fun w => ⟨fun g => π (σ g w), by
          intro h g
          change π (σ ((h : G) * g) w) = ρ h (π (σ g w))
          rw [σ.map_mul]
          exact
            Representation.IntertwiningMap.isIntertwining
              (ρ := σ.comp H.subtype) (σ := ρ) π h (σ g w)⟩
      map_add' := by
        intro w1 w2
        apply Subtype.ext
        ext g
        simp
      map_smul' := by
        intro a w
        apply Subtype.ext
        ext g
        simp }
  refine Theory.Representation.RepMap.mk lift ?_
  intro g
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  ext x
  simp [lift, coindRep, Representation.coind_apply, σ.map_mul]

private theorem CFSG.coindEval_coindMapFromRepMapAux
    {F : Type*} [Field F] {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] {W : Type*}
    [AddCommGroup W] [Module F W] (σ : Representation F G W)
    (ρ : Representation F H V) (π : σ.comp H.subtype →ₗ ρ) (g : G) (w : W) :
    coindEval (ρ := ρ) g (coindMapFromRepMapAux σ ρ π w) = π (σ g w) := rfl

private noncomputable def CFSG.coindMapFromRepMapAuxOfSubrepAux
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] (σ : Representation F G V)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (σ.comp H.subtype)) :
    σ →ₗ coindRep M.toRepresentation := by
  let σH : Representation F H V := σ.comp H.subtype
  have hσHcr : σH.IsCompletelyReducible := by
    exact Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime (ρ := σH) hchar
  let : ComplementedLattice (Subrepresentation σH) := by
    exact
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
        (ρ := σH)).2 hσHcr
  let ψ : Subrepresentation σH := Classical.choose (exists_isCompl M)
  have hcompl : IsCompl M ψ := Classical.choose_spec (exists_isCompl M)
  have hcompl_sub : IsCompl M.toSubmodule ψ.toSubmodule := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      calc
        (M ⊓ ψ).toSubmodule = (⊥ : Subrepresentation σH).toSubmodule :=
          congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
        _ = (⊥ : Submodule F V) := rfl
    · rw [codisjoint_iff]
      calc
        (M ⊔ ψ).toSubmodule = (⊤ : Subrepresentation σH).toSubmodule :=
          congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
        _ = (⊤ : Submodule F V) := rfl
  let proj : V →ₗ[F] M.toSubmodule :=
    Submodule.projectionOnto M.toSubmodule ψ.toSubmodule hcompl_sub
  have hproj_intertwining (h : H) :
      proj.comp (σH h) = (M.toRepresentation h).comp proj := by
    apply LinearMap.ext
    intro v
    rcases Submodule.existsUnique_add_of_isCompl hcompl_sub v with ⟨u, w, huw, huniq⟩
    have hu_mem : (σH h) u ∈ M.toSubmodule := M.apply_mem_toSubmodule h u.2
    have hw_mem : (σH h) w ∈ ψ.toSubmodule := ψ.apply_mem_toSubmodule h w.2
    let projψ : V →ₗ[F] ψ.toSubmodule :=
      Submodule.projectionOnto ψ.toSubmodule M.toSubmodule hcompl_sub.symm
    have hdecomp : (proj v : V) + (projψ v : V) = v := by
      simpa [proj, projψ] using Submodule.projection_add_projection_eq_self hcompl_sub v
    have hproj_v : proj v = u := by
      exact huniq (proj v) (projψ v) hdecomp |>.1
    have hproj_hu : proj ((σH h) u) = ⟨(σH h) u, hu_mem⟩ := by
      simpa [proj] using Submodule.projectionOnto_apply_left hcompl_sub ⟨(σH h) u, hu_mem⟩
    have hproj_hw : proj ((σH h) w) = 0 := by
      simpa [proj] using Submodule.projectionOnto_apply_right hcompl_sub ⟨(σH h) w, hw_mem⟩
    apply Subtype.ext
    calc
      (((proj.comp (σH h)) v : M.toSubmodule) : V) =
          ((proj ((σH h) u + (σH h) w) : M.toSubmodule) : V) := by
            rw [LinearMap.comp_apply, ← huw, map_add]
      _ = ((proj ((σH h) u) : M.toSubmodule) : V) + ((proj ((σH h) w) : M.toSubmodule) : V) := by
            simp [map_add]
      _ = (σH h) u + 0 := by
            rw [hproj_hu, hproj_hw]
            simp
      _ = (σH h) u := by simp
      _ = (σH h) (proj v) := by rw [congrArg Subtype.val hproj_v.symm]
      _ = (((M.toRepresentation h).comp proj v : M.toSubmodule) : V) := by rfl
  exact
    coindMapFromRepMapAux σ M.toRepresentation
      (Theory.Representation.RepMap.mk proj hproj_intertwining)

private theorem CFSG.coindMapFromRepMapAuxOfSubrepAuxAux_eval_one
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] (σ : Representation F G V)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (σ.comp H.subtype)) (m : M.toSubmodule) :
    coindEval (ρ := M.toRepresentation) (1 : G)
      (coindMapFromRepMapAuxOfSubrepAux σ hchar M m) = m := by
  classical
  unfold coindMapFromRepMapAuxOfSubrepAux
  simp only [coindEval_coindMapFromRepMapAux, map_one, Module.End.one_apply,
    Theory.Representation.RepMap.coe_mk, Submodule.projectionOnto_apply_left]

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.semisimple_le_ker_of_forall_simple_submodule_le_ker {G : Type*} [Group G] {F : Type*}
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
    intro s hs x hx
    induction s using Finset.induction_on generalizing x with
    | empty =>
        simp at hx
        simp [hx]
    | @insert q t hqt ih =>
        rw [Finset.iSup_insert] at hx
        have hx' : x ∈ q ⊔ ⨆ m ∈ t, m := by
          simpa [hqt] using hx
        obtain ⟨xq, hxq, xt, hxt, rfl⟩ := Submodule.mem_sup.mp hx'
        have hq_simple : IsSimpleModule (MonoidAlgebra F G) q := hs (Finset.mem_insert_self q t)
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
            exact hs (Finset.mem_insert_of_mem hm)) xt hxt
        calc
          ρ h (ρ.asModuleEquiv (xq + xt))
              = ρ h (ρ.asModuleEquiv xq + ρ.asModuleEquiv xt) := by simp
          _ = ρ h (ρ.asModuleEquiv xq) + ρ h (ρ.asModuleEquiv xt) := by simp
          _ = ρ.asModuleEquiv xq + ρ.asModuleEquiv xt := by simp [hq_fix, ht_fix]
          _ = ρ.asModuleEquiv (xq + xt) := by simp
  simpa [v'] using hsfix s hs v' hvs

set_option backward.isDefEq.respectTransparency false in
/-- A semisimple representation on which a subgroup acts nontrivially has a simple
constituent on which that subgroup still acts nontrivially. -/
public theorem CFSG.exists_simple_submodule_not_le_ker_of_semisimple
    {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule]
    (H : Subgroup G) (hH : ¬ H ≤ ρ.ker) :
    ∃ m : Submodule (MonoidAlgebra F G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra F G) m ∧
        ¬ H ≤ (Subrepresentation.ofSubmodule' m).toRepresentation.ker := by
  by_contra hcontra
  push Not at hcontra
  exact hH (semisimple_le_ker_of_forall_simple_submodule_le_ker ρ H hcontra)
set_option backward.isDefEq.respectTransparency false in
/-- A simple group-algebra submodule defines an irreducible subrepresentation. -/
public theorem CFSG.irreducible_subrepresentation_of_simple_asModuleSubmodule {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    {m : Submodule (MonoidAlgebra F G) ρ.asModule}
    (hm : IsSimpleModule (MonoidAlgebra F G) m) :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' m).toRepresentation := by
  rw [Subrepresentation.irreducible_iff_isAtom]
  exact
    ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm.isAtom_iff
      (a := m)).2 <| (isSimpleModule_iff_isAtom).1 hm

set_option backward.isDefEq.respectTransparency false in
/-- An irreducible representation is equivalent to the coinduction of a simple constituent
of its semisimple restriction when that constituent has no equivalent nontrivial conjugate. -/
public noncomputable def CFSG.coindEquivOfSubrep_noNontrivialConj
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ρ : Representation F G V) [Representation.IsIrreducible ρ]
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (ρ.comp H.subtype))
    [Representation.IsIrreducible M.toRepresentation]
    (hnconj : ∀ x : G, (x : G ⧸ H) ≠ 1 →
      ¬ Nonempty (M.toRepresentation ≃ₗ Theory.Representation.conjugateRep M.toRepresentation x)) :
    ρ ≃ₗ coindRep M.toRepresentation := by
  let : FiniteDimensional F M.toSubmodule := FiniteDimensional.of_injective M.toSubmodule.subtype
    Subtype.val_injective
  let f : ρ →ₗ coindRep M.toRepresentation := coindMapFromRepMapAuxOfSubrepAux ρ hchar M
  let : Nontrivial M.toSubmodule := Subrepresentation.irreducible_module_nontrivial M.toRepresentation
  have hf_ne : f ≠ 0 := by
    obtain ⟨m0, hm0_ne⟩ := exists_ne (0 : M.toSubmodule)
    intro hf0
    have h_eval :
        coindEval (ρ := M.toRepresentation) (1 : G) (f m0) = m0 :=
      coindMapFromRepMapAuxOfSubrepAuxAux_eval_one ρ hchar M m0
    have h_zero :
        coindEval (ρ := M.toRepresentation) (1 : G) (f m0) = 0 := by
      simp [f, hf0]
    exact hm0_ne (h_eval.symm.trans h_zero)
  have hsimple_coind :
      IsSimpleOrder (Subrepresentation (coindRep (ρ := M.toRepresentation))) :=
    coindRep_irreducible_of_noNontrivialConj (ρ := M.toRepresentation) hnconj
  let : Representation.IsIrreducible (coindRep (ρ := M.toRepresentation)) := hsimple_coind
  have hfinj : Function.Injective f := by
    rcases (Representation.IsIrreducible.injective_or_eq_zero
      (ρ := ρ) (σ := coindRep (ρ := M.toRepresentation)) (f := f)) with hfinj | hf0
    · exact hfinj
    · exact False.elim (hf_ne hf0)
  have hrange_ne : f.range ≠ ⊥ := by
    intro hbot
    apply hf_ne
    apply Theory.Representation.RepMap.toLinearMap_injective
    apply LinearMap.range_eq_bot.mp
    calc
      f.toLinearMap.range = f.range.toSubmodule := rfl
      _ = (⊥ : Subrepresentation (coindRep (ρ := M.toRepresentation))).toSubmodule :=
        congrArg Subrepresentation.toSubmodule hbot
      _ = (⊥ : Submodule F (Representation.coindV H.subtype M.toRepresentation)) := rfl
  have hrange_top : f.range = ⊤ := by
    rcases (inferInstance : Representation.IsIrreducible (coindRep (ρ := M.toRepresentation))).eq_bot_or_eq_top f.range with
      hbot | htop
    · exact False.elim (hrange_ne hbot)
    · exact htop
  have hfsurj : Function.Surjective f := by
    exact LinearMap.range_eq_top.mp (by
      calc
        f.toLinearMap.range = f.range.toSubmodule := rfl
        _ = (⊤ : Subrepresentation (coindRep (ρ := M.toRepresentation))).toSubmodule :=
          congrArg Subrepresentation.toSubmodule hrange_top
        _ = (⊤ : Submodule F (Representation.coindV H.subtype M.toRepresentation)) := rfl)
  let eLin : V ≃ₗ[F] Representation.coindV H.subtype M.toRepresentation :=
    LinearEquiv.ofBijective f.toLinearMap ⟨hfinj, hfsurj⟩
  refine Theory.Representation.RepEquiv.mk eLin ?_
  intro g
  ext v x
  simpa [LinearMap.comp_apply, eLin] using congrArg
    (fun z : Representation.coindV H.subtype M.toRepresentation => z.1 x)
    (Representation.IntertwiningMap.isIntertwining
      (ρ := ρ) (σ := coindRep (ρ := M.toRepresentation)) f g v)

noncomputable def CFSG.quotientSection [Fintype (G ⧸ H)] (q : G ⧸ H) : G :=
  Classical.choose (QuotientGroup.mk_surjective q)

omit [H.Normal] in
theorem CFSG.quotientSection_spec [Fintype (G ⧸ H)] (q : G ⧸ H) :
    ((quotientSection (G := G) (H := H) q : G) : G ⧸ H) = q :=
  Classical.choose_spec (QuotientGroup.mk_surjective q)

theorem CFSG.coindBase_eq_coindProj_of_section [Fintype (G ⧸ H)]
    (f : Representation.coindV H.subtype ρ) (q : G ⧸ H) :
    coindBaseFunctionAt (ρ := ρ)
        (quotientSection (G := G) (H := H) q)
        (coindEval (ρ := ρ) (quotientSection (G := G) (H := H) q) f) =
      coindProj (ρ := ρ) q f := by
  let g : G := quotientSection (G := G) (H := H) q
  have hg : (g : G ⧸ H) = q := quotientSection_spec (G := G) (H := H) q
  have hEq0 :
      coindBaseFunctionAt (ρ := ρ) g (coindEval (ρ := ρ) g f) =
        coindProj (ρ := ρ) (g : G ⧸ H) f := by
    let lhs : ↥((coindCosetSubrep (ρ := ρ) (g : G ⧸ H)).toSubmodule) := by
      refine ⟨coindBaseFunctionAt (ρ := ρ) g (coindEval (ρ := ρ) g f), ?_⟩
      simpa using
        (coindBaseFunctionAt_mem_coset (ρ := ρ) g (coindEval (ρ := ρ) g f))
    let rhs : ↥((coindCosetSubrep (ρ := ρ) (g : G ⧸ H)).toSubmodule) :=
      coindProjToCoset (ρ := ρ) (g : G ⧸ H) f
    have hEqImg : coindCosetEquiv (ρ := ρ) g lhs = coindCosetEquiv (ρ := ρ) g rhs := by
      change coindEval (ρ := ρ) g lhs.1 = coindEval (ρ := ρ) g rhs.1
      change
        coindEval (ρ := ρ) g (coindBaseFunctionAt (ρ := ρ) g (coindEval (ρ := ρ) g f)) =
          coindEval (ρ := ρ) g (coindProj (ρ := ρ) (g : G ⧸ H) f)
      rw [coindEval_base]
      change f.1 g = (coindProj (ρ := ρ) (g : G ⧸ H) f).1 g
      simp [coindProj_apply]
    have hEq : lhs = rhs := (coindCosetEquiv (ρ := ρ) g).injective hEqImg
    exact congrArg Subtype.val hEq
  simpa [g, hg] using hEq0

public noncomputable def CFSG.coindPiEquiv [Fintype (G ⧸ H)] :
    Representation.coindV H.subtype ρ ≃ₗ[F] (G ⧸ H → V) where
  toFun f q := coindEval (ρ := ρ) (quotientSection (G := G) (H := H) q) f
  invFun ψ := ∑ q : G ⧸ H,
    coindBaseFunctionAt (ρ := ρ) (quotientSection (G := G) (H := H) q) (ψ q)
  left_inv f := by
    ext x
    calc
      (∑ q : G ⧸ H,
          coindBaseFunctionAt (ρ := ρ) (quotientSection (G := G) (H := H) q)
            (coindEval (ρ := ρ) (quotientSection (G := G) (H := H) q) f)).1 x
          = (∑ q : G ⧸ H, coindProj (ρ := ρ) q f).1 x := by
              simp [coindBase_eq_coindProj_of_section]
      _ = f.1 x := by
            simp
  right_inv ψ := by
    ext q
    let g : G := quotientSection (G := G) (H := H) q
    have hg : (g : G ⧸ H) = q := quotientSection_spec (G := G) (H := H) q
    calc
      coindEval (ρ := ρ) g
          (∑ q' : G ⧸ H,
            coindBaseFunctionAt (ρ := ρ)
              (quotientSection (G := G) (H := H) q') (ψ q'))
          = ∑ q' : G ⧸ H,
              coindEval (ρ := ρ) g
                (coindBaseFunctionAt (ρ := ρ)
                  (quotientSection (G := G) (H := H) q') (ψ q')) := by
                change (coindEval (ρ := ρ) g).toLinearMap
                    (∑ q' : G ⧸ H,
                      coindBaseFunctionAt (ρ := ρ)
                        (quotientSection (G := G) (H := H) q') (ψ q')) =
                  ∑ q' : G ⧸ H,
                    (coindEval (ρ := ρ) g).toLinearMap
                      (coindBaseFunctionAt (ρ := ρ)
                        (quotientSection (G := G) (H := H) q') (ψ q'))
                simp
      _ = ψ q := by
            classical
            rw [Finset.sum_eq_single q]
            · simp [g]
            · intro q' _ hq'
              have hqg :
                  ((quotientSection (G := G) (H := H) q' : G) : G ⧸ H) ≠ (g : G ⧸ H) := by
                simpa [quotientSection_spec (G := G) (H := H) q',
                  hg] using hq'
              have hqg' : (g : G ⧸ H) ≠ ((quotientSection (G := G) (H := H) q' : G) : G ⧸ H) := by
                simpa [ne_comm] using hqg
              simpa [g] using
                (coindEval_of_ne_coset (ρ := ρ)
                  (x := g)
                  (g := quotientSection (G := G) (H := H) q')
                  hqg' (ψ q'))
            · intro hq'
              exact False.elim (hq' (Finset.mem_univ q))
  map_add' f₁ f₂ := by
    ext q
    simp
  map_smul' a f := by
    ext q
    simp

public theorem CFSG.finrank_coindRep_eq_card_mul [Fintype (G ⧸ H)] [FiniteDimensional F V] :
    Module.finrank F (Representation.coindV H.subtype ρ) =
      Fintype.card (G ⧸ H) * Module.finrank F V := by
  rw [LinearEquiv.finrank_eq (coindPiEquiv (ρ := ρ))]
  simpa using
    (Module.finrank_pi_fintype (R := F) (M := fun _ : G ⧸ H => V))

end

set_option backward.isDefEq.respectTransparency false in
lemma CFSG.lemma_2_3_algClosed
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [inst : IsAbsolutelyIrreducible ρ] :
    Module.finrank F V ∣ Nat.card G := by
  classical
  generalize hcard : Nat.card G = n
  revert G V ρ inst hcard
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ W _ _ _ ρ hσabs hcard
    let : IsAbsolutelyIrreducible ρ := hσabs
    let : IsIrreducible ρ :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
    by_cases! hn : n ≤ 1
    · have hk1 : Nat.card G = 1 := by
        have hkpos : 0 < Nat.card G := Nat.card_pos
        omega
      let : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hk1).1
      let : IsMulCommutative G := {
        is_comm := {
          comm a b := by
            have ha : a = 1 := by exact Subsingleton.eq_one a
            have hb : b = 1 := by exact Subsingleton.eq_one b
            rw [ha, hb]
        }
      }
      have hdim1 : Module.finrank F W = 1 := by
        simpa using
          (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
            (ρ := ρ))
      rw [hdim1]
      exact Nat.one_dvd _
    · let : Nontrivial G := by
        exact Finite.one_lt_card_iff_nontrivial.mp <| Nat.lt_of_lt_of_eq hn (id (Eq.symm hcard))
      obtain ⟨H, hH1, hH2⟩ := exist_index_p_of_solvable G
      let : H.Normal := hH1
      let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
      let ρH : Representation F H W := ρ.comp H.subtype
      let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
      obtain ⟨N, hNirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρH
      let σ : Representation F H N.toSubmodule := N.toRepresentation
      let : IsIrreducible σ := hNirr
      have hσsurj : Function.Surjective (algebraMap F (End σ)) := by
        exact surjective_of_jacobson_density_surjective_rep σ
          (jacobson_density_surjective_isAlgClosed_rep σ)
      let : IsAbsolutelyIrreducible σ := (isAbsolutelyIrreducible_iff_surjective σ).2 hσsurj
      have hHlt : Nat.card H < n := by
        have hmul : Nat.card H * H.index = n := by
          calc
            Nat.card H * H.index = Nat.card G := by simp
            _ = n := hcard
        have hHpos : 0 < Nat.card H := Nat.card_pos (α := H)
        have hHmul : Nat.card H < Nat.card H * H.index := by
          simpa [one_mul] using Nat.mul_lt_mul_of_pos_left hH2.one_lt hHpos
        calc
          Nat.card H < Nat.card H * H.index := hHmul
          _ = n := hmul
      have hσ_dvd_H : Module.finrank F N.toSubmodule ∣ Nat.card H := by
        exact ih (Nat.card H) hHlt (ρ := σ) rfl
      have hcardQ : Nat.card (G ⧸ H) = H.index := by
        rw [H.index_eq_card]
      let : Fact (Nat.Prime H.index) := ⟨hH2⟩
      have hcyc : IsCyclic (G ⧸ H) := isCyclic_of_prime_card (α := G ⧸ H) hcardQ
      have hQ_nontrivial : Nontrivial (G ⧸ H) := by
        have hQcard : Fintype.card (G ⧸ H) = H.index := by
          simpa using H.index_eq_card.symm
        exact
          Finite.one_lt_card_iff_nontrivial.mp <|
            by simpa [hQcard] using hH2.one_lt
      let : Nontrivial (G ⧸ H) := hQ_nontrivial
      let q0 : G ⧸ H := Classical.choose (exists_ne (1 : G ⧸ H))
      have hq0_ne : q0 ≠ 1 := Classical.choose_spec (exists_ne (1 : G ⧸ H))
      let x : G := quotientSection (G := G) (H := H) q0
      have hxq : (x : G ⧸ H) = q0 := quotientSection_spec (G := G) (H := H) q0
      have hx_ne_one : (x : G ⧸ H) ≠ 1 := by
        simpa [x, hxq] using hq0_ne
      by_cases hxe : Nonempty (σ ≃ₗ conjugateRep σ x)
      · rcases hxe with ⟨e⟩
        have hE : ∀ y : G, σ ≃ₗ conjugateRep σ y :=
          all_conjugates_of_prime_quotient (ρ := σ) hcardQ hH2 hx_ne_one e
        let eρσ : ρH ≃ₗ σ :=
          proposition_2_2_a
            (G := G) (H := H) (W := W) hcyc σ hE
            (ι := ρ) (φ := N) (RepEquiv.refl σ)
        have hdim_eq : Module.finrank F W = Module.finrank F N.toSubmodule := by
          simpa [ρH, σ] using (LinearEquiv.finrank_eq eρσ.toLinearEquiv)
        have hHdvdG : Nat.card H ∣ Nat.card G := by
          refine ⟨H.index, ?_⟩
          simp
        have hfinG : Module.finrank F W ∣ Nat.card G := by
          rw [hdim_eq]
          exact dvd_trans hσ_dvd_H hHdvdG
        simpa [hcard] using hfinG
      · let shiftMap : ∀ g : G, conjugateRep σ g⁻¹ →ₗ ρH := fun g => by
            refine RepMap.mk ?_ ?_
            · exact
                { toFun := fun v => ρ g v
                  map_add' := by
                    intro u v
                    simp
                  map_smul' := by
                    intro a v
                    simp }
            · intro h
              ext v
              let k : H := ⟨g⁻¹ * h * g,
                by
                  simpa using
                    (Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⁻¹)⟩
              have hk :
                  ρ g (σ k v) = ρ h (ρ g v) := by
                change (((ρ g) * (ρ (k : G))) v) = (((ρ h) * (ρ g)) v)
                rw [← ρ.map_mul, ← ρ.map_mul]
                congr 1
                simp [k, mul_assoc]
              simpa [Theory.Representation.conjugateRep_apply, ρH, σ, k] using hk
        let A : G ⧸ H → Subrepresentation ρH := fun q =>
          (shiftMap (quotientSection (G := G) (H := H) q)).range
        let eA : ∀ q : G ⧸ H,
            conjugateRep σ (quotientSection (G := G) (H := H) q)⁻¹ ≃ₗ (A q).toRepresentation := by
          intro q
          let g : G := quotientSection (G := G) (H := H) q
          let f : conjugateRep σ g⁻¹ →ₗ (A q).toRepresentation := by
            refine RepMap.mk ?_ ?_
            · exact
                { toFun := fun v => ⟨shiftMap g v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
                  map_add' := by
                    intro u v
                    ext; simp
                  map_smul' := by
                    intro a v
                    ext; simp }
            · intro h
              ext v
              change
                shiftMap g (conjugateRep σ g⁻¹ h v) =
                  ρH h (shiftMap g v)
              exact
                Representation.IntertwiningMap.isIntertwining
                  (ρ := conjugateRep σ g⁻¹) (σ := ρH) (f := shiftMap g) h v
          refine RepEquiv.mk (LinearEquiv.ofBijective f.toLinearMap ?_) ?_
          · constructor
            · intro u v huv
              apply Subtype.ext
              apply (Representation.apply_bijective ρ g).1
              exact congrArg Subtype.val huv
            · intro w
              rcases w.2 with ⟨v, hv⟩
              refine ⟨v, ?_⟩
              apply Subtype.ext
              exact hv
          · intro h
            ext v
            simpa using
                (Representation.IntertwiningMap.isIntertwining
                  (ρ := conjugateRep σ g⁻¹) (σ := (A q).toRepresentation) (f := f) h v)
        have hA_irr (q : G ⧸ H) : IsIrreducible (A q).toRepresentation := by
          let g : G := quotientSection (G := G) (H := H) q
          let : IsIrreducible (conjugateRep σ g⁻¹) :=
            conjugateRep_irreducible (G := G) (H := H) (ρ := σ) g⁻¹
          exact (RepEquiv.irreducible_euqiv (eA q).symm).2 inferInstance
        have hA_dim (q : G ⧸ H) :
            Module.finrank F (A q).toSubmodule = Module.finrank F N.toSubmodule := by
          simpa [σ] using (LinearEquiv.finrank_eq (eA q).toLinearEquiv).symm
        have hA_disj :
            Pairwise fun q r : G ⧸ H => Disjoint (A q).toSubmodule (A r).toSubmodule := by
          intro q r hqr
          refine Submodule.disjoint_def.mpr ?_
          intro w hwq hwr
          by_cases hw0 : w = 0
          · exact hw0
          · let gq : G := quotientSection (G := G) (H := H) q
            let gr : G := quotientSection (G := G) (H := H) r
            have hgq : (gq : G ⧸ H) = q := quotientSection_spec (G := G) (H := H) q
            have hgr : (gr : G ⧸ H) = r := quotientSection_spec (G := G) (H := H) r
            have : IsIrreducible (A q).toRepresentation := hA_irr q
            have : IsIrreducible (A r).toRepresentation := hA_irr r
            have hq_le_r : A q ≤ A r := by
              exact
                subrep_le_of_nonzero_mem
                  (ρ' := ρH) (S := A q) (T := A r) hwq hwr hw0
            have hr_le_q : A r ≤ A q := by
              exact
                subrep_le_of_nonzero_mem
                  (ρ' := ρH) (S := A r) (T := A q) hwr hwq hw0
            have hEq : A q = A r := le_antisymm hq_le_r hr_le_q
            have eqr : conjugateRep σ gq⁻¹ ≃ₗ conjugateRep σ gr⁻¹ := by
              refine (eA q).trans ?_
              rw [hEq]
              exact (eA r).symm
            have hdiff_ne_one : (((gr⁻¹ * gq : G) : G ⧸ H)) ≠ 1 := by
              intro h1
              have hmul : (gr : G ⧸ H)⁻¹ * (gq : G ⧸ H) = 1 := by
                simpa [div_eq_mul_inv] using h1
              have hEqgrgq : (gr : G ⧸ H) = (gq : G ⧸ H) := by
                have hmul' :=
                  congrArg (fun z : G ⧸ H => (gr : G ⧸ H) * z) hmul
                simpa [mul_assoc] using hmul'.symm
              apply hqr
              calc
                q = (gq : G ⧸ H) := hgq.symm
                _ = (gr : G ⧸ H) := hEqgrgq.symm
                _ = r := hgr
            have hconj : σ ≃ₗ conjugateRep σ (gr⁻¹ * gq) := by
              simpa using (conj_diff_equiv (ρ := σ) (e := eqr))
            have hall : ∀ y : G, σ ≃ₗ conjugateRep σ y :=
              all_conjugates_of_prime_quotient
                (ρ := σ) hcardQ hH2 hdiff_ne_one hconj
            exact False.elim (hxe ⟨hall x⟩)
        let Tsub : Submodule F W := ⨆ q : G ⧸ H, (A q).toSubmodule
        have hmap_A (y : G) (q : G ⧸ H) :
            Submodule.map (ρ y) (A q).toSubmodule ≤ (A ((y : G ⧸ H) * q)).toSubmodule := by
          intro w hw
          let gq : G := quotientSection (G := G) (H := H) q
          have hgq : (gq : G ⧸ H) = q := quotientSection_spec (G := G) (H := H) q
          let s : G := quotientSection (G := G) (H := H) ((y : G ⧸ H) * q)
          have hs : (s : G ⧸ H) = (y : G ⧸ H) * q :=
            quotientSection_spec (G := G) (H := H) ((y : G ⧸ H) * q)
          rcases hw with ⟨u, hu, rfl⟩
          rcases hu with ⟨v, rfl⟩
          change ρ y (ρ gq v) ∈ LinearMap.range ((shiftMap s).toLinearMap)
          refine LinearMap.mem_range.mpr ?_
          have hyq : ((y * gq : G) : G ⧸ H) = (s : G ⧸ H) := by
            calc
              ((y * gq : G) : G ⧸ H) = (y : G ⧸ H) * (gq : G ⧸ H) := by simp
              _ = (y : G ⧸ H) * q := by rw [hgq]
              _ = (s : G ⧸ H) := hs.symm
          have hdiv : (y * gq) / s ∈ H := (QuotientGroup.eq_iff_div_mem).mp hyq
          have ha_mem : s⁻¹ * y * gq ∈ H := by
            simpa [div_eq_mul_inv, mul_assoc] using
              Subgroup.Normal.conj_mem (inferInstance : H.Normal) ((y * gq) / s) hdiv s⁻¹
          let a : H := ⟨s⁻¹ * y * gq, ha_mem⟩
          refine ⟨σ a v, ?_⟩
          change ρ s (ρ a v) = ρ y (ρ gq v)
          calc
            ρ s (ρ a v) = ((ρ s) * (ρ a)) v := by
              rfl
            _ = ρ (s * a) v := by
              rw [← ρ.map_mul]
            _ = ρ (y * gq) v := by
              have hsa : s * (a : G) = y * gq := by
                simp [a, mul_assoc]
              rw [hsa]
            _ = ((ρ y) * (ρ gq)) v := by
              rw [← ρ.map_mul]
            _ = ρ y (ρ gq v) := by
              rfl
        have hTmap (y : G) : Submodule.map (ρ y) Tsub ≤ Tsub := by
          dsimp [Tsub]
          rw [Submodule.map_iSup]
          refine iSup_le ?_
          intro q
          exact (hmap_A y q).trans (le_iSup (fun r : G ⧸ H => (A r).toSubmodule) ((y : G ⧸ H) * q))
        let T : Subrepresentation ρ := {
          toSubmodule := Tsub
          apply_mem_toSubmodule := by
            intro y w hw
            have hwmap : ρ y w ∈ Submodule.map (ρ y) Tsub := by
              exact Submodule.mem_map_of_mem (f := ρ y) hw
            exact hTmap y hwmap
        }
        let g1 : G := quotientSection (G := G) (H := H) (1 : G ⧸ H)
        let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial σ
        let n0 : N.toSubmodule := Classical.choose (exists_ne (0 : N.toSubmodule))
        have hn0_ne : n0 ≠ 0 := Classical.choose_spec (exists_ne (0 : N.toSubmodule))
        have hw1_mem : ρ g1 n0 ∈ Tsub := by
          apply Submodule.mem_iSup_of_mem (1 : G ⧸ H)
          change ρ g1 n0 ∈ LinearMap.range ((shiftMap g1).toLinearMap)
          exact LinearMap.mem_range.mpr ⟨n0, rfl⟩
        have hw1_ne : ρ g1 n0 ≠ 0 := by
          intro h0
          apply hn0_ne
          apply Subtype.ext
          apply (Representation.apply_bijective ρ g1).1
          simpa using h0
        have hw1_memT : ρ g1 n0 ∈ T.toSubmodule := hw1_mem
        have hT_ne : T ≠ ⊥ := by
          intro hT
          have hw0 : ρ g1 n0 = 0 := by
            have : ρ g1 n0 ∈ (⊥ : Subrepresentation ρ).toSubmodule := by
              simpa [hT] using hw1_memT
            change ρ g1 n0 = 0 at this
            exact this
          exact hw1_ne hw0
        have hT_top : T = ⊤ := by
          rcases (inferInstance : IsIrreducible ρ).eq_bot_or_eq_top T with hbot | htop
          · exact False.elim (hT_ne hbot)
          · exact htop
        have hTsub_top : Tsub = ⊤ := by
          calc
            Tsub = T.toSubmodule := rfl
            _ = (⊤ : Subrepresentation ρ).toSubmodule :=
              congrArg Subrepresentation.toSubmodule hT_top
            _ = (⊤ : Submodule F W) := rfl
        have hA_indep : iSupIndep (fun q : G ⧸ H => (A q).toSubmodule) := by
          classical
          have hA_disjoint_biSup :
              ∀ q : G ⧸ H, ∀ s : Finset (G ⧸ H), q ∉ s →
                Disjoint (A q).toSubmodule (⨆ q' ∈ s, (A q').toSubmodule) := by
            intro q s hq
            rw [disjoint_iff]
            apply bot_unique
            intro w hw
            rcases Submodule.mem_inf.mp hw with ⟨hwq, hws⟩
            by_cases hw0 : w = 0
            · simp [hw0]
            · let : Module F[H] (Representation.asModule ρH) :=
                ρH.instModuleMonoidAlgebraAsModule
              let U : Subrepresentation ρH := ⨆ r ∈ s, A r
              let Umod : Submodule F[H] (Representation.asModule ρH) :=
                ⨆ r : s, ((A r).asSubmodule : Submodule F[H] (Representation.asModule ρH))
              have hUmod_eq : U.asSubmodule = Umod := by
                calc
                  U.asSubmodule
                      = (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρH)) U := rfl
                  _ = (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρH))
                        (⨆ r ∈ s, A r) := by rfl
                  _ = ⨆ r ∈ s,
                        (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρH)) (A r) := by
                          simp
                  _ = ⨆ r ∈ s,
                        ((A r).asSubmodule : Submodule F[H] (Representation.asModule ρH)) := by
                          simp
                  _ = Umod := by
                        simp [Umod, iSup_subtype]
              have hleU_toSubmodule : (⨆ r ∈ s, (A r).toSubmodule) ≤ U.toSubmodule := by
                refine iSup_le fun r => iSup_le fun hr => ?_
                change (A r).toSubmodule ≤ U.toSubmodule
                exact show A r ≤ U from le_iSup_of_le r (le_iSup_of_le hr le_rfl)
              have hwU : w ∈ U := by
                exact hleU_toSubmodule hws
              have hleU : A q ≤ U := by
                exact subrep_le_of_nonzero_mem
                  (ρ' := ρH) (S := A q) (T := U) hwq hwU hw0
              have hleMod : (A q).asSubmodule ≤ Umod := by
                rw [← hUmod_eq]
                intro x hx
                exact hleU hx
              let sSet : Set (Submodule F[H] (Representation.asModule ρH)) :=
                Set.range fun r : s => ((A r).asSubmodule : Submodule F[H] (Representation.asModule ρH))
              have hU_eq : sSup sSet = Umod := by
                simpa [sSet, Umod] using
                  (sSup_range
                    (f := fun r : s =>
                      ((A r).asSubmodule : Submodule F[H] (Representation.asModule ρH))))
              have hleSet : (A q).asSubmodule ≤ sSup sSet := by
                rw [hU_eq]
                exact hleMod
              have hsimple (r : s) :
                  IsSimpleModule F[H]
                    (((A r).asSubmodule :
                      Submodule F[H] (Representation.asModule ρH))) := by
                rw [isSimpleModule_iff_isAtom]
                exact
                  ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρH)).isAtom_iff
                    (a := A r)).2 <|
                    (Subrepresentation.irreducible_iff_isAtom (φ := A r)).1 (hA_irr r)
              have hsimpleSet (m : sSet) : IsSimpleModule F[H] m := by
                rcases m with ⟨m, hm⟩
                rcases hm with ⟨r, rfl⟩
                exact hsimple r
              have hsimpleq :
                  IsSimpleModule F[H]
                    (((A q).asSubmodule :
                      Submodule F[H] (Representation.asModule ρH))) := by
                rw [isSimpleModule_iff_isAtom]
                exact
                  ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρH)).isAtom_iff
                    (a := A q)).2 <|
                    (Subrepresentation.irreducible_iff_isAtom (φ := A q)).1 (hA_irr q)
              let : IsSimpleModule F[H]
                  (((A q).asSubmodule :
                    Submodule F[H] (Representation.asModule ρH))) := hsimpleq
              let : ∀ m : sSet, IsSimpleModule F[H] m := hsimpleSet
              obtain ⟨S, hS, ⟨eS⟩⟩ :=
                Submodule.linearEquiv_of_le_sSup
                  (R := F[H]) (M := Representation.asModule ρH)
                  (N := (A q).asSubmodule) (s := sSet) hleSet
              rcases hS with ⟨r, rfl⟩
              have hqr : q ≠ r := by
                intro hqr'
                apply hq
                simp [hqr']
              have heqA : (A q).toRepresentation ≃ₗ (A r).toRepresentation := by
                refine RepEquiv.mk (eS.restrictScalars F) ?_
                intro h
                apply LinearMap.ext
                intro v
                let v' : ((A q).asSubmodule :
                    Submodule F[H] (Representation.asModule ρH)) := ⟨v.1, v.2⟩
                apply Subtype.ext
                calc
                  ρH.asModuleEquiv ↑(eS (((A q).toRepresentation h) v))
                      = ρH.asModuleEquiv ↑(eS ((MonoidAlgebra.single h (1 : F)) • v')) := by
                          have hv' :
                              (((A q).toRepresentation h) v) =
                                ((MonoidAlgebra.single h (1 : F)) • v' :
                                  ((A q).asSubmodule :
                                    Submodule F[H] (Representation.asModule ρH))) := by
                            have : ((MonoidAlgebra.single h (1 : F)) • v' : ((A q).asSubmodule :
                                    Submodule F[H] (Representation.asModule ρH))) = (A q).toRepresentation h v' := by
                              apply Subtype.ext
                              simp only [SetLike.val_smul, single_smul, one_smul]
                              rfl
                            rw [this]
                            rfl
                          exact congrArg (fun z => ρH.asModuleEquiv ↑(eS z)) hv'
                  _ = ρH.asModuleEquiv ↑(((MonoidAlgebra.single h (1 : F)) • eS v' :
                        ((A r).asSubmodule :
                          Submodule F[H] (Representation.asModule ρH)))) := by
                          exact congrArg (fun z => ρH.asModuleEquiv (Subtype.val z))
                            (eS.map_smul (MonoidAlgebra.single h (1 : F)) v')
                  _ = (ρH h) (ρH.asModuleEquiv ↑(eS v')) := by
                          simp only [SetLike.val_smul, single_smul, one_smul]
                          rfl
                  _ = (ρH h) (ρH.asModuleEquiv ↑(eS v)) := by
                          rfl
              let eqqr :
                  conjugateRep σ (quotientSection (G := G) (H := H) q)⁻¹ ≃ₗ
                    conjugateRep σ (quotientSection (G := G) (H := H) r)⁻¹ :=
                (eA q).trans (heqA.trans (eA r).symm)
              have hneqone :
                  ((((quotientSection (G := G) (H := H) r)⁻¹ *
                      quotientSection (G := G) (H := H) q : G) : G ⧸ H)) ≠ 1 := by
                intro h1
                have hmul :
                    ((quotientSection (G := G) (H := H) r : G) : G ⧸ H)⁻¹ *
                        ((quotientSection (G := G) (H := H) q : G) : G ⧸ H) = 1 := by
                  simpa [div_eq_mul_inv] using h1
                have hEqrq :
                    ((quotientSection (G := G) (H := H) r : G) : G ⧸ H) =
                      ((quotientSection (G := G) (H := H) q : G) : G ⧸ H) := by
                  have hmul' :=
                    congrArg
                      (fun z : G ⧸ H =>
                        ((quotientSection (G := G) (H := H) r : G) : G ⧸ H) * z) hmul
                  simpa [mul_assoc] using hmul'.symm
                apply hqr
                calc
                  q = ((quotientSection (G := G) (H := H) q : G) : G ⧸ H) := by
                    symm
                    exact quotientSection_spec (G := G) (H := H) q
                  _ = ((quotientSection (G := G) (H := H) r : G) : G ⧸ H) := hEqrq.symm
                  _ = r := quotientSection_spec (G := G) (H := H) r
              have hconj : σ ≃ₗ conjugateRep σ
                  ((quotientSection (G := G) (H := H) r)⁻¹ *
                    quotientSection (G := G) (H := H) q) := by
                simpa using (conj_diff_equiv (ρ := σ) (e := eqqr))
              have hall : ∀ y : G, σ ≃ₗ conjugateRep σ y :=
                all_conjugates_of_prime_quotient
                  (ρ := σ) hcardQ hH2 hneqone hconj
              exact False.elim (hxe ⟨hall x⟩)
          rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
            (p := fun q : G ⧸ H => (A q).toSubmodule)]
          intro s
          refine Finset.induction_on s ?_ ?_
          · intro v hv hv0 i hi
            exact False.elim (by simp at hi)
          · intro q s hq ih v hv hv0 i hi
            have hv0_orig := hv0
            have hvq : v q ∈ (A q).toSubmodule := hv q (by simp)
            have hvs : ∀ j ∈ s, v j ∈ (A j).toSubmodule := by
              intro j hj
              exact hv j (by simp [hj])
            have hdisj : Disjoint (A q).toSubmodule (⨆ j ∈ s, (A j).toSubmodule) :=
              hA_disjoint_biSup q s hq
            have hsum_mem : ∑ j ∈ s, v j ∈ ⨆ j ∈ s, (A j).toSubmodule := by
              exact Submodule.sum_mem_biSup hvs
            have hvq_eq : v q = -(∑ j ∈ s, v j) := by
              rw [Finset.sum_insert hq, add_eq_zero_iff_eq_neg] at hv0
              exact hv0
            have hvq_mem : v q ∈ ⨆ j ∈ s, (A j).toSubmodule := by
              rw [hvq_eq]
              exact (⨆ j ∈ s, (A j).toSubmodule).neg_mem hsum_mem
            have hvq_zero : v q = 0 := by
              have hmem : v q ∈ (A q).toSubmodule ⊓ ⨆ j ∈ s, (A j).toSubmodule := by
                exact Submodule.mem_inf.mpr ⟨hvq, hvq_mem⟩
              have : v q ∈ (⊥ : Submodule F W) := by
                simpa [hdisj.eq_bot] using hmem
              simpa using this
            have hv0_sum : ∑ j ∈ s, v j = 0 := by
              rw [Finset.sum_insert hq, hvq_zero, zero_add] at hv0_orig
              exact hv0_orig
            by_cases hiq : i = q
            · simpa [hiq] using hvq_zero
            · have hi_s : i ∈ s := by
                simpa [hiq] using hi
              exact ih v hvs hv0_sum i hi_s
        have hA_internal : DirectSum.IsInternal (fun q : G ⧸ H => (A q).toSubmodule) := by
          refine
            (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
              (R := F) (ι := G ⧸ H) (M := W) (A := fun q : G ⧸ H => (A q).toSubmodule)).2 ?_
          exact ⟨hA_indep, hTsub_top⟩
        let eTop :
            (⨁ q : G ⧸ H, (A q).toSubmodule) ≃ₗ[F] W :=
          LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun q : G ⧸ H => (A q).toSubmodule)) hA_internal
        have hfin :
            Module.finrank F W = Fintype.card (G ⧸ H) * Module.finrank F N.toSubmodule := by
          calc
            Module.finrank F W
                = Module.finrank F (⨁ q : G ⧸ H, (A q).toSubmodule) := by
                    symm
                    exact LinearEquiv.finrank_eq eTop
            _ = Module.finrank F (∀ q : G ⧸ H, (A q).toSubmodule) := by
                    rw [LinearEquiv.finrank_eq
                      (DirectSum.linearEquivFunOnFintype F (G ⧸ H)
                        (fun q : G ⧸ H => (A q).toSubmodule))]
            _ = ∑ q : G ⧸ H, Module.finrank F ((A q).toSubmodule) := by
                    simpa using
                      (Module.finrank_pi_fintype (R := F)
                        (M := fun q : G ⧸ H => (A q).toSubmodule))
            _ = ∑ _q : G ⧸ H, Module.finrank F N.toSubmodule := by
                    refine Finset.sum_congr rfl ?_
                    intro q hq
                    exact hA_dim q
            _ = Fintype.card (G ⧸ H) * Module.finrank F N.toSubmodule := by
                    simp
        have hcardG' : Fintype.card (G ⧸ H) * Nat.card H = Nat.card G := by
          have hQcard : Fintype.card (G ⧸ H) = H.index := by
            simpa using H.index_eq_card.symm
          calc
            Fintype.card (G ⧸ H) * Nat.card H = H.index * Nat.card H := by
              rw [hQcard]
            _ = Nat.card G := by simp [Nat.mul_comm]
        rw [hfin]
        have hfinG :
            Fintype.card (G ⧸ H) * Module.finrank F N.toSubmodule ∣ Nat.card G := by
          rw [← hcardG']
          exact Nat.mul_dvd_mul_left (Fintype.card (G ⧸ H)) hσ_dvd_H
        simpa [hcard] using hfinG

set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.lemma_2_3
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [inst : IsAbsolutelyIrreducible ρ] :
    Module.finrank F V ∣ Nat.card G := by
  let F' := AlgebraicClosure F
  let ρ' := extendScalars F' ρ
  let : IsAbsolutelyIrreducible ρ' := (IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_extendScalars _ _).mpr inst
  have h := lemma_2_3_algClosed ρ'
  rw [Module.finrank_baseChange] at h
  exact h
