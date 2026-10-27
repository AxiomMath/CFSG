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
section Main

/- # General Results on Representations -/

/-
**Kind**: Theorem
**Note**: Proposition 2.1
**Stmt**:
Let $G$ be a group.
Let $F$ be a field.
Let $M$ be an finite dimensional irreducible $FG$-module.
Then
(a) $M$ is absolutely irreducible if and only if $\End_{FG}(M) = F$.
(b) If $G$ is faithful on $M$ and $\End_{FG}(M) = F$, then $\End_{F}(M) = E(G)$.
(c) If $F$ is a finite field and $K = \End_{FG}(M)$, then $K$ is a finite field and we can regard $M$ as an absolutely irreducible $KG$-module.
**Remark** : Faithful condition in (b) is redundant.
  (a) is moved to isAbsolutelyIrreducible_iff_surjective
  (b) is just jacobson_density_surjective_rep.
  (c) is moved to endFieldRep_isAbsolutelyIrreducible
-/

public alias proposition_2_1_a := isAbsolutelyIrreducible_iff_surjective

public alias proposition_2_1_b := jacobson_density_surjective_rep

public alias proposition_2_1_c := endFieldRep_isAbsolutelyIrreducible

/-
**Kind**: Theorem
**Note**: Proposition 2.2
**Stmt**:
Let $G$ be a group.
Let $H \triangleleft G$, and $G/H$ is cyclic.
Let $F$ be an algebraically closed field.
Let $M$ be an finite dimensional irreducible $FH$-module, such that $M \cong M^x$ for all $x \in G$.
Then
(a) If $L$ is an irreducible $FG$-module and $M$ is isomorphic to a submodule of $L_H$, then $L_H \cong M$.
(b) The representation of $H$ on $M$ can be extended to a representation of $G$.
-/

section Proposition2_2

variable {F : Type*} [Field F] [IsAlgClosed F]
variable {G : Type*} [Group G]
variable (H : Subgroup G) [hN : H.Normal] (hcyc : IsCyclic (G ⧸ H))
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
variable (rho : Representation F H V) (E : ∀ x : G, rho ≃ₗ conjugateRep rho x)
variable [IsIrreducible rho]
variable (iota : Representation F G W) [IsIrreducible iota]

abbrev CFSG.proposition_2_2_sigma : Representation F H W := iota.comp H.subtype

def CFSG.proposition_2_2_conjugateMap (x : G) (u : rho →ₗ proposition_2_2_sigma H iota) :
    conjugateRep rho x →ₗ conjugateRep (proposition_2_2_sigma H iota) x := by
  refine RepMap.mk u.toLinearMap ?_
  intro h
  ext v
  have hu :
      u (rho ⟨x * h.val * x⁻¹, Subgroup.Normal.conj_mem hN h h.prop x⟩ v) =
        (proposition_2_2_sigma H iota) ⟨x * h.val * x⁻¹, Subgroup.Normal.conj_mem hN h h.prop x⟩ (u v) :=
    Representation.IntertwiningMap.isIntertwining
      (ρ := rho) (σ := proposition_2_2_sigma H iota) u
      (⟨x * h.val * x⁻¹, Subgroup.Normal.conj_mem hN h h.prop x⟩ : H) v
  convert hu using 1 <;> rfl

omit [IsAlgClosed
  F] [FiniteDimensional F V] [FiniteDimensional F W] [rho.IsIrreducible] [iota.IsIrreducible] in
@[simp]
theorem CFSG.proposition_2_2_conjugateMap_apply (x : G) (u : rho →ₗ proposition_2_2_sigma H iota) (v : V) :
    proposition_2_2_conjugateMap H rho iota x u v = u v := rfl

noncomputable def CFSG.proposition_2_2_restrictionConjEquiv (x : G) :
    conjugateRep (proposition_2_2_sigma H iota) x ≃ₗ proposition_2_2_sigma H iota := by
  refine RepEquiv.mk (LinearEquiv.ofBijective (iota x⁻¹) (Representation.apply_bijective iota x⁻¹)) ?_
  intro h
  ext v
  simp [conjugateRep_apply, mul_assoc]

/-- The restriction of a `G`-representation to a normal subgroup is equivalent to each conjugate. -/
public noncomputable def CFSG.cyclicQuotientRestrictionConjEquiv (x : G) :
    conjugateRep (iota.comp H.subtype) x ≃ₗ iota.comp H.subtype := by
  refine RepEquiv.mk (LinearEquiv.ofBijective (iota x⁻¹) (Representation.apply_bijective iota x⁻¹)) ?_
  intro h
  ext v
  simp [conjugateRep_apply, mul_assoc]

omit [IsAlgClosed F] [FiniteDimensional F W] [iota.IsIrreducible] in
@[simp]
theorem CFSG.proposition_2_2_restrictionConjEquiv_apply (x : G) (w : W) :
    proposition_2_2_restrictionConjEquiv H iota x w = iota x⁻¹ w := rfl

noncomputable def CFSG.proposition_2_2_twistMap (x : G) :
    Module.End F (Theory.Representation.RepMap rho (proposition_2_2_sigma H iota)) := by
  refine
    { toFun := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro u
    exact
      (proposition_2_2_restrictionConjEquiv H iota x).toRepMap.comp
        ((proposition_2_2_conjugateMap H rho iota x u).comp (E x).toRepMap)
  · intro u v
    ext w
    simp [RepMap.comp_apply]
  · intro a u
    ext w
    simp [RepMap.comp_apply]

def CFSG.proposition_2_2_subrepInclusion (phi : Subrepresentation (proposition_2_2_sigma H iota)) :
    phi.toRepresentation →ₗ proposition_2_2_sigma H iota := by
  refine RepMap.mk phi.toSubmodule.subtype ?_
  intro h
  ext v
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The explicit equivalence constructed in Proposition 2.2(a). -/
public noncomputable def CFSG.proposition_2_2_a_apply
    (phi : Subrepresentation (iota.comp H.subtype)) (f : rho ≃ₗ phi.toRepresentation) :
    iota.comp H.subtype ≃ₗ rho := by
  classical
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  let u0 : Theory.Representation.RepMap rho (proposition_2_2_sigma H iota) :=
    (proposition_2_2_subrepInclusion H iota phi).comp f.toRepMap
  have hu0_ne : u0 ≠ 0 := by
    apply RepMap.ne_zero_of_injective
    intro v1 v2 h
    apply f.injective
    apply Subtype.ext
    exact h
  let L := (Representation.linHom rho (proposition_2_2_sigma H iota)).invariants
  let e : L ≃ₗ[F] (rho →ₗ proposition_2_2_sigma H iota) :=
    Representation.invariantsEquivIntertwiningMap (ρ := rho) (σ := proposition_2_2_sigma H iota)
  let u0' : L := e.symm u0
  have hu0'_ne : u0' ≠ 0 := by
    intro hu0'
    apply hu0_ne
    have := congrArg e hu0'
    simpa [u0'] using this
  let : Nontrivial L := ⟨⟨0, u0', hu0'_ne.symm⟩⟩
  let q : G ⧸ H := Classical.choose (IsCyclic.exists_generator (α := G ⧸ H))
  have hq : ∀ y : G ⧸ H, y ∈ Subgroup.zpowers q :=
    Classical.choose_spec (IsCyclic.exists_generator (α := G ⧸ H))
  let x : G := Classical.choose (QuotientGroup.mk_surjective q)
  have hxq : (x : G ⧸ H) = q := Classical.choose_spec (QuotientGroup.mk_surjective q)
  let Tsub : Module.End F L := by
    refine {
      toFun := fun u => e.symm (proposition_2_2_twistMap H rho E iota x (e u))
      map_add' := ?_
      map_smul' := ?_ }
    · intro u v
      apply e.injective
      simp
    · intro a u
      apply e.injective
      simp
  let mu : F := Classical.choose (Module.End.exists_eigenvalue Tsub)
  have hmu : Tsub.HasEigenvalue mu := Classical.choose_spec (Module.End.exists_eigenvalue Tsub)
  let u' : L := Classical.choose (hmu.exists_hasEigenvector)
  have hu' : Tsub.HasEigenvector mu u' := Classical.choose_spec (hmu.exists_hasEigenvector)
  let u : rho →ₗ proposition_2_2_sigma H iota := e u'
  have hu_ne : u ≠ 0 := by
    intro hu0
    apply hu'.2
    have := congrArg e.symm hu0
    simpa [u] using this
  have hu : proposition_2_2_twistMap H rho E iota x u = mu • u := by
    have h := congrArg e hu'.apply_eq_smul
    simpa [Tsub, u] using h
  have hTinj : Function.Injective (proposition_2_2_twistMap H rho E iota x) := by
    intro u1 u2 hEq
    ext v
    have hEq' := congrArg (fun f : rho →ₗ proposition_2_2_sigma H iota => f ((E x).symm v)) hEq
    have hEq'' : iota x⁻¹ (u1 v) = iota x⁻¹ (u2 v) := by
      simpa [proposition_2_2_twistMap, proposition_2_2_conjugateMap_apply] using hEq'
    exact (Representation.apply_bijective iota x⁻¹).1 hEq''
  have hmu_ne : mu ≠ 0 := by
    intro hmu0
    apply hu_ne
    apply hTinj
    simp [hu, hmu0]
  have hxinv_mem_range (v : V) : iota x⁻¹ (u v) ∈ u.range.toSubmodule := by
    refine LinearMap.mem_range.mpr ?_
    refine ⟨mu • (E x).symm v, ?_⟩
    calc
      u (mu • (E x).symm v) = mu • u ((E x).symm v) := RepMap.map_smul u _ _
      _ = (mu • u) ((E x).symm v) :=
        (RepMap.smul_apply rho (proposition_2_2_sigma H iota) mu u _).symm
      _ = proposition_2_2_twistMap H rho E iota x u ((E x).symm v) := by rw [hu]
      _ = iota x⁻¹ (u v) := by
        simp [proposition_2_2_twistMap, proposition_2_2_conjugateMap_apply]
  have hx_mem_range (v : V) : iota x (u v) ∈ u.range.toSubmodule := by
    refine LinearMap.mem_range.mpr ?_
    refine ⟨mu⁻¹ • E x v, ?_⟩
    have h := congrArg (fun f : rho →ₗ proposition_2_2_sigma H iota => f v) hu
    have h' : u (E x v) = mu • iota x (u v) := by
      have h0 : (proposition_2_2_restrictionConjEquiv H iota x) (u (E x v)) = mu • u v := by
        simpa [proposition_2_2_twistMap, proposition_2_2_conjugateMap_apply] using h
      have := congrArg (iota x) h0
      simpa [proposition_2_2_restrictionConjEquiv_apply, mul_assoc] using this
    calc
      u (mu⁻¹ • E x v) = mu⁻¹ • u (E x v) := by simp
      _ = mu⁻¹ • (mu • iota x (u v)) := by rw [h']
      _ = iota x (u v) := by rw [smul_smul, inv_mul_cancel₀ hmu_ne, one_smul]
  let S : Submodule F W := u.range.toSubmodule
  have hx_mem (w : W) (hw : w ∈ S) : iota x w ∈ S := by
    rcases LinearMap.mem_range.mp hw with ⟨v, rfl⟩
    exact hx_mem_range v
  have hxinv_mem (w : W) (hw : w ∈ S) : iota x⁻¹ w ∈ S := by
    rcases LinearMap.mem_range.mp hw with ⟨v, rfl⟩
    exact hxinv_mem_range v
  have hxpow_mem : ∀ n : ℤ, ∀ w ∈ S, iota (x ^ n) w ∈ S := by
    intro n
    let P : G → Prop := fun a => ∀ w ∈ S, iota a w ∈ S
    change P (x ^ n)
    refine zpow_induction_right (g := x) (P := P) ?_ ?_ ?_ n
    · intro w hw
      simpa using hw
    · intro a ha w hw
      have hxw : iota x w ∈ S := hx_mem w hw
      simpa [map_mul] using ha (iota x w) hxw
    · intro a ha w hw
      have hxw : iota x⁻¹ w ∈ S := hxinv_mem w hw
      simpa [map_mul] using ha (iota x⁻¹ w) hxw
  have hGstable : ∀ g : G, ∀ w ∈ S, iota g w ∈ S := by
    intro g w hw
    rcases Subgroup.mem_zpowers_iff.mp (hq (g : G ⧸ H)) with ⟨n, hn⟩
    have hgxn : (g : G ⧸ H) = (x ^ n : G) := by
      simpa [hxq] using hn.symm
    have hdiv : g / x ^ n ∈ H := (QuotientGroup.eq_iff_div_mem).mp hgxn
    let h' : H := ⟨g / x ^ n, hdiv⟩
    have hxnw : iota (x ^ n) w ∈ S := hxpow_mem n w hw
    have hhxw : (proposition_2_2_sigma H iota) h' (iota (x ^ n) w) ∈ S :=
      u.range.apply_mem_toSubmodule h' hxnw
    have hgdecomp : (h' : G) * x ^ n = g := by
      dsimp [h']
      simp [div_eq_mul_inv, mul_assoc]
    rw [← hgdecomp, map_mul]
    simpa using hhxw
  let psi : Subrepresentation iota := {
    toSubmodule := S
    apply_mem_toSubmodule := hGstable
  }
  have hpsi_ne : psi ≠ ⊥ := by
    intro hpsi
    have hSbot : S = ⊥ := by
      calc
        S = psi.toSubmodule := rfl
        _ = (⊥ : Subrepresentation iota).toSubmodule :=
          congrArg Subrepresentation.toSubmodule hpsi
        _ = (⊥ : Submodule F W) := rfl
    apply hu_ne
    apply Theory.Representation.RepMap.toLinearMap_injective
    exact LinearMap.range_eq_bot.mp hSbot
  have hpsi_top : psi = ⊤ := by
    rcases (inferInstance : IsIrreducible iota).eq_bot_or_eq_top psi with hbot | htop
    · exact False.elim (hpsi_ne hbot)
    · exact htop
  have hsurj : Function.Surjective u := by
    have hS_top : S = ⊤ := by
      calc
        S = psi.toSubmodule := rfl
        _ = (⊤ : Subrepresentation iota).toSubmodule :=
          congrArg Subrepresentation.toSubmodule hpsi_top
        _ = (⊤ : Submodule F W) := rfl
    exact LinearMap.range_eq_top.mp hS_top
  have hinj : Function.Injective u := by
    rcases (Representation.IsIrreducible.injective_or_eq_zero (ρ := rho) (σ := proposition_2_2_sigma H iota) (f := u)) with huinj | hu0
    · exact huinj
    · exact False.elim (hu_ne hu0)
  let eu : rho ≃ₗ proposition_2_2_sigma H iota :=
    RepEquiv.mk (LinearEquiv.ofBijective u.toLinearMap ⟨hinj, hsurj⟩) (by
      intro h
      ext v
      simpa using (Representation.IntertwiningMap.isIntertwining (ρ := rho) (σ := proposition_2_2_sigma H iota) u h v))
  exact eu.symm

end Proposition2_2

/-- Proposition 2.2(a): an irreducible constituent of the restriction is equivalent to `ρ`. -/
public noncomputable def CFSG.proposition_2_2_a
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G]
    (H : Subgroup G) [hN : H.Normal] (hcyc : IsCyclic (G ⧸ H))
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F H V) (E : ∀ x : G, ρ ≃ₗ conjugateRep ρ x) [IsIrreducible ρ]
    (ι : Representation F G W) [IsIrreducible ι]
    (φ : Subrepresentation (ι.comp H.subtype))
    (f : ρ ≃ₗ φ.toRepresentation) :
    ι.comp H.subtype ≃ₗ ρ :=
  proposition_2_2_a_apply H hcyc ρ E ι φ f


section Proposition22bFunctionSpace

variable {F : Type*} [Field F]
variable {G : Type*} [Group G]
variable {H : Subgroup G} [H.Normal]
variable {V : Type*} [AddCommGroup V] [Module F V]

def CFSG.p22b_subrepInclusion {ρ : Representation F H V} (S : Subrepresentation ρ) :
    S.toRepresentation →ₗ ρ := by
  refine RepMap.mk S.toSubmodule.subtype ?_
  intro h
  ext v
  rfl

omit [H.Normal] in
theorem CFSG.p22b_repMapRangeNeBotOfNeZero
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

omit [H.Normal] in
theorem CFSG.p22b_repMapRangeEqTopOfNeZero
    {V₁ : Type*} [AddCommGroup V₁] [Module F V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module F V₂]
    {ρ₁ : Representation F H V₁} {ρ₂ : Representation F H V₂}
    [Representation.IsIrreducible ρ₂] (f : ρ₁ →ₗ ρ₂) (hf : f ≠ 0) :
    f.range = ⊤ := by
  rcases (inferInstance : Representation.IsIrreducible ρ₂).eq_bot_or_eq_top f.range with
    hbot | htop
  · exact False.elim (p22b_repMapRangeNeBotOfNeZero f hf hbot)
  · exact htop

set_option backward.isDefEq.respectTransparency false in
noncomputable def CFSG.p22b_repEquivOfNeZero
    {V₁ : Type*} [AddCommGroup V₁] [Module F V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module F V₂]
    {ρ₁ : Representation F H V₁} {ρ₂ : Representation F H V₂}
    [Representation.IsIrreducible ρ₁] [Representation.IsIrreducible ρ₂]
    (f : ρ₁ →ₗ ρ₂) (hf : f ≠ 0) :
    ρ₁ ≃ₗ ρ₂ := by
  have hfinj : Function.Injective f := by
    rcases (Representation.IsIrreducible.injective_or_eq_zero
      (ρ := ρ₁) (σ := ρ₂) (f := f)) with hfinj | hf0
    · exact hfinj
    · exact False.elim (hf hf0)
  have hfsurj : Function.Surjective f := by
    exact LinearMap.range_eq_top.mp (by
      calc
        f.toLinearMap.range = f.range.toSubmodule := rfl
        _ = (⊤ : Subrepresentation ρ₂).toSubmodule :=
          congrArg Subrepresentation.toSubmodule
            (p22b_repMapRangeEqTopOfNeZero f hf)
        _ = (⊤ : Submodule F V₂) := rfl)
  refine RepEquiv.mk (LinearEquiv.ofBijective f.toLinearMap ⟨hfinj, hfsurj⟩) ?_
  intro h
  ext v
  simpa using (Representation.IntertwiningMap.isIntertwining (ρ := ρ₁) (σ := ρ₂) f h v)

def CFSG.p22b_funSubmodule (ρ : Representation F H V) : Submodule F (G → V) where
  carrier := {f | ∀ h : H, ∀ x : G, f ((h : G) * x) = ρ h (f x)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg h x
    simp [hf h x, hg h x]
  smul_mem' := by
    intro a f hf h x
    simp [hf h x]

abbrev CFSG.p22b_funSpace (ρ : Representation F H V) := ↥(p22b_funSubmodule (G := G) (H := H) ρ)

instance (ρ : Representation F H V) : CoeFun (p22b_funSpace (G := G) (H := H) ρ) (fun _ => G → V) :=
  ⟨fun f => f.1⟩

def CFSG.p22b_funRep (ρ : Representation F H V) :
    Representation F G (p22b_funSpace (G := G) (H := H) ρ) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f (x * g), by
          intro h x
          simpa [mul_assoc] using f.2 h (x * g)⟩
      map_add' := by
        intro f₁ f₂
        ext x
        rfl
      map_smul' := by
        intro a f
        ext x
        rfl }
  map_one' := by
    ext f x
    simp
  map_mul' g₁ g₂ := by
    ext f x
    simp [mul_assoc]

omit [H.Normal] in
@[simp] theorem CFSG.p22b_funRep_apply (ρ : Representation F H V) (g : G)
    (f : p22b_funSpace (G := G) (H := H) ρ) (x : G) :
    p22b_funRep (G := G) (H := H) ρ g f x = f (x * g) := rfl

def CFSG.p22b_funCosetSubrep (ρ : Representation F H V) (q : G ⧸ H) :
    Subrepresentation ((p22b_funRep (G := G) (H := H) ρ).comp H.subtype) where
  toSubmodule := {
    carrier := {f | ∀ g : G, ((g : G ⧸ H) ≠ q) → f g = 0}
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
    change f (g * h) = 0
    apply hf
    intro hq
    have hh : ((h : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff (h : G)).2 h.prop
    apply hg
    change ((g : G ⧸ H) * ((h : G) : G ⧸ H) = q) at hq
    rw [hh, mul_one] at hq
    exact hq

def CFSG.p22b_funEval (ρ : Representation F H V) (g : G) :
    ((p22b_funRep (G := G) (H := H) ρ).comp H.subtype) →ₗ conjugateRep ρ g := by
  refine RepMap.mk ?_ ?_
  · refine
      { toFun := fun f => f g
        map_add' := by intro f₁ f₂; rfl
        map_smul' := by intro a f; rfl }
  · intro h
    ext f
    change f (g * h.val) =
      ρ ⟨(g : G) * h.val * (g : G)⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop (g : G)⟩ (f g)
    simpa [Theory.Representation.conjugateRep_apply, mul_assoc] using
      f.2
        ⟨(g : G) * h.val * (g : G)⁻¹,
          Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop (g : G)⟩
        (g : G)

noncomputable def CFSG.p22b_funBaseFunctionAt (ρ : Representation F H V) (g : G) (v : V) :
    p22b_funSpace (G := G) (H := H) ρ := by
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

@[simp] theorem CFSG.p22b_funEval_base (ρ : Representation F H V) (g : G) (v : V) :
    p22b_funEval (G := G) (H := H) ρ g
      (p22b_funBaseFunctionAt (G := G) (H := H) ρ g v) = v := by
  classical
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

theorem CFSG.p22b_funBaseFunctionAt_mem_coset (ρ : Representation F H V) (g : G) (v : V) :
    p22b_funBaseFunctionAt (G := G) (H := H) ρ g v ∈
      (p22b_funCosetSubrep (G := G) (H := H) ρ (g : G ⧸ H)).toSubmodule := by
  classical
  intro x hx
  change (if hx' : x * g⁻¹ ∈ H then ρ ⟨x * g⁻¹, hx'⟩ v else 0) = 0
  rw [dif_neg]
  intro hmem
  apply hx
  exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hmem)

@[simp] theorem CFSG.p22b_funEval_of_ne_coset
    (ρ : Representation F H V) {g x : G} (hx : (x : G ⧸ H) ≠ (g : G ⧸ H)) (v : V) :
    p22b_funEval (G := G) (H := H) ρ x
      (p22b_funBaseFunctionAt (G := G) (H := H) ρ g v) = 0 := by
  classical
  change (if hx' : x * g⁻¹ ∈ H then ρ ⟨x * g⁻¹, hx'⟩ v else 0) = 0
  rw [dif_neg]
  intro hmem
  apply hx
  exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hmem)

set_option backward.isDefEq.respectTransparency false in
noncomputable def CFSG.p22b_funCosetEquiv (ρ : Representation F H V) (g : G) :
    (p22b_funCosetSubrep (G := G) (H := H) ρ (g : G ⧸ H)).toRepresentation ≃ₗ conjugateRep ρ g := by
  let S := p22b_funCosetSubrep (G := G) (H := H) ρ (g : G ⧸ H)
  let evLin :
      S.toSubmodule →ₗ[F] V :=
    (p22b_funEval (G := G) (H := H) ρ g).toLinearMap.comp S.toSubmodule.subtype
  let ev : S.toRepresentation →ₗ conjugateRep ρ g := by
    refine RepMap.mk evLin ?_
    intro h
    ext f
    change f.1.1 (g * h.val) =
      ρ ⟨g * h.val * g⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⟩ (f.1.1 g)
    simpa [mul_assoc] using
      f.1.2
        ⟨g * h.val * g⁻¹,
          Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⟩
        g
  refine RepEquiv.mk (LinearEquiv.ofBijective ev.toLinearMap ⟨?_, ?_⟩) ?_
  · intro f₁ f₂ hfg
    ext x
    by_cases hx : (x : G ⧸ H) = (g : G ⧸ H)
    · have hmem : x * g⁻¹ ∈ H := by
        simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).mp hx
      have hf₁ :
          f₁.1.1 x = ρ ⟨x * g⁻¹, hmem⟩ (f₁.1.1 g) := by
        simpa [p22b_funEval, hmem, div_eq_mul_inv, mul_assoc] using
          f₁.1.2 ⟨x * g⁻¹, hmem⟩ (g : G)
      have hf₂ :
          f₂.1.1 x = ρ ⟨x * g⁻¹, hmem⟩ (f₂.1.1 g) := by
        simpa [p22b_funEval, hmem, div_eq_mul_inv, mul_assoc] using
          f₂.1.2 ⟨x * g⁻¹, hmem⟩ (g : G)
      have hg : f₁.1.1 g = f₂.1.1 g := by
        simpa [ev, evLin, p22b_funEval] using hfg
      rw [hf₁, hf₂, hg]
    · have hf₁x : f₁.1.1 x = 0 := f₁.2 x hx
      have hf₂x : f₂.1.1 x = 0 := f₂.2 x hx
      rw [hf₁x, hf₂x]
  · intro v
    refine
      ⟨⟨p22b_funBaseFunctionAt (G := G) (H := H) ρ g v,
        p22b_funBaseFunctionAt_mem_coset (G := G) (H := H) ρ g v⟩, ?_⟩
    change p22b_funEval (G := G) (H := H) ρ g
        (p22b_funBaseFunctionAt (G := G) (H := H) ρ g v) = v
    simp
  · intro h
    ext f
    simpa using
      (Representation.IntertwiningMap.isIntertwining
        (ρ := S.toRepresentation) (σ := conjugateRep ρ g) ev h f)

noncomputable def CFSG.p22b_funQuotientSection [Fintype (G ⧸ H)] (q : G ⧸ H) : G :=
  Classical.choose (QuotientGroup.mk_surjective q)

omit [H.Normal] in
theorem CFSG.p22b_funQuotientSection_spec [Fintype (G ⧸ H)] (q : G ⧸ H) :
    ((p22b_funQuotientSection (G := G) (H := H) q : G) : G ⧸ H) = q :=
  Classical.choose_spec (QuotientGroup.mk_surjective q)

theorem CFSG.p22b_funSumSections [Fintype (G ⧸ H)] (ρ : Representation F H V)
    (f : p22b_funSpace (G := G) (H := H) ρ) :
    (∑ q : G ⧸ H,
      p22b_funBaseFunctionAt (G := G) (H := H) ρ
        (p22b_funQuotientSection (G := G) (H := H) q)
        (p22b_funEval (G := G) (H := H) ρ
          (p22b_funQuotientSection (G := G) (H := H) q) f)) = f := by
  classical
  ext x
  let qx : G ⧸ H := x
  have hmain :
      (p22b_funBaseFunctionAt (G := G) (H := H) ρ
        (p22b_funQuotientSection (G := G) (H := H) qx)
        (p22b_funEval (G := G) (H := H) ρ
          (p22b_funQuotientSection (G := G) (H := H) qx) f)) x = f x := by
    let sx : G := p22b_funQuotientSection (G := G) (H := H) qx
    have hxq :
        (x : G ⧸ H) = (sx : G ⧸ H) := by
      simpa [qx] using (p22b_funQuotientSection_spec (G := G) (H := H) qx).symm
    have hxmem : x * sx⁻¹ ∈ H := by
      simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).1 hxq
    have hmap :
        ρ ⟨x * sx⁻¹, hxmem⟩ (f sx) = f x := by
      simpa [sx, mul_assoc] using (f.2 ⟨x * sx⁻¹, hxmem⟩ sx).symm
    simpa [p22b_funBaseFunctionAt, p22b_funEval, sx, hxmem] using hmap
  calc
    (∑ q : G ⧸ H,
        p22b_funBaseFunctionAt (G := G) (H := H) ρ
          (p22b_funQuotientSection (G := G) (H := H) q)
          (p22b_funEval (G := G) (H := H) ρ
            (p22b_funQuotientSection (G := G) (H := H) q) f)) x
      =
        ∑ q : G ⧸ H,
          p22b_funEval (G := G) (H := H) ρ x
            (p22b_funBaseFunctionAt (G := G) (H := H) ρ
              (p22b_funQuotientSection (G := G) (H := H) q)
              (p22b_funEval (G := G) (H := H) ρ
                (p22b_funQuotientSection (G := G) (H := H) q) f)) := by
          change (p22b_funEval (G := G) (H := H) ρ x).toLinearMap
              (∑ q : G ⧸ H,
                p22b_funBaseFunctionAt (G := G) (H := H) ρ
                  (p22b_funQuotientSection (G := G) (H := H) q)
                  (p22b_funEval (G := G) (H := H) ρ
                    (p22b_funQuotientSection (G := G) (H := H) q) f)) =
            ∑ q : G ⧸ H,
              (p22b_funEval (G := G) (H := H) ρ x).toLinearMap
                (p22b_funBaseFunctionAt (G := G) (H := H) ρ
                  (p22b_funQuotientSection (G := G) (H := H) q)
                  (p22b_funEval (G := G) (H := H) ρ
                    (p22b_funQuotientSection (G := G) (H := H) q) f))
          simp
    _ = f x := by
      rw [Finset.sum_eq_single qx]
      · exact hmain
      · intro q _ hq
        have hneq :
            ((p22b_funQuotientSection (G := G) (H := H) q : G) : G ⧸ H) ≠ (x : G ⧸ H) := by
          simpa [p22b_funQuotientSection_spec (G := G) (H := H) q, qx] using hq
        have hneq' :
            (x : G ⧸ H) ≠ ((p22b_funQuotientSection (G := G) (H := H) q : G) : G ⧸ H) := by
          simpa [ne_comm] using hneq
        simpa using
          (p22b_funEval_of_ne_coset (G := G) (H := H) ρ
            (x := x)
            (g := p22b_funQuotientSection (G := G) (H := H) q)
            hneq'
            (p22b_funEval (G := G) (H := H) ρ
              (p22b_funQuotientSection (G := G) (H := H) q) f))
      · intro hq
        exact False.elim (hq (Finset.mem_univ qx))

noncomputable def CFSG.p22b_funPiEquiv [Fintype (G ⧸ H)] (ρ : Representation F H V) :
    p22b_funSpace (G := G) (H := H) ρ ≃ₗ[F] (G ⧸ H → V) where
  toFun f q := p22b_funEval (G := G) (H := H) ρ
    (p22b_funQuotientSection (G := G) (H := H) q) f
  invFun ψ := ∑ q : G ⧸ H,
    p22b_funBaseFunctionAt (G := G) (H := H) ρ
      (p22b_funQuotientSection (G := G) (H := H) q) (ψ q)
  left_inv := p22b_funSumSections (G := G) (H := H) ρ
  right_inv := by
    intro ψ
    ext q
    let g : G := p22b_funQuotientSection (G := G) (H := H) q
    have hg : (g : G ⧸ H) = q := p22b_funQuotientSection_spec (G := G) (H := H) q
    calc
      p22b_funEval (G := G) (H := H) ρ g
          (∑ q' : G ⧸ H,
            p22b_funBaseFunctionAt (G := G) (H := H) ρ
              (p22b_funQuotientSection (G := G) (H := H) q') (ψ q'))
          = ∑ q' : G ⧸ H,
              p22b_funEval (G := G) (H := H) ρ g
                (p22b_funBaseFunctionAt (G := G) (H := H) ρ
                  (p22b_funQuotientSection (G := G) (H := H) q') (ψ q')) := by
            change (p22b_funEval (G := G) (H := H) ρ g).toLinearMap
                (∑ q' : G ⧸ H,
                  p22b_funBaseFunctionAt (G := G) (H := H) ρ
                    (p22b_funQuotientSection (G := G) (H := H) q') (ψ q')) =
              ∑ q' : G ⧸ H,
                (p22b_funEval (G := G) (H := H) ρ g).toLinearMap
                  (p22b_funBaseFunctionAt (G := G) (H := H) ρ
                    (p22b_funQuotientSection (G := G) (H := H) q') (ψ q'))
            simp
      _ = ψ q := by
        classical
        rw [Finset.sum_eq_single q]
        · simp [g]
        · intro q' _ hq'
          have hqg :
              ((p22b_funQuotientSection (G := G) (H := H) q' : G) : G ⧸ H) ≠ (g : G ⧸ H) := by
            simpa [p22b_funQuotientSection_spec (G := G) (H := H) q', hg] using hq'
          have hqg' :
              (g : G ⧸ H) ≠ ((p22b_funQuotientSection (G := G) (H := H) q' : G) : G ⧸ H) := by
            simpa [ne_comm] using hqg
          simpa [g] using
            (p22b_funEval_of_ne_coset (G := G) (H := H) ρ
              (x := g)
              (g := p22b_funQuotientSection (G := G) (H := H) q')
              hqg' (ψ q'))
        · intro hq'
          exact False.elim (hq' (Finset.mem_univ q))
  map_add' f₁ f₂ := by
    ext q
    simp
  map_smul' a f := by
    ext q
    simp

set_option backward.isDefEq.respectTransparency false in
noncomputable def CFSG.p22b_funProj (ρ : Representation F H V) (q : G ⧸ H) :
    ((p22b_funRep (G := G) (H := H) ρ).comp H.subtype) →ₗ
      ((p22b_funRep (G := G) (H := H) ρ).comp H.subtype) := by
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
      ∀ f ∈ p22b_funSubmodule (G := G) (H := H) ρ, proj f ∈ p22b_funSubmodule (G := G) (H := H) ρ := by
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
      simp [p22b_funRep_apply, LinearMap.restrict_apply, proj, hx]
    · have hhx : ((x * (h : G) : G) : G ⧸ H) ≠ q := by
        intro hhx
        apply hx
        have hh : ((h : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff (h : G)).2 h.prop
        change ((x : G ⧸ H) * (h : G ⧸ H)) = q at hhx
        rwa [hh, mul_one] at hhx
      simp [p22b_funRep_apply, LinearMap.restrict_apply, proj, hx]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem CFSG.p22b_funProj_apply (ρ : Representation F H V) [DecidableEq (G ⧸ H)] (q : G ⧸ H)
    (f : p22b_funSpace (G := G) (H := H) ρ) (x : G) :
    (p22b_funProj (G := G) (H := H) ρ q f) x = if (x : G ⧸ H) = q then f x else 0 := by
  classical
  simp [p22b_funProj, LinearMap.restrict_apply]

theorem CFSG.p22b_funProj_mem_coset (ρ : Representation F H V) (q : G ⧸ H)
    (f : p22b_funSpace (G := G) (H := H) ρ) :
    p22b_funProj (G := G) (H := H) ρ q f ∈
      (p22b_funCosetSubrep (G := G) (H := H) ρ q).toSubmodule := by
  classical
  intro x hx
  rw [p22b_funProj_apply]
  simp [hx]

noncomputable def CFSG.p22b_funProjToCoset (ρ : Representation F H V) (q : G ⧸ H) :
    ((p22b_funRep (G := G) (H := H) ρ).comp H.subtype) →ₗ
      (p22b_funCosetSubrep (G := G) (H := H) ρ q).toRepresentation := by
  classical
  refine RepMap.mk ?_ ?_
  · refine
      { toFun := fun f => ⟨p22b_funProj (G := G) (H := H) ρ q f,
          p22b_funProj_mem_coset (G := G) (H := H) ρ q f⟩
        map_add' := by
          intro f g
          ext x
          simp [p22b_funProj_apply]
        map_smul' := by
          intro a f
          ext x
          simp [p22b_funProj_apply] }
  · intro h
    ext f x
    change (p22b_funProj (G := G) (H := H) ρ q
        (((p22b_funRep (G := G) (H := H) ρ).comp H.subtype) h f)) x =
      (((p22b_funRep (G := G) (H := H) ρ).comp H.subtype) h
        (p22b_funProj (G := G) (H := H) ρ q f)) x
    have hcomm :=
      Representation.IntertwiningMap.isIntertwining
        (ρ := ((p22b_funRep (G := G) (H := H) ρ).comp H.subtype))
        (σ := ((p22b_funRep (G := G) (H := H) ρ).comp H.subtype))
        (p22b_funProj (G := G) (H := H) ρ q) h f
    simp

theorem CFSG.p22b_conjugateRep_irreducible
    (ρ : Representation F H V) (g : G) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (conjugateRep ρ g) := by
  let e : H ≃* H := {
    toFun := fun h => ⟨g⁻¹ * (h : G) * g, by
      simpa using Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⁻¹⟩
    invFun := fun h => ⟨g * (h : G) * g⁻¹, by
      simpa using Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⟩
    left_inv := by
      intro a
      apply Subtype.ext
      simp [mul_assoc]
    right_inv := by
      intro a
      apply Subtype.ext
      simp [mul_assoc]
    map_mul' := by
      intro a b
      apply Subtype.ext
      simp [mul_assoc] }
  exact
    RepEquiv.irreducible_of_group_iso
      (ρ := ρ) (σ := conjugateRep ρ g) e
      (by
        intro h v
        simp [e, Theory.Representation.conjugateRep_apply, mul_assoc])
      inferInstance

theorem CFSG.p22b_funCosetSubrep_irreducible
    (ρ : Representation F H V) [Representation.IsIrreducible ρ] (q : G ⧸ H) :
    @Representation.IsIrreducible H F
      ((p22b_funCosetSubrep (G := G) (H := H) ρ q).toSubmodule)
      inferInstance inferInstance inferInstance inferInstance
      ((p22b_funCosetSubrep (G := G) (H := H) ρ q).toRepresentation) := by
  let g : G := Classical.choose (QuotientGroup.mk_surjective q)
  have hg : (g : G ⧸ H) = q := Classical.choose_spec (QuotientGroup.mk_surjective q)
  let e :
      (p22b_funCosetSubrep (G := G) (H := H) ρ (g : G ⧸ H)).toRepresentation ≃ₗ
        conjugateRep ρ g :=
    p22b_funCosetEquiv (G := G) (H := H) ρ g
  have hIrr :
      @Representation.IsIrreducible H F
        ((p22b_funCosetSubrep (G := G) (H := H) ρ (g : G ⧸ H)).toSubmodule)
        inferInstance inferInstance inferInstance inferInstance
        ((p22b_funCosetSubrep (G := G) (H := H) ρ (g : G ⧸ H)).toRepresentation) := by
    let : Representation.IsIrreducible (ρ := conjugateRep (ρ := ρ) g) :=
      p22b_conjugateRep_irreducible (G := G) (H := H) ρ g
    exact (RepEquiv.irreducible_euqiv e).2 inferInstance
  rw [← hg]
  exact hIrr

end Proposition22bFunctionSpace

public theorem CFSG.proposition_2_2_b
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G]
    (H : Subgroup G) [hN : H.Normal] (hcyc : IsCyclic (G ⧸ H)) [Finite (G ⧸ H)]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F H V) [IsIrreducible ρ]
    (E : ∀ x : G, ρ ≃ₗ conjugateRep ρ x) :
    ∃ (σ : Representation F G V), σ.comp H.subtype = ρ := by
  let _ := (inferInstance : FiniteDimensional F W)
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let M := p22b_funSpace (G := G) (H := H) ρ
  let σM : Representation F G M := p22b_funRep (G := G) (H := H) ρ
  let : FiniteDimensional F M :=
    (p22b_funPiEquiv (G := G) (H := H) ρ).symm.finiteDimensional
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨v0, hv0_ne⟩ := exists_ne (0 : V)
  let f0 : M := p22b_funBaseFunctionAt (G := G) (H := H) ρ (1 : G) v0
  have hf0_ne : f0 ≠ 0 := by
    intro hf0
    apply hv0_ne
    have h0 := congrArg (p22b_funEval (G := G) (H := H) ρ (1 : G)) hf0
    simpa [f0] using h0
  let : Nontrivial M := ⟨f0, 0, hf0_ne⟩
  obtain ⟨L, hLirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional σM
  let := hLirr
  let σLH : Representation F H L.toSubmodule := L.toRepresentation.comp H.subtype
  let : Nontrivial L.toSubmodule := Subrepresentation.irreducible_module_nontrivial L.toRepresentation
  obtain ⟨N, hNirr⟩ :=
    @Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
      F H L.toSubmodule inferInstance inferInstance inferInstance inferInstance inferInstance
      σLH inferInstance
  let := hNirr
  let iL : σLH →ₗ (σM.comp H.subtype) := by
    refine RepMap.mk L.toSubmodule.subtype ?_
    intro h
    ext v
    rfl
  let iN : N.toRepresentation →ₗ σLH := p22b_subrepInclusion (G := G) (H := H) N
  let iN0 : N.toRepresentation →ₗ (σM.comp H.subtype) := iL.comp iN
  have hiN0_inj : Function.Injective iN0 := by
    intro a b hab
    simpa [iN0, iL, iN, p22b_subrepInclusion] using hab
  let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
  obtain ⟨n0, hn0_ne⟩ := exists_ne (0 : N.toSubmodule)
  have hiN0n0_ne : iN0 n0 ≠ 0 := by
    intro h0
    apply hn0_ne
    exact hiN0_inj h0
  obtain ⟨x, hx_ne⟩ : ∃ x : G, iN0 n0 x ≠ 0 := by
    by_contra hnone
    apply hiN0n0_ne
    ext y
    by_cases hy : iN0 n0 y = 0
    · exact hy
    · exact False.elim (hnone ⟨y, hy⟩)
  let q : G ⧸ H := x
  let Pq : N.toRepresentation →ₗ (p22b_funCosetSubrep (G := G) (H := H) ρ q).toRepresentation :=
    (p22b_funProjToCoset (G := G) (H := H) ρ q).comp iN0
  have hPq_ne : Pq ≠ 0 := by
    intro hP0
    apply hx_ne
    have h0 := congrArg (fun f => (((f n0).1 : p22b_funSpace (G := G) (H := H) ρ) x)) hP0
    simpa [Pq, q, p22b_funProjToCoset, p22b_funProj_apply] using h0
  let :
      @Representation.IsIrreducible H F
        ((p22b_funCosetSubrep (G := G) (H := H) ρ q).toSubmodule)
        inferInstance inferInstance inferInstance inferInstance
        ((p22b_funCosetSubrep (G := G) (H := H) ρ q).toRepresentation) :=
    p22b_funCosetSubrep_irreducible (G := G) (H := H) ρ q
  let eNq : N.toRepresentation ≃ₗ (p22b_funCosetSubrep (G := G) (H := H) ρ q).toRepresentation :=
    p22b_repEquivOfNeZero
      (G := G) (H := H)
      (V₁ := N.toSubmodule)
      (V₂ := (p22b_funCosetSubrep (G := G) (H := H) ρ q).toSubmodule)
      (ρ₁ := N.toRepresentation)
      (ρ₂ := (p22b_funCosetSubrep (G := G) (H := H) ρ q).toRepresentation)
      Pq hPq_ne
  have eρq :
      ρ ≃ₗ (p22b_funCosetSubrep (G := G) (H := H) ρ q).toRepresentation := by
    let g : G := p22b_funQuotientSection (G := G) (H := H) q
    have hg : (g : G ⧸ H) = q := p22b_funQuotientSection_spec (G := G) (H := H) q
    have htmp :
        ρ ≃ₗ (p22b_funCosetSubrep (G := G) (H := H) ρ (g : G ⧸ H)).toRepresentation :=
      (E g).trans (p22b_funCosetEquiv (G := G) (H := H) ρ g).symm
    rw [hg] at htmp
    exact htmp
  let fN : ρ ≃ₗ N.toRepresentation := eρq.trans eNq.symm
  let eL : L.toRepresentation.comp H.subtype ≃ₗ ρ :=
    proposition_2_2_a
      (G := G) (H := H) (W := L.toSubmodule) hcyc ρ E
      (ι := L.toRepresentation)
      (φ := N)
      fN
  let eV : L.toSubmodule ≃ₗ[F] V := eL.toLinearEquiv
  refine ⟨
    { toFun := fun g =>
        eV.toLinearMap.comp ((L.toRepresentation g).comp eV.symm.toLinearMap)
      map_one' := by
        ext v
        simp [eV]
      map_mul' := by
        intro g₁ g₂
        ext v
        simp},
    ?_⟩
  ext h v
  change eV ((L.toRepresentation h) (eV.symm v)) = ρ h v
  have hcomm :=
    Representation.IntertwiningMap.isIntertwining
      (ρ := L.toRepresentation.comp H.subtype) (σ := ρ) eL.toRepMap h (eV.symm v)
  change eL.toLinearEquiv ((L.toRepresentation h) (eV.symm v)) =
    ρ h (eL.toLinearEquiv (eV.symm v)) at hcomm
  calc
    eV ((L.toRepresentation h) (eV.symm v))
        = ρ h (eL.toLinearEquiv (eV.symm v)) := by
            change eL.toLinearEquiv ((L.toRepresentation h) (eV.symm v)) = _
            exact hcomm
    _ = ρ h v := by simp [eV]
