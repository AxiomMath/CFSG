module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTBridge
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT
open CFSG.LieType.Steinberg.Adjoint

section Transport

open Matrix

private def chiZ (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) : ZMod 3 :=
  ∑ k, ((x k : ℤ) : ZMod 3) * v k

private def e6chiZ (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    Multiplicative (ZMod 3) := e6Chi v (Multiplicative.ofAdd x)

private theorem e6chiZ_apply (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6chiZ v x = Multiplicative.ofAdd (chiZ v x) := by
  simp [e6chiZ, e6Chi, chiZ]

private theorem e6chiZ_one_iff
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6chiZ v x = 1 ↔ chiZ v x = 0 := by
  rw [e6chiZ_apply]
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa using this
  · intro h
    rw [h]
    simp

private theorem mem_kernelRoots_iff
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    x ∈ kernelRoots (e6Chi v) ↔ IsRoot Tag.E6 x ∧ chiZ v x = 0 := by
  simp only [kernelRoots, Set.mem_setOf_eq, e6chiZ]
  exact and_congr_right fun _ => e6chiZ_one_iff v x

private theorem chiZ_add (v : Fin Tag.E6.rank → ZMod 3) (x y : Fin Tag.E6.rank → ℤ) :
    chiZ v (x + y) = chiZ v x + chiZ v y := by
  simp [chiZ, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem chiZ_smul (v : Fin Tag.E6.rank → ZMod 3) (c : ℤ) (x : Fin Tag.E6.rank → ℤ) :
    chiZ v (c • x) = (c : ZMod 3) * chiZ v x := by
  simp only [chiZ, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem chiZ_neg
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    chiZ v (-x) = -chiZ v x := by
  have h0 : chiZ v (0 : Fin Tag.E6.rank → ℤ) = 0 := by simp [chiZ]
  have h := chiZ_add v x (-x)
  rw [add_neg_cancel, h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem chiZ_sub
    (v : Fin Tag.E6.rank → ZMod 3) (x y : Fin Tag.E6.rank → ℤ) :
    chiZ v (x - y) = chiZ v x - chiZ v y := by
  rw [sub_eq_add_neg, chiZ_add, chiZ_neg, sub_eq_add_neg]
  rfl

private theorem chiZ_single (v : Fin Tag.E6.rank → ZMod 3) (i : Fin Tag.E6.rank) :
    chiZ v (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = v i := by
  simp only [chiZ, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem chiZ_sum
    {ι : Type*} (v : Fin Tag.E6.rank → ZMod 3) (s : Finset ι)
    (f : ι → Fin Tag.E6.rank → ℤ) :
    chiZ v (∑ i ∈ s, f i) = ∑ i ∈ s, chiZ v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chiZ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, chiZ_add, ih]

private def finE6 {j : Fin 7} (hj : j.val < 6) : Fin Tag.E6.rank :=
  ⟨j.val, by rw [show Tag.E6.rank = 6 from rfl]; exact hj⟩

private theorem cast_sum_cartan (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ) :
    (∑ k, (x k : ZMod 3) * (Tag.E6.cartan i k : ZMod 3)) =
      ((∑ l, Tag.E6.cartan i l * x l : ℤ) : ZMod 3) := by
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Int.cast_mul]
  ring

private theorem chiZ_genActZ_expand {j : Fin 7} (hj : j.val < 6)
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    chiZ (genActZ j v) x = chiZ v x -
      (∑ k, (x k : ZMod 3) * (Tag.E6.cartan (finE6 hj) k : ZMod 3)) *
        v (finE6 hj) := by
  have hg : genActZ j v =
      fun k => v k - (Tag.E6.cartan (finE6 hj) k : ZMod 3) * v (finE6 hj) := by
    funext k
    rw [genActZ]
    split_ifs
    · rfl
  rw [hg]
  simp only [chiZ, mul_sub]
  rw [show (∑ x_1, ((x x_1 : ZMod 3) * v x_1 -
        (x x_1 : ZMod 3) * ((Tag.E6.cartan (finE6 hj) x_1 : ZMod 3) * v (finE6 hj)))) =
      (∑ x_1, (x x_1 : ZMod 3) * v x_1) -
        ∑ x_1, (x x_1 : ZMod 3) * ((Tag.E6.cartan (finE6 hj) x_1 : ZMod 3) * v (finE6 hj))
    from Finset.sum_sub_distrib (s := Finset.univ)
      (fun x_1 => (x x_1 : ZMod 3) * v x_1)
      (fun x_1 => (x x_1 : ZMod 3) * ((Tag.E6.cartan (finE6 hj) x_1 : ZMod 3) * v (finE6 hj)))]
  rw [Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => by ring

private theorem chiZ_genActZ_of_lt
    {j : Fin 7} (hj : j.val < 6)
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    chiZ (genActZ j v) x = chiZ v (simple Tag.E6 (finE6 hj) • x) := by
  rw [chiZ_genActZ_expand hj, cast_sum_cartan]
  rw [simple_smul]
  rw [show reflect Tag.E6 (finE6 hj) x =
      x - (∑ l, Tag.E6.cartan (finE6 hj) l * x l) •
        (Pi.single (finE6 hj) 1 : Fin Tag.E6.rank → ℤ) from rfl]
  rw [chiZ_sub, chiZ_smul, chiZ_single]

private theorem chiZ_genActZ_six (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    chiZ (genActZ 6 v) x = chiZ v (-x) := by
  have h6 : genActZ 6 v = fun k => -v k := by
    funext k
    simp [genActZ]
  rw [h6]
  simp only [chiZ, Pi.neg_apply, Int.cast_neg, neg_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact mul_neg _ _

private def addHomOf (f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, f (x + y) = f x + f y) : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ)
    where
  toFun := f
  map_zero' := by
    have h : f 0 = f 0 + f 0 := by rw [← hadd, zero_add]
    have h1 : f 0 + 0 = f 0 + f 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h1).symm
  map_add' := hadd

private theorem add_map_sum_single (f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, f (x + y) = f x + f y) (x : Fin Tag.E6.rank → ℤ) :
    f x = ∑ i, x i • f (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  change addHomOf f hadd (∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
    ∑ i, x i • f (Pi.single i 1)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  rfl

private theorem sum_single_decomp (x : Fin Tag.E6.rank → ℤ) :
    x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem chiZ_map_of_basis
    (f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, f (x + y) = f x + f y) (v : Fin Tag.E6.rank → ZMod 3) (c : ZMod 3)
    (hb : ∀ i, chiZ v (f (Pi.single i 1)) = c * v i) (x : Fin Tag.E6.rank → ℤ) :
    chiZ v (f x) = c * chiZ v x := by
  rw [add_map_sum_single f hadd x, chiZ_sum]
  conv_rhs => rw [chiZ]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chiZ_smul, hb i]
  ring

private theorem iform_sum_sum
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℤ) (u : ι → Fin Tag.E6.rank → ℤ) (b : κ → ℤ)
    (v : κ → Fin Tag.E6.rank → ℤ) :
    iform (∑ i ∈ s, a i • u i) (∑ j ∈ t, b j • v j) =
      ∑ i ∈ s, ∑ j ∈ t, a i * (b j * iform (u i) (v j)) := by
  rw [iform_finset_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iform_finset_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iform_smul_left, iform_smul_right]

private theorem iform_map_of_basis
    (f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hgram : ∀ i j, iform (f (Pi.single i 1)) (f (Pi.single j 1)) =
      iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1))
    (x y : Fin Tag.E6.rank → ℤ) : iform (f x) (f y) = iform x y := by
  conv_lhs => rw [add_map_sum_single f hadd x, add_map_sum_single f hadd y]
  conv_rhs => rw [sum_single_decomp x, sum_single_decomp y]
  rw [iform_sum_sum, iform_sum_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hgram i j]

private structure E6G where
  toFun : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  inv' : ∀ x, toFun (toFun x) = x
  root_iff : ∀ x, IsRoot Tag.E6 (toFun x) ↔ IsRoot Tag.E6 x
  iform' : ∀ x y, iform (toFun x) (toFun y) = iform x y
  compRank' : ∀ Ψ : Set (Fin Tag.E6.rank → ℤ), compRank (toFun '' Ψ) = compRank Ψ
  twist_iff : ∀ (Ψ : Set (Fin Tag.E6.rank → ℤ))
    (τ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)),
    (∀ γ ∈ Ψ, IsRoot Tag.E6 γ) →
    (twistInner (toFun '' Ψ) (fun x => toFun (τ (toFun x))) ↔ twistInner Ψ τ)

private theorem E6G_injective (D : E6G) : Function.Injective D.toFun := by
  intro a b hab
  have h := congrArg D.toFun hab
  rwa [D.inv', D.inv'] at h

private theorem E6G_map_kernelRoots
    (D : E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, chiZ v' x = chiZ v (D.toFun x)) {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ kernelRoots (e6Chi v')) : D.toFun α ∈ kernelRoots (e6Chi v) := by
  rw [mem_kernelRoots_iff] at hα ⊢
  exact ⟨(D.root_iff α).2 hα.1, by rw [← hchi α]; exact hα.2⟩

private theorem E6G_map_kernelRoots_inv
    (D : E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, chiZ v' x = chiZ v (D.toFun x)) {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ kernelRoots (e6Chi v)) : D.toFun β ∈ kernelRoots (e6Chi v') := by
  rw [mem_kernelRoots_iff] at hβ ⊢
  exact ⟨(D.root_iff β).2 hβ.1, by rw [hchi, D.inv']; exact hβ.2⟩

private theorem isRoot_of_mem_componentRoots' {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →*
    Multiplicative (ZMod 3)} {i : KernelComponent χ} {γ : Fin Tag.E6.rank → ℤ}
    (h : γ ∈ componentRoots χ i) : IsRoot Tag.E6 γ := (Classical.choose h).1

private theorem E6G_mk_eq_mk_iff
    (D : E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, chiZ v' x = chiZ v (D.toFun x)) {α γ : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ kernelRoots (e6Chi v')) (hγ : γ ∈ kernelRoots (e6Chi v')) :
    (⟦⟨α, hα⟩⟧ : KernelComponent (e6Chi v')) = ⟦⟨γ, hγ⟩⟧ ↔
      (⟦⟨D.toFun α, E6G_map_kernelRoots D v v' hchi hα⟩⟧ : KernelComponent (e6Chi v)) =
        ⟦⟨D.toFun γ, E6G_map_kernelRoots D v v' hchi hγ⟩⟧ := by
  have key : ∀ {x y : kernelRoots (e6Chi v')},
      Relation.EqvGen (fun a b : kernelRoots (e6Chi v') => a.1 ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ b.1) ≠ 0) x y →
      Relation.EqvGen (fun a b : kernelRoots (e6Chi v) => a.1 ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ b.1) ≠ 0)
        ⟨D.toFun x.1, E6G_map_kernelRoots D v v' hchi x.2⟩
        ⟨D.toFun y.1, E6G_map_kernelRoots D v v' hchi y.2⟩ := by
    intro x y hxy
    induction hxy with
    | rel x y hr =>
      refine Relation.EqvGen.rel _ _ ?_
      change (D.toFun x.1) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (D.toFun y.1)) ≠ 0
      rw [dotProduct_mulVec_eq_iform, D.iform']
      rw [dotProduct_mulVec_eq_iform] at hr
      exact hr
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have key' : ∀ {x y : kernelRoots (e6Chi v)},
      Relation.EqvGen (fun a b : kernelRoots (e6Chi v) => a.1 ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ b.1) ≠ 0) x y →
      Relation.EqvGen (fun a b : kernelRoots (e6Chi v') => a.1 ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ b.1) ≠ 0)
        ⟨D.toFun x.1, E6G_map_kernelRoots_inv D v v' hchi x.2⟩
        ⟨D.toFun y.1, E6G_map_kernelRoots_inv D v v' hchi y.2⟩ := by
    intro x y hxy
    induction hxy with
    | rel x y hr =>
      refine Relation.EqvGen.rel _ _ ?_
      change (D.toFun x.1) ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (D.toFun y.1)) ≠ 0
      rw [dotProduct_mulVec_eq_iform, D.iform']
      rw [dotProduct_mulVec_eq_iform] at hr
      exact hr
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  constructor
  · intro h
    exact Quotient.sound (key (Quotient.exact h))
  · intro h
    have h' := key' (Quotient.exact h)
    have h'' : Relation.EqvGen (fun a b : kernelRoots (e6Chi v') => a.1 ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ b.1) ≠ 0) ⟨α, hα⟩ ⟨γ, hγ⟩ := by
      simpa only [D.inv'] using h'
    exact Quotient.sound h''

private theorem E6G_componentRoots_image
    (D : E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, chiZ v' x = chiZ v (D.toFun x))
    (i : KernelComponent (e6Chi v')) :
    ∃ i' : KernelComponent (e6Chi v),
      componentRoots (e6Chi v) i' = D.toFun '' componentRoots (e6Chi v') i := by
  obtain ⟨⟨β, hβ⟩, rfl⟩ := Quotient.exists_rep i
  have hgβ := E6G_map_kernelRoots D v v' hchi hβ
  refine ⟨⟦⟨D.toFun β, hgβ⟩⟧, ?_⟩
  ext α
  constructor
  · rintro ⟨hα, hαi⟩
    have hgα := E6G_map_kernelRoots_inv D v v' hchi hα
    refine ⟨D.toFun α, ⟨hgα, ?_⟩, D.inv' α⟩
    rw [E6G_mk_eq_mk_iff D v v' hchi hgα hβ]
    simpa only [D.inv'] using hαi
  · rintro ⟨γ, ⟨hγ, hγi⟩, rfl⟩
    have hkg := E6G_map_kernelRoots D v v' hchi hγ
    refine ⟨hkg, ?_⟩
    have := (E6G_mk_eq_mk_iff D v v' hchi hγ hβ).1 hγi
    simpa only [D.inv'] using this

private theorem closure_conj_subset {S T : Set (WeylGroup Tag.E6)} {u : WeylGroup Tag.E6}
    (h : ∀ s ∈ S, u * s * u⁻¹ ∈ T) :
    ∀ w ∈ Subgroup.closure S, u * w * u⁻¹ ∈ Subgroup.closure T := by
  have hle : Subgroup.closure S ≤
      (Subgroup.closure T).comap (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro s hs
    exact (Subgroup.mem_comap).2 (Subgroup.subset_closure (h s hs))
  intro w hw
  simpa [MulAut.conj_apply] using hle hw

private theorem twistInner_smul_image
    (i : Fin Tag.E6.rank)
    (Ψ : Set (Fin Tag.E6.rank → ℤ))
    (τ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hΨ : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ) :
    twistInner ((fun x => simple Tag.E6 i • x) '' Ψ)
      (fun x => simple Tag.E6 i • (τ (simple Tag.E6 i • x))) ↔ twistInner Ψ τ := by
  set g : WeylGroup Tag.E6 := simple Tag.E6 i with hg
  have hgg : g * g = 1 := (coxeterSystem Tag.E6).simple_mul_simple_self i
  constructor
  · rintro ⟨w, hw, hact⟩
    refine ⟨g⁻¹ * w * g, ?_, fun δ hδ => ?_⟩
    · refine closure_conj_subset (u := g⁻¹) ?_ w hw
      rintro s ⟨γ, ⟨ε, hε, rfl⟩, rfl⟩
      refine ⟨ε, hε, ?_⟩
      rw [rootReflection_smul_root g (hΨ ε hε)]
      group
    · have h := hact (g • δ) ⟨δ, hδ, rfl⟩
      simp only [smul_smul, hgg, one_smul] at h
      have h2 := congrArg (fun x => g⁻¹ • x) h
      simpa [← mul_smul, mul_assoc] using h2
  · rintro ⟨w, hw, hact⟩
    refine ⟨g * w * g⁻¹, ?_, fun γ hγ => ?_⟩
    · refine closure_conj_subset (u := g) ?_ w hw
      rintro s ⟨ε, hε, rfl⟩
      exact ⟨g • ε, ⟨ε, hε, rfl⟩, (rootReflection_smul_root g (hΨ ε hε)).symm⟩
    · obtain ⟨δ, hδ, rfl⟩ := hγ
      have h := hact δ hδ
      show g • (τ (g • (g • δ))) = (g * w * g⁻¹) • (g • δ)
      rw [smul_smul, hgg, one_smul, h, mul_smul, mul_smul]
      have hcancel : g⁻¹ • (g • δ) = δ := by rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [hcancel]

private theorem twistInner_neg_image
    (Ψ : Set (Fin Tag.E6.rank → ℤ))
    (τ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hΨ : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ) :
    twistInner ((fun x => -x) '' Ψ) (fun x => -τ (-x)) ↔ twistInner Ψ τ := by
  have hset : {s : WeylGroup Tag.E6 | ∃ γ ∈ (fun x => -x) '' Ψ, s = rootReflection γ} =
      {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ} := by
    ext s
    constructor
    · rintro ⟨γ, ⟨δ, hδ, rfl⟩, rfl⟩
      exact ⟨δ, hδ, rootReflection_neg (hΨ δ hδ)⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact ⟨-δ, ⟨δ, hδ, rfl⟩, (rootReflection_neg (hΨ δ hδ)).symm⟩
  rw [twistInner, twistInner, hset]
  constructor
  · rintro ⟨w, hw, hact⟩
    refine ⟨w, hw, fun δ hδ => ?_⟩
    have h := hact (-δ) ⟨δ, hδ, rfl⟩
    simp only [Pi.neg_apply, neg_neg] at h
    rw [smul_neg] at h
    exact neg_injective h
  · rintro ⟨w, hw, hact⟩
    refine ⟨w, hw, fun γ hγ => ?_⟩
    obtain ⟨δ, hδ, rfl⟩ := hγ
    have h := hact δ hδ
    show -τ (-(-δ)) = w • (-δ)
    rw [neg_neg, smul_neg, h]

private noncomputable def e6G_smul
    (i : Fin Tag.E6.rank) : E6G where
  toFun := fun x => simple Tag.E6 i • x
  map_add' := fun x y => smul_add (simple Tag.E6 i) x y
  inv' := by
    intro x
    rw [← mul_smul, (coxeterSystem Tag.E6).simple_mul_simple_self i, one_smul]
  root_iff := by intro x; exact isRoot_smul_iff (simple Tag.E6 i)
  iform' := by intro x y; exact iform_smul (simple Tag.E6 i) x y
  compRank' := by
    intro Ψ
    exact compRank_image (simple Tag.E6 i) Ψ
  twist_iff := by
    intro Ψ τ hΨ
    exact twistInner_smul_image i Ψ τ hΨ

private noncomputable def e6G_neg :
    E6G where
  toFun := fun x => -x
  map_add' := fun x y => neg_add x y
  inv' := fun x => neg_neg x
  root_iff := fun x => isRoot_neg_iff
  iform' := by
    intro x y
    rw [← neg_one_smul ℤ x, ← neg_one_smul ℤ y, iform_smul_left, iform_smul_right]
    ring
  compRank' := by
    intro Ψ
    have hspan : Submodule.span ℚ ((fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) ''
          ((fun x => -x) '' Ψ)) =
        Submodule.span ℚ ((fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) '' Ψ) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨γ, ⟨δ, hδ, rfl⟩, rfl⟩
        have h : (fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) ((fun x => -x) δ) =
            -(fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) δ := by ext i; simp
        rw [h]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨δ, hδ, rfl⟩)
      · apply Submodule.span_le.mpr
        rintro _ ⟨δ, hδ, rfl⟩
        have h : (fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) δ =
            -(fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) ((fun x => -x) δ) := by ext i; simp
        rw [h]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨-δ, ⟨δ, hδ, rfl⟩, rfl⟩)
    show compRank ((fun x => -x) '' Ψ) = compRank Ψ
    unfold compRank
    rw [hspan]
  twist_iff := by
    intro Ψ τ hΨ
    exact twistInner_neg_image Ψ τ hΨ

private noncomputable def conjPerm (D : E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ)) :
    Equiv.Perm (Fin Tag.E6.rank → ℤ) :=
  (Equiv.trans
    { toFun := D.toFun, invFun := D.toFun, left_inv := D.inv', right_inv := D.inv' } ρ').trans
    { toFun := D.toFun, invFun := D.toFun, left_inv := D.inv', right_inv := D.inv' }

private theorem conjPerm_apply (D : E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (x : Fin Tag.E6.rank → ℤ) : conjPerm D ρ' x = D.toFun (ρ' (D.toFun x)) := rfl

private theorem conjPerm_iter (D : E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (k : ℕ) :
    ((conjPerm D ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k]) =
      fun x => D.toFun (((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k])
        (D.toFun x)) := by
  induction k with
  | zero =>
    funext x
    simp [D.inv']
  | succ k ih =>
    funext x
    rw [Function.iterate_succ_apply', ih]
    show D.toFun (ρ' (D.toFun (D.toFun ((ρ')^[k] (D.toFun x))))) = _
    rw [D.inv', Function.iterate_succ_apply']

private theorem conjPerm_iter_image
    (D : E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (k : ℕ) (S : Set (Fin Tag.E6.rank → ℤ)) :
    ((conjPerm D ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k])
        '' (D.toFun '' S) =
      D.toFun '' (((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k]) '' S) := by
  rw [conjPerm_iter]
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨((ρ')^[k]) w, ⟨w, hw, rfl⟩, by simp [D.inv']⟩
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨D.toFun w, ⟨w, hw, rfl⟩, by simp [D.inv']⟩

private theorem componentOrbitLength_conj
    (D : E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (Ψ : Set (Fin Tag.E6.rank → ℤ)) :
    componentOrbitLength (conjPerm D ρ') (D.toFun '' Ψ) =
      componentOrbitLength ρ' Ψ := by
  unfold componentOrbitLength
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  rw [conjPerm_iter_image]
  constructor
  · rintro ⟨hs, he⟩
    exact ⟨hs, (Set.image_injective (f := D.toFun)).2 (E6G_injective D) he⟩
  · rintro ⟨hs, he⟩
    exact ⟨hs, by rw [he]⟩

private theorem ncard_image_conj
    (D : E6G) (Ψ : Set (Fin Tag.E6.rank → ℤ)) :
    (D.toFun '' Ψ).ncard = Ψ.ncard :=
  Set.ncard_image_of_injective Ψ (E6G_injective D)

private theorem E6G_image_image (D : E6G) (S : Set (Fin Tag.E6.rank → ℤ)) :
    D.toFun '' (D.toFun '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa [D.inv'] using hz
  · intro hx
    exact ⟨D.toFun x, ⟨x, hx, rfl⟩, D.inv' x⟩

private theorem e6TableTAt_of_data
    (D : E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, chiZ v' x = chiZ v (D.toFun x)) (h : E6TableTAt v) :
    E6TableTAt v' := by
  intro ρ' r hadd' hroot' hadm' hv0' Ψ' hΨ' hs'
  have hv0 : v ≠ 0 := by
    intro hv
    apply hv0'
    funext k
    rw [← chiZ_single v' k, hchi]
    simp [chiZ, hv]
  have hΨ'root : ∀ γ ∈ Ψ', IsRoot Tag.E6 γ := by
    obtain ⟨i', hi'⟩ := hΨ'
    intro γ hγ
    exact isRoot_of_mem_componentRoots' (χ := e6Chi v') (i := i') (by rwa [hi'] at hγ)
  have hiso' : ∀ x y, iform (ρ' x) (ρ' y) = iform x y :=
    iform_map_of_basis ρ' hadd' hadm'.2.1
  have hchar' : ∀ x, chiZ v' (ρ' x) = r * chiZ v' x :=
    chiZ_map_of_basis ρ' hadd' v' r hadm'.2.2
  let ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ) := conjPerm D ρ'
  have hρapply : ∀ x, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) x =
      D.toFun (ρ' (D.toFun x)) := fun x => conjPerm_apply D ρ' x
  have hadd : ∀ x y, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) (x + y) =
      ρ x + ρ y := by
    intro x y
    simp only [hρapply, D.map_add' x y, hadd', D.map_add']
  have hroot : ∀ γ, IsRoot Tag.E6 γ →
      IsRoot Tag.E6 ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) γ) := by
    intro γ hγ
    rw [hρapply]
    exact (D.root_iff _).2 (hroot' (D.toFun γ) ((D.root_iff γ).2 hγ))
  have hadm : E6Admissible (fun i => (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
      (Pi.single i 1)) v r := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      change IsRoot Tag.E6 ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
        (Pi.single i 1))
      rw [hρapply]
      exact (D.root_iff _).2 (hroot' (D.toFun (Pi.single i 1))
        ((D.root_iff _).2 (IsRoot.basis i)))
    · intro i j
      change iform ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) (Pi.single i 1))
        ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) (Pi.single j 1)) =
        iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1)
      rw [hρapply, hρapply, D.iform', hiso', D.iform']
    · intro i
      change chiZ v ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) (Pi.single i 1)) =
        r * v i
      have h1 : chiZ v ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
          (Pi.single i 1)) = r * chiZ v (Pi.single i 1) := by
        rw [hρapply]
        rw [← hchi (ρ' (D.toFun (Pi.single i 1)))]
        rw [hchar' (D.toFun (Pi.single i 1))]
        rw [hchi (D.toFun (Pi.single i 1))]
        rw [D.inv' (Pi.single i 1)]
      rwa [chiZ_single] at h1
  set Ψ : Set (Fin Tag.E6.rank → ℤ) := D.toFun '' Ψ' with hΨdef
  have hΨ : E6KerComponent v Ψ := by
    obtain ⟨i', hi'⟩ := hΨ'
    obtain ⟨i, hi⟩ := E6G_componentRoots_image D v v' hchi i'
    exact ⟨i, by rw [hΨdef, hi', hi]⟩
  have hs : ∀ Ψ'' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ'' →
      ∃ k : ℕ, ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k]) '' Ψ = Ψ'' := by
    intro Ψ'' hΨ''
    obtain ⟨i'', rfl⟩ := hΨ''
    have hchi' : ∀ x, chiZ v x = chiZ v' (D.toFun x) := by
      intro x
      rw [hchi (D.toFun x), D.inv']
    obtain ⟨i', hi'⟩ := E6G_componentRoots_image D v' v hchi' i''
    obtain ⟨k, hk⟩ := hs' (componentRoots (e6Chi v') i') ⟨i', rfl⟩
    refine ⟨k, ?_⟩
    rw [hΨdef, conjPerm_iter_image, hk, hi', E6G_image_image]
  have hconcl := h ρ r hadd hroot hadm hv0 Ψ hΨ hs
  have hcr : compRank Ψ = compRank Ψ' := D.compRank' Ψ'
  have hnc : Ψ.ncard = Ψ'.ncard := ncard_image_conj D Ψ'
  have hlen : componentOrbitLength ρ Ψ = componentOrbitLength ρ' Ψ' :=
    componentOrbitLength_conj D ρ' Ψ'
  have htw : twistInner Ψ ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3]) ↔
      twistInner Ψ' ((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3]) := by
    rw [conjPerm_iter]
    exact D.twist_iff Ψ' ((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3]) hΨ'root
  rcases hconcl with h | h | h | h
  · exact Or.inl ⟨by rw [← hcr]; exact h.1, by rw [← hnc]; exact h.2.1,
      by rw [← hlen]; exact h.2.2⟩
  · exact Or.inr (Or.inl ⟨by rw [← hcr]; exact h.1, by rw [← hnc]; exact h.2.1,
      by rw [← hlen]; exact h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by rw [← hcr]; exact h.1, by rw [← hnc]; exact h.2.1,
      by rw [← hlen]; exact h.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by rw [← hcr]; exact h.1, by rw [← hnc]; exact h.2.1,
      by rw [← hlen]; exact h.2.2.1, fun hr => htw.mp (h.2.2.2.1 hr),
      fun hr => fun hh => h.2.2.2.2 hr (htw.mpr hh)⟩))

theorem e6TableTAt_genActZ
    (j : Fin 7) (v : Fin Tag.E6.rank → ZMod 3) (h : E6TableTAt v) :
    E6TableTAt (genActZ j v) := by
  by_cases hj : j.val < 6
  · refine e6TableTAt_of_data (e6G_smul (finE6 hj)) v (genActZ j v) ?_ h
    intro x
    exact chiZ_genActZ_of_lt hj v x
  · have hval : j.val = 6 := by omega
    have hj6 : j = (6 : Fin 7) := Fin.ext hval
    subst hj6
    refine e6TableTAt_of_data e6G_neg v (genActZ 6 v) ?_ h
    intro x
    exact chiZ_genActZ_six v x

end Transport

end CFSG.StandardType.TablePThreeKG

end
