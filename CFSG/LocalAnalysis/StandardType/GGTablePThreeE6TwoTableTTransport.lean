module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoTableTBridge
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.A1Action
import CFSG.RankThree.PartOne.KE.A1Levi
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KE.ThreeA1Group
import Certificates.Certificate1953
import Certificates.Certificate1954

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

section Transport

open Matrix
open CFSG.LieType.Steinberg.Adjoint

private def e6tTrans_chiZ (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) : ZMod 3 :=
  ∑ k, ((x k : ℤ) : ZMod 3) * v k

private def e6tTrans_e6chiZ (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    Multiplicative (ZMod 3) := e6Chi v (Multiplicative.ofAdd x)

private theorem e6tTrans_e6chiZ_apply (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_e6chiZ v x = Multiplicative.ofAdd (e6tTrans_chiZ v x) := by
  simp [e6tTrans_e6chiZ, e6Chi, e6tTrans_chiZ]

private theorem e6tTrans_e6chiZ_one_iff
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_e6chiZ v x = 1 ↔ e6tTrans_chiZ v x = 0 := by
  rw [e6tTrans_e6chiZ_apply]
  constructor
  · intro h
    have := congrArg Multiplicative.toAdd h
    simpa using this
  · intro h
    rw [h]
    simp

private theorem e6tTrans_mem_kernelRoots_iff
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    x ∈ kernelRoots (e6Chi v) ↔ IsRoot Tag.E6 x ∧ e6tTrans_chiZ v x = 0 := by
  simp only [kernelRoots, Set.mem_setOf_eq, e6tTrans_e6chiZ]
  exact and_congr_right fun _ => e6tTrans_e6chiZ_one_iff v x

private theorem e6tTrans_chiZ_add (v : Fin Tag.E6.rank → ZMod 3) (x y : Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ v (x + y) = e6tTrans_chiZ v x + e6tTrans_chiZ v y := by
  simp [e6tTrans_chiZ, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem e6tTrans_chiZ_smul (v : Fin Tag.E6.rank → ZMod 3) (c : ℤ) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ v (c • x) = (c : ZMod 3) * e6tTrans_chiZ v x := by
  simp only [e6tTrans_chiZ, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem e6tTrans_chiZ_neg
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ v (-x) = -e6tTrans_chiZ v x := by
  have h0 : e6tTrans_chiZ v (0 : Fin Tag.E6.rank → ℤ) = 0 := by simp [e6tTrans_chiZ]
  have h := e6tTrans_chiZ_add v x (-x)
  rw [add_neg_cancel, h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem e6tTrans_chiZ_sub
    (v : Fin Tag.E6.rank → ZMod 3) (x y : Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ v (x - y) = e6tTrans_chiZ v x - e6tTrans_chiZ v y := by
  rw [sub_eq_add_neg, e6tTrans_chiZ_add, e6tTrans_chiZ_neg, sub_eq_add_neg]
  rfl

private theorem e6tTrans_chiZ_single (v : Fin Tag.E6.rank → ZMod 3) (i : Fin Tag.E6.rank) :
    e6tTrans_chiZ v (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = v i := by
  simp only [e6tTrans_chiZ, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem e6tTrans_chiZ_sum
    {ι : Type*} (v : Fin Tag.E6.rank → ZMod 3) (s : Finset ι)
    (f : ι → Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ v (∑ i ∈ s, f i) = ∑ i ∈ s, e6tTrans_chiZ v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [e6tTrans_chiZ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, e6tTrans_chiZ_add, ih]

private def e6tTrans_finE6 {j : Fin 7} (hj : j.val < 6) : Fin Tag.E6.rank :=
  ⟨j.val, by rw [show Tag.E6.rank = 6 from rfl]; exact hj⟩

private theorem e6tTrans_cast_sum_cartan (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ) :
    (∑ k, (x k : ZMod 3) * (Tag.E6.cartan i k : ZMod 3)) =
      ((∑ l, Tag.E6.cartan i l * x l : ℤ) : ZMod 3) := by
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Int.cast_mul]
  ring

private theorem e6tTrans_chiZ_genActZ_expand {j : Fin 7} (hj : j.val < 6)
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ (genActZ j v) x = e6tTrans_chiZ v x -
      (∑ k, (x k : ZMod 3) * (Tag.E6.cartan (e6tTrans_finE6 hj) k : ZMod 3)) *
        v (e6tTrans_finE6 hj) := by
  have hg : genActZ j v =
      fun k => v k - (Tag.E6.cartan (e6tTrans_finE6 hj) k : ZMod 3) * v (e6tTrans_finE6 hj) := by
    funext k
    rw [genActZ]
    split_ifs
    · rfl
  rw [hg]
  simp only [e6tTrans_chiZ, mul_sub]
  rw [show (∑ x_1, ((x x_1 : ZMod 3) * v x_1 -
        (x x_1 : ZMod 3) * ((Tag.E6.cartan (e6tTrans_finE6 hj) x_1 : ZMod 3) * v (e6tTrans_finE6 hj)))) =
      (∑ x_1, (x x_1 : ZMod 3) * v x_1) -
        ∑ x_1, (x x_1 : ZMod 3) * ((Tag.E6.cartan (e6tTrans_finE6 hj) x_1 : ZMod 3) * v (e6tTrans_finE6 hj))
    from Finset.sum_sub_distrib (s := Finset.univ)
      (fun x_1 => (x x_1 : ZMod 3) * v x_1)
      (fun x_1 => (x x_1 : ZMod 3) * ((Tag.E6.cartan (e6tTrans_finE6 hj) x_1 : ZMod 3) * v (e6tTrans_finE6 hj)))]
  rw [Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => by ring

private theorem e6tTrans_chiZ_genActZ_of_lt
    {j : Fin 7} (hj : j.val < 6)
    (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ (genActZ j v) x = e6tTrans_chiZ v (simple Tag.E6 (e6tTrans_finE6 hj) • x) := by
  rw [e6tTrans_chiZ_genActZ_expand hj, e6tTrans_cast_sum_cartan]
  rw [simple_smul]
  rw [show reflect Tag.E6 (e6tTrans_finE6 hj) x =
      x - (∑ l, Tag.E6.cartan (e6tTrans_finE6 hj) l * x l) •
        (Pi.single (e6tTrans_finE6 hj) 1 : Fin Tag.E6.rank → ℤ) from rfl]
  rw [e6tTrans_chiZ_sub, e6tTrans_chiZ_smul, e6tTrans_chiZ_single]

private theorem e6tTrans_chiZ_genActZ_six (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ (genActZ 6 v) x = e6tTrans_chiZ v (-x) := by
  have h6 : genActZ 6 v = fun k => -v k := by
    funext k
    simp [genActZ]
  rw [h6]
  simp only [e6tTrans_chiZ, Pi.neg_apply, Int.cast_neg, neg_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact mul_neg _ _

private def e6tTrans_addHomOf (f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, f (x + y) = f x + f y) : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ)
    where
  toFun := f
  map_zero' := by
    have h : f 0 = f 0 + f 0 := by rw [← hadd, zero_add]
    have h1 : f 0 + 0 = f 0 + f 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h1).symm
  map_add' := hadd

private theorem e6tTrans_add_map_sum_single (f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, f (x + y) = f x + f y) (x : Fin Tag.E6.rank → ℤ) :
    f x = ∑ i, x i • f (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  change e6tTrans_addHomOf f hadd (∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
    ∑ i, x i • f (Pi.single i 1)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  rfl

private theorem e6tTrans_sum_single_decomp (x : Fin Tag.E6.rank → ℤ) :
    x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem e6tTrans_chiZ_map_of_basis
    (f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, f (x + y) = f x + f y) (v : Fin Tag.E6.rank → ZMod 3) (c : ZMod 3)
    (hb : ∀ i, e6tTrans_chiZ v (f (Pi.single i 1)) = c * v i) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_chiZ v (f x) = c * e6tTrans_chiZ v x := by
  rw [e6tTrans_add_map_sum_single f hadd x, e6tTrans_chiZ_sum]
  conv_rhs => rw [e6tTrans_chiZ]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e6tTrans_chiZ_smul, hb i]
  ring

private theorem e6tTrans_iform_sum_sum
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

private theorem e6tTrans_iform_map_of_basis
    (f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hgram : ∀ i j, iform (f (Pi.single i 1)) (f (Pi.single j 1)) =
      iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1))
    (x y : Fin Tag.E6.rank → ℤ) : iform (f x) (f y) = iform x y := by
  conv_lhs => rw [e6tTrans_add_map_sum_single f hadd x, e6tTrans_add_map_sum_single f hadd y]
  conv_rhs => rw [e6tTrans_sum_single_decomp x, e6tTrans_sum_single_decomp y]
  rw [e6tTrans_iform_sum_sum, e6tTrans_iform_sum_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hgram i j]

private structure e6tTrans_E6G where
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

private theorem e6tTrans_E6G_injective (D : e6tTrans_E6G) : Function.Injective D.toFun := by
  intro a b hab
  have h := congrArg D.toFun hab
  rwa [D.inv', D.inv'] at h

private theorem e6tTrans_E6G_map_kernelRoots
    (D : e6tTrans_E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, e6tTrans_chiZ v' x = e6tTrans_chiZ v (D.toFun x)) {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ kernelRoots (e6Chi v')) : D.toFun α ∈ kernelRoots (e6Chi v) := by
  rw [e6tTrans_mem_kernelRoots_iff] at hα ⊢
  exact ⟨(D.root_iff α).2 hα.1, by rw [← hchi α]; exact hα.2⟩

private theorem e6tTrans_E6G_map_kernelRoots_inv
    (D : e6tTrans_E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, e6tTrans_chiZ v' x = e6tTrans_chiZ v (D.toFun x)) {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ kernelRoots (e6Chi v)) : D.toFun β ∈ kernelRoots (e6Chi v') := by
  rw [e6tTrans_mem_kernelRoots_iff] at hβ ⊢
  exact ⟨(D.root_iff β).2 hβ.1, by rw [hchi, D.inv']; exact hβ.2⟩

private theorem e6tTrans_isRoot_of_mem_componentRoots' {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →*
    Multiplicative (ZMod 3)} {i : KernelComponent χ} {γ : Fin Tag.E6.rank → ℤ}
    (h : γ ∈ componentRoots χ i) : IsRoot Tag.E6 γ := (Classical.choose h).1

private theorem e6tTrans_E6G_mk_eq_mk_iff
    (D : e6tTrans_E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, e6tTrans_chiZ v' x = e6tTrans_chiZ v (D.toFun x)) {α γ : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ kernelRoots (e6Chi v')) (hγ : γ ∈ kernelRoots (e6Chi v')) :
    (⟦⟨α, hα⟩⟧ : KernelComponent (e6Chi v')) = ⟦⟨γ, hγ⟩⟧ ↔
      (⟦⟨D.toFun α, e6tTrans_E6G_map_kernelRoots D v v' hchi hα⟩⟧ : KernelComponent (e6Chi v)) =
        ⟦⟨D.toFun γ, e6tTrans_E6G_map_kernelRoots D v v' hchi hγ⟩⟧ := by
  have key : ∀ {x y : kernelRoots (e6Chi v')},
      Relation.EqvGen (fun a b : kernelRoots (e6Chi v') => a.1 ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ b.1) ≠ 0) x y →
      Relation.EqvGen (fun a b : kernelRoots (e6Chi v) => a.1 ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ b.1) ≠ 0)
        ⟨D.toFun x.1, e6tTrans_E6G_map_kernelRoots D v v' hchi x.2⟩
        ⟨D.toFun y.1, e6tTrans_E6G_map_kernelRoots D v v' hchi y.2⟩ := by
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
        ⟨D.toFun x.1, e6tTrans_E6G_map_kernelRoots_inv D v v' hchi x.2⟩
        ⟨D.toFun y.1, e6tTrans_E6G_map_kernelRoots_inv D v v' hchi y.2⟩ := by
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

private theorem e6tTrans_E6G_componentRoots_image
    (D : e6tTrans_E6G) (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, e6tTrans_chiZ v' x = e6tTrans_chiZ v (D.toFun x))
    (i : KernelComponent (e6Chi v')) :
    ∃ i' : KernelComponent (e6Chi v),
      componentRoots (e6Chi v) i' = D.toFun '' componentRoots (e6Chi v') i := by
  obtain ⟨⟨β, hβ⟩, rfl⟩ := Quotient.exists_rep i
  have hgβ := e6tTrans_E6G_map_kernelRoots D v v' hchi hβ
  refine ⟨⟦⟨D.toFun β, hgβ⟩⟧, ?_⟩
  ext α
  constructor
  · rintro ⟨hα, hαi⟩
    have hgα := e6tTrans_E6G_map_kernelRoots_inv D v v' hchi hα
    refine ⟨D.toFun α, ⟨hgα, ?_⟩, D.inv' α⟩
    rw [e6tTrans_E6G_mk_eq_mk_iff D v v' hchi hgα hβ]
    simpa only [D.inv'] using hαi
  · rintro ⟨γ, ⟨hγ, hγi⟩, rfl⟩
    have hkg := e6tTrans_E6G_map_kernelRoots D v v' hchi hγ
    refine ⟨hkg, ?_⟩
    have := (e6tTrans_E6G_mk_eq_mk_iff D v v' hchi hγ hβ).1 hγi
    simpa only [D.inv'] using this

private theorem e6tTrans_closure_conj_subset {S T : Set (WeylGroup Tag.E6)} {u : WeylGroup Tag.E6}
    (h : ∀ s ∈ S, u * s * u⁻¹ ∈ T) :
    ∀ w ∈ Subgroup.closure S, u * w * u⁻¹ ∈ Subgroup.closure T := by
  have hle : Subgroup.closure S ≤
      (Subgroup.closure T).comap (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro s hs
    exact (Subgroup.mem_comap).2 (Subgroup.subset_closure (h s hs))
  intro w hw
  simpa [MulAut.conj_apply] using hle hw

private theorem e6tTrans_twistInner_smul_image
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
    · refine e6tTrans_closure_conj_subset (u := g⁻¹) ?_ w hw
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
    · refine e6tTrans_closure_conj_subset (u := g) ?_ w hw
      rintro s ⟨ε, hε, rfl⟩
      exact ⟨g • ε, ⟨ε, hε, rfl⟩, (rootReflection_smul_root g (hΨ ε hε)).symm⟩
    · obtain ⟨δ, hδ, rfl⟩ := hγ
      have h := hact δ hδ
      show g • (τ (g • (g • δ))) = (g * w * g⁻¹) • (g • δ)
      rw [smul_smul, hgg, one_smul, h, mul_smul, mul_smul]
      have hcancel : g⁻¹ • (g • δ) = δ := by rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [hcancel]

private theorem e6tTrans_twistInner_neg_image
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

private noncomputable def e6tTrans_e6G_smul
    (i : Fin Tag.E6.rank) : e6tTrans_E6G where
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
    exact e6tTrans_twistInner_smul_image i Ψ τ hΨ

private noncomputable def e6tTrans_e6G_neg :
    e6tTrans_E6G where
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
    exact e6tTrans_twistInner_neg_image Ψ τ hΨ

private noncomputable def e6tTrans_conjPerm (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ)) :
    Equiv.Perm (Fin Tag.E6.rank → ℤ) :=
  (Equiv.trans
    { toFun := D.toFun, invFun := D.toFun, left_inv := D.inv', right_inv := D.inv' } ρ').trans
    { toFun := D.toFun, invFun := D.toFun, left_inv := D.inv', right_inv := D.inv' }

private theorem e6tTrans_conjPerm_apply (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (x : Fin Tag.E6.rank → ℤ) : e6tTrans_conjPerm D ρ' x = D.toFun (ρ' (D.toFun x)) := rfl

private theorem e6tTrans_conjPerm_iter (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (k : ℕ) :
    ((e6tTrans_conjPerm D ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k]) =
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

private theorem e6tTrans_conjPerm_iter_image
    (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (k : ℕ) (S : Set (Fin Tag.E6.rank → ℤ)) :
    ((e6tTrans_conjPerm D ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k])
        '' (D.toFun '' S) =
      D.toFun '' (((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k]) '' S) := by
  rw [e6tTrans_conjPerm_iter]
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨((ρ')^[k]) w, ⟨w, hw, rfl⟩, by simp [D.inv']⟩
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨D.toFun w, ⟨w, hw, rfl⟩, by simp [D.inv']⟩

private theorem e6tTrans_componentOrbitLength_conj
    (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (Ψ : Set (Fin Tag.E6.rank → ℤ)) :
    componentOrbitLength (e6tTrans_conjPerm D ρ') (D.toFun '' Ψ) =
      componentOrbitLength ρ' Ψ := by
  unfold componentOrbitLength
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  rw [e6tTrans_conjPerm_iter_image]
  constructor
  · rintro ⟨hs, he⟩
    exact ⟨hs, (Set.image_injective (f := D.toFun)).2 (e6tTrans_E6G_injective D) he⟩
  · rintro ⟨hs, he⟩
    exact ⟨hs, by rw [he]⟩

private theorem e6tTrans_ncard_image_conj
    (D : e6tTrans_E6G) (Ψ : Set (Fin Tag.E6.rank → ℤ)) :
    (D.toFun '' Ψ).ncard = Ψ.ncard :=
  Set.ncard_image_of_injective Ψ (e6tTrans_E6G_injective D)

private theorem e6tTrans_E6G_image_image (D : e6tTrans_E6G) (S : Set (Fin Tag.E6.rank → ℤ)) :
    D.toFun '' (D.toFun '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa [D.inv'] using hz
  · intro hx
    exact ⟨D.toFun x, ⟨x, hx, rfl⟩, D.inv' x⟩

private theorem e6tTrans_twist_iter (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (j : ℕ) (Ψ' : Set (Fin Tag.E6.rank → ℤ)) (hroot : ∀ γ ∈ Ψ', IsRoot Tag.E6 γ) :
    twistInner (D.toFun '' Ψ') (((e6tTrans_conjPerm D ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[j])) ↔
      twistInner Ψ' ((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[j]) := by
  rw [e6tTrans_conjPerm_iter]
  exact D.twist_iff Ψ' ((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[j]) hroot

private theorem e6tTrans_solv (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (Ψ' : Set (Fin Tag.E6.rank → ℤ)) (hroot : ∀ γ ∈ Ψ', IsRoot Tag.E6 γ) :
    E6SolvTwo (e6tTrans_conjPerm D ρ') (D.toFun '' Ψ') ↔ E6SolvTwo ρ' Ψ' := by
  have hcr : compRank (D.toFun '' Ψ') = compRank Ψ' := D.compRank' Ψ'
  have hnc : (D.toFun '' Ψ').ncard = Ψ'.ncard := e6tTrans_ncard_image_conj D Ψ'
  have hlen : componentOrbitLength (e6tTrans_conjPerm D ρ') (D.toFun '' Ψ') =
      componentOrbitLength ρ' Ψ' := e6tTrans_componentOrbitLength_conj D ρ' Ψ'
  have ht1 : twistInner (D.toFun '' Ψ') (e6tTrans_conjPerm D ρ') ↔ twistInner Ψ' ρ' := by
    have := e6tTrans_twist_iter D ρ' 1 Ψ' hroot
    simpa using this
  unfold E6SolvTwo
  rw [hcr, hnc, hlen]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2, h3, fun hh => h4 (ht1.mpr hh)⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2, h3, fun hh => h4 (ht1.mp hh)⟩

private theorem e6tTrans_rowW (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (Ψ' : Set (Fin Tag.E6.rank → ℤ)) (hroot : ∀ γ ∈ Ψ', IsRoot Tag.E6 γ) :
    E6RowTwoW (e6tTrans_conjPerm D ρ') (D.toFun '' Ψ') ↔ E6RowTwoW ρ' Ψ' := by
  have hcr : compRank (D.toFun '' Ψ') = compRank Ψ' := D.compRank' Ψ'
  have hnc : (D.toFun '' Ψ').ncard = Ψ'.ncard := e6tTrans_ncard_image_conj D Ψ'
  have hlen : componentOrbitLength (e6tTrans_conjPerm D ρ') (D.toFun '' Ψ') =
      componentOrbitLength ρ' Ψ' := e6tTrans_componentOrbitLength_conj D ρ' Ψ'
  have ht1 : twistInner (D.toFun '' Ψ') (e6tTrans_conjPerm D ρ') ↔ twistInner Ψ' ρ' := by
    have := e6tTrans_twist_iter D ρ' 1 Ψ' hroot
    simpa using this
  have ht2 : twistInner (D.toFun '' Ψ') (((e6tTrans_conjPerm D ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2])) ↔
      twistInner Ψ' ((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2]) :=
    e6tTrans_twist_iter D ρ' 2 Ψ' hroot
  unfold E6RowTwoW
  rw [hcr, hnc, hlen]
  constructor
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl ⟨h1, h2, h3, ht1.mp h4⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3, fun hh => h4 (ht1.mpr hh), ht2.mp h5⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, h3, ht2.mp h4⟩)
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl ⟨h1, h2, h3, ht1.mpr h4⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3, fun hh => h4 (ht1.mp hh), ht2.mpr h5⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, h3, ht2.mpr h4⟩)

private theorem e6tTrans_rowT (D : e6tTrans_E6G) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (Ψ' : Set (Fin Tag.E6.rank → ℤ)) (hroot : ∀ γ ∈ Ψ', IsRoot Tag.E6 γ) :
    E6RowTwoT (e6tTrans_conjPerm D ρ') (D.toFun '' Ψ') ↔ E6RowTwoT ρ' Ψ' := by
  have hcr : compRank (D.toFun '' Ψ') = compRank Ψ' := D.compRank' Ψ'
  have hnc : (D.toFun '' Ψ').ncard = Ψ'.ncard := e6tTrans_ncard_image_conj D Ψ'
  have hlen : componentOrbitLength (e6tTrans_conjPerm D ρ') (D.toFun '' Ψ') =
      componentOrbitLength ρ' Ψ' := e6tTrans_componentOrbitLength_conj D ρ' Ψ'
  have ht1 : twistInner (D.toFun '' Ψ') (e6tTrans_conjPerm D ρ') ↔ twistInner Ψ' ρ' := by
    have := e6tTrans_twist_iter D ρ' 1 Ψ' hroot
    simpa using this
  have ht2 : twistInner (D.toFun '' Ψ') (((e6tTrans_conjPerm D ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2])) ↔
      twistInner Ψ' ((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[2]) :=
    e6tTrans_twist_iter D ρ' 2 Ψ' hroot
  have ht3 : twistInner (D.toFun '' Ψ') (((e6tTrans_conjPerm D ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3])) ↔
      twistInner Ψ' ((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[3]) :=
    e6tTrans_twist_iter D ρ' 3 Ψ' hroot
  unfold E6RowTwoT
  rw [hcr, hnc, hlen]
  constructor
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact Or.inl ⟨h1, h2, h3, fun hh => h4 (ht1.mpr hh)⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3, fun hh => h4 (ht1.mpr hh)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, fun hh => h4 (ht1.mpr hh)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, fun hh => h4 (ht3.mpr hh)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, ht1.mp h4⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, fun hh => h4 (ht1.mpr hh),
        fun hh => h5 (ht2.mpr hh)⟩))))
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact Or.inl ⟨h1, h2, h3, fun hh => h4 (ht1.mp hh)⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3, fun hh => h4 (ht1.mp hh)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, fun hh => h4 (ht1.mp hh)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, fun hh => h4 (ht3.mp hh)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, ht1.mpr h4⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, fun hh => h4 (ht1.mp hh),
        fun hh => h5 (ht2.mp hh)⟩))))

private def e6tTrans_div3 (x : Fin Tag.E6.rank → ℤ) : Prop := ∀ k, ((x k : ℤ) : ZMod 3) = 0

private theorem e6tTrans_div3_add_iff {x y : Fin Tag.E6.rank → ℤ} (hy : e6tTrans_div3 y) :
    e6tTrans_div3 (x + y) ↔ e6tTrans_div3 x := by
  simp only [e6tTrans_div3, Pi.add_apply, Int.cast_add]
  constructor
  · intro h k
    simpa [hy k] using h k
  · intro h k
    simp [h k, hy k]

private theorem e6tTrans_div3_sub_iff {x y : Fin Tag.E6.rank → ℤ} (hy : e6tTrans_div3 y) :
    e6tTrans_div3 (x - y) ↔ e6tTrans_div3 x := by
  simp only [e6tTrans_div3, Pi.sub_apply, Int.cast_sub]
  constructor
  · intro h k
    have hk := h k
    rw [hy k] at hk
    exact sub_eq_zero.mp hk
  · intro h k
    simp [h k, hy k]

private theorem e6tTrans_div3_map (ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ' (x + y) = ρ' x + ρ' y) {x : Fin Tag.E6.rank → ℤ}
    (hx : e6tTrans_div3 x) : e6tTrans_div3 (ρ' x) := by
  intro k
  rw [e6tTrans_add_map_sum_single ρ' hadd x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_eq_zero fun i _ => by rw [hx i, zero_mul]

private theorem e6tTrans_reflect_apply (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ) :
    CFSG.Blueprint.Chevalley.reflect Tag.E6 i x =
      x - (∑ j, Tag.E6.cartan i j * x j) • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := rfl

private theorem e6tTrans_div3_smul_simple (i : Fin Tag.E6.rank) {x : Fin Tag.E6.rank → ℤ}
    (hx : e6tTrans_div3 x) : e6tTrans_div3 (simple Tag.E6 i • x) := by
  intro k
  rw [simple_smul, e6tTrans_reflect_apply]
  have hc : ((∑ j, Tag.E6.cartan i j * x j : ℤ) : ZMod 3) = 0 := by
    rw [Int.cast_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [Int.cast_mul, hx j, mul_zero]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Int.cast_sub, Int.cast_mul, hc, hx k]
  ring

private theorem e6tTrans_div3_smul_simple_iff (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ) :
    e6tTrans_div3 (simple Tag.E6 i • x) ↔ e6tTrans_div3 x := by
  constructor
  · intro h
    have h2 : e6tTrans_div3 (simple Tag.E6 i • (simple Tag.E6 i • x)) :=
      e6tTrans_div3_smul_simple i h
    rw [← mul_smul, (coxeterSystem Tag.E6).simple_mul_simple_self i, one_smul] at h2
    exact h2
  · exact e6tTrans_div3_smul_simple i

private theorem e6tTrans_div3_smul_threeVarpiOne (i : Fin Tag.E6.rank) :
    e6tTrans_div3 (simple Tag.E6 i • e6ThreeVarpiOne - e6ThreeVarpiOne) := by
  have hdecomp : simple Tag.E6 i • e6ThreeVarpiOne - e6ThreeVarpiOne =
      -((∑ j, Tag.E6.cartan i j * e6ThreeVarpiOne j) •
        (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
    rw [simple_smul, e6tTrans_reflect_apply]
    abel
  have hc : ((∑ j, Tag.E6.cartan i j * e6ThreeVarpiOne j : ℤ) : ZMod 3) = 0 := by
    fin_cases i <;> decide +kernel
  intro k
  rw [hdecomp]
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Int.cast_neg, Int.cast_mul, hc]
  simp

private theorem e6tTrans_E6G_map_sub (D : e6tTrans_E6G) (a b : Fin Tag.E6.rank → ℤ) :
    D.toFun (a - b) = D.toFun a - D.toFun b := by
  have h0 : D.toFun 0 = 0 := map_zero (e6tTrans_addHomOf D.toFun D.map_add')
  have hneg : ∀ b, D.toFun (-b) = -D.toFun b := by
    intro b
    have h := D.map_add' b (-b)
    rw [add_neg_cancel, h0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [sub_eq_add_neg, sub_eq_add_neg, D.map_add', hneg]

private theorem e6tTrans_cosetW_smul
    (i : Fin Tag.E6.rank) (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ' (x + y) = ρ' x + ρ' y) :
    E6CosetW (e6tTrans_conjPerm (e6tTrans_e6G_smul i) ρ') ↔ E6CosetW ρ' := by
  have hDdiv : ∀ x, e6tTrans_div3 ((e6tTrans_e6G_smul i).toFun x) ↔ e6tTrans_div3 x :=
    fun x => e6tTrans_div3_smul_simple_iff i x
  have hDw : e6tTrans_div3 ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne - e6ThreeVarpiOne) :=
    e6tTrans_div3_smul_threeVarpiOne i
  have hPdiv : ∀ x, e6tTrans_div3 x → e6tTrans_div3 (ρ' x) :=
    fun x hx => e6tTrans_div3_map ρ' hadd hx
  have step1 : e6tTrans_div3 ((e6tTrans_e6G_smul i).toFun (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne)) -
        e6ThreeVarpiOne) ↔
      e6tTrans_div3 (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne) -
        (e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne) := by
    have heq : (e6tTrans_e6G_smul i).toFun (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne)) -
          e6ThreeVarpiOne =
        (e6tTrans_e6G_smul i).toFun (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne) -
          (e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne) := by
      rw [e6tTrans_E6G_map_sub, (e6tTrans_e6G_smul i).inv']
    rw [heq]
    exact hDdiv _
  have step2 : e6tTrans_div3 (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne) -
        (e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne) ↔
      e6tTrans_div3 (ρ' e6ThreeVarpiOne - e6ThreeVarpiOne) := by
    have hd : e6tTrans_div3 ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne - e6ThreeVarpiOne) := hDw
    have hPd : e6tTrans_div3 (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne - e6ThreeVarpiOne)) :=
      hPdiv _ hd
    have hdiff : e6tTrans_div3 (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne - e6ThreeVarpiOne) -
        ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne - e6ThreeVarpiOne)) :=
      (e6tTrans_div3_sub_iff hd).mpr hPd
    have hsplit : (e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne = e6ThreeVarpiOne +
        ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne - e6ThreeVarpiOne) := by abel
    have heq : ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne) -
          (e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne =
        (ρ' e6ThreeVarpiOne - e6ThreeVarpiOne) +
          (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne - e6ThreeVarpiOne) -
            ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne - e6ThreeVarpiOne)) := by
      conv_lhs => rw [hsplit]
      rw [hadd]
      abel
    rw [heq]
    exact e6tTrans_div3_add_iff hdiff
  show e6tTrans_div3 ((e6tTrans_e6G_smul i).toFun (ρ' ((e6tTrans_e6G_smul i).toFun e6ThreeVarpiOne)) -
      e6ThreeVarpiOne) ↔ e6tTrans_div3 (ρ' e6ThreeVarpiOne - e6ThreeVarpiOne)
  exact step1.trans step2

private theorem e6tTrans_cosetW_neg
    (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ' (x + y) = ρ' x + ρ' y) :
    E6CosetW (e6tTrans_conjPerm e6tTrans_e6G_neg ρ') ↔ E6CosetW ρ' := by
  have hfun : e6tTrans_conjPerm e6tTrans_e6G_neg ρ' = ρ' := by
    refine Equiv.ext (fun x => ?_)
    have hneg : ρ' (-x) = -ρ' x := by
      have h0 : ρ' 0 = 0 := map_zero (e6tTrans_addHomOf ρ' hadd)
      have h := hadd x (-x)
      rw [add_neg_cancel, h0] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    show - (ρ' (-x)) = ρ' x
    rw [hneg, neg_neg]
  rw [hfun]

private theorem e6tTrans_of_data
    (D : e6tTrans_E6G)
    (v v' : Fin Tag.E6.rank → ZMod 3)
    (hchi : ∀ x, e6tTrans_chiZ v' x = e6tTrans_chiZ v (D.toFun x))
    (hcoset : ∀ (ρ' : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
      (∀ x y, ρ' (x + y) = ρ' x + ρ' y) →
      (E6CosetW (e6tTrans_conjPerm D ρ') ↔ E6CosetW ρ'))
    (h : E6TableTTwoAt v) : E6TableTTwoAt v' := by
  intro ρ' hadd' hroot' hadm' hv0' Ψ' hΨ' hns' hs'
  have hv0 : v ≠ 0 := by
    intro hv
    apply hv0'
    funext k
    rw [← e6tTrans_chiZ_single v' k, hchi]
    simp [e6tTrans_chiZ, hv]
  have hΨ'root : ∀ γ ∈ Ψ', IsRoot Tag.E6 γ := by
    obtain ⟨i', hi'⟩ := hΨ'
    intro γ hγ
    exact e6tTrans_isRoot_of_mem_componentRoots' (χ := e6Chi v') (i := i') (by rwa [hi'] at hγ)
  have hiso' : ∀ x y, iform (ρ' x) (ρ' y) = iform x y :=
    e6tTrans_iform_map_of_basis ρ' hadd' hadm'.2.1
  have hchar' : ∀ x, e6tTrans_chiZ v' (ρ' x) = 2 * e6tTrans_chiZ v' x :=
    e6tTrans_chiZ_map_of_basis ρ' hadd' v' 2 hadm'.2.2
  let ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ) := e6tTrans_conjPerm D ρ'
  have hρapply : ∀ x, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) x =
      D.toFun (ρ' (D.toFun x)) := fun x => e6tTrans_conjPerm_apply D ρ' x
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
      (Pi.single i 1)) v 2 := by
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
      change e6tTrans_chiZ v ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) (Pi.single i 1)) =
        2 * v i
      have h1 : e6tTrans_chiZ v ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
          (Pi.single i 1)) = 2 * e6tTrans_chiZ v (Pi.single i 1) := by
        rw [hρapply]
        rw [← hchi (ρ' (D.toFun (Pi.single i 1)))]
        rw [hchar' (D.toFun (Pi.single i 1))]
        rw [hchi (D.toFun (Pi.single i 1))]
        rw [D.inv' (Pi.single i 1)]
      rwa [e6tTrans_chiZ_single] at h1
  set Ψ : Set (Fin Tag.E6.rank → ℤ) := D.toFun '' Ψ' with hΨdef
  have hΨ : E6KerComponent v Ψ := by
    obtain ⟨i', hi'⟩ := hΨ'
    obtain ⟨i, hi⟩ := e6tTrans_E6G_componentRoots_image D v v' hchi i'
    exact ⟨i, by rw [hΨdef, hi', hi]⟩
  have hsolv : E6SolvTwo ρ Ψ ↔ E6SolvTwo ρ' Ψ' := e6tTrans_solv D ρ' Ψ' hΨ'root
  have hns : ¬ E6SolvTwo ρ Ψ := fun hh => hns' (hsolv.mp hh)
  have hs : ∀ Ψ'' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ'' →
      (∀ k : ℕ, ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k]) '' Ψ ≠ Ψ'') →
      E6SolvTwo ρ Ψ'' := by
    intro Ψ'' hΨ'' hnot
    obtain ⟨i'', rfl⟩ := hΨ''
    have hchi' : ∀ x, e6tTrans_chiZ v x = e6tTrans_chiZ v' (D.toFun x) := by
      intro x
      rw [hchi (D.toFun x), D.inv']
    obtain ⟨i', hi'⟩ := e6tTrans_E6G_componentRoots_image D v' v hchi' i''
    have hnot' : ∀ k : ℕ, ((ρ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k]) '' Ψ' ≠
        componentRoots (e6Chi v') i' := by
      intro k hk
      apply hnot k
      rw [hΨdef, e6tTrans_conjPerm_iter_image, hk, hi', e6tTrans_E6G_image_image]
    have hsolv' : E6SolvTwo ρ' (D.toFun '' componentRoots (e6Chi v) i'') := by
      rw [← hi']
      exact hs' (componentRoots (e6Chi v') i') ⟨i', rfl⟩ hnot'
    have hrootD : ∀ γ ∈ D.toFun '' componentRoots (e6Chi v) i'', IsRoot Tag.E6 γ := by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := hγ
      exact (D.root_iff δ).2 (e6tTrans_isRoot_of_mem_componentRoots' hδ)
    have hiff := e6tTrans_solv D ρ' (D.toFun '' componentRoots (e6Chi v) i'') hrootD
    rw [e6tTrans_E6G_image_image] at hiff
    exact hiff.mpr hsolv'
  have hconcl := h ρ hadd hroot hadm hv0 Ψ hΨ hns hs
  have hrowW : E6RowTwoW ρ Ψ ↔ E6RowTwoW ρ' Ψ' := e6tTrans_rowW D ρ' Ψ' hΨ'root
  have hrowT : E6RowTwoT ρ Ψ ↔ E6RowTwoT ρ' Ψ' := e6tTrans_rowT D ρ' Ψ' hΨ'root
  have hcoset' : E6CosetW ρ ↔ E6CosetW ρ' := hcoset ρ' hadd'
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · exact hrowW.mp (hconcl.1 (hcoset'.mpr hc))
  · exact hrowT.mp (hconcl.2 (fun hr => hc (hcoset'.mp hr)))

end Transport

theorem e6TableTTwoAt_genActZ
    (j : Fin 7) (v : Fin Tag.E6.rank → ZMod 3) (h : E6TableTTwoAt v) : E6TableTTwoAt (genActZ j v) := by
  by_cases hj : j.val < 6
  · refine e6tTrans_of_data (e6tTrans_e6G_smul (e6tTrans_finE6 hj)) v (genActZ j v) ?_ ?_ h
    · intro x
      exact e6tTrans_chiZ_genActZ_of_lt hj v x
    · exact fun ρ' hadd' => e6tTrans_cosetW_smul (e6tTrans_finE6 hj) ρ' hadd'
  · have hval : j.val = 6 := by omega
    have hj6 : j = (6 : Fin 7) := Fin.ext hval
    subst hj6
    refine e6tTrans_of_data e6tTrans_e6G_neg v (genActZ 6 v) ?_ ?_ h
    · intro x
      exact e6tTrans_chiZ_genActZ_six v x
    · exact fun ρ' hadd' => e6tTrans_cosetW_neg ρ' hadd'

end CFSG.StandardType.TablePThreeKG

end
