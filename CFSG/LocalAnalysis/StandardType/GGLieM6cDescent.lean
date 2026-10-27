module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType.GGFinModel

theorem exists_algebra_isAlgClosure_ggl
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ (inst : Algebra K GGL), letI := inst; IsAlgClosure K GGL := by
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  haveI : Algebra.IsAlgebraic (ZMod 2) K := Algebra.IsAlgebraic.of_finite (ZMod 2) K
  let f : K →ₐ[ZMod 2] GGL := IsAlgClosed.lift
  let inst : Algebra K GGL := f.toRingHom.toAlgebra
  refine ⟨inst, ?_⟩
  letI := inst
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  have h : Algebra.IsAlgebraic K GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) (A := GGL)
  exact (isAlgClosure_iff (k := K) (K := GGL)).mpr ⟨inferInstance, h⟩


end CFSG.StandardType.GGFinModel

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel

theorem exists_finite_subfield_lift_adjoint
    {τ : Tag} {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω]
    (S : Finset (ModGL τ Ω)) (hS : (↑S : Set (ModGL τ Ω)) ⊆ adjointGroup τ Ω)
    (k₀ : Type) [Field k₀] [Finite k₀] (ι₀ : k₀ →+* Ω) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (κ : k₀ →+* k) (ι : k →+* Ω),
      ι.comp κ = ι₀ ∧ ∀ s ∈ S, ∃ s' ∈ adjointGroup τ k, baseChangeGL ι s' = s := by
  classical
  have : CharP k₀ 2 := RingHom.charP ι₀ ι₀.injective 2
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra k₀ Ω := ι₀.toAlgebra
  have : IsScalarTower (ZMod 2) k₀ Ω :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have : Algebra.IsAlgebraic k₀ Ω :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := k₀)
  have hdesc : ∀ s : {x // x ∈ S}, ∃ E : Finset Ω, ∀ K : Subfield Ω, (E : Set Ω) ⊆ K →
      ∃ y ∈ adjointGroup τ K, baseChangeGL K.subtype y = s.1 :=
    fun s => exists_finset_descent (τ := τ) (hS (Finset.mem_coe.2 s.2))
  choose Es hEs using hdesc
  let E : Finset Ω := Finset.univ.biUnion Es
  have hEs_sub : ∀ s : {x // x ∈ S}, (Es s : Set Ω) ⊆ (E : Set Ω) := fun s a ha =>
    Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _, Finset.mem_coe.1 ha⟩)
  obtain ⟨F, hFfin, hEF, hkF⟩ := exists_finite_subfield_of_finset (K := k₀) (L := Ω) E
  refine ⟨↥F, inferInstance, hFfin, ι₀.codRestrict F (fun x => hkF ⟨x, rfl⟩), F.subtype, ?_, ?_⟩
  · exact RingHom.ext fun _ => rfl
  · intro s hs
    obtain ⟨y, hy, hyeq⟩ := hEs ⟨s, hs⟩ F fun x hx => hEF (hEs_sub ⟨s, hs⟩ hx)
    exact ⟨y, hy, hyeq⟩

end CFSG.StandardType.LieCore.M6c

namespace CFSG.StandardType.LieCore

variable {Ω : Type} [Field Ω] [CharP Ω 2]
  [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]


open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel

theorem exists_finite_adjoint_action_descent
    {E N : Type} [Group E] [Group N] [Finite E] [Finite N]
    (e : E →* ModGL Tag.E6 Ω) (j : N →* ModGL Tag.E6 Ω)
    (he : ∀ a, e a ∈ adjointGroup Tag.E6 Ω)
    (hj : ∀ n, j n ∈ adjointGroup Tag.E6 Ω)
    (α : N →* MulAut E)
    (hα : ∀ n a, e (α n a) = j n * e a * (j n)⁻¹)
    (k₀ : Type) [Field k₀] [Finite k₀] (ι₀ : k₀ →+* Ω) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (κ : k₀ →+* k) (ι : k →+* Ω),
      ι.comp κ = ι₀ ∧
      ∃ e_k : E →* adjointGroup Tag.E6 k, ∃ j_k : N →* adjointGroup Tag.E6 k,
        (∀ a, baseChangeGL ι (e_k a).val = e a) ∧
        (∀ n, baseChangeGL ι (j_k n).val = j n) ∧
        (∀ n a, e_k (α n a) = j_k n * e_k a * (j_k n)⁻¹) ∧
        (Function.Injective e → Function.Injective e_k) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype N := Fintype.ofFinite N
  let S : Finset (ModGL Tag.E6 Ω) :=
    Finset.univ.image e ∪ Finset.univ.image j
  have hS : (↑S : Set (ModGL Tag.E6 Ω)) ⊆ adjointGroup Tag.E6 Ω := by
    intro s hs
    rw [Finset.mem_coe, Finset.mem_union] at hs
    rcases hs with hs | hs
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
      exact he a
    · obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hs
      exact hj n
  have heS : ∀ a : E, e a ∈ S := fun a =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem e (Finset.mem_univ a))
  have hjS : ∀ n : N, j n ∈ S := fun n =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem j (Finset.mem_univ n))
  obtain ⟨k, hk, hkfin, κ, ι, hcomp, hlift⟩ :=
    M6c.exists_finite_subfield_lift_adjoint S hS k₀ ι₀
  letI : Field k := hk
  letI : Finite k := hkfin
  have hchar : CharP k 2 := RingHom.charP ι ι.injective 2
  have build : ∀ {X : Type} [Group X] [Fintype X]
      (f : X →* ModGL Tag.E6 Ω), (∀ x, f x ∈ S) →
      ∃ f_k : X →* adjointGroup Tag.E6 k,
        ∀ x, baseChangeGL ι (f_k x).val = f x := by
    intro X _ _ f hfS
    let fLift : X → ModGL Tag.E6 k := fun x =>
      Classical.choose (hlift (f x) (hfS x))
    have fLift_mem : ∀ x, fLift x ∈ adjointGroup Tag.E6 k := fun x =>
      (Classical.choose_spec (hlift (f x) (hfS x))).1
    have fLift_eq : ∀ x, baseChangeGL ι (fLift x) = f x := fun x =>
      (Classical.choose_spec (hlift (f x) (hfS x))).2
    let f0 : X →* ModGL Tag.E6 k :=
      { toFun := fLift
        map_one' := by
          apply baseChangeGL_injective ι
          calc
            baseChangeGL ι (fLift 1) = f 1 := fLift_eq 1
            _ = 1 := map_one f
            _ = baseChangeGL ι (1 : ModGL Tag.E6 k) := (map_one (baseChangeGL ι)).symm
        map_mul' := fun x y => by
          apply baseChangeGL_injective ι
          calc
            baseChangeGL ι (fLift (x * y)) = f (x * y) := fLift_eq (x * y)
            _ = f x * f y := map_mul f x y
            _ = baseChangeGL ι (fLift x) * baseChangeGL ι (fLift y) := by
              rw [fLift_eq x, fLift_eq y]
            _ = baseChangeGL ι (fLift x * fLift y) :=
              (map_mul (baseChangeGL ι) _ _).symm }
    exact ⟨f0.codRestrict (adjointGroup Tag.E6 k) fLift_mem, fun x => fLift_eq x⟩
  obtain ⟨e_k, he_k⟩ := build e heS
  obtain ⟨j_k, hj_k⟩ := build j hjS
  refine ⟨k, hk, hkfin, hchar, κ, ι, hcomp, e_k, j_k, he_k, hj_k, ?_, ?_⟩
  · intro n a
    apply Subtype.ext
    apply baseChangeGL_injective ι
    calc
      baseChangeGL ι (e_k (α n a)).val = e (α n a) := he_k _
      _ = j n * e a * (j n)⁻¹ := hα n a
      _ = baseChangeGL ι (j_k n).val * baseChangeGL ι (e_k a).val *
            (baseChangeGL ι (j_k n).val)⁻¹ := by rw [hj_k n, he_k a]
      _ = baseChangeGL ι ((j_k n * e_k a * (j_k n)⁻¹).val) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  · intro he_inj a b hab
    apply he_inj
    calc
      e a = baseChangeGL ι (e_k a).val := (he_k a).symm
      _ = baseChangeGL ι (e_k b).val :=
        congrArg (fun x : adjointGroup Tag.E6 k => baseChangeGL ι x.val) hab
      _ = e b := he_k b


end CFSG.StandardType.LieCore
