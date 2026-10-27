module

public import CFSG.Mathlib.LinearAlgebra.RootSystem.LatticeStabilizer
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

public section

namespace CFSG.RootPairing

open TauCeti

section RatFlip

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : _root_.RootPairing ι ℤ X Y)

@[expose] def toRatDual : Y →ₗ[ℤ] X →ₗ[ℤ] ℚ :=
  P.toLinearMap.flip.compr₂ (Algebra.linearMap ℤ ℚ)

@[simp]
lemma toRatDual_apply (y : Y) (x : X) : toRatDual P y x = (P.toLinearMap x y : ℚ) := by
  simp [toRatDual]

lemma toRatDual_injective : Function.Injective (toRatDual P) := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
  apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).1
  ext x
  have h := LinearMap.congr_fun hy x
  simp only [toRatDual_apply, LinearMap.zero_apply, Int.cast_eq_zero] at h
  simp [h]

lemma exists_toRatDual_eq (g : X →ₗ[ℤ] ℚ) (hg : ∀ x, ∃ n : ℤ, g x = n) :
    ∃ y : Y, toRatDual P y = g := by
  choose c hc using hg
  let g' : X →ₗ[ℤ] ℤ :=
    { toFun := c
      map_add' := fun x x' => Int.cast_injective (α := ℚ) (by simp [← hc, map_add])
      map_smul' := fun n x => Int.cast_injective (α := ℚ) (by simp [← hc]) }
  obtain ⟨y, hy⟩ := (LinearMap.IsPerfPair.bijective_right P.toLinearMap).2 g'
  refine ⟨y, LinearMap.ext fun x => ?_⟩
  rw [toRatDual_apply, hc x]
  have h := LinearMap.congr_fun hy x
  simp only [LinearMap.flip_apply] at h
  rw [h]
  rfl

@[expose] def evalRat : X →ₗ[ℤ] Module.Dual ℚ (X →ₗ[ℤ] ℚ) where
  toFun x :=
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' x x' := by ext f; simp
  map_smul' n x := by ext f; simp

@[simp]
lemma evalRat_apply (x : X) (f : X →ₗ[ℤ] ℚ) : evalRat x f = f x := rfl

include P in
lemma evalRat_injective : Function.Injective (evalRat : X →ₗ[ℤ] Module.Dual ℚ (X →ₗ[ℤ] ℚ)) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).1
  ext y
  have h := LinearMap.congr_fun hx (toRatDual P y)
  simp only [evalRat_apply, toRatDual_apply, LinearMap.zero_apply, Int.cast_eq_zero] at h
  simp [h]

lemma linearIndependent_toRatDual {κ : Type*} {v : κ → Y} (hv : LinearIndependent ℤ v) :
    LinearIndependent ℚ (toRatDual P ∘ v) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    (hv.map' (toRatDual P) (LinearMap.ker_eq_bot.mpr (toRatDual_injective P)))

include P in
lemma linearIndependent_evalRat {κ : Type*} {v : κ → X} (hv : LinearIndependent ℤ v) :
    LinearIndependent ℚ (evalRat ∘ v) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    (hv.map' evalRat (LinearMap.ker_eq_bot.mpr (evalRat_injective P)))

variable [Module.Free ℤ X] [Module.Finite ℤ X]

@[expose] noncomputable def ratFlip :
    _root_.RootPairing ι ℚ (X →ₗ[ℤ] ℚ) (Module.Dual ℚ (X →ₗ[ℤ] ℚ)) where
  toLinearMap := Module.Dual.eval ℚ (X →ₗ[ℤ] ℚ)
  isPerfPair_toLinearMap := inferInstance
  root := ⟨fun i => toRatDual P (P.coroot i), (toRatDual_injective P).comp P.coroot.injective⟩
  coroot := ⟨fun i => evalRat (P.root i), (evalRat_injective P).comp P.root.injective⟩
  root_coroot_two i := by simp [P.root_coroot_two i]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    simp only [Function.Embedding.coeFn_mk, Module.Dual.eval_apply, evalRat_apply,
      toRatDual_apply]
    rw [← P.reflectionPerm_coroot i j, map_sub, map_zsmul, Int.cast_smul_eq_zsmul]
  reflectionPerm_coroot i j := by
    simp only [Function.Embedding.coeFn_mk, Module.Dual.eval_apply, evalRat_apply,
      toRatDual_apply]
    rw [← P.reflectionPerm_root i j, map_sub, map_zsmul, Int.cast_smul_eq_zsmul]

@[simp] lemma ratFlip_root (i : ι) : (ratFlip P).root i = toRatDual P (P.coroot i) := rfl

@[simp] lemma ratFlip_coroot (i : ι) : (ratFlip P).coroot i = evalRat (P.root i) := rfl

@[simp] lemma ratFlip_reflectionPerm : (ratFlip P).reflectionPerm = P.reflectionPerm := rfl

@[simp] lemma ratFlip_coroot'_apply (i : ι) (f : X →ₗ[ℤ] ℚ) :
    (ratFlip P).coroot' i f = f (P.root i) := rfl

lemma ratFlip_pairing (i j : ι) : (ratFlip P).pairing i j = (P.pairing j i : ℚ) := rfl

instance : (ratFlip P).IsCrystallographic :=
  ⟨fun i j => ⟨P.pairing j i, by rw [ratFlip_pairing]; simp⟩⟩

instance [P.flip.IsReduced] : (ratFlip P).IsReduced := by
  refine ⟨fun i j h => ?_⟩
  have h' : ¬ LinearIndependent ℤ ![P.flip.root i, P.flip.root j] := by
    intro hli
    apply h
    have := linearIndependent_toRatDual P hli
    convert this using 1
    funext k
    fin_cases k <;> rfl
  rcases _root_.RootPairing.IsReduced.eq_or_eq_neg i j h' with h1 | h1
  · left
    simp only [_root_.RootPairing.flip_root] at h1
    simp [h1]
  · right
    simp only [_root_.RootPairing.flip_root] at h1
    simp [h1]

instance [P.IsReduced] : (ratFlip P).flip.IsReduced := by
  refine ⟨fun i j h => ?_⟩
  have h' : ¬ LinearIndependent ℤ ![P.root i, P.root j] := by
    intro hli
    apply h
    have := linearIndependent_evalRat P hli
    convert this using 1
    funext k
    fin_cases k <;> rfl
  rcases _root_.RootPairing.IsReduced.eq_or_eq_neg i j h' with h1 | h1
  · left
    simp [h1]
  · right
    simp [h1]

lemma span_ratFlip_root (hsc : P.corootSpan ℤ = ⊤) :
    Submodule.span ℚ (Set.range (ratFlip P).root) = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  obtain ⟨m, gen, hgen⟩ := Module.Finite.exists_fin (R := ℤ) (M := X)
  set d : ℕ := ∏ k, (f (gen k)).den
  have hd : (d : ℚ) ≠ 0 := by
    simp only [d]; push_cast
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast (f (gen k)).den_nz
  have hint : ∀ x, ∃ n : ℤ, ((d : ℚ) • f) x = n := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range gen) := hgen ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have hdk : (f (gen k)).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
      obtain ⟨c, hc⟩ := hdk
      refine ⟨c * (f (gen k)).num, ?_⟩
      rw [LinearMap.smul_apply, smul_eq_mul, hc]
      push_cast
      rw [mul_comm ((f (gen k)).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
    | zero => exact ⟨0, by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨n', hn'⟩ := hx'
      exact ⟨n + n', by rw [map_add, hn, hn']; push_cast; ring⟩
    | smul c x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨c * n, by rw [map_zsmul, hn]; push_cast; simp⟩
  obtain ⟨y, hy⟩ := exists_toRatDual_eq P _ hint
  have hy' : y ∈ AddSubgroup.closure (Set.range P.coroot) := by
    have h0 : y ∈ P.corootSpan ℤ := by rw [hsc]; exact Submodule.mem_top
    have h1 : y ∈ (Submodule.span ℤ (Set.range P.coroot)).toAddSubgroup := h0
    rwa [Submodule.span_int_eq_addSubgroupClosure] at h1
  have hmap : toRatDual P y ∈ AddSubgroup.closure (Set.range (ratFlip P).root) := by
    have h1 := AddSubgroup.mem_map_of_mem (toRatDual P).toAddMonoidHom hy'
    rw [AddMonoidHom.map_closure, ← Set.range_comp] at h1
    exact h1
  have hspan : toRatDual P y ∈ Submodule.span ℚ (Set.range (ratFlip P).root) := by
    refine AddSubgroup.closure_le (Submodule.span ℚ _).toAddSubgroup |>.mpr ?_ hmap
    exact Submodule.subset_span
  have : f = (d : ℚ)⁻¹ • toRatDual P y := by
    rw [hy, smul_smul, inv_mul_cancel₀ hd, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ hspan

end RatFlip

section Torus

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : _root_.RootPairing ι ℤ X Y)
  {K : Type*} [Field K]

variable [Module.Free ℤ X] [Module.Finite ℤ X]

lemma weylGroupToPerm_ofIdx {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (Q : _root_.RootPairing ι R M N) (i : ι) :
    Q.weylGroupToPerm (RootPairing.weylGroup.ofIdx Q i) = Q.reflectionPerm i :=
  Equiv.ext (_root_.RootPairing.weylGroupToPerm_ofIdx_apply Q i)

variable [Finite ι]

lemma isRootSystem_ratFlip (hsc : P.corootSpan ℤ = ⊤) : (ratFlip P).IsRootSystem := by
  have : Fintype ι := Fintype.ofFinite ι
  have h := span_ratFlip_root P hsc
  exact ⟨h, ((ratFlip P).rootSpan_eq_top_iff).mp h⟩

end Torus

end CFSG.RootPairing
