module

public import CFSG.Quasithin.H13.NQBlockTensorGL3
public import CFSG.LocalAnalysis.SteinbergCEMixedIrreducibleHead

public section

namespace CFSG.Quasithin.H13.NQBlock

open Module TensorProduct Subgroup CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
  CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement

section Tensor

variable {k : Type*} [Field k] {U I : Type*} [AddCommGroup U] [Module k U] [AddCommGroup I]
  [Module k I]

theorem rTensor_smulRight_apply (l : Module.Dual k U) (u : U) (t : U ⊗[k] I) :
    LinearMap.rTensor I (l.smulRight u) t =
      u ⊗ₜ TensorProduct.lid k I (LinearMap.rTensor I l t) := by
  induction t with
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.smulRight_apply,
      TensorProduct.lid_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, TensorProduct.tmul_add]

theorem exists_eq_lTensor_of_commute (b : Basis (Fin 3) k U) (φ : Module.End k (U ⊗[k] I))
    (hφ : ∀ g : (Module.End k U)ˣ, φ ∘ₗ LinearMap.rTensor I (g : Module.End k U) =
      LinearMap.rTensor I (g : Module.End k U) ∘ₗ φ) :
    ∃ h : Module.End k I, ∀ (u : U) (v : I), φ (u ⊗ₜ v) = u ⊗ₜ h v := by
  classical
  let C : Submodule k (Module.End k U) :=
    { carrier := {f | φ ∘ₗ LinearMap.rTensor I f = LinearMap.rTensor I f ∘ₗ φ}
      add_mem' := fun {f g} hf hg => by
        change φ ∘ₗ LinearMap.rTensor I (f + g) = LinearMap.rTensor I (f + g) ∘ₗ φ
        rw [LinearMap.rTensor_add, LinearMap.comp_add, LinearMap.add_comp]
        rw [show φ ∘ₗ LinearMap.rTensor I f = LinearMap.rTensor I f ∘ₗ φ from hf,
          show φ ∘ₗ LinearMap.rTensor I g = LinearMap.rTensor I g ∘ₗ φ from hg]
      zero_mem' := by
        change φ ∘ₗ LinearMap.rTensor I 0 = LinearMap.rTensor I 0 ∘ₗ φ
        rw [LinearMap.rTensor_zero, LinearMap.comp_zero, LinearMap.zero_comp]
      smul_mem' := fun c f hf => by
        change φ ∘ₗ LinearMap.rTensor I (c • f) = LinearMap.rTensor I (c • f) ∘ₗ φ
        rw [LinearMap.rTensor_smul, LinearMap.comp_smul, LinearMap.smul_comp]
        rw [show φ ∘ₗ LinearMap.rTensor I f = LinearMap.rTensor I f ∘ₗ φ from hf] }
  have hmemC : ∀ f, f ∈ C ↔ φ ∘ₗ LinearMap.rTensor I f = LinearMap.rTensor I f ∘ₗ φ :=
    fun _ => Iff.rfl
  have hmul : ∀ f g, f ∈ C → g ∈ C → f * g ∈ C := by
    intro f g hf hg
    rw [hmemC] at hf hg ⊢
    rw [LinearMap.rTensor_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hf,
      LinearMap.comp_assoc, hg, LinearMap.comp_assoc]
  have hunit : ∀ g : (Module.End k U)ˣ, (g : Module.End k U) ∈ C := hφ
  have h1 : (1 : Module.End k U) ∈ C := by
    have := hunit 1
    rwa [Units.val_one] at this
  set E : Fin 3 → Fin 3 → Module.End k U := fun i j => (b.coord j).smulRight (b i) with hEdef
  have hEapp : ∀ i j x, E i j x = b.coord j x • b i := fun _ _ _ => rfl
  have hc : ∀ i j, b.coord j (b i) = Finsupp.single i 1 j := fun i j => by
    rw [Basis.coord_apply, Basis.repr_self]
  have hEoff : ∀ i j, i ≠ j → E i j ∈ C := by
    intro i j hij
    have hsq : E i j * E i j = 0 := by
      ext x
      rw [Module.End.mul_apply, hEapp i j x, map_smul, hEapp, hc,
        Finsupp.single_eq_of_ne' hij, zero_smul, smul_zero, LinearMap.zero_apply]
    let g : (Module.End k U)ˣ :=
      ⟨1 + E i j, 1 - E i j,
        by rw [add_mul, one_mul, mul_sub, mul_one, hsq, sub_zero, sub_add_cancel],
        by rw [sub_mul, one_mul, mul_add, mul_one, hsq, add_zero, add_sub_cancel_right]⟩
    have e : E i j = (g : Module.End k U) - 1 := by
      change E i j = 1 + E i j - 1
      rw [add_sub_cancel_left]
    rw [e]
    exact C.sub_mem (hunit g) h1
  have hE00 : E 0 0 ∈ C := by
    have e : E 0 0 = E 0 1 * E 1 0 := by
      ext x
      rw [Module.End.mul_apply, hEapp 1 0 x, map_smul, hEapp 0 1, hc,
        Finsupp.single_eq_same, one_smul, hEapp]
    rw [e]
    exact hmul _ _ (hEoff 0 1 (by decide)) (hEoff 1 0 (by decide))
  have hEi0 : ∀ i, E i 0 ∈ C := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
      exact hE00
    · exact hEoff i 0 hi
  have hF : ∀ u : U, (b.coord 0).smulRight u ∈ C := by
    intro u
    have e : (b.coord 0).smulRight u = ∑ i, b.repr u i • E i 0 := by
      ext x
      rw [LinearMap.smulRight_apply, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, hEapp, smul_comm (b.repr u _) (b.coord 0 x)]
      rw [← Finset.smul_sum, ← b.equivFun_apply, b.sum_equivFun]
    rw [e]
    exact C.sum_mem fun i _ => C.smul_mem _ (hEi0 i)
  refine ⟨TensorProduct.lid k I ∘ₗ LinearMap.rTensor I (b.coord 0) ∘ₗ φ ∘ₗ
    TensorProduct.mk k U I (b 0), fun u v => ?_⟩
  have key := LinearMap.congr_fun ((hmemC _).mp (hF u)) (b 0 ⊗ₜ v)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearMap.smulRight_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
    one_smul] at key
  rw [key, rTensor_smulRight_apply]
  rfl

end Tensor

section Columns

variable {I : Type*} [AddCommGroup I] [Module (ZMod 2) I]

@[expose] noncomputable def colEquiv (b : Basis (Fin 3) (ZMod 2) I) :
    (Fin 3 → I) ≃ₗ[ZMod 2] Mat3 :=
  (LinearEquiv.piCongrRight fun _ => b.equivFun).trans
    (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) (ZMod 2) (ZMod 2))

theorem colEquiv_apply (b : Basis (Fin 3) (ZMod 2) I) (v : Fin 3 → I) (i k : Fin 3) :
    colEquiv b v i k = b.repr (v k) i :=
  rfl

theorem colEquiv_map (b : Basis (Fin 3) (ZMod 2) I) (g : Module.End (ZMod 2) I)
    (v : Fin 3 → I) :
    colEquiv b (fun k => g (v k)) = LinearMap.toMatrix b b g * colEquiv b v := by
  ext i k
  rw [colEquiv_apply, Matrix.mul_apply]
  have h := congrFun (LinearMap.toMatrix_mulVec_repr b b g (v k)) i
  rw [Matrix.mulVec, dotProduct] at h
  rw [← h]
  rfl

end Columns

section GL3

theorem card_axisT : Nat.card axisT = 4 := by
  have e : (ZMod 2 × ZMod 2) ≃ axisT :=
    { toFun := fun p => ⟨unitriGL 0 p.1 p.2, p.1, p.2, rfl⟩
      invFun := fun g => ((g : GL32) 0 2, (g : GL32) 1 2)
      left_inv := fun _ => rfl
      right_inv := fun g => by
        obtain ⟨_, b, c, rfl⟩ := g
        rfl }
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

theorem exists_map_conj_eq_sylowT {B : Subgroup GL32} (hB2 : IsPGroup 2 B)
    (hB8 : Nat.card B = 8) : ∃ g : GL32, B.map (MulAut.conj g).toMonoidHom = sylowT := by
  obtain ⟨U, hU⟩ := exists_sylow_T
  obtain ⟨P, hP⟩ := hB2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GL32 P U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardP : Nat.card (P : Subgroup GL32) = 8 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity U, hU, card_sylowT]
  have hBP : B = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hcardP, hB8])
  refine ⟨g, ?_⟩
  rw [hBP, ← hU, ← hg]
  rfl

theorem isPerfect_of_simple_noncomm {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : Group.IsPerfect Q := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hQ
    apply hab
    have hc : ⁅a, b⁆ ∈ commutator Q :=
      Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  · exact h

theorem GL32_noncomm : ∃ a b : GL32, a * b ≠ b * a := by
  refine ⟨transvecGL 0 1 (by decide), transvecGL 1 0 (by decide), fun h => ?_⟩
  have h1 := congrArg Units.val h
  rw [Units.val_mul, Units.val_mul, transvecGL_val, transvecGL_val] at h1
  revert h1
  decide

theorem alternatingGroup_five_noncomm :
    ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 0 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    fun h => ?_⟩
  have h1 := congrArg Subtype.val h
  revert h1
  decide

end GL3

section Coinvariants

variable {k : Type*} [Field k] {D : Type*} [AddCommGroup D] [Module k D] {G : Type*} [Group G]

theorem coinvariants_ker_eq_commSpace (ρ : Representation k G D)
    {Y : Subgroup (LinearMap.GeneralLinearGroup k D)}
    (hρY : ∀ g, ∃ y ∈ Y, ρ g = (y : Module.End k D))
    (hYρ : ∀ y ∈ Y, ∃ g, ρ g = (y : Module.End k D)) :
    Representation.Coinvariants.ker ρ = CFSG.LocalAnalysis.commSpace ⊤ Y := by
  apply le_antisymm
  · rw [Representation.Coinvariants.ker, Submodule.span_le]
    rintro _ ⟨⟨g, x⟩, rfl⟩
    obtain ⟨y, hy, hgy⟩ := hρY g
    change ρ g x - x ∈ _
    rw [hgy]
    exact CFSG.LocalAnalysis.sub_mem_commSpace hy Submodule.mem_top
  · rw [CFSG.LocalAnalysis.commSpace_le_iff]
    intro y hy x _
    obtain ⟨g, hg⟩ := hYρ y hy
    rw [← hg]
    exact Representation.Coinvariants.sub_mem_ker g x

end Coinvariants

end CFSG.Quasithin.H13.NQBlock
