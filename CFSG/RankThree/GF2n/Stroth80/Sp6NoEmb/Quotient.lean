module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.NK

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped TensorProduct
open Representation CFSG.Open
open CFSG.QuasithinUnique.Setup.X7b (exists_isCoatom_subrep quotient_isIrreducible_of_isCoatom)
open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal (block)

variable {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]

theorem zmod_two_smul_eq {M : Type} [AddCommGroup M] [Module K M] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (f : N →+ M) (c : ZMod 2) (a : N) :
    f (c • a) = (algebraMap (ZMod 2) K c) • f a := by
  have : c = 0 ∨ c = 1 := by revert c; decide
  rcases this with rfl | rfl <;> simp

theorem exists_quotient_of_embedding {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    {ρN : Representation (ZMod 2) (StatedSp 3 K) N} (hNirr : ρN.IsIrreducible)
    (hNcard : Nat.card N = Fintype.card K ^ 8)
    {M : Type} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (ρM : Representation K (StatedSp 3 K) M) (f : N →+ M) (hf : ∀ g a, f (ρN g a) = ρM g (f a))
    (hinj : Function.Injective f) :
    ∃ (Yb : Type) (_ : AddCommGroup Yb) (_ : Module K Yb) (_ : FiniteDimensional K Yb)
      (ρY : Representation K (StatedSp 3 K) Yb)
      (π : (baseChangeRep (K := K) ρN).IntertwiningMap ρY),
      ρY.IsIrreducible ∧ Function.Surjective π ∧ 8 ≤ finrank K Yb ∧
      ∀ J, pat (ρY.comp block) J ≤ pat (ρM.comp block) J := by
  classical
  letI : Module (ZMod 2) M := Module.compHom M (algebraMap (ZMod 2) K)
  haveI : IsScalarTower (ZMod 2) K M :=
    ⟨fun c k m => by
      change (c • k) • m = (algebraMap (ZMod 2) K c) • (k • m)
      rw [Algebra.smul_def, mul_smul]⟩
  let fL : N →ₗ[ZMod 2] M := { f with map_smul' := zmod_two_smul_eq f }
  let F : K ⊗[ZMod 2] N →ₗ[K] M := fL.liftBaseChange K
  have hF : ∀ (g : StatedSp 3 K) (y : K ⊗[ZMod 2] N),
      F (baseChangeRep (K := K) ρN g y) = ρM g (F y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [baseChangeRep_apply, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
        LinearMap.liftBaseChange_tmul, map_smul]
      exact congrArg (c • ·) (hf g a)
    | add x y hx hy => simp only [map_add, hx, hy]
  let Ysub : Subrepresentation ρM :=
    ⟨LinearMap.range F, by
      rintro g _ ⟨y, rfl⟩
      exact ⟨baseChangeRep (K := K) ρN g y, hF g y⟩⟩
  have hNnt : Nontrivial N := by
    rw [← Finite.one_lt_card_iff_nontrivial, hNcard]
    have : 2 ≤ Fintype.card K := Fintype.one_lt_card
    calc 1 < 2 := by norm_num
      _ ≤ Fintype.card K := this
      _ ≤ Fintype.card K ^ 8 := Nat.le_self_pow (by norm_num) _
  haveI hYnt : Nontrivial Ysub.toSubmodule := by
    obtain ⟨a, ha⟩ := exists_ne (0 : N)
    refine ⟨⟨⟨F (1 ⊗ₜ a), ⟨_, rfl⟩⟩, 0, fun h => ha (hinj ?_)⟩⟩
    have h1 : F (1 ⊗ₜ a) = 0 := congrArg Subtype.val h
    rw [LinearMap.liftBaseChange_one_tmul] at h1
    rw [map_zero]
    exact h1
  obtain ⟨W, hW⟩ := exists_isCoatom_subrep Ysub.toRepresentation
  have hQirr := quotient_isIrreducible_of_isCoatom _ W hW
  let π : (baseChangeRep (K := K) ρN).IntertwiningMap W.quotient :=
    ⟨W.toSubmodule.mkQ ∘ₗ F.rangeRestrict, fun g => by
      refine LinearMap.ext fun y => ?_
      change Submodule.Quotient.mk (⟨F (baseChangeRep (K := K) ρN g y), _⟩ : Ysub.toSubmodule) =
        Submodule.Quotient.mk (⟨ρM g (F y), _⟩ : Ysub.toSubmodule)
      congr 2
      exact hF g y⟩
  have hπ : Function.Surjective π :=
    (Submodule.mkQ_surjective _).comp (LinearMap.surjective_rangeRestrict F)
  refine ⟨_, _, _, inferInstance, W.quotient, π, hQirr, hπ, ?_, fun J => ?_⟩
  ·
    let ι : N →+ (Ysub.toSubmodule ⧸ W.toSubmodule) :=
      { toFun := fun a => π (1 ⊗ₜ a)
        map_zero' := by rw [TensorProduct.tmul_zero, map_zero]
        map_add' := fun a b => by rw [TensorProduct.tmul_add, map_add] }
    have hι : Function.Injective ι := by
      rw [← AddMonoidHom.ker_eq_bot_iff ι]
      let S : Submodule (ZMod 2) N := AddSubgroup.toZModSubmodule 2 ι.ker
      have hS : ∀ g, ∀ a ∈ S, ρN g a ∈ S := by
        intro g a ha
        change ι (ρN g a) = 0
        change ι a = 0 at ha
        change π (1 ⊗ₜ ρN g a) = 0
        have : (1 : K) ⊗ₜ[ZMod 2] ρN g a = baseChangeRep (K := K) ρN g (1 ⊗ₜ a) := by
          rw [baseChangeRep_apply, LinearMap.baseChange_tmul]
        rw [this, show π (baseChangeRep (K := K) ρN g (1 ⊗ₜ a)) =
            W.quotient g (π (1 ⊗ₜ a)) from LinearMap.congr_fun (π.isIntertwining' g) _]
        change W.quotient g (ι a) = 0
        rw [ha, map_zero]
      rcases ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρN).mp hNirr).2 S hS
        with h | h
      · exact (AddSubgroup.toZModSubmodule 2).injective (h.trans (map_bot _).symm)
      · exfalso
        have hall : ∀ a, π (1 ⊗ₜ a) = 0 := fun a => by
          have : a ∈ S := h ▸ Submodule.mem_top
          exact this
        have hzero : ∀ y, π y = 0 := by
          intro y
          induction y using TensorProduct.induction_on with
          | zero => exact map_zero π
          | tmul c a =>
            have : c ⊗ₜ[ZMod 2] a = c • ((1 : K) ⊗ₜ[ZMod 2] a) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rw [this, map_smul, hall a, smul_zero]
          | add x y hx hy => rw [map_add, hx, hy, add_zero]
        have hne := ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff _).mp hQirr).1
        obtain ⟨x, hx⟩ := exists_ne (0 : Ysub.toSubmodule ⧸ W.toSubmodule)
        obtain ⟨y, rfl⟩ := hπ x
        exact hx (hzero y)
    haveI : Finite (Ysub.toSubmodule ⧸ W.toSubmodule) := Module.finite_of_finite K
    have hcard := Nat.card_le_card_of_injective ι hι
    rw [hNcard] at hcard
    have hY : Nat.card (Ysub.toSubmodule ⧸ W.toSubmodule) =
        Fintype.card K ^ finrank K (Ysub.toSubmodule ⧸ W.toSubmodule) := by
      haveI := Fintype.ofFinite (Ysub.toSubmodule ⧸ W.toSubmodule)
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K)]
    rw [hY] at hcard
    exact (Nat.pow_le_pow_iff_right (Fintype.one_lt_card (α := K))).mp hcard
  ·
    calc pat (W.quotient.comp block) J
        ≤ pat (Ysub.toRepresentation.comp block) J :=
          pat_quot_le (Ysub.toRepresentation.comp block) (subComp W block) J
      _ ≤ pat (ρM.comp block) J := pat_sub_le (ρM.comp block) (subComp Ysub block) J

theorem finrank_zmod_eq {n : ℕ} (hK : Fintype.card K = 2 ^ n) {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] [Finite N] (hNcard : Nat.card N = Fintype.card K ^ 8) :
    finrank (ZMod 2) N = 8 * n := by
  haveI := Fintype.ofFinite N
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := N)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hNcard, hK, ← pow_mul] at h
  have := Nat.pow_right_injective (le_refl 2) h
  omega

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
