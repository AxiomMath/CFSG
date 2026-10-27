module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameWeyl
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase
public import CFSG.LocalAnalysis.StandardType.GGSpJoinWeylRank
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.SpFrame

open CFSG.StandardType CFSG.StandardType.SpJoin CFSG.LieType.Universal CFSG.LieType.RootSystem
  CoxeterSystem CFSG.LieType.Universal.Symplectic CFSG.Open
open Module
open scoped IsMulCommutative

theorem exists_frame_coords {G : Type*} [Group G] {Bs : Subgroup G} [Finite Bs] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hm : 1 ≤ m)
    (hrank : Nat.card Bs = p ^ (m + 1)) {A : Subgroup (MulAut ↥Bs)}
    (e : (coxeterMatrix (isFiniteType_cartanC (m + 1))).Group ≃* ↥A)
    (he : ∀ i : Fin (m + 1),
      ((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) : ↥A) :
          MulAut ↥Bs) ^ 2 = 1 ∧
        Nat.card {b : ↥Bs //
          ((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) : ↥A) :
            MulAut ↥Bs) b = b} * p = Nat.card Bs) :
    ∃ Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs, ∀ k : Fin (m + 1), ∀ a,
      ((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k) : ↥A) :
          MulAut ↥Bs) (Φ a) = Φ (spReflPerm (m + 1) p k a) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥Bs := hBs.1
  have hp2' : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hV : ∀ x : Additive ↥Bs, p • x = 0 := fun x => by
    apply Additive.toMul.injective
    show x.toMul ^ p = 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 x.toMul x.toMul.2
  letI : Module (ZMod p) (Additive ↥Bs) := AddCommGroup.zmodModule (n := p) hV
  haveI hfin : Module.Finite (ZMod p) (Additive ↥Bs) := Module.Finite.of_finite
  let lin : MulAut ↥Bs →* Module.End (ZMod p) (Additive ↥Bs) :=
    { toFun := fun φ => (MonoidHom.toAdditive φ.toMonoidHom).toZModLinearMap p
      map_one' := by ext x; rfl
      map_mul' := by intro φ ψ; ext x; rfl }
  have hlin_apply : ∀ (φ : MulAut ↥Bs) (x : Additive ↥Bs),
      lin φ x = Additive.ofMul (φ (Additive.toMul x)) := fun φ x => rfl
  have hlin_inj : Function.Injective lin := by
    intro φ ψ hφψ
    apply MulEquiv.ext
    intro b
    have h := congrArg (fun g : Module.End (ZMod p) (Additive ↥Bs) => g (Additive.ofMul b)) hφψ
    simp only [hlin_apply, toMul_ofMul] at h
    exact Additive.ofMul.injective h
  let ρ : (coxeterMatrix (isFiniteType_cartanC (m + 1))).Group →*
      Module.End (ZMod p) (Additive ↥Bs) := lin.comp (A.subtype.comp e.toMonoidHom)
  have hsub : Function.Injective (A.subtype.comp e.toMonoidHom) := by
    intro x y hxy
    exact e.injective (Subtype.val_injective hxy)
  have hρ : Function.Injective ρ := hlin_inj.comp hsub
  have hcardV : Nat.card (Additive ↥Bs) = p ^ Module.finrank (ZMod p) (Additive ↥Bs) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive ↥Bs)
    rw [Nat.card_zmod] at h
    exact h
  have hcardBs : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) (Additive ↥Bs) := by
    rw [← hcardV]
    exact (Nat.card_congr (Additive.toMul : Additive ↥Bs ≃ ↥Bs)).symm
  have hdim : Module.finrank (ZMod p) (Additive ↥Bs) = m + 1 := by
    apply Nat.pow_right_injective hp.two_le
    change p ^ Module.finrank (ZMod p) (Additive ↥Bs) = p ^ (m + 1)
    rw [← hcardBs, hrank]
  have hrefl : ∀ i, IsRefl
      (ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i)) := by
    intro i
    obtain ⟨hφ2, hφfix⟩ := he i
    refine IsRefl.of_finrank_eigenspace_one hp2' ?_ ?_
    · change lin (((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) :
            ↥A) : MulAut ↥Bs)) *
          lin (((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) :
            ↥A) : MulAut ↥Bs)) = 1
      rw [← map_mul, ← pow_two, hφ2, map_one]
    · let E₁ := Module.End.eigenspace
        (ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i)) 1
      haveI : Module.Finite (ZMod p) E₁ := Module.Finite.of_finite
      have hEcard : Nat.card E₁ = Nat.card {b : ↥Bs //
          (((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) : ↥A) :
            MulAut ↥Bs)) b = b} := by
        apply Nat.card_congr
        refine Equiv.subtypeEquiv Additive.toMul ?_
        intro b
        rw [Module.End.mem_eigenspace_iff, one_smul]
        have h : ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) b =
            Additive.ofMul
              ((((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) :
                ↥A) : MulAut ↥Bs)) (Additive.toMul b)) := by
          change lin
            (((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple i) :
              ↥A) : MulAut ↥Bs)) b = _
          rw [hlin_apply]
        rw [h]
        constructor
        · intro hb
          exact Additive.ofMul.injective (by rw [hb, ofMul_toMul])
        · intro hb
          rw [hb, ofMul_toMul]
      have hEcard2 : Nat.card E₁ = p ^ Module.finrank (ZMod p) E₁ := by
        have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := E₁)
        rw [Nat.card_zmod] at h
        exact h
      have hfix' : Module.finrank (ZMod p) E₁ + 1 =
          Module.finrank (ZMod p) (Additive ↥Bs) := by
        apply Nat.pow_right_injective hp.two_le
        change p ^ (Module.finrank (ZMod p) E₁ + 1) =
          p ^ Module.finrank (ZMod p) (Additive ↥Bs)
        rw [pow_succ, ← hEcard2, hEcard, hφfix]
        exact hcardBs
      exact hfix'
  obtain ⟨f, hf1, hf2⟩ := exists_frame (k := ZMod p) (V := Additive ↥Bs) hp2' hm hdim ρ hρ hrefl
  let Φ0 : (Fin (m + 1) → ZMod p) ≃ₗ[ZMod p] Additive ↥Bs := f.equivFun.symm
  let Φ : (Fin (m + 1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
    { toFun := fun a => Additive.toMul (Φ0 (fun i => Multiplicative.toAdd (a i)))
      invFun := fun b => fun i => Multiplicative.ofAdd (Φ0.symm (Additive.ofMul b) i)
      left_inv := by
        intro a
        funext i
        simp only [ofMul_toMul, LinearEquiv.symm_apply_apply, ofAdd_toAdd]
      right_inv := by
        intro b
        show Additive.toMul (Φ0 (fun i => Multiplicative.toAdd
          (Multiplicative.ofAdd (Φ0.symm (Additive.ofMul b) i)))) = b
        have h1 : (fun i => Multiplicative.toAdd
            (Multiplicative.ofAdd (Φ0.symm (Additive.ofMul b) i))) =
            Φ0.symm (Additive.ofMul b) := by
          funext i
          rw [toAdd_ofAdd]
        rw [h1, LinearEquiv.apply_symm_apply, toMul_ofMul]
      map_mul' := by
        intro a b
        have h : (fun i => Multiplicative.toAdd ((a * b) i)) =
            (fun i => Multiplicative.toAdd (a i)) +
              (fun i => Multiplicative.toAdd (b i)) := by
          funext i
          rw [Pi.mul_apply, toAdd_mul, Pi.add_apply]
        rw [h, map_add, toMul_add] }
  refine ⟨Φ, ?_⟩
  intro k a
  have hkey : ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k)
      (Φ0 (fun i => Multiplicative.toAdd (a i))) =
      Φ0 (fun i => Multiplicative.toAdd (spReflPerm (m + 1) p k a i)) := by
    by_cases hk : k.val + 1 < m + 1
    ·
      have hd : (fun i => Multiplicative.toAdd (spReflPerm (m + 1) p k a i)) =
          fun i => Multiplicative.toAdd (a (Equiv.swap k ⟨k.val + 1, hk⟩ i)) := by
        funext i
        rw [spReflPerm_of_lt (m + 1) p k hk]
        simp [coordPerm_apply, Equiv.symm_swap]
      have h1 : ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k)
          (Φ0 (fun i => Multiplicative.toAdd (a i))) =
          ∑ j, Multiplicative.toAdd (a j) • f (Equiv.swap k ⟨k.val + 1, hk⟩ j) := by
        rw [show Φ0 (fun i => Multiplicative.toAdd (a i)) =
            ∑ j, Multiplicative.toAdd (a j) • f j from Module.Basis.equivFun_symm_apply f _]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul, hf1 k hk j]
      have h2 : (∑ j, Multiplicative.toAdd (a j) • f (Equiv.swap k ⟨k.val + 1, hk⟩ j)) =
          ∑ t, Multiplicative.toAdd (a (Equiv.swap k ⟨k.val + 1, hk⟩ t)) • f t := by
        rw [← Equiv.sum_comp (Equiv.swap k ⟨k.val + 1, hk⟩)
          (fun t => Multiplicative.toAdd (a (Equiv.swap k ⟨k.val + 1, hk⟩ t)) • f t)]
        exact Finset.sum_congr rfl fun j _ => by rw [Equiv.swap_apply_self]
      rw [h1, hd, h2]
      exact (Module.Basis.equivFun_symm_apply f _).symm
    ·
      have hklast : k = Fin.last m := by
        apply Fin.ext
        have hkval : k.val = m := by
          have := k.isLt
          omega
        simp [Fin.last, hkval]
      have hd : (fun i => Multiplicative.toAdd (spReflPerm (m + 1) p k a i)) =
          Function.update (fun i => Multiplicative.toAdd (a i)) (Fin.last m)
            (- Multiplicative.toAdd (a (Fin.last m))) := by
        funext t
        rw [spReflPerm_of_not_lt (m + 1) p k hk, coordInv_apply, hklast]
        by_cases ht : t = Fin.last m
        · subst ht
          simp only [Function.update_self, toAdd_inv]
          rfl
        · rw [Function.update_of_ne ht, Function.update_of_ne ht]
      have h1 : ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k)
          (Φ0 (fun i => Multiplicative.toAdd (a i))) =
          ∑ j, Multiplicative.toAdd (a j) • (if j = Fin.last m then -f j else f j) := by
        rw [show Φ0 (fun i => Multiplicative.toAdd (a i)) =
            ∑ j, Multiplicative.toAdd (a j) • f j from Module.Basis.equivFun_symm_apply f _]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul, hklast, hf2 j]
      have hsum : (∑ j, Multiplicative.toAdd (a j) •
            (if j = Fin.last m then -f j else f j)) =
          ∑ j, (Function.update (fun i => Multiplicative.toAdd (a i)) (Fin.last m)
            (- Multiplicative.toAdd (a (Fin.last m)))) j • f j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = Fin.last m
        · subst hj
          rw [if_pos rfl, Function.update_self]
          have hneg : Multiplicative.toAdd (a (Fin.last m)) • (-f (Fin.last m)) =
              (-Multiplicative.toAdd (a (Fin.last m))) • f (Fin.last m) := by
            conv_lhs => rw [← neg_neg (Multiplicative.toAdd (a (Fin.last m)))]
            rw [neg_smul_neg]
            rfl
          exact hneg
        · rw [if_neg hj, Function.update_of_ne hj]
      rw [h1, hd, hsum]
      exact (Module.Basis.equivFun_symm_apply f _).symm
  have hstep :
      (((e ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k) : ↥A) :
        MulAut ↥Bs)) (Φ a) =
      Additive.toMul (ρ ((coxeterMatrix (isFiniteType_cartanC (m + 1))).toCoxeterSystem.simple k)
        (Φ0 (fun i => Multiplicative.toAdd (a i)))) := rfl
  rw [hstep, hkey]
  rfl

end CFSG.StandardType.SpFrame
