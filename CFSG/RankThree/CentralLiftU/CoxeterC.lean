module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRoots
import all CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherInvariant

public section

namespace CFSG.RankThree.CentralLiftU

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (simpleRefl)

variable {r : ℕ} {Q : Type*} [Group Q] {q : Fin r → Q}

private theorem isLiftable_coxeterC (hsq : ∀ i, q i * q i = 1)
    (hbraid : ∀ i j : Fin r, i.val + 1 = j.val → j.val + 1 < r →
      q j * q i * q j = q i * q j * q i)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → q i * q j = q j * q i)
    (hlong : ∀ i j : Fin r, i.val + 1 = j.val → ¬j.val + 1 < r →
      q i * q j * q i * (q i * q j * q i) = 1 ∧ q i * q j * q i * q j = q j * (q i * q j * q i)) :
    (CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r)).IsLiftable q := by
  have key : ∀ i j : Fin r, i < j → (q i * q j) ^
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r)) i j = 1 := by
    intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hadj : i.val + 1 = j.val
    · by_cases hj : j.val + 1 < r
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_short r hadj hj]
        exact pow_three_eq_one (hsq i) (hsq j) (hbraid i j hadj hj)
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_long r hadj hj]
        exact pow_four_eq_one (hsq j) (hlong i j hadj hj).1 (hlong i j hadj hj).2
    · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_far r hij.ne hadj (by omega)]
      exact pow_two_eq_one_of_commute (hsq i) (hsq j) (hfar i j (by omega))
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact key i j h
  · rw [CoxeterMatrix.diagonal, pow_one]
    exact hsq i
  · rw [CoxeterMatrix.symmetric]
    exact pow_eq_one_comm (key j i h)

theorem injective_of_coxeterC (hgen : Subgroup.closure (Set.range q) = ⊤)
    (hsq : ∀ i, q i * q i = 1)
    (hbraid : ∀ i j : Fin r, i.val + 1 = j.val → j.val + 1 < r →
      q j * q i * q j = q i * q j * q i)
    (hfar : ∀ i j : Fin r, i.val + 1 < j.val → q i * q j = q j * q i)
    (hlong : ∀ i j : Fin r, i.val + 1 = j.val → ¬j.val + 1 < r →
      q i * q j * q i * (q i * q j * q i) = 1 ∧ q i * q j * q i * q j = q j * (q i * q j * q i))
    (ψ : Q →* signedPermGroup r)
    (hψ : ∀ i, (ψ (q i) : Equiv.Perm (Fin r ⊕ Fin r)) = simpleRefl r i) :
    Function.Injective ψ := by
  set hA := CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r
  set cs := (CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem
  set L := cs.lift ⟨q, isLiftable_coxeterC hsq hbraid hfar hlong⟩ with hL
  have hsimple : ∀ i, epsAct ((ψ (L (cs.simple i)) : signedPermGroup r) :
      Equiv.Perm (Fin r ⊕ Fin r)) = CFSG.LieType.Universal.Symplectic.stdRefl r i := by
    intro i
    rw [hL, CoxeterSystem.lift_apply_simple, hψ]
    funext e
    unfold simpleRefl
    split_ifs with h
    · rw [epsAct_sumCongr_swap, CFSG.LieType.Universal.Symplectic.stdRefl_of_lt r h]
    · rw [epsAct_swap_inl_inr, CFSG.LieType.Universal.Symplectic.stdRefl_of_not_lt r h]
  have hact : ∀ w v, CFSG.LieType.Universal.Symplectic.toStd r
      (CFSG.LieType.RootSystem.weylAction hA w v) =
        epsAct (ψ (L w) : Equiv.Perm (Fin r ⊕ Fin r))
          (CFSG.LieType.Universal.Symplectic.toStd r v) := by
    intro w
    refine cs.simple_induction_left (p := fun w => ∀ v,
      CFSG.LieType.Universal.Symplectic.toStd r (CFSG.LieType.RootSystem.weylAction hA w v) =
        epsAct (ψ (L w) : Equiv.Perm (Fin r ⊕ Fin r))
          (CFSG.LieType.Universal.Symplectic.toStd r v)) w ?_ ?_
    · intro v
      rw [map_one, map_one, map_one]
      rfl
    · intro w i ih v
      rw [CFSG.LieType.RootSystem.weylAction_mul_apply,
        CFSG.LieType.RootSystem.weylAction_simple,
        CFSG.LieType.Universal.Symplectic.toStd_reflection, ih, map_mul, map_mul,
        Subgroup.coe_mul, epsAct_mul (ψ (L w)).2, hsimple]
  have hinj : ∀ w, ψ (L w) = 1 → w = 1 := by
    intro w hw
    apply CFSG.LieType.RootSystem.weylAction_injective hA
    rw [map_one]
    refine LinearMap.ext fun v => CFSG.LieType.Universal.Symplectic.toStd_injective r ?_
    rw [hact, hw, Module.End.one_apply]
    rfl
  have hsurj : Function.Surjective L := by
    have hle : Subgroup.closure (Set.range q) ≤ L.range := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨cs.simple i, CoxeterSystem.lift_apply_simple _ _ i⟩
    rw [hgen] at hle
    exact fun x => hle (Subgroup.mem_top x)
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨w, rfl⟩ := hsurj x
  rw [hinj w hx, map_one]

end CFSG.RankThree.CentralLiftU
