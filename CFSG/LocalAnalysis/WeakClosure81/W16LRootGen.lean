module

public import CFSG.LocalAnalysis.WeakClosure81.W16LRootLine
public import CFSG.LocalAnalysis.WeakClosure81.W16LRootComb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

variable {P : Type} [Group P] [Finite P] {n : ℕ}

section Certified


theorem IsPSUGp.exists_sylowCenter_sup_eq_top (hP : IsPSUGp P 3 n) {Q Q' : Sylow 2 P}
    (hne : Q ≠ Q') : ∃ Q'' : Sylow 2 P, sylowCenter Q ⊔ sylowCenter Q' ⊔ sylowCenter Q'' = ⊤ := by
  haveI : Finite (Sylow 2 P) :=
    Finite.of_injective (SetLike.coe : Sylow 2 P → Set P) SetLike.coe_injective
  have hn2 : 2 ≤ n := two_le_of_isPSUGp hP
  have hq1 : 1 < 2 ^ n := one_lt_pow' (by norm_num) (by omega)
  have hlt : 2 ^ n + 1 < (2 ^ n) ^ 3 + 1 := by
    have h : 2 ^ n < (2 ^ n) ^ 3 := by
      calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
        _ < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right hq1 (by norm_num)
    omega
  obtain ⟨Q'', hQ''⟩ : ∃ Q'' : Sylow 2 P, Q'' ∉ psuRootLine Q Q' := by
    by_contra hcontra
    rw [not_exists] at hcontra
    have hmem : ∀ x : Sylow 2 P, x ∈ psuRootLine Q Q' := fun x => by
      by_contra hx
      exact hcontra x hx
    have huniv : psuRootLine Q Q' = Set.univ := Set.eq_univ_of_forall hmem
    have hcardLine : (psuRootLine Q Q').ncard = 2 ^ n + 1 := hP.ncard_psuRootLine hne
    have hcardSylow : Nat.card (Sylow 2 P) = (2 ^ n) ^ 3 + 1 := hP.isU3Shape.card_sylow
    have heq : 2 ^ n + 1 = (2 ^ n) ^ 3 + 1 := by
      rw [← hcardLine, huniv, Set.ncard_univ, hcardSylow]
    omega
  let H : Subgroup P := sylowCenter Q ⊔ sylowCenter Q' ⊔ sylowCenter Q''
  let S : Set (Sylow 2 P) := {x | sylowCenter x ≤ H}
  have hSuniv : S = Set.univ :=
    w16l_eq_univ_of_line_closed (Ω := Sylow 2 P) (q := 2 ^ n)
      hP.isU3Shape.card_sylow (psuRootLine (X := P))
      (fun x y _ => mem_psuRootLine_left x y)
      (fun x y _ => mem_psuRootLine_right x y)
      (fun x y hxy => hP.ncard_psuRootLine hxy)
      (fun x y z w hxy hz hw hzw => hP.psuRootLine_eq_of_mem hxy hz hw hzw)
      (S := S) (fun x hx y hy _ z hz => by
        show sylowCenter z ≤ H
        exact le_trans hz (sup_le hx hy))
      (a := Q) (b := Q') (c := Q'')
      (by show sylowCenter Q ≤ H; exact le_trans le_sup_left le_sup_left)
      (by show sylowCenter Q' ≤ H; exact le_trans le_sup_right le_sup_left)
      (by show sylowCenter Q'' ≤ H; exact le_sup_right)
      hne hQ''
  let N : Subgroup P := ⨆ x : Sylow 2 P, sylowCenter x
  have hNleH : N ≤ H := by
    refine iSup_le (fun x => ?_)
    change x ∈ S
    rw [hSuniv]
    exact Set.mem_univ x
  have hNnormal : N.Normal := by
    refine ⟨fun y hy g => ?_⟩
    refine Subgroup.iSup_induction (fun x : Sylow 2 P => sylowCenter x)
      (C := fun t => g * t * g⁻¹ ∈ N) hy ?_ ?_ ?_
    · intro i y hyi
      obtain ⟨i', -, hi'⟩ := sylowCenter_conj_exists i g⁻¹
      refine Subgroup.mem_iSup_of_mem i' ?_
      rw [hi']
      refine (mem_conjSubgroup_iff (A := sylowCenter i) (g := g⁻¹)
        (x := g * y * g⁻¹)).mpr ?_
      rw [show g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y by group]
      exact hyi
    · simpa using N.one_mem
    · intro a b ha hb
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact N.mul_mem ha hb
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hle : sylowCenter Q ≤ (⊥ : Subgroup P) := by
      rw [← hbot]
      exact le_iSup (fun x : Sylow 2 P => sylowCenter x) Q
    have hEqBot : sylowCenter Q = ⊥ := le_bot_iff.mp hle
    have hcard : Nat.card (sylowCenter Q) = 2 ^ n := hP.isU3Shape.card_sylowCenter Q
    rw [hEqBot, Subgroup.card_bot] at hcard
    omega
  have hsimple : IsSimpleGroup P :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity P 3 2 n
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hP)).2
  have hNtop : N = ⊤ := by
    letI : N.Normal := hNnormal
    exact (hsimple.eq_bot_or_eq_top_of_normal N).resolve_left hNne
  have hHtop : H = ⊤ := by
    rw [hNtop] at hNleH
    exact top_le_iff.mp hNleH
  exact ⟨Q'', by rw [← hHtop]⟩

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
