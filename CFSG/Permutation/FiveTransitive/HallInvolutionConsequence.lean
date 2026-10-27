module

public import CFSG.Permutation.FiveTransitive.OddFourCorrection
public import CFSG.Permutation.FiveTransitive.OddFourInvolutionGeometry

public section

namespace CFSG

namespace FiveTransitive.Research.HallInvolutionConsequence

open Research.OddFourStabilizerLifts
open Research.OddFourCorrection
open Research.OddFourCentralizer
open Research.OddFourInvolutionGeometry
open Research.SharpFourDegreeCompletion

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem smul_base_of_setwisePermHom_eq
    (e : Fin 4 ↪ X)
    (w : baseSetwiseStabilizer (G := G) e)
    (sigma : Equiv.Perm (Fin 4))
    (hw : baseSetwisePermHom (G := G) e w =
      (baseRangeEquiv e).permCongrHom sigma) :
    ∀ i, (w : G) • e i = e (sigma i) := by
  intro i
  have hi := Equiv.Perm.congr_fun hw (baseRangeEquiv e i)
  have hiVal := congrArg Subtype.val hi
  change (w : G) • e i =
    (((baseRangeEquiv e).permCongrHom sigma)
      (baseRangeEquiv e i) : Set.range e) at hiVal
  simpa [baseRangeEquiv, Equiv.ofInjective_apply] using hiVal

theorem exists_single_double_involution_lifts
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    ∃ s d : G,
      s ^ 2 = 1 ∧ s ≠ 1 ∧ d ^ 2 = 1 ∧
      (∀ i, s • e i =
        e (Research.SharpFourBound.baseSingleSwap i)) ∧
      (∀ i, d • e i =
        e (Research.SharpFourBound.baseDoubleSwap i)) := by
  classical
  obtain ⟨u, v, huOrder, hvOrder, huvComm, huImage, hvImage⟩ :=
    exists_commuting_involution_lifts h4 e hodd
  have huData : u ^ 2 = 1 ∧ u ≠ 1 :=
    orderOf_eq_prime_iff.mp huOrder
  have hvData : v ^ 2 = 1 ∧ v ≠ 1 :=
    orderOf_eq_prime_iff.mp hvOrder
  let s : G := v
  let d : G := (u * v : baseSetwiseStabilizer (G := G) e)
  have hsTwo : s ^ 2 = 1 := congrArg Subtype.val hvData.1
  have hsNe : s ≠ 1 := by
    intro hs
    apply hvData.2
    apply Subtype.ext
    exact hs
  have hdTwoK : (u * v) ^ 2 = 1 := by
    rw [huvComm.mul_pow, huData.1, hvData.1, one_mul]
  have hdTwo : d ^ 2 = 1 := congrArg Subtype.val hdTwoK
  have hsImage : baseSetwisePermHom (G := G) e v =
      (baseRangeEquiv e).permCongrHom
        Research.SharpFourBound.baseSingleSwap := by
    change baseSetwisePermHom (G := G) e v =
      (baseRangeEquiv e).permCongrHom baseRightSwap at hvImage
    exact hvImage
  have hdImage : baseSetwisePermHom (G := G) e (u * v) =
      (baseRangeEquiv e).permCongrHom
        Research.SharpFourBound.baseDoubleSwap := by
    rw [map_mul, huImage, hvImage]
    change
      (baseRangeEquiv e).permCongrHom baseLeftSwap *
          (baseRangeEquiv e).permCongrHom baseRightSwap =
        (baseRangeEquiv e).permCongrHom
          Research.SharpFourBound.baseDoubleSwap
    exact (map_mul (baseRangeEquiv e).permCongrHom
      baseLeftSwap baseRightSwap).symm
  have hsbase := smul_base_of_setwisePermHom_eq e v
    Research.SharpFourBound.baseSingleSwap hsImage
  have hdbase := smul_base_of_setwisePermHom_eq e (u * v)
    Research.SharpFourBound.baseDoubleSwap hdImage
  exact ⟨s, d, hsTwo, hsNe, hdTwo, hsbase, hdbase⟩

private theorem involution_conjugate_doubleSwapLift_of_odd_stabilizer
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (g d : G) (hgTwo : g ^ 2 = 1) (hdTwo : d ^ 2 = 1)
    (hgNe : g ≠ 1)
    (hdbase : ∀ i, d • e i =
      e (Research.SharpFourBound.baseDoubleSwap i)) :
    ∃ q : G, q * g * q⁻¹ = d := by
  exact involution_conjugate_doubleSwapLift h4 hX e hodd
    (sameBaseInvolutionConjugacy_of_odd_pointwiseStabilizer e hodd)
    g d hgTwo hdTwo hgNe hdbase

theorem all_involutions_conjugate
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (g h : G) (hgTwo : g ^ 2 = 1) (hhTwo : h ^ 2 = 1)
    (hgNe : g ≠ 1) (hhNe : h ≠ 1) :
    ∃ q : G, q * g * q⁻¹ = h := by
  obtain ⟨s, d, hsTwo, hsNe, hdTwo, hsbase, hdbase⟩ :=
    exists_single_double_involution_lifts h4 e hodd
  obtain ⟨qg, hqg⟩ :=
    involution_conjugate_doubleSwapLift_of_odd_stabilizer
      h4 hX e hodd g d hgTwo hdTwo hgNe hdbase
  obtain ⟨qh, hqh⟩ :=
    involution_conjugate_doubleSwapLift_of_odd_stabilizer
      h4 hX e hodd h d hhTwo hdTwo hhNe hdbase
  refine ⟨qh⁻¹ * qg, ?_⟩
  calc
    (qh⁻¹ * qg) * g * (qh⁻¹ * qg)⁻¹ =
        qh⁻¹ * (qg * g * qg⁻¹) * qh := by group
    _ = qh⁻¹ * d * qh := by rw [hqg]
    _ = h := by
      rw [← hqh]
      group

theorem involution_fixedBy_ncard_eq_two_or_three
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (g : G) (hgTwo : g ^ 2 = 1) (hgNe : g ≠ 1) :
    (MulAction.fixedBy X g).ncard = 2 ∨
      (MulAction.fixedBy X g).ncard = 3 := by
  classical
  obtain ⟨s, d, hsTwo, hsNe, hdTwo, hsbase, hdbase⟩ :=
    exists_single_double_involution_lifts h4 e hodd
  obtain ⟨qg, hqg⟩ :=
    involution_conjugate_doubleSwapLift_of_odd_stabilizer
      h4 hX e hodd g d hgTwo hdTwo hgNe hdbase
  obtain ⟨qs, hqs⟩ :=
    involution_conjugate_doubleSwapLift_of_odd_stabilizer
      h4 hX e hodd s d hsTwo hdTwo hsNe hdbase
  have hfixEq : (MulAction.fixedBy X g).ncard =
      (MulAction.fixedBy X s).ncard := by
    calc
      (MulAction.fixedBy X g).ncard =
          (MulAction.fixedBy X d).ncard :=
        fixedBy_ncard_eq_of_conjugate g d qg hqg
      _ = (MulAction.fixedBy X s).ncard :=
        (fixedBy_ncard_eq_of_conjugate s d qs hqs).symm
  have he01 : e 0 ≠ e 1 := by
    intro heq
    exact (show (0 : Fin 4) ≠ 1 by decide) (e.injective heq)
  have hpair : ({e 0, e 1} : Set X) ⊆ MulAction.fixedBy X s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change s • e 0 = e 0
      rw [hsbase,
        show Research.SharpFourBound.baseSingleSwap 0 = 0 by decide]
    · change s • e 1 = e 1
      rw [hsbase,
        show Research.SharpFourBound.baseSingleSwap 1 = 1 by decide]
  have hlowerS : 2 ≤ (MulAction.fixedBy X s).ncard := by
    have hle := Set.ncard_le_ncard hpair
    simpa [Set.ncard_pair he01] using hle
  have hlower : 2 ≤ (MulAction.fixedBy X g).ncard := by
    rwa [hfixEq]
  have hupper : (MulAction.fixedBy X g).ncard ≤ 3 :=
    involution_fixedBy_ncard_le_three h4 e hodd g hgTwo hgNe
  omega

theorem single_double_centralizer_equation_of_odd_stabilizer
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 8 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (s d : G) (hsTwo : s ^ 2 = 1) (hdTwo : d ^ 2 = 1)
    (hsNe : s ≠ 1)
    (hsbase : ∀ i, s • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hdbase : ∀ i, d • e i =
      e (Research.SharpFourBound.baseDoubleSwap i)) :
    ((MulAction.fixedBy X s).ncard.descFactorial 2 *
        (Fintype.card X - (MulAction.fixedBy X s).ncard)) *
        Nat.card (centralizingBaseStabilizer e s) =
      ((Fintype.card X - (MulAction.fixedBy X s).ncard) *
        (Fintype.card X - (MulAction.fixedBy X s).ncard - 2)) *
        Nat.card (centralizingBaseStabilizer e d) := by
  exact single_double_centralizer_equation h4 hX e hodd
    (sameBaseInvolutionConjugacy_of_odd_pointwiseStabilizer e hodd)
    s d hsTwo hdTwo hsNe hsbase hdbase

end FiveTransitive.Research.HallInvolutionConsequence

end CFSG
