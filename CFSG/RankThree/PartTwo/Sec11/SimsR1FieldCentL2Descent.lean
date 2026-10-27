module

public import CFSG.RankThree.PartTwo.Sec11.Item116H3KFact
import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL2Fixed
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent

open scoped MatrixGroups
open CFSG.GorensteinWalter CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Assembly.RankThreeEven (projSL)

theorem nonempty_fixedSub_equiv_L2Odd {p e : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (he : 1 ≤ e)
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* projSL 2 (GaloisField p (3 * e))))
    {α : MulAut X} (hα : orderOf α = 3) (hαi : α ∉ (MulAut.conj : X →* MulAut X).range) :
    Nonempty (Sec11.fixedSub α ≃* projSL 2 (GaloisField p e)) := by
  obtain ⟨ψ0⟩ := hX
  set F := GaloisField p (3 * e) with hFdef
  let ψ : X ≃* PSL2 F := ψ0.trans (Sec4.projSLEquivPSL F)
  obtain ⟨α', hα'def⟩ : ∃ α' : MulAut (PSL2 F), α' = MulAut.congr ψ α := ⟨_, rfl⟩
  have hα'o : orderOf α' = 3 := by
    rw [hα'def, MulEquiv.orderOf_eq (MulAut.congr ψ) α, hα]
  have hα'3 : α' ^ 3 = 1 := by
    have h := pow_orderOf_eq_one α'
    rwa [hα'o] at h
  have hαi' : ¬ IsInnerAut α' := fun h =>
    hαi ((isInnerAut_congr ψ α).1 (hα'def ▸ h))
  have hD : α' ∉ (pglAction F).range := fun h =>
    hαi' (isInnerAut_of_mem_inndiag_of_pow_three (α := α') h hα'3)
  obtain ⟨σ, hσo, g, hg⟩ := linear_two_prime_order_field_descent Nat.prime_three α' hα'o hD
  obtain ⟨e1⟩ := L2.nonempty_fixedSub_equiv_of_compat ψ α α' (fun x => by
    rw [hα'def]
    simp [MulAut.congr_apply])
  obtain ⟨e2⟩ := L2.nonempty_fixedSub_equiv_of_compat ((pglAction F g)⁻¹ : MulAut (PSL2 F)) α'
    (psl2FieldAut F σ) (fun y => by
      rw [hg]
      simp [MulAut.mul_apply])
  have hFcard : Nat.card F = p ^ (3 * e) := GaloisField.card p (3 * e) (by omega)
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (Fact.out : p.Prime) (by omega : 1 ≤ 3 * e) hFcard
  obtain ⟨-, S, hSset, hScard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσo, Nat.mul_div_cancel_left e (by norm_num : 0 < 3)] at hScard
  have hσ1 : σ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σ
    rwa [hσo] at h
  have hσ3 : ∀ x, σ (σ (σ x)) = x := by
    intro x
    have h := congrArg (fun τ : F ≃+* F => τ x) hσ1
    simpa only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply] using h
  have hσfin : IsOfFinOrder σ := orderOf_pos_iff.mp (by rw [hσo]; norm_num)
  have hSσ : ∀ a, a ∈ S ↔ σ a = a := by
    intro a
    have h : a ∈ (S : Set F) ↔ a ∈ {a | ∀ τ ∈ Subgroup.zpowers σ, τ a = a} := by rw [hSset]
    simp only [SetLike.mem_coe, Set.mem_setOf_eq] at h
    rw [h]
    constructor
    · intro h1
      exact h1 σ (Subgroup.mem_zpowers σ)
    · intro h1 τ hτ
      have key : ∀ n : ℕ, (σ ^ n) a = a := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, RingAut.mul_apply, h1, ih]
      rw [← hσfin.mem_powers_iff_mem_zpowers] at hτ
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hτ
      exact key n
  obtain ⟨e3⟩ := L2.nonempty_psl2_equiv_fixedSub S σ hσ3 hSσ
  haveI : Finite S := Nat.finite_of_card_ne_zero (by
    rw [hScard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hcard : Fintype.card S = Fintype.card (GaloisField p e) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hScard,
      GaloisField.card p e (by omega)]
  let τ : S ≃+* GaloisField p e := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e1.trans (e2.trans (e3.symm.trans ((psl2RingEquiv τ).trans
    (Sec4.projSLEquivPSL (GaloisField p e)).symm)))⟩

end CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent
