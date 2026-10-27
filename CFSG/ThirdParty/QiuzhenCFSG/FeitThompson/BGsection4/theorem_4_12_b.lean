module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_12_a

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 4.12(b) from BG Section 4 -/

section Main

open scoped FixedPoints

public theorem CFSG.theorem_4_12_b {R A : Type*} [Group R] [Finite R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    [MulDistribMulAction A R] (hcop : Nat.Coprime p (Nat.card A))
    (hmeta : IsMetacyclic R) :
    commutatorAction (A := A) (G := R) ⊔ fixedPointSubgroup A R = ⊤ ∧
      Disjoint (commutatorAction (A := A) (G := R)) (fixedPointSubgroup A R) := by
  have hRsolv : Group.IsSolvable R := by
    let : Group.IsNilpotent R := (Fact.out : IsPGroup p R).isNilpotent
    infer_instance
  have hcop' : Nat.Coprime (Nat.card A) (Nat.card R) := by
    obtain ⟨n, hn⟩ := (Fact.out : IsPGroup p R).exists_card_eq
    rw [hn]
    exact hcop.symm.pow_right n
  have hsup :
      fixedPointSubgroup A R ⊔ commutatorAction (A := A) (G := R) = ⊤ :=
    proposition_1_6_a (G := R) (A := A) hRsolv hcop'
  let H : Subgroup R := commutatorAction (A := A) (G := R)
  let : IsInvariant A R H := by
    simpa [H] using commutatorAction_isInvariant (G := R) (A := A)
  let : MulDistribMulAction A H := inferInstance
  have hHp : IsPGroup p H := (Fact.out : IsPGroup p R).to_subgroup H
  have hHsolv : Group.IsSolvable H := by
    let : Group.IsNilpotent H := hHp.isNilpotent
    infer_instance
  have hcopH : Nat.Coprime (Nat.card A) (Nat.card H) := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    rw [hn]
    exact hcop.symm.pow_right n
  have hcommH : IsMulCommutative H := by
    simpa [H] using theorem_4_12_a (R := R) (A := A) (p := p) hpodd hcop hmeta
  have hcomplH :
      IsCompl (fixedPointSubgroup A H) (commutatorAction (A := A) (G := H)) :=
    proposition_1_6_d (G := H) (A := A) hHsolv hcopH hcommH
  have hcomm₂_eq : commutatorAction₂ (A := A) (G := R) = H := by
    simpa [H] using proposition_1_6_b (G := R) (A := A) hRsolv hcop'
  have hmapH :
      (commutatorAction (A := A) (G := H)).map H.subtype = H := by
    calc
      (commutatorAction (A := A) (G := H)).map H.subtype
          = commutatorAction₂ (A := A) (G := R) := by
            simpa [H] using commutatorAction_map_subtype_eq_commutatorAction₂ (G := R) (A := A)
      _ = H := hcomm₂_eq
  have hcommH_top : commutatorAction (A := A) (G := H) = ⊤ := by
    apply eq_top_iff.2
    intro x _hx
    have hxmap : (x : R) ∈ (commutatorAction (A := A) (G := H)).map H.subtype := by
      rw [hmapH]
      exact x.2
    rcases (Subgroup.mem_map).1 hxmap with ⟨y, hy, hyx⟩
    have hy_eq_x : y = x := H.subtype_injective hyx
    simpa [hy_eq_x] using hy
  have hfixedH_bot : fixedPointSubgroup A H = ⊥ := by
    apply eq_bot_iff.2
    intro x hx
    have hxinf : x ∈ fixedPointSubgroup A H ⊓ commutatorAction (A := A) (G := H) := by
      exact ⟨hx, by simp [hcommH_top]⟩
    have hinf_bot :
        fixedPointSubgroup A H ⊓ commutatorAction (A := A) (G := H) = ⊥ :=
      (disjoint_iff).1 hcomplH.disjoint
    simpa [hinf_bot] using hxinf
  have hdisj : Disjoint H (fixedPointSubgroup A R) := by
    apply (disjoint_iff).2
    apply eq_bot_iff.2
    intro x hx
    rcases hx with ⟨hxH, hxF⟩
    have hxHfix : (⟨x, hxH⟩ : H) ∈ fixedPointSubgroup A H := by
      rw [FixedPoints.mem_subgroup]
      intro a
      ext
      have hxF' : ∀ a : A, a • x = x := by
        simpa [fixedPointSubgroup] using hxF
      exact hxF' a
    have hxHbot : (⟨x, hxH⟩ : H) ∈ (⊥ : Subgroup H) := by
      simpa [hfixedH_bot] using hxHfix
    have hxone : x = 1 := by
      have hxoneH : (⟨x, hxH⟩ : H) = 1 := by
        simpa using hxHbot
      exact congrArg H.subtype hxoneH
    simp [hxone]
  constructor
  · simpa [H, sup_comm] using hsup
  · simpa [H] using hdisj
