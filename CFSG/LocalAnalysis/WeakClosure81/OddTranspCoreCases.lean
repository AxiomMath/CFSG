module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmallCls
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStar
public import CFSG.OddTranspositions.PartThree.SixThreeGlobal
import CFSG.Goldschmidt75.OddCore
import CFSG.OddTranspositions.SevenThreeKind
import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def OddTranspCoreThreeTranspInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (t : Y), orderOf t = 2 →
    Subgroup.normalClosure ({t} : Set Y) = ⊤ →
    (∀ a b : Y, IsConj t a → IsConj t b → orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)) →
    fusionOddCore Y = ⊥ →
    (∃ n : ℕ, ∃ e : Y ≃* Equiv.Perm (Fin n), (e t).IsSwap) ∨
      ∃ e₁ e₂ e₃ : Y, IsConj t e₁ ∧ IsConj t e₂ ∧ IsConj t e₃ ∧
        orderOf (t * e₁) = 3 ∧ orderOf (t * e₂) = 3 ∧ orderOf (t * e₃) = 3 ∧
        e₁ * e₂ = e₂ * e₁ ∧ e₁ * e₃ = e₃ * e₁ ∧ e₂ * e₃ = e₃ * e₂ ∧
        e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃

@[expose] def OddTranspCoreRadicalInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    ¬ fusionOddCore X ≤ Subgroup.center X →
    (CFSG.solvableRadical X).map (QuotientGroup.mk' (fusionOddCore X)) ≤
      Subgroup.center (X ⧸ fusionOddCore X) →
    ¬ (∀ d e : X, IsConj s d → IsConj s e →
      orderOf (QuotientGroup.mk' (fusionOddCore X) d * QuotientGroup.mk' (fusionOddCore X) e) ∈
        ({1, 2, 3} : Set ℕ)) →
    (∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ Lh ∧
        ¬ Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s) ≤ pCoreOf 2 Lh ∧
        (⨆ (y : X ⧸ fusionOddCore X)
            (_ : conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y ≤ Lh),
            conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) y) = Lh ∧
        HasQuotShape Lh (pCoreOf 2 Lh : Set (X ⧸ fusionOddCore X)) (fun Y _ => IsSymGp Y 3) ∧
        4 ≤ Set.ncard {W : Subgroup (X ⧸ fusionOddCore X) | ∃ x ∈ pCoreOf 2 Lh,
            W = conjSubgroup (Subgroup.zpowers (QuotientGroup.mk' (fusionOddCore X) s)) x}) ∨
      ∃ Lh : Subgroup (X ⧸ fusionOddCore X),
        ∃ hsLh : QuotientGroup.mk' (fusionOddCore X) s ∈ Lh,
        Subgroup.normalClosure ({⟨_, hsLh⟩} : Set ↥Lh) = ⊤ ∧
        ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥Lh ⧸ fusionZStar ↥Lh) n

theorem oddTranspositionCoreInputSCCls_of_cases (hI : OddTranspCoreThreeTranspInput)
    (hII : OddTranspCoreRadicalInput) : OddTranspositionCoreInputSCCls := by
  intro X _ _ s hord hodd hncl hO2 hOZ
  classical
  set π := QuotientGroup.mk' (fusionOddCore X) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hS : CFSG.Timmesfeld.Bridge.Asc72.Setup X {x : X | IsConj s x} :=
    ⟨⟨s, rfl⟩, hodd, by
      have h := CFSG.Timmesfeld.CorB.normalClosure_eq s
      rw [hncl] at h
      exact h.symm⟩
  by_cases h3 : ∀ d e : X, IsConj s d → IsConj s e → orderOf (π d * π e) ∈ ({1, 2, 3} : Set ℕ)
  ·
    have hss : s * s = 1 := by rw [← pow_two, ← hord, pow_orderOf_eq_one]
    have hπs1 : π s ≠ 1 := by
      intro h
      have hmem : s ∈ fusionOddCore X := (QuotientGroup.eq_one_iff s).mp h
      have hodd' : Odd (Nat.card (fusionOddCore X)) := CFSG.Goldschmidt75.odd_card_oddCore
      have h1 : s = 1 :=
        CFSG.Goldschmidt75.eq_one_of_mem_odd_of_two_power hodd' hmem (k := 1) (by
          rw [pow_one, ← hord, pow_orderOf_eq_one])
      rw [h1, orderOf_one] at hord
      exact absurd hord (by decide)
    have hord' : orderOf (π s) = 2 :=
      orderOf_eq_prime (by rw [← map_pow, pow_two, hss, map_one]) hπs1
    have hncl' : Subgroup.normalClosure ({π s} : Set (X ⧸ fusionOddCore X)) = ⊤ := by
      rw [← Set.image_singleton, ← Subgroup.map_normalClosure _ π hπsurj, hncl,
        Subgroup.map_top_of_surjective π hπsurj]
    have hlift : ∀ a : X ⧸ fusionOddCore X, IsConj (π s) a → ∃ d : X, IsConj s d ∧ π d = a := by
      intro a ha
      obtain ⟨c, rfl⟩ := isConj_iff.mp ha
      obtain ⟨c', rfl⟩ := hπsurj c
      exact ⟨c' * s * c'⁻¹, isConj_iff.mpr ⟨c', rfl⟩, by simp⟩
    have h3' : ∀ a b : X ⧸ fusionOddCore X, IsConj (π s) a → IsConj (π s) b →
        orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ) := by
      intro a b ha hb
      obtain ⟨d, hd, rfl⟩ := hlift a ha
      obtain ⟨e, he, rfl⟩ := hlift b hb
      exact h3 d e hd he
    have hY : fusionOddCore (X ⧸ fusionOddCore X) = ⊥ := CFSG.Goldschmidt75.oddCore_quotient_eq_bot
    rcases hI (X ⧸ fusionOddCore X) (π s) hord' hncl' h3' hY with ⟨n, e, he⟩ |
        ⟨e₁, e₂, e₃, k₁, k₂, k₃, o₁, o₂, o₃, c₁₂, c₁₃, c₂₃, n₁₂, n₁₃, n₂₃⟩
    · exact Or.inl ⟨n, e, he⟩
    · right
      left
      have htt : π s * π s = 1 := by rw [← map_mul, hss, map_one]
      have hsq : ∀ x : X ⧸ fusionOddCore X, IsConj (π s) x → x * x = 1 := by
        intro x hx
        obtain ⟨c, rfl⟩ := isConj_iff.mp hx
        rw [show c * π s * c⁻¹ * (c * π s * c⁻¹) = c * (π s * π s) * c⁻¹ by group, htt, mul_one,
          mul_inv_cancel]
      have hbr : ∀ x : X ⧸ fusionOddCore X, IsConj (π s) x → orderOf (π s * x) = 3 →
          π s * x * π s = x * π s * x := fun x hx h =>
        (CFSG.OddTranspositions.conj_eq_of_orderOf_mul_eq_three htt (hsq x hx) h).symm
      have hne : π s ≠ e₁ := by
        intro h
        rw [← h, htt, orderOf_one] at o₁
        exact absurd o₁ (by decide)
      exact CoreStar.configB_of_star htt (hsq e₁ k₁) (hsq e₂ k₂) (hsq e₃ k₃) (hbr e₁ k₁ o₁)
        (hbr e₂ k₂ o₂) (hbr e₃ k₃ o₃) c₁₂ c₁₃ c₂₃ hne n₁₂ n₁₃ n₂₃ k₁ k₂ k₃
  ·
    rcases CFSG.OddTranspositions.PartThree.sixThree hS with h1 | h2 | h3''
    · exact absurd (fun d e hd he => h1 d hd e he) h3
    · exact Or.inr (hII X s hord hodd hncl hO2 hOZ h2 h3)
    · exact absurd h3'' hOZ

end CFSG.LocalAnalysis.WeakClosure81
