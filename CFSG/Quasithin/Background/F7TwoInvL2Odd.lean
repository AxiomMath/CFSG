module

public import CFSG.Quasithin.Background.F7TwoInvL2OddSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentNative

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GorensteinWalter CFSG.PSL2Table
open BenderSuzuki.PFAppendixIII (IsInvolution)
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
  (native_semilinear_involution_conjugacy)
open scoped MatrixGroups

section Reduction

variable {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
  (hcard : 3 < Nat.card K)

theorem invAutGen_map_conj (g y : PGammaL2 K)
    (hy : InvAutGen (PSL2 K) (pGammaL2ToMulAutPSL2 K hK hcard y)) :
    InvAutGen (PSL2 K) (pGammaL2ToMulAutPSL2 K hK hcard (g * y * g⁻¹)) := by
  rw [map_mul, map_mul, map_inv]
  exact (InvAutGen.conj_iff _ _).1 hy

theorem invAutGen_of_isConj {x y : PGammaL2 K} (h : IsConj x y)
    (hy : InvAutGen (PSL2 K) (pGammaL2ToMulAutPSL2 K hK hcard y)) :
    InvAutGen (PSL2 K) (pGammaL2ToMulAutPSL2 K hK hcard x) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hx : x = c⁻¹ * y * c⁻¹⁻¹ := by rw [← hc]; group
  rw [hx]
  exact invAutGen_map_conj hK hcard c⁻¹ y hy

theorem invAutGen_pgl2_of_isConj {a b : PGL2 K} (h : IsConj a b)
    (hb : InvAutGen (PSL2 K) (pgl2InnerAutPSL2 K hK hcard b)) :
    InvAutGen (PSL2 K) (pgl2InnerAutPSL2 K hK hcard a) := by
  have h' := MonoidHom.map_isConj (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) h
  have := invAutGen_of_isConj hK hcard h' (by rwa [pGammaL2ToMulAutPSL2_inl])
  rwa [pGammaL2ToMulAutPSL2_inl] at this

theorem invAutGen_psl2_odd_of_nonsplit {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (hN : ∀ {ν : K} (hν : ¬ IsSquare ν),
      InvAutGen (PSL2 K) (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν)))) :
    ∀ φ : MulAut (PSL2 K), φ * φ = 1 → φ ≠ 1 → InvAutGen (PSL2 K) φ := by
  intro φ hφ2 hφ1
  obtain ⟨x, rfl⟩ := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard φ
  have hx2 : x * x = 1 :=
    pGammaL2ToMulAutPSL2_injective K hK hcard (by rw [map_mul, map_one]; exact hφ2)
  have hx1 : x ≠ 1 := fun h => hφ1 (by rw [h, map_one])
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard (odd_of_isOddPrimePower hK)
  by_cases hfield : x.right = 1
  · have hxa : SemidirectProduct.inl x.left = x := by
      simpa [hfield] using SemidirectProduct.inl_left_mul_inr_right x
    have ha2 : x.left * x.left = 1 := by
      have h : (SemidirectProduct.inl (x.left * x.left) : PGammaL2 K) =
          SemidirectProduct.inl 1 := by
        rw [map_mul, hxa, hx2, map_one]
      exact SemidirectProduct.inl_injective h
    have ha1 : x.left ≠ 1 := by
      intro h
      apply hx1
      rw [← hxa, h, map_one]
    have hainv : BenderSuzuki.PFAppendixIII.IsInvolution x.left :=
      ⟨ha1, by rw [pow_two]; exact ha2⟩
    have hchar : ringChar K ≠ 2 := fun h => h2 (by simpa using (ringChar.spec K 2).mpr (by rw [h]))
    obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hchar
    have hν0 := ne_zero_of_not_isSquare hν
    have hS0 : BenderSuzuki.PFAppendixIII.IsInvolution (pgl2S0 K) :=
      ⟨pgl2S0_ne_one h2, by rw [pow_two]; exact pgl2S0_mul_self⟩
    have hN0 : BenderSuzuki.PFAppendixIII.IsInvolution (N0 ν hν0) :=
      ⟨N0_ne_one ν hν0, by rw [pow_two]; exact N0_mul_self ν hν0⟩
    have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
    have hS0mem : pgl2S0 K ∈ commutator (PGL2 K) ↔ IsSquare (-1 : K) := by
      rw [hcomm, pgl2S0, pgl2_mk_mem_psl2_range_iff_det_isSquare, val_det_pgl2S0GL]
    have hN0mem : N0 ν hν0 ∈ commutator (PGL2 K) ↔ ¬ IsSquare (-1 : K) := by
      rw [hcomm]
      exact N0_mem_range_iff hν
    have hconj : IsConj x.left (pgl2S0 K) ∨ IsConj x.left (N0 ν hν0) := by
      by_cases hamem : x.left ∈ commutator (PGL2 K)
      · by_cases hε : IsSquare (-1 : K)
        · obtain ⟨g, -, hg⟩ :=
            pgl2_inner_involutions_conjugate hK hcard hamem hainv (hS0mem.2 hε) hS0
          exact Or.inl (isConj_iff.mpr ⟨g, hg⟩)
        · obtain ⟨g, -, hg⟩ :=
            pgl2_inner_involutions_conjugate hK hcard hamem hainv (hN0mem.2 hε) hN0
          exact Or.inr (isConj_iff.mpr ⟨g, hg⟩)
      · by_cases hε : IsSquare (-1 : K)
        · exact Or.inr (pgl2_outer_involutions_conjugate K hK hcard hainv hN0 hamem
            fun h => (hN0mem.1 h) hε)
        · exact Or.inl (pgl2_outer_involutions_conjugate K hK hcard hainv hS0 hamem
            fun h => hε (hS0mem.1 h))
    rw [← hxa, pGammaL2ToMulAutPSL2_inl]
    rcases hconj with h | h
    · exact invAutGen_pgl2_of_isConj hK hcard h (invAutGen_pgl2_split_involution hK hcard)
    · exact invAutGen_pgl2_of_isConj hK hcard h (hN hν)
  · have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
    obtain ⟨h, hh⟩ := native_semilinear_involution_conjugacy hK x hxord hfield
    have hσ2 : x.right * x.right = 1 := by simpa using congrArg SemidirectProduct.right hx2
    have hP : InvAutGen (PSL2 K)
        (pGammaL2ToMulAutPSL2 K hK hcard (SemidirectProduct.inr x.right)) := by
      rw [pGammaL2ToMulAutPSL2_inr]
      exact invAutGen_psl2FieldAut hK hcard x.right hfield hσ2
    have key := invAutGen_map_conj hK hcard (SemidirectProduct.inl h) _ hP
    rwa [← hh] at key

end Reduction

theorem invAutGen_psl2_odd {K : Type} [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    ∀ φ : MulAut (PSL2 K), φ * φ = 1 → φ ≠ 1 → InvAutGen (PSL2 K) φ := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    subst h0
    simp at h5
  have hKodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, hf, hK⟩
  have hcard : 3 < Nat.card K := by omega
  refine invAutGen_psl2_odd_of_nonsplit hKodd hcard hK fun {ν} hν => ?_
  by_cases h7 : Nat.card K = 7
  · exact invAutGen_pgl2_nonsplit_seven hKodd hcard h7 hν
  by_cases h9 : Nat.card K = 9
  · exact invAutGen_pgl2_nonsplit_nine hKodd hcard h9 hν
  exact invAutGen_pgl2_nonsplit_involution hKodd hcard h7 h9 hν

end CFSG.Quasithin.F7Two
