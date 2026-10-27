module

public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHModule
public import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH

variable {K S : Type} [Group K] [Group S]

theorem map_eq_of_invariant {ρ : K →* MulAut S} {N : Subgroup S}
    (hN : ∀ k : K, ∀ n ∈ N, ρ k n ∈ N) (k : K) :
    N.map ((ρ k : MulAut S) : S →* S) = N := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact hN k n hn
  · intro hx
    refine ⟨ρ k⁻¹ x, hN k⁻¹ x hx, ?_⟩
    show ρ k (ρ k⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

@[expose] noncomputable def quotAct (ρ : K →* MulAut S) (N : Subgroup S) [N.Normal]
    (hN : ∀ k : K, ∀ n ∈ N, ρ k n ∈ N) : K →* MulAut (S ⧸ N) where
  toFun k := QuotientGroup.congr N N (ρ k) (map_eq_of_invariant hN k)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H u => simp [QuotientGroup.congr_mk]
  map_mul' := by
    intro a b
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H u => simp [QuotientGroup.congr_mk]

theorem quotAct_mk (ρ : K →* MulAut S) (N : Subgroup S) [N.Normal]
    (hN : ∀ k : K, ∀ n ∈ N, ρ k n ∈ N) (k : K) (u : S) :
    quotAct ρ N hN k (u : S ⧸ N) = ((ρ k u : S) : S ⧸ N) := by
  simp [quotAct, QuotientGroup.congr_mk]

theorem fpf_quot [Finite S] {ρ : K →* MulAut S} (hρ : Fpf ρ) (N : Subgroup S) [N.Normal]
    (hN : ∀ k : K, ∀ n ∈ N, ρ k n ∈ N) (h3 : ¬ 3 ∣ Nat.card N) : Fpf (quotAct ρ N hN) := by
  intro y hy3 hy1 q hq
  induction q using QuotientGroup.induction_on with
  | H u =>
    rw [quotAct_mk, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at hq
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3' : ρ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    obtain ⟨v, hv, hfix⟩ := CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_lift
      (ρ y) h3' N inferInstance (hN y) h3 u hq
    have hv1 : v = 1 := hρ y hy3 hy1 v hfix
    rw [hv1, one_mul] at hv
    rw [QuotientGroup.eq_one_iff]
    simpa using inv_mem hv

end CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH
