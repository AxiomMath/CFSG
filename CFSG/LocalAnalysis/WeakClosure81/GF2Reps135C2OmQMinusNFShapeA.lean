module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeylEx
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFNW
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFRank
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFVanish
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFClass

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem
open CFSG.StandardType CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omqnf_exists_conj_shapeA {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {y : spinGroup (quadMinus n K b c)} (hy : y * y = 1) (hy1 : y ≠ 1) {r : ℕ} (hr1 : 1 ≤ r)
    (hr2 : 2 * r ≤ n - 1)
    (hlet : suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) =
      SuzukiLetter.a)
    (hrank : finrank K (commSpace (spinAction (quadMinus n K b c) y)) = 2 * r) :
    ∃ (g : spinGroup (quadMinus n K b c))
      (x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group)
      (π : Equiv.Perm (Fin (n - 1))) (s : Fin (n - 1) → ℤ),
      SpIsSign s ∧ omqnfRealizes (n - 1) x π s ∧
      (SmallO8mCurtis.curtisDatum n hn hirr).nW x = g * y * g⁻¹ ∧
      ((∀ a, s a = 1) ∧ π * π = 1 ∧ π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
        π ⟨1, by omega⟩ = ⟨0, by omega⟩) := by
  obtain ⟨x, hx⟩ := exists_omqnfRealizes_of_signedPerm (omqnfPermA (n - 1) r)
    (spIsSign_one (m := n - 1))
  have hacts := omqnf_spinAction_nW hn hirr hx (spIsSign_one (m := n - 1))
  set T := spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) with hT
  have hσ := omqnf_spMonoPerm_mul_self_A (n - 1) r
  have hTT : T * T = 1 := hacts.mul_self_eq_one hσ
  have hrk : finrank K (commSpace T) = 2 * r := by
    rw [omqnf_finrank_commSpace hirr hacts hσ, omqnf_support_card_A hr2]
    simp only [Pi.one_apply, Finset.prod_const_one, if_true]
    omega
  have hvan := omqnf_vanish_of_involution (omqnfPermA_mul_self _ r) hacts
  have hlT : suzukiLetter (quadMinus n K b c) T = SuzukiLetter.a :=
    suzukiLetter_eq_a_iff.mpr ⟨⟨r, by omega⟩, hvan⟩
  have hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    exact map_spinAction (quadMinus n K b c) _ v
  have hT1 : T ≠ 1 := by
    intro h
    have h0 : commSpace (1 : Vm n K ≃ₗ[K] Vm n K) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
      simp
    rw [h, h0, finrank_bot] at hrk
    omega
  have hT2 : orderOf T = 2 := orderOf_eq_prime (by rw [pow_two]; exact hTT) hT1
  obtain ⟨g, hg⟩ := omqnf_exists_conj_of_spinAction_eq hn hirr hy hy1 hTO hT2
    (hlT.trans hlet.symm) (hrk.trans hrank.symm)
    (fun h => by have := h.2; omega) (z := (SmallO8mCurtis.curtisDatum n hn hirr).nW x) rfl
  exact ⟨g, x, _, 1, spIsSign_one, hx, hg.symm, fun a => rfl, omqnfPermA_mul_self _ _,
    omqnfPermA_zero hr1 hr2, omqnfPermA_one hr1 hr2⟩

end CFSG.LocalAnalysis.WeakClosure81
