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

theorem omqnf_exists_conj_shapeC {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {y : spinGroup (quadMinus n K b c)} (hy : y * y = 1) (hy1 : y ≠ 1) {j : ℕ} (hj : Odd j)
    (hj2 : j ≤ n - 1)
    (hlet : suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) =
      SuzukiLetter.c)
    (hrank : finrank K (commSpace (spinAction (quadMinus n K b c) y)) = j + 1) :
    ∃ (g : spinGroup (quadMinus n K b c))
      (x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group)
      (π : Equiv.Perm (Fin (n - 1))) (s : Fin (n - 1) → ℤ),
      SpIsSign s ∧ omqnfRealizes (n - 1) x π s ∧
      (SmallO8mCurtis.curtisDatum n hn hirr).nW x = g * y * g⁻¹ ∧
      (π = 1 ∧ s ⟨0, by omega⟩ = -1 ∧
        Odd (Finset.univ.filter fun a => s a = -1).card) := by
  have hj1 : 1 ≤ j := hj.pos
  obtain ⟨x, hx⟩ := exists_omqnfRealizes_of_signedPerm (1 : Equiv.Perm (Fin (n - 1)))
    (omqnfSignC_isSign (n - 1) j)
  have hacts := omqnf_spinAction_nW hn hirr hx (omqnfSignC_isSign (n - 1) j)
  set T := spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) with hT
  have hσ := omqnf_spMonoPerm_mul_self_C (n - 1) j
  have hTT : T * T = 1 := hacts.mul_self_eq_one hσ
  have hprod : ∏ a, omqnfSignC (n - 1) j a = -1 := by
    rw [omqnfSignC_prod hj2]
    exact hj.neg_one_pow
  have hrk : finrank K (commSpace T) = j + 1 := by
    rw [omqnf_finrank_commSpace hirr hacts hσ, omqnf_support_card_C hj2, hprod]
    simp only [show ¬ ((-1 : ℤ) = 1) by norm_num, if_false]
    omega
  have h0 : omqnfSignC (n - 1) j ⟨0, by omega⟩ = -1 := omqnfSignC_zero hj1 hj2
  obtain ⟨x0, hx0, hQ⟩ := omqnf_nonvanish_of_flip h0 hacts
  have hlT : suzukiLetter (quadMinus n K b c) T = SuzukiLetter.c :=
    suzukiLetter_eq_c_iff.mpr ⟨by rw [hrk]; exact hj.add_one, x0, hx0, hQ⟩
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
    (fun h => by rw [hlet] at h; exact absurd h.1 (by decide))
    (z := (SmallO8mCurtis.curtisDatum n hn hirr).nW x) rfl
  exact ⟨g, x, 1, omqnfSignC (n - 1) j, omqnfSignC_isSign _ _, hx, hg.symm, rfl, h0,
    by rw [omqnfSignC_card hj2]; exact hj⟩

end CFSG.LocalAnalysis.WeakClosure81
