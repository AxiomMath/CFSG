module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenHeartNorm
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenComb10
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)
open CFSG.RankThree.PartTwo.Sec19.SolEven (NormalizerIsSym)

open CFSG.RankThree.PartTwo.Sec19.SolEven
open CFSG.HardMathSupport.Cooperstein.Coordinator

private theorem s16c167_altHeart_add_comm {n : ℕ} (a b : altHeart n) : a + b = b + a := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm]

private theorem s16c167_altHeart_add_self {n : ℕ} (a : altHeart n) : a + a = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← QuotientAddGroup.mk_add]
  have : x + x = 0 :=
    Subtype.ext (funext fun _ => (show ∀ c : ZMod 2, c + c = 0 by decide) _)
  rw [this, QuotientAddGroup.mk_zero]

private noncomputable instance s16c167_altHeartAddCommGroup {n : ℕ} :
    AddCommGroup (altHeart n) :=
  { (inferInstance : AddGroup (altHeart n)) with add_comm := s16c167_altHeart_add_comm }

theorem s16c167_normalizerIsSym_five : NormalizerIsSym 5 := by
  intro γ hγ
  obtain ⟨φ, hφ⟩ := exists_aut_of_normalizing (by norm_num : 5 ≤ 5) γ hγ
  obtain ⟨π, hπ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inl rfl) φ
  let δ : altHeart 5 →+ altHeart 5 := (altAct π⁻¹).comp γ.toAddMonoidHom
  have hδ : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, δ (altAct σ v) = altAct σ (δ v) := by
    intro σ hσ v
    show altAct π⁻¹ (γ (altAct σ v)) = altAct σ (altAct π⁻¹ (γ v))
    rw [hφ ⟨σ, hσ⟩ v, ← altAct_mul, ← altAct_mul, hπ ⟨σ, hσ⟩]
    congr 1
    group
  have hγπ : ∀ v, γ v = altAct π (δ v) := fun v => (altAct_apply_inv π (γ v)).symm
  rcases altHeart_endo_eq_zero_or_id (by norm_num : 5 ≤ 5) δ hδ with h0 | h1
  · exfalso
    obtain ⟨v, hv⟩ := altHeart_exists_ne_zero (n := 5) (by norm_num)
    refine hv (γ.injective ?_)
    rw [hγπ v, h0]
    simp
  · exact ⟨π, fun v => by rw [hγπ v, h1]; rfl⟩

theorem s16c167_normalizerIsSym {n : ℕ} (hn : 5 ≤ n) : NormalizerIsSym n := by
  rcases (by omega : n = 5 ∨ n = 6 ∨ 7 ≤ n) with rfl | rfl | h7
  · exact s16c167_normalizerIsSym_five
  · exact normalizerIsSym_six
  · exact normalizerIsSym_of_seven_le h7

theorem s16c167_altHeart_transvection_eq_swap {n : ℕ} (hn : 5 ≤ n)
    (t : altHeart n ≃+ altHeart n)
    (hnorm : ∀ σ ∈ alternatingGroup (Fin n), ∃ σ' ∈ alternatingGroup (Fin n),
      ∀ v, t (altAct σ v) = altAct σ' (t v))
    {K : AddSubgroup (altHeart n)} (hK : K.index = 2) (htK : ∀ v ∈ K, t v = v)
    (ht : ∀ v, t v - v ∈ K) (h1 : t ≠ AddEquiv.refl _) :
    ∃ σ : Equiv.Perm (Fin n), σ.IsSwap ∧ (∀ v, t v = altAct σ v) ∧
      ∀ v, altAct σ v = v ↔ v ∈ K := by
  obtain ⟨π, hπ⟩ := s16c167_normalizerIsSym hn t hnorm
  have hpair : ∀ u v : altHeart n, altAct π u - u ≠ 0 → altAct π v - v ≠ 0 →
      altAct π u - u = altAct π v - v := by
    intro u v hu hv
    have huK : u ∉ K := fun h => hu (by rw [← hπ u, htK u h, sub_self])
    have hvK : v ∉ K := fun h => hv (by rw [← hπ v, htK v h, sub_self])
    have huv : u + v ∈ K := by
      rw [AddSubgroup.add_mem_iff_of_index_two hK]
      exact ⟨fun h => absurd h huK, fun h => absurd h hvK⟩
    have hsum : t u + t v = u + v := by
      rw [← map_add, htK (u + v) huv]
    have hdiff : t u - u = t v - v := by
      have hneg : ∀ x : altHeart n, -x = x := fun x =>
        (eq_neg_of_add_eq_zero_left (s16c167_altHeart_add_self x)).symm
      rw [sub_eq_add_neg, sub_eq_add_neg, hneg u, hneg v]
      have hrearr : (t u + u) + (t v + v) = (t u + t v) + (u + v) := by abel
      have hA : (t u + u) + (t v + v) = 0 := by
        rw [hrearr, hsum]
        exact s16c167_altHeart_add_self _
      exact (eq_neg_of_add_eq_zero_left hA).trans
        (eq_neg_of_add_eq_zero_left (s16c167_altHeart_add_self (t v + v))).symm
    simpa only [hπ u, hπ v] using hdiff
  rcases Comb.eq_one_or_isSwap_of_commutator_eq hn hpair with hπ1 | hπswap
  · exfalso
    apply h1
    refine AddEquiv.ext fun v => ?_
    rw [hπ v, hπ1, altAct_one]
    rfl
  · refine ⟨π, hπswap, hπ, fun v => ?_⟩
    constructor
    · intro hv
      by_contra hvK
      have htv : t v = v := (hπ v).trans hv
      have ht_eq : t = AddEquiv.refl _ := by
        refine AddEquiv.ext fun u => ?_
        by_cases huK : u ∈ K
        · exact htK u huK
        · have huv : u + v ∈ K := by
            rw [AddSubgroup.add_mem_iff_of_index_two hK]
            exact ⟨fun h => absurd h huK, fun h => absurd h hvK⟩
          have hsum : t u + t v = u + v := by
            rw [← map_add, htK (u + v) huv]
          rw [htv] at hsum
          exact add_right_cancel hsum
      exact h1 ht_eq
    · intro hvK
      exact (hπ v).symm.trans (htK v hvK)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
