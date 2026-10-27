module

public import CFSG.Quasithin.AppendixH.H11.InvolutionRank

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem two_mul_rk_lt_rkIdx_of_isQuadratic [Finite V]
    (hLM : IsOver L M) (h : M12Ten L ⊤ ⊥) {A : Subgroup (MulAut V)} (hAM : A ≤ M)
    (hAe : IsElemAbelian2 A) (hne : A ≠ ⊥) (hq : IsQuadratic A) :
    2 * rk ↥A < rkIdx (fixV A) := by
  obtain ⟨e, he⟩ := m12_std h
  have hc := CFSG.Quasithin.B45Mat.card_eq_two_pow_rk hAe
  have hk := m12_card_le hLM h hAM hAe hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psi12 rhoC12_m24Pair_injective phi12
    (T12s2.toSub_injective _ _) card_T12s2 (fun _ h1 h2 => T12s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos12s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 4 [] CFSG.Quasithin.B45Mat.quad_searches.2.2.2.2 _ hk)) e
    (map_le_of_normalizer hLM he normalizer_rhoC12 hAM) hAe hc
  exact CFSG.Quasithin.B45Mat.lt_of_predQ hpred (chainAct12 e g) hchain
    (chainAut_injective rhoC12_m24Pair_injective (T12s2.toSub_injective _ _) g) hind
    (CFSG.Quasithin.B45Mat.ne_nil_of_chainSub hchain hne)
    ((isQuadratic_iff_commSeries_two A).mp hq)

theorem rk_eq_two_and_four_lt_rkIdx_of_isQuadratic [Finite V] [Finite (MulAut V)]
    (c : NativeCoords L) (hV : ∀ v : V, v ^ 2 = 1) (hLM : IsOver L M)
    (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥) (h : M12Ten L ⊤ ⊥)
    {A : Subgroup (MulAut V)} (hAM : A ≤ M) (hnc : ¬ IsCyclic ↥A) (hq : IsQuadratic A) :
    rk ↥A = 2 ∧ 4 < rkIdx (fixV A) := by
  have hAe : IsElemAbelian2 A := isElemAbelian2_of_isQuadratic hV hq
  have hne : A ≠ ⊥ := by
    intro hbot
    exact hnc (by rw [hbot]; infer_instance)
  have h2 := two_mul_rk_lt_rkIdx_of_isQuadratic hLM h hAM hAe hne hq
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha2 : (a : MulAut V) ^ 2 = 1 := hAe.2 (a : MulAut V) a.2
  have ha1 : (a : MulAut V) ≠ 1 := fun h => ha (Subtype.ext (by simpa using h))
  have hord : orderOf (a : MulAut V) = 2 := orderOf_eq_prime ha2 ha1
  have h4a := four_le_rkIdx_of_mem_M_of_orderOf_eq_two c hV hLM hC (hAM a.2) hord
  have hle := rkIdx_zpowers_le_rk_fixV_of_isQuadratic hV hq a.2
  have hfix4 : 4 ≤ rk ↥(fixV A) := le_trans h4a hle
  have hcardV : Nat.card V = 2 ^ 10 := card_V_of_nativeCoords c
  have hrkV : rk V = 10 := by
    unfold rk
    rw [hcardV, padicValNat.prime_pow]
  have hsum : rk ↥(fixV A) + rkIdx (fixV A) = 10 := by
    rw [rk_add_rkIdx (fixV A), hrkV]
  have hidx_le : rkIdx (fixV A) ≤ 6 := by omega
  have hA_le : rk ↥A ≤ 2 := by omega
  have hA_ge : 2 ≤ rk ↥A := by
    by_contra hlt
    push Not at hlt
    have hcardA : Nat.card A = 2 ^ rk ↥A := CFSG.Quasithin.B45Mat.card_eq_two_pow_rk hAe
    have hdvd : Nat.card A ∣ 2 := by
      rw [hcardA]
      have h0 : rk ↥A = 0 ∨ rk ↥A = 1 := by omega
      rcases h0 with h0 | h0 <;> rw [h0] <;> norm_num
    exact hnc (isCyclic_of_card_dvd_prime hdvd)
  have hrk : rk ↥A = 2 := le_antisymm hA_le hA_ge
  refine ⟨hrk, ?_⟩
  rw [hrk] at h2
  omega

end CFSG.Quasithin.AppendixH.H11
