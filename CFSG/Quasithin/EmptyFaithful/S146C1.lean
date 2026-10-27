module

public import CFSG.Quasithin.EmptyFaithful.S146B0
public import CFSG.Quasithin.EmptyFaithful.S146R5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_pCoreOf_of_kbarIsL3Two {K : Subgroup G} (h : KbarIsL3Two K) :
    (pCoreOf 2 K).relIndex K = 168 := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card (KBar K) = 168 := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_succ]
  exact h1

theorem four_lt_relIndex_of_kbarIsL3Two {T H K : Subgroup G} (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (h : KbarIsL3Two K) :
    4 < (pCoreOf 2 H).relIndex T := by
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hT
  have hsub : IsSubnormal K H :=
    A4.subnormal_of_normal hKH ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK)
  have hKS : IsSylowTwoOf (T ⊓ K) K := isSylowTwoOf_inf_normal hT hKH (hT.1.trans hHK)
  have hOK : pCoreOf 2 K ≤ T ⊓ K := pCoreOf_two_le_of_isSylowTwoOf hKS
  have hQK : pCoreOf 2 H ⊓ K = pCoreOf 2 K := by
    refine le_antisymm ?_ (le_inf (A4.pCoreOf_le_of_subnormal 2 hsub) (pCoreOf_le 2 K))
    have hnorm : K ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ K : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 H (hKH hx), Subgroup.le_normalizer hx⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
      ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
  have h168 := relIndex_pCoreOf_of_kbarIsL3Two h
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 K) (T ⊓ K) K hOK inf_le_right
  have hodd : ¬ 2 ∣ (T ⊓ K).relIndex K := hKS.2.2
  have hr : (pCoreOf 2 K).relIndex (T ⊓ K) = 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hKS.2.1.exists_card_eq
    have hdvd : (pCoreOf 2 K).relIndex (T ⊓ K) ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.relIndex_dvd_card _ _
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hm, h168] at hmul
    have h2m : 2 ^ m ∣ 168 := ⟨(T ⊓ K).relIndex K, hmul.symm⟩
    have hm3 : m ≤ 3 := by
      by_contra hlt
      have h16 : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 (by omega : 4 ≤ m)).trans h2m
      norm_num at h16
    have hm3' : 3 ≤ m := by
      by_contra hlt
      have hm2 : m ≤ 2 := by omega
      interval_cases m <;> omega
    have : m = 3 := le_antisymm hm3 hm3'
    rw [hm, this]
    norm_num
  have hQK' : pCoreOf 2 H ⊓ (T ⊓ K) = pCoreOf 2 K := by
    rw [← inf_assoc, inf_eq_left.mpr hQT, hQK]
  have h1 : (pCoreOf 2 H).relIndex (T ⊓ K) = 8 := by
    rw [← Subgroup.inf_relIndex_right (pCoreOf 2 H) (T ⊓ K), hQK']
    exact hr
  have h2 : (pCoreOf 2 H).relIndex (T ⊓ K) ≤ (pCoreOf 2 H).relIndex T :=
    Subgroup.relIndex_le_of_le_right inf_le_left (relIndex_ne_zero_fin _ _)
  omega

end CFSG.Quasithin
