module

public import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Frame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a m : ℕ}

theorem oTwoUpper_le_pCoreOf_of_isL2
    (hF : Hyp111 L1 L2 S)
    (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S) (hm : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {Y : Subgroup G} (hYQ : Y ≤ Q2 L1 L2 S)
    (hYn : L2 ⊔ S ≤ Subgroup.normalizer (Y : Set G))
    (hYc : ⁅Y, oTwoUpper (L2 ⊔ S)⁆ = ⊥) {s : G} (hs : s ∈ S)
    (hsQ : s ∉ Q2 L1 L2 S)
    (hc : ∀ x ∈ Q2 L1 L2 S, x * s * x⁻¹ * s⁻¹ ∈ Y) :
    oTwoUpper (L2 ⊔ S) ≤ Q2 L1 L2 S := by
  set H : Subgroup G := L2 ⊔ S with hH
  set Q : Subgroup G := Q2 L1 L2 S with hQ
  have hQ2S : Q ≤ S := by
    rw [hQ]
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hQH : Q ≤ H := by
    rw [hH]
    exact hQ2S.trans le_sup_right
  have hHP2 : H ≤ P2 L1 L2 S := by
    rw [hH]
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hQN : H ≤ Subgroup.normalizer (Q : Set G) := by
    refine hHP2.trans ?_
    rw [hQ]
    exact le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hpCore : pCoreOf 2 H = Q := by
    rw [hH, hQ, sup_eq_of_S_eq_right hS2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hQ2 : IsPGroup 2 Q := hpCore ▸ pCoreOf_isPGroup 2 H
  have hsimple : IsSimpleGroup (oTwoQuot ↥H) := by
    rw [hH]
    exact isSimpleGroup_oTwoQuot_sup_right_of_isL2Quot hF hS2 hm hL2
  have hM4 : ∀ K : Subgroup G, K ≤ H →
      H ≤ Subgroup.normalizer (K : Set G) → Q ≤ K →
      K = H ∨ ∀ k ∈ K, (∃ n : ℕ, k ^ (2 ^ n) = 1) → k ∈ Q := by
    intro K hKH hKn hQK
    have h := eq_or_mem_pCoreOf_of_normal_of_isSimple hsimple hKH hKn
      (by simpa [hpCore] using hQK)
    rwa [hpCore] at h
  have hCQ : H ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    rw [hH, hQ]
    exact inf_centralizer_pCoreOf_right_of_hyp111 hF
  have hsH : s ∈ H := (le_sup_right : S ≤ H) hs
  have hs2 : ∃ n : ℕ, s ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hF.h2.pgroup.exists_pow_pow_eq_one ⟨s, hs⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hres := oTwoUpper_le_of_lemmaT hQH hQN hQ2 hM4 hCQ hYQ hYn hYc
    hsH hs2 hsQ hc
  rwa [hH, hQ] at hres

theorem false_of_commutator_le_of_isL2
    (hF : Hyp111 L1 L2 S)
    (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S) (hm : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {Y : Subgroup G} (hYQ : Y ≤ Q2 L1 L2 S)
    (hYn : L2 ⊔ S ≤ Subgroup.normalizer (Y : Set G))
    (hYc : ⁅Y, oTwoUpper (L2 ⊔ S)⁆ = ⊥) {s : G} (hs : s ∈ S)
    (hsQ : s ∉ Q2 L1 L2 S)
    (hc : ∀ x ∈ Q2 L1 L2 S, x * s * x⁻¹ * s⁻¹ ∈ Y) : False := by
  have hO2Q : oTwoUpper (L2 ⊔ S) ≤ Q2 L1 L2 S :=
    oTwoUpper_le_pCoreOf_of_isL2 hF hS2 hm hL2 hYQ hYn hYc hs hsQ hc
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hHS : L2 ⊔ S = oTwoUpper (L2 ⊔ S) ⊔ S :=
    CFSG.Quasithin.H13.eq_oTwoUpper_sup_of_isSylowTwoOf (by
      rw [sup_eq_of_S_eq_right hS2]
      have hS2' : S = (S ⊓ L2) ⊔ Q1 L2 L1 S := by
        simpa [Q1, Q2, P1, P2, bigB_comm] using hS2
      have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.symm hS2'
      simpa [Q1, Q2, P1, P2, bigB_comm] using h)
  have hL2S : L2 ≤ S := by
    have hle : L2 ⊔ S ≤ S := by
      rw [hHS]
      exact sup_le (hO2Q.trans hQ2S) le_rfl
    exact (le_sup_left : L2 ≤ L2 ⊔ S).trans hle
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  apply hR.r2.borel_ne
  have hS2' : S ⊓ L2 = L2 := le_antisymm inf_le_right (le_inf hL2S le_rfl)
  have hN : L2 ⊓ Subgroup.normalizer (L2 : Set G) = L2 := inf_eq_left.mpr Subgroup.le_normalizer
  rw [hS2', hN]

end CFSG.Quasithin.Stroth

end
