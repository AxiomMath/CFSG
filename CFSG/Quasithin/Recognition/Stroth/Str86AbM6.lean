module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbBase

import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleProp39

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem str86_sq_le_relIndex_conjClosure_of_mem_p1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {t : G}
    (htP : t ∈ P1 L1 L2 S) (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1) :
    (2 ^ k) ^ 2 ≤ (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (conjClosure (Z2 L1 L2 S) L1) := by
  classical
  have hF := hI.hF
  obtain ⟨hVQ1, hP1NV, -⟩ := str86_conjClosure_frame hI hZQ
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hV : IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1) :=
    hF.1.h1.pgroup.to_le (hVQ1.trans hQ1S)
  have hVH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S := hVQ1.trans (hQ1S.trans le_sup_right)
  have ht1 : t ≠ 1 := fun h => htQ (h ▸ (Q1 L1 L2 S).one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hX2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have htH : t ∈ L1 ⊔ S :=
    (str86_le_lhat_of_isPGroup hI hX2).1 (Subgroup.zpowers_le.mpr htP) (Subgroup.mem_zpowers t)
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hI.hSB (Or.inr (Or.inl h1))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S :=
    le_antisymm (sup_le le_sup_left (hS1.le.trans (sup_le (inf_le_right.trans le_sup_left)
      le_sup_right))) (sup_le le_sup_left (hQ1S.trans le_sup_right))
  have hQcore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hSyl : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hX : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
    have he : oTwoQuot ↥(L1 ⊔ S) ≃* oTwoQuot ↥L1 := by
      rw [hsup1]
      exact oTwoQuotSupEquiv hF.1
    exact IsSzU3Quot.of_mulEquiv he (Or.inr ⟨k, hI.hk, rfl, F, inferInstance, inferInstance,
      hI.hFc, hI.hU3⟩)
  have hHV : L1 ⊔ S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans hP1NV
  have hnorm : IsNormalIn (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
      (conjClosure (Z2 L1 L2 S) L1) :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHV hg) x).mp hx⟩
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom (conjClosure (Z2 L1 L2 S) L1) hnorm
  have ht2p : t * t ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [hQcore, ht2]
    exact (Q1 L1 L2 S).one_mem
  have htO : t ∉ pCoreOf 2 (L1 ⊔ S) := by rwa [hQcore]
  have hM6 := pow_sq_le_relIndex_centralizer (H := L1 ⊔ S)
    (U := conjClosure (Z2 L1 L2 S) L1) (q := 2 ^ k) (c := c) hX hV hVH hser htH ht2p htO
  have hc : c ≠ 0 := str86_chief_count_ne_zero hF hSyl hV hser
  exact (le_self_pow (one_le_pow₀ (Nat.one_le_pow k 2 (by norm_num))) hc).trans hM6

end CFSG.Quasithin.Stroth

end
