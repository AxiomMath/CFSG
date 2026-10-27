module

public import CFSG.Quasithin.H13.A5S135
public import CFSG.Quasithin.H13.A5S1514

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem pCoreOf_M_ne_bot : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨P, hP1, hP2, hPeq⟩, -⟩ := S.uniqueM.1.1
  intro h
  have := le_pCoreOf_normalizer 2 P hP2
  rw [← hPeq, h] at this
  exact hP1 (le_bot_iff.1 this)

theorem charTwo_M : CharTwo (Subgroup.normalizer (L : Set G)) :=
  S.charTwo_of_inH ⟨S.T_le_NL, S.pCoreOf_M_ne_bot⟩

theorem pCoreOf_M_le_T : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≤ T := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  have := pCoreOf_two_le_sylow (Subgroup.normalizer (L : Set G)) P (hP ▸ S.T_le_NL)
  rwa [hP] at this

theorem V_le_pCoreOf_M : V ≤ pCoreOf 2 (Subgroup.normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have hOLT : pCoreOf 2 M ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (S.pCoreOf_M_le_T.trans le_sup_right)
      ((sup_le Subgroup.le_normalizer S.T_le_NL).trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  have hOC : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G) := hOLT.trans (S.cLT ▸ inf_le_right)
  intro v hv
  have hvM : v ∈ M := S.NV_le_M (Subgroup.le_normalizer hv)
  have hvC : v ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hOC hq) v hv).symm
  exact S.charTwo_M ⟨hvM, hvC⟩

theorem V_le_pCoreOf_of_le_M {X : Subgroup G} (hVX : V ≤ X)
    (hXM : X ≤ Subgroup.normalizer (L : Set G)) : V ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ⊓ X ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (B2F.le_normalizer_inf (hXM.trans (le_normalizer_pCoreOf 2 _)) Subgroup.le_normalizer)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  exact fun v hv => h1 ⟨S.V_le_pCoreOf_M hv, hVX hv⟩

omit S [Finite G] in
theorem oTwoRes_sup_le {A Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ Subgroup.normalizer (A : Set G)) : oTwoRes (A ⊔ Q) ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul : ((A ⊔ Q : Subgroup G) : Set G) = (A : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A Q hQA
  rw [oTwoRes, Subgroup.closure_le]
  rintro y ⟨hy, m, hm, hym⟩
  obtain ⟨a, ha, q, hq, rfl⟩ : y ∈ (A : Set G) * (Q : Set G) := by rw [← hmul]; exact hy
  obtain ⟨a', ha', he⟩ := pow_mem_mul_of_normalizes ha (hQA hq) m
  have hqm : q ^ m ∈ A := by
    have : a' * q ^ m = 1 := by rw [← he, hym]
    have e : q ^ m = a'⁻¹ := eq_inv_of_mul_eq_one_right this
    rw [e]
    exact A.inv_mem ha'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨q, hq⟩
  have hord : orderOf q = 2 ^ k := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  have hcop : m.Coprime (orderOf q) := by
    rw [hord]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  have hqA : q ∈ A := by
    rw [← hc]
    exact A.pow_mem hqm c
  exact A.mul_mem ha hqA

theorem oTwoRes_L1_sup {Q : Subgroup G} (hQT : Q ≤ T) : oTwoRes (S.L1 ⊔ Q) = S.L1 := by
  apply le_antisymm
  · exact oTwoRes_sup_le (S.isPGroup_T.to_le hQT) (hQT.trans S.T_le_normalizer_L1)
  · show oTwoRes (L ⊓ Subgroup.normalizer (S.V1 : Set G)) ≤ oTwoRes (S.L1 ⊔ Q)
    rw [oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    refine Subgroup.subset_closure ⟨le_sup_left (a := S.L1) ?_, m, hm, hym⟩
    exact Subgroup.subset_closure ⟨hy, m, hm, hym⟩

theorem mem_normalizer_L1_of_mem_normalizer_sup {H : Subgroup G} (hH : H ∈ S.Hz) {x : G}
    (hx : x ∈ Subgroup.normalizer ((S.L1 ⊔ pCoreOf 2 H : Subgroup G) : Set G)) :
    x ∈ Subgroup.normalizer (S.L1 : Set G) := by
  have hQT : pCoreOf 2 H ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow (le_sup_right.trans hH.1.1))
  have := le_normalizer_oTwoRes_of_le_normalizer (Subgroup.zpowers_le.mpr hx)
    (Subgroup.mem_zpowers x)
  rwa [S.oTwoRes_L1_sup hQT] at this

theorem normalizer_L1_mem_Hz {H : Subgroup G} (hH : H ∈ S.Hz)
    (hM : ¬ H ⊓ Subgroup.normalizer (S.L1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    H ⊓ Subgroup.normalizer (S.L1 : Set G) ∈ S.Hz := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1T : S.L1 ⊔ T ≤ H ⊓ Subgroup.normalizer (S.L1 : Set G) :=
    le_inf hH.1.1 (sup_le Subgroup.le_normalizer S.T_le_normalizer_L1)
  refine ⟨⟨hL1T, fun h => ?_⟩, inf_le_left.trans hH.2.1, hM⟩
  have hV1 : S.V1 ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (S.L1 : Set G)) := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ (S.isPGroup_V.to_le S.V1_le_V)
    · exact (S.V1_le_V.trans S.V_le_T).trans (le_sup_right.trans hL1T)
    · intro x hx
      rw [← S.G1_eq_normalizer]
      exact hH.2.1 hx.1
  rw [h, le_bot_iff] at hV1
  have hc := S.card_V1
  rw [hV1] at hc
  simp at hc

theorem lemma_13_5_19_two (h1323 : Input1323Two)
    (hcon : ∀ H' ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H') →
      ¬ H' ≤ Subgroup.normalizer (S.L1 : Set G))
    {H : Subgroup G} (hH : H ∈ S.Hz) :
    V ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (S.L1 : Set G)) := by
  by_contra hV
  have hVH1 : V ≤ H ⊓ Subgroup.normalizer (S.L1 : Set G) :=
    le_inf ((S.hypF91 h1323 hH).V_le_H)
      (S.V_le_T.trans S.T_le_normalizer_L1)
  have hM : ¬ H ⊓ Subgroup.normalizer (S.L1 : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun h => hV (S.V_le_pCoreOf_of_le_M hVH1 h)
  have hH1 := S.normalizer_L1_mem_Hz hH hM
  have hna : ¬ IsElemAbelian 2 (conjClosure S.V3 (H ⊓ Subgroup.normalizer (S.L1 : Set G))) :=
    fun hab => hV (((S.tfae_13_5_10 h1323 hH1).out 1 2).2 hab)
  exact hcon _ hH1 hna inf_le_right

end Setting

end CFSG.Quasithin.H13.A5
