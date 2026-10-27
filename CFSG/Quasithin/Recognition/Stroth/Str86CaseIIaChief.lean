module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaBasic
public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseII2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

theorem vSzBig_or_vU3Big_of_isSzU3Quot {L : Subgroup G} {q : ℕ}
    (h : IsSzU3Quot (oTwoQuot ↥L) q) : VSzBig L ∨ VU3Big L := by
  rcases h with ⟨a, ha, -, he⟩ | ⟨n, hn, -, F, hFld, hFin, hF, he⟩
  · exact Or.inl ⟨a, ha, he⟩
  · exact Or.inr ⟨n, hn, F, hFld, hFin, hF, he⟩

theorem not_isFFInt_z1_of_caseII
    {L1 L2 S : Subgroup G} {q : ℕ}
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    ¬ IsFFInt (L1 ⊔ S) (Z1 L1 L2 S) (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)) ∧
      ¬ IsDualFFInt (L1 ⊔ S) (Z1 L1 L2 S)
        (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)) := by
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    rw [hsup1]
    refine sup_le ?_ ?_
    · exact ((le_sup_left : L1 ≤ P1 L1 L2 S).trans
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))))
    · exact (Q1_le_centralizer_Z1 L1 L2 S).trans
        (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hC : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S :=
    inf_centralizer_z1_eq_q1_of_caseII hF.toW hB hB1 hII
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hq2 : 2 ≤ q := le_trans (by norm_num) (IsSzU3Quot.four_le hq)
  have hq' : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) q := by
    rw [hsup1]
    exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF.1) hq
  have hdisp : ∀ t ∈ S, t * t ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
      t ∉ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
      q ^ 2 ≤ (Z1 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex
        (Z1 L1 L2 S) := by
    intro t htS ht2 htC
    have htQ1 : t ∉ Q1 L1 L2 S := fun htQ =>
      htC (Q1_le_centralizer_Z1 L1 L2 S htQ)
    have htH : t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) htS
    have ht2Q1 : t * t ∈ Q1 L1 L2 S := by
      have htSC : t * t ∈ S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        ⟨S.mul_mem htS htS, ht2⟩
      rwa [hC] at htSC
    have hHc : ¬ L1 ⊔ S ≤
        ((L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) ⊔ pCoreOf 2 (L1 ⊔ S) := by
      rw [hpCore1]
      intro hle
      have hQ1C : Q1 L1 L2 S ≤
          (L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        le_inf (hQ1S.trans le_sup_right) (Q1_le_centralizer_Z1 L1 L2 S)
      have hHleC : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        (hle.trans (sup_le le_rfl hQ1C)).trans inf_le_right
      exact hII (by rwa [hsup1] at hHleC)
    exact sq_le_relIndex_centralizer_of_sq_mem hq'
      (fun v hv => by rw [← pow_two]; exact
        (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).2 v hv) hHZ1 hHc htH
      (by rwa [hpCore1]) (by rwa [hpCore1])
  have hhab : ∀ A : Subgroup G, A ≤ S →
      (∀ x ∈ A, ∀ y ∈ A,
        x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) ∧
          x * x ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G)) →
      (A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex A ≤ q := by
    intro A hAS hA
    have hsq : ∀ x ∈ A, x ^ 2 ∈ Q1 L1 L2 S := by
      intro x hx
      rw [pow_two]
      have hxSC : x * x ∈ S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        ⟨S.mul_mem (hAS hx) (hAS hx), (hA x hx x hx).2⟩
      rwa [hC] at hxSC
    have h := relIndex_inf_q1_le hF.1 hS1 hq hAS hsq
    have hAinf : A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = A ⊓ Q1 L1 L2 S := by
      calc A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)
          = (A ⊓ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
            rw [inf_eq_left.mpr hAS]
        _ = A ⊓ (S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) := by rw [inf_assoc]
        _ = A ⊓ Q1 L1 L2 S := by rw [hC]
    rwa [hAinf]
  exact not_isFFInt_of_disp (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S))
    hHZ1 hSyl1 hq2 hdisp hhab

theorem isElemAbelian_str86U_of_caseII
    {L1 L2 S : Subgroup G} {q m : ℕ}
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S) :
    IsElemAbelian 2 (str86U L1 L2 S) := by
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [sup_eq_of_S_eq_right hS2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hD11 : D11Hyp (L1 ⊔ S) (L2 ⊔ S) S (Z1 L1 L2 S) (borelOf L2 S ⊔ S) :=
    d11Hyp_of_caseII hF.toW hB hB1 hL2 hm hII
  have hFF := not_isFFInt_z1_of_caseII hF hB hq hII
  have hVR₂ : Z1 L1 L2 S ≤ pCoreOf 2 (L2 ⊔ S) := by
    rwa [hpCore2]
  simpa [str86U] using D15Proof.isElemAbelian_conjClosure hD11 hFF.1 hVR₂

theorem str86_caseIIa_chief_le_one_false
    {L1 L2 S : Subgroup G} {q m : ℕ}
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S) {c : ℕ}
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) c)
    (hc1 : c ≤ 1) : False := by
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hD11 : D11Hyp (L1 ⊔ S) (L2 ⊔ S) S (Z1 L1 L2 S) (borelOf L2 S ⊔ S) :=
    d11Hyp_of_caseII hF.toW hB hB1 hL2 hm hII
  have hFF := not_isFFInt_z1_of_caseII hF hB hq hII
  have hVR₂ : Z1 L1 L2 S ≤ pCoreOf 2 (L2 ⊔ S) := by
    rwa [hpCore2]
  have hZcent : L2 ⊔ S ≤
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)) : Set G) := by
    rw [hpCore2, hsup2]
    exact hIIa
  exact no_chiefSeries_le_one_of_d11Hyp hD11 hFF.1 hFF.2 hVR₂ hZcent hc hc1

end CFSG.Quasithin.Stroth

end
