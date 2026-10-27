module


import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
import CFSG.Quasithin.Recognition.Stroth.Y9Transport
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.Stroth.F112Tree

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_of_inf_sylow_le {H N S Q X : Subgroup G} (hS : IsSylowTwoOf S H) (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hQ : IsPGroup 2 Q)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hSNQ : S ⊓ N ≤ Q) (hXN : X ≤ N)
    (hX : IsPGroup 2 X) : X ≤ Q := by
  have hSN : IsSylowTwoOf (S ⊓ N) N := A4.isSylowTwoOf_inf_normal hS hNH hHN
  have hQN : IsSylowTwoOf (Q ⊓ N) N := by
    refine ⟨inf_le_right, hQ.to_le inf_le_left, fun h2 => hSN.2.2 ?_⟩
    exact h2.trans (Subgroup.relIndex_dvd_of_le_left N (le_inf hSNQ inf_le_right))
  have hQNn : ((Q ⊓ N).subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (hHQ (hNH hx)) y,
      Subgroup.mem_normalizer_iff.mp (hHN (hNH hx)) y]
  exact (le_of_isSylowTwoOf_normal hQN hQNn hXN hX).trans inf_le_left

theorem str86_f2_linear {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {X : Subgroup G}
    (hX : X ≤ ballStab 1 (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) (hX2 : IsPGroup 2 X) :
    X ≤ Q2 L1 L2 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hyp := F112W.amalgamHyp_alpha hR
  obtain ⟨hNle, hNn⟩ := (CosetGeom.ballStab_one_γ₀ hyp.gen).2.1
  set N := ballStab 1 (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) with hNdef
  have hPB : P2 L1 L2 S ⊓ P1 L1 L2 S = bigB L1 L2 S := by
    rw [inf_comm]
    exact F1.parabolic_inf_parabolic hR
  have hNB : N ≤ bigB L1 L2 S := hNle.trans hPB.le
  have hNP2 : N ≤ P2 L1 L2 S := hNle.trans inf_le_left
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hSB' : S ≤ bigB L1 L2 S := le_sup_right
  have hHP2 : L2 ⊔ Q2 L1 L2 S ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hHQ2 : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hHP2.trans (le_normalizer_pCoreOf 2 _)
  have hNH : N ⊓ (L2 ⊔ Q2 L1 L2 S) ≤ Q2 L1 L2 S := by
    have hK : (N ⊓ (L2 ⊔ Q2 L1 L2 S)) ⊔ Q2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S :=
      sup_le inf_le_right le_sup_right
    have hKn : L2 ⊔ Q2 L1 L2 S ≤
        Subgroup.normalizer (((N ⊓ (L2 ⊔ Q2 L1 L2 S)) ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
      refine F1.le_normalizer_sup (fun x hx => ?_) hHQ2
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [SetLike.mem_coe, Subgroup.mem_inf]
      rw [Subgroup.mem_normalizer_iff.mp (hNn (hHP2 hx)) y,
        Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y]
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW hn hL2 hK hKn le_sup_right with h | h
    · exact le_sup_left.trans h.le
    · exfalso
      have hL2B : L2 ≤ bigB L1 L2 S := by
        have h' : L2 ⊔ Q2 L1 L2 S ≤ bigB L1 L2 S :=
          h.symm.le.trans (sup_le (inf_le_left.trans hNB) (hQ2S.trans hSB'))
        exact le_sup_left.trans h'
      have hlt : L2 ⊓ bigB L1 L2 S < L2 := by
        rw [← bigB_comm L1 L2 S, F1.inf_bigB_eq_borelOf hR.symm]
        exact F1.lt_borelOf hR.symm
      exact hlt.ne (inf_eq_left.mpr hL2B)
  have hSN : S ⊓ N ≤ Q2 L1 L2 S := fun x hx =>
    hNH (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2,
      str86_s_le_u3H hF.toW hSB hn hL2 (Subgroup.mem_inf.mp hx).1⟩)
  exact le_of_inf_sylow_le (f112_isSylowTwoOf_P2 hF.toW) hNP2 hNn (pCoreOf_isPGroup 2 _)
    (le_normalizer_pCoreOf 2 _) hSN hX hX2

theorem str86_f2_unitary {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) {X : Subgroup G}
    (hX : X ≤ ballStab 1 (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) (hX2 : IsPGroup 2 X) :
    X ≤ Q1 L1 L2 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hyp := F112W.amalgamHyp_alpha hR
  obtain ⟨hNle, hNn⟩ := (CosetGeom.ballStab_one_γ₁ hyp.gen).2.1
  set N := ballStab 1 (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) with hNdef
  have hPB : P2 L1 L2 S ⊓ P1 L1 L2 S = bigB L1 L2 S := by
    rw [inf_comm]
    exact F1.parabolic_inf_parabolic hR
  have hNB : N ≤ bigB L1 L2 S := hNle.trans hPB.le
  have hNP1 : N ≤ P1 L1 L2 S := hNle.trans inf_le_right
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSB' : S ≤ bigB L1 L2 S := le_sup_right
  have hHP1 : L1 ⊔ Q1 L1 L2 S ≤ P1 L1 L2 S :=
    sup_le le_sup_left (pCoreOf_le 2 (P1 L1 L2 S))
  have hHQ1 : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hHP1.trans (le_normalizer_pCoreOf 2 _)
  have hpH : pCoreOf 2 (L1 ⊔ Q1 L1 L2 S) = Q1 L1 L2 S := pCoreOf_sup_pCoreOf hF.1
  have hqLhat : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S)) (2 ^ k) := by
    refine Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, ?_⟩
    rcases hU3 with h | h
    · obtain ⟨eL⟩ := h
      exact Or.inl ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
    · obtain ⟨eL⟩ := h
      exact Or.inr ⟨(oTwoQuotSupEquiv hF.1).trans eL⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB
      (Or.inr (Or.inl ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩))
  have hSH : S ≤ L1 ⊔ Q1 L1 L2 S :=
    hS1.le.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
  have hK : (N ⊓ (L1 ⊔ Q1 L1 L2 S)) ⊔ Q1 L1 L2 S ≤ L1 ⊔ Q1 L1 L2 S :=
    sup_le inf_le_right le_sup_right
  have hKn : L1 ⊔ Q1 L1 L2 S ≤
      Subgroup.normalizer (((N ⊓ (L1 ⊔ Q1 L1 L2 S)) ⊔ Q1 L1 L2 S : Subgroup G) : Set G) := by
    refine F1.le_normalizer_sup (fun x hx => ?_) hHQ1
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (hNn (hHP1 hx)) y,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y]
  have hQK : pCoreOf 2 (L1 ⊔ Q1 L1 L2 S) ≤ (N ⊓ (L1 ⊔ Q1 L1 L2 S)) ⊔ Q1 L1 L2 S :=
    hpH.le.trans le_sup_right
  rcases eq_or_mem_pCoreOf_of_normal hqLhat hK hKn hQK with h | h
  · exfalso
    have hL1B : L1 ≤ bigB L1 L2 S := by
      have h' : L1 ⊔ Q1 L1 L2 S ≤ bigB L1 L2 S :=
        h.symm.le.trans (sup_le (inf_le_left.trans hNB) (hQ1S.trans hSB'))
      exact le_sup_left.trans h'
    have hlt : L1 ⊓ bigB L1 L2 S < L1 := by
      rw [F1.inf_bigB_eq_borelOf hR]
      exact F1.lt_borelOf hR
    exact hlt.ne (inf_eq_left.mpr hL1B)
  · have hSN : S ⊓ N ≤ Q1 L1 L2 S := by
      intro x hx
      obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.mp hx
      have hxK : x ∈ (N ⊓ (L1 ⊔ Q1 L1 L2 S)) ⊔ Q1 L1 L2 S :=
        Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxN, hSH hxS⟩)
      obtain ⟨j, hj⟩ := hF.1.h1.pgroup ⟨x, hxS⟩
      have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      exact hpH.le (h x hxK ⟨j, hj'⟩)
    exact le_of_inf_sylow_le (f112_isSylowTwoOf_P1 hF.toW) hNP1 hNn (pCoreOf_isPGroup 2 _)
      (le_normalizer_pCoreOf 2 _) hSN hX hX2

end CFSG.Quasithin.Stroth

end
