module

public import CFSG.Quasithin.Recognition.Stroth.Str83Props
public import CFSG.Quasithin.Recognition.Stroth.LocTransCount
public import CFSG.Quasithin.Recognition.Stroth.F112Moufang
public import CFSG.Quasithin.Recognition.Stroth.Y9TwistedF4
public import CFSG.Quasithin.Recognition.GoldschmidtF112RSt84HypA
public import CFSG.Quasithin.Recognition.Stroth.WeissStrothLeaves

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

theorem f112_card_edge {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    Nat.card ↥((f112Completion L1 L2 S).φ1.range ⊓ (f112Completion L1 L2 S).φ2.range) =
      Nat.card ↥(bigB L1 L2 S) := by
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let B : Subgroup G := bigB L1 L2 S
  let G0 : Subgroup G := P1 ⊔ P2
  have hr1 : (f112Completion L1 L2 S).φ1.range = P1.subgroupOf G0 :=
    Subgroup.inclusion_range (le_sup_left : P1 ≤ P1 ⊔ P2)
  have hr2 : (f112Completion L1 L2 S).φ2.range = P2.subgroupOf G0 :=
    Subgroup.inclusion_range (le_sup_right : P2 ≤ P1 ⊔ P2)
  have hinf : P1 ⊓ P2 = B := f112_parabolic_inf_eq_bigB hF
  have hK : (f112Completion L1 L2 S).φ1.range ⊓ (f112Completion L1 L2 S).φ2.range =
      B.subgroupOf G0 := by
    rw [hr1, hr2]
    ext z
    have key : ∀ x : G, (x ∈ P1 ∧ x ∈ P2) ↔ x ∈ B := by
      intro x
      rw [← hinf]
      simp only [Subgroup.mem_inf]
    simpa only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, z.2, true_and] using key (z : G)
  rw [hK]
  have hle : B ≤ G0 := le_trans le_sup_right le_sup_left
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem str83LocTrans9_of_pathFix (hO : Str83Orders)
    (hP : Str83PathFix) : Str83LocTrans9 := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  obtain ⟨hm, hQ1, hQ2, hS⟩ := hO G L1 L2 S a hF ha hSz hBig hL2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hv1 : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) =
      2 ^ (2 * (2 * a + 1)) + 1 := by
    have hrel : (borelOf L1 S).relIndex L1 = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
      have h' := index_borelOf_of_sz ha hF.1.h1.sylow (Classical.choice hSz)
      simpa [Subgroup.relIndex] using h'
    rw [F112W.relIndex_sup_eq_relIndex_inf (N := L1) (B := bigB L1 L2 S)
      ((F1.bigB_le_normalizer_left hR).1), F1.inf_bigB_eq_borelOf hR, hrel, ← pow_mul]
    congr 1
    ring
  have hv2 : (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) =
      2 ^ (2 * a + 1) + 1 := by
    have hrel : (borelOf L2 S).relIndex L2 = 2 ^ (2 * a + 1) + 1 := by
      have h' := CFSG.Quasithin.F112R.St84.index_borelOf_of_psl2 (f := 2 * a + 1)
        (by omega) hF.1.h2.sylow hm
      simpa [Subgroup.relIndex] using h'
    have hinf : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
      have h := F1.inf_bigB_eq_borelOf hR.symm
      rwa [bigB_comm] at h
    rw [F112W.relIndex_sup_eq_relIndex_inf (N := L2) (B := bigB L1 L2 S)
      ((F1.bigB_le_normalizer_left hR).2), hinf]
    exact hrel
  have hq1 : (f112Amalgam L1 L2 S).qOne = 2 ^ (2 * (2 * a + 1)) :=
    f112_qOne hF hv1
  have hq2 : (f112Amalgam L1 L2 S).qTwo = 2 ^ (2 * a + 1) :=
    f112_qTwo hF hv2
  have hSylB : IsSylowTwoOf S (bigB L1 L2 S) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF)
      le_sup_right le_sup_right
  have hmB : Odd (S.relIndex (bigB L1 L2 S)) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hSylB
  let c := f112Completion L1 L2 S
  have hc : c.IsFaithful := f112Completion_isFaithful L1 L2 S
  have hB : Nat.card ↥(c.φ1.range ⊓ c.φ2.range) =
      ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ 4 *
        S.relIndex (bigB L1 L2 S) := by
    change Nat.card ↥((f112Completion L1 L2 S).φ1.range ⊓
      (f112Completion L1 L2 S).φ2.range) = _
    have hpow : (2 ^ (2 * (2 * a + 1)) * 2 ^ (2 * a + 1)) ^ 4 =
        (2 ^ (2 * a + 1)) ^ 12 := by
      rw [← pow_add, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hinf : S ⊓ bigB L1 L2 S = S := by
      show S ⊓ (borelOf L1 S ⊔ borelOf L2 S ⊔ S) = S
      exact inf_eq_left.mpr (le_sup_right : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S)
    have h := Subgroup.relIndex_mul_card (H := S) (K := bigB L1 L2 S)
    rw [hinf] at h
    rw [f112_card_edge hF, hq1, hq2, hpow]
    calc Nat.card ↥(bigB L1 L2 S) =
          S.relIndex (bigB L1 L2 S) * Nat.card ↥S := h.symm
      _ = S.relIndex (bigB L1 L2 S) * (2 ^ (2 * a + 1)) ^ 12 := by rw [hS]
      _ = (2 ^ (2 * a + 1)) ^ 12 * S.relIndex (bigB L1 L2 S) := by rw [mul_comm]
  refine isLocallyTransHat_of_odd_stabPath (α := f112Amalgam L1 L2 S) c hc
    (j := 4) (e₁ := 2 * (2 * a + 1)) (e₂ := 2 * a + 1)
    (m := S.relIndex (bigB L1 L2 S)) hq1 hq2 hmB hB ?_
  intro p hp g hfix hg
  exact hP G L1 L2 S a hF ha hSz hBig hL2
    ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) c hc p hp g hfix hg

end CFSG.Quasithin.Stroth
