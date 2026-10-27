module

public import CFSG.Quasithin.Recognition.Stroth.Str86Props
public import CFSG.Quasithin.Recognition.Stroth.Str83LocTransParts
public import CFSG.Quasithin.Recognition.Stroth.F112U3Vertex

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem str86LocTrans5_of_pathFix (hO : Str86Orders)
    (hP : Str86PathFix) : Str86LocTrans5 := by
  intro G _ _ L1 L2 S hF hU3 hBig hL2
  obtain ⟨k, hk, F, hField, hFin, hFc, hU3'⟩ := hU3
  letI : Field F := hField
  haveI : Finite F := hFin
  obtain ⟨hRL2, hQ1, hQ2, hS⟩ := hO G L1 L2 S k F hF hk hFc hU3' hBig hL2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hv1 : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 2 ^ (3 * k) + 1 := by
    rw [f112_relIndex_bigB_of_u3 hF hk hFc hU3', ← pow_mul]
    congr 1
    ring
  have hv2 : (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) = 2 ^ (2 * k) + 1 := by
    have hrel : (borelOf L2 S).relIndex L2 = 2 ^ (2 * k) + 1 := by
      have h' := CFSG.Quasithin.F112R.St84.index_borelOf_of_psl2 (f := 2 * k)
        (by omega) hF.1.h2.sylow hRL2
      simpa [Subgroup.relIndex] using h'
    have hinf : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
      have h := F1.inf_bigB_eq_borelOf hR.symm
      rwa [bigB_comm] at h
    rw [F112W.relIndex_sup_eq_relIndex_inf (N := L2) (B := bigB L1 L2 S)
      ((F1.bigB_le_normalizer_left hR).2), hinf]
    exact hrel
  have hq1 : (f112Amalgam L1 L2 S).qOne = 2 ^ (3 * k) := f112_qOne hF.toW hv1
  have hq2 : (f112Amalgam L1 L2 S).qTwo = 2 ^ (2 * k) := f112_qTwo hF.toW hv2
  have hSylB : IsSylowTwoOf S (bigB L1 L2 S) :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P1 hF.toW)
      le_sup_right le_sup_right
  have hmB : Odd (S.relIndex (bigB L1 L2 S)) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hSylB
  let c := f112Completion L1 L2 S
  have hc : c.IsFaithful := f112Completion_isFaithful L1 L2 S
  have hB : Nat.card ↥(c.φ1.range ⊓ c.φ2.range) =
      ((f112Amalgam L1 L2 S).qOne * (f112Amalgam L1 L2 S).qTwo) ^ 2 *
        S.relIndex (bigB L1 L2 S) := by
    change Nat.card ↥((f112Completion L1 L2 S).φ1.range ⊓
      (f112Completion L1 L2 S).φ2.range) = _
    have hpow : (2 ^ (3 * k) * 2 ^ (2 * k)) ^ 2 = (2 ^ k) ^ 10 := by
      rw [← pow_add, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hinf : S ⊓ bigB L1 L2 S = S := by
      show S ⊓ (borelOf L1 S ⊔ borelOf L2 S ⊔ S) = S
      exact inf_eq_left.mpr (le_sup_right : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S)
    have h := Subgroup.relIndex_mul_card (H := S) (K := bigB L1 L2 S)
    rw [hinf] at h
    rw [f112_card_edge hF.toW, hq1, hq2, hpow]
    calc Nat.card ↥(bigB L1 L2 S) =
          S.relIndex (bigB L1 L2 S) * Nat.card ↥S := h.symm
      _ = S.relIndex (bigB L1 L2 S) * (2 ^ k) ^ 10 := by rw [hS]
      _ = (2 ^ k) ^ 10 * S.relIndex (bigB L1 L2 S) := by rw [mul_comm]
  refine isLocallyTransHat_of_odd_stabPath (α := f112Amalgam L1 L2 S) c hc
    (j := 2) (e₁ := 3 * k) (e₂ := 2 * k)
    (m := S.relIndex (bigB L1 L2 S)) hq1 hq2 hmB hB ?_
  intro p hp g hfix hg
  refine hP G L1 L2 S hF ⟨k, hk, F, hField, hFin, hFc, hU3'⟩ hBig hL2 p hp g ?_ hg
  intro i hi
  rw [f112CosetSMul_eq_smul]
  exact hfix i hi

end CFSG.Quasithin.Stroth
