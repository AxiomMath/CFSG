module

public import CFSG.Quasithin.Background.OTwoUpperPerfect
public import CFSG.Quasithin.Recognition.Stroth.Str86XOne3
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIPushUp

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_oTwoUpper_sup_q1 {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    oTwoUpper (L1 ⊔ S) ⊔ Q1 L1 L2 S = L1 ⊔ S := by
  have hVU3 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hQ1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    simpa [u3LS] using u3LS_pCoreOf (k := k) (F := F) hF hSB hVU3
  have hperf : Group.IsPerfect (oTwoQuot ↥(L1 ⊔ S)) :=
    (isQuasisimple_oTwoQuot_of_u3 (L := ↥(L1 ⊔ S)) hk hFc
      (u3HQU3 hF hSB hU3 hVU3)).1
  have h := eq_oTwoUpper_sup_pCoreOf_of_perfect (H := L1 ⊔ S) hperf
  rw [hQ1] at h
  exact h.symm

theorem str86_z1_sup_q2_of_not_le {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hZ : ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S) :
    Z1 L1 L2 S ⊔ Q2 L1 L2 S = S ∧
      (Z1 L1 L2 S ⊓ Q2 L1 L2 S).relIndex (Z1 L1 L2 S) = 2 ^ m := by
  have hm2 : 2 ≤ m :=
    CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hZ1S : Z1 L1 L2 S ≤ S := (A4.omegaOneCenterOf_le (Q1 L1 L2 S)).trans hQ1S
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  have hsup : Z1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_cartan_supplement hF.toW hSB hB2 ⟨m, hm⟩ hZ1S hBN hZ
  have hZ1NQ2 : Z1 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hZ1S.trans (le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S))
  refine ⟨hsup, ?_⟩
  rw [Subgroup.inf_relIndex_left, ← F1.relIndex_sup_eq_of_le_normalizer hZ1NQ2, hsup]
  exact str86_relIndex_q2_s hF.toW hSB hm2 hm

end CFSG.Quasithin.Stroth

end
