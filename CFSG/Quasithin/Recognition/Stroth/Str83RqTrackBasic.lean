module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack
import CFSG.Quasithin.Recognition.Stroth.F112Tree

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem Gv_zero : t.Gv 0 = P1 L1 L2 S := by
  ext y
  simp [mem_qv_iff, trackElt, trackPar]

theorem Gv_one : t.Gv 1 = P2 L1 L2 S := by
  ext y
  simp [mem_qv_iff, trackElt, trackPar]

theorem Qv_zero : t.Qv 0 = Q1 L1 L2 S := by
  ext y
  simp [mem_qv_iff, trackElt, trackPar]

theorem Qv_one : t.Qv 1 = Q2 L1 L2 S := by
  ext y
  simp [mem_qv_iff, trackElt, trackPar]

theorem Zv_zero : t.Zv 0 = Z1 L1 L2 S := by
  ext y
  simp [mem_qv_iff, trackElt, trackPar]

theorem Zv_one : t.Zv 1 = Z2 L1 L2 S := by
  ext y
  simp [mem_qv_iff, trackElt, trackPar]

theorem Gw_zero_one (hF : F112HypW L1 L2 S) :
    t.Gw 0 1 = bigB L1 L2 S := by
  change win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 0 (0 + 1) = _
  rw [win_add_one_right (a := 0) (b := 0) (by omega), win_self, zero_add]
  rw [show qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 0 = t.Gv 0 from rfl, t.Gv_zero,
    show qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ 1 = t.Gv 1 from rfl, t.Gv_one]
  exact f112_parabolic_inf_eq_bigB hF

theorem pCoreOf_Gw_zero_one {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    pCoreOf 2 (t.Gw 0 1) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [t.Gw_zero_one hfr.hF]
  have hSyl := F1.isSylowTwoOf_bigB_of_normal (Hyp111R.of_hyp111 rankOneListedFacts hfr.hF.1)
    hfr.hN
  exact le_antisymm (F7.isSylowTwoOf_pCoreOf_le hSyl)
    (le_pCoreOf_of_le_normalizer 2 hSyl.1 hfr.hN hSyl.2.1)

theorem isPGroup_Qv (i : ℤ) : IsPGroup 2 (t.Qv i) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [t.Qv_eq i]
  exact pCoreOf_isPGroup 2 _

theorem Zv_le_Qv (i : ℤ) : t.Zv i ≤ t.Qv i := by
  rw [t.Zv_eq i]
  exact A4.omegaOneCenterOf_le _

theorem Zv_le_centralizer (i : ℤ) : t.Zv i ≤ centralizer (t.Qv i : Set G) := by
  rw [t.Zv_eq i]
  exact (A4.omegaOneCenterOf_le_centerOf _).trans inf_le_right

theorem isPGroup_Zv (i : ℤ) : IsPGroup 2 (t.Zv i) :=
  (t.isPGroup_Qv i).to_le (t.Zv_le_Qv i)

theorem Qv_le_Gv_self (i : ℤ) : t.Qv i ≤ t.Gv i := by
  rw [t.Qv_eq i]
  exact pCoreOf_le 2 _

theorem Gv_le_normalizer_Qv (i : ℤ) : t.Gv i ≤ normalizer (t.Qv i : Set G) := by
  rw [t.Qv_eq i]
  exact le_normalizer_pCoreOf 2 _

theorem Gv_le_normalizer_Zv (i : ℤ) : t.Gv i ≤ normalizer (t.Zv i : Set G) := by
  rw [t.Zv_eq i]
  exact (t.Gv_le_normalizer_Qv i).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

theorem K_le_Gv (i : ℤ) : t.K ≤ t.Gv i := by
  have h := t.K_le_Gw i i
  rwa [show t.Gw i i = t.Gv i from win_self _] at h

theorem Zv_ne_bot (hF : F112HypW L1 L2 S) (i : ℤ) :
    t.Zv i ≠ ⊥ := by
  have h1 : omegaOneCenterOf S ≤ Z1 L1 L2 S :=
    omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf hF.1
  have h2 : omegaOneCenterOf S ≤ Z2 L1 L2 S := by
    have hle := omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf (L1 := L2) (L2 := L1) (S := S)
      hF.1.symm
    simpa [Z1, Z2, Q1, Q2, P1, P2, bigB_comm] using hle
  have hne := omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  intro hbot
  have hpar : trackPar (Z1 L1 L2 S) (Z2 L1 L2 S) i = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp hbot
  unfold trackPar at hpar
  split_ifs at hpar
  · exact hne (le_bot_iff.mp (hpar ▸ h1))
  · exact hne (le_bot_iff.mp (hpar ▸ h2))

theorem Qv_ne_bot (hF : F112HypW L1 L2 S) (i : ℤ) :
    t.Qv i ≠ ⊥ := fun h => t.Zv_ne_bot hF i (le_bot_iff.mp (h ▸ t.Zv_le_Qv i))

end Track

end CFSG.Quasithin.Stroth.Rq

end
