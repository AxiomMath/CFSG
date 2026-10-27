module

public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.F112WKernel
public import CFSG.Quasithin.Background.RonanF13Hall
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Background.RonanF13Singer

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement
open CFSG.Quasithin.RonanF13 (HallTwoPrime)

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G}

theorem z1_inf_centralizer_le_z2 (hF : Hyp111 L1 L2 S) :
    Z1 L1 L2 S ⊓ Subgroup.centralizer (pCoreOf 2 (bigB L1 L2 S) : Set G) ≤ Z2 L1 L2 S := by
  intro z hz
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  obtain ⟨hzZ1, hzC⟩ := Subgroup.mem_inf.mp hz
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic' hR)
  have hzQ1 : z ∈ Q1 L1 L2 S := (omegaOneCenterOf_le (Q1 L1 L2 S)) hzZ1
  have hz2 : z ^ 2 = 1 := CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hzZ1
  have hzP2 : z ∈ P2 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) (hQ1S hzQ1))
  have hQ2bigB : Q2 L1 L2 S ≤ bigB L1 L2 S :=
    hQ2S.trans (le_sup_right : S ≤ bigB L1 L2 S)
  have hQ2p : Q2 L1 L2 S ≤ pCoreOf 2 (bigB L1 L2 S) :=
    le_pCoreOf_of_le_normalizer 2 hQ2bigB
      ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
        (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
      (pCoreOf_isPGroup 2 (P2 L1 L2 S))
  have hzCent : z ∈ Subgroup.centralizer (Q2 L1 L2 S : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hzC ⊢
    intro q hq
    exact hzC q (hQ2p hq)
  have hchar2 : CharTwo (P2 L1 L2 S) := by
    have h := F1.parabolic_charTwo hR.symm
    rwa [bigB_comm] at h
  have hzQ2 : z ∈ Q2 L1 L2 S := hchar2 ⟨hzP2, hzCent⟩
  exact CFSG.Quasithin.mem_omegaOneCenterOf hzQ2
    (fun y hy => Subgroup.mem_centralizer_iff.mp hzCent y hy) hz2

theorem z2_inf_centralizer_le_z1 (hF : Hyp111 L1 L2 S) :
    Z2 L1 L2 S ⊓ Subgroup.centralizer (pCoreOf 2 (bigB L1 L2 S) : Set G) ≤ Z1 L1 L2 S := by
  have h := z1_inf_centralizer_le_z2 (L1 := L2) (L2 := L1) (S := S) hF.symm
  simpa [Z1, Z2, Q1, Q2, P1, P2, bigB_comm] using h

theorem eq_bot_of_le_bigB (hF : Hyp111 L1 L2 S) {X : Subgroup G}
    (hX : X ≤ bigB L1 L2 S)
    (h1 : L1 ≤ (P1 L1 L2 S ⊓ Subgroup.normalizer (X : Set G)) ⊔ Q1 L1 L2 S)
    (h2 : L2 ≤ (P2 L1 L2 S ⊓ Subgroup.normalizer (X : Set G)) ⊔ Q2 L1 L2 S) : X = ⊥ := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic' hR)
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  refine F112W.eq_bot_of_normalizer_transitive (F112W.amalgamHyp_beta hR) ?_ ?_ ?_
  · rwa [F1.parabolic_inf_parabolic hR]
  · intro g hg
    obtain ⟨l, hl, b, hb, hgab⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes
        (F1.bigB_le_normalizer_left hR).1).mp hg
    obtain ⟨n, hn, q, hq, hlq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer
        ((inf_le_left : P1 L1 L2 S ⊓ Subgroup.normalizer (X : Set G) ≤ P1 L1 L2 S).trans
          (le_normalizer_pCoreOf 2 (P1 L1 L2 S)))).mp (h1 hl)
    refine ⟨n, hn, ?_⟩
    rw [hgab, hlq, show n⁻¹ * (n * q * b) = q * b from by group]
    exact (P2 L1 L2 S).mul_mem (hBP2 (hSB (hQ1S hq))) (hBP2 hb)
  · intro g hg
    obtain ⟨l, hl, b, hb, hgab⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes
        (F1.bigB_le_normalizer_left hR).2).mp hg
    obtain ⟨n, hn, q, hq, hlq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer
        ((inf_le_left : P2 L1 L2 S ⊓ Subgroup.normalizer (X : Set G) ≤ P2 L1 L2 S).trans
          (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))).mp (h2 hl)
    refine ⟨n, hn, ?_⟩
    rw [hgab, hlq, show n⁻¹ * (n * q * b) = q * b from by group]
    exact (P1 L1 L2 S).mul_mem (hBP1 (hSB (hQ2S hq))) (hBP1 hb)

end CFSG.Quasithin.Stroth
