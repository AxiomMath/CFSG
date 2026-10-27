module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourCZ
public import CFSG.Quasithin.Vol2.Ch6NatLift

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_1_13_four_ZL_of : Stmt5_1_13_four_ZL := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m _ _ _ _ _ _ V' hV' _ hnat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hred := hV'.isTwoReducedIn
  have hVel : IsElemAbelian 2 V' := hred.2.2.1
  have hVT : V' ≤ T := h.V_le_T hV'
  have hTV : T ≤ Subgroup.normalizer (V' : Set G) := le_sup_right.trans hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V' : Set G) := le_sup_left.trans hred.2.1
  have hS := h.isSylowTwoOf_inf
  have hCL : L ⊓ Subgroup.centralizer (V' : Set G) ≤ T :=
    (h.inf_centralizer_le hLV hV'.2.2).trans ((F7.isSylowTwoOf_pCoreOf_le hS).trans inf_le_left)
  obtain ⟨z, hzV, hzT, hzL⟩ := hnat.exists_fixed_ch6 h.two_le hVel.2 h.sylow.1
    h.T_le_normalizer hTV hVT hS hCL
  intro hZL
  have hzZ : z ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hVT hzV, hzT⟩, hVel.2 z hzV⟩
  exact hzL (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZL hzZ)

end CFSG.Quasithin.H13
