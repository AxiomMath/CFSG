module

public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.E3Offender

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Lower

variable {G : Type u} [Group G] [Finite G] {V T : Subgroup G}

omit [Finite G] in
theorem autI_normalizer_eq_top (hV : IsElemAbelian 2 V) :
    autI hV (Subgroup.normalizer (V : Set G)) = autI hV ⊤ := by
  unfold autI
  rw [Subgroup.subgroupOf_self, Subgroup.top_subgroupOf]

omit [Finite G] in
theorem le_wParam_of_wClos_le {n : ℕ}
    (h : ∀ j < n, wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    (n : ℕ∞) ≤ wParam T V :=
  le_iInf₂ fun j hj => Nat.cast_le.2 (not_lt.1 fun hlt => hj (h j hlt))

omit [Finite G] in
theorem wClos_le_of_lt_wParam {i : ℕ} (h : (i : ℕ∞) < wParam T V) :
    wClos V i T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  by_contra hcon
  exact absurd h (not_lt.2 (iInf₂_le i hcon))

theorem e3_34_one (hV : IsElemAbelian 2 V) (hT : HypE322 T V)
    (h : aParam (autI hV ⊤) < sParam hV) :
    ((sParam hV - aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ wParam T V ∧
      0 < sParam hV - aParam (autI hV ⊤) := by
  refine ⟨le_wParam_of_wClos_le fun j hj => ?_, by omega⟩
  have hi : j < sParam hV - aParam (autI hV (Subgroup.normalizer (V : Set G))) := by
    rwa [autI_normalizer_eq_top hV]
  have hc := e3_18_comm hV hT.normal le_rfl hV hi
  refine le_inf (wClos_le j T) ?_
  exact le_centralizer_iff_comm.1 (commutator_eq_bot_iff_le_centralizer'.1 hc)

theorem e3_34_two (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {M : Subgroup G}
    (hM : IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M)
    {i : ℕ} (hi : i < rk ↥V) (hiw : (i : ℕ∞) < wParam T V) :
    Subgroup.normalizer (wClos V i T : Set G) ≤ M ∧
      Subgroup.centralizer (cClos V i T : Set G) ≤ M := by
  have hW := wClos_le_of_lt_wParam hiw
  have hY2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (V : Set G)) :=
    hT.sylow.isPGroup.to_le inf_le_left
  have hne := wClos_ne_bot hV hT.le hi
  exact ⟨(e3_16_one hT.sylow le_top hY2 hW hne hM).2, e3_16_three hT.sylow le_top hY2 hW hne hM⟩

end Lower

end E3

end CFSG.Quasithin
