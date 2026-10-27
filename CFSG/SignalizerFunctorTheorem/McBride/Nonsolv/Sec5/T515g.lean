module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KHat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515e
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515g.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515g.Sol

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem theorem_5_15_g
    {p : ℕ} {A G : Subgroup Γ} (h : KSetting p A G) (hKA : kDown G A = ⊥)
    {B : Subgroup Γ} (hBA : B ≤ A) :
    khat (G ⊓ Subgroup.centralizer (B : Set Γ)) =
      khat G ⊓ Subgroup.centralizer (B : Set Γ) := by
  have hsol : sol G = ⊥ := sol_eq_bot_of_kDown_eq_bot hKA
  have hBG : B ≤ Subgroup.normalizer (G : Set Γ) := hBA.trans h.normalizes
  have hsolV := T515g.sol_inf_centralizer_eq_bot h hKA hBA
  have hAV := T515g.le_normalizer_inf_centralizer h hBA
  have hDV := T515g.inf_centralizer_le_inf_centralizer G hBA
  have hlcal := T515f.lcal_inf_centralizer_eq h hKA hBA
  set V := G ⊓ Subgroup.centralizer (B : Set Γ) with hV
  have hNV : V ≤ Subgroup.normalizer ((khat V : Subgroup Γ) : Set Γ) := fun v hv =>
    mem_normalizer_khat_of_mem_normalizer (Subgroup.le_normalizer hv)
  apply le_antisymm
  ·
    have hX : IsDAInvariant A G (khat V) :=
      ⟨(khat_le V).trans inf_le_left, fun d hd => hNV (hDV hd),
        fun a ha => mem_normalizer_khat_of_mem_normalizer (hAV ha)⟩
    have hsolX : sol (khat V) = ⊥ :=
      le_bot_iff.mp (hsolV ▸ T515g.sol_le_sol_of_le_normalizer (khat_le V) hNV)
    have hKX : khat (khat V) = khat V := by
      refine le_antisymm (khat_le _) fun x hx => ?_
      rw [T515e.mem_khat_iff_of_sol_eq_bot hsolX]
      refine ⟨hx, fun M hM => ?_⟩
      have hMV : M ∈ lcal V := T515g.mem_lcal_of_isSubnormal hM (khat_le V)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (khat_le V)).mpr hNV).isSubnormal
      exact ((T515e.mem_khat_iff_of_sol_eq_bot hsolV).mp hx).2 M hMV
    exact le_inf (theorem_5_15_e h hX hKA hKX) ((khat_le V).trans inf_le_right)
  ·
    intro x hx
    obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxJ := ((T515e.mem_khat_iff_of_sol_eq_bot hsol).mp hxK).2
    rw [T515e.mem_khat_iff_of_sol_eq_bot hsolV]
    refine ⟨Subgroup.mem_inf.mpr ⟨khat_le G hxK, hxC⟩, fun M hM => ?_⟩
    rw [hlcal] at hM
    obtain ⟨J, hJ, rfl⟩ := hM
    have hxL : x ∈ Subgroup.normalizer ((orbitClosure J B : Subgroup Γ) : Set Γ) := by
      rw [orbitClosure_eq_sSup]
      exact T515g.mem_normalizer_sSup_of_forall fun J' hJ' =>
        hxJ J' (conjOrbit_subset_lcal hBG hJ hJ')
    exact T515g.mem_normalizer_inSubgroup_generalizedFitting
      (mem_normalizer_inf hxL (Subgroup.le_normalizer hxC))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
