module

public import CFSG.Quasithin.Background.RonanG1015Big
public import CFSG.Quasithin.Background.RonanG1015Inputs
public import CFSG.Quasithin.Background.RonanG1015OuterSp
public import CFSG.Quasithin.Background.RonanG1015Eight

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth CFSG.Quasithin.G11.P4InspSp

theorem nonSQTOuter : NonSQTOuter := by
  intro U _ _ _ f M K Q v hD hns α P _ _ _ hcomm
  rcases big_cases hD hns with ⟨-, hK, h6⟩ | ⟨q, hq, hM, hK, horb, n, hn, hcases⟩
  · subst hK
    exact indAll_spSub hD.symp h6 α
  · subst hK
    have hf : IsSymplectic f := hD.symp
    rcases hcases with ⟨hplus, h4⟩ | ⟨hminus, h3⟩
    · by_cases h5 : 5 ≤ n
      · exact indAll_orth_plus hf hq h5 hn hplus α
      · have hn4 : n = 4 := by omega
        subst hn4
        obtain ⟨hv0, hvp, hfull⟩ := hD.Q_trans
        have hqv : q v = 0 := ((horb v).1 ⟨1, M.one_mem, by simp⟩).2
        have hMO : M ≤ orthSub q := by
          rcases hM with rfl | rfl
          · exact le_rfl
          · exact g12o_omegaSub_le_orthSub hq hf
        have hK0 : ⁅orthSub q, orthSub q⁆ ≠ ⊥ := p4insporth_ne_bot hD.K_irr (by omega)
        have hsimple : IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ :=
          p4insporth_simple_plus hf hq (by norm_num) hn hplus
        have hna : ¬ ∀ x y : ↥⁅orthSub q, orthSub q⁆, x * y = y * x := by
          intro hc
          have hperf : ⁅⁅orthSub q, orthSub q⁆, ⁅orthSub q, orthSub q⁆⁆ =
              ⁅orthSub q, orthSub q⁆ := Subgroup.isPerfect_iff.1 hD.K_perf
          have hbot : ⁅⁅orthSub q, orthSub q⁆, ⁅orthSub q, orthSub q⁆⁆ = ⊥ := by
            rw [eq_bot_iff, Subgroup.commutator_le]
            intro a ha b hb
            have h' : a * b = b * a := congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)
            rw [Subgroup.mem_bot, commutatorElement_def]
            calc a * b * a⁻¹ * b⁻¹ = b * a * a⁻¹ * b⁻¹ := by rw [h']
              _ = 1 := by group
          exact hK0 (hperf ▸ hbot)
        have hZ : ∀ z : ↥⁅orthSub q, orthSub q⁆, (∀ m, z * m = m * z) → z = 1 := by
          intro z hz
          exact Subtype.ext (CFSG.LieType.ChevTwo.OrthBasic.eq_one_of_forall_commute hna z.2
            fun w hw => congrArg Subtype.val (hz ⟨w, hw⟩))
        exact eight_induced hf hq (by omega) hplus rfl hv0 hqv (hD.Q_le.trans hMO) hvp hfull hZ α
          hcomm
    · exact indAll_orth_minus hf hq h3 hn hminus α

end RonanG1015

end CFSG.Quasithin
