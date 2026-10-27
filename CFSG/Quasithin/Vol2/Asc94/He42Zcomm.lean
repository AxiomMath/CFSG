module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

theorem HeSetup.stepZcomm (S : HeSetup G) (hB : S.BaseFacts) : S.StepZcomm := by
  have hT := S.hD.hT
  have hAL : S.A ≤ S.L := (hB.A_le_J.trans hB.J_le_K).trans (hB.K_le_L1.trans le_sup_left)
  have hA'L : S.A' ≤ S.L := (hB.A'_le_J.trans hB.J_le_K).trans (hB.K_le_L2.trans le_sup_right)
  set CL := (commutator ↥S.L).map S.L.subtype with hCL
  have key : ∀ M : M2, ∀ y ∈ S.A ⊓ S.A', S.m y = M → y ∈ CL := by
    intro M
    induction M using Matrix.induction_on' with
    | h_zero =>
      intro y hy hym
      have : y = 1 := hT.minj y hy 1 (Subgroup.one_mem _) (by rw [hym, hT.m_one])
      subst this
      exact CL.one_mem
    | h_add p q hp hq =>
      intro y hy hym
      obtain ⟨xp, hxp, hxpm⟩ := hT.msurj p
      obtain ⟨xq, hxq, hxqm⟩ := hT.msurj q
      have hyy : y = xp * xq := hT.minj y hy _ ((S.A ⊓ S.A').mul_mem hxp hxq) (by
        rw [hym, hT.mmul xp hxp xq hxq, hxpm, hxqm])
      rw [hyy]
      exact CL.mul_mem (hp xp hxp hxpm) (hq xq hxq hxqm)
    | h_std_basis i j c =>
      intro y hy hym
      have hc : c = 0 ∨ c = 1 := by
        clear hym; revert c; decide
      rcases hc with rfl | rfl
      · have : y = 1 := hT.minj y hy 1 (Subgroup.one_mem _) (by
          rw [hym, hT.m_one]; simp)
        subst this
        exact CL.one_mem
      · obtain ⟨xi, hxi, hxiu⟩ := hT.cu.surj (Pi.single i 1)
        obtain ⟨yj, hyj, hyjw⟩ := hT.cw.surj (Pi.single j 1)
        obtain ⟨hzmem, hzm⟩ := hT.comm xi hxi yj hyj
        have hyz : y = xi * yj * xi⁻¹ * yj⁻¹ := hT.minj y hy _ hzmem (by
          rw [hym, hzm, hxiu, hyjw, ← Matrix.single_eq_single_vecMulVec_single])
        rw [hyz]
        exact ⟨_, Subgroup.commutator_mem_commutator
          (Subgroup.mem_top (⟨xi, hAL hxi⟩ : ↥S.L))
          (Subgroup.mem_top (⟨yj, hA'L hyj⟩ : ↥S.L)), rfl⟩
  intro z hz
  exact key _ z hz rfl

end CFSG.Quasithin.A94.He42
