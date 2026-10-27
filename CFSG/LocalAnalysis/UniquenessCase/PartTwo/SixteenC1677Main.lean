module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Fin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem r16_57_62_not_case167_7F (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h126 : R126 D) (h127 : R127 D) (h119 : F11.R119 D) (h183 : W3Thm183 G) (h145 : Thm145 D)
    (h21 : R1621 D) (h129 : R129_1 D) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hH : Hyp16 D V₀ V) : ¬ Case167_7F D V₀ V hV := by
  intro h7
  have h22 : R1622 D := R1622_of_R1621 D hSg h1219 h21
  have h59 := h7.sixteen_fiftyNine D hx hSg h1219 h21 h22 h129 h61 hH
  have h60 := h7.sixteen_sixty D hx h61 h66 h127 (r1114_holds D hx h61) h183 hH h59.2
  have h24 := h7.trichotomy D h126 hSg h1219 hx h61 hH
  obtain ⟨-, hC⟩ := h7.sixteen_sixtyOne D hH h24 h59.2 h60
  obtain ⟨z, hz, -, hzM⟩ :=
    h7.sixteen_sixtyTwo D hx h61 h127 (r119W_of_r119 D h119) h145 hH h60
  apply hC
  have hzmem : z ∈ V ⊓ centralizer (D.T : Set G) := by
    rw [hz]
    exact Subgroup.mem_zpowers z
  obtain ⟨hzV, hzT⟩ := Subgroup.mem_inf.1 hzmem
  have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D hH.hyp125.inCalV
  have hzc : ∀ t ∈ D.T, z * t = t * z := fun t ht =>
    (Subgroup.mem_centralizer_iff.1 hzT t ht).symm
  refine le_trans ?_ hzM
  refine Subgroup.centralizer_le ?_
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact mem_cClos_of_mem_center D V 2 (hVT hzV) hzc

@[expose] def R16_57F (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    ¬ Case167_7F D V₀ V hV

theorem r16_57F_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h126 : R126 D) (h127 : R127 D)
    (h119 : F11.R119 D) (h183 : W3Thm183 G) (h145 : Thm145 D) (h21 : R1621 D)
    (h129 : R129_1 D) : R16_57F D := fun _ V _ hV hS =>
  r16_57_62_not_case167_7F D hSg h1219 hx h61 h66 h126 h127 h119 h183 h145 h21 h129 hV
    hS.setting.hyp16

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
