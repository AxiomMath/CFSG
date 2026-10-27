module

public import CFSG.Quasithin.MS93.S45Z

public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45 CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Clause

variable {G : Type} [Group G]

@[expose] def MS93Case13W (V L : Subgroup G) : Prop :=
  ∃ W : Subgroup G, frattiniIn V ≤ W ∧ W ≤ V ⊓ Subgroup.centralizer (frattiniIn V : Set G) ∧
    L ≤ Subgroup.normalizer (W : Set G) ∧ (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧
    ¬ W ≤ centerOf (V ⊓ Subgroup.centralizer (frattiniIn V : Set G))

end Clause

section BaseA

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem caseW_of_baseA (h : PUHyp M T L) {W : Subgroup (puAmalgam h.le).Universal}
    (h₁ : frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ≤ W)
    (h₂ : W ≤ ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓ Subgroup.centralizer
      (frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ : Set _))
    (h₃ : Ltil h.le L (baseA _) ≤ Subgroup.normalizer (W : Set _))
    (h₄ : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (h₅ : ¬ W ≤ centerOf (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
      Subgroup.centralizer (frattiniIn ⁅Qv (puAmalgam h.le) (baseA _),
        Ltil h.le L (baseA _)⁆ : Set _))) :
    MS93Case13W (Vq M L) L := by
  have hOM : pCoreOf 2 M ≤ M := pCoreOf_le' M
  have hVM : Vq M L ≤ M := Vq_le h.L_le
  have hQ : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hLt : Ltil h.le L (baseA _) = imM h.le L :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)
  have hV : ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ = imM h.le (Vq M L) := by
    rw [hQ, hLt, imM_commutator h.le hOM h.L_le]
  set V := Vq M L with hVdef
  have hΦM : frattiniIn V ≤ M := (Subgroup.map_subtype_le _).trans hVM
  have hCM : V ⊓ Subgroup.centralizer (frattiniIn V : Set G) ≤ M := inf_le_left.trans hVM
  have eΦ : imM h.le (frattiniIn V) =
      frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ := by
    rw [imM_frattiniIn h.le hVM, hV]
  have eC : imM h.le (V ⊓ Subgroup.centralizer (frattiniIn V : Set G)) =
      ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓ Subgroup.centralizer
        (frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ : Set _) := by
    rw [imM_inf_centralizer h.le V hΦM, eΦ, hV]
  have hWM : W ≤ imM h.le M := by
    refine (h₂.trans inf_le_left).trans ?_
    rw [hV]
    exact imM_mono h.le hVM
  have hW'M : S46.imMPull h.le W ≤ M := S46.imMPull_le h.le W
  have hiW : imM h.le (S46.imMPull h.le W) = W := S46.imM_imMPull h.le hWM
  refine ⟨S46.imMPull h.le W, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← imM_le_imM_iff h.le hΦM, hiW, eΦ]
    exact h₁
  · rw [← imM_le_imM_iff h.le hW'M, hiW, eC]
    exact h₂
  · rw [Subgroup.le_normalizer_iff_commutator_le_left,
      ← imM_le_imM_iff h.le (commutator_le_of_le hW'M h.L_le),
      imM_commutator h.le hW'M h.L_le, hiW, ← hLt]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp h₃
  · intro x hx y hy
    have hxW : (puAmalgam h.le).ofA ⟨x, hW'M hx⟩ ∈ imM h.le (S46.imMPull h.le W) :=
      (S46.ofA_mem_imM h.le ⟨x, hW'M hx⟩).mpr hx
    have hyW : (puAmalgam h.le).ofA ⟨y, hW'M hy⟩ ∈ imM h.le (S46.imMPull h.le W) :=
      (S46.ofA_mem_imM h.le ⟨y, hW'M hy⟩).mpr hy
    rw [hiW] at hxW hyW
    have := h₄ _ hxW _ hyW
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective this)
  · intro hcen
    apply h₅
    have := imM_mono h.le hcen
    rwa [hiW, S46.imM_centerOf h.le hCM, eC] at this

end BaseA

end CFSG.Quasithin.SzMSW
