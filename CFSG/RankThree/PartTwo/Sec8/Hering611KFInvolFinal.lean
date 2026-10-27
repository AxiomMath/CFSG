module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolA9G
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolSp48
import CFSG.RankThree.PartTwo.Sec8.Hering611KFBridge
public import CFSG.RankThree.PartTwo.Sec8.Hering611Facts

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def KF611InvolSp62K : Prop :=
  ∀ (Kb : Type) [Group Kb] [Finite Kb], StatedClassicalModel Kb .PSp 3 2 1 →
    ∀ α : MulAut Kb, α ^ 3 = 1 →
    ∀ P ∈ thetaComponentsIn (Item426.fixSub α),
      Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* alternatingGroup (Fin 6)) →
      ∃ t : Kb, t ^ 2 = 1 ∧ α t = t ∧ S6Act P t

section Final


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem exists_field_involution_sp62 (hSp62 : KF611InvolSp62K) (h45 : Sec4.Item4_5)
    (C : Cfg611 G A c L E T d S K)
    (hK : StatedClassicalModel (K ⧸ aschbacherSolvableCore 3 K) .PSp 3 2 1) :
    ∃ s : G, s ^ 2 = 1 ∧ KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L s .field := by
  obtain ⟨hcN, h3, -, hP, hPq⟩ := exists_bridge_image h45 C
  obtain ⟨t, ht2, hfix, hS6⟩ := hSp62 (K ⧸ aschbacherSolvableCore 3 K) hK _ h3 _ hP hPq
  exact exists_field_involution_fix h45 C ht2 hfix hS6

end Final

@[expose] def KF611Sp62Inner : Prop :=
  ∀ (Kb : Type) [Group Kb] [Finite Kb], StatedClassicalModel Kb .PSp 3 2 1 →
    ∀ α : MulAut Kb, α ^ 3 = 1 → ∃ γ : Kb, γ ^ 3 = 1 ∧ α = MulAut.conj γ

@[expose] def KF611Sp62Cent : Prop :=
  ∀ (Kb : Type) [Group Kb] [Finite Kb], StatedClassicalModel Kb .PSp 3 2 1 →
    ∀ γ : Kb, γ ^ 3 = 1 →
    ∀ P ∈ thetaComponentsIn (Subgroup.centralizer ({γ} : Set Kb)),
      Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* alternatingGroup (Fin 6)) →
      ∃ Cg : Subgroup Kb, Cg ≤ Subgroup.centralizer ({γ} : Set Kb) ∧ P ≤ Cg ∧
        Nonempty (Cg ≃* Equiv.Perm (Fin 6))

theorem kF611InvolSp62K_of (hInn : KF611Sp62Inner) (hCent : KF611Sp62Cent) : KF611InvolSp62K := by
  intro Kb _ _ hK α hα3 P hP hPq
  obtain ⟨γ, hγ3, rfl⟩ := hInn Kb hK α hα3
  have hfix : Item426.fixSub (MulAut.conj γ) = Subgroup.centralizer ({γ} : Set Kb) := by
    ext x
    rw [Item426.mem_fixSub, Subgroup.mem_centralizer_singleton_iff]
    change γ * x * γ⁻¹ = x ↔ x * γ = γ * x
    constructor
    · intro h
      calc x * γ = γ * x * γ⁻¹ * γ := by rw [h]
        _ = γ * x := by group
    · intro h
      calc γ * x * γ⁻¹ = x * γ * γ⁻¹ := by rw [h]
        _ = x := by group
  rw [hfix] at hP
  obtain ⟨Cg, hCg, hPCg, ⟨ι⟩⟩ := hCent Kb hK γ hγ3 P hP hPq
  obtain ⟨ePA⟩ := hPq
  have hq : Nat.card (P ⧸ aschbacherSolvableCore 3 P) = 360 := by
    rw [Nat.card_congr ePA.toEquiv, nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  obtain ⟨t, htC, ht2, hS6⟩ := exists_s6act_of_perm Cg ι hPCg
    (isPerfect_of_mem_thetaComponentsIn hP) hq
  refine ⟨t, ht2, ?_, hS6⟩
  have := Subgroup.mem_centralizer_singleton_iff.mp (hCg htC)
  change γ * t * γ⁻¹ = t
  calc γ * t * γ⁻¹ = t * γ * γ⁻¹ := by rw [this]
    _ = t := by group

section Final2


theorem kF611Invol_of (h45 : Sec4.Item4_5) (hSp62 : KF611InvolSp62K) : KF611Invol := by
  intro G _ _ A c L E T d S K C hprem
  rcases hprem with hK | ⟨hA9, hcK⟩ | ⟨hSp, hcf⟩
  · exact exists_field_involution_sp62 hSp62 h45 C hK
  · exact exists_field_involution_a9 h45 C hA9 hcK
  · exact exists_field_involution_sp48 h45 C hSp hcf

end Final2

end CFSG.RankThree.PartTwo.Sec8.Hering611
