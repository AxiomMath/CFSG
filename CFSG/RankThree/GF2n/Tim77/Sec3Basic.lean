module

public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.RankThree.GF2n.Tim77.Cor2Hyp
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

namespace Sec3Ctx

theorem exists_abar_eq (h : Sec3Ctx A Abar S₀ B) : ∃ g : G, Abar = conjSubgroup g A :=
  h.nota.choice.1

theorem abar0_eq (_h : Sec3Ctx A Abar S₀ B) :
    Section3.Abar0 A Abar = Abar ⊓ normalizer (A : Set G) := by
  unfold Section3.Abar0 normalizerIn; rfl

theorem a0_eq (_h : Sec3Ctx A Abar S₀ B) :
    Section3.A0 A Abar = A ⊓ normalizer (Abar : Set G) := by
  unfold Section3.A0 normalizerIn; rfl

theorem m_eq (_h : Sec3Ctx A Abar S₀ B) :
    Section3.M A Abar = Section3.A0 A Abar ⊔ Section3.Abar0 A Abar := by
  unfold Section3.M; rfl

theorem x_eq (_h : Sec3Ctx A Abar S₀ B) : Section3.X A Abar = A ⊔ Abar := by
  unfold Section3.X; rfl

theorem setup_symm (h : Sec3Ctx A Abar S₀ B) :
    Prop24Setup Abar A (Section3.Abar0 A Abar) (Section3.A0 A Abar)
      (Section3.Abar0 A Abar ⊔ Section3.A0 A Abar) := by
  obtain ⟨g, hg⟩ := h.exists_abar_eq
  refine
    { elem := hg ▸ isElemAbelian_conj h.hyp.elemAbelian g
      ti := hg ▸ isTI_conjSubgroup h.hyp.ti g
      conj := ⟨g⁻¹, ?_⟩
      hL := rfl
      hLb := rfl
      hM := rfl
      ne_bot := h.nota.choice.2.1.1
      ne := h.nota.choice.2.1.2 }
  rw [hg, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem setup (h : Sec3Ctx A Abar S₀ B) :
    Prop24Setup A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar) (Section3.M A Abar) := by
  have S := h.setup_symm.symm
  rwa [sup_comm] at S

theorem a0_ne_bot (h : Sec3Ctx A Abar S₀ B) : Section3.A0 A Abar ≠ ⊥ := h.setup.ne_bot

theorem a0_ne (h : Sec3Ctx A Abar S₀ B) : Section3.A0 A Abar ≠ A := h.setup.ne

theorem inf_abar_eq_bot (h : Sec3Ctx A Abar S₀ B) : A ⊓ Abar = ⊥ := h.setup.inf_eq_bot

theorem b_le_centralizer (h : Sec3Ctx A Abar S₀ B) : B ≤ centralizer (A : Set G) :=
  fun _ hb => (h.nota.le hb).2

theorem b_le_s0 (h : Sec3Ctx A Abar S₀ B) : B ≤ S₀ := fun _ hb => (h.nota.le hb).1

theorem isPGroup_s0 (h : Sec3Ctx A Abar S₀ B) : IsPGroup 2 S₀ := h.nota.sylow.1

theorem s0_le_normalizer (h : Sec3Ctx A Abar S₀ B) : S₀ ≤ normalizer (A : Set G) :=
  h.nota.sylow.2.1

theorem a_le_s0 (h : Sec3Ctx A Abar S₀ B) : A ≤ S₀ := le_sup_left.trans h.nota.contains

theorem abar0_le_s0 (h : Sec3Ctx A Abar S₀ B) : Section3.Abar0 A Abar ≤ S₀ :=
  le_sup_right.trans h.nota.contains

end Sec3Ctx

end CFSG.RankThree.GF2n.Tim77
