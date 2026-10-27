module

public import CFSG.Milestones.ASVolI.C61.PAppDD0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61Base

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace GCfg

variable {T M H S L : Subgroup G} (C : GCfg T M H S L)
include C

theorem card_Q : Nat.card ↥(pCoreOf 2 H) = 16 * Nat.card ↥(blockD S L) := by
  have h := B2F.card_sup_mul_card_inf_of_commute
    (fun u hu d hd => C.U_comm_D hu hd : ∀ u ∈ C.U, ∀ d ∈ blockD S L, u * d = d * u)
  rw [C.U_inf_D, Subgroup.card_bot, C.card_U] at h
  rw [C.Q_eq]
  omega

end GCfg

namespace GMate
open CFSG.QuasithinUnique.AppD.GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)
include C m

theorem Q_isMax : IsMaxElemAbelian S (pCoreOf 2 H) :=
  ⟨C.hQS, GMate.Q_elem (m := m) C, fun B hBS hBe => by
    obtain ⟨-, hcard, hle, -⟩ := C.aU_spec hBe hBS
    exact hcard.trans (Subgroup.card_le_of_le hle)⟩

theorem card_eq_Q {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    Nat.card ↥A = Nat.card ↥(pCoreOf 2 H) :=
  le_antisymm ((GMate.Q_isMax (m := m) C).2.2 A hA.1 hA.2.1) (hA.2.2 _ C.hQS (GMate.Q_elem (m := m) C))

theorem Qx_isMax : IsMaxElemAbelian S (conjR (pCoreOf 2 H) x) :=
  C56.isMaxElemAbelian_conjSubgroup (GMate.Q_isMax (m := m) C) m.xN

theorem J_eq_B : thompsonJ S = baum S := by
  refine le_antisymm (C5.thompsonJ_le_baum' S) ?_
  rw [GMate.B_eq_sup (m := m) C]
  refine sup_le ?_ (GammaExtra.le_thompsonJ (GMate.Q_isMax (m := m) C))
  exact (C5.conjSubgroup_mono C.hUQ x).trans (GammaExtra.le_thompsonJ (GMate.Qx_isMax (m := m) C))

end GMate

end CFSG.QuasithinUnique.burnsideC56_P.AppD
