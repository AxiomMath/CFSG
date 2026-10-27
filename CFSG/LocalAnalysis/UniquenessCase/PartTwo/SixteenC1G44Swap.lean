module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.SixSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem s16c1G44_mem_cTilde_iff {M V₀ V : Subgroup G} {x : G} :
    x ∈ F11.CTilde M V₀ V ↔ x ∈ M ∧ x ∈ normalizer (V₀ : Set G) ∧ CentralizesMod V₀ V x := by
  unfold F11.CTilde
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h
    obtain ⟨hM, hN, -⟩ := h 1 V.one_mem
    exact ⟨hM, hN, fun v hv => (h v hv).2.2⟩
  · rintro ⟨hM, hN, hC⟩ v hv
    exact ⟨hM, hN, hC v hv⟩

theorem s16c1G44_cTilde_conj [Finite G] (M V₀ V : Subgroup G) (g : G) :
    F11.CTilde (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) =
      conjSubgroup (F11.CTilde M V₀ V) g := by
  ext x
  rw [mem_conjSubgroup_iff, s16c1G44_mem_cTilde_iff, s16c1G44_mem_cTilde_iff]
  refine and_congr mem_conjSubgroup_iff (and_congr ?_ ?_)
  · rw [← E3.conjSubgroup_normalizer, mem_conjSubgroup_iff]
  · exact CFSG.LocalAnalysis.WeakClosure81.centralizesMod_conj' V₀ V x g

theorem s16c1G44_oneDual_iff [Finite G] (M V₀ V : Subgroup G) (g : G) :
    OneDual M V₀ V g ↔ OneFirst M V₀ V g⁻¹ := by
  unfold OneDual OneFirst
  rw [← E3.conjSubgroup_le_conjSubgroup_iff g⁻¹, E3.conjSubgroup_inf, E3.conjSubgroup_inf,
    E3.conjSubgroup_centralizer, E3.conjSubgroup_inf, E3.conjSubgroup_conj_inv,
    E3.conjSubgroup_conj_inv, s16c1G44_cTilde_conj, E3.conjSubgroup_conj_inv]

theorem s16c1G44_le_conj_iff {A B : Subgroup G} (g : G) :
    A ≤ conjSubgroup B g ↔ conjSubgroup A g⁻¹ ≤ B := by
  rw [← E3.conjSubgroup_le_conjSubgroup_iff g⁻¹, E3.conjSubgroup_conj_inv]

theorem s16c1G44_oDual_iff (n : ℕ) (M V₀ V : Subgroup G) (g : G) :
    ODual n M V₀ V g ↔ OFirst n M V₀ V g⁻¹ := by
  unfold ODual OFirst
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact not_congr (s16c1G44_le_conj_iff (A := V) (B := M) g)
  · rw [← E3.mQuot_conjSubgroup (conjSubgroup V g) M g⁻¹, E3.conjSubgroup_conj_inv]
  · refine imp_congr_right fun _ => ?_
    rw [ne_eq, ne_eq, ← conjSubgroup_eq_bot_iff (g := g⁻¹), E3.conjSubgroup_inf,
      E3.conjSubgroup_conj_inv]

theorem s16c1G44_oFirst_iff (n : ℕ) (M V₀ V : Subgroup G) (g : G) :
    OFirst n M V₀ V g ↔ ODual n M V₀ V g⁻¹ := by
  rw [s16c1G44_oDual_iff, inv_inv]

theorem s16c1G44_inCalO_inv (n : ℕ) (M V₀ V : Subgroup G) (g : G) :
    InCalO n M V₀ V g ↔ InCalO n M V₀ V g⁻¹ := by
  unfold InCalO
  rw [s16c1G44_oDual_iff, s16c1G44_oFirst_iff, and_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
