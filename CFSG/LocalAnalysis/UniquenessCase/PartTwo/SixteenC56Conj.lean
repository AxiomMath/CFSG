module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G]

private theorem mem_cElt_conj_iff [Finite G] (M V₀ : Subgroup G) (g v x : G) :
    x ∈ F11.CElt (conjSubgroup M g) (conjSubgroup V₀ g) v ↔
      g * x * g⁻¹ ∈ F11.CElt M V₀ (g * v * g⁻¹) := by
  show (x ∈ conjSubgroup M g ∧ x ∈ normalizer (conjSubgroup V₀ g : Set G) ∧
      x * v * x⁻¹ * v⁻¹ ∈ conjSubgroup V₀ g) ↔
    (g * x * g⁻¹ ∈ M ∧ g * x * g⁻¹ ∈ normalizer (V₀ : Set G) ∧
      (g * x * g⁻¹) * (g * v * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ ∈ V₀)
  rw [mem_conjSubgroup_iff, ← E3.conjSubgroup_normalizer, mem_conjSubgroup_iff,
    mem_conjSubgroup_iff]
  have e : g * (x * v * x⁻¹ * v⁻¹) * g⁻¹ =
      (g * x * g⁻¹) * (g * v * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ := by group
  rw [e]

theorem cTilde_conjSubgroup [Finite G] (M V₀ V : Subgroup G) (g : G) :
    F11.CTilde (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) =
      conjSubgroup (F11.CTilde M V₀ V) g := by
  ext x
  rw [mem_conjSubgroup_iff]
  unfold F11.CTilde
  simp only [Subgroup.mem_iInf, mem_conjSubgroup_iff]
  constructor
  · intro h w hw
    have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    have h1 := (mem_cElt_conj_iff M V₀ g (g⁻¹ * w * g) x).1
      (h (g⁻¹ * w * g) (by rw [e]; exact hw))
    rwa [e] at h1
  · intro h v hv
    exact (mem_cElt_conj_iff M V₀ g v x).2 (h _ hv)

theorem oDual_iff_oFirst_inv (n : ℕ) (M V₀ V : Subgroup G) (g : G) :
    ODual n M V₀ V g ↔ OFirst n M V₀ V g⁻¹ := by
  unfold ODual OFirst
  have h1 : V ≤ conjSubgroup M g ↔ conjSubgroup V g⁻¹ ≤ M :=
    E3.le_conjSubgroup_iff_inv_le g
  have h2 : E3.mQuot (conjSubgroup V g) M = E3.mQuot V (conjSubgroup M g⁻¹) := by
    have := E3.mQuot_conjSubgroup (conjSubgroup V g) M g⁻¹
    rw [E3.conjSubgroup_conj_inv] at this
    exact this.symm
  have h3 : conjSubgroup V₀ g ⊓ M ≠ ⊥ ↔ V₀ ⊓ conjSubgroup M g⁻¹ ≠ ⊥ := by
    rw [ne_eq, ne_eq, ← conjSubgroup_eq_bot_iff (g := g⁻¹), E3.conjSubgroup_inf,
      E3.conjSubgroup_conj_inv]
  rw [h1, h2]
  simp only [h3]

theorem twoDual_iff_twoFirst_inv (n : ℕ) (M V : Subgroup G) (g : G) :
    TwoDual n M V g ↔ TwoFirst n M V g⁻¹ := by
  have key : ∀ (h : G) (I : Subgroup G),
      (V ⊓ conjSubgroup M h ⊓ centralizer (I : Set G) ≤ centralizer (conjSubgroup V h : Set G)) ↔
        (conjSubgroup V h⁻¹ ⊓ M ⊓ centralizer (conjSubgroup I h⁻¹ : Set G) ≤
          centralizer (V : Set G)) := by
    intro h I
    rw [← E3.conjSubgroup_le_conjSubgroup_iff h⁻¹, E3.conjSubgroup_inf, E3.conjSubgroup_inf,
      E3.conjSubgroup_conj_inv, E3.conjSubgroup_centralizer, E3.conjSubgroup_centralizer,
      E3.conjSubgroup_conj_inv]
  constructor
  · rintro ⟨I, hI, hne⟩
    refine ⟨conjSubgroup I g⁻¹, ?_, fun hle => hne ((key g I).2 hle)⟩
    have h1 : conjSubgroup I g⁻¹ ∈
        E3.gammaSet (conjSubgroup V g) n (conjSubgroup (conjSubgroup V g ⊓ M) g⁻¹) :=
      E3.conj_mem_gammaSet g⁻¹ hI
    rwa [E3.gammaSet_conjV, E3.conjSubgroup_inf, E3.conjSubgroup_conj_inv] at h1
  · rintro ⟨I, hI, hne⟩
    refine ⟨conjSubgroup I g, ?_, fun hle => hne ?_⟩
    · have h1 : conjSubgroup I g ∈
          E3.gammaSet V n (conjSubgroup (V ⊓ conjSubgroup M g⁻¹) g) :=
        E3.conj_mem_gammaSet g hI
      rw [← E3.gammaSet_conjV (V := V) g, E3.conjSubgroup_inf, E3.conjSubgroup_inv_conj] at h1
      exact h1
    · have := (key g (conjSubgroup I g)).1 hle
      rwa [E3.conjSubgroup_conj_inv] at this

theorem oneDual_iff_oneFirst_inv [Finite G] (M V₀ V : Subgroup G) (g : G) :
    OneDual M V₀ V g ↔ OneFirst M V₀ V g⁻¹ := by
  unfold OneDual OneFirst
  rw [← E3.conjSubgroup_le_conjSubgroup_iff g⁻¹, E3.conjSubgroup_inf, E3.conjSubgroup_inf,
    E3.conjSubgroup_conj_inv, E3.conjSubgroup_centralizer, E3.conjSubgroup_inf,
    E3.conjSubgroup_conj_inv, cTilde_conjSubgroup, E3.conjSubgroup_conj_inv]

private theorem conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g :=
  Subgroup.map_sup A B _

theorem inCalO2_inv {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : InCalO2 n M V₀ V g) :
    InCalO2 n M V₀ V g⁻¹ := by
  obtain ⟨⟨hF, hD⟩, hTF, hTD, hnp⟩ := h
  refine ⟨⟨(oDual_iff_oFirst_inv n M V₀ V g).1 hD, ?_⟩,
    (twoDual_iff_twoFirst_inv n M V g).1 hTD, ?_, ?_⟩
  · rw [oDual_iff_oFirst_inv, inv_inv]
    exact hF
  · rw [twoDual_iff_twoFirst_inv, inv_inv]
    exact hTF
  · intro hp
    apply hnp
    have h1 : IsPGroup 2 ↥(conjSubgroup (V ⊔ conjSubgroup V g⁻¹) g) :=
      E3.isPGroup_conjSubgroup hp g
    have h2 : conjSubgroup (V ⊔ conjSubgroup V g⁻¹) g = V ⊔ conjSubgroup V g := by
      rw [conjSubgroup_sup, E3.conjSubgroup_inv_conj, sup_comm]
    rwa [h2] at h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
