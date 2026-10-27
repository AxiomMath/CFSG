module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_conj_sup_twelve (P Q : Subgroup G) (g : G) :
    conjSubgroup (P ⊔ Q) g = conjSubgroup P g ⊔ conjSubgroup Q g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_sup _ _ _

namespace Nine3Choice

theorem nine_twelve_Ig_A (hc : Nine3Choice V T A K S X p g x) :
    ⁅conjSubgroup (nineI V K) g, A⁆ = ⊥ := by
  have hV : conjSubgroup A g⁻¹ = V := by
    rw [← hc.V_g, E3.conjSubgroup_conj_inv]
  have hIV : ⁅nineI V K, V⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc.core.nineI_le_centralizer
  have h := E3.conjSubgroup_commutator (nineI V K) (conjSubgroup A g⁻¹) g
  rw [E3.conjSubgroup_inv_conj, hV, hIV, E3.conjSubgroup_bot] at h
  exact h.symm

theorem conj_nineI_le_S (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S) :
    conjSubgroup (nineI V K) g ≤ S := by
  have h := E3.conjSubgroup_mono_left g (hc'.nineI_le_conj_S hI)
  rwa [E3.conjSubgroup_inv_conj] at h

theorem commutator_nineI_conj_le (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S) :
    ⁅nineI V K, conjSubgroup (nineI V K) g⁆ ≤ nineI V K ⊓ conjSubgroup (nineI V K) g := by
  refine le_inf ?_ ?_
  · have hIgN : conjSubgroup (nineI V K) g ≤ Subgroup.normalizer (nineI V K : Set G) :=
      fun b hb => conjSubgroup_eq_iff_mem_normalizer.mp
        (Nine3Core.conjSubgroup_nineI (hc.core.S_le_K (hc'.conj_nineI_le_S hI hb)))
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hIgN
  · have hKN : K ≤ Subgroup.normalizer (nineI V K : Set G) := fun k hk =>
      conjSubgroup_eq_iff_mem_normalizer.mp (Nine3Core.conjSubgroup_nineI hk)
    have hKgN : conjSubgroup K g ≤ Subgroup.normalizer (conjSubgroup (nineI V K) g : Set G) := by
      rw [← E3.conjSubgroup_normalizer]
      exact E3.conjSubgroup_mono_left g hKN
    have hIN : nineI V K ≤ Subgroup.normalizer (conjSubgroup (nineI V K) g : Set G) :=
      (hc.nineI_le_conj_S hI).trans ((E3.conjSubgroup_mono_left g hc.core.S_le_K).trans hKgN)
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hIN

theorem nine_twelve_H_le_normalizer (hc : Nine3Choice V T A K S X p g x)
    (hH : ⁅nineH V K, conjSubgroup (nineI V K) g⁆ ≤ nineI V K) :
    nineH V K ≤ normalizer (nineI0 V K g : Set G) := by
  have key : ∀ h ∈ nineH V K, conjSubgroup (nineI0 V K g) h ≤ nineI0 V K g := by
    intro h hh
    have hhK : h ∈ K := nineH_le_K hh
    have hIN : conjSubgroup (nineI V K) h = nineI V K := Nine3Core.conjSubgroup_nineI hhK
    have hhN : h ∈ normalizer (nineI V K : Set G) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hIN
    have hIg_le : conjSubgroup (conjSubgroup (nineI V K) g) h ≤ nineI0 V K g := by
      intro u hu
      have hu' : h * u * h⁻¹ ∈ conjSubgroup (nineI V K) g := mem_conjSubgroup_iff.mp hu
      have hcomm : ⁅h, h * u * h⁻¹⁆ ∈ nineI V K :=
        Subgroup.commutator_le.mp hH h hh (h * u * h⁻¹) hu'
      have hcomm' : ⁅h * u * h⁻¹, h⁆ ∈ nineI V K := by
        rw [(commutatorElement_inv h (h * u * h⁻¹)).symm]
        exact (nineI V K).inv_mem hcomm
      have hinv : ⁅h⁻¹, h * u * h⁻¹⁆ ∈ nineI V K := by
        rw [commutatorElement_inv_left]
        exact (Subgroup.mem_normalizer_iff''.mp hhN ⁅h * u * h⁻¹, h⁆).mp hcomm'
      have hu_eq : u = ⁅h⁻¹, h * u * h⁻¹⁆ * (h * u * h⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [hu_eq]
      exact (nineI V K ⊔ conjSubgroup (nineI V K) g).mul_mem
        (Subgroup.mem_sup_left hinv) (Subgroup.mem_sup_right hu')
    show conjSubgroup (nineI V K ⊔ conjSubgroup (nineI V K) g) h ≤ nineI0 V K g
    rw [nineThree_conj_sup_twelve, hIN]
    exact sup_le le_sup_left hIg_le
  intro h hh
  have h1 := key h hh
  have h2 := key h⁻¹ ((nineH V K).inv_mem hh)
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  refine le_antisymm h1 ?_
  have h3 := E3.conjSubgroup_mono_left h h2
  rwa [E3.conjSubgroup_inv_conj] at h3

end Nine3Choice

end CFSG.LocalAnalysis.WeakClosure81
