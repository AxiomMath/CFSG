module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePair

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_coreClaim (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) : ⁅nineH V K, conjSubgroup (nineI V K) g⁆ ≤ nineI V K := by
  have hIeq : conjSubgroup (nineI V K) g =
      ⨆ U, ⨆ _ : U ∈ omegaIn V K (nineE V K),
        conjSubgroup (U ⊓ pCoreOf 2 K) g := by
    unfold nineI
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
  let C : Subgroup G :=
    { carrier := {k : G | k ∈ K ∧ ∀ h ∈ nineH V K, ⁅h, k⁆ ∈ nineI V K}
      one_mem' := by
        refine ⟨K.one_mem, ?_⟩
        intro h _
        rw [commutatorElement_one_right]
        exact (nineI V K).one_mem
      mul_mem' := by
        rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
        refine ⟨K.mul_mem haK hbK, ?_⟩
        intro h hh
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hconj : a * ⁅h, b⁆ * a⁻¹ ∈ nineI V K := by
          have hmem : ⁅h, b⁆ ∈ conjSubgroup (nineI V K) a := by
            rw [Nine3Core.conjSubgroup_nineI haK]
            exact hb h hh
          exact mem_conjSubgroup_iff.mp hmem
        simpa only [mul_assoc] using (nineI V K).mul_mem (ha h hh) hconj
      inv_mem' := by
        rintro a ⟨haK, ha⟩
        refine ⟨K.inv_mem haK, ?_⟩
        intro h hh
        have hcomm : ⁅a, h⁆ ∈ nineI V K := by
          simpa only [commutatorElement_inv] using (nineI V K).inv_mem (ha h hh)
        rw [commutatorElement_inv_right]
        have hmem : ⁅a, h⁆ ∈ conjSubgroup (nineI V K) a⁻¹ := by
          rw [Nine3Core.conjSubgroup_nineI (K.inv_mem haK)]
          exact hcomm
        simpa only [inv_inv] using mem_conjSubgroup_iff.mp hmem }
  have hle : conjSubgroup (nineI V K) g ≤ C := by
    rw [hIeq]
    refine iSup_le fun U => iSup_le fun hU => ?_
    intro x hx
    set w : G := g * x * g⁻¹ with hwdef
    have hw : w ∈ U ⊓ pCoreOf 2 K := by
      rw [hwdef]
      exact mem_conjSubgroup_iff.mp hx
    have hxeq : x = g⁻¹ * w * g := by
      rw [hwdef]
      group
    refine ⟨?_, ?_⟩
    · have hxI : x ∈ conjSubgroup (nineI V K) g :=
        E3.conjSubgroup_mono_left g (le_iSup₂_of_le U hU le_rfl) hx
      exact hc.core.S_le_K (hc'.conj_nineI_le_S hI hxI)
    · rw [hxeq]
      intro h hh
      by_cases hUS : U ≤ S
      · have hUΩ : U ∈ nineOmegaIn V K S := ⟨hU.1, hUS⟩
        by_cases hUA : U = A
        · have hwA : w ∈ A ⊓ pCoreOf 2 K := by simpa [hUA] using hw
          have hjA : g⁻¹ * w * g ∈ conjSubgroup A g := by
            rw [mem_conjSubgroup_iff]
            have : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
            rw [this]
            exact hwA.1
          have hjV : g⁻¹ * w * g ∈ V := by
            rw [← hc.A_g]
            exact hjA
          have hmemC : h ∈ centralizer (V : Set G) := hc.core.nineH_le_centralizer hh
          have hcomm1 : ⁅h, g⁻¹ * w * g⁆ = 1 :=
            (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hmemC)
              (g⁻¹ * w * g) hjV
          rw [hcomm1]
          exact (nineI V K).one_mem
        · have hUΔ : U ∈ nineDelta V S :=
            hc.core.mem_nineDelta_iff.mpr (Or.inr hUΩ)
          have hUgΔ : conjSubgroup U g ∈ nineDelta V S := hc.conj_mem_nineDelta hUΔ
          have hUgV : conjSubgroup U g ≠ V := by
            intro hV
            apply hUA
            calc U = conjSubgroup (conjSubgroup U g) g⁻¹ := by
                    rw [E3.conjSubgroup_conj_inv]
              _ = conjSubgroup V g⁻¹ := by rw [hV]
              _ = A := by rw [← hc.A_g, E3.conjSubgroup_conj_inv]
          have hUgΩ : conjSubgroup U g ∈ nineOmegaIn V K S :=
            (hc.core.mem_nineDelta_iff.mp hUgΔ).resolve_left hUgV
          have hUgA : conjSubgroup U g ≠ A := by
            intro hA
            have hUeqV : U = V := by
              calc U = conjSubgroup (conjSubgroup U g) g⁻¹ := by
                      rw [E3.conjSubgroup_conj_inv]
                _ = conjSubgroup A g⁻¹ := by rw [hA]
                _ = V := by rw [← hc.V_g, E3.conjSubgroup_conj_inv]
            exact hc.core.V_not_mem_nineOmegaIn (hUeqV ▸ hUΩ)
          have hEq := hc.inf_pCoreOf_eq_inf_conj hI hUgΩ hUgA
          have hjI : g⁻¹ * w * g ∈ nineI V K := by
            have hjU : g⁻¹ * w * g ∈ conjSubgroup U g := by
              rw [mem_conjSubgroup_iff]
              have : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
              rw [this]
              exact hw.1
            have hjRg : g⁻¹ * w * g ∈ conjSubgroup (pCoreOf 2 K) g := by
              rw [mem_conjSubgroup_iff]
              have : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
              rw [this]
              exact hw.2
            have hjInf : g⁻¹ * w * g ∈ conjSubgroup U g ⊓ pCoreOf 2 K := by
              rw [hEq]
              exact ⟨hjU, hjRg⟩
            exact hc.inf_pCoreOf_le_nineI hUgΩ hjInf
          have hhK : h ∈ K := Nine3Choice.nineH_le_K hh
          have hconj : h * (g⁻¹ * w * g) * h⁻¹ ∈ nineI V K := by
            have hmem : g⁻¹ * w * g ∈ conjSubgroup (nineI V K) h := by
              rw [Nine3Core.conjSubgroup_nineI hhK]
              exact hjI
            exact mem_conjSubgroup_iff.mp hmem
          rw [commutatorElement_def]
          exact (nineI V K).mul_mem hconj ((nineI V K).inv_mem hjI)
      · exact nine3_core_gen hc hc' hI h35 hU hUS hw h hh
  change ⁅nineH V K, conjSubgroup (nineI V K) g⁆ ≤ nineI V K
  rw [Subgroup.commutator_le]
  intro h hh j hj
  exact (hle hj).2 h hh

end CFSG.LocalAnalysis.WeakClosure81
