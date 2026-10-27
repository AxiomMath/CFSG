module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreHbar
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeTwelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_conj_iSup {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

theorem nine3_exists_hbar_aut (hc : Nine3Choice V T A K S X p g x) {k : G} (hk : k ∈ K) :
    ∃ φ : Nine3Hbar V K →* Nine3Hbar V K, Function.Injective φ ∧
      (∀ h h' : ↥(nineH V K), (h' : G) = k * h * k⁻¹ →
        φ (QuotientGroup.mk h) = QuotientGroup.mk h') ∧
      ∀ d ∈ Nine3Dbar V K, φ d ∈ Nine3Dbar V K := by
  have hHle : ∀ {y : G}, y ∈ K → conjSubgroup (nineH V K) y ≤ nineH V K := by
    intro y hy
    unfold nineH
    rw [nine3_conj_iSup]
    refine iSup_le fun U => ?_
    rw [nine3_conj_iSup]
    refine iSup_le fun hU => ?_
    exact le_iSup₂_of_le (conjSubgroup U y) (conjSubgroup_mem_omegaIn hU hy) le_rfl
  have hHconj : conjSubgroup (nineH V K) k = nineH V K := by
    refine le_antisymm (hHle hk) ?_
    have h1 : conjSubgroup (conjSubgroup (nineH V K) k⁻¹) k ≤
        conjSubgroup (nineH V K) k :=
      E3.conjSubgroup_mono_left k (hHle (K.inv_mem hk))
    rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
      CFSG.Quasithin.conjSubgroup_one] at h1
  have hHmem : ∀ h : ↥(nineH V K), k * (h : G) * k⁻¹ ∈ nineH V K := by
    intro h
    have hh : (h : G) ∈ conjSubgroup (nineH V K) k := by rw [hHconj]; exact h.2
    exact mem_conjSubgroup_iff.mp hh
  let ψ : ↥(nineH V K) →* ↥(nineH V K) :=
    { toFun := fun h => ⟨k * (h : G) * k⁻¹, hHmem h⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        group }
  have hpre : ∀ h : ↥(nineH V K),
      ψ h ∈ (nineI V K).subgroupOf (nineH V K) ↔
        h ∈ (nineI V K).subgroupOf (nineH V K) := by
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have h1 := (mem_conjSubgroup_iff (A := nineI V K) (g := k) (x := (h : G)))
    rw [Nine3Core.conjSubgroup_nineI hk] at h1
    exact h1.symm
  have hmap : (nineI V K).subgroupOf (nineH V K) ≤
      ((nineI V K).subgroupOf (nineH V K)).comap ψ := by
    intro h hh
    rw [Subgroup.mem_comap]
    exact (hpre h).mpr hh
  let φ : Nine3Hbar V K →* Nine3Hbar V K :=
    QuotientGroup.map ((nineI V K).subgroupOf (nineH V K))
      ((nineI V K).subgroupOf (nineH V K)) ψ hmap
  have hsecond : ∀ h h' : ↥(nineH V K), (h' : G) = k * h * k⁻¹ →
      φ (QuotientGroup.mk h) = QuotientGroup.mk h' := by
    intro h h' hh
    rw [QuotientGroup.map_mk]
    congr 1
    ext
    exact hh.symm
  refine ⟨φ, ?_, hsecond, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hx
    rw [QuotientGroup.eq_one_iff]
    exact (hpre h).mp hx
  · rintro d ⟨U, hU, u, huU, huR, rfl⟩
    refine ⟨conjSubgroup U k⁻¹, conjSubgroup_mem_omegaIn hU (K.inv_mem hk), ψ u, ?_, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      change k⁻¹ * (k * (u : G) * k⁻¹) * (k⁻¹)⁻¹ ∈ U
      rw [show k⁻¹ * (k * (u : G) * k⁻¹) * (k⁻¹)⁻¹ = (u : G) by group]
      exact huU
    · intro hR
      exact huR ((Nine3Core.mem_pCoreOf_conj_iff K hk).mpr hR)
    · exact (hsecond u (ψ u) rfl).symm

theorem nine3_comm_Ig_B (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) : ⁅conjSubgroup (nineI V K) g, B⁆ ≤ nineI V K := by
  by_cases hBA : B = A
  · rw [hBA, hc.nine_twelve_Ig_A]
    exact bot_le
  · have hBΔ : B ∈ nineDelta V S := hc.core.mem_nineDelta_iff.mpr (Or.inr hB)
    have hBinvΔ : conjSubgroup B g⁻¹ ∈ nineDelta V S := hc.conj_inv_mem_nineDelta hBΔ
    have hBinvV : conjSubgroup B g⁻¹ ≠ V := by
      intro e
      apply hBA
      have h1 := congrArg (fun C => conjSubgroup C g) e
      rw [E3.conjSubgroup_inv_conj, hc.V_g] at h1
      exact h1
    have hBinvΩ : conjSubgroup B g⁻¹ ∈ nineOmegaIn V K S :=
      (hc.core.mem_nineDelta_iff.mp hBinvΔ).resolve_left hBinvV
    have hcomm := E3.conjSubgroup_commutator (nineI V K) (conjSubgroup B g⁻¹) g
    rw [hI.comm (conjSubgroup B g⁻¹) hBinvΩ, E3.conjSubgroup_inf,
      E3.conjSubgroup_inv_conj, ← hc.inf_pCoreOf_eq_inf_conj hI hB hBA] at hcomm
    rw [← hcomm]
    exact le_iSup₂_of_le B ⟨hB.1, hB.2.trans hc.core.S_le_K⟩ le_rfl

end CFSG.LocalAnalysis.WeakClosure81
