module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvQV
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvAct

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private theorem e6ib_mu1List_subset_qRoots :
    {β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} ⊆ qRoots := by
  intro β hβ
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hβ
  have hi8 : i < 8 := hi
  interval_cases i
  · have hv : β = (![-1, -1, -1, -1, 0, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨37, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, -1, -1, -1, 0, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨30, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, 0, 0, 0, 1, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨4, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, 0, 0, 0, 1, 1] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨15, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, 0, 0, 1, 1, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨13, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, 0, 0, 1, 1, 1] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨25, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, 1, 1, 2, 2, 1] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨58, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![1, 1, 1, 2, 2, 1] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨62, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩

private theorem e6ib_mu2List_subset_qRoots :
    {β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} ⊆ qRoots := by
  intro β hβ
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hβ
  have hi8 : i < 8 := hi
  interval_cases i
  · have hv : β = (![0, -1, 0, -1, -1, -1] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨42, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, -1, 0, -1, -1, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨31, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, 0, 1, 0, 0, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨2, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![0, 0, 1, 1, 0, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨11, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![1, 0, 1, 0, 0, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨7, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![1, 0, 1, 1, 0, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨18, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![1, 1, 2, 2, 1, 0] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨55, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩
  · have hv : β = (![1, 1, 2, 2, 1, 1] : Fin Tag.E6.rank → ℤ) := by
      rw [← hget]; rfl
    rw [hv]
    exact ⟨(RootCertificate.isRoot_iff e6Certificate_check).2
      ⟨61, by decide, by apply RootCertificate.eq_of_ofFn_beq; decide⟩, by decide⟩

private theorem e6ib_uMu1_le_qE :
    uMu1 ≤ qE := by
  intro x hx
  simp only [uMu1, qE, Subgroup.mem_subgroupOf] at hx ⊢
  exact rootSpan_mono e6ib_mu1List_subset_qRoots hx

private theorem e6ib_uMu2_le_qE :
    uMu2 ≤ qE := by
  intro x hx
  simp only [uMu2, qE, Subgroup.mem_subgroupOf] at hx ⊢
  exact rootSpan_mono e6ib_mu2List_subset_qRoots hx

theorem invariant_between_z0E_qE
    (U : Subgroup EC) (h1 : z0E ≤ U) (h2 : U ≤ qE)
    (hN : Subgroup.normalizer (rE : Set EC) ≤ Subgroup.normalizer (U : Set EC)) :
    U = z0E ∨ U = qE ∨ U = z0E ⊔ uMu1 ∨ U = z0E ⊔ uMu2 := by
  obtain ⟨c, hc⟩ := exists_qcoord
  let W : Submodule (ZMod 2) e6TwoRestQV :=
    { carrier := {v | ∃ u : ↥qE, (u : EC) ∈ U ∧ c u = Multiplicative.ofAdd v}
      add_mem' := by
        rintro v w ⟨u, hu, hcu⟩ ⟨u', hu', hcu'⟩
        refine ⟨u * u', ?_, ?_⟩
        · exact U.mul_mem hu hu'
        · rw [map_mul, hcu, hcu', ← ofAdd_add]
      zero_mem' := ⟨1, U.one_mem, by simp⟩
      smul_mem' := by
        rintro a v ⟨u, hu, hcu⟩
        have ha : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
        rcases ha a with rfl | rfl
        · refine ⟨1, U.one_mem, ?_⟩
          simp
        · refine ⟨u, hu, ?_⟩
          rw [one_smul]
          exact hcu }
  have hWinv : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W := by
    rintro k v ⟨u, hu, hcu⟩
    have hg : e6TwoRestInvWord k ∈ Subgroup.normalizer (rE : Set EC) := invWord_mem_normalizer_rE k
    have hmemU : e6TwoRestInvWord k * (u : EC) * (e6TwoRestInvWord k)⁻¹ ∈ U :=
      ((Subgroup.mem_normalizer_iff.mp (hN hg)) (u : EC)).mp hu
    obtain ⟨hq, hcq⟩ := invWord_action hc k u
    refine ⟨⟨e6TwoRestInvWord k * (u : EC) * (e6TwoRestInvWord k)⁻¹, hq⟩, hmemU, ?_⟩
    simpa [hcu] using hcq
  have mem_W_iff : ∀ q : ↥qE, Multiplicative.toAdd (c q) ∈ W ↔ (q : EC) ∈ U := by
    intro q
    constructor
    · rintro ⟨u, hu, hcu⟩
      have hcu' : c u = c q := by rw [hcu]; rfl
      have hker : q * u⁻¹ ∈ c.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcu']
        exact mul_inv_cancel _
      rw [hc.2.1, Subgroup.mem_subgroupOf] at hker
      have hprod : ((q * u⁻¹) * u : ↥qE) = q := by group
      have hU : (((q * u⁻¹) * u : ↥qE) : EC) ∈ U := U.mul_mem (h1 hker) hu
      rwa [hprod] at hU
    · intro hq
      exact ⟨q, hq, (ofAdd_toAdd (c q)).symm⟩
  rcases invariant_submodule_classification W hWinv with hW | hW | hW | hW
  ·
    left
    refine le_antisymm ?_ h1
    intro x hx
    have hxq : x ∈ qE := h2 hx
    let q : ↥qE := ⟨x, hxq⟩
    have hmem : Multiplicative.toAdd (c q) ∈ W := (mem_W_iff q).2 hx
    rw [hW] at hmem
    have hzero : Multiplicative.toAdd (c q) = 0 := by simpa using hmem
    have hone : c q = 1 := by
      have h := congrArg Multiplicative.ofAdd hzero
      rwa [ofAdd_toAdd] at h
    have hker : q ∈ c.ker := MonoidHom.mem_ker.2 hone
    rw [hc.2.1, Subgroup.mem_subgroupOf] at hker
    simpa using hker
  ·
    have hle : z0E ⊔ uMu1 ≤ qE := sup_le z0E_le_qE e6ib_uMu1_le_qE
    right; right; left
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxq : x ∈ qE := h2 hx
      have hmem : Multiplicative.toAdd (c ⟨x, hxq⟩) ∈ W := (mem_W_iff ⟨x, hxq⟩).2 hx
      rw [hW] at hmem
      have := (qcoord_mem_U1_iff hc ⟨x, hxq⟩).1 hmem
      simpa using this
    · intro x hx
      have hxq : x ∈ qE := hle hx
      have hmem : Multiplicative.toAdd (c ⟨x, hxq⟩) ∈ W := by
        rw [hW]
        exact (qcoord_mem_U1_iff hc ⟨x, hxq⟩).2 hx
      exact (mem_W_iff ⟨x, hxq⟩).1 hmem
  ·
    have hle : z0E ⊔ uMu2 ≤ qE := sup_le z0E_le_qE e6ib_uMu2_le_qE
    right; right; right
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxq : x ∈ qE := h2 hx
      have hmem : Multiplicative.toAdd (c ⟨x, hxq⟩) ∈ W := (mem_W_iff ⟨x, hxq⟩).2 hx
      rw [hW] at hmem
      have := (qcoord_mem_U2_iff hc ⟨x, hxq⟩).1 hmem
      simpa using this
    · intro x hx
      have hxq : x ∈ qE := hle hx
      have hmem : Multiplicative.toAdd (c ⟨x, hxq⟩) ∈ W := by
        rw [hW]
        exact (qcoord_mem_U2_iff hc ⟨x, hxq⟩).2 hx
      exact (mem_W_iff ⟨x, hxq⟩).1 hmem
  ·
    right; left
    refine le_antisymm h2 ?_
    intro x hx
    have hmem : Multiplicative.toAdd (c ⟨x, hx⟩) ∈ W := by
      rw [hW]
      exact Submodule.mem_top
    exact (mem_W_iff ⟨x, hx⟩).1 hmem

end CFSG.StandardType.GGSixE6Two
