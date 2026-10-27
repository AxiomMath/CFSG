module

public import CFSG.RankThree.PartOne.KE.SigmaTransport
public import CFSG.RankThree.PartOne.KE.SigmaUnion

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open scoped Pointwise

variable {τ : Tag} {L : Type} [Field L]

theorem SigmaFactor.transport (Fr : L →+* L) (hFr : Function.Bijective Fr) (v : WeylGroup τ)
    (n : ModGL τ L) {S' : Set (Fin τ.rank → ℤ)} (hS' : ∀ r ∈ S', IsRoot τ r) {ι' : Type}
    {P' : ι' → Subgroup (ModGL τ L)} {N' : Subgroup (ModGL τ L)}
    (h : SigmaFactor ((canonicalRep (coxeterSystem τ) L v)⁻¹ * n *
      canonicalRep (coxeterSystem τ) L v) Fr S' P' N') :
    SigmaFactor n Fr ((fun γ => v • γ) '' S')
      (fun i => (P' i).map (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom)
      (N'.map (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom) := by
  classical
  set V : ModGL τ L := canonicalRep (coxeterSystem τ) L v with hV
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set c : ModGL τ L →* ModGL τ L := (MulAut.conj V).toMonoidHom with hc
  have hcapp : ∀ x, c x = V * x * V⁻¹ := fun x => by simp [hc, MulAut.conj_apply]
  have hcinj : Function.Injective c := (MulAut.conj V).injective
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFr) v
    have h2 : (RingEquiv.ofBijective Fr hFr).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  have hVadj : V ∈ adjointGroup τ L := canonicalRep_mem_adjointGroup _ L v
  have hVN : V ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    canonicalRep_mem_normalizer v
  have hcH : ∀ x, c x ∈ torusGroup τ L ↔ x ∈ torusGroup τ L := fun x => by
    rw [hcapp]
    exact (Subgroup.mem_normalizer_iff.1 hVN x).symm
  have hHmap : (torusGroup τ L).map c = torusGroup τ L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hcH x).2 hx
    · intro hy
      have hmem : V⁻¹ * y * V ∈ torusGroup τ L := by
        refine (hcH _).1 ?_
        rw [hcapp]
        have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      refine ⟨V⁻¹ * y * V, hmem, ?_⟩
      rw [hcapp]
      group
  have hQmap : (rootSpan τ L S').map c = rootSpan τ L ((fun γ => v • γ) '' S') :=
    map_conj_rootSpan v hS'
  have hsup : (torusGroup τ L ⊔ rootSpan τ L S').map c =
      torusGroup τ L ⊔ rootSpan τ L ((fun γ => v • γ) '' S') := by
    rw [Subgroup.map_sup, hHmap, hQmap]
  have hRiff : ∀ x, x ∈ twistedFixedPoints (V⁻¹ * n * V) Φ ↔ c x ∈ twistedFixedPoints n Φ :=
    fun x => by rw [hcapp]; exact mem_twistedFixedPoints_conj hΦV
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i y hy hyR u hu => ?_, ?_⟩
  · have := h.finite i
    exact Finite.of_equiv (P' i) (Subgroup.equivMapOfInjective (P' i) c hcinj).toEquiv
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective (P' i) c hcinj) (h.quasi i)
  · rw [← hQmap]
    exact Subgroup.map_mono (h.le_root i)
  · rintro _ ⟨x, hx, rfl⟩
    exact (hRiff x).1 (h.le_fix i hx)
  · rintro _ ⟨x, hx, rfl⟩
    rw [hcapp]
    exact mul_mem (mul_mem hVadj (h.le_adj i hx)) (inv_mem hVadj)
  · obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨u', hu', rfl⟩ := hu
    refine ⟨y' * u' * y'⁻¹, h.norm i y' hy' ((hRiff y').2 hyR) u' hu', ?_⟩
    simp only [map_mul, map_inv]
  · intro y hy hcomm
    rw [← hsup] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨hy'T, hy'C⟩ := h.thetaFree y' hy' fun i u' hu' => by
      apply hcinj
      rw [map_mul, map_mul]
      exact hcomm i (c u') ⟨u', hu', rfl⟩
    refine ⟨(hcH y').2 hy'T, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [← hQmap] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hy'C g' hg']

end CFSG.RankThree.PartOne.KE
