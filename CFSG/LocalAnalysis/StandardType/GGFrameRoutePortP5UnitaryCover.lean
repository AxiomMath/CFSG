module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryFix
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.Assembly

open scoped commutatorElement

variable {K : Type} [Field K] {d q : ℕ}

private lemma ker_le_scalars_subgroupOf_of_cover {L : Type*} [Group L]
    {φ : ↥(LargeEvenSUGroup (Fin d) K q) →* L}
    (hker : ∀ g, φ g = 1 → ∃ c : K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal fun _ => c)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K q)) = ⊥) :
    ((QuotientGroup.mk' (Subgroup.center L)).comp φ).ker ≤
      (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K q) := by
  intro s hs
  have hcent : φ s ∈ Subgroup.center L := by
    have hq : (QuotientGroup.mk (φ s) : L ⧸ Subgroup.center L) = 1 := by
      simpa only [MonoidHom.coe_comp, Function.comp_apply,
        QuotientGroup.mk'_apply] using MonoidHom.mem_ker.mp hs
    exact (QuotientGroup.eq_one_iff (φ s)).mp hq
  have hcomm : ∀ g : ↥(LargeEvenSUGroup (Fin d) K q), ⁅s, g⁆ ∈
      (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K q) := by
    intro g
    have hφc : φ ⁅s, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hcent (φ g)).symm
    obtain ⟨c, hc⟩ := hker ⁅s, g⁆ hφc
    rw [Subgroup.mem_subgroupOf, largeEvenScalars_def,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      ⟨c, by rw [Matrix.scalar_apply]; exact hc.symm⟩
  have hcentral : ∀ g : ↥(LargeEvenSUGroup (Fin d) K q),
      (QuotientGroup.mk s : LargeEvenProj (LargeEvenSUGroup (Fin d) K q)) *
        QuotientGroup.mk g = QuotientGroup.mk g * QuotientGroup.mk s := by
    intro g
    have h1 : QuotientGroup.mk (⁅s, g⁆ : ↥(LargeEvenSUGroup (Fin d) K q)) =
        (1 : LargeEvenProj (LargeEvenSUGroup (Fin d) K q)) :=
      (QuotientGroup.eq_one_iff (⁅s, g⁆ : ↥(LargeEvenSUGroup (Fin d) K q))).mpr (hcomm g)
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    refine mul_inv_eq_one.mp ?_
    rw [mul_inv_rev]
    simpa only [mul_assoc] using h1
  have hmem : (QuotientGroup.mk s : LargeEvenProj (LargeEvenSUGroup (Fin d) K q)) ∈
      Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K q)) := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K q)) r
    rw [← hg, QuotientGroup.mk'_apply]
    exact (hcentral g).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff s).mp hmem

private lemma scalars_subgroupOf_le_ker_of_cover {L : Type*} [Group L]
    {φ : ↥(LargeEvenSUGroup (Fin d) K q) →* L} (hφ : Function.Surjective φ) :
    (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K q) ≤
      ((QuotientGroup.mk' (Subgroup.center L)).comp φ).ker := by
  intro s hs
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk (φ s) : L ⧸ Subgroup.center L) = 1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro l
  obtain ⟨g, rfl⟩ := hφ l
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.mp
    (TableB.scalars_le_center (Subgroup.mem_subgroupOf.mp hs)) (g : GL (Fin d) K))

theorem exists_centerQuotEquiv_of_cover {L : Type*} [Group L]
    {φ : ↥(LargeEvenSUGroup (Fin d) K q) →* L} (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → ∃ c : K,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.diagonal fun _ => c)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K q)) = ⊥) :
    ∃ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K q),
      ∀ s, θ (QuotientGroup.mk (φ s)) = LargeEvenProjMk _ s := by
  let SU := LargeEvenSUGroup (Fin d) K q
  let N := (LargeEvenScalars (Fin d) K).subgroupOf SU
  let f : ↥SU →* L ⧸ Subgroup.center L := (QuotientGroup.mk' (Subgroup.center L)).comp φ
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hφ
  have hker_eq : f.ker = N := by
    apply le_antisymm
    · simpa only [f, N, SU] using ker_le_scalars_subgroupOf_of_cover hker hZ
    · simpa only [f, N, SU] using scalars_subgroupOf_le_ker_of_cover hφ
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker_eq), ?_⟩
  intro s
  rw [MulEquiv.trans_apply]
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf) (QuotientGroup.mk s) = f s := by
    change QuotientGroup.kerLift f (QuotientGroup.mk s) = f s
    exact QuotientGroup.kerLift_mk (φ := f) s
  change (QuotientGroup.quotientMulEquivOfEq hker_eq)
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f s)) =
    LargeEvenProjMk (LargeEvenSUGroup (Fin d) K q) s
  rw [← h1, MulEquiv.symm_apply_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private lemma diagGL_mem_normalizer_largeEvenSUGroup {e : Fin d → Kˣ}
    (he : ∀ i, e i ^ (q + 1) = 1) :
    TauCeti.diagGL e ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) K q : Set (GL (Fin d) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact diagGL_mul_mul_inv_mem_largeEvenSUGroup he hg
  · intro hg
    have he' : ∀ i, (e⁻¹ : Fin d → Kˣ) i ^ (q + 1) = 1 := fun i => by
      rw [Pi.inv_apply, inv_pow, he i, inv_one]
    have hDinv : TauCeti.diagGL (e⁻¹ : Fin d → Kˣ) = (TauCeti.diagGL e)⁻¹ :=
      map_inv (TauCeti.diagGL) e
    have h := diagGL_mul_mul_inv_mem_largeEvenSUGroup he' hg
    rw [hDinv] at h
    have hg' : (TauCeti.diagGL e)⁻¹ * (TauCeti.diagGL e * g * (TauCeti.diagGL e)⁻¹) *
        ((TauCeti.diagGL e)⁻¹)⁻¹ = g := by group
    rwa [hg'] at h

theorem exists_mulAut_of_diagConj {G : Type} [Group G] {L : Subgroup G}
    {φ : ↥(LargeEvenSUGroup (Fin d) K q) →* ↥L} (hφ : Function.Surjective φ)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K q)}
    (hθ : ∀ s, θ (QuotientGroup.mk (φ s)) = LargeEvenProjMk _ s)
    {e : Fin d → Kˣ} (he : ∀ i, e i ^ (q + 1) = 1) {b : G}
    (hb : ∀ s s' : ↥(LargeEvenSUGroup (Fin d) K q),
      (s' : GL (Fin d) K) = TauCeti.diagGL e * s * (TauCeti.diagGL e)⁻¹ →
        ((φ s' : ↥L) : G) = b⁻¹ * φ s * b) :
    ∃ ψ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K q)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ ∧
        LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K q))
          (fun h h' => (h' : GL (Fin d) K) =
            TauCeti.diagGL e * (h : GL (Fin d) K) * (TauCeti.diagGL e)⁻¹) ψ := by
  let SU := LargeEvenSUGroup (Fin d) K q
  let D : GL (Fin d) K := TauCeti.diagGL e
  have hD : D ∈ Subgroup.normalizer (SU : Set (GL (Fin d) K)) := by
    simpa only [D, SU] using diagGL_mem_normalizer_largeEvenSUGroup (q := q) he
  let ψ : MulAut (LargeEvenProj SU) := TableB.projConj SU ⟨D, hD⟩
  have hgraph : LargeEvenGraphAut (LargeEvenProjMk SU)
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL e * (h : GL (Fin d) K) * (TauCeti.diagGL e)⁻¹) ψ := by
    intro h h' hrel
    have hψ : ψ (LargeEvenProjMk SU h) =
        ((SU.normalizerMonoidHom ⟨D, hD⟩ h : SU) : LargeEvenProj SU) :=
      TableB.projConj_mk SU ⟨D, hD⟩ h
    rw [hψ]
    have hconj : ((SU.normalizerMonoidHom ⟨D, hD⟩ h : SU) : GL (Fin d) K) =
        D * (h : GL (Fin d) K) * D⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe SU ⟨D, hD⟩ h
    exact congrArg (fun x : SU => (x : LargeEvenProj SU))
      (Subtype.ext (by rw [hconj]; exact hrel.symm))
  refine ⟨ψ, ?_, hgraph⟩
  intro l l' hl
  obtain ⟨s, rfl⟩ := hφ l
  let s' : ↥SU := ⟨D * s * D⁻¹, by
    simpa only [D] using diagGL_mul_mul_inv_mem_largeEvenSUGroup he s.2⟩
  have hrel : (s' : GL (Fin d) K) =
      TauCeti.diagGL e * (s : GL (Fin d) K) * (TauCeti.diagGL e)⁻¹ := rfl
  have hs' : ((φ s' : ↥L) : G) = b⁻¹ * φ s * b := hb s s' hrel
  have hl' : φ s' = l' := Subtype.ext (by rw [hs', hl])
  rw [← hl', hθ s, hθ s']
  exact hgraph s s' hrel

end CFSG.StandardType.FrameRoute.UnitaryModel
