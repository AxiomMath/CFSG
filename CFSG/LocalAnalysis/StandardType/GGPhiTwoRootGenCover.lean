module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenLang

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem canonicalRep_inv_conj_mem_torus_sup_rootSpan
    {τ : Tag} {L : Type} [Field L] (v : WeylGroup τ) {S S' : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot τ γ ∧ v⁻¹ • γ ∈ S') {g : ModGL τ L}
    (hg : g ∈ torusGroup τ L ⊔ rootSpan τ L S) :
    (canonicalRep (coxeterSystem τ) L v)⁻¹ * g * canonicalRep (coxeterSystem τ) L v ∈
      torusGroup τ L ⊔ rootSpan τ L S' := by
  classical
  have hle : (torusGroup τ L ⊔ rootSpan τ L S).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) L v)⁻¹).toMonoidHom ≤
        torusGroup τ L ⊔ rootSpan τ L S' := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (inv_mem (canonicalRep_mem_normalizer v)) t).1 ht
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨k, hk, hkn⟩ := canonicalRep_inv_eq (K := L) v
      have hSroots : ∀ α ∈ S, IsRoot τ α := fun α hα => (hS α hα).1
      have htransport : canonicalRep (coxeterSystem τ) L v⁻¹ * g *
          (canonicalRep (coxeterSystem τ) L v⁻¹)⁻¹ ∈
          rootSpan τ L ((fun α => v⁻¹ • α) '' S) := by
        have hmap := (canonical_weyl_root_transport τ L).1 v⁻¹ S hSroots
        rw [← hmap]
        exact Subgroup.mem_map_of_mem _ hg
      have hle' : rootSpan τ L ((fun α => v⁻¹ • α) '' S) ≤ rootSpan τ L S' :=
        rootSpan_mono (fun α hα => by
          obtain ⟨β, hβ, rfl⟩ := hα
          exact (hS β hβ).2)
      have hTroots : ∀ α ∈ (fun α => v⁻¹ • α) '' S, IsRoot τ α := by
        rintro _ ⟨β, hβ, rfl⟩
        exact IsRoot.smul (hS β hβ).1 v⁻¹
      have hnorm : k * (canonicalRep (coxeterSystem τ) L v⁻¹ * g *
          (canonicalRep (coxeterSystem τ) L v⁻¹)⁻¹) * k⁻¹ ∈
          rootSpan τ L ((fun α => v⁻¹ • α) '' S) :=
        (Subgroup.mem_normalizer_iff.1
          (torusGroup_le_normalizer_rootSpan (S := (fun α => v⁻¹ • α) '' S) hTroots hk)
          (canonicalRep (coxeterSystem τ) L v⁻¹ * g *
            (canonicalRep (coxeterSystem τ) L v⁻¹)⁻¹)).1 htransport
      have hnorm' : k * (canonicalRep (coxeterSystem τ) L v⁻¹ * g *
          (canonicalRep (coxeterSystem τ) L v⁻¹)⁻¹) * k⁻¹ ∈ rootSpan τ L S' :=
        hle' hnorm
      have hnv : canonicalRep (coxeterSystem τ) L v =
          (k * canonicalRep (coxeterSystem τ) L v⁻¹)⁻¹ := by
        rw [← hkn, inv_inv]
      have heq : (canonicalRep (coxeterSystem τ) L v)⁻¹ * g *
          canonicalRep (coxeterSystem τ) L v =
          k * (canonicalRep (coxeterSystem τ) L v⁻¹ * g *
            (canonicalRep (coxeterSystem τ) L v⁻¹)⁻¹) * k⁻¹ := by
        rw [hkn, hnv]
        group
      change (canonicalRep (coxeterSystem τ) L v)⁻¹ * g *
        canonicalRep (coxeterSystem τ) L v ∈ rootSpan τ L S'
      rw [heq]
      exact hnorm'
  exact hle ⟨g, hg, rfl⟩

theorem mem_iSup_phiTwoComp_of_mem_rootSpan_of_step
    {τ : Tag} {K : Type} [Field K] [CharP K 2]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {w : WeylGroup τ}
    (hw : ∀ v : WeylGroup τ, v * w = w * v) {Φ₁ : Set (Fin τ.rank → ℤ)}
    (hstep : ∀ g ∈ adjointGroup τ (AlgebraicClosure K),
      Units.map (entrywiseHom Fr) g = g * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w →
      ∀ x : adjointGroup τ K,
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g ∈
          torusGroup τ (AlgebraicClosure K) ⊔ rootSpan τ (AlgebraicClosure K) Φ₁ →
        x ∈ ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g γ.1)
    {Φ₀ : Set (Fin τ.rank → ℤ)} {z : ModGL τ (AlgebraicClosure K)}
    (hz : z ∈ torusGroup τ (AlgebraicClosure K) ⊔ rootSpan τ (AlgebraicClosure K) Φ₀)
    (hzFr : Units.map (entrywiseHom Fr) z =
      z * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {v : WeylGroup τ} {S : Set (Fin τ.rank → ℤ)} (hΦS : Φ₀ ⊆ S)
    (hS : ∀ γ ∈ S, IsRoot τ γ ∧ v⁻¹ • γ ∈ Φ₁)
    {x : adjointGroup τ K} (hx : (x : ModGL τ K) ∈ rootSpan τ K S) :
    x ∈ ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp z γ.1 := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hzC : z ∈ adjointGroup τ (AlgebraicClosure K) :=
    CFSG.LieType.AlgebraicGroups.torus_sup_rootSpan_le_adjointGroup (S := Φ₀) hz
  have hznC : z * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v ∈
      adjointGroup τ (AlgebraicClosure K) :=
    mul_mem hzC (canonicalRep_mem_adjointGroup (coxeterSystem τ) (AlgebraicClosure K) v)
  have hzS : z ∈ torusGroup τ (AlgebraicClosure K) ⊔ rootSpan τ (AlgebraicClosure K) S :=
    (sup_le le_sup_left ((rootSpan_mono hΦS).trans le_sup_right)) hz
  have hxL : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) ∈
      rootSpan τ (AlgebraicClosure K) S :=
    CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan (algebraMap K (AlgebraicClosure K)) hx
  have hy : z⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * z ∈
      torusGroup τ (AlgebraicClosure K) ⊔ rootSpan τ (AlgebraicClosure K) S :=
    mul_mem (mul_mem (inv_mem hzS) (Subgroup.mem_sup_right hxL)) hzS
  have hx' : (z * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
        (z * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v) ∈
      torusGroup τ (AlgebraicClosure K) ⊔ rootSpan τ (AlgebraicClosure K) Φ₁ := by
    have heq : (z * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          (z * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v) =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ *
          (z⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * z) *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v := by
      group
    rw [heq]
    exact canonicalRep_inv_conj_mem_torus_sup_rootSpan v hS hy
  have hmem := hstep _ hznC (isLang_mul_canonicalRep (hw v) hzFr) x hx'
  rwa [iSup_phiTwoComp_mul_canonicalRep z v] at hmem

theorem iSup_phiTwoComp_eq_top_of_cover
    {τ : Tag} {K : Type} [Field K] [CharP K 2]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {w : WeylGroup τ}
    (hw : ∀ v : WeylGroup τ, v * w = w * v) {Φ₀ Φ₁ : Set (Fin τ.rank → ℤ)}
    (hstep : ∀ g ∈ adjointGroup τ (AlgebraicClosure K),
      Units.map (entrywiseHom Fr) g = g * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w →
      ∀ x : adjointGroup τ K,
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g ∈
          torusGroup τ (AlgebraicClosure K) ⊔ rootSpan τ (AlgebraicClosure K) Φ₁ →
        x ∈ ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g γ.1)
    (hcover : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∃ (v : WeylGroup τ) (S : Set (Fin τ.rank → ℤ)),
      γ ∈ S ∧ Φ₀ ⊆ S ∧ ∀ δ ∈ S, IsRoot τ δ ∧ v⁻¹ • δ ∈ Φ₁)
    {z : ModGL τ (AlgebraicClosure K)}
    (hz : z ∈ torusGroup τ (AlgebraicClosure K) ⊔ rootSpan τ (AlgebraicClosure K) Φ₀)
    (hzFr : Units.map (entrywiseHom Fr) z =
      z * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) :
    (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp z γ.1) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hxC : (x : ModGL τ K) ∈ rootSpan τ K {α | IsRoot τ α} := by
    rw [← adjointGroup_eq_rootSpan]
    exact x.2
  have hle : rootSpan τ K {α | IsRoot τ α} ≤
      (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp z γ.1).map
        (adjointGroup τ K).subtype := by
    refine iSup₂_le fun α hα => ?_
    intro y hy
    obtain ⟨v, S, hαS, hΦS, hS⟩ := hcover α hα
    exact Subgroup.mem_map_of_mem (adjointGroup τ K).subtype
      (mem_iSup_phiTwoComp_of_mem_rootSpan_of_step (x := ⟨y, rootSubgroup_le_adjointGroup α hy⟩)
        hw hstep hz hzFr hΦS hS (rootSubgroup_le_rootSpan hαS hy))
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle hxC)
  exact (Subtype.ext hyx) ▸ hy

theorem iSup_phiTwoComp_eq_top_of_kernelRoots_cover
    {τ : Tag} {M : Type} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hdesc : ∀ x ∈ adjointGroup τ (AlgebraicClosure K), Units.map (entrywiseHom Fr) x = x →
      x ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} (hw : ∀ v : WeylGroup τ, v * w = w * v)
    (hwχ : w ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots χ))
    {Φ₁ : Set (Fin τ.rank → ℤ)}
    (hstep : ∀ g ∈ adjointGroup τ (AlgebraicClosure K),
      Units.map (entrywiseHom Fr) g = g * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w →
      ∀ x : adjointGroup τ K,
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g ∈
          torusGroup τ (AlgebraicClosure K) ⊔ rootSpan τ (AlgebraicClosure K) Φ₁ →
        x ∈ ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g γ.1)
    (hcover : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∃ (v : WeylGroup τ) (S : Set (Fin τ.rank → ℤ)),
      γ ∈ S ∧ kernelRoots χ ⊆ S ∧ ∀ δ ∈ S, IsRoot τ δ ∧ v⁻¹ • δ ∈ Φ₁)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) :
    (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1) = ⊤ := by
  obtain ⟨h, d, hd, hg0eq⟩ := exists_mul_eq_kernelGroup χ hFr
    (fun X _ hXC hXF _ hy => hdesc _ (hXC hy) (hXF _ hy)) hg0C hg0
    (CFSG.LieType.AlgebraicGroups.canonicalRep_mem_torus_sup_rootSpan_kernelRoots hwχ)
  have hcomp : Fr.comp (algebraMap K (AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, hFr, ← map_pow]
    congr 1
    letI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hdFr : Units.map (entrywiseHom Fr) d =
      d * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
    rw [hg0eq, map_mul, units_map_entrywiseHom_eq_baseChangeGL Fr (baseChangeGL _ _),
      baseChangeGL_baseChangeGL, hcomp, mul_assoc] at hg0
    exact mul_left_cancel hg0
  rw [hg0eq, iSup_phiTwoComp_baseChange_mul h d,
    iSup_phiTwoComp_eq_top_of_cover hw hstep hcover hd hdFr]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective

end CFSG.StandardType.PhiTwoRootGen

end
