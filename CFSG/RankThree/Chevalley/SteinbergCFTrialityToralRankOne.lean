module

public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def graphFixedRootPair (O : Set (Fin t.tag.rank → ℤ)) : Subgroup (ModGL t.tag K) :=
  (rootSpan t.tag K O ⊓ twistedFixedGroup t K σ) ⊔
    (rootSpan t.tag K (-O) ⊓ twistedFixedGroup t K σ)

variable {K} in
@[expose] def fixedOrbitImage (v : WeylGroup t.tag) (b : Fin t.foldedTag.rank) :
    Set (Fin t.tag.rank → ℤ) :=
  (fun i => v • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit b)

@[expose] def orbitConjRankOneHom (v : WeylGroup t.tag) (b : Fin t.foldedTag.rank) :
    SL2 (orbitField t K σ b) →* ModGL t.tag K :=
  (MulAut.conj (canonicalRep (coxeterSystem t.tag) K v)).toMonoidHom.comp
    (orbitRankOneHom t K σ b)

variable {t K σ}

theorem orbitConjRankOneHom_apply (v : WeylGroup t.tag) (b : Fin t.foldedTag.rank)
    (g : SL2 (orbitField t K σ b)) :
    orbitConjRankOneHom t K σ v b g = canonicalRep (coxeterSystem t.tag) K v *
      orbitRankOneHom t K σ b g * (canonicalRep (coxeterSystem t.tag) K v)⁻¹ :=
  rfl

theorem orbitConjRankOneHom_injective {v : WeylGroup t.tag} {b : Fin t.foldedTag.rank}
    (hR : Function.Injective (orbitRankOneHom t K σ b)) :
    Function.Injective (orbitConjRankOneHom t K σ v b) :=
  (MulAut.conj (canonicalRep (coxeterSystem t.tag) K v)).injective.comp hR

theorem image_smul_neg_orbit (v : WeylGroup t.tag) (b : Fin t.foldedTag.rank) :
    (fun α => v • α) '' ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit b)) =
      -fixedOrbitImage t v b := by
  ext β
  simp only [Set.mem_image, Finset.mem_coe, Set.mem_neg, fixedOrbitImage]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, by rw [smul_neg, neg_neg]⟩
  · rintro ⟨i, hi, hiβ⟩
    exact ⟨_, ⟨i, hi, rfl⟩, by rw [smul_neg, hiβ, neg_neg]⟩

theorem map_conj_rootSpan_neg_orbit (v : WeylGroup t.tag) (b : Fin t.foldedTag.rank) :
    (rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit b))).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K v)).toMonoidHom =
      rootSpan t.tag K (-fixedOrbitImage t v b) := by
  rw [(canonical_weyl_root_transport t.tag K).1 v _ (by
    rintro _ ⟨i, -, rfl⟩
    exact IsRoot.neg (isRoot_single t.tag i)), image_smul_neg_orbit]

theorem range_orbitConjRankOneHom {v : WeylGroup t.tag} (hv : v ∈ relWeylTwist t)
    (b : Fin t.foldedTag.rank) :
    (orbitConjRankOneHom t K σ v b).range = graphFixedRootPair t K σ (fixedOrbitImage t v b) := by
  obtain ⟨hpar1, -, hpar3, -, -⟩ := fixed_root_orbit_parametrization t K σ
  obtain ⟨e₁, he₁⟩ := hpar1 b v hv
  obtain ⟨e₃, he₃⟩ := hpar3 b
  have hnΓ : canonicalRep (coxeterSystem t.tag) K v ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hv)
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [orbitConjRankOneHom, MonoidHom.range_comp, orbitRankOneHom_range, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨x, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
    · refine Subgroup.mem_sup_left ?_
      have h := (e₁ (Multiplicative.ofAdd c)).2
      rw [he₁ c] at h
      exact h
    · refine Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      · have hy := (Subgroup.mem_inf.1 (e₃ (Multiplicative.ofAdd c)).2).1
        rw [he₃ c] at hy
        rw [← map_conj_rootSpan_neg_orbit]
        exact ⟨_, hy, rfl⟩
      · have hy := (Subgroup.mem_inf.1 (e₃ (Multiplicative.ofAdd c)).2).2
        rw [he₃ c] at hy
        exact mul_mem (mul_mem hnΓ hy) (inv_mem hnΓ)
  · intro x hx
    obtain ⟨m, hm⟩ := e₁.surjective ⟨x, hx⟩
    refine ⟨uSL (Multiplicative.toAdd m), ?_⟩
    rw [orbitConjRankOneHom_apply, orbitRankOneHom_uSL, ← he₁, ofAdd_toAdd, hm]
  · intro x hx
    obtain ⟨hxS, hxΓ⟩ := Subgroup.mem_inf.1 hx
    rw [← map_conj_rootSpan_neg_orbit] at hxS
    obtain ⟨y, hyS, rfl⟩ := hxS
    have hyΓ : y ∈ twistedFixedGroup t K σ := by
      have e : y = (canonicalRep (coxeterSystem t.tag) K v)⁻¹ *
          ((MulAut.conj (canonicalRep (coxeterSystem t.tag) K v)).toMonoidHom y) *
            canonicalRep (coxeterSystem t.tag) K v := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact mul_mem (mul_mem (inv_mem hnΓ) hxΓ) hnΓ
    obtain ⟨m, hm⟩ := e₃.surjective ⟨y, Subgroup.mem_inf.2 ⟨hyS, hyΓ⟩⟩
    refine ⟨vSL (Multiplicative.toAdd m), ?_⟩
    rw [orbitConjRankOneHom_apply, orbitRankOneHom_vSL, ← he₃, ofAdd_toAdd, hm]
    rfl

theorem exists_eq_orbitConjRankOneHom_uSL {v : WeylGroup t.tag} (hv : v ∈ relWeylTwist t)
    {b : Fin t.foldedTag.rank} {x : ModGL t.tag K}
    (hx : x ∈ rootSpan t.tag K (fixedOrbitImage t v b) ⊓ twistedFixedGroup t K σ) :
    ∃ c, x = orbitConjRankOneHom t K σ v b (uSL c) := by
  obtain ⟨hpar1, -⟩ := fixed_root_orbit_parametrization t K σ
  obtain ⟨e₁, he₁⟩ := hpar1 b v hv
  obtain ⟨m, hm⟩ := e₁.surjective ⟨x, hx⟩
  refine ⟨Multiplicative.toAdd m, ?_⟩
  rw [orbitConjRankOneHom_apply, orbitRankOneHom_uSL, ← he₁, ofAdd_toAdd, hm]

theorem exists_eq_orbitConjRankOneHom_vSL {v : WeylGroup t.tag} (hv : v ∈ relWeylTwist t)
    {b : Fin t.foldedTag.rank} {x : ModGL t.tag K}
    (hx : x ∈ rootSpan t.tag K (-fixedOrbitImage t v b) ⊓ twistedFixedGroup t K σ) :
    ∃ c, x = orbitConjRankOneHom t K σ v b (vSL c) := by
  have hx' : x ∈ (orbitConjRankOneHom t K σ v b).range := by
    rw [range_orbitConjRankOneHom hv]
    exact Subgroup.mem_sup_right hx
  obtain ⟨-, -, hpar3, -, -⟩ := fixed_root_orbit_parametrization t K σ
  obtain ⟨e₃, he₃⟩ := hpar3 b
  have hnΓ : canonicalRep (coxeterSystem t.tag) K v ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hv)
  obtain ⟨hxS, hxΓ⟩ := Subgroup.mem_inf.1 hx
  rw [← map_conj_rootSpan_neg_orbit] at hxS
  obtain ⟨y, hyS, rfl⟩ := hxS
  have hyΓ : y ∈ twistedFixedGroup t K σ := by
    have e : y = (canonicalRep (coxeterSystem t.tag) K v)⁻¹ *
        ((MulAut.conj (canonicalRep (coxeterSystem t.tag) K v)).toMonoidHom y) *
          canonicalRep (coxeterSystem t.tag) K v := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact mul_mem (mul_mem (inv_mem hnΓ) hxΓ) hnΓ
  obtain ⟨m, hm⟩ := e₃.surjective ⟨y, Subgroup.mem_inf.2 ⟨hyS, hyΓ⟩⟩
  refine ⟨Multiplicative.toAdd m, ?_⟩
  rw [orbitConjRankOneHom_apply, orbitRankOneHom_vSL, ← he₃, ofAdd_toAdd, hm]
  rfl

theorem graphFixedRootTorus_le_graphFixedRootMonomial :
    graphFixedRootTorus t K σ ≤ graphFixedRootMonomial t K σ :=
  inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial t K σ)

theorem orbitConjRankOneHom_HSL_mem {v : WeylGroup t.tag} (hv : v ∈ relWeylTwist t)
    (b : Fin t.foldedTag.rank) (u : (orbitField t K σ b)ˣ) :
    orbitConjRankOneHom t K σ v b (HSL u) ∈ graphFixedRootTorus t K σ := by
  obtain ⟨-, -, -, -, h5⟩ := fixed_root_orbit_parametrization t K σ
  have hC := (h5 b u).2
  have hH : (orbitH t K σ b u : ModGL t.tag K) ∈ graphFixedRootTorus t K σ :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨orbitH_mem_torusGroup b u,
      graphFixedRootGroup_le t K σ hC⟩, hC⟩
  have hn := canonicalRep_mem_graphFixedRootMonomial t K σ hv
  have h := (graphFixedRootTorus_subgroupOf_normal t K σ).conj_mem
    ⟨_, graphFixedRootTorus_le_graphFixedRootMonomial hH⟩ (Subgroup.mem_subgroupOf.2 hH) ⟨_, hn⟩
  rw [Subgroup.mem_subgroupOf] at h
  rw [orbitConjRankOneHom_apply, orbitRankOneHom_HSL]
  simpa using h

theorem exists_canonicalRep_eq_mul_orbitConjRankOneHom {v : WeylGroup t.tag}
    (hv : v ∈ relWeylTwist t) (b : Fin t.foldedTag.rank) :
    ∃ h ∈ graphFixedRootTorus t K σ,
      canonicalRep (coxeterSystem t.tag) K (v * t.orbitReflection b * v⁻¹) =
        h * orbitConjRankOneHom t K σ v b WSL := by
  have hr := t.orbitReflection_mem b
  have hw : v * t.orbitReflection b * v⁻¹ ∈ relWeylTwist t :=
    mul_mem (mul_mem hv hr) (inv_mem hv)
  have hnv := canonicalRep_mem_graphFixedRootMonomial t K σ hv
  have hnr := canonicalRep_mem_graphFixedRootMonomial t K σ hr
  have hnw := canonicalRep_mem_graphFixedRootMonomial t K σ hw
  have hm : orbitConjRankOneHom t K σ v b WSL = canonicalRep (coxeterSystem t.tag) K v *
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) *
        (canonicalRep (coxeterSystem t.tag) K v)⁻¹ := by
    rw [orbitConjRankOneHom_apply, orbitRankOneHom_WSL,
      ← canonicalRep_orbitReflection_eq_orbitN t σ b]
  have hmN : orbitConjRankOneHom t K σ v b WSL ∈ graphFixedRootMonomial t K σ := by
    rw [hm]
    exact mul_mem (mul_mem hnv hnr) (inv_mem hnv)
  have him : graphFixedRootWeylHom t K σ ⟨_, hmN⟩ = v * t.orbitReflection b * v⁻¹ := by
    have e : (⟨_, hmN⟩ : graphFixedRootMonomial t K σ) = ⟨_, hnv⟩ * ⟨_, hnr⟩ * (⟨_, hnv⟩)⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; exact hm)
    rw [e, map_mul, map_mul, map_inv, graphFixedRootWeylHom_canonicalRep t K σ hv,
      graphFixedRootWeylHom_canonicalRep t K σ hr]
  have hker : (⟨_, hnw⟩ : graphFixedRootMonomial t K σ) * (⟨_, hmN⟩)⁻¹ ∈
      (graphFixedRootWeylHom t K σ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, graphFixedRootWeylHom_canonicalRep t K σ hw, him,
      mul_inv_cancel]
  rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at hker
  exact ⟨_, hker, by simp⟩

theorem orbitRankOneHom_mem_graphFixedRootGroup (b : Fin t.foldedTag.rank)
    (g : SL2 (orbitField t K σ b)) : orbitRankOneHom t K σ b g ∈ graphFixedRootGroup t K σ := by
  have hle : (orbitRankOneHom t K σ b).range ≤ graphFixedRootGroup t K σ := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ b c)
    · exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (orbitY_mem_graphFixedNegUnipotent _ _ b c)
  exact hle ⟨g, rfl⟩

theorem orbitConjRankOneHom_mem_graphFixedRootGroup {v : WeylGroup t.tag}
    (hv : v ∈ relWeylTwist t) (b : Fin t.foldedTag.rank) (g : SL2 (orbitField t K σ b)) :
    orbitConjRankOneHom t K σ v b g ∈ graphFixedRootGroup t K σ := by
  have hn := canonicalRep_mem_graphFixedRootGroup (K := K) (σ := σ) hv
  rw [orbitConjRankOneHom_apply]
  exact mul_mem (mul_mem hn (orbitRankOneHom_mem_graphFixedRootGroup b g)) (inv_mem hn)

theorem orbitConjRankOneHom_uSL_mem {v : WeylGroup t.tag} (hv : v ∈ relWeylTwist t)
    (b : Fin t.foldedTag.rank) (c : orbitField t K σ b) :
    orbitConjRankOneHom t K σ v b (uSL c) ∈
      rootSpan t.tag K (fixedOrbitImage t v b) ⊓ twistedFixedGroup t K σ := by
  obtain ⟨hpar1, -⟩ := fixed_root_orbit_parametrization t K σ
  obtain ⟨e₁, he₁⟩ := hpar1 b v hv
  have h := (e₁ (Multiplicative.ofAdd c)).2
  rw [he₁ c] at h
  rw [orbitConjRankOneHom_apply, orbitRankOneHom_uSL]
  exact h

theorem orbitConjRankOneHom_vSL_mem {v : WeylGroup t.tag} (hv : v ∈ relWeylTwist t)
    (b : Fin t.foldedTag.rank) (c : orbitField t K σ b) :
    orbitConjRankOneHom t K σ v b (vSL c) ∈
      rootSpan t.tag K (-fixedOrbitImage t v b) ⊓ twistedFixedGroup t K σ := by
  obtain ⟨-, -, hpar3, -, -⟩ := fixed_root_orbit_parametrization t K σ
  obtain ⟨e₃, he₃⟩ := hpar3 b
  have hnΓ : canonicalRep (coxeterSystem t.tag) K v ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hv)
  have hy := (e₃ (Multiplicative.ofAdd c)).2
  rw [he₃ c] at hy
  obtain ⟨hyS, hyΓ⟩ := Subgroup.mem_inf.1 hy
  rw [orbitConjRankOneHom_apply, orbitRankOneHom_vSL]
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hnΓ hyΓ) (inv_mem hnΓ)⟩
  rw [← map_conj_rootSpan_neg_orbit]
  exact ⟨_, hyS, rfl⟩

end CFSG.RankThree.Chevalley
