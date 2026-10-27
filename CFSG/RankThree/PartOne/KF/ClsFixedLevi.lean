module

public import CFSG.RankThree.PartOne.KF.ClsRankOneLevi

public section

namespace CFSG.RankThree.PartOne.KFU

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.SteinbergCD

section Levi

theorem isCyclic_of_le_graphFixedParabolic_singleton {t : TwistTag} {K : Type} [Field K]
    [Finite K] [CharP K 2] (σ : K ≃+* K) (a : Fin t.foldedTag.rank) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hrT : ¬ r ∣ Nat.card (graphFixedRootTorus t K σ.toRingHom))
    {P : Subgroup (ModGL t.tag K)} (hP : P ≤ graphFixedParabolic t K σ.toRingHom {a})
    (hPr : IsPGroup r P) : IsCyclic P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL t.tag K) := finite_modGL
  set Γ := twistedFixedGroup t K σ.toRingHom
  set E := simpleOrbitRoots t a with hE
  set E' := (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a) with hE'
  have hEroot : ∀ α ∈ E, IsRoot t.tag α := by
    rintro _ ⟨i, -, rfl⟩
    exact isRoot_single _ i
  have hE'root : ∀ α ∈ E', IsRoot t.tag α := by
    rintro _ ⟨i, -, rfl⟩
    exact isRoot_neg_single _ i
  have hX : ∀ c, (orbitX t K σ.toRingHom a c : ModGL t.tag K) ∈ rootSpan t.tag K E ⊓ Γ :=
    orbitX_mem t σ.toRingHom a
  have hY : ∀ c, (orbitY t K σ.toRingHom a c : ModGL t.tag K) ∈ rootSpan t.tag K E' ⊓ Γ :=
    fun c => (mem_rootSpan_negSimpleOrbitRoots_iff a).2 ⟨c, rfl⟩
  have hrange := orbitRankOneHom_range_eq σ.toRingHom a
  have hA_a : ∀ i ∈ t.orbit a, i ∈ t.orbitUnion {a} := fun i hi =>
    (mem_orbitUnion_iff_orbitIndex).2 ((t.mem_orbit_iff).1 hi)
  have hEM : rootSpan t.tag K E ≤ parabolicLevi t.tag K (t.orbitUnion {a}) := by
    refine iSup₂_le fun α hα => ?_
    obtain ⟨i, hi, rfl⟩ := hα
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, pinnedX_single]
    exact mem_sup_right (subset_closure ⟨i, hA_a i hi, c, Or.inl rfl⟩)
  have hE'M : rootSpan t.tag K E' ≤ parabolicLevi t.tag K (t.orbitUnion {a}) := by
    refine iSup₂_le fun α hα => ?_
    obtain ⟨i, hi, rfl⟩ := hα
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, pinnedX_neg_single]
    exact mem_sup_right (subset_closure ⟨i, hA_a i hi, c, Or.inr rfl⟩)
  have hV : graphFixedParabolicLeviUnipotent t K σ.toRingHom {a} ≤
      (orbitRankOneHom t K σ.toRingHom a).range := by
    intro v hv
    obtain ⟨hvS, hvΓ⟩ := mem_inf.1 hv
    rw [hrange]
    exact mem_sup_left ⟨rootSpan_mono (fun α hα => mem_simpleOrbitRoots_of_mem_parabolicPosRoots
      hα) hvS, hvΓ⟩
  have hn : ∀ b ∈ ({a} : Set (Fin t.foldedTag.rank)),
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection b) ∈
        (orbitRankOneHom t K σ.toRingHom a).range := by
    rintro b rfl
    rw [hrange, canonicalRep_orbitReflection_eq_orbitN t σ.toRingHom b, orbitN, coe_mul, coe_mul]
    exact mul_mem (mul_mem (mem_sup_left (hX _)) (mem_sup_right (hY _))) (mem_sup_left (hX _))
  have hRX : (orbitRankOneHom t K σ.toRingHom a).range ≤
      graphFixedParabolic t K σ.toRingHom {a} := by
    rw [hrange]
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨c, rfl⟩ := (mem_rootSpan_simpleOrbitRoots_iff σ.toRingHom a).1 hg
      exact graphFixedRootBorel_le_graphFixedParabolic t K _ _
        (graphFixedPosUnipotent_le_graphFixedRootBorel
          (orbitX_mem_graphFixedPosUnipotent t σ.toRingHom a c))
    · obtain ⟨c, rfl⟩ := (mem_rootSpan_negSimpleOrbitRoots_iff a).1 hg
      exact orbitY_mem_graphFixedParabolic a c
  have hRM : (orbitRankOneHom t K σ.toRingHom a).range ≤
      parabolicLevi t.tag K (t.orbitUnion {a}) ⊓ twistedFixedGroup t K σ.toRingHom := by
    rw [hrange]
    exact sup_le (inf_le_inf_right _ hEM) (inf_le_inf_right _ hE'M)
  have hTR : graphFixedRootTorus t K σ.toRingHom ≤
      normalizer ((orbitRankOneHom t K σ.toRingHom a).range : Set (ModGL t.tag K)) := by
    intro h hh
    obtain ⟨⟨hhH, hhΓ⟩, -⟩ := mem_inf.1 hh
    rw [hrange]
    exact inf_normalizer_le_normalizer_sup _ _
      ⟨inf_normalizer_le_normalizer_inf ⟨torusGroup_le_normalizer_rootSpan hEroot hhH,
          le_normalizer hhΓ⟩,
        inf_normalizer_le_normalizer_inf ⟨torusGroup_le_normalizer_rootSpan hE'root hhH,
          le_normalizer hhΓ⟩⟩
  obtain ⟨-, -, -, -, -, -, hQM, -, hQX, hQn, -, -, hB, -, -, -, hfin, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ {a}
  refine isCyclic_of_le_sup_of_coprime
    (Q := graphFixedParabolicRadical t K σ.toRingHom {a})
    (R := (orbitRankOneHom t K σ.toRingHom a).range) (T := graphFixedRootTorus t K σ.toRingHom)
    ?_ hRX (graphFixedRootTorus_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic t K _ {a}))
    ((normal_subgroupOf_iff_le_normalizer hQX).1 hQn) hTR (hfin 2) ?_ hr2 hrT
    (fun P' h hP' => isCyclic_of_le_range_of_ker_scalar _ (fun g hg => by
      obtain ⟨l, -, hl⟩ := eq_smul_one_of_mem_ker_orbitRankOneHom hg
      exact ⟨l, hl⟩) hr2 h hP') hP hPr
  · refine sup_le (fun b hb => ?_) ((closure_le _).2 ?_)
    · have hb' : b ∈ (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) := hb
      rw [hB] at hb'
      obtain ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩ := hb'
      exact mul_mem (mem_sup_left (mem_sup_left hq))
        (mul_mem (mem_sup_right hh) (mem_sup_left (mem_sup_right (hV hv))))
    · rintro _ ⟨b, hb, rfl⟩
      exact mem_sup_left (mem_sup_right (hn b hb))
  · refine eq_bot_iff.2 fun g hg => ?_
    rw [← hQM]
    exact ⟨hg.1, hRM hg.2⟩

end Levi

end CFSG.RankThree.PartOne.KFU
