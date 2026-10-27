module

public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergCE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

theorem exists_mulEquiv_twisted_E6_inner_fixed
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) [CharP (AlgebraicClosure F) p]
    {α : MulAut (graphFixedRootGroup TwistTag.E6 F σ.toRingHom)} (hα : α ^ 2 = 1)
    (hαi : α ∈ twistedE6Inn F σ) :
    ∃ x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
        (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
          (diagramMap TwistTag.E6 (AlgebraicClosure F))),
      x ^ 2 = 1 ∧
        Nonempty (↥(α.toMonoidHom.eqLocus
            (MonoidHom.id (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))) ≃*
          ↥(⁅fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
              (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
                (diagramMap TwistTag.E6 (AlgebraicClosure F))),
            fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
              (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
                (diagramMap TwistTag.E6 (AlgebraicClosure F)))⁆ ⊓ Subgroup.centralizer {x})) := by
  classical
  have hp : p.Prime := Fact.out
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨t, rfl⟩ := hαi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZ, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf F hF σ hσ
  have ht2 : t * t = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_mul, ← sq, hα, map_one])
  obtain ⟨-, -, -, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.E6
    hp hf hodd F hF σ.toRingHom hσ (AlgebraicClosure F)
    (iterateFrobenius (AlgebraicClosure F) p f) (fun c => iterateFrobenius_def p f c)
  obtain ⟨ι, hιdef⟩ : ∃ ι : ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag (AlgebraicClosure F),
      ι = baseChangeGL (algebraMap F (AlgebraicClosure F)) := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := hιdef ▸ baseChangeGL_injective _
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
    (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
      (diagramMap TwistTag.E6 (AlgebraicClosure F))) with hR
  have hRtw : R = twistedFixedGroup TwistTag.E6 (AlgebraicClosure F)
      (iterateFrobenius (AlgebraicClosure F) p f) := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
        (diagramMap TwistTag.E6 (AlgebraicClosure F)) y = y ↔
      twistHom TwistTag.E6 (AlgebraicClosure F) (iterateFrobenius (AlgebraicClosure F) p f) y = y
    rw [frobTwistGL_apply, twistHom_apply]
  have hRA : ⁅R, R⁆ = (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map ι := by
    rw [hRtw, hιdef]
    exact hder
  set x := ι t with hx
  have hxR' : x ∈ ⁅R, R⁆ := by
    rw [hRA]
    exact ⟨_, t.2, rfl⟩
  have hxR : x ∈ R := Subgroup.commutator_le_self R hxR'
  have hx2 : x ^ 2 = 1 := by
    rw [hx, sq, ← map_mul]
    change ι ((t * t : graphFixedRootGroup TwistTag.E6 F σ.toRingHom) :
      ModGL TwistTag.E6.tag F) = 1
    rw [ht2]
    exact map_one ι
  let φ : graphFixedRootGroup TwistTag.E6 F σ.toRingHom →*
      ModGL TwistTag.E6.tag (AlgebraicClosure F) :=
    ι.comp (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).subtype
  have hφ : Function.Injective φ := hιinj.comp Subtype.val_injective
  have hmap : ((MulAut.conj t).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))).map φ =
      ⁅R, R⁆ ⊓ Subgroup.centralizer {x} := by
    rw [hRA]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have hc' : t * c * t⁻¹ = c := hc
      have htc : t * c = c * t := mul_inv_eq_iff_eq_mul.1 hc'
      change ι (c : ModGL TwistTag.E6.tag F) * ι t = ι t * ι (c : ModGL TwistTag.E6.tag F)
      rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, htc]
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have hcx' : ι c * ι t = ι t * ι c := hcx
      rw [← map_mul, ← map_mul] at hcx'
      have htc : t * ⟨c, hc⟩ = ⟨c, hc⟩ * t := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact (hιinj hcx').symm
      change t * ⟨c, hc⟩ * t⁻¹ = ⟨c, hc⟩
      rw [htc, mul_inv_cancel_right]
  exact ⟨x, hxR, hx2,
    ⟨(Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)⟩⟩

end CFSG.LocalAnalysis.SteinbergCE
