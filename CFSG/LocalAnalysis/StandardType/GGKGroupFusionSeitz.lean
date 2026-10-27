module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionTop
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

@[expose] def GGKFLieSeitz (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p ≠ d.1.characteristic ∧
    ¬ IsD2SeitzException p d.1

@[expose] def GGKFLieSeitzException (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ IsD2SeitzException p d.1

theorem ggIsD2SeitzException_characteristic {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : IsD2SeitzException p d) : d.characteristic = 2 := by
  rcases h with ⟨-, ⟨q, hq, -, rfl⟩ | ⟨q, hq, -, rfl⟩ | ⟨q, hq, -, rfl⟩ |
    ⟨q, hq, -, rfl | rfl⟩ | rfl⟩ | ⟨-, rfl | rfl⟩
  · simpa using hq
  · simpa using hq
  · simpa using hq
  · simpa using hq
  · simpa using hq
  · exact TauCeti.LieTypeIndex.characteristic_tits
  · exact TauCeti.LieTypeIndex.characteristic_tits
  · exact TauCeti.LieTypeIndex.characteristic_suzuki 2

theorem ggGeneralizedFitting_le_of_seitz (hS : KFactSeitzRankTwo) {W : Type} [Group W]
    [Finite W] {p : ℕ} {H E : Subgroup W} (hyp : GGHypThreeSixteen p H E)
    (d : TauCeti.ValidLieTypeIndex)
    (e : ↥(CFSG.generalizedFitting W) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) (hex : ¬ IsD2SeitzException p d.1) :
    CFSG.generalizedFitting W ≤ H := by
  obtain ⟨⟨hp, hp2, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, -⟩ := hyp
  set K := CFSG.generalizedFitting W
  have : K.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hφ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine ggEq_one_of_commute_generalizedFitting hsimple hnab fun k hk => ?_
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  let ψ : W →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hψ : Function.Injective ψ := fun x y hxy => hφ ((MulAut.congr e).injective hxy)
  have hfix : ∀ (a : W) (k : K), ψ a (e k) = e k ↔ a * (k : W) * a⁻¹ = k := by
    intro a k
    have h1 : ψ a (e k) = e (MulAut.conjNormal (H := K) a k) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1, e.apply_eq_iff_eq, ← Subtype.coe_inj, MulAut.conjNormal_apply]
  have hclos := hS d p hp hp2 hpd hex (E.map ψ)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p ⟨hE.1, hE.2⟩ ψ)
    (by rw [Subgroup.card_map_of_injective hψ, hEcard])
  have hle : Subgroup.closure
      {t : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ E.map ψ, ε ≠ 1 ∧ ε t = t} ≤
      (H.subgroupOf K).map e.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro t ⟨_, ⟨a, haE, rfl⟩, hε1, hεt⟩
    refine ⟨e.symm t, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hε1 (map_one ψ)
    have hfixa : a * ((e.symm t : K) : W) * a⁻¹ = (e.symm t : K) :=
      (hfix a (e.symm t)).mp (by simpa using hεt)
    apply hfus.centralizer_le haE ha1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfixa).symm
  intro k hk
  have hk' : e ⟨k, hk⟩ ∈ Subgroup.closure
      {t : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ E.map ψ, ε ≠ 1 ∧ ε t = t} := by
    rw [hclos]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyk⟩ := hle hk'
  have hyk' : y = ⟨k, hk⟩ := e.injective hyk
  rw [hyk'] at hy
  exact Subgroup.mem_subgroupOf.mp hy

theorem ggKGroupFusionAt_seitz (hS : KFactSeitzRankTwo) : GGKGroupFusionAt GGKFLieSeitz := by
  rintro W _ _ p H E i ⟨d, rfl, hpd, hex⟩ hyp - hKH ⟨e⟩
  exact absurd (ggGeneralizedFitting_le_of_seitz hS hyp d e hpd hex) hKH

theorem ggKGroupFusionAt_lieCross_of_seitz (hS : KFactSeitzRankTwo)
    (hexc : GGKGroupFusionAt GGKFLieSeitzException) : GGKGroupFusionAt GGKFLieCross :=
  GGKGroupFusionAt.of_cover (fun _ p _ _ ⟨d, hi, hpd⟩ => by
    by_cases hx : IsD2SeitzException p d.1
    · exact Or.inr ⟨d, hi, hx⟩
    · exact Or.inl ⟨d, hi, hpd, hx⟩) (ggKGroupFusionAt_seitz hS) hexc

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggKGroupFusionLayerInput_of_families (hSch : SchreierFor InCatalog)
    (hS : KFactSeitzRankTwo) (hA : GGKGroupFusionAt GGKFAlternating)
    (hD : GGKGroupFusionAt GGKFLieDefining) (hX : GGKGroupFusionAt GGKFLieSeitzException)
    (hSp : GGKGroupFusionAt GGKFSporadic) : GGKGroupFusionLayerInput :=
  ggKGroupFusionLayerInput_of_at hSch
    (ggKGroupFusionAt_of_families hA hD (ggKGroupFusionAt_lieCross_of_seitz hS hX) hSp)

end CFSG.StandardType
