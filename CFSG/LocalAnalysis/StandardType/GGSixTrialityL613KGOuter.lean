module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGClass

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.StandardType.D4Rank

@[expose] def GGD4FieldSylowInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ α : MulAut (Om8 K), α ^ 3 = 1 →
      (∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = α) →
      ∀ S : Sylow 3 (Om8 K), (∀ s ∈ (S : Subgroup (Om8 K)), α s = s) → α ∈ inner (Om8 K)

namespace L613KG

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem dgHom_injective : Function.Injective (dgHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  funext k
  have h := congrFun (congrArg (fun x => act x (Pi.single (ie k) 1)) hc) (ie k)
  simp only [dgHom_apply, act_dg, act_one, twHom_ie, Pi.single_eq_same, mul_one] at h
  exact Units.ext h

theorem isElemAbelian_eTorus : CFSG.Assembly.IsElemAbelian 3 (eTorus (K := K)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, c, -, rfl⟩ := a
    obtain ⟨_, d, -, rfl⟩ := b
    change dgHom c * dgHom d = dgHom d * dgHom c
    rw [← map_mul, ← map_mul, mul_comm c d]
  · rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply] at hc
    rw [← map_pow, hc, map_one]

theorem card_eTorus_ge (hK3 : 3 ∣ Nat.card K - 1) : 81 ≤ Nat.card (eTorus (K := K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact hK3)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  rw [eTorus, Subgroup.card_map_of_injective dgHom_injective]
  let F : (Fin 4 → Fin 3) → (powMonoidHom 3 : (Fin 4 → Kˣ) →* (Fin 4 → Kˣ)).ker :=
    fun a => ⟨fun k => ω ^ (a k : ℕ), by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      funext k
      simp only [Pi.pow_apply, Pi.one_apply]
      rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]⟩
  have hF : Function.Injective F := by
    intro a b hab
    funext k
    have h := congrFun (congrArg Subtype.val hab) k
    have hk := pow_injOn_Iio_orderOf (x := ω) (by rw [hω]; exact (a k).2)
      (by rw [hω]; exact (b k).2) h
    exact Fin.ext hk
  have h := Nat.card_le_card_of_injective F hF
  rw [Nat.card_fun, Nat.card_fin, Nat.card_fin] at h
  simpa using h

theorem not_fix_sylow_of_not_semilinear (hK3 : 3 ∣ Nat.card K - 1) {α : MulAut (Om8 K)}
    (hα3 : α ^ 3 = 1) (hns : ∀ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g ≠ α)
    (S : Sylow 3 (Om8 K)) (hfix : ∀ s ∈ (S : Subgroup (Om8 K)), α s = s) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S'', hS''⟩ := (isPGroup_eTorus (K := K)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Om8 K) S S''
  set E := (eTorus (K := K)).map (MulAut.conj g⁻¹).toMonoidHom with hE
  have hES : ∀ e ∈ E, α e = e := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ (S'' : Subgroup (Om8 K)) := hS'' hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨s, hs, rfl⟩ := hx'
    have e : (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g • s) = s := by
      rw [MulAut.smul_def]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hfix s hs
  have hEl : CFSG.Assembly.IsElemAbelian 3 E := isElemAbelian_map _ isElemAbelian_eTorus
  have h9 := card_le_nine_of_classInput ggD4TrialityClassInput_holds α hα3 hns E hEl hES
  have hcard : Nat.card E = Nat.card (eTorus (K := K)) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have h81 := card_eTorus_ge (K := K) hK3
  omega

end L613KG

theorem ggD4OuterSylowInput_of_field (h : GGD4FieldSylowInput) : GGD4OuterSylowInput := by
  intro K _ _ _ hK3 α hα3 S hS
  by_cases hsl : ∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = α
  · exact h K hK3 α hα3 hsl S hS
  · exact (L613KG.not_fix_sylow_of_not_semilinear hK3 hα3 (fun g hg => hsl ⟨g, hg⟩) S hS).elim

section Main

theorem ggD4TrialityCentralInput_of_rest (hF : GGD4FieldSylowInput)
    (h2 : GGD4SemilinearLayerInput) (h4 : GGD4ClassThreeLayerInput) :
    GGD4TrialityCentralInput :=
  ggD4TrialityCentralInput_of_om8 (ggD4OuterSylowInput_of_field hF) h2
    ggD4CentralClassThreeInput_holds h4

theorem ggSixTrialityInput_of_rest (h611 : GGSixLSixElevenInput) (hF : GGD4FieldSylowInput)
    (h2 : GGD4SemilinearLayerInput) (h4 : GGD4ClassThreeLayerInput)
    (h5 : GGD4ClassThreeCentralInput) (h6 : GGSixTrialityDClassThreeInput) :
    GGSixTrialityInput :=
  ggSixTrialityInput_of_lSixEleven_central h611 (ggD4TrialityCentralInput_of_rest hF h2 h4)
    (ggSixTrialityDCentralInput_of_om8 h6 h5)

end Main

end CFSG.StandardType
