module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.HardMathSupport.Lang.D4Three.Outer
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LocalAnalysis.StandardType.GGCentD4RatTwAux

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three

theorem ntpD4_rat_twisted
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ((2 : ℕ) ^ f) ^ 3)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra K L]
    (r : ℕ) (hr : r = 1 ∨ r = 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (((2 : ℕ) ^ f) ^ r))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f))
    (g : ↥(adjointGroup Tag.D4 L)) (ε : ℕ) (hε : ε = 1 ∨ ε = 2)
    (hcomm : ∀ x ∈ adjointGroup Tag.D4 L,
      d4P L ^ r * Units.map (entrywiseHom Fr) ((g : ModGL Tag.D4 L) *
          (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) * (d4P L ^ r)⁻¹ =
        (g : ModGL Tag.D4 L) * (d4P L ^ ε * (d4P L ^ r * Units.map (entrywiseHom Fr) x *
          (d4P L ^ r)⁻¹) * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) :
    ∃ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        (baseChangeGL (algebraMap K L) (φ x).1 : ModGL Tag.D4 L) =
          (g : ModGL Tag.D4 L) * (d4P L ^ ε *
            (baseChangeGL (algebraMap K L) x.1 : ModGL Tag.D4 L) *
            (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) ∧
      φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hσ3 : σ ^ 3 = 1 := ntpRT_sigma_cube hf hK σ hσ
  have hσ3c : ∀ c, σ (σ (σ c)) = c := fun c => by
    have h := congrArg (fun e : K ≃+* K => e c) hσ3
    simpa using h
  have hSg := ntpRT_S_fixed hf hK r hr Fr hFr g ε hε hcomm
  obtain ⟨g', hg'⟩ := ntpRT_mem_image hf hK r hr σ hσ Fr hFr g hSg
  let ιH : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      ↥(adjointGroup Tag.D4 L) :=
    (adjointBaseChangeHom Tag.D4 (algebraMap K L)).comp
      (Subgroup.inclusion ((graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom).trans inf_le_left))
  have hιH : ∀ u, (ιH u : ModGL Tag.D4 L) = baseChangeGL (algebraMap K L) u.1 := fun _ => rfl
  have hgι : (ιH g' : ModGL Tag.D4 L) = (g : ModGL Tag.D4 L) := by
    rw [hιH]
    exact hg'
  refine ⟨MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)), ?_, ?_⟩
  · intro x
    have hrel : d4P L ^ ε * (ιH x : ModGL Tag.D4 L) * (d4P L ^ ε)⁻¹ =
        (ιH (fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x) : ModGL Tag.D4 L) := by
      rw [hιH x, hιH (fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x)]
      exact ntpRT_entrywise_eq_conj (K := K) (L := L) σ hε x
    have hφx : (ιH ((MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) x) :
        ModGL Tag.D4 L) =
        (g : ModGL Tag.D4 L) *
          (ιH (fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x) : ModGL Tag.D4 L) *
            (g : ModGL Tag.D4 L)⁻¹ := by
      have h1 : (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) x =
          g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x * (g')⁻¹ := by
        simp only [MulAut.mul_apply, MulAut.conj_apply]
      rw [h1]
      have h2 : (ιH (g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x * (g')⁻¹) :
          ModGL Tag.D4 L) =
          (ιH g' : ModGL Tag.D4 L) *
            (ιH (fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x) : ModGL Tag.D4 L) *
              (ιH g')⁻¹ := by
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h2]
      simp only [Subgroup.coe_inv, hgι]
    calc ((baseChangeGL (algebraMap K L)
        ((MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) x).1 :
          ModGL Tag.D4 L))
        = (ιH ((MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) x) :
          ModGL Tag.D4 L) := (hιH _).symm
      _ = (g : ModGL Tag.D4 L) *
            (ιH (fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) x) : ModGL Tag.D4 L) *
              (g : ModGL Tag.D4 L)⁻¹ := hφx
      _ = (g : ModGL Tag.D4 L) *
            (d4P L ^ ε * (ιH x : ModGL Tag.D4 L) * (d4P L ^ ε)⁻¹) *
              (g : ModGL Tag.D4 L)⁻¹ := by rw [← hrel]
      _ = (g : ModGL Tag.D4 L) *
            (d4P L ^ ε * (baseChangeGL (algebraMap K L) x.1 : ModGL Tag.D4 L) *
              (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹ :=
        congrArg (fun z : ModGL Tag.D4 L => (g : ModGL Tag.D4 L) *
          (d4P L ^ ε * z * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) (hιH x).symm
  · rcases hr with rfl | rfl
    · obtain ⟨⟨Θ, hΘ, hker⟩, -⟩ := exists_theta (p := 2) Nat.prime_two hf hK σ (by
        simpa using hσ)
      have hδ : σ ^ (3 - ε) ≠ 1 := ntpRT_sigma_pow_ne_one hf (Or.inl rfl) hK σ hσ ε hε
      intro hin
      have h1 : Θ (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) =
          σ ^ (3 - ε) := hΘ _ g' _ rfl
      have h2 : MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)) ∈ Θ.ker := by
        rw [hker]
        exact hin
      rw [MonoidHom.mem_ker, h1] at h2
      exact hδ h2
    · set τ : K ≃+* K := σ ^ 2 with hτdef
      haveI : Fintype K := Fintype.ofFinite K
      have hτ : ∀ c, τ c = c ^ ((2 : ℕ) ^ f) := by
        intro c
        have hq3 : ∀ d : K, d ^ ((2 : ℕ) ^ f) ^ 3 = d := fun d => by
          rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
        rw [hτdef, pow_two, RingAut.mul_apply, hσ, hσ, ← pow_mul,
          show ((2 : ℕ) ^ f) ^ 2 * ((2 : ℕ) ^ f) ^ 2 =
            ((2 : ℕ) ^ f) ^ 3 * (2 : ℕ) ^ f by ring, pow_mul, hq3]
      have hστ : ∀ c, σ (τ c) = c := fun c => by
        change σ (σ (σ c)) = c
        exact hσ3c c
      have h1 : τ.toRingHom.comp σ.toRingHom = RingHom.id K := RingHom.ext fun c => by
        change τ (σ c) = c
        have h := congrArg (fun e : K ≃+* K => e c) hσ3
        simpa [hτdef, pow_two, RingAut.mul_apply] using h
      set e : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃*
          ↥(graphFixedRootGroup TwistTag.D4 K τ.toRingHom) :=
        (Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
            (MulAut.conj (CFSG.RankThree.Chevalley.permModuleMap
              CFSG.HardMathSupport.Dickson.DefCharOuter.Export.d4OuterSwap_cartan K)).toMonoidHom
            (MulAut.conj (CFSG.RankThree.Chevalley.permModuleMap
              CFSG.HardMathSupport.Dickson.DefCharOuter.Export.d4OuterSwap_cartan
                K)).injective).trans
          (MulEquiv.subgroupCongr
            (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.map_conj_outerSwap_graphFixedRootGroup
              K h1 (RingHom.ext hστ))) with hedef
      have hτδ : (MulAut.congr e) (fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) =
          fieldActor (t := TwistTag.D4) τ (σ ^ (3 - ε)) := by
        rw [hedef]
        exact ntpRT_orient_fieldActor σ τ h1 (RingHom.ext hστ) (σ ^ (3 - ε))
      have hcongr : (MulAut.congr e)
          (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) =
          MulAut.conj (e g') * fieldActor (t := TwistTag.D4) τ (σ ^ (3 - ε)) := by
        rw [map_mul, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, hτδ]
      have hδ : σ ^ (3 - ε) ≠ 1 := ntpRT_sigma_pow_ne_one hf (Or.inr rfl) hK σ hσ ε hε
      obtain ⟨⟨Θ, hΘ, hker⟩, -⟩ := exists_theta (p := 2) Nat.prime_two hf hK τ hτ
      have hnot : (MulAut.congr e)
          (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) ∉
          CFSG.ComponentClassification.OuterAutomorphisms.inner
            ↥(graphFixedRootGroup TwistTag.D4 K τ.toRingHom) := by
        intro hin
        have h1 : Θ ((MulAut.congr e)
            (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε)))) =
            σ ^ (3 - ε) := by
          rw [hcongr]
          exact hΘ _ (e g') _ rfl
        have h2 : (MulAut.congr e)
            (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) ∈ Θ.ker := by
          rw [hker]
          exact hin
        rw [MonoidHom.mem_ker, h1] at h2
        exact hδ h2
      intro hin
      have hmem : (MulAut.congr e)
          (MulAut.conj g' * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - ε))) ∈
          (CFSG.ComponentClassification.OuterAutomorphisms.inner
            ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
              (MulAut.congr e).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hin
      rw [CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at hmem
      exact hnot hmem

end CFSG.StandardType.NTPlane
