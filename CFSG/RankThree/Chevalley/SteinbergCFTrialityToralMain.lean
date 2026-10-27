module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralSylow
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralQuasisimple

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TrialityFold
open scoped Pointwise commutatorElement

section Helpers

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem nonempty_SL2_mulEquiv_outer (hσ : σ ^ 3 = 1) (h3 : ∀ c, σ (σ (σ c)) = c)
    {v : WeylGroup TwistTag.D4.tag} (hv : v ∈ relWeylTwist TwistTag.D4) :
    Nonempty (SL2 K ≃* graphFixedRootPair TwistTag.D4 K σ.toRingHom
      (fixedOrbitImage TwistTag.D4 v ⟨0, by decide⟩)) := by
  obtain ⟨eQ⟩ := nonempty_mulEquiv_graphFixedRootPair_D4 σ hσ hv ⟨0, by decide⟩
  have htop := orbitField_D4_zero_eq_top σ h3
  have e1 : SL2 K ≃* SL2 (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) :=
    sl2CongrRingEquiv ((RingEquiv.subfieldCongr htop).trans Subfield.topEquiv).symm
  exact ⟨e1.trans eQ⟩

theorem nonempty_SL2_mulEquiv_middle (hσ : σ ^ 3 = 1) {v : WeylGroup TwistTag.D4.tag}
    (hv : v ∈ relWeylTwist TwistTag.D4) :
    Nonempty (SL2 (trialityFixedField K σ.toRingHom) ≃* graphFixedRootPair TwistTag.D4 K
      σ.toRingHom (fixedOrbitImage TwistTag.D4 v ⟨1, by decide⟩)) := by
  obtain ⟨eQ⟩ := nonempty_mulEquiv_graphFixedRootPair_D4 σ hσ hv ⟨1, by decide⟩
  have hk := (triality_all_characteristic_faithful_torus_coordinates K σ hσ).2.2.2.1
  have e1 : SL2 (trialityFixedField K σ.toRingHom) ≃*
      SL2 (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) :=
    sl2CongrRingEquiv (RingEquiv.subfieldCongr hk.symm)
  exact ⟨e1.trans eQ⟩

end Helpers

theorem foldedD4_cases (b : Fin TwistTag.D4.foldedTag.rank) :
    b = ⟨0, by decide⟩ ∨ b = ⟨1, by decide⟩ := by
  revert b
  decide

theorem triality_split_prime_toral_Sylow_and_centralizers {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f - 1) :
    (∀ P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p P →
      ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        P.map (MulAut.conj g).toMonoidHom ≤
          (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
    (∃ e : (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) ≃*
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ a b, (e (a, b) : ModGL TwistTag.D4.tag K) =
        trialityOuterTorus K σ a * trialityMiddleTorus K σ b) ∧
    (∀ S : Sylow 2 (graphFixedRootTorus TwistTag.D4 K σ.toRingHom),
      (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) ∧
    (ℓ = 2 → Odd (Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom))) ∧
    ∀ ζ : (trialityFixedField K σ.toRingHom)ˣ, orderOf ζ = p → ∀ u v : ℕ,
      trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) * trialityMiddleTorus K σ (ζ ^ v) ≠
        1 →
      ∃ a : Fin TwistTag.D4.tag.rank → Kˣ,
        trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) * trialityMiddleTorus K σ (ζ ^ v) =
          rootDiagUnit TwistTag.D4.tag a ∧
        orderOf (rootDiagUnit TwistTag.D4.tag a) = p ∧
        ((rootCharKernel a = ∅ ∧
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
              Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} =
            graphFixedRootTorus TwistTag.D4 K σ.toRingHom) ∨
        ∃ α : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧
          rootCharKernel a =
            (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∪
              -(TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∧
          ∃ D Q : Subgroup (ModGL TwistTag.D4.tag K),
            D = graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
              Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} ∧
            Q = graphFixedRootPair TwistTag.D4 K σ.toRingHom
              (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∧
            D = graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔ Q ∧
            (D : Set (ModGL TwistTag.D4.tag K)) =
              (graphFixedRootTorus TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) *
                (Q : Set (ModGL TwistTag.D4.tag K)) ∧
            ((TwistTag.D4.diagramOrbit α).card = 3 → Nonempty (SL2 K ≃* Q)) ∧
            ((TwistTag.D4.diagramOrbit α).card = 1 →
              Nonempty (SL2 (trialityFixedField K σ.toRingHom) ≃* Q)) ∧
            CFSG.IsQuasisimple Q ∧ ⁅D, D⁆ = Q ∧
            D ⊓ Subgroup.centralizer (Q : Set (ModGL TwistTag.D4.tag K)) =
              (Subgroup.center D).map D.subtype ∧
            (Subgroup.center D).map D.subtype ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ∧
            (∀ S : Sylow 2 (Subgroup.center D),
              (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) ∧
            (ℓ = 2 → Odd (Nat.card (Subgroup.center D)))) := by
  classical
  obtain ⟨hSyl, ⟨e, he⟩, hS2, hodd⟩ := triality_split_prime_toral_Sylow hℓ hf K hK σ hσ hp hp3 hpq
  refine ⟨hSyl, ⟨e, he⟩, hS2, hodd, fun ζ hζ u v hne => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul,
      show ℓ ^ f * (ℓ ^ f * ℓ ^ f) = (ℓ ^ f) ^ 3 by ring, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => h3 c
  set z := trialityFixedUnit K σ ζ with hz
  have hzp : z ^ p = 1 := by rw [hz, ← map_pow, ← hζ, pow_orderOf_eq_one, map_one]
  have hσz : ∀ m : ℕ, Units.map σ.toRingHom.toMonoidHom (z ^ m) = z ^ m := fun m =>
    Units.ext (by
      change σ ((z ^ m : Kˣ) : K) = ((z ^ m : Kˣ) : K)
      rw [Units.val_pow_eq_pow_val, map_pow, hz, sigma_trialityFixedUnit])
  have hy : trialityFixedUnit K σ (ζ ^ v) = z ^ v := map_pow _ _ _
  set A : Kˣ := (z ^ u) ^ 2 * (z ^ v)⁻¹ with hA
  set B : Kˣ := (z ^ u * z ^ u * z ^ u)⁻¹ * (z ^ v) ^ 2 with hB
  have hha : trialityOuterTorus K σ (z ^ u) * trialityMiddleTorus K σ (ζ ^ v) =
      rootDiagUnit TwistTag.D4.tag (d4Tuple A A B A) := by
    rw [trialityOuter_mul_middle_eq, hy, hσz, hσz]
  set a := d4Tuple A A B A with ha
  have hpow : ∀ m : ℕ, (z ^ m) ^ p = 1 := fun m => by
    rw [← pow_mul, mul_comm, pow_mul, hzp, one_pow]
  have hAp : A ^ p = 1 := by
    rw [hA, mul_pow, inv_pow, ← pow_mul, mul_comm 2 p, pow_mul, hpow, hpow]
    simp
  have hBp : B ^ p = 1 := by
    rw [hB, mul_pow, inv_pow, mul_pow, mul_pow, hpow, ← pow_mul, mul_comm 2 p, pow_mul, hpow]
    simp
  have hAB : ¬(A = 1 ∧ B = 1) := by
    rintro ⟨hA1, hB1⟩
    apply hne
    rw [hha, ha, hA1, hB1]
    convert rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K) using 2
    funext i
    rcases fin_cases i with rfl | rfl | rfl | rfl <;> rfl
  have hap : a ^ p = 1 := by
    funext i
    rcases fin_cases i with rfl | rfl | rfl | rfl
    · exact hAp
    · exact hAp
    · exact hBp
    · exact hAp
  have ha1 : a ≠ 1 := fun h => hAB ⟨congrFun h i0, congrFun h i2⟩
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = p := by
    rw [orderOf_rootDiagUnit]
    exact orderOf_eq_prime hap ha1
  refine ⟨a, hha, hord, ?_⟩
  rcases triality_toral_centralizer_cases σ (a := a) rfl rfl rfl rfl hp hp3 hAp hBp hAB with
    hcase | ⟨v₀, hv₀, b, hker, hOpos, hDeq, hDset⟩
  · exact Or.inl hcase
  right
  set α := v₀ • (Pi.single (TwistTag.D4.orbitMin b) 1 : Fin TwistTag.D4.tag.rank → ℤ) with hαdef
  have hαO : α ∈ fixedOrbitImage TwistTag.D4 v₀ b := ⟨_, TwistTag.D4.orbitMin_mem b, rfl⟩
  have hdiag : TwistTag.D4.diagramOrbit α = (TwistTag.D4.orbit b).image
      fun j => v₀ • (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
    rw [hαdef, TwistTag.D4.diagramOrbit_smul_single hv₀, TwistTag.D4.orbitIndex_orbitMin]
  have hOset : (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
      fixedOrbitImage TwistTag.D4 v₀ b := by
    rw [hdiag, Finset.coe_image]
    rfl
  have hcard : (TwistTag.D4.diagramOrbit α).card = (TwistTag.D4.orbit b).card := by
    rw [hdiag, TwistTag.D4.card_image_smul_single]
  have hq6 : 6 ≤ ℓ ^ f := by
    have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    have hp5 := five_le_of_prime_of_three_lt hp hp3
    have := Nat.le_of_dvd (by omega) hpq
    omega
  have h4 : ∃ s : Finset (orbitField TwistTag.D4 K σ.toRingHom b), s.card = 4 := by
    have : Fintype (orbitField TwistTag.D4 K σ.toRingHom b) := Fintype.ofFinite _
    have hcardL := card_orbitField_D4_orientation hℓ hf hK (r := 1) (Or.inl rfl)
      (σ := σ.toRingHom) (by simpa using hσ) b
    have hle : 4 ≤ (Finset.univ : Finset (orbitField TwistTag.D4 K σ.toRingHom b)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardL]
      have hpos : 1 ≤ (TwistTag.D4.orbit b).card := TwistTag.D4.card_orbit_pos b
      calc 4 ≤ ℓ ^ f := by omega
        _ ≤ (ℓ ^ f) ^ (TwistTag.D4.orbit b).card := Nat.le_self_pow (by omega) _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨hquasi, hcomm, hZ, hZH⟩ := triality_orbitPair_structure σ hσ3 hv₀ b h4 _ hDeq
  have hb := foldedD4_cases b
  set D := graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
    Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag a} with hDdef
  set ιZ : Subgroup.center D →* graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    MonoidHom.codRestrict (D.subtype.comp (Subgroup.center D).subtype) _
      (fun z => hZH ⟨z, z.2, rfl⟩)
  have hιZ : Function.Injective ιZ := fun z z' h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  refine ⟨α, IsRoot.smul (isRoot_single _ _) v₀, hOpos α hαO, by rw [hOset]; exact hker, D,
    graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v₀ b), rfl,
    by rw [hOset], hDeq, hDset, fun h3' => ?_, fun h1' => ?_, hquasi, hcomm, hZ, hZH,
    fun S => ?_, fun hℓ2 => ?_⟩
  ·
    rcases hb with rfl | rfl
    · exact nonempty_SL2_mulEquiv_outer σ hσ3 h3 hv₀
    · exfalso
      rw [hcard] at h3'
      exact absurd h3' (by decide)
  ·
    rcases hb with rfl | rfl
    · exfalso
      rw [hcard] at h1'
      exact absurd h1' (by decide)
    · exact nonempty_SL2_mulEquiv_middle σ hσ3 hv₀
  · exact comm_and_two_generated_of_injective_prod
      (e.symm.toMonoidHom.comp (ιZ.comp (S : Subgroup (Subgroup.center D)).subtype))
      (e.symm.injective.comp (hιZ.comp (S : Subgroup (Subgroup.center D)).subtype_injective))
  · have hdvd : Nat.card (Subgroup.center D) ∣
        Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective]
      exact Subgroup.card_dvd_of_le hZH
    exact Odd.of_dvd_nat (hodd hℓ2) hdvd

end CFSG.RankThree.Chevalley
