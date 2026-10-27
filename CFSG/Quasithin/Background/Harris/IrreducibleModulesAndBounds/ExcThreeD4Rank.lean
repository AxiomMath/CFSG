module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4SylowInst
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem rank_transport_N {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') {N : ℕ}
    (hr : ∀ B : Subgroup S', (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ N) :
    ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ N := by
  intro B hBc hB2
  have h := hr (B.map e.toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBc x hx y hy]) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hB2 x hx, map_one])
  rwa [Subgroup.card_map_of_injective e.injective] at h

theorem rank_le_of_sylow {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) {N : ℕ}
    (hP : ∀ B : Subgroup (P : Subgroup G), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ N) :
    ∀ E : Subgroup G, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ N := by
  intro E hc h2
  have hE : IsPGroup 2 E := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_one, sq] using h2 g.1 g.2⟩
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  have hQ := rank_transport_N (Sylow.equiv Q P) hP
  have hB := hQ (E.subgroupOf Q) (fun x hx y hy => Subtype.ext
      (hc _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy)))
    (fun x hx => Subtype.ext (h2 _ (Subgroup.mem_subgroupOf.1 hx)))
  have hcard : Nat.card (E.subgroupOf Q) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv
  rwa [hcard] at hB

section Main


theorem trialityD4_rank_le {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∀ B : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
        Nat.card B ≤ 2 * (2 ^ f) ^ 5 := by
  have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hK'
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [pow_succ, pow_zero, one_mul, RingHom.mul_def, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ3E : σ ^ 3 = 1 :=
    RingEquiv.ext fun c => by
      change σ (σ (σ c)) = c
      exact ringEquiv_cube_apply_eq hK hσ c
  have hkcard : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f := by
    obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3E
    have hcardL := card_orbitField_D4_orientation (K := K) Nat.prime_two hf hK (r := 1)
      (Or.inl rfl) (σ := σ.toRingHom) (fun c => by show σ c = _; rw [hσ c, pow_one]) ⟨1, by decide⟩
    rw [← hL2, hcardL, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]
  have hK3 : Nat.card K = Nat.card (trialityFixedField K σ.toRingHom) ^ 3 := by
    rw [hkcard, hK]
  obtain ⟨D⟩ := exists_d4Syl K σ hσ3
  haveI : Finite (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :=
    Finite.of_surjective _ D.bij.2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Psyl, hsyl⟩⟩ :=
    even_triality_positive_orbit_parametrization K σ hσ3
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_injective (fun g => (g : ModGL TwistTag.D4.tag K)) Subtype.val_injective
  have hle : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  let e : (Psyl : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    (MulEquiv.subgroupCongr hsyl).trans (Subgroup.subgroupOfEquivOfLe hle)
  refine rank_le_of_sylow Psyl (rank_transport_N e fun B hc h2 => ?_)
  have := D.card_elemAbelian_le hK3 B hc h2
  rwa [hkcard] at this

end Main

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
