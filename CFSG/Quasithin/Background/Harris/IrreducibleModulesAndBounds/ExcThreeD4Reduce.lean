module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Generic
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LieType.Steinberg.CentralExt.GriessTriality

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section Cover

theorem trialityD4_cover {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
      (π : E →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥ := by
  intro E _ _ _ π hπ hcen _
  obtain ⟨-, -, -, -, -, hcomm, -, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hq2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f) := hσ
  let eT := CFSG.LieType.Steinberg.TwistedD4.twistedGroupEquivDerived σ.toRingHom hq2 hK hσq
  let eC : CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    eT.trans (MulEquiv.subgroupCongr hcomm)
  let π' : E →* CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom :=
    eC.symm.toMonoidHom.comp π
  have hπ' : Function.Surjective π' := eC.symm.surjective.comp hπ
  have hcen' : π'.ker ≤ Subgroup.center E := fun x hx => hcen (by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact eC.symm.map_eq_one_iff.1 hx)
  obtain ⟨s', hs'⟩ : ∃ s : CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom →* E,
      ∀ g, π' (s g) = g := by
    rcases (show 2 ^ f = 2 ∨ 3 ≤ 2 ^ f by
      have : 2 ≤ 2 ^ f := hq2
      by_cases h2 : 2 ^ f = 2
      · exact Or.inl h2
      · exact Or.inr (by omega)) with h2 | h3
    · have hf1 : f = 1 := by
        have := Nat.pow_right_injective (le_refl 2) (show 2 ^ f = 2 ^ 1 by rw [h2])
        exact this
      subst hf1
      exact CFSG.LieType.Steinberg.CentralExt.GriessExceptional.triality_two_exists_section
        (by simpa using hK) (fun c => by simpa using hσq c) hπ' hcen'
    · exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.triality_exists_section_of_central
        h3 hK hσq hπ' hcen'
  refine ker_eq_bot_of_section π hcen (s'.comp eC.symm.toMonoidHom) fun g => ?_
  exact eC.symm.injective (hs' (eC.symm g))

end Cover

section Main

theorem trialityD4_ppd_dvd_card {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ 2 ^ (12 * f) - 1)
    (hmin : ¬ p ∣ 2 ^ (4 * f) - 1) :
    p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ) := by
  obtain ⟨hcard, -⟩ := triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K hK 1
    (Or.inl rfl) σ (fun c => by rw [hσ c, pow_one])
  rw [hcard]
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hfac : (2 ^ f) ^ 12 - 1 = ((2 ^ f) ^ 4 - 1) * (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1)) := by
    have h4 : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [h4, Nat.one_le_pow 12 (2 ^ f) (by omega)]
    ring
  have h12 : (2 : ℕ) ^ (12 * f) = (2 ^ f) ^ 12 := by rw [← pow_mul, mul_comm]
  rw [h12, hfac] at hdvd
  have h4f : (2 ^ f) ^ 4 - 1 = 2 ^ (4 * f) - 1 := by rw [← pow_mul, mul_comm]
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact absurd (h4f ▸ h) hmin
  · exact Dvd.dvd.mul_left h _

end Main

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
