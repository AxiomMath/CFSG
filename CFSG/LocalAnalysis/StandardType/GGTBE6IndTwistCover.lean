module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LieType.Chevalley.TwistedE6EvenCover
public import CFSG.RankThree.PartOne.KEXC.OddCenterCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Coprime
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignField

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny


theorem exists_cover_fixed_of_odd {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] [Finite L] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (θ : K ≃+* K) (hθ : ∀ c, θ c = c ^ (2 ^ f))
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) (hodd : Odd (Nat.card ψ.ker)) :
    ∃ φ : fixedGroup K θ.toRingHom →* L,
      Function.Surjective φ ∧
      (∀ x, ψ (φ x) = CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθ x) ∧
      φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) := by
  have hθ2 : ∀ c, θ (θ c) = c := by
    intro c
    rw [hθ, hθ, ← pow_mul, ← pow_two, ← hK]
    let : Fintype K := Fintype.ofFinite K
    simpa only [Fintype.card_eq_nat_card] using FiniteField.pow_card c
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθ
  have hq : Function.Surjective q :=
    CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf hK θ.toRingHom hθ
  have hqc : q.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) := by
    have he := CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC
      hf hK θ.toRingHom (fun c => hθ c)
    exact he.le
  have hno2 : ∀ y ∈ ψ.ker, y ^ 2 = 1 → y = 1 := by
    intro y hy hy2
    have hc2 : Nat.Coprime 2 (Nat.card ψ.ker) := Nat.coprime_two_left.mpr hodd
    have hd : orderOf y ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard ψ.ker hy
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc2
      (orderOf_dvd_of_pow_eq_one hy2) hd)
  obtain ⟨φ, hφ, hφs⟩ := StdSubRestU.exists_surjective_of_oddKernel hq
    (fun _ _ _ π hπ hc h2 =>
      CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_exists_section_of_coprime
        hθ2 hπ hc h2) hψ hker hperf hno2
  refine ⟨φ, hφs, hφ, ?_⟩
  intro x hx
  apply hqc
  rw [MonoidHom.mem_ker, ← hφ x, hx, map_one]

theorem odd_card_ker_of_two_le {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] [Finite L] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (θ : K ≃+* K) (hθ : ∀ c, θ c = c ^ (2 ^ f))
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) : Odd (Nat.card ψ.ker) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ, -, -, -, k, hkset, hkcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two (by omega) K hK
  have hk : Nat.card (TwistedE6Cover.fixField θ.toRingHom) = 2 ^ f := by
    have heq : TwistedE6Cover.fixField θ.toRingHom = k := by
      ext c
      change θ c = c ↔ c ∈ k
      have hmem : c ∈ k ↔ c ^ 2 ^ f = c := by
        change c ∈ (k : Set K) ↔ _
        rw [hkset]
        rfl
      rw [hmem, hθ]
    rw [heq, hkcard]
  let : Group.IsPerfect L := ⟨hperf⟩
  apply CFSG.RankThree.PartOne.KEXC.odd_card_ker_of_central_two_cover ψ hψ hker
  intro E _ _ _ η hη hc h2
  exact TwistedE6Cover.ker_eq_bot_of_graphFixedRootGroup θ.surjective hf hk η hη hc h2

theorem exists_cover_fixed {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] [Finite L] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (θ : K ≃+* K) (hθ : ∀ c, θ c = c ^ (2 ^ f))
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) :
    ∃ φ : fixedGroup K θ.toRingHom →* L,
      Function.Surjective φ ∧
      (∀ x, ψ (φ x) = CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ.toRingHom hθ x) ∧
      φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) :=
  exists_cover_fixed_of_odd (by omega) hK θ hθ ψ hψ hker hperf
    (odd_card_ker_of_two_le hf hK θ hθ ψ hψ hker hperf)

end CFSG.StandardType.TBE6IndTwist
