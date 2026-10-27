module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianRootDatum
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwSetup
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Blueprint (LieModel)
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Minuscule.MinData.Valid

section OddSplit

theorem oddCentralSplit_twistedE6 {k : Type} [Field k] [Finite k] {θ : k →+* k}
    (hθ : ∀ c, θ (θ c) = c) [CharP k 2] :
    CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit ↥(fixedGroup k θ) := by
  intro E _ _ π hπ hcen hodd
  exact CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_exists_section_of_coprime
    (k := k) hθ hπ hcen (Nat.coprime_two_left.2 hodd)

end OddSplit

section Cover

theorem exists_odd_cover_twistedE6 {K : Type} [Group K] [Finite K] {m f : ℕ}
    (hL : LieModel (K ⧸ Subgroup.center K) .twistedE6 m 2 f)
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K))) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (θ : k →+* k),
      CharP k 2 ∧ (∀ c, θ (θ c) = c) ∧
      ∃ α : ↥(fixedGroup k θ) →* K, Function.Surjective α ∧ Odd (Nat.card α.ker) := by
  obtain ⟨-, hf1, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hL
  obtain ⟨k, hkfield, hkfin, hkcard, θ, hθq, ⟨e⟩⟩ := hT
  let : Field k := hkfield
  let : Finite k := hkfin
  have hk2 : Nat.card k = (2 ^ f) ^ 2 := by rw [hkcard]; rfl
  have hθ2 : ∀ c, θ (θ c) = c :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card hk2 hθq
  have hcard2 : Nat.card k = 2 ^ (2 * f) := by rw [hk2, ← pow_mul, mul_comm]
  have hk4 : 4 ≤ Nat.card k := by
    rw [hcard2]
    exact (show 4 ≤ 2 ^ 2 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hchar : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hcard2
  let : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  have : Group.IsPerfect K := ⟨hq.1⟩
  have hZt : Subgroup.center
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived θ) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.center_twDerived_eq_bot
      (σ := θ) Nat.prime_two (by omega) hk2 hθq
  let θm : K ⧸ Subgroup.center K ≃*
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived θ) :=
    e.trans (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.derivedCentralQuotientEquiv θ hZt)
  let β := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog θ hθ2 hk4
  let η := θm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hηker : η.ker = Subgroup.center K := by
    dsimp only [η]
    rw [MonoidHom.ker_comp_of_injective _ θm.toMonoidHom θm.injective, QuotientGroup.ker_mk']
  obtain ⟨α, hαcomp, hαsurj, -⟩ :=
    CFSG.SeitzReduction.SeitzQ2.exists_surjective_of_oddCentralSplit (β := β) (η := η)
      (oddCentralSplit_twistedE6 hθ2)
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twIsog_surjective θ hθ2 hk4)
      (θm.surjective.comp (QuotientGroup.mk'_surjective _)) hηker.le (by rw [hηker]; exact hodd)
  refine ⟨k, hkfield, hkfin, θ, hchar, hθ2, α, hαsurj, ?_⟩
  have hαle : α.ker ≤ Subgroup.center ↥(fixedGroup k θ) := fun x hx =>
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_center_of_twIsog_eq_one θ hθ2 hk4
      (show β x = 1 by rw [← hαcomp x, MonoidHom.mem_ker.1 hx, map_one])
  refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le hαle)
  rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
    (q := 2 ^ f) hk2 hθq).1]
  exact Odd.of_dvd_nat (by norm_num) (Nat.gcd_dvd_left 3 _)

theorem k_BorelTorusAbelian_twistedE6 : K_BorelTorusAbelian_twistedE6 := by
  refine k_BorelFamily_of_odd_card_center .twistedE6 ?_
  intro K _ _ m f _ hL hq hodd S hS
  obtain ⟨k, hkfield, hkfin, θ, hchar, hθ2, α, hα, hoddα⟩ :=
    exists_odd_cover_twistedE6 hL hq hodd
  let : Field k := hkfield
  let : Finite k := hkfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := hchar
  let : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  have : Finite ↥(fixedGroup k θ) := Subtype.finite
  exact k_BorelFamily_of_odd_cover_rootDatum
    (D := twistedDatum k θ) (n := nHat θ) (H := hHat k θ)
    (twistedDatum_isCTGroupDatum θ hθ2 (iSup_twistedDatum_rootGroup θ hθ2))
    (twistedDatum_steinbergExtras θ hθ2) (twistedDatum_bruhatExtras θ)
    (fun γ hγ => CFSG.LieType.HighestRoot.isPGroup_twistedE6_rootGroup θ
      (isRoot_of_mem_twistedDatum_roots θ hγ))
    (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.coprime_card_torus θ hθ2 (p := 2))
    α hα hoddα S hS

end Cover

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
