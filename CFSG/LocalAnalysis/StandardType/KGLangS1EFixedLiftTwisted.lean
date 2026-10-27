module

public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.LieType.Chevalley.GraphFixedData
import CFSG.LieType.Simplicity.Exceptional
import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift
import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Lift
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKernelCore
import CFSG.LocalAnalysis.StandardType.GGTBE6Cover
public import CFSG.LieType.Chevalley.RootCommutatorData

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6


theorem kgLangS1EFixedLift_twistedCover (k : Type) [Field k] [Finite k] [CharP k 2] {q : ℕ}
    (hq : 5 ≤ q) (hk : Nat.card k = q ^ 2) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ q)
    (R : Type) [Group R] (ε : R ≃* ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom))
    (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    (α : MulAut K) :
    ∃ (κ : ↥(fixedGroup k σ.toRingHom) →* K) (αU : MulAut ↥(fixedGroup k σ.toRingHom)),
      Function.Surjective κ ∧
      (∀ u, ((ε (θ (QuotientGroup.mk (κ u))) :
          ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom)) : ModGL TwistTag.E6.tag k) =
        ((e6Isogeny k (u : ↥(e6Data_valid.minGroup k)) : ↥(adjointGroup Tag.E6 k)) :
          ModGL Tag.E6 k)) ∧
      (∀ u, κ (αU u) = α (κ u)) := by
  classical
  have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c =>
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card (θ := σ.toRingHom)
      hk hσ c
  have hk4 : 4 ≤ Nat.card k := by rw [hk]; nlinarith
  obtain ⟨f, hf1, rfl⟩ : ∃ f : ℕ, 1 ≤ f ∧ q = 2 ^ f := by
    letI : Fintype k := Fintype.ofFinite k
    obtain ⟨n, -, hn⟩ := FiniteField.card k 2
    have hdvd : q ∣ 2 ^ (n : ℕ) := by
      rw [← hn, ← Nat.card_eq_fintype_card, hk]
      exact Dvd.intro q (by ring)
    obtain ⟨f, -, hfq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    refine ⟨f, ?_, hfq⟩
    rcases f with _ | f
    · simp at hfq; omega
    · omega
  have hder := (CFSG.LieType.Chevalley.finite_fixed_root_group_perfect TwistTag.E6
    Nat.prime_two hf1 k hk σ.toRingHom hσ).2.2.1
  let ψ : K →* ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) :=
    ε.toMonoidHom.comp (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
  have hψs : Function.Surjective ψ :=
    ε.surjective.comp (θ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hψk : ψ.ker ≤ Subgroup.center K := by
    intro x hx
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := by
      have hx' : ε (θ (QuotientGroup.mk x)) = 1 := hx
      exact θ.injective (ε.injective (by rw [hx', map_one, map_one]))
    exact (QuotientGroup.eq_one_iff x).mp h1
  let q0 : ↥(fixedGroup k σ.toRingHom) →* ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) :=
    (MulEquiv.subgroupCongr hder).toMonoidHom.comp
      (CFSG.LieType.Simplicity.twistedIsogeny σ.toRingHom hθ hk4)
  have hq0s : Function.Surjective q0 :=
    (MulEquiv.subgroupCongr hder).surjective.comp
      (CFSG.LieType.Simplicity.twistedIsogeny_surjective σ.toRingHom hθ hk4)
  have hq0k : q0.ker = Subgroup.center ↥(fixedGroup k σ.toRingHom) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hder).injective]
    exact CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.ker_twistedIsogeny_eq_center hθ hk4
  have hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(fixedGroup k σ.toRingHom)),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : ↥(fixedGroup k σ.toRingHom) →* E, ∀ g, π (s g) = g :=
    fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_exists_section_of_central
        (θ := σ.toRingHom) hq hk hσ hπ hcen
  obtain ⟨κ, hκψ, hκs⟩ :=
    CFSG.StandardType.E6ThreeKernel.exists_surjective_of_split hq0s hsec hψs hψk hK
  have hκker : κ.ker ≤ Subgroup.center ↥(fixedGroup k σ.toRingHom) := by
    intro x hx
    rw [← hq0k, MonoidHom.mem_ker, ← hκψ x]
    rw [MonoidHom.mem_ker] at hx
    rw [hx, map_one]
  have hperfU : commutator ↥(fixedGroup k σ.toRingHom) = ⊤ :=
    (fixedGroup_isPerfect_of_four_le_card σ.toRingHom hθ hk4).commutator_eq_top
  obtain ⟨αU, hαU⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.exists_lift_aut κ hκs hκker hperfU
      hsec α
  exact ⟨κ, αU, hκs, fun u => congrArg Subtype.val (hκψ u), hαU⟩

theorem kgLangS1EFixedLift_twisted_isPerfect (k : Type) [Field k] [Finite k] {q : ℕ}
    (hq : 5 ≤ q) (hk : Nat.card k = q ^ 2) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ q) :
    Group.IsPerfect ↥(fixedGroup k σ.toRingHom) := by
  have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c =>
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card (θ := σ.toRingHom)
      hk hσ c
  have hk4 : 4 ≤ Nat.card k := by rw [hk]; nlinarith
  exact fixedGroup_isPerfect_of_four_le_card σ.toRingHom hθ hk4

end CFSG.StandardType
