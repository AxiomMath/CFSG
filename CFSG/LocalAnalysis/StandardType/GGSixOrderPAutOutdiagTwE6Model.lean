module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Model
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.ComponentInitial

namespace OutdiagTwE6

theorem exists_injective_factor {A C G : Type*} [Group A] [Group C] [Group G] {π : A →* C}
    (hπ : Function.Surjective π) {ψ : A →* G} (hker : ψ.ker = π.ker) :
    ∃ χ : C →* G, Function.Injective χ ∧ ∀ a, χ (π a) = ψ a := by
  have hle : π.ker ≤ ψ.ker := hker.ge
  refine ⟨MonoidHom.liftOfSurjective π hπ ⟨ψ, hle⟩, ?_, fun a => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨a, rfl⟩ := hπ x
    have h1 : ψ a = 1 := by
      rw [← hx]
      exact (MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
        (Function.rightInverse_surjInv hπ) ⟨ψ, hle⟩ a).symm
    have h2 : a ∈ π.ker := hker ▸ h1
    exact h2
  · exact MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨ψ, hle⟩ a

end OutdiagTwE6

section Inner

namespace OutdiagTwE6

theorem mem_inner_of_pow_eq_one_aux {f r : ℕ} (hf : 1 ≤ f) (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hrf : ¬ r ∣ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hα : α ^ r = 1) :
    α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  have hK2 : Nat.card K = 2 ^ (f * 2) := by rw [hK, ← pow_mul]
  have hring := (card_ringAut_and_isCyclic Nat.prime_two K hK2).1
  have hΘ : Θ α = 1 := by
    have hp : (Θ α) ^ r = 1 := by rw [← map_pow, hα, map_one]
    have h1 : orderOf (Θ α) ∣ f * 2 := by
      have h := orderOf_dvd_natCard (Θ α)
      rwa [hring] at h
    have h2 : orderOf (Θ α) ∣ r := orderOf_dvd_of_pow_eq_one hp
    rcases (Nat.dvd_prime hr).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h1
      rcases (Nat.Prime.dvd_mul hr).mp h1 with h3 | h3
      · exact absurd h3 hrf
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3) hr2
  have hmem : α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rw [← hker]
    exact hΘ
  refine ExcNonsplit.mem_inner_of_pow_eq_one (D := twistedE6Diag K σ) ?_ hr hr3 hmem hα
  intro d hd
  have hdm : d ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := Subgroup.mem_sup_right hd
  have h3 := hcube (QuotientGroup.mk (⟨d, hdm⟩ : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ)))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

end OutdiagTwE6

end Inner

section Model

namespace OutdiagTwE6

theorem mem_inner_of_pow_eq_one {f r : ℕ} (hf : 1 ≤ f) (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hrf : ¬ r ∣ f)
    {α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hα : α ^ r = 1) :
    α ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  have key : ∀ θ : GaloisField 2 (2 * f) →+* GaloisField 2 (2 * f),
      θ = (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom →
      ∀ α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) θ), α ^ r = 1 →
        α ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) θ) →*
          MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) θ)).range := by
    intro θ hθ α hα
    subst hθ
    exact mem_inner_of_pow_eq_one_aux hf hr hr2 hr3 hrf hK _ hσ hα
  exact key _ hσθ.symm α hα

theorem mem_range_of_pow_eq_one {G : Type*} [Group G] {f r : ℕ} (hf : 1 ≤ f) (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrf : ¬ r ∣ f)
    {χ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G}
    (hχ : Function.Injective χ) (hC : Subgroup.centralizer (χ.range : Set G) = ⊥) {m : G}
    (hm : m ∈ Subgroup.normalizer (χ.range : Set G)) (hmr : m ^ r = 1) : m ∈ χ.range := by
  obtain ⟨α, hα⟩ := OutdiagModel.exists_induces hχ hm
  have hαr : α ^ r = 1 := by
    have h1 := hα.pow r
    rw [hmr] at h1
    exact OutdiagModel.Induces.unique hχ h1 OutdiagModel.Induces.one
  obtain ⟨c, rfl⟩ := mem_inner_of_pow_eq_one hf hr hr2 hr3 hrf hαr
  rw [OutdiagModel.Induces.inj hC hα (OutdiagModel.Induces.conj (χ := χ) c)]
  exact ⟨c, rfl⟩

theorem exists_model {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* G}
    (hS : GGSixFusionSetting p Bs G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ) :
    ∃ χ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G,
      Function.Injective χ ∧ χ.range = G₀ ∧
      ∀ c ∈ Subgroup.normalizer (G₀ : Set G), GGPsiInnerDiag (ggU .twistedE6 n f).D ψ c →
        ∃ α ∈ LayerSixE.twInndiagAut f, OutdiagModel.Induces χ c α := by
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, hperf, -⟩ := hS.presents
  have hC := hS.centralizer_eq_bot
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  subst hrange
  obtain ⟨π, hπ, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hπker ▸ hker
  have hkerEq : ψ.ker = π.ker := by
    refine le_antisymm hkπ ?_
    rw [hπker]
    intro z hz
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subgroup.mem_center_iff.mp hz y)
    rw [hC, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχ, hval⟩ := exists_injective_factor hπ hkerEq
  have hrange : χ.range = ψ.range := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨y, rfl⟩ := hπ c
      exact ⟨y, (hval y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨π y, hval y⟩
  refine ⟨χ, hχ, hrange, ?_⟩
  intro c hcN hci
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hcN hci
  refine ⟨α, hαD, fun x => ?_⟩
  obtain ⟨u, rfl⟩ := hπ x
  obtain ⟨u', hu'⟩ := LayerSixE.exists_conj_eq hcN u
  calc c * χ (π u) * c⁻¹ = c * ψ u * c⁻¹ := congrArg (fun t => c * t * c⁻¹) (hval u)
    _ = ψ u' := hu'.symm
    _ = χ (π u') := (hval u').symm
    _ = χ (α (π u)) := congrArg χ (hα u u' hu')

end OutdiagTwE6

end Model

end CFSG.StandardType
