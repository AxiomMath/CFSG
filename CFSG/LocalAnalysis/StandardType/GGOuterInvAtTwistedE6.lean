module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvModelData
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6Twisted
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6TwRankOne

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Open (IsElemAbelian)

@[expose] def TwistedE6GraphNone
    : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ f) →
    ∀ (p : ℕ) (α β : MulAut (twistedE6RootGroup K σ))
      (E : Subgroup (MulAut (twistedE6RootGroup K σ))),
      p.Prime → p ≠ 2 → β ≠ 1 → β ∈ E → E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ →
      IsElemAbelian p E → p ^ 4 ≤ Nat.card E → E ≤ Subgroup.centralizer {α} → α * α = 1 →
      α ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ ∀ x, β x = x → α x = x

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional in
theorem ggOuterInv_twE6Marking
    (f : ℕ) (hf : 1 ≤ f)
    (hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f)
    (π : twistedE6Group 2 f →* ↥(twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)))
    (hπ : Function.Surjective π) (hπker : π.ker = Subgroup.center (twistedE6Group 2 f))
    (hπvalT : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    {G : Type} [Group G] (ψ : twistedE6Group 2 f →* G)
    (hker' : ψ.ker = Subgroup.center (twistedE6Group 2 f)) {c : G}
    (hdiag : GGPsiInnerDiag (twistedE6Datum 2 f) ψ c) :
    ∃ φ ∈ twistedE6Inn (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) ⊔
        twistedE6Diag (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f),
      ∀ u u', c * ψ u * c⁻¹ = ψ u' → φ (π u) = π u' := by
  obtain ⟨_, ⟨w, rfl⟩, b, hbc, hb⟩ := InnerDiagTwE6.twE6DiagInput_of_rankOne hf
    (InnerDiagTwE6.twE6RankOneInput_holds f hf) G ψ hker'.le c hdiag
  obtain ⟨v, hv⟩ := exists_compatDiag_eq (t := TwistTag.E6)
    (σ := (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom) (b := b)
    (by rw [hσθ]; exact hbc)
  set Δ := compatDiagAutHom TwistTag.E6 (GaloisField 2 (2 * f))
    (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom v with hΔdef
  have key := ggOuterInv_marking_of_closure ψ π hπ (hπker.trans hker'.symm)
    (InnerDiagTwE6.closure_fundamental_eq_top (frobQ 2 f) (frobQ_frobQ 2 f hf)) (c * ψ w) Δ (by
      rintro z ⟨j, γ, hγ, hz⟩
      obtain ⟨z', h1, h2⟩ := hb j γ hγ z hz
      refine ⟨z', h1, Subtype.ext ?_⟩
      rw [hΔdef, coe_compatDiagAutHom, hv, hπvalT, hπvalT, h2])
  refine ⟨Δ⁻¹ * MulAut.conj (π w)⁻¹,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right ⟨v, rfl⟩))
      (Subgroup.mem_sup_left ⟨_, rfl⟩), fun u u' hcu => ?_⟩
  have h1 := key u' (w⁻¹ * u * w) (by
    rw [map_mul, map_mul, map_inv, ← hcu]
    group)
  have e : ∀ y, Δ (Δ⁻¹ y) = y := fun y => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [MulAut.mul_apply]
  apply Δ.injective
  rw [e, h1, MulAut.conj_apply]
  simp only [map_mul, map_inv, inv_inv]

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional in
theorem ggOuterInvModelDataAt_twistedE6_of
    (hD3 : TwistedE6GraphNone) :
    GGOuterInvModelDataAt .twistedE6 := by
  intro n f hadm _
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, hexp, -⟩, -, hder, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  have hH : ⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
      twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆ =
      twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) := by
    rw [← hσθ]
    exact hder
  let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 f hf)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 f hf)
  have hπvalT : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  have hπker : π.ker = Subgroup.center (twistedE6Group 2 f) :=
    AutSt.ker_eq_center_of_surjective π hπ hZ (RootDetectTwE6.ker_le_center f π hπvalT)
  refine ⟨twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f), inferInstance, π,
    twistedE6Inn _ _ ⊔ twistedE6Diag _ _, hπ, hπker, le_sup_left, ?_, ?_, ?_⟩
  · exact AutSt.odd_card_of_pow_three hexp
  · intro G _ ψ hker' c _ hdiag
    exact ggOuterInv_twE6Marking f hf hσθ π hπ hπker hπvalT ψ hker' hdiag
  · intro p β α E hp hp2 hβ1 hβE hEI hEab hEcard hEα hα2 hαI _
    exact hD3 f _ hf hK _ hσ p α β E hp hp2 hβ1 hβE hEI hEab hEcard hEα hα2 hαI

theorem ggOuterInvAt_twistedE6_of
    (h2 : GGO2CentralizerG0At .twistedE6)
    (hD3 : TwistedE6GraphNone) : GGOuterInvAt .twistedE6 :=
  ggOuterInvAt_of_modelData ggSteinbergCorrectionAt_twistedE6 h2
    (ggOuterInvModelDataAt_twistedE6_of hD3)

end CFSG.StandardType
