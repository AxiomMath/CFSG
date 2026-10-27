module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6TwistedGood

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace AutSt

section Fixed

theorem xm_three_mem_fixedGroup (f : ℕ) :
    e6Data_valid.xm (GaloisField 2 (2 * f)) (Pi.single (e6Node 3) 1) 1 *
        e6Data_valid.xm (GaloisField 2 (2 * f)) (-Pi.single (e6Node 3) 1) 1 ∈
      fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f) := by
  rw [mem_fixedGroup, map_mul, sigma_xm_single, sigma_xm_neg_single, map_one,
    show rhoPerm (e6Node 3) = e6Node 3 by decide]

end Fixed

theorem exists_conj_of_conj_on {U C : Type*} [Group U] [Group C] (π : U →* C) (Δ : MulAut C)
    {u z h : U} (hΔz : Δ (π z) = π (h * z * h⁻¹)) :
    ∃ k : C, Δ (π (u * z * u⁻¹)) = k * π (u * z * u⁻¹) * k⁻¹ :=
  ⟨Δ (π u) * π h * (π u)⁻¹, by simp only [map_mul, map_inv, hΔz]; group⟩

section Model

variable (f : ℕ) {C : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))}
  (π : twistedE6Group 2 f →* C)

theorem coe_twE6A
    (hπval : ∀ z, ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f)))) :
    ((π ⟨_, xm_three_mem_fixedGroup f⟩ : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((xPar (rootOperatorFamily .E6) (Pi.single (e6Node 3) 1) (1 : GaloisField 2 (2 * f)) *
        xPar (rootOperatorFamily .E6) (-Pi.single (e6Node 3) 1) 1 :
          adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) := by
  rw [hπval]
  change ((e6Isogeny (GaloisField 2 (2 * f))
      (e6Data_valid.xm (GaloisField 2 (2 * f)) (Pi.single (e6Node 3) 1) 1 *
        e6Data_valid.xm (GaloisField 2 (2 * f)) (-Pi.single (e6Node 3) 1) 1) :
      adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) = _
  rw [map_mul, e6Isogeny_xm_single, e6Isogeny_xm_neg_single, xPar_simple, xPar_neg_simple]

theorem exists_conj_of_twDiag (hf : 1 ≤ f)
    (hπval : ∀ z, ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom a)ˣ)
    (Δ : MulAut C)
    (hΔ : ∀ g : C, ((Δ g : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom u) * g *
      (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom u))⁻¹)
    {γ : Fin (twistedE6Datum 2 f).rank → ℤ} (hγ : γ ∈ (twistedE6Datum 2 f).roots)
    (u' z : twistedE6Group 2 f) (hz : z ∈ (twistedE6Datum 2 f).rootGroup γ) :
    ∃ k : C, Δ (π (u' * z * u'⁻¹)) = k * π (u' * z * u'⁻¹) * k⁻¹ := by
  obtain ⟨h, -, hzh⟩ := RootDetectTwE6.hdiag_twisted (frobQ 2 f) (frobQ_frobQ 2 f hf)
    (compatDiag TwistTag.E6 (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom u)
    (RootDetectTwE6.compatDiag_rho f u) γ hγ
  have hΔz : Δ (π z) = π (h * z * h⁻¹) := by
    apply Subtype.ext
    have h1 := hzh z hz
    rw [← hπval, ← hπval] at h1
    rw [hΔ, h1]
    rfl
  exact exists_conj_of_conj_on π Δ hΔz

end Model

section Kernel

theorem ker_eq_center_of_surjective {U C : Type*} [Group U] [Group C] (π : U →* C)
    (hπ : Function.Surjective π) (hZ : Subgroup.center C = ⊥) (hker : π.ker ≤ Subgroup.center U) :
    π.ker = Subgroup.center U := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hc : π z ∈ Subgroup.center C := Subgroup.mem_center_iff.2 fun y => by
    obtain ⟨x, rfl⟩ := hπ y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
  rw [hZ] at hc
  exact hc

end Kernel

section Main

variable (f : ℕ)

theorem autModel_twistedE6 (hf : 1 ≤ f)
    (π : twistedE6Group 2 f →* twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))
    (hπval : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f)))) :
    GGAutModel (twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))
      (GGModelRoot (twistedE6Datum 2 f) .twistedE6 π) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have : Finite (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := finite_modGL
  obtain ⟨-, -, -, -, -, hΔ, -, hnf, ⟨Θ, hΘ, -, hker, -, hexp, hinv⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  have hΘF : ∀ δ, Θ (fieldActor (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) δ) = δ :=
    fun δ => hΘ _ 1 1 δ (by rw [map_one, map_one, one_mul, one_mul])
  have hInn : (MulAut.conj : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) →* MulAut _).range ≤ Θ.ker := by
    rw [hker]
    exact le_sup_left
  refine autModel_of_hom Θ (fieldActorHom (t := TwistTag.E6)
    (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)).range hInn ?_
    (fun α => ⟨_, ⟨Θ α, rfl⟩, hΘF (Θ α)⟩) ?_ ?_
  · rw [hker]
    have h := odd_card_of_pow_three hexp
    exact h
  · rintro _ ⟨δ, rfl⟩ h1
    change Θ (fieldActor _ δ) = 1 at h1
    rw [hΘF] at h1
    subst h1
    exact fieldActor_one _
  · rintro r hr _ ⟨δ, rfl⟩ hc2 hc1 e he
    change fieldActor _ δ ^ 2 = 1 at hc2
    change fieldActor _ δ ≠ 1 at hc1
    change GGGoodAut r (e * fieldActor _ δ * e⁻¹)
    obtain rfl : δ = iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f := by
      rcases hinv _ hc2 with hI | ⟨h, -⟩
      · exfalso
        have h1 := hInn hI
        rw [MonoidHom.mem_ker, hΘF] at h1
        subst h1
        exact hc1 (fieldActor_one _)
      · rwa [hΘF] at h
    obtain ⟨g, s, hs, hgr⟩ := exists_conj_twTop_of_modelRoot f π hf hπval hr
    have hs' : iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f s = s := by
      rw [hσ, ← frobQ_apply]
      exact hs
    have h0 := goodAut_twGraph hf hK _ hσ g hs' hgr _ (coe_twE6A f π hπval)
    obtain ⟨g', u, δ', hgu⟩ := hnf e
    obtain rfl : δ' = 1 := by
      rw [← hΘ e g' u δ' hgu]
      exact he
    rw [fieldActor_one, mul_one] at hgu
    obtain ⟨-, γ, ⟨hγ, -⟩, u', z, hz, rfl⟩ := hr
    obtain ⟨k, hk⟩ := exists_conj_of_twDiag f π hf hπval u _ (hΔ u) hγ u' z hz
    refine h0.conj e ⟨g' * k, ?_⟩
    rw [hgu, MulAut.mul_apply, MulAut.conj_apply, hk]
    group

end Main

end AutSt

section Family

theorem ggAutModelAt_twistedE6 : GGAutModelAt .twistedE6 := by
  intro n f hadm _ _
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, hZ, -⟩ :=
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
  have hπval : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  have hπvalT : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  exact ⟨twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f), inferInstance, π, hπ,
    AutSt.ker_eq_center_of_surjective π hπ hZ (RootDetectTwE6.ker_le_center f π hπvalT),
    AutSt.autModel_twistedE6 f hf π hπval⟩

end Family

end CFSG.StandardType
