module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6Core
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6Root
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6Torus
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RootDetectTwE6

section Field


theorem exists_frobQ_ne (f : ℕ) (hf : 1 ≤ f) :
    ∃ b : GaloisField 2 (2 * f), frobQ 2 f b ≠ b := by
  classical
  have : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
  have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hcard : Fintype.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hlt : (Polynomial.X ^ 2 ^ f - Polynomial.X :
      Polynomial (GaloisField 2 (2 * f))).natDegree < Cardinal.mk (GaloisField 2 (2 * f)) := by
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ h1, Cardinal.mk_fintype, Nat.cast_lt, hcard]
    nlinarith
  obtain ⟨b, hb⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _
    (FiniteField.X_pow_card_sub_X_ne_zero _ h1) hlt
  refine ⟨b, fun h => hb ?_⟩
  rw [frobQ_apply] at h
  simp [h]

theorem map_frobQ (f : ℕ) (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f))
    (x : GaloisField 2 (2 * f)) : δ (frobQ 2 f x) = frobQ 2 f (δ x) := by
  rw [frobQ_apply, frobQ_apply, map_pow]

end Field

section Isogeny

variable (f : ℕ) {C : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))}
  (π : twistedE6Group 2 f →* C)

theorem mem_ker_e6IsogenyT_of_mem_ker
    (hπval : ∀ z, ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    {x : twistedE6Group 2 f} (hx : x ∈ π.ker) :
    (x : e6Data_valid.minGroup (GaloisField 2 (2 * f))) ∈
      (e6IsogenyT (GaloisField 2 (2 * f))).ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  apply Subtype.ext
  have h3 := congrArg (fun y : C => (y : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) hx
  simp only [hπval, OneMemClass.coe_one] at h3
  exact h3

theorem ker_le_center
    (hπval : ∀ z, ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) :
    π.ker ≤ Subgroup.center (twistedE6Group 2 f) := by
  intro x hx
  have hc := ker_e6IsogenyT_le_center (GaloisField 2 (2 * f))
    (mem_ker_e6IsogenyT_of_mem_ker f π hπval hx)
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  exact Subtype.ext (hc y)

theorem odd_card_ker
    (hπval : ∀ z, ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) :
    Odd (Nat.card π.ker) := by
  have hle : π.ker.map (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype ≤
      (e6IsogenyT (GaloisField 2 (2 * f))).ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_ker_e6IsogenyT_of_mem_ker f π hπval hx
  have hdvd : Nat.card π.ker ∣ Nat.card (e6IsogenyT (GaloisField 2 (2 * f))).ker := by
    rw [← Subgroup.card_subtype]
    exact Subgroup.card_dvd_of_le hle
  have h := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker
    (GaloisField 2 (2 * f)) (p := 2)
  have hodd : Odd (Nat.card (e6IsogenyT (GaloisField 2 (2 * f))).ker) :=
    Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
  exact hodd.of_dvd_nat hdvd

theorem twistedRootGroup_mul_self :
    ∀ β ∈ (twistedE6Datum 2 f).roots, ∀ z ∈ (twistedE6Datum 2 f).rootGroup β, z * z = 1 := by
  intro β hβ z hz
  have hβ' : IsRoot .F4 β := isRoot_of_mem_twistedDatum_roots (frobQ 2 f) hβ
  obtain ⟨hα, hp⟩ := liftRoot_spec hβ'
  have hz' := (mem_twistedRootGroup_iff (frobQ 2 f) hα hp z).mp hz
  have hsq : ∀ (γ : Fin (Tag.rank .E6) → ℤ) (c : GaloisField 2 (2 * f)),
      e6Data_valid.xm (GaloisField 2 (2 * f)) γ c * e6Data_valid.xm (GaloisField 2 (2 * f)) γ c =
        1 := by
    intro γ c
    rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, OneMemClass.coe_one]
  by_cases hfix : rho (liftRoot β) = liftRoot β
  · rw [hfix, sup_idem] at hz'
    obtain ⟨c, hc⟩ := (e6Data_valid.mem_rootGroup _).mp hz'
    rw [← hc, hsq]
  · obtain ⟨c, d, hcd⟩ := (mem_sup_rootGroup_of_commute (commute_xm_rho hα hfix)).mp hz'
    rw [hcd]
    calc e6Data_valid.xm _ (liftRoot β) c * e6Data_valid.xm _ (rho (liftRoot β)) d *
          (e6Data_valid.xm _ (liftRoot β) c * e6Data_valid.xm _ (rho (liftRoot β)) d) =
        e6Data_valid.xm _ (liftRoot β) c * (e6Data_valid.xm _ (rho (liftRoot β)) d *
          e6Data_valid.xm _ (liftRoot β) c) * e6Data_valid.xm _ (rho (liftRoot β)) d := by group
      _ = e6Data_valid.xm _ (liftRoot β) c * (e6Data_valid.xm _ (liftRoot β) c *
          e6Data_valid.xm _ (rho (liftRoot β)) d) * e6Data_valid.xm _ (rho (liftRoot β)) d := by
        rw [(commute_xm_rho hα hfix c d).eq]
      _ = 1 := by
        rw [← mul_assoc, hsq, one_mul, hsq]

end Isogeny

section Field

variable (f : ℕ) {C : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))}
  (π : twistedE6Group 2 f →* C)

theorem hfield_twisted (hf : 1 ≤ f)
    (hπval : ∀ z, ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))))
    {p : ℕ} (hp : Odd p) {γ : Fin (twistedE6Datum 2 f).rank → ℤ}
    (hγ : γ ∈ (twistedE6Datum 2 f).roots) (N : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
    (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)) (hδp : δ ^ p = 1)
    (h : ∀ z ∈ (twistedE6Datum 2 f).rootGroup γ,
      N * Units.map (entrywiseHom δ.toRingHom)
        ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * N⁻¹ =
          ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) :
    δ = 1 := by
  set K := GaloisField 2 (2 * f)
  have hθ : ∀ c, frobQ 2 f (frobQ 2 f c) = c := frobQ_frobQ 2 f hf
  have hcomm : ∀ x, δ (frobQ 2 f x) = frobQ 2 f (δ x) := map_frobQ f δ
  have hγ' : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots (frobQ 2 f) hγ
  obtain ⟨hα, hpr⟩ := liftRoot_spec hγ'
  set α₀ := liftRoot γ with hα₀
  set s₁ : K := (relSignOr (rootOperatorFamily .E6) e6AdjData_valid α₀ : K) with hs₁
  have hs₁0 : s₁ ≠ 0 := by
    intro h0
    have := relSignOr_mul_self (k := K) (F := rootOperatorFamily .E6) (hD := e6AdjData_valid) α₀
    rw [← hs₁, h0, zero_mul] at this
    exact zero_ne_one this
  have hδs₁ : δ s₁ = s₁ := map_intCast δ _
  by_cases hfix : rho α₀ = α₀
  ·
    refine eq_one_of_conj_fixed (rootOperatorFamily .E6) (frobQ 2 f) hθ ⟨α₀, hα⟩ hs₁0 hδs₁ hcomm
      hp hδp N fun c hc => ?_
    have hz := h (xFixed (frobQ 2 f) hα hfix c hc)
      (by rw [← hpr]; exact xFixed_mem (frobQ 2 f) hα hfix c hc)
    rw [hπval, xFixed_val, e6Isogeny_xm K hα, yPar, xPar_of_isRoot hα,
      RootOperatorFamily.coe_eltElement] at hz
    exact hz
  ·
    set s₂ : K := (relSignOr (rootOperatorFamily .E6) e6AdjData_valid (rho α₀) : K) *
      (twistSign α₀ : K) with hs₂
    have hδs₂ : δ s₂ = s₂ := by rw [hs₂, map_mul, map_intCast, map_intCast]
    have hht : ht (rho α₀) = ht α₀ := by rw [← ht_proj, proj_rho, ht_proj]
    have h0 : ht α₀ ≠ 0 := hα.height_ne_zero
    set ε : ℤ := if 0 < ht α₀ then 1 else -1 with hε
    let φ : (Fin (Tag.rank .E6) → ℤ) →+ ℤ := AddMonoidHom.mk' (fun v => ε * ht v) fun u v => by
      simp only [ht, Pi.add_apply, Finset.sum_add_distrib]
      ring
    have hφα : 1 ≤ φ α₀ := by
      change 1 ≤ ε * ht α₀
      rw [hε]
      split_ifs with hpos <;> omega
    have hφβ : φ α₀ ≤ φ (rho α₀) := by
      change ε * ht α₀ ≤ ε * ht (rho α₀)
      rw [hht]
    refine eq_one_of_conj_pair (rootOperatorFamily .E6) (frobQ 2 f) hθ (exists_frobQ_ne f hf)
      ⟨α₀, hα⟩ ⟨rho α₀, isRoot_rho hα⟩ hfix φ hφα hφβ hs₁0 hδs₁ hδs₂ hcomm hp hδp N
      fun c => ?_
    have hval : ((π (xPair (frobQ 2 f) hθ hα hfix c) : C) : ModGL TwistTag.E6.tag K) =
        (rootOperatorFamily .E6).eltUnit K ⟨α₀, hα⟩ (s₁ * c) *
          (rootOperatorFamily .E6).eltUnit K ⟨rho α₀, isRoot_rho hα⟩ (s₂ * frobQ 2 f c) := by
      rw [hπval, xPair_val, map_mul, e6Isogeny_xm K hα, e6Isogeny_xm K (isRoot_rho hα), yPar,
        yPar, xPar_of_isRoot hα, xPar_of_isRoot (isRoot_rho hα), Subgroup.coe_mul,
        RootOperatorFamily.coe_eltElement, RootOperatorFamily.coe_eltElement, hs₂, mul_assoc]
    have hz := h (xPair (frobQ 2 f) hθ hα hfix c)
      (by rw [← hpr]; exact xPair_mem (frobQ 2 f) hθ hα hfix c)
    rw [hval] at hz
    exact hz
theorem compatDiag_rho
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom a)ˣ) (i : Fin (Tag.rank .E6)) :
    compatDiag TwistTag.E6 (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom u
        (rhoPerm i) = Units.map (frobQ 2 f : GaloisField 2 (2 * f) →* GaloisField 2 (2 * f))
      (compatDiag TwistTag.E6 (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom u
        i) := by
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [iterateFrobeniusEquiv_def, frobQ_apply]
  rw [show rhoPerm i = TwistTag.E6.perm i from rfl, compatDiag_perm u i]
  exact congrArg (fun φ : GaloisField 2 (2 * f) →+* GaloisField 2 (2 * f) =>
    Units.map (φ : GaloisField 2 (2 * f) →* GaloisField 2 (2 * f))
      (compatDiag TwistTag.E6 (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom u i))
    hσθ
theorem hform_twisted (hf : 1 ≤ f)
    (π₀ : twistedE6Group 2 f →* twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))
    (hπval : ∀ z, ((π₀ z : twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))))
    {p : ℕ} :
    ∀ β : MulAut (twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)), β ^ p = 1 →
      ∃ (g : twistedE6RootGroup (GaloisField 2 (2 * f))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))
        (d : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
        (σ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)), σ ^ p = 1 ∧
        (∀ δ ∈ (twistedE6Datum 2 f).roots, ∃ h ∈ ggTorus (twistedE6Datum 2 f),
          ∀ z ∈ (twistedE6Datum 2 f).rootGroup δ,
            ((π₀ (h * z * h⁻¹) : twistedE6RootGroup (GaloisField 2 (2 * f))
              (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
                ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
              d * ((π₀ z : twistedE6RootGroup (GaloisField 2 (2 * f))
                (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
                  ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * d⁻¹) ∧
        ∀ h : twistedE6RootGroup (GaloisField 2 (2 * f))
            (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f),
          (β h : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
            (g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * d *
              Units.map (entrywiseHom σ.toRingHom)
                (h : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * d⁻¹ *
                  (g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹ := by
  intro β hβ
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  obtain ⟨-, -, -, -, -, hΔ, hδ0, hnf, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  obtain ⟨g, u, δ, hgu⟩ := hnf β
  have hδp : δ ^ p = 1 := by
    rw [← hΘ β g u δ hgu, ← map_pow, hβ, map_one]
  refine ⟨g, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6
    (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom u), δ, hδp, ?_, ?_⟩
  · intro β' hβ'
    obtain ⟨h, hh, hz⟩ := hdiag_twisted (frobQ 2 f) (frobQ_frobQ 2 f hf) _
      (compatDiag_rho f u) β' hβ'
    exact ⟨h, hh, fun z hzm => by rw [hπval, hπval]; exact hz z hzm⟩
  · intro h
    rw [hgu]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hΔ, hδ0]
    group

end Field
end RootDetectTwE6

section Family

theorem ggRootDetect_twistedE6 : GGRootDetect .twistedE6 := by
  intro G _ _ n f ψ hadm _ hker p hp hp2 _ c hc hcp γ hγ u hT
  obtain ⟨-, hf, -⟩ := hadm
  have hoddp : Odd p := hp.odd_of_ne_two hp2
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
  have : Finite (twistedE6Group 2 f) := by
    have : Finite (Module.End (GaloisField 2 (2 * f)) (Fin e6Data.d →₀ GaloisField 2 (2 * f))) :=
      Module.finite_of_finite (GaloisField 2 (2 * f))
    infer_instance
  have hperf : ⁅(⊤ : Subgroup (twistedE6Group 2 f)), (⊤ : Subgroup (twistedE6Group 2 f))⁆ = ⊤ :=
    (fixedGroup_isPerfect_of_four_le_card (frobQ 2 f) (frobQ_frobQ 2 f hf)
      (four_le_card_galoisField 2 f hf)).commutator_eq_top
  exact RootDetectTwE6.ggPsiInnerDiag_of_isogeny_semilinear (twistedE6Datum 2 f) hperf
    (twistedE6RootGroup (GaloisField 2 (2 * f)) (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f))
    hZ hπ (RootDetectTwE6.ker_le_center f π hπvalT) (RootDetectTwE6.odd_card_ker f π hπvalT)
    (RootDetectTwE6.twistedRootGroup_mul_self f) (RootDetectTwE6.hform_twisted f hf π hπval)
    (fun N δ hδp h => RootDetectTwE6.hfield_twisted f π hf hπval hoddp hγ N δ hδp h)
    hker hc hcp hT

end Family

end CFSG.StandardType
