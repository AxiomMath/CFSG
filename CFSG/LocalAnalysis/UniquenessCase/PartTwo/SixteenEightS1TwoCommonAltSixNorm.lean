module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Quasithin.Background.B1MoreSevenB
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenHeartNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (altAct altAct_mul altAct_one altAct_inv_apply altAct_apply_inv)
open CFSG.RankThree.PartTwo.Sec19.SolEven (normalizerIsSym_six altAct_eq_iff)
open Equiv Equiv.Perm

private noncomputable def s16e_twoAN_altActEquiv {n : ℕ} (σ : Perm (Fin n)) :
    altHeart n ≃+ altHeart n where
  toFun := altAct σ
  invFun := altAct σ⁻¹
  left_inv v := altAct_inv_apply σ v
  right_inv v := altAct_apply_inv σ v
  map_add' v w := map_add (altAct σ) v w

private noncomputable def s16e_twoAN_coordAut {W : Type} [CommGroup W] {J : Subgroup W}
    (ψ : ↥J ≃* Multiplicative (altHeart 6)) (σ : Perm (Fin 6)) : MulAut ↥J :=
  ψ.trans ((AddEquiv.toMultiplicative (s16e_twoAN_altActEquiv σ)).trans ψ.symm)

private theorem s16e_twoAN_coordAut_apply {W : Type} [CommGroup W] {J : Subgroup W}
    (ψ : ↥J ≃* Multiplicative (altHeart 6)) (σ : Perm (Fin 6)) (u : ↥J) :
    ψ (s16e_twoAN_coordAut ψ σ u) =
      Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd (ψ u))) := by
  simp [s16e_twoAN_coordAut, s16e_twoAN_altActEquiv]

private noncomputable def s16e_twoAN_coordHom {W : Type} [CommGroup W] {J : Subgroup W}
    (ψ : ↥J ≃* Multiplicative (altHeart 6)) : Perm (Fin 6) →* MulAut ↥J where
  toFun := s16e_twoAN_coordAut ψ
  map_one' := by
    refine MulEquiv.ext fun u => ?_
    apply ψ.injective
    simp only [s16e_twoAN_coordAut_apply, MulAut.one_apply, altAct_one, ofAdd_toAdd]
  map_mul' σ τ := by
    refine MulEquiv.ext fun u => ?_
    apply ψ.injective
    simp only [s16e_twoAN_coordAut_apply, MulAut.mul_apply, toAdd_ofAdd, altAct_mul]

private theorem s16e_twoAN_coordHom_apply {W : Type} [CommGroup W] {J : Subgroup W}
    (ψ : ↥J ≃* Multiplicative (altHeart 6)) (σ : Perm (Fin 6)) (u : ↥J) :
    ψ (s16e_twoAN_coordHom ψ σ u) =
      Multiplicative.ofAdd (altAct σ (Multiplicative.toAdd (ψ u))) :=
  s16e_twoAN_coordAut_apply ψ σ u

private noncomputable def s16e_twoAN_gW {W : Type} [CommGroup W] {J : Subgroup W}
    (ψ : ↥J ≃* Multiplicative (altHeart 6)) (g : MulAut ↥J) : altHeart 6 ≃+ altHeart 6 :=
  AddEquiv.toMultiplicative.symm (ψ.symm.trans (g.trans ψ))

private theorem s16e_twoAN_gW_apply {W : Type} [CommGroup W] {J : Subgroup W}
    (ψ : ↥J ≃* Multiplicative (altHeart 6)) (g : MulAut ↥J) (w : altHeart 6) :
    s16e_twoAN_gW ψ g w =
      Multiplicative.toAdd (ψ (g (ψ.symm (Multiplicative.ofAdd w)))) := rfl

theorem s16e_two_alt6_normalizer_isSym {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {J : Subgroup W} (h : AlternatingNatural H J ⊥ 6) :
    IsSym ↥(normalizer (autSub H J : Set (MulAut ↥J))) 6 := by
  obtain ⟨π, ψ, hπ, hψ⟩ := s16c167_altNatural_equiv (n := 6) (by norm_num) h
  obtain ⟨π₀, hReal⟩ := h
  obtain ⟨-, -, -, hJinv, -, -, -, -⟩ := hReal
  let θH : Perm (Fin 6) →* MulAut ↥J := s16e_twoAN_coordHom ψ
  let θA : alternatingGroup (Fin 6) →* MulAut ↥J :=
    θH.comp (alternatingGroup (Fin 6)).subtype
  have hAut : autSub H J = θA.range := by
    ext φ
    rw [mem_autSub]
    constructor
    · rintro ⟨g, hgH, hgφ⟩
      obtain ⟨γ, hγ⟩ := hπ ⟨(g : MulAut W), hgH⟩
      refine MonoidHom.mem_range.mpr ⟨γ, ?_⟩
      rw [← hgφ]
      refine MulEquiv.ext fun u => ?_
      apply ψ.injective
      change ψ (s16e_twoAN_coordHom ψ (γ : Perm (Fin 6)) u) = ψ (resHom J g u)
      rw [s16e_twoAN_coordHom_apply]
      have hγval : ((π γ : ↥H) : MulAut W) = (g : MulAut W) := by rw [hγ]
      have hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ J := by
        rw [hγval]
        exact (g.2 u).2 u.2
      have heq : (⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ : ↥J) = resHom J g u := by
        apply Subtype.ext
        rw [resHom_apply]
        exact congrArg (fun m : MulAut W => m (u : W)) hγval
      rw [← hψ γ u hu, heq]
    · rintro ⟨γ, hγ⟩
      have hstab : ((π γ : ↥H) : MulAut W) ∈ stabSub J :=
        mem_stabSub_of_invariant (fun u hu => hJinv (π γ) u hu) (fun u hu => by
          have hh := hJinv ((π γ)⁻¹) u hu
          simpa using hh)
      refine mem_autSub.mpr ⟨⟨((π γ : ↥H) : MulAut W), hstab⟩, (π γ).2, ?_⟩
      rw [← hγ]
      refine MulEquiv.ext fun u => ?_
      apply ψ.injective
      change ψ (resHom J ⟨((π γ : ↥H) : MulAut W), hstab⟩ u) =
        ψ (s16e_twoAN_coordHom ψ (γ : Perm (Fin 6)) u)
      rw [s16e_twoAN_coordHom_apply]
      have hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ J := (hstab u).2 u.2
      have heq : (⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ : ↥J) =
          resHom J ⟨((π γ : ↥H) : MulAut W), hstab⟩ u := by
        apply Subtype.ext
        rw [resHom_apply]
      rw [← heq, ← hψ γ u hu]
  have hθHinj : Function.Injective θH := by
    intro σ τ hστ
    refine (altAct_eq_iff (n := 6) (by norm_num)).1 fun v => ?_
    obtain ⟨u, rfl⟩ : ∃ u : ↥J, Multiplicative.toAdd (ψ u) = v :=
      ⟨ψ.symm (Multiplicative.ofAdd v), by simp⟩
    have h := congrArg (fun m : MulAut ↥J => Multiplicative.toAdd (ψ (m u))) hστ
    rw [s16e_twoAN_coordHom_apply, s16e_twoAN_coordHom_apply, toAdd_ofAdd,
      toAdd_ofAdd] at h
    exact h
  have hle : (s16e_twoAN_coordHom ψ).range ≤ normalizer (θA.range) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk l hl
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hk
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hl
    have hmem : σ * (γ : Perm (Fin 6)) * σ⁻¹ ∈ alternatingGroup (Fin 6) :=
      (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ γ.2 σ
    refine MonoidHom.mem_range.mpr ⟨⟨σ * (γ : Perm (Fin 6)) * σ⁻¹, hmem⟩, ?_⟩
    show θH (σ * (γ : Perm (Fin 6)) * σ⁻¹) =
      θH σ * θH (γ : Perm (Fin 6)) * (θH σ)⁻¹
    rw [map_mul θH, map_mul θH, map_inv θH]
  have h4a : ∀ σ : Perm (Fin 6),
      θH σ ∈ normalizer (autSub H J : Set (MulAut ↥J)) := by
    intro σ
    rw [hAut]
    exact hle (MonoidHom.mem_range.mpr ⟨σ, rfl⟩)
  have h4b : ∀ φ : MulAut ↥J,
      φ ∈ normalizer (autSub H J : Set (MulAut ↥J)) → ∃ σ, θH σ = φ := by
    intro φ hφ
    let γφ : altHeart 6 ≃+ altHeart 6 := s16e_twoAN_gW ψ φ
    have hγ : ∀ σ ∈ alternatingGroup (Fin 6), ∃ σ' ∈ alternatingGroup (Fin 6),
        ∀ v, γφ (altAct σ v) = altAct σ' (γφ v) := by
      intro σ hσ
      have hσmem : θH σ ∈ autSub H J := by
        rw [hAut]
        exact MonoidHom.mem_range.mpr ⟨⟨σ, hσ⟩, rfl⟩
      have hconj : φ * θH σ * φ⁻¹ ∈ autSub H J :=
        (Subgroup.mem_normalizer_iff.mp hφ (θH σ)).1 hσmem
      rw [hAut] at hconj
      obtain ⟨γ', hγ'raw⟩ := MonoidHom.mem_range.mp hconj
      have hγ'eq : θH (γ' : Perm (Fin 6)) = φ * θH σ * φ⁻¹ := hγ'raw
      refine ⟨(γ' : Perm (Fin 6)), γ'.2, ?_⟩
      intro v
      obtain ⟨u, rfl⟩ : ∃ u : ↥J, Multiplicative.toAdd (ψ u) = v :=
        ⟨ψ.symm (Multiplicative.ofAdd v), by simp⟩
      calc γφ (altAct σ (Multiplicative.toAdd (ψ u)))
          = γφ (Multiplicative.toAdd (ψ (θH σ u))) := by
              congr 1
              rw [s16e_twoAN_coordHom_apply, toAdd_ofAdd]
        _ = Multiplicative.toAdd (ψ (φ (θH σ u))) := by
              rw [s16e_twoAN_gW_apply]
              simp
        _ = Multiplicative.toAdd (ψ (θH (γ' : Perm (Fin 6)) (φ u))) := by
              rw [hγ'eq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
                MulEquiv.symm_apply_apply]
        _ = altAct (γ' : Perm (Fin 6)) (Multiplicative.toAdd (ψ (φ u))) := by
              rw [s16e_twoAN_coordHom_apply, toAdd_ofAdd]
        _ = altAct (γ' : Perm (Fin 6)) (γφ (Multiplicative.toAdd (ψ u))) := by
              congr 1
              rw [s16e_twoAN_gW_apply]
              simp
    obtain ⟨π', hπ'⟩ := normalizerIsSym_six γφ hγ
    refine ⟨π', ?_⟩
    refine MulEquiv.ext fun u => ?_
    apply ψ.injective
    change ψ (s16e_twoAN_coordHom ψ π' u) = ψ (φ u)
    rw [s16e_twoAN_coordHom_apply]
    have hval : Multiplicative.toAdd (ψ (φ u)) = γφ (Multiplicative.toAdd (ψ u)) := by
      rw [s16e_twoAN_gW_apply]
      simp
    rw [← ofAdd_toAdd (ψ (φ u)), hval, hπ']
  let θN : Perm (Fin 6) →* ↥(normalizer (autSub H J : Set (MulAut ↥J))) :=
    θH.codRestrict _ h4a
  refine ⟨(MulEquiv.ofBijective θN ⟨?_, ?_⟩).symm⟩
  · intro σ τ hστ
    exact hθHinj (congrArg Subtype.val hστ)
  · intro φ
    obtain ⟨σ, hσ⟩ := h4b φ.1 φ.2
    exact ⟨σ, Subtype.ext hσ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
