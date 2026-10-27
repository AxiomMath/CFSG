module

public import CFSG.LieType.Ree.LargeReeInvolutionIntermediateOddCore
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.Sporadic.Schreier.TitsModelExcl

public noncomputable section

namespace CFSG.Sporadic.Schreier.LargeReeExcl

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier.Tits

@[expose] def fittingConj {X Γ : Type*} [Group X] [Group Γ]
    (θ : GeneralizedFitting.subgroup X ≃* Γ) : X →* MulAut Γ :=
  haveI := GeneralizedFitting.normal X
  (MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal

theorem fittingConj_apply {X Γ : Type*} [Group X] [Group Γ]
    (θ : GeneralizedFitting.subgroup X ≃* Γ) (x : X) (y : GeneralizedFitting.subgroup X) :
    ((θ.symm (fittingConj θ x (θ y)) : GeneralizedFitting.subgroup X) : X) = x * y * x⁻¹ := by
  simp [fittingConj, MulAut.congr]

theorem fittingConj_injective {X Γ : Type*} [Group X] [Finite X] [Group Γ]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* Γ) : Function.Injective (fittingConj θ) := by
  have hcenter : Subgroup.center (GeneralizedFitting.subgroup X) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (GeneralizedFitting.subgroup X))
      with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  rw [injective_iff_map_eq_one]
  intro x hx
  have hconj : ∀ y ∈ GeneralizedFitting.subgroup X, x * y * x⁻¹ = y := by
    intro y hy
    have := fittingConj_apply θ x ⟨y, hy⟩
    rw [hx, MulAut.one_apply, MulEquiv.symm_apply_apply] at this
    exact this.symm
  have hxC : x ∈ Subgroup.centralizer (GeneralizedFitting.subgroup X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    calc y * x = x * y * x⁻¹ * x := by rw [hconj y hy]
      _ = x * y := by group
  have hxF := GeneralizedFitting.centralizer_le X hxC
  have hz : (⟨x, hxF⟩ : GeneralizedFitting.subgroup X) ∈
      Subgroup.center (GeneralizedFitting.subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxC) y y.2)
  rw [hcenter, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem map_fittingConj {X Γ : Type*} [Group X] [Group Γ]
    (θ : GeneralizedFitting.subgroup X ≃* Γ) :
    (GeneralizedFitting.subgroup X).map (fittingConj θ) =
      (MulAut.conj : Γ →* MulAut Γ).range := by
  ext φ
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨θ ⟨y, hy⟩, MulEquiv.ext fun d => ?_⟩
    apply θ.symm.injective
    apply Subtype.ext
    rw [← θ.apply_symm_apply d, fittingConj_apply]
    simp
  · rintro ⟨d, rfl⟩
    refine ⟨θ.symm d, (θ.symm d).2, MulEquiv.ext fun d' => ?_⟩
    apply θ.symm.injective
    apply Subtype.ext
    rw [← θ.apply_symm_apply d', fittingConj_apply]
    simp

theorem noOddNormal_of_oddCore_eq_bot {G : Type*} [Group G] (h : CFSG.oddCore G = ⊥) :
    Tits.NoOddNormal G :=
  fun _ hR hodd => eq_bot_iff.2 (h ▸ le_sSup ⟨hR, hodd⟩)

theorem involution_of_intermediate {X Γ : Type*} [Group X] [Finite X] [Group Γ]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* Γ)
    (hΓ : ∀ Y : Subgroup (MulAut Γ), (MulAut.conj : Γ →* MulAut Γ).range ≤ Y →
      ∀ u ∈ Y, orderOf u = 2 →
        u ∈ (MulAut.conj : Γ →* MulAut Γ).range ∧ CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {u}) = ⊥)
    (u : X) (hu : orderOf u = 2) :
    u ∈ GeneralizedFitting.subgroup X ∧ Tits.NoOddNormal ↥(Subgroup.centralizer {u}) := by
  set ρ := fittingConj θ
  have hinj := fittingConj_injective hsimple hnab θ
  have hρu : orderOf (ρ u) = 2 := by rw [orderOf_injective ρ hinj u, hu]
  have hY : (MulAut.conj : Γ →* MulAut Γ).range ≤ ρ.range := by
    rw [← map_fittingConj θ]
    exact Subgroup.map_le_range _ _
  obtain ⟨hinner, hodd⟩ := hΓ ρ.range hY (ρ u) ⟨u, rfl⟩ hρu
  have huF : u ∈ GeneralizedFitting.subgroup X := by
    rw [← map_fittingConj θ] at hinner
    obtain ⟨y, hy, e⟩ := hinner
    rwa [← hinj e]
  have e : Subgroup.centralizer {u} ≃* ↥(ρ.range ⊓ Subgroup.centralizer {ρ u}) :=
    ((Subgroup.centralizer {u}).equivMapOfInjective ρ hinj).trans
      (MulEquiv.subgroupCongr (map_centralizer_of_injective ρ hinj u))
  exact ⟨huF, Tits.NoOddNormal.of_equiv e (noOddNormal_of_oddCore_eq_bot hodd)⟩

theorem CTUC_large_Ree_model_almost_simple_full_involution_centralizer_exclusion
    (X : Type)
    [Group X] [Finite X] (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) (p f : ℕ)
    (hmodel : ReeTitsModel (GeneralizedFitting.subgroup X) .twistedF4 p f) :
    p = 2 ∧ (∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1) ∧
    (∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], f = 2 * m + 1 →
      Nat.card K = p ^ f →
      Nonempty (GeneralizedFitting.subgroup X ≃* DerivedCentralQuotient (reeFixedGroup .F4 K
        reeF4Perm fun i => if i ∈ reeF4Long then p ^ m else p ^ (m + 1))) →
      Nonempty (GeneralizedFitting.subgroup X ≃* F4.reeGamma K m) ∧
      ∀ θ : GeneralizedFitting.subgroup X ≃* F4.reeGamma K m,
        (∀ (x : X) (y : GeneralizedFitting.subgroup X),
          ((θ.symm (fittingConj θ x (θ y)) : GeneralizedFitting.subgroup X) : X) =
            x * y * x⁻¹) ∧
        Function.Injective (fittingConj θ) ∧
        (GeneralizedFitting.subgroup X).map (fittingConj θ) =
          (MulAut.conj : F4.reeGamma K m →* MulAut (F4.reeGamma K m)).range) ∧
    (∀ u : X, orderOf u = 2 → u ∈ GeneralizedFitting.subgroup X ∧
      CFSG.oddCore ↥(Subgroup.centralizer {u}) = ⊥ ∧
      CFSG.piCore {q : Nat.Primes | q.val ≠ 2} ↥(Subgroup.centralizer {u}) = ⊥) ∧
    ¬ ∃ u : X, orderOf u = 2 ∧ CFSG.oddCore ↥(Subgroup.centralizer ({u} : Set X)) ≠ ⊥ := by
  obtain ⟨-, -, -, hp, ⟨m₀, hm₀, hfm₀⟩, hiso⟩ := large_Ree_model_Schreier _ p f hmodel
  subst hp
  have hall : ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime], f = 2 * m + 1 →
      Nat.card K = 2 ^ f →
      Nonempty (GeneralizedFitting.subgroup X ≃* DerivedCentralQuotient (reeFixedGroup .F4 K
        reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ m else 2 ^ (m + 1))) →
      Nonempty (GeneralizedFitting.subgroup X ≃* F4.reeGamma K m) ∧
      ∀ θ : GeneralizedFitting.subgroup X ≃* F4.reeGamma K m,
        (∀ (x : X) (y : GeneralizedFitting.subgroup X),
          ((θ.symm (fittingConj θ x (θ y)) : GeneralizedFitting.subgroup X) : X) =
            x * y * x⁻¹) ∧
        Function.Injective (fittingConj θ) ∧
        (GeneralizedFitting.subgroup X).map (fittingConj θ) =
          (MulAut.conj : F4.reeGamma K m →* MulAut (F4.reeGamma K m)).range :=
    fun m K _ _ _ hfm hK hw => ⟨hiso m K hfm hK hw, fun θ =>
      ⟨fittingConj_apply θ, fittingConj_injective hsimple hnab θ, map_fittingConj θ⟩⟩
  obtain ⟨-, a, hfa, K, _, _, hK, hw⟩ := hmodel
  have ha : a = m₀ := by omega
  subst ha
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K F4.prime := hc
  obtain ⟨θ⟩ := hiso a K hfa hK hw
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hΓ := (LargeReeInvolution.large_Ree_all_intermediate_involution_centralizers_odd_core_free
    a hm₀ K hK').1
  have key : ∀ u : X, orderOf u = 2 → u ∈ GeneralizedFitting.subgroup X ∧
      CFSG.oddCore ↥(Subgroup.centralizer {u}) = ⊥ ∧
      CFSG.piCore {q : Nat.Primes | q.val ≠ 2} ↥(Subgroup.centralizer {u}) = ⊥ := by
    intro u hu
    obtain ⟨huF, hno⟩ := involution_of_intermediate hsimple hnab θ
      (fun Y hY v hv hv2 => ⟨(hΓ Y hY v hv hv2).1, (hΓ Y hY v hv hv2).2.1⟩) u hu
    exact ⟨huF, Tits.NoOddNormal.oddCore_eq_bot hno, Tits.NoOddNormal.piCore_eq_bot hno⟩
  refine ⟨rfl, ⟨a, hm₀, hfa⟩, hall, key, ?_⟩
  rintro ⟨u, hu, hne⟩
  exact hne (key u hu).2.1

theorem CTU_catalog_large_Ree_Tits_check
    (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (f : ℕ) (ht : t = .twistedF4 ∨ t = .Tits)
    (hmodel : ReeTitsModel (GeneralizedFitting.subgroup X) t 2 f) :
    ¬ ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) ≠ ⊥ := by
  rcases ht with rfl | rfl
  · exact (CTUC_large_Ree_model_almost_simple_full_involution_centralizer_exclusion X hsimple
      hnab 2 f hmodel).2.2.2.2
  · have hf1 : f = 1 := hmodel.1.2.2.2.2
    subst hf1
    exact (CTUC_Tits_model_almost_simple_full_involution_centralizer_exclusion X hsimple hnab
      hmodel).2.2.2

end CFSG.Sporadic.Schreier.LargeReeExcl
