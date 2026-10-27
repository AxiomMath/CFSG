module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RE8Frame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RE8Surv
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDual
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RConj
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDualFrob
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFive
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4C2

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus Certificates.TcRes
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso GGHasLabel GGInnerDiagOn)

section GlueFive

private theorem tc_odd_of_orderOf_five {f : ℕ} (hc : orderOf ((2 : ZMod 5) ^ f) = 4) :
    f % 2 = 1 := by
  by_contra h
  obtain ⟨k, hk⟩ : ∃ k, f = 2 * k := ⟨f / 2, by omega⟩
  subst hk
  have h1 : ((2 : ZMod 5) ^ (2 * k)) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * k * 2 = 4 * k by ring, pow_mul]
    have h4 : (2 : ZMod 5) ^ 4 = 1 := by decide
    rw [h4, one_pow]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hc] at h2
  omega

private theorem tc_five_dvd_sq_add_one {f : ℕ} (hf : f % 2 = 1) : 5 ∣ 2 ^ f * 2 ^ f + 1 := by
  have h := tc_two_pow_mod_five f
  have hm : 2 ^ f % 5 = 2 ∨ 2 ^ f % 5 = 3 := by
    split_ifs at h <;> omega
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.mul_mod]
  rcases hm with hm | hm <;> rw [hm]

private theorem tc_two_pow_cast_five {f : ℕ} (hf : f % 2 = 1) :
    ∃ r : ℕ, ((r = 2 ∧ f % 4 = 1) ∨ (r = 3 ∧ f % 4 = 3)) ∧
      (((2 ^ f : ℕ)) : ZMod 5) = (r : ZMod 5) := by
  have h := tc_two_pow_mod_five f
  have hcast : (((2 ^ f : ℕ)) : ZMod 5) = ((2 ^ f % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod _ _).symm
  by_cases h1 : f % 4 = 1
  · refine ⟨2, Or.inl ⟨rfl, h1⟩, ?_⟩
    rw [hcast, h]
    simp [h1]
  · have h3 : f % 4 = 3 := by omega
    refine ⟨3, Or.inr ⟨rfl, h3⟩, ?_⟩
    rw [hcast, h]
    simp [h3]

private theorem tc_five_dvd_sq_sub_one (f : ℕ) : 5 ∣ (2 ^ (f * 2)) ^ 2 - 1 := by
  have h := tc_five_dvd_two_pow_sub_one_iff (4 * f)
  have h4 : ((4 * f) % 4 == 0) = true := by simp
  rw [h4] at h
  have h5 : (2 ^ (4 * f) - 1) % 5 = 0 := by simpa using h
  have : (2 ^ (f * 2)) ^ 2 = 2 ^ (4 * f) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [this]
  exact Nat.dvd_of_mod_eq_zero h5

theorem tc_componentOrbitLength_le_two {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hρ2 : ∀ γ, IsRoot τ γ → ρ (ρ γ) = -γ) : componentOrbitLength ρ Ψ ≤ 2 := by
  unfold componentOrbitLength
  apply Nat.sInf_le
  refine ⟨by norm_num, ?_⟩
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    show ρ (ρ δ) ∈ Ψ
    rw [hρ2 δ (hΨ.isRoot δ hδ)]
    exact hΨ.neg_mem δ hδ
  · intro hγ
    refine ⟨-γ, hΨ.neg_mem γ hγ, ?_⟩
    show ρ (ρ (-γ)) = γ
    rw [hρ2 (-γ) (IsRoot.neg (hΨ.isRoot γ hγ)), neg_neg]

private theorem tcrWEnd_sq_neg {τ : Tag} (g : WeylGroup τ)
    (hg : ∀ j : Fin τ.rank, (g * g) • (Pi.single j 1 : Fin τ.rank → ℤ) = -Pi.single j 1)
    (x : Fin τ.rank → ℤ) : tcrWEnd τ g (tcrWEnd τ g x) = -x := by
  let ψ : AddMonoid.End (Fin τ.rank → ℤ) := (tcrWEnd τ g).comp (tcrWEnd τ g)
  have hψ : ∀ y, ψ y = tcrWEnd τ g (tcrWEnd τ g y) := fun y => rfl
  have hj : ∀ j : Fin τ.rank, ψ (Pi.single j 1) = -(Pi.single j 1) := fun j => by
    rw [hψ, tcrWEnd_apply, tcrWEnd_apply, ← mul_smul]
    exact hg j
  rw [← hψ, tch_map_decomp ψ x]
  simp only [hj]
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem tcrWEnd_sq_E8 (x : Fin Tag.E8.rank → ℤ) :
    tcrWEnd Tag.E8 NoOffRest.weylE8W (tcrWEnd Tag.E8 NoOffRest.weylE8W x) = -x :=
  tcrWEnd_sq_neg NoOffRest.weylE8W NoOffRest.weylE8W_sq_single x

theorem tc_dvd_card_of_compFieldSL
    {G : Type} [Group G] {K : Subgroup G} {m ℓ : ℕ} (hℓ : ℓ ∣ (2 ^ m) ^ 2 - 1)
    (h : CFSG.StandardType.GGCompFieldAtSL (2 ^ m) K) : ℓ ∣ Nat.card ↥K :=
  hℓ.trans (ggCompFieldAt_dvd h.toAt)

end GlueFive

section Leaf

theorem false_E8_four_five_of_inputs
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel) (hG6 : GGTCInputG6InnerDiagLang)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E8 f) (hc : orderOf ((2 : ZMod p) ^ f) = 4) (hp : p = 5) :
    False := by
  classical
  subst hp
  have hfodd : f % 2 = 1 := tc_odd_of_orderOf_five hc
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E8 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hJG : J ≤ G₀ := h.j_comp.1.trans inf_le_left
  have hJperf : commutator ↥J = ⊤ := (Assembly.isComponentOf_iff_open.1 h.j_comp).2.2.1
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨K, _, _, _, S₁, fr₁, hq, hDT, hρ, a, i, ha, hap, hspan, h2, hfield⟩ :=
    uframe_dataE8 hR hmod h.b_norm h.inner_E8 h.b_faithful h.b_elem h.b_card
      (tc_five_dvd_sq_add_one hfodd) h.d_le hJG (Assembly.isComponentOf_iff_open.1 h.j_comp)
      ⟨t', m, f', hlt, hm⟩
  have hρ2 : ∀ γ, IsRoot Tag.E8 γ → S₁.ρ (S₁.ρ γ) = -γ := by
    intro γ hγ
    rw [hρ γ hγ, hρ _ (IsRoot.smul hγ _)]
    exact tcrWEnd_sq_E8 γ
  have he : componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) = 2 :=
    le_antisymm (tc_componentOrbitLength_le_two S₁.ρ (isRootComponent_componentRoots i) hρ2) h2
  rw [he] at hfield
  have hpJ : 5 ∣ Nat.card ↥J := by
    obtain ⟨eJ⟩ := fr₁.exists_tcCenterQuotEquiv hJG hJperf
    exact tc_dvd_card_of_compFieldSL (tc_five_dvd_sq_sub_one f) (hfield.of_centerQuotEquiv eJ.symm)
  obtain ⟨P, iJ, x', ix, hP2, hfrob, hJ2, hxP, hx0, hJx, hne, hsplit, hoth⟩ :=
    tc_lang_survivors_E8 hR2 hG6 h hpJ fr₁ hq hDT ⟨_, hρ⟩ a i ha hap hspan h2
  obtain ⟨r, hr, hcast⟩ := tc_two_pow_cast_five hfodd
  rw [hcast] at hfrob
  have hfl : (r = 2 ∧ (f = 1 ∨ (f % 4 = 1 ∧ 5 ≤ f))) ∨ (r = 3 ∧ f % 4 = 3 ∧ 3 ≤ f) := by
    rcases hr with ⟨hr2, h1⟩ | ⟨hr3, h3⟩
    · refine Or.inl ⟨hr2, ?_⟩
      by_cases hf1 : f = 1
      · exact Or.inl hf1
      · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨hr3, h3, by omega⟩
  exact tcC2_of_certificate (tcrWEnd Tag.E8 NoOffRest.weylE8W)
    (tcrWEnd_iform _) (fun γ hγ => IsRoot.smul hγ _) tcrWEnd_sq_E8 S₁.ρ hρ hfl P hP2 hfrob iJ hJ2
    hxP hx0 ix hJx hne hsplit hoth

end Leaf

end CFSG.StandardType.TableCRes

end
