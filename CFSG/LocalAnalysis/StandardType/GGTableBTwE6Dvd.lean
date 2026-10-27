module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DvdCore
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankSix
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RecipeFieldE6

namespace TwE6Dvd


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem isSimpleGroup_recipeR (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    IsSimpleGroup (TwE6Delta.RecipeR K n) ∧
      ∃ a b : TwE6Delta.RecipeR K n, a * b ≠ b * a := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ.toRingHom c = c ^ 2 ^ n := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσdef, iterateFrobeniusEquiv_apply,
      iterateFrobenius_def]
  obtain ⟨hperf, ⟨x, hx, y, hy, hxy⟩, hΓ, -, -⟩ :=
    finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC₀
  have hnc : ∃ a b : C₀, a * b ≠ b * a :=
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have : Group.IsPerfect C₀ := Subgroup.isPerfect_iff.2 hperf
  have : Nontrivial C₀ := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hsimple : IsSimpleGroup C₀ := by
    refine IsSimpleGroup.mk fun M hM => ?_
    by_cases hbot : M = ⊥
    · exact Or.inl hbot
    · right
      have hnot : ¬ M ≤ Subgroup.center C₀ := by
        rw [hZ]
        exact fun h => hbot (le_bot_iff.1 h)
      have hsolv := fixed_noncentral_normal_solvable_quotient TwistTag.E6 K σ M hnot
      by_contra htop
      have : Nontrivial (C₀ ⧸ M) := by
        rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
        exact htop
      exact Group.IsPerfect.not_isSolvable _ hsolv
  obtain ⟨-, T, -, -⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ.toRingHom hσ
  have hZH := TwE6Delta.center_recipeH_eq_bot hn hK
  let e₁ : TwE6Delta.RecipeR K n ≃* TwE6Delta.RecipeH K n :=
    (QuotientGroup.quotientMulEquivOfEq hZH).trans QuotientGroup.quotientBot
  let e : TwE6Delta.RecipeR K n ≃* C₀ := (e₁.trans T.symm).trans (MulEquiv.subgroupCongr hΓ)
  refine ⟨MulEquiv.isSimpleGroup e, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  apply e.symm.injective
  rw [map_mul, map_mul, h]

theorem exists_conj_field (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {τ : MulAut (TwE6Delta.RecipeR K n)} (hτI : τ ∉ TwE6Delta.RecipeI K n)
    (hτp : τ ^ p = 1) :
    ∃ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n),
      orderOf f = p ∧ ∃ u ∈ TwE6Delta.RecipeI K n, τ = u * f * u⁻¹ := by
  obtain ⟨hsimple, hnc⟩ := isSimpleGroup_recipeR hn hK
  obtain ⟨f₀, hf₀, hu₀⟩ : ∃ f₀ ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (TwE6Delta.RecipeH K n), τ * f₀⁻¹ ∈ TwE6Delta.RecipeI K n := by
    have hQ := RawAutTwE6.twE6Quot_recipe hn K hK
    suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
        H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
          TwistTag.E6.perm n →
        ∀ ψ : MulAut (LargeEvenCenterQuot H),
          ∃ f₀ ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K H,
            ψ * f₀⁻¹ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
      key _ (largeEvenTwistedH_eq _ K _ n) τ
    intro H hH
    subst hH
    obtain ⟨Θ, -, hker, -, hex⟩ := hQ
    intro ψ
    obtain ⟨f₀, hf₀, hΘ⟩ := hex (Θ ψ)
    refine ⟨f₀, hf₀, mem_chevID_iff_isInnDiagOn.mpr ((hker _).mp ?_)⟩
    rw [map_mul, map_inv, hΘ, mul_inv_cancel]
  have hL : GGRawFieldConj p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)) :=
    RecipeExcLang.ggRawFieldConj_twE6 hn hK hp hp2
  have hτ : τ * f₀⁻¹ * f₀ = τ := inv_mul_cancel_right τ f₀
  obtain ⟨f, hf, u, hu, hord, he⟩ := hL hsimple hnc (τ * f₀⁻¹) hu₀ f₀ (Subgroup.subset_closure hf₀)
    (by rwa [hτ]) (by rw [hτ]; exact hτp)
  exact ⟨f, hf, hord, u, hu, by rw [← he, hτ]⟩

theorem card_le_mul_inf_inn (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) {E : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card (E ⊓ (MulAut.conj : TwE6Delta.RecipeR K n →*
      MulAut (TwE6Delta.RecipeR K n)).range : Subgroup (MulAut (TwE6Delta.RecipeR K n))) := by
  have := TwE6Delta.finite_mulAut_recipeR hK
  obtain ⟨Θ, hker⟩ : ∃ Θ : MulAut (TwE6Delta.RecipeR K n) →* (K ≃+* K),
      ∀ φ, Θ φ = 1 → φ ∈ TwE6Delta.RecipeI K n := by
    have hQ := RawAutTwE6.twE6Quot_recipe hn K hK
    suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
        H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
          TwistTag.E6.perm n →
        ∃ Θ : MulAut (LargeEvenCenterQuot H) →* (K ≃+* K),
          ∀ φ, Θ φ = 1 → φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
      key _ (largeEvenTwistedH_eq _ K _ n)
    intro H hH
    subst hH
    obtain ⟨Θ, -, hker, -, -⟩ := hQ
    exact ⟨Θ, fun φ h => mem_chevID_iff_isInnDiagOn.mpr ((hker φ).mp h)⟩
  have hcyc : IsCyclic (K ≃+* K) :=
    TableBExc.isCyclic_ringAut K (f := 2 * n) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  set N := (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range with hN
  set φ : E →* (K ≃+* K) := Θ.comp E.subtype with hφ
  have h1 := TableB.card_range_mul_card_ker φ
  have hrange : Nat.card φ.range ≤ p := by
    have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
    refine TableB.card_le_of_isCyclic hp.pos inferInstance ?_
    rintro _ ⟨e, rfl⟩
    rw [← map_pow, show e ^ p = 1 from Subtype.ext (hE.2 e e.2), map_one]
  have hkerle :
      Nat.card φ.ker ≤ Nat.card (E ⊓ N : Subgroup (MulAut (TwE6Delta.RecipeR K n))) := by
    refine Nat.card_le_card_of_injective
      (fun e => (⟨(e : E), (e : E).2, TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 _
        (hker _ (MonoidHom.mem_ker.mp e.2)) (hE.2 _ (e : E).2)⟩ :
          (E ⊓ N : Subgroup (MulAut (TwE6Delta.RecipeR K n))))) fun x y hxy => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (E ⊓ N : Subgroup (MulAut (TwE6Delta.RecipeR K n))) =>
      (z : MulAut (TwE6Delta.RecipeR K n))) hxy
  calc Nat.card E = Nat.card φ.range * Nat.card φ.ker := h1.symm
    _ ≤ p * Nat.card (E ⊓ N : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :=
      Nat.mul_le_mul hrange hkerle

end TwE6Dvd

@[expose] def GGTwE6FieldCentInvInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → p ≠ 3 → p ∣ n →
    ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n), orderOf f = p →
      TwE6Dvd.CentInv p f

section Main


theorem ggTwE6BstarDvdInput_of_fieldCentInv (h : GGTwE6FieldCentInvInput) :
    GGTwE6BstarDvdInput := by
  intro K _ _ n p hn hK hp hpn hp3 hpd
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  have := TwE6Delta.finite_recipeR hK
  refine TwE6Dvd.ggBstarBoundInnR_of_centInv hp (TwE6Delta.center_recipeR_eq_bot hn hK)
    (TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3)
    (fun A hA => TwE6Rank.card_le_of_isElemAbelian hn hK hp hp2 hp3 hpn hA)
    (fun E hE => TwE6Dvd.card_le_mul_inf_inn hn hK hp hp3 hE) fun τ hτI hτp => ?_
  obtain ⟨f, hf, hord, u, -, rfl⟩ := TwE6Dvd.exists_conj_field hn hK hp hp2 hτI hτp
  exact (h K n p hn hK hp hpn hp3 hpd f hf hord).conj u

theorem ggTwE6BstarInput_of_fieldCentInv (h : GGTwE6FieldCentInvInput) : GGTwE6BstarInput :=
  ggTwE6BstarInput_of_dvd (ggTwE6BstarDvdInput_of_fieldCentInv h)

end Main

end CFSG.StandardType
