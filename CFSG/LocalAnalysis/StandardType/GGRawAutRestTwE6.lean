module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangSz

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6

namespace RawAutTwE6

@[expose] def TwE6QuotFor (K : Type) [Field K] (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop)
    (H : Subgroup (MarkChev.GLS S K)) : Prop :=
  ∃ Θ : MulAut (LargeEvenCenterQuot H) →* (K ≃+* K),
    Function.Surjective Θ ∧
    (∀ φ, Θ φ = 1 ↔ IsInnDiagOn H (markDiagUnit S K) φ) ∧
    (∀ (σ : K ≃+* K) φ,
      (∀ h h' : H, ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
          MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _) →
        φ (LargeEvenCenterMk H h) = LargeEvenCenterMk H h') → Θ φ = σ) ∧
    ∀ σ : K ≃+* K, ∃ φ : MulAut (LargeEvenCenterQuot H),
      ∀ h h' : H, ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
          MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _) →
        φ (LargeEvenCenterMk H h) = LargeEvenCenterMk H h'

@[expose] def TwE6QuotOn (K : Type) [Field K] (n : ℕ)
    (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) : Prop :=
  TwE6QuotFor K S (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)

theorem TwE6QuotOn.of_eq {K : Type} [Field K] {n : ℕ}
    {S S' : (Fin TwistTag.E6.tag.rank → ℤ) → Prop} (hS : S = S') (h : TwE6QuotOn K n S) :
    TwE6QuotOn K n S' :=
  hS ▸ h


theorem twE6QuotOn_isRoot {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) : TwE6QuotOn K n (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ₀ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ₀ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, hcompat, hfield, hnf, ⟨Θ, hΘ, hsurj, -⟩, -, -, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ₀ hσ
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = twistedE6RootGroup K σ₀ := by
    rw [twistedH_eq_commutator K .E6 n σ₀.toRingHom hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ₀.toRingHom hσ).2.2.1
  unfold TwE6QuotOn
  rw [hC]
  unfold TwE6QuotFor
  rw [markDiagUnit_isRoot]
  have hmk : Function.Injective (LargeEvenCenterMk (twistedE6RootGroup K σ₀)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  have hfa : ∀ (σ : K ≃+* K) (h h' : twistedE6RootGroup K σ₀),
      ((h' : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) =
        MarkChev.entrywise (IsRoot TwistTag.E6.tag) K σ (map_zero σ)
          ((h : ModGL TwistTag.E6.tag K) : Module.End K _) → fieldActor σ₀ σ h = h' := by
    intro σ h h' hh'
    apply Subtype.ext
    apply Units.ext
    rw [hfield, hh']
    rfl
  refine ⟨Θ.comp (MulAut.congr (centerQuotEquivOfBot hZ)).toMonoidHom, fun σ => ?_,
    fun φ => ?_, fun σ φ hφ => ?_, fun σ => ?_⟩
  · obtain ⟨α, hα⟩ := hsurj σ
    exact ⟨(MulAut.congr (centerQuotEquivOfBot hZ)).symm α, by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hα]⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h1
      obtain ⟨g, u, δ, hα⟩ := hnf (MulAut.congr (centerQuotEquivOfBot hZ) φ)
      have hδ : δ = 1 := by rw [← hΘ _ g u δ hα, h1]
      subst hδ
      rw [fieldActor_one, mul_one] at hα
      set d := rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ₀.toRingHom u) with hd
      have hd1 : ∀ h ∈ twistedE6RootGroup K σ₀, d * h * d⁻¹ ∈ twistedE6RootGroup K σ₀ := by
        intro h hh
        have hmem := (compatDiagAutHom TwistTag.E6 K σ₀.toRingHom u ⟨h, hh⟩).2
        rwa [hcompat, ← hd] at hmem
      have hd2 : ∀ h ∈ twistedE6RootGroup K σ₀, d⁻¹ * h * d ∈ twistedE6RootGroup K σ₀ := by
        intro h hh
        set y := (compatDiagAutHom TwistTag.E6 K σ₀.toRingHom u).symm ⟨h, hh⟩ with hy
        have hyy : compatDiagAutHom TwistTag.E6 K σ₀.toRingHom u y = ⟨h, hh⟩ :=
          MulEquiv.apply_symm_apply _ _
        have e := congrArg (fun z : twistedE6RootGroup K σ₀ => (z : ModGL TwistTag.E6.tag K)) hyy
        simp only [hcompat] at e
        rw [← hd] at e
        have e' : d⁻¹ * h * d = (y : ModGL TwistTag.E6.tag K) := by
          rw [← e]
          group
        rw [e']
        exact y.2
      refine ⟨g, g.2, compatDiag TwistTag.E6 σ₀.toRingHom u, hd1, hd2, fun h hh => ?_,
        fun h hh => ?_⟩
      · have e : (g : ModGL TwistTag.E6.tag K) * d * h * ((g : ModGL TwistTag.E6.tag K) * d)⁻¹ =
            g * (d * h * d⁻¹) * (g : ModGL TwistTag.E6.tag K)⁻¹ := by group
        rw [e]
        exact (twistedE6RootGroup K σ₀).mul_mem ((twistedE6RootGroup K σ₀).mul_mem g.2
          (hd1 h hh)) ((twistedE6RootGroup K σ₀).inv_mem g.2)
      · rw [congr_centerQuotEquivOfBot_mk hZ φ h]
        refine congrArg (LargeEvenCenterMk _) (Subtype.ext ?_)
        rw [hα, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, hcompat]
        simp only
        group
    · rintro ⟨g, hg, a, ha1, -, hφ⟩
      obtain ⟨u, hu⟩ := exists_compatDiag_eq
        (fun i => TableB.TwE6.compat_of_forall_conj_mem (t := TwistTag.E6) ha1 i)
      refine hΘ _ ⟨g, hg⟩ u 1 ?_
      rw [fieldActor_one, mul_one]
      refine MulEquiv.ext fun h => ?_
      have h1 := hφ.2 h (hφ.1 h h.2)
      rw [congr_centerQuotEquivOfBot_mk hZ φ h] at h1
      rw [hmk h1]
      apply Subtype.ext
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hcompat, hu]
      simp only
      group
  · have he : MulAut.congr (centerQuotEquivOfBot hZ) φ = fieldActor σ₀ σ := by
      refine MulEquiv.ext fun h => ?_
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        centerQuotEquivOfBot_symm, hφ h (fieldActor σ₀ σ h) (by rw [hfield]; rfl),
        centerQuotEquivOfBot_mk]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he]
    exact hΘ _ 1 1 σ (by rw [map_one, map_one, one_mul, one_mul])
  · refine ⟨(MulAut.congr (centerQuotEquivOfBot hZ)).symm (fieldActor σ₀ σ), fun h h' hh' => ?_⟩
    rw [RecipeExcLang.congr_symm_apply_mk hZ, hfa σ h h' hh']

theorem twE6Quot_recipe {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ Θ : MulAut (LargeEvenCenterQuot (MarkChev.twistedH TwistTag.E6.tag.cartan
        (LargeEvenIsRoot TwistTag.E6.tag.cartan) K TwistTag.E6.perm n)) →* (K ≃+* K),
      Function.Surjective Θ ∧
      (∀ φ, Θ φ = 1 ↔ IsInnDiagOn (MarkChev.twistedH TwistTag.E6.tag.cartan
        (LargeEvenIsRoot TwistTag.E6.tag.cartan) K TwistTag.E6.perm n)
          (TableB.diagHom TwistTag.E6.tag.cartan K) φ) ∧
      (∀ (σ : K ≃+* K) φ, φ ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
          (MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
            TwistTag.E6.perm n) →
        (∀ h h' : MarkChev.twistedH TwistTag.E6.tag.cartan
            (LargeEvenIsRoot TwistTag.E6.tag.cartan) K TwistTag.E6.perm n,
          ((h' : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
              Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
            LargeEvenEntrywise TwistTag.E6.tag.cartan K σ (map_zero σ)
              ((h : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
                Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) →
          φ (LargeEvenCenterMk _ h) = LargeEvenCenterMk _ h') → Θ φ = σ) ∧
      ∀ σ : K ≃+* K, ∃ φ ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
          (MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
            TwistTag.E6.perm n), Θ φ = σ := by
  have hQ := (twE6QuotOn_isRoot hn K hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  unfold TwE6QuotOn TwE6QuotFor at hQ
  rw [← diagHom_eq_markDiagUnit] at hQ
  obtain ⟨Θ, hsurj, hker, hfield, hex⟩ := hQ
  refine ⟨Θ, hsurj, hker, fun σ φ _ hφ => hfield σ φ hφ, fun σ => ?_⟩
  obtain ⟨φ, hφ⟩ := hex σ
  exact ⟨φ, ⟨σ, hφ⟩, hfield σ φ hφ⟩

theorem ggRawInnField_twE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p
      (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  have hQ := twE6Quot_recipe hn K hK
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      GGRawInnField p (LargeEvenCenterQuot H) (LargeEvenChevIDImage TwistTag.E6.tag.cartan K H)
        (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K H) from
    key _ (largeEvenTwistedH_eq _ K _ n)
  intro H hH
  subst hH
  obtain ⟨Θ, -, hker, hfield, -⟩ := hQ
  refine ggRawInnField_of_subgroup hp
    (Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage TwistTag.E6.tag.cartan K _)) rfl
    (conj_mem_chevIDImage _) fun φ hφ hφI => ?_
  obtain ⟨σ, hσ⟩ := hφ
  have h1 : Θ φ = σ := hfield σ φ ⟨σ, hσ⟩ hσ
  rw [(hker φ).mpr (mem_chevID_iff_isInnDiagOn.mp hφI)] at h1
  subst h1
  refine MulEquiv.ext fun z => ?_
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  rw [MulAut.one_apply]
  exact hσ h h (largeEvenEntrywise_of_forall_eq _ (fun x => rfl) _).symm

theorem ggRawPCyclic_twE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} :
    GGRawPCyclic p
      (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  intro _ _
  have hQ := twE6Quot_recipe hn K hK
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      ∃ J S : Subgroup (MulAut (LargeEvenCenterQuot H)),
        (J : Set (MulAut (LargeEvenCenterQuot H))) =
          LargeEvenChevIDImage TwistTag.E6.tag.cartan K H ∧
        J ≤ S ∧ (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
        ∀ α : MulAut (LargeEvenCenterQuot H), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S from
    key _ (largeEvenTwistedH_eq _ K _ n)
  intro H hH
  subst hH
  obtain ⟨Θ, hsurj, hker, -, -⟩ := hQ
  have h2n : 1 ≤ 2 * n := by omega
  obtain ⟨Fr, -, -, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two h2n (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨g₀, hg₀⟩ := hsurj Fr
  refine ⟨Θ.ker, ⊤, ?_, le_top, Subgroup.normal_subgroupOf,
    ⟨g₀, Subgroup.mem_top _, fun s _ => ?_⟩, fun α _ => Subgroup.mem_top α⟩
  · ext φ
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hker, ← mem_chevID_iff_isInnDiagOn]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_top (Θ s))
    refine ⟨-k, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_zpow, hg₀, ← hk, ← _root_.zpow_add, neg_add_cancel,
      zpow_zero]

theorem ggOddAutInnField_twE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (p : ℕ) :
    GGOddAutInnField p
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  have hQ := twE6Quot_recipe hn K hK
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      GGOddAutInnField p (LargeEvenChevIDImage TwistTag.E6.tag.cartan K H)
        (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K H) from
    key _ (largeEvenTwistedH_eq _ K _ n)
  intro H hH
  subst hH
  obtain ⟨Θ, -, hker, -, hex⟩ := hQ
  refine RawAut.ggOddAutInnField_of_hom Θ
    (fun φ h1 => mem_chevID_iff_isInnDiagOn.mpr ((hker φ).mp h1)) fun φ _ => ?_
  obtain ⟨f, hf, hfΘ⟩ := hex (Θ φ)
  exact ⟨f, Subgroup.subset_closure hf, hfΘ⟩

end RawAutTwE6

open RawAutTwE6

section Labels


theorem ggRawInnFieldOn_twE6 : GGRawInnFieldOn fun lab => lab.tag = .twE6 := by
  intro p hp _ lab hlab ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  exact recipeTwisted_and (fun K _ _ hK => ggRawInnField_twE6 hn K hK hp.one_lt.ne') hQ

theorem ggRawPCyclicOn_twE6 : GGRawPCyclicOn fun _ lab => lab.tag = .twE6 := by
  intro p _ _ lab hlab ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  exact recipeTwisted_and (fun K _ _ hK => ggRawPCyclic_twE6 hn K hK) hQ

theorem ggOddAutOn_twE6 : GGOddAutOn fun lab => lab.tag = .twE6 := by
  intro p lab _ _ hlab ht _ Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  exact recipeTwisted_and (P := fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGOddAutInnField p I F)
    (fun K _ _ hK _ _ => ggOddAutInnField_twE6 hn K hK p) hQ

end Labels

end CFSG.StandardType

end
