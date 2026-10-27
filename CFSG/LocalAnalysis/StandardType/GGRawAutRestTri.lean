module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace RawAutTri

@[expose] def TriAutOn (K : Type) [Field K] (n : ℕ) (S : (Fin TwistTag.D4.tag.rank → ℤ) → Prop) :
    Prop :=
  Subgroup.center (MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n) = ⊥ ∧
    (∀ (σ : K ≃+* K) (h : MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n),
      ∃ h' : MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n,
        ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
          MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _)) ∧
    (∀ (σ : K ≃+* K) (g : MarkChev.GLS S K),
      g ∈ MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n →
      (∀ h : MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n,
        MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _) =
          ((g * h * g⁻¹ : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K))) → σ = 1) ∧
    ∀ α : MulAut (MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n),
      ∃ g ∈ MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n, ∃ σ : K ≃+* K,
        ∀ h : MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n,
          ((α h : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
            (g : Module.End K (MarkChev.Space S K)) *
              MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _) *
                ((g⁻¹ : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K))

theorem TriAutOn.of_eq {K : Type} [Field K] {n : ℕ} {S S' : (Fin TwistTag.D4.tag.rank → ℤ) → Prop}
    (hS : S = S') (h : TriAutOn K n S) : TriAutOn K n S' :=
  hS ▸ h


theorem triAutOn_isRoot {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) : TriAutOn K n (IsRoot TwistTag.D4.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ₀ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ₀ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨hfield, hnf, ⟨Θ, hΘ, -, hker, -⟩, -, -, hcomm, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK σ₀ hσ
  have hC : MarkChev.twistedH TwistTag.D4.tag.cartan (IsRoot TwistTag.D4.tag) K TwistTag.D4.perm
      n = graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom := by
    rw [twistedH_eq_commutator K .D4 n σ₀.toRingHom hσ]
    exact hcomm
  unfold TriAutOn
  rw [hC]
  refine ⟨hZ, fun σ h => ⟨fieldActor σ₀ σ h, ?_⟩, fun σ g hg hrel => ?_, fun α => ?_⟩
  · rw [hfield]
    rfl
  · have hfc : fieldActor σ₀ σ =
        MulAut.conj (⟨g, hg⟩ : graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom) := by
      refine MulEquiv.ext fun h => Subtype.ext (Units.ext ?_)
      rw [hfield, MulAut.conj_apply]
      exact hrel h
    have h1 : Θ (fieldActor σ₀ σ) = σ := hΘ _ 1 σ (by rw [map_one, one_mul])
    have h2 : MulAut.conj (⟨g, hg⟩ : graphFixedRootGroup TwistTag.D4 K σ₀.toRingHom) ∈
        Θ.ker := by
      rw [hker]
      exact ⟨_, rfl⟩
    rw [← h1, hfc]
    exact h2
  · obtain ⟨⟨g, δ⟩, hα, -⟩ := hnf α
    refine ⟨g, g.2, δ, fun h => ?_⟩
    rw [hα, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Units.val_mul, Units.val_mul, hfield]
    rfl

theorem ggRawInnField_triD4 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
      (LargeEvenChevIDImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
      (LargeEvenChevFieldImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) := by
  have hsub := TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK
  obtain ⟨hZ, hstab, hkey, -⟩ :=
    (triAutOn_isRoot hn K hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.D4.tag).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.D4.tag.cartan K),
      H = MarkChev.twistedH TwistTag.D4.tag.cartan (LargeEvenIsRoot TwistTag.D4.tag.cartan) K
        TwistTag.D4.perm n →
      LargeEvenChevIDImage TwistTag.D4.tag.cartan K H ⊆
        (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range →
      GGRawInnField p (LargeEvenCenterQuot H) (LargeEvenChevIDImage TwistTag.D4.tag.cartan K H)
        (LargeEvenChevFieldImage TwistTag.D4.tag.cartan K H) from
    key _ (largeEvenTwistedH_eq _ K _ n) hsub
  intro H hH hsub
  subst hH
  refine ggRawInnField_of_subgroup hp
    (Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage TwistTag.D4.tag.cartan K _)) rfl
    (conj_mem_chevIDImage _) fun φ hφ hφI => ?_
  obtain ⟨σ, hσ⟩ := hφ
  obtain ⟨y, hy⟩ := hsub hφI
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hmk : Function.Injective (LargeEvenCenterMk (MarkChev.twistedH TwistTag.D4.tag.cartan
      (LargeEvenIsRoot TwistTag.D4.tag.cartan) K TwistTag.D4.perm n)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  have hrel : ∀ h : MarkChev.twistedH TwistTag.D4.tag.cartan
      (LargeEvenIsRoot TwistTag.D4.tag.cartan) K TwistTag.D4.perm n,
      MarkChev.entrywise (LargeEvenIsRoot TwistTag.D4.tag.cartan) K σ (map_zero σ)
          ((h : LargeEvenChevGL TwistTag.D4.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) =
        (((g : LargeEvenChevGL TwistTag.D4.tag.cartan K) * h *
            (g : LargeEvenChevGL TwistTag.D4.tag.cartan K)⁻¹ :
              LargeEvenChevGL TwistTag.D4.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) := by
    intro h
    obtain ⟨h', hh'⟩ := hstab σ h
    have e1 := hσ h h' hh'
    have e2 : φ (LargeEvenCenterMk _ h) = LargeEvenCenterMk _ (g * h * g⁻¹) := by
      rw [← hy]
      exact conj_mk_centerQuot g h
    have e3 := hmk (e1.symm.trans e2)
    rw [← hh', e3]
    rfl
  have hσ1 := hkey σ g g.2 hrel
  subst hσ1
  ext z
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨h', hh'⟩ := hstab 1 h
  have e1 := hσ h h' hh'
  rw [MulAut.one_apply]
  change φ (LargeEvenCenterMk _ h) = LargeEvenCenterMk _ h
  rw [e1]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [hh']
  exact largeEvenEntrywise_of_forall_eq _ (fun x => rfl) _

theorem exists_conj_mul_field_triD4 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3)
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))) :
    ∃ u ∈ LargeEvenChevIDImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n),
      ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage LargeEvenCartanD4 K
          (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)), φ = u * f := by
  obtain ⟨hZ, -, -, hnf⟩ :=
    (triAutOn_isRoot hn K hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.D4.tag).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.D4.tag.cartan K),
      H = MarkChev.twistedH TwistTag.D4.tag.cartan (LargeEvenIsRoot TwistTag.D4.tag.cartan) K
        TwistTag.D4.perm n →
      ∀ φ : MulAut (LargeEvenCenterQuot H), ∃ u ∈ LargeEvenChevIDImage TwistTag.D4.tag.cartan K H,
        ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage TwistTag.D4.tag.cartan K H), φ = u * f from
    key _ (largeEvenTwistedH_eq _ K _ n) φ
  intro H hH φ
  subst hH
  obtain ⟨g, hg, σ, hσ⟩ := hnf (MulAut.congr (centerQuotEquivOfBot hZ) φ)
  refine ⟨MulAut.conj (LargeEvenCenterMk _ ⟨g, hg⟩), conj_mem_chevIDImage _ _,
    (MulAut.conj (LargeEvenCenterMk _ ⟨g, hg⟩))⁻¹ * φ,
    Subgroup.subset_closure ⟨σ, fun h h' hh' => ?_⟩, (mul_inv_cancel_left _ φ).symm⟩
  rw [MulAut.mul_apply, congr_centerQuotEquivOfBot_mk hZ φ h, MulAut.conj_inv_apply, ← map_inv,
    ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, hσ h, hh']
  calc ((g⁻¹ : LargeEvenChevGL TwistTag.D4.tag.cartan K) :
        Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) *
        ((g : Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) *
          MarkChev.entrywise (LargeEvenIsRoot TwistTag.D4.tag.cartan) K σ (map_zero σ)
            ((h : LargeEvenChevGL TwistTag.D4.tag.cartan K) :
              Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) *
          ((g⁻¹ : LargeEvenChevGL TwistTag.D4.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K))) *
        (g : Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) =
      ((g⁻¹ : LargeEvenChevGL TwistTag.D4.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) * g *
        MarkChev.entrywise (LargeEvenIsRoot TwistTag.D4.tag.cartan) K σ (map_zero σ)
          ((h : LargeEvenChevGL TwistTag.D4.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) *
        (((g⁻¹ : LargeEvenChevGL TwistTag.D4.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.D4.tag.cartan K)) * g) := by
        simp only [mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, one_mul, mul_one]
        rfl

end RawAutTri

open RawAutTri

section Labels


theorem ggRawInnFieldOn_triD4 : GGRawInnFieldOn fun lab => lab.tag = .triD4 := by
  intro p hp _ lab hlab ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  exact recipeTwisted_and (fun K _ _ hK => ggRawInnField_triD4 hn K hK hp.one_lt.ne') hQ

theorem ggOddAutOn_triD4 : GGOddAutOn fun lab => lab.tag = .triD4 := by
  intro p lab _ _ hlab ht _ Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  exact recipeTwisted_and (P := fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGOddAutInnField p I F)
    (fun K _ _ hK _ _ => RawAut.ggOddAutInnField_of_forall (exists_conj_mul_field_triD4 hn K hK))
    hQ

end Labels

end CFSG.StandardType

end
