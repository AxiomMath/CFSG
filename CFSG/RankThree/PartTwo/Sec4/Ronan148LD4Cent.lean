module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LU3FieldD4Def
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LD4Pgu
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage projSU)
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial

section Cent


@[expose] def KF138TrialityG2Excl : Prop :=
  ∀ (n : ℕ), Odd n → 1 < n → ¬ 3 ∣ n →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) →
    ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsStdGraphFieldConj σ α →
    ∀ Y : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), (∀ y ∈ Y, α y = y) →
      (Y.subgroupOf (autFix α)).IsSubnormal → Group.IsPerfect Y →
    ∀ π : Y →* projSU 3 2 n, Function.Surjective π → Nat.Coprime (Nat.card π.ker) 3 → False


theorem kf138TrialityPGUCent_of_g2Excl (hG : KF138TrialityG2Excl) : KF138TrialityPGUCent := by
  intro n hn hn1 h3n K _ _ hK σ hσ α hα3 hαk Y hYα hYsn hYp π hπ hker
  have hn0 : 1 ≤ n := by omega
  have hin : ¬ IsInnerAut α := not_isInnerAut_of_trialityHasKind hn0 hK hσ hαk (by decide)
  have hcls := Sec8.inputs47ClassesD4_of_lang Sec8.kF82D4LangCoset_holds
    Sec8.kF82D4SecondCent_holds n hn K σ hK hσ α hα3 hin
  rcases hcls with hstd | ⟨γ, y, -, -, -, -, hiso⟩
  · exact (hG n hn hn1 h3n K hK σ hσ α hstd Y hYα hYsn hYp π hπ hker).elim
  obtain ⟨K', _, _, hK', ⟨e⟩⟩ := hiso
  have hYE : Y ≤ autFix α := fun y hy => mem_autFix.mpr (hYα y hy)
  set Y₂ : Subgroup ↥(projImage (glPi false 3 (2 ^ n) K')) :=
    (Y.subgroupOf (autFix α)).map e.toMonoidHom with hY₂
  let ι : Y ≃* Y₂ := (Subgroup.subgroupOfEquivOfLe hYE).symm.trans
    ((Y.subgroupOf (autFix α)).equivMapOfInjective e.toMonoidHom e.injective)
  haveI : Group.IsPerfect Y := hYp
  have hY₂p : Group.IsPerfect Y₂ :=
    Group.IsPerfect.ofSurjective (f := ι.toMonoidHom) ι.surjective
  have hK'u : UnitaryFieldData 2 n K' :=
    ⟨Nat.prime_two, hn0, by rw [hK', ← pow_mul, mul_comm]⟩
  have hπ₂ : Function.Surjective (π.comp ι.symm.toMonoidHom) :=
    hπ.comp ι.symm.surjective
  obtain ⟨u₂, d₂, t₂, w₂, hu3, hd3, ht2, hud, hut, huN, hdt, hw⟩ :=
    pgu3_triple hn hK'u hY₂p (π.comp ι.symm.toMonoidHom) hπ₂
  have hι : ∀ z : Y₂, ((ι.symm z : Y) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      ((e.symm (z : ↥(projImage (glPi false 3 (2 ^ n) K'))) : ↥(autFix α)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    intro z
    have h1 : ((ι (ι.symm z) : Y₂) : ↥(projImage (glPi false 3 (2 ^ n) K'))) = z := by
      rw [MulEquiv.apply_symm_apply]
    have h2 : ((ι (ι.symm z) : Y₂) : ↥(projImage (glPi false 3 (2 ^ n) K'))) =
        e ⟨(ι.symm z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom), hYE (ι.symm z).2⟩ := rfl
    rw [← h1, h2, MulEquiv.symm_apply_apply]
  have hι' : ∀ y' : Y, ((ι y' : Y₂) : ↥(projImage (glPi false 3 (2 ^ n) K'))) =
      e ⟨(y' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom), hYE y'.2⟩ := fun _ => rfl
  set u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ((e.symm u₂ : ↥(autFix α)) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom) with hu
  have hecoe : ∀ a b : ↥(projImage (glPi false 3 (2 ^ n) K')),
      ((e.symm (a * b) : ↥(autFix α)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
        (e.symm a : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * (e.symm b) := by
    intro a b
    rw [map_mul, Subgroup.coe_mul]
  refine ⟨u, ι.symm d₂, ι.symm t₂, ι.symm w₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_autFix.mp (e.symm u₂).2
  · rw [hu, ← Subgroup.coe_pow, ← map_pow, hu3, map_one, Subgroup.coe_one]
  · rw [← map_pow, hd3, map_one]
  · rw [← map_pow, ht2, map_one]
  · rw [hι, hu, ← hecoe, ← hecoe, hud]
  · rw [hι, hu, ← hecoe, ← hecoe, hut]
  · apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨z, hzdef⟩ : ∃ z : Y₂, z = ι ⟨x, hx⟩ := ⟨_, rfl⟩
    have hx' : x = ((ι.symm z : Y) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rw [hzdef, MulEquiv.symm_apply_apply]
    have hz := (Subgroup.mem_normalizer_iff.mp huN z).mp z.2
    have hmem : u * x * u⁻¹ = ((ι.symm ⟨_, hz⟩ : Y) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rw [hx', hι, hι, hu, hecoe, hecoe, map_inv, Subgroup.coe_inv]
    rw [hmem]
    exact (ι.symm ⟨_, hz⟩).2
  · have h1 : π (ι.symm d₂ * ι.symm t₂) = (π.comp ι.symm.toMonoidHom) (d₂ * t₂) := by
      change π (ι.symm d₂ * ι.symm t₂) = π (ι.symm (d₂ * t₂))
      rw [map_mul ι.symm]
    have h2 : π (ι.symm t₂ * ι.symm d₂) = (π.comp ι.symm.toMonoidHom) (t₂ * d₂) := by
      change π (ι.symm t₂ * ι.symm d₂) = π (ι.symm (t₂ * d₂))
      rw [map_mul ι.symm]
    rw [h1, h2]
    exact hdt
  · intro w' hw' hπw
    have hz : ((ι w' : Y₂) : ↥(projImage (glPi false 3 (2 ^ n) K'))) = u₂ * w₂ * u₂⁻¹ := by
      rw [hι']
      apply e.symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply Subtype.ext
      rw [hecoe, hecoe, map_inv, Subgroup.coe_inv]
      change (w' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = _
      rw [hw', hι, hu]
    apply hw (ι w') hz
    change π (ι.symm (ι w')) = π (ι.symm w₂)
    rw [MulEquiv.symm_apply_apply]
    exact hπw

end Cent

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
