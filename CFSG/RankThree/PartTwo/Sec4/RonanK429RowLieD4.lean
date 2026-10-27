module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieL3
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLiePGL
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage)

@[expose] def G2Excl429 : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (m : ℕ), Nat.card k = 2 ^ m → 1 ≤ m →
    ∀ (G : Type) [Group G] [Finite G] (C J : Subgroup G), Nonempty (C ≃* adjointGroup Tag.G2 k) →
      J ≤ C → Group.IsPerfect J → (J.subgroupOf C).IsSubnormal →
        IsType429 (J ⧸ CFSG.pCore 2 J) → False

section Fix

variable {X : Type*} [Group X]

theorem autFix_inv (γ : MulAut X) : Sec4.autFix γ⁻¹ = Sec4.autFix γ := by
  ext x
  rw [Sec4.mem_autFix, Sec4.mem_autFix]
  constructor
  · intro h
    have h' := congrArg γ h
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at h'
    exact h'.symm
  · intro h
    have h' := congrArg (γ⁻¹ : MulAut X) h
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h'
    exact h'.symm

@[expose] noncomputable def autFixConjEquiv (β γ : MulAut X) :
    Sec4.autFix (β * γ * β⁻¹) ≃* Sec4.autFix γ :=
  (MulEquiv.subgroupCongr (show Sec4.autFix (β * γ * β⁻¹) = Sec4.autFix (MulAut.congr β γ) from
    rfl)).trans (Sec4.autFixCongrEquiv β γ)

end Fix

section D4


theorem rowLie_D4 (hG2 : G2Excl429) {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {f : ℕ} (hm : ChevalleyExceptionalModel S .trialityD4 2 f)
    {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {K : Subgroup S} (hKC : K ≤ Sec4.autFix σ)
    [Group.IsPerfect K] (hsub : (K.subgroupOf (Sec4.autFix σ)).IsSubnormal)
    (htype : IsType429 (K ⧸ CFSG.pCore 2 K)) :
    CFSG.pCore 2 (Sec4.autFix σ) = ⊥ ∧ 1 ≤ f ∧ IsoLThreePi K 2 f ∧ ¬ IsInnerAut σ := by
  obtain ⟨F, _, _, _, σF, hF, hσF, -, hf1, hsimp, ⟨φ⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  obtain ⟨E, hEK, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 htype
  have hfix : ∀ k ∈ K, σ k = k := fun k hk => Sec4.mem_autFix.mp (hKC hk)
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three hE3 hE9
  have h3 : ∃ k ∈ K, k ≠ 1 ∧ k ^ 3 = 1 := ⟨k₀, hEK hk₀E, hk₀1, hk₀3⟩
  have hnaC : ∃ a b : graphFixedRootGroup TwistTag.D4 F σF.toRingHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  have hZ := center_trivial_of_isSimpleGroup hsimp hnaC
  have hF' : Nat.card F = (2 ^ f) ^ TwistTag.D4.order := hF
  set α := MulAut.congr φ σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hin : IsInnerAut α
  ·
    exfalso
    refine false_of_fix_e9_of_mulEquiv φ
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 F σF.toRingHom →* MulAut _).range ?_
      (fun s => ⟨s, rfl⟩) hZ hin hσ3 hσ1 hEK hEc hE3 hE9 hfix hEZ
    intro B hB h3B hcB
    have hinj := conj_injective_of_center hZ
    set B' := B.comap
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 F σF.toRingHom →* MulAut _) with hB'
    have hmap : B'.map
        (MulAut.conj : graphFixedRootGroup TwistTag.D4 F σF.toRingHom →* MulAut _) = B := by
      rw [hB', Subgroup.map_comap_eq, inf_eq_right.mpr hB]
    have hcard : Nat.card B' = Nat.card B := by
      rw [← hmap, Subgroup.card_map_of_injective hinj]
    have hB'e : CFSG.Assembly.IsElemAbelian 3 B' := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun a ha => hinj ?_⟩
      · simp only [Subgroup.coe_mul, map_mul]
        exact hcB _ a.2 _ b.2
      · rw [map_pow, map_one]
        exact h3B _ ha
    rw [← hcard]
    exact Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup hf1 hF' hσF B' hB'e
  · have hout : ¬ IsInnerAut σ := fun h => hin ((isInnerAut_congr φ σ).mpr h)
    suffices h : IsoLThreePi K 2 f ∧ CFSG.pCore 2 (Sec4.autFix σ) = ⊥ from ⟨h.2, hf1, h.1, hout⟩
    have hεσ : Sec4.autFix σ ≃* Sec4.autFix α := (Sec4.autFixCongrEquiv φ σ).symm
    by_cases hstd : Sec4.IsStdGraphFieldConj σF α
    ·
      exfalso
      have hchar : ringChar F = 2 := ringChar.eq F 2
      obtain ⟨eG⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σF) hchar
      have hγ : Sec4.autFix (fieldActor (t := TwistTag.D4) σF σF) =
          (fieldActor (t := TwistTag.D4) σF σF).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
      have hfixG : Nonempty (Sec4.autFix α ≃* adjointGroup Tag.G2 (fixSubfield σF)) := by
        obtain ⟨β, hβ | hβ⟩ := hstd
        · rw [hβ]
          exact ⟨((autFixConjEquiv β _).trans (MulEquiv.subgroupCongr hγ)).trans eG⟩
        · rw [hβ]
          exact ⟨(((autFixConjEquiv β _).trans
            (MulEquiv.subgroupCongr (autFix_inv _))).trans (MulEquiv.subgroupCongr hγ)).trans eG⟩
      obtain ⟨eα⟩ := hfixG
      exact hG2 (fixSubfield σF) f (card_fixSubfield_of_cube hf1 hF hσF) hf1 S (Sec4.autFix σ) K
        ⟨hεσ.trans eα⟩ hKC inferInstance hsub htype
    ·
      have hPGL : ∃ (π : Bool) (F' : Type) (_ : Field F') (_ : Finite F'), PiField π 2 f F' ∧
          ModThree π (2 ^ f) ∧ Nonempty (Sec4.autFix α ≃* projImage (glPi π 3 (2 ^ f) F')) := by
        rcases Nat.even_or_odd f with hev | hodd
        · obtain ⟨F', _, _, hF'c, ⟨e⟩⟩ :=
            Sec8.kF89D4SecondCentEven_holds f hev hf1 F σF hF hσF α hα3 hin hstd
          refine ⟨true, F', inferInstance, inferInstance,
            ⟨Nat.prime_two, hf1, by simpa [piCard] using hF'c⟩, ?_, ⟨e⟩⟩
          obtain ⟨j, rfl⟩ := hev
          change (2 ^ (j + j)) % 3 = 1
          rw [← two_mul, pow_mul]
          norm_num [Nat.pow_mod]
        · rcases Sec8.inputs47ClassesD4_of_lang Sec8.kF82D4LangCoset_holds
            Sec8.kF82D4SecondCent_holds f hodd F σF hF hσF α hα3 hin with hstd' |
            ⟨γ, y, -, -, -, -, F', _, _, hF'c, ⟨e⟩⟩
          · exact absurd hstd' hstd
          · refine ⟨false, F', inferInstance, inferInstance,
              ⟨Nat.prime_two, hf1, by simpa [piCard] using hF'c⟩, ?_, ⟨e⟩⟩
            obtain ⟨j, rfl⟩ := hodd
            change (2 ^ (2 * j + 1)) % 3 = 2
            rw [pow_succ, pow_mul]
            norm_num [Nat.mul_mod, Nat.pow_mod]
      obtain ⟨π, F', _, _, hPi, hq, ⟨e⟩⟩ := hPGL
      exact pglCase hPi hq (hεσ.trans e) hKC hsub h3

end D4

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
