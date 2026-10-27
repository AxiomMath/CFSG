module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarTwE6ThreeNine
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar

@[expose] def GGTwE6ThreeTwoLocalRankSixInput : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → 3 ∣ 2 ^ f + 1 →
    ∀ {X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))},
      IsElemAbelian 3 X → X ≤ LayerSixE.twInndiagAut f → Nat.card X = 3 ^ 4 →
      (∃ U : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))), U ≠ ⊥ ∧ IsPGroup 2 U ∧ X ≤ Subgroup.normalizer (U : Set _)) →
      ∃ Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))),
        Y ≤ LayerSixE.twInndiagAut f ∧ X ≤ Y ∧ IsElemAbelian 3 Y ∧ Nat.card Y = 3 ^ 6

private theorem relIndex_inner_twInndiag_le_three {f : ℕ} (hf : 1 ≤ f) :
    ((MulAut.conj : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) →*
        MulAut ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))).range).relIndex
      (LayerSixE.twInndiagAut f) ≤ 3 := by
  let K := GaloisField 2 (2 * f)
  let C := ↥(twistedE6RootGroup K (frobQEquiv hf))
  let I : Subgroup (MulAut C) := (MulAut.conj : C →* MulAut C).range
  let M : Subgroup (MulAut C) := LayerSixE.twInndiagAut f
  have hM : M = I ⊔ twistedE6Diag K (frobQEquiv hf) := by
    change LayerSixE.twInndiagAut f =
      (MulAut.conj : C →* MulAut C).range ⊔ twistedE6Diag K (frobQEquiv hf)
    rw [twInndiagAut_eq_range_twistedE6InndiagConj hf, range_twistedE6InndiagConj]
    rfl
  let q : MulAut C →* MulAut C ⧸ I := QuotientGroup.mk' I
  have hker : q.ker = I := QuotientGroup.ker_mk' I
  have hrel : I.relIndex M = Nat.card ↥(M.map q) := by
    rw [← Subgroup.relIndex_ker (K := M) q, hker]
  have hmap : M.map q ≤
      (q.comp (compatDiagAutHom TwistTag.E6 K (frobQEquiv hf).toRingHom)).range := by
    rw [hM, Subgroup.map_sup]
    have hIbot : Subgroup.map q I = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      show I ≤ q.ker
      rw [hker]
    rw [hIbot, bot_sup_eq]
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨u, rfl⟩ := hd
    exact ⟨u, rfl⟩
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQEquiv hf c = c ^ (2 ^ f) := fun c => by
    change frobQ 2 f c = c ^ (2 ^ f)
    exact frobQ_apply 2 f c
  have hcard : Nat.card ↥((q.comp (compatDiagAutHom TwistTag.E6 K
      (frobQEquiv hf).toRingHom)).range) ≤ 3 :=
    lot_card_range_diag_outer_le_three hK (frobQEquiv hf) hσ
  calc I.relIndex M = Nat.card ↥(M.map q) := hrel
    _ ≤ Nat.card ↥((q.comp (compatDiagAutHom TwistTag.E6 K
          (frobQEquiv hf).toRingHom)).range) := Subgroup.card_le_of_le hmap
    _ ≤ 3 := hcard

theorem ggTwE6ThreeToralCentInput_of_rankSix (h : GGTwE6ThreeTwoLocalRankSixInput) :
    GGTwE6ThreeToralCentInput := by
  intro f hf h3 X hXel hXI hXc h2loc
  obtain ⟨Y, hYI, hXY, hYel, hYc⟩ := h hf h3 hXel hXI hXc h2loc
  let K := GaloisField 2 (2 * f)
  let C := ↥(twistedE6RootGroup K (frobQEquiv hf))
  let I : Subgroup (MulAut C) := (MulAut.conj : C →* MulAut C).range
  let M : Subgroup (MulAut C) := LayerSixE.twInndiagAut f
  let Y' : Subgroup (MulAut C) := Y
  have hY'I : Y' ≤ M := hYI
  haveI : Nonempty ↥M := ⟨1⟩
  have hne : I.relIndex M ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card (H := I) (K := M)
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hidx : I.relIndex Y' ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hY'I hne).trans (relIndex_inner_twInndiag_le_three hf)
  have hmul := Subgroup.relIndex_mul_card (H := I) (K := Y')
  have hle : Nat.card Y' ≤ 3 * Nat.card ↥(I ⊓ Y') := by
    calc Nat.card Y' = I.relIndex Y' * Nat.card ↥(I ⊓ Y') := hmul.symm
      _ ≤ 3 * Nat.card ↥(I ⊓ Y') := Nat.mul_le_mul_right _ hidx
  have hY'c : Nat.card Y' = 3 ^ 6 := hYc
  have hinf : 3 ^ 5 ≤ Nat.card ↥(I ⊓ Y') := by
    have h3' : (3 : ℕ) ^ 6 ≤ 3 * Nat.card ↥(I ⊓ Y') := by
      rw [← hY'c]
      exact hle
    have hpow : (3 : ℕ) ^ 6 = 3 * 3 ^ 5 := by norm_num
    omega
  have hlt : Nat.card X < Nat.card ↥(I ⊓ Y') := by
    rw [hXc]
    calc (3 : ℕ) ^ 4 < 3 ^ 5 := by norm_num
      _ ≤ Nat.card ↥(I ⊓ Y') := hinf
  have hex : ∃ g, g ∈ I ⊓ Y' ∧ g ∉ X := by
    by_contra hc
    rw [not_exists] at hc
    have hle : I ⊓ Y' ≤ X := fun g hg => by
      by_contra hgX
      exact hc g ⟨hg, hgX⟩
    exact (not_le.mpr hlt) (Subgroup.card_le_of_le hle)
  obtain ⟨g, hgIY, hgX⟩ := hex
  refine ⟨g, ?_, ?_, hgX, ?_⟩
  · show g ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range
    exact hgIY.1
  · show g ^ 3 = 1
    exact hYel.2 g hgIY.2
  · intro y hy
    have hyY : y ∈ Y := hXY hy
    haveI : IsMulCommutative ↥Y := hYel.1
    have h1 : (⟨g, hgIY.2⟩ : Y) * (⟨y, hyY⟩ : Y) =
        (⟨y, hyY⟩ : Y) * ⟨g, hgIY.2⟩ := mul_comm' _ _
    exact congrArg Subtype.val h1

end CFSG.StandardType.NoOffTwE6Three
