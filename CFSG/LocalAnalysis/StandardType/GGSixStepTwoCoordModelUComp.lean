module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompAlignMain

public section

namespace CFSG.StandardType

namespace CoordSU

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Multiplicative

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

variable {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G}

theorem injective_comp_ι (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    (hker : SURep.GGFrameKer φ) : Function.Injective (φ.comp F.ι) := by
  have : Finite K := h.finite
  intro s s' hss'
  apply F.ι_injective
  have hz : φ ((F.ι s)⁻¹ * F.ι s') = 1 := by
    rw [map_mul, map_inv]
    change (φ.comp F.ι s)⁻¹ * φ.comp F.ι s' = 1
    rw [hss', inv_mul_cancel]
  have hzp : ((F.ι s)⁻¹ * F.ι s') ^ p = 1 :=
    hA.pow _ (A.mul_mem (A.inv_mem (ι_mem F s)) (ι_mem F s'))
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
  · apply Subtype.ext
    apply Units.ext
    ext x
    exact isEmptyElim x
  · obtain ⟨c, hc⟩ := hker _ hz
    exact inv_mul_eq_one.mp (SUNS.eq_one_of_scalar_mem h hA.prime hA.not_dvd i hc hzp)

open Classical in
theorem comp_class [Finite G] (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    (hFm : FrameMoves F) (hinj : Function.Injective (φ.comp F.ι)) {β : Fin F.r → ZMod p}
    {x : ↥(unitarySU 2 f K n)} (hxβ : F.ι (ofAdd β) = x) {a : K[X]}
    (ha : a ∈ primaryFactors (Xe x)) (ha1 : a ≠ X - C 1) {L₁ : Subgroup G}
    (hL₁ : L₁ = (sb h x a).map φ)
    (hcard : Nat.card ((φ.comp F.ι).range ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤
      p ^ 2) :
    ∃ (k : Fin F.r) (c : ZMod p) (ε : Fin F.r → (ZMod p)ˣ), c ≠ 0 ∧
      (∀ i, ε i ∈ negQ p (2 ^ f)) ∧ (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
      ∀ s : Fin F.r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
        φ (F.ι (ofAdd s)) ∈ L₁ := by
  have hp := hA.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨i₀, hi₀⟩ := exists_pieceIn hA F hxβ ha ha1
  have hc := ne_zero_of_pieceIn hA F hxβ ha ha1 hi₀
  have hal : ∀ i, ∃ o : (ZMod p)ˣ, o ∈ negQ p (2 ^ f) ∧
      (PieceIn F x a i → β i = (o : ZMod p) * β i₀) := by
    intro i
    by_cases hi : PieceIn F x a i
    · obtain ⟨o, hoO, ho⟩ := exists_negQ_mul_of_pieceIn hA F hFm hxβ ha ha1 hi₀ hi
      exact ⟨o, hoO, fun _ => ho⟩
    · exact ⟨1, (negQ p (2 ^ f)).one_mem, fun h' => absurd h' hi⟩
  choose ε hεO hβε using hal
  have hε₀ : ε i₀ = 1 := by
    have h1 := hβε i₀ hi₀
    apply Units.ext
    rw [Units.val_one]
    exact (mul_right_cancel₀ hc (h1.symm.trans (one_mul _).symm))
  set S' := Finset.univ.filter fun i => ¬ PieceIn F x a i with hS'
  have hS'card : S'.card ≤ 1 := card_not_pieceIn_le_one hA F hinj hxβ ha ha1 hL₁ hcard
  obtain ⟨k, hk⟩ : ∃ k, ∀ i, ¬ PieceIn F x a i → i = k := by
    by_cases hne : S'.Nonempty
    · obtain ⟨k, hk⟩ := hne
      refine ⟨k, fun i hi => ?_⟩
      have hiS : i ∈ S' := by simp [hS', hi]
      exact Finset.card_le_one.mp hS'card i hiS k hk
    · refine ⟨i₀, fun i hi => absurd ⟨i, by simp [hS', hi]⟩ hne⟩
  refine ⟨k, β i₀, ε, hc, hεO, fun i hik => ?_, fun s hsk hsum => ?_⟩
  · by_cases hi : PieceIn F x a i
    · exact hβε i hi
    · exact absurd (hk i hi) hik
  · rw [hL₁]
    refine Subgroup.mem_map_of_mem _ (ι_mem_sb_torus hA F hFm hxβ ha hεO hε₀ hβε
      (fun i hi => ?_) hsum)
    rw [hk i hi]
    exact hsk

end CoordSU

open CoordSU NsFrameComp Multiplicative

theorem ggSUPieceCompInput_holds : GGSUPieceCompInput := by
  intro G _ _ f n K _ h p A hA F hFm hr ψ₁ hFk L₁ β hL hcard
  have : Finite K := h.finite
  have hp := hA.prime
  set x := F.ι (ofAdd β) with hxdef
  have hxA : x ∈ A := ι_mem F _
  have hinj := injective_comp_ι hA F hFk
  by_cases hex : ∃ a : CFSG.RankThree.PartOne.KCPrimary.primaryFactors
      ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)),
      CFSG.RankThree.PartOne.KCUnitary.IsGoodBlock h (toUnitHom x) a ∧ L₁ ≤ (sb h x a).map ψ₁
  · obtain ⟨a, ha, hle⟩ := hex
    have hL₁ := eq_map_sb_of_le hFk hp hA.ne_two hA.not_dvd (hA.pow x hxA) hL a ha hle
    by_cases ha1 : (a : Polynomial K) = Polynomial.X - Polynomial.C 1
    · left
      rw [ha1] at hL₁
      exact comp_zero hA F (by omega) hinj hL₁ (ha1 ▸ a.2) hcard
    · right
      exact comp_class hA F hFm hinj rfl a.2 ha1 hL₁ hcard
  · exfalso
    push Not at hex
    have hle := card_le_card_inf_centralizer (L₁ := L₁) hinj id Function.injective_id
      fun s => map_mem_centralizer_of_not_le hFk hA hxA hL hex (ι_mem F _)
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hle.trans hcard)
    omega

end CFSG.StandardType

namespace CFSG.StandardType

section Model

theorem ggStepTwoCoordModelOn_PSU_of_move_shape (hmove : GGSUPieceMoveInput)
    (hshape : GGSUPieceShapeInput) : GGStepTwoCoordModelOn .PSU :=
  ggStepTwoCoordModelOn_PSU_of_piece hmove ggSUPieceCompInput_holds hshape

theorem ggStepTwoToralWitnessOn_PSU_of_move_shape (hmove : GGSUPieceMoveInput)
    (hshape : GGSUPieceShapeInput) : GGStepTwoToralWitnessOn .PSU :=
  ggStepTwoToralWitnessOn_of_coordModel (ggStepTwoCoordModelOn_PSU_of_move_shape hmove hshape)

end Model

end CFSG.StandardType
