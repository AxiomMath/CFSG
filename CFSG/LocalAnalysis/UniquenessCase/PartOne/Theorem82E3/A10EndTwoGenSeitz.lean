module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndTwoGenInner
import CFSG.LocalAnalysis.UniquenessCase.UC22P20w
import CFSG.Adapters.CatalogueFieldBridges.Symplectic
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthChev
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116e
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10TwoGen

open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (SeitzGoodIndex)
open CFSG.LieType.SeitzGeneration (IsClassicalIndex UToralRestPrime)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth (nonempty_equiv_of_fixedField_model)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm card_autIm
  isElemAbelian_autIm le_centGenI_of_autIm le_glbCore_of_centGenI)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116e
  (characteristic_eq_two_of_excIndex_three)

private theorem exists_classical_index_psl {L : Type} [Group L] {n p f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel L .PSL n p f) (hn : 3 ≤ n) (hp2 : p ≠ 2) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧ IsClassicalIndex d.1 ∧
      ¬ UToralRestPrime d 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hpow2 : p ^ f ≠ 2 := fun h2 => hp2 (Nat.prime_two.pow_eq_iff.1 h2).1
  have hdup : ¬ ((n = 2 ∧ (p ^ f = 4 ∨ p ^ f = 5 ∨ p ^ f = 9)) ∨ (n = 3 ∧ p ^ f = 2) ∨
      (n = 4 ∧ p ^ f = 2)) := by
    rintro (⟨h2, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩)
    · omega
    · exact hpow2 h2
    · exact hpow2 h2
  obtain ⟨q, hv, hqp, -, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_index_psl hm hdup
  refine ⟨⟨.A (n - 1) q, hv⟩, ?_, trivial, ?_, he⟩
  · rw [TauCeti.LieTypeIndex.characteristic_A, hqp]
  · rintro ⟨m, q', hd, -⟩
    cases hd

private theorem exists_classical_index_psu {L : Type} [Group L] {n p f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel L .PSU n p f) (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (hu : ¬ (3 ∣ p ^ f + 1 ∧ 3 ∣ n)) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧ IsClassicalIndex d.1 ∧
      ¬ UToralRestPrime d 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hpow2 : p ^ f ≠ 2 := fun h2 => hp2 (Nat.prime_two.pow_eq_iff.1 h2).1
  obtain ⟨q, hv, hqp, hqc, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_index_psu hm
  refine ⟨⟨.twistedA (n - 1) q, hv⟩, ?_, trivial, ?_, he⟩
  · rw [TauCeti.LieTypeIndex.characteristic_twistedA, hqp]
  · rintro ⟨m, q', hd, h3, hrest⟩
    obtain ⟨hmn, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj hd
    have h3p : 3 ∣ p ^ f + 1 := by rwa [hqc] at h3
    have h3n : 3 ∣ n := by
      rcases hrest with h2 | hg
      · exact absurd (hqc.symm.trans h2) hpow2
      · have h : 3 ∣ m + 1 := hg.trans (Nat.gcd_dvd_left _ _)
        rwa [show m + 1 = n by omega] at h
    exact hu ⟨h3p, h3n⟩

private theorem exists_classical_index_psp {L : Type} [Group L] {n p f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel L .PSp n p f) (hn : 3 ≤ n) (hp2 : p ≠ 2) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧ IsClassicalIndex d.1 ∧
      ¬ UToralRestPrime d 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hp : p.Prime := hm.1.1
  have hf : 1 ≤ f := hm.1.2.1
  obtain ⟨-, K, hfield, hfinite, hK, ⟨θ⟩⟩ := hm
  let _ := hfield
  let _ := hfinite
  let q : TauCeti.PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (TauCeti.LieTypeIndex.C n q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨hn, hp2⟩, not_false⟩
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_C_of_statedProj
    hv (by rw [TauCeti.PrimePower.card_def]; exact hK)
  refine ⟨⟨.C n q, hv⟩, ?_, trivial, ?_, ⟨θ.trans e⟩⟩
  · rw [TauCeti.LieTypeIndex.characteristic_C]
  · rintro ⟨m, q', hd, -⟩
    cases hd

private theorem exists_classical_index_pomegaOdd {L : Type} [Group L] {n p f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel L .POmegaOdd n p f) (hn : 3 ≤ n) (hp2 : p ≠ 2) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧ IsClassicalIndex d.1 ∧
      ¬ UToralRestPrime d 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hp : p.Prime := hm.1.1
  have hf : 1 ≤ f := hm.1.2.1
  obtain ⟨-, K, hfield, hfinite, hK, ⟨θ⟩⟩ := hm
  let _ := hfield
  let _ := hfinite
  let q : TauCeti.PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (TauCeti.LieTypeIndex.B n q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  obtain ⟨e⟩ := nonempty_equiv_of_fixedField_model
    (fun K _ => CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd n K))
    (fun φ => CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadOdd_comp φ))
    ⟨.B n q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q hv hp2 hn)
    (by simp [TauCeti.ValidLieTypeIndex.fieldOrder, q, hK]) θ
  refine ⟨⟨.B n q, hv⟩, ?_, trivial, ?_, ⟨e⟩⟩
  · rw [TauCeti.LieTypeIndex.characteristic_B]
  · rintro ⟨m, q', hd, -⟩
    cases hd

private theorem exists_classical_index_pomegaPlus {L : Type} [Group L] {n p f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel L .POmegaPlus n p f) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧ IsClassicalIndex d.1 ∧
      ¬ UToralRestPrime d 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨q, hv, hqp, -, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_index_pomegaPlus hm
  refine ⟨⟨.D n q, hv⟩, ?_, trivial, ?_, he⟩
  · rw [TauCeti.LieTypeIndex.characteristic_D, hqp]
  · rintro ⟨m, q', hd, -⟩
    cases hd

private theorem exists_classical_index_pomegaMinus {L : Type} [Group L] {n p f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel L .POmegaMinus n p f) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧ IsClassicalIndex d.1 ∧
      ¬ UToralRestPrime d 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨q, hv, hqp, -, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_index_pomegaMinus hm
  refine ⟨⟨.twistedD n q, hv⟩, ?_, trivial, ?_, he⟩
  · rw [TauCeti.LieTypeIndex.characteristic_twistedD, hqp]
  · rintro ⟨m, q', hd, -⟩
    cases hd

private theorem exists_classical_index_of_odd {L : Type} [Group L] {t : CFSG.Open.StatedLieTag}
    {n p f : ℕ} (hm : CFSG.Open.StatedClassicalModel L t n p f) (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (hu : t = .PSU → ¬ (3 ∣ p ^ f + 1 ∧ 3 ∣ n)) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧ IsClassicalIndex d.1 ∧
      ¬ UToralRestPrime d 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  cases t with
  | PSL => exact exists_classical_index_psl hm hn hp2
  | PSU => exact exists_classical_index_psu hm hn hp2 (hu rfl)
  | PSp => exact exists_classical_index_psp hm hn hp2
  | POmegaOdd => exact exists_classical_index_pomegaOdd hm hn hp2
  | POmegaPlus => exact exists_classical_index_pomegaPlus hm
  | POmegaMinus => exact exists_classical_index_pomegaMinus hm
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact hm.2.elim

theorem glbCore_eq_top_of_classical {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (hd : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) (hd3 : d.1.characteristic ≠ 3)
    (hc : CFSG.LieType.SeitzGeneration.IsClassicalIndex d.1)
    (hu : ¬ CFSG.LieType.SeitzGeneration.UToralRestPrime d 3) (hex : ¬ ChevQ.ExcIndex 3 d.1)
    {A : Subgroup L} (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  classical
  haveI : IsSimpleGroup L := hL
  obtain ⟨e⟩ := hd
  have hsimple : IsSimpleGroup ↥(⊤ : Subgroup L) := Subgroup.topEquiv.isSimpleGroup
  have hnc' : ∃ a b : ↥(⊤ : Subgroup L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩,
      fun h => hab (congrArg Subtype.val h)⟩
  have hcent : Subgroup.centralizer ((⊤ : Subgroup L) : Set L) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      hL hnc
  have hBN : A ≤ Subgroup.normalizer ((⊤ : Subgroup L) : Set L) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_top]
    exact le_top
  have hBC : A ⊓ Subgroup.centralizer ((⊤ : Subgroup L) : Set L) = ⊥ := by
    rw [hcent]
    simp
  have hEcard : Nat.card (autIm A ⊤) = 3 ^ 3 := by
    rw [card_autIm hBN hBC, hcard]
    norm_num
  have hEel : CFSG.Open.IsElemAbelian 3 (autIm A ⊤) := isElemAbelian_autIm hA ⊤
  have hinn : autIm A ⊤ ≤ (MulAut.conj : ↥(⊤ : Subgroup L) →* MulAut ↥(⊤ : Subgroup L)).range := by
    rintro _ ⟨x, -, rfl⟩
    refine ⟨⟨(x : L), Subgroup.mem_top _⟩, ?_⟩
    ext k
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    rfl
  have hgen := seitzHyperGamma_eq_top_of_classical Nat.prime_three (by norm_num) hsimple hnc'
    d (Subgroup.topEquiv.trans e) (fun h => hd3 h.symm) hc hu (Or.inl hex) hEel hEcard hinn
  exact eq_top_iff.mpr (le_glbCore_of_centGenI Nat.prime_three le_rfl hA
    (by rw [hcard]; norm_num) (le_centGenI_of_autIm hBN hBC hgen))

theorem glbCore_eq_top_of_lieModel_odd {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hm : LieModel L t n p f) (hn : 3 ≤ n) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hu : t = .PSU → ¬ (3 ∣ p ^ f + 1 ∧ 3 ∣ n)) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  have hn0 : n ≠ 0 := by omega
  have hm' : CFSG.Open.StatedClassicalModel L t n p f :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (G := L) hn0 hm
  obtain ⟨d, hdchar, hc, hdut, he⟩ := exists_classical_index_of_odd hm' hn hp2 hu
  have hd3 : d.1.characteristic ≠ 3 := by rw [hdchar]; exact hp3
  have hex : ¬ ChevQ.ExcIndex 3 d.1 := by
    intro h
    exact hp2 (hdchar.symm.trans (characteristic_eq_two_of_excIndex_three h))
  exact glbCore_eq_top_of_classical hL hnc d he hd3 hc hdut hex hA hcard

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10TwoGen
