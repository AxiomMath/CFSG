module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootBasic
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcF4
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcE
public import CFSG.LieType.ChevTwo.Layered
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnPlane
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthChev
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.GH74.Generic.Context
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthGeneric

public section

namespace CFSG.StandardType

open RootCentExc
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction CFSG.LieType.ChevTwo
  CFSG.Yardstones.Md0ec50421ce4

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section C3


theorem isChevTwoLayered_C3Levi {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsChevTwoLayered ↥(F4Pilot.C3Levi K) := by
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  refine isChevTwoLayered_of_isQuasisimple F4Pilot.isQuasisimple_open_C3Levi ?_
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  have hv : (TauCeti.LieTypeIndex.B 3 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [TauCeti.PrimePower.card_def]
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ :=
    CFSG.GH74.Generic.stated_of_lieModel_PSp (F4Pilot.lieModel_C3Levi hK)
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 3 q, hv⟩
  haveI : Fintype K' := Fintype.ofFinite K'
  haveI : Fintype ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) :=
    Fintype.ofFinite _
  have hFcard : Fintype.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) =
      Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      TauCeti.ValidLieTypeIndex.card_fixedField, hK']
    simp [TauCeti.ValidLieTypeIndex.fieldOrder, q, TauCeti.PrimePower.card_def]
  let φ : K' ≃+* ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) :=
    FiniteField.ringEquivOfCardEq hFcard.symm
  let eField := CFSG.Adapters.RankTwoModelTransports.statedProjCongr (ι := Fin 3 ⊕ Fin 3)
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp (K := K')
      (L := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩)) φ 3)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  let eCat :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 3 q hv rfl (by norm_num)
  have hchev : IsChevSimple 2 ↥(F4Pilot.C3Levi K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨.B 3 q, hv⟩
      (by rw [TauCeti.LieTypeIndex.characteristic_B]) (e.trans (eField.trans eCat.symm))
  let eZ : ↥(F4Pilot.C3Levi K) ⧸ Subgroup.center ↥(F4Pilot.C3Levi K) ≃* ↥(F4Pilot.C3Levi K) :=
    (QuotientGroup.quotientMulEquivOfEq F4Pilot.center_C3Levi_eq_bot).trans
      QuotientGroup.quotientBot
  exact isChevSimple_of_mulEquiv eZ hchev

end C3

section A5


theorem isChevTwoLayered_a5Levi {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsChevTwoLayered ↥(E6Pilot.a5Levi K) := by
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  refine isChevTwoLayered_of_isQuasisimple E6Pilot.isQuasisimple_open_a5Levi ?_
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  have hv : (TauCeti.LieTypeIndex.A 5 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [TauCeti.PrimePower.card_def]
  obtain ⟨K', _, _, hK', ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (E6Pilot.lieModel_a5Levi hK)
  haveI : Fintype K' := Fintype.ofFinite K'
  have eCat := CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.catEquivProjectiveSL
    (m := 5) (k := K') (ℓ := 2) (e := f) Nat.prime_two (by omega) hK' hv
  have hchev : IsChevSimple 2 ↥(E6Pilot.a5Levi K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨.A 5 q, hv⟩
      (by rw [TauCeti.LieTypeIndex.characteristic_A]) (e.trans eCat.symm)
  let eZ : ↥(E6Pilot.a5Levi K) ⧸ Subgroup.center ↥(E6Pilot.a5Levi K) ≃* ↥(E6Pilot.a5Levi K) :=
    (QuotientGroup.quotientMulEquivOfEq E6Pilot.center_a5Levi_eq_bot).trans
      QuotientGroup.quotientBot
  exact isChevSimple_of_mulEquiv eZ hchev

end A5

section D6


theorem isChevTwoLayered_perpLevi_E7 {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsChevTwoLayered ↥(EPilot.perpLevi .E7 K) := by
  refine isChevTwoLayered_of_isQuasisimple E7Pilot.isQuasisimple_open_perpLevi_E7 ?_
  have hsc : StatedClassicalModel (EPilot.perpLevi .E7 K) .POmegaPlus 6 2 f :=
    (E7Pilot.lieModel_perpLevi_E7 hK).statedClassicalModel (by decide)
  have hchev : IsChevSimple 2 ↥(EPilot.perpLevi .E7 K) :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth.isChevSimple_of_pomegaPlus hsc
  let eZ : ↥(EPilot.perpLevi .E7 K) ⧸ Subgroup.center ↥(EPilot.perpLevi .E7 K) ≃*
      ↥(EPilot.perpLevi .E7 K) :=
    (QuotientGroup.quotientMulEquivOfEq E7Pilot.center_perpLevi_E7_eq_bot).trans
      QuotientGroup.quotientBot
  exact isChevSimple_of_mulEquiv eZ hchev

end D6

section E7


theorem isChevTwoLayered_e7Levi {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsChevTwoLayered ↥(E8Pilot.e7Levi K) := by
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  refine isChevTwoLayered_of_isQuasisimple E8Pilot.isQuasisimple_open_e7Levi ?_
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  have hqcard : q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def]
  have hv : (TauCeti.LieTypeIndex.E7 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e7 q hv K (by rw [hK, hqcard])
  have hchev : IsChevSimple 2 ↥(E8Pilot.e7Levi K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie ⟨.E7 q, hv⟩
      (by rw [TauCeti.LieTypeIndex.characteristic_E7])
      (E8Pilot.e7LeviEquivAdjointQuotient.trans b)
  let eZ : ↥(E8Pilot.e7Levi K) ⧸ Subgroup.center ↥(E8Pilot.e7Levi K) ≃*
      ↥(E8Pilot.e7Levi K) :=
    (QuotientGroup.quotientMulEquivOfEq E8Pilot.center_e7Levi_eq_bot).trans
      QuotientGroup.quotientBot
  exact isChevSimple_of_mulEquiv eZ hchev

end E7

end Levi

namespace RootCentQLTyped

open RootCentExc

variable {τ : Tag} {K : Type} [Field K]

theorem of_conj {P : adjointGroup τ K → Prop}
    (hP : ∀ (α : MulAut (adjointGroup τ K)) (z : adjointGroup τ K), P z → P (α z))
    {z g : adjointGroup τ K} (h : P (g * z * g⁻¹)) : P z := by
  have h' := hP (MulAut.conj g⁻¹) _ h
  change P (g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹) at h'
  rwa [show g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z by group] at h'

section Iff


theorem iff_of_adj {P : adjointGroup τ K → Prop}
    (hP : ∀ (α : MulAut (adjointGroup τ K)) (z : adjointGroup τ K), P z → P (α z))
    (h2 : (2 : K) = 0) (F : RootOperatorFamily τ) {j k : Fin τ.rank}
    (h1 : τ.cartan k j = -1) (h1' : τ.cartan j k = -1) :
    P (xPar F (Pi.single j 1) (1 : K)) ↔ P (xPar F (Pi.single k 1) (1 : K)) := by
  obtain ⟨g, hg⟩ := exists_conj_xPar_single_of_adj h2 F h1 h1'
  constructor
  · intro h
    rw [← hg]
    exact hP (MulAut.conj g) _ h
  · intro h
    rw [← hg] at h
    exact of_conj hP h

end Iff

section OfMem


theorem of_mem_rootGroup [Finite K] [CharP K 2] {P : adjointGroup τ K → Prop}
    (hP : ∀ (α : MulAut (adjointGroup τ K)) (z : adjointGroup τ K), P z → P (α z))
    (F : RootOperatorFamily τ) (hs : ∀ j, P (xPar F (Pi.single j 1) (1 : K)))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {z : adjointGroup τ K}
    (hz : z ∈ rootGroup F K γ) (hz1 : z ≠ 1) : P z := by
  obtain ⟨g, j, hg⟩ := AutSt.exists_conj_xPar_single hγ hz hz1
  have h := hs j
  rw [← hg] at h
  exact of_conj hP h

theorem exists_single [Finite K] [CharP K 2] {P : adjointGroup τ K → Prop}
    (hP : ∀ (α : MulAut (adjointGroup τ K)) (z : adjointGroup τ K), P z → P (α z))
    (F : RootOperatorFamily τ) {θ : Fin τ.rank → ℤ} {i₀ : Fin τ.rank}
    (hd : HighRootData τ θ i₀) (h : P (xPar F θ (1 : K))) :
    ∃ j, P (xPar F (Pi.single j 1) (1 : K)) := by
  have hx1 : xPar F θ (1 : K) ≠ 1 := by
    intro h'
    rw [← xPar_zero (F := F) θ] at h'
    exact one_ne_zero (xPar_injective hd.maxHeight.1 h')
  obtain ⟨g, j, hg⟩ := AutSt.exists_conj_xPar_single hd.maxHeight.1
    (xPar_mem hd.maxHeight.1 (1 : K)) hx1
  refine ⟨j, ?_⟩
  rw [← hg]
  exact hP (MulAut.conj g) _ h

end OfMem

section Singles


theorem single_E6 [Finite K] [CharP K 2] {P : adjointGroup .E6 K → Prop}
    (hP : ∀ (α : MulAut (adjointGroup .E6 K)) (z : adjointGroup .E6 K), P z → P (α z))
    (F : RootOperatorFamily .E6) (hθ : P (xPar F e6HighRoot (1 : K)))
    (j : Fin Tag.E6.rank) : P (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set Q : Fin Tag.E6.rank → Prop :=
    fun j => P (xPar F (Pi.single j 1) (1 : K)) with hQ
  have step : ∀ a b : Fin Tag.E6.rank, Tag.cartan .E6 b a = -1 → Tag.cartan .E6 a b = -1 →
      (Q b ↔ Q ⟨0, by decide⟩) → (Q a ↔ Q ⟨0, by decide⟩) :=
    fun a b h h' hb => (iff_of_adj hP h2 F h h').trans hb
  have h0 : ∀ j, Q j ↔ Q ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) (step _ ⟨2, by decide⟩ (by decide)
        (by decide) (step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl))
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
        (by decide) Iff.rfl)
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) (step _ ⟨2, by decide⟩ (by decide)
        (by decide) (step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl))
    · exact step _ ⟨4, by decide⟩ (by decide) (by decide) (step _ ⟨3, by decide⟩ (by decide)
        (by decide) (step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩
          (by decide) (by decide) Iff.rfl)))
  obtain ⟨j₁, hj₁⟩ := exists_single hP F highRootData_E6 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

theorem single_E7 [Finite K] [CharP K 2] {P : adjointGroup .E7 K → Prop}
    (hP : ∀ (α : MulAut (adjointGroup .E7 K)) (z : adjointGroup .E7 K), P z → P (α z))
    (F : RootOperatorFamily .E7) (hθ : P (xPar F e7HighRoot (1 : K)))
    (j : Fin Tag.E7.rank) : P (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set Q : Fin Tag.E7.rank → Prop :=
    fun j => P (xPar F (Pi.single j 1) (1 : K)) with hQ
  have step : ∀ a b : Fin Tag.E7.rank, Tag.cartan .E7 b a = -1 → Tag.cartan .E7 a b = -1 →
      (Q b ↔ Q ⟨0, by decide⟩) → (Q a ↔ Q ⟨0, by decide⟩) :=
    fun a b h h' hb => (iff_of_adj hP h2 F h h').trans hb
  have h3 : Q ⟨3, by decide⟩ ↔ Q ⟨0, by decide⟩ :=
    step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
      (by decide) Iff.rfl)
  have h4 : Q ⟨4, by decide⟩ ↔ Q ⟨0, by decide⟩ :=
    step _ ⟨3, by decide⟩ (by decide) (by decide) h3
  have h5 : Q ⟨5, by decide⟩ ↔ Q ⟨0, by decide⟩ :=
    step _ ⟨4, by decide⟩ (by decide) (by decide) h4
  have h0 : ∀ j, Q j ↔ Q ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) h3
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact h3
    · exact h4
    · exact h5
    · exact step _ ⟨5, by decide⟩ (by decide) (by decide) h5
  obtain ⟨j₁, hj₁⟩ := exists_single hP F highRootData_E7 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

theorem single_E8 [Finite K] [CharP K 2] {P : adjointGroup .E8 K → Prop}
    (hP : ∀ (α : MulAut (adjointGroup .E8 K)) (z : adjointGroup .E8 K), P z → P (α z))
    (F : RootOperatorFamily .E8) (hθ : P (xPar F e8HighRoot (1 : K)))
    (j : Fin Tag.E8.rank) : P (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set Q : Fin Tag.E8.rank → Prop :=
    fun j => P (xPar F (Pi.single j 1) (1 : K)) with hQ
  have step : ∀ a b : Fin Tag.E8.rank, Tag.cartan .E8 b a = -1 → Tag.cartan .E8 a b = -1 →
      (Q b ↔ Q ⟨0, by decide⟩) → (Q a ↔ Q ⟨0, by decide⟩) :=
    fun a b h h' hb => (iff_of_adj hP h2 F h h').trans hb
  have h3 : Q ⟨3, by decide⟩ ↔ Q ⟨0, by decide⟩ :=
    step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
      (by decide) Iff.rfl)
  have h4 : Q ⟨4, by decide⟩ ↔ Q ⟨0, by decide⟩ :=
    step _ ⟨3, by decide⟩ (by decide) (by decide) h3
  have h5 : Q ⟨5, by decide⟩ ↔ Q ⟨0, by decide⟩ :=
    step _ ⟨4, by decide⟩ (by decide) (by decide) h4
  have h6 : Q ⟨6, by decide⟩ ↔ Q ⟨0, by decide⟩ :=
    step _ ⟨5, by decide⟩ (by decide) (by decide) h5
  have h0 : ∀ j, Q j ↔ Q ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) h3
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact step _ ⟨6, by decide⟩ (by decide) (by decide) h6
  obtain ⟨j₁, hj₁⟩ := exists_single hP F highRootData_E8 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

end Singles

section SingleF4


theorem single_F4 [Finite K] [CharP K 2] {P : adjointGroup .F4 K → Prop}
    (hP : ∀ (α : MulAut (adjointGroup .F4 K)) (z : adjointGroup .F4 K), P z → P (α z))
    (F : RootOperatorFamily .F4) (hθ : P (xPar F f4HighRoot (1 : K)))
    (j : Fin Tag.F4.rank) : P (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := (inferInstance : CharP K 2)
  set Q : Fin Tag.F4.rank → Prop :=
    fun j => P (xPar F (Pi.single j 1) (1 : K)) with hQ
  let φ : MulAut (adjointGroup Tag.F4 K) := CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K
  have hφ3 : φ (xElement (τ := Tag.F4) ⟨3, by decide⟩ (1 : K)) =
      xElement (τ := Tag.F4) ⟨0, by decide⟩ 1 := by
    have h := CFSG.LieType.Ree.ReeTag.finiteExceptionalAut_xElement
      (t := CFSG.LieType.Ree.ReeTag.F4) (K := K) ⟨3, by decide⟩ 1
    rw [one_pow, show CFSG.LieType.Ree.ReeTag.F4.perm ⟨3, by decide⟩ = ⟨0, by decide⟩ by
      decide] at h
    exact h
  have h30 : Q ⟨3, by decide⟩ ↔ Q ⟨0, by decide⟩ := by
    simp only [hQ, xPar_single_eq_xElement h2 F]
    constructor
    · intro h
      have h' := hP φ _ h
      rwa [hφ3] at h'
    · intro h
      have h' := hP φ.symm _ h
      rwa [← hφ3, MulEquiv.symm_apply_apply] at h'
  have h01 : Q ⟨1, by decide⟩ ↔ Q ⟨0, by decide⟩ := iff_of_adj hP h2 F (by decide) (by decide)
  have h20 : Q ⟨2, by decide⟩ ↔ Q ⟨0, by decide⟩ :=
    (iff_of_adj hP h2 F (k := ⟨3, by decide⟩) (by decide) (by decide)).trans h30
  have h0 : ∀ j, Q j ↔ Q ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact h01
    · exact h20
    · exact h30
  obtain ⟨j₁, hj₁⟩ := exists_single hP F highRootData_F4 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

end SingleF4

end RootCentQLTyped

section Base

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section F4Base


theorem xPar_f4HighRoot_typed {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .F4) :
    GGRootCentQLTyped (xPar F f4HighRoot (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he : xPar F f4HighRoot (1 : K) = F4Pilot.zT K := by
    refine Subtype.ext ((coe_xPar_eq_pinnedX h2 F isRoot_f4HighRoot 1).trans ?_)
    change pinnedX .F4 K f4HighRoot 1 = pinnedX .F4 K (RootOps.orbitCertRoot .F4 47) 1
    rw [F4Pilot.orbitCertRoot_47_44.1]
    rfl
  rw [he]
  obtain ⟨hQ2, hQL, -, hLQ⟩ := F4Pilot.isTwoRadicalDecomp_zT (K := K)
  exact ⟨_, _, hQ2, hQL, hLQ, isChevTwoLayered_C3Levi hK⟩

end F4Base

section EBase


theorem xPar_highRoot_E_typed {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hL : IsChevTwoLayered ↥(EPilot.perpLevi τ K)) (F : RootOperatorFamily τ)
    {i₀ : Fin τ.rank} (hd : HighRootData τ (highRoot τ) i₀) :
    GGRootCentQLTyped (xPar F (highRoot τ) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he : xPar F (highRoot τ) (1 : K) =
      EPilot.pinnedElt τ (highRoot τ) 1 :=
    Subtype.ext (coe_xPar_eq_pinnedX h2 F hd.maxHeight.1 1)
  rw [he]
  obtain ⟨hQ2, hQL, -, hLQ⟩ := EPilot.isTwoRadicalDecomp_highRoot (K := K) hτ one_ne_zero
  exact ⟨_, _, hQ2, hQL, hLQ, hL⟩

end EBase

section E6Base


theorem xPar_e6HighRoot_typed {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .E6) :
    GGRootCentQLTyped (xPar F e6HighRoot (1 : K)) :=
  xPar_highRoot_E_typed (Or.inl rfl) (isChevTwoLayered_a5Levi hK) F highRootData_E6

end E6Base

section E7Base


theorem xPar_e7HighRoot_typed {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .E7) :
    GGRootCentQLTyped (xPar F e7HighRoot (1 : K)) :=
  xPar_highRoot_E_typed (Or.inr (Or.inl rfl)) (isChevTwoLayered_perpLevi_E7 hK) F
    highRootData_E7

end E7Base

section E8Base


theorem xPar_e8HighRoot_typed {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (F : RootOperatorFamily .E8) :
    GGRootCentQLTyped (xPar F e8HighRoot (1 : K)) :=
  xPar_highRoot_E_typed (Or.inr (Or.inr rfl)) (isChevTwoLayered_e7Levi hK) F highRootData_E8

end E8Base

end Base

section Isogeny

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section E6Iso


theorem e6Isogeny_qL_typed {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ (e6Datum K).roots)
    {z : e6Data_valid.minGroup K} (hz : z ∈ (e6Datum K).rootGroup γ)
    (hz1 : e6Isogeny K z ≠ 1) : GGRootCentQLTyped (e6Isogeny K z) := by
  have hγ' : IsRoot .E6 γ :=
    e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
  rw [e6Isogeny_xm K hγ'] at hz1 ⊢
  exact RootCentQLTyped.of_mem_rootGroup (P := GGRootCentQLTyped)
    (fun α z h => h.map α) _ (fun j => RootCentQLTyped.single_E6
      (P := GGRootCentQLTyped) (fun α z h => h.map α) _
      (xPar_e6HighRoot_typed hK _) j) hγ' (xPar_mem hγ' _) hz1

end E6Iso

section E7Iso


theorem e7Isogeny_qL_typed {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {γ : Fin Tag.E7.rank → ℤ} (hγ : γ ∈ (e7Datum K).roots)
    {z : e7Data_valid.minGroup K} (hz : z ∈ (e7Datum K).rootGroup γ)
    (hz1 : e7Isogeny K z ≠ 1) : GGRootCentQLTyped (e7Isogeny K z) := by
  have hγ' : IsRoot .E7 γ :=
    e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hz
  rw [e7Isogeny_xm] at hz1 ⊢
  exact RootCentQLTyped.of_mem_rootGroup (P := GGRootCentQLTyped)
    (fun α z h => h.map α) _ (fun j => RootCentQLTyped.single_E7
      (P := GGRootCentQLTyped) (fun α z h => h.map α) _
      (xPar_e7HighRoot_typed hK _) j) hγ' (xPar_mem hγ' _) hz1

end E7Iso

end Isogeny

section TagTheorems

section TagF4


theorem ggRootInvolModelTypedTag_F4 : GGRootInvolModelTypedTag .F4 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .F4 γ := mem_adjDatum_roots.mp hγ
  have hcz : GGRootCentQLTyped z :=
    RootCentQLTyped.of_mem_rootGroup (P := GGRootCentQLTyped)
      (fun α z h => h.map α) _ (fun j => RootCentQLTyped.single_F4
        (P := GGRootCentQLTyped) (fun α z h => h.map α) _
        (xPar_f4HighRoot_typed hK _) j) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .F4 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).symm
  exact ⟨_, inferInstance, MonoidHom.id _, u * z * u⁻¹, Function.surjective_id,
    hker', rfl, hcz.conj u⟩

end TagF4

section TagE6


theorem ggRootInvolModelTypedTag_E6 : GGRootInvolModelTypedTag .E6 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e6Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e6Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := e6Isogeny_qL_typed hK hγ hz hz1
  have e : e6Isogeny (GaloisField 2 f) (u * z * u⁻¹) =
      e6Isogeny (GaloisField 2 f) u * e6Isogeny (GaloisField 2 f) z *
        (e6Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  have hcz' : GGRootCentQLTyped (e6Isogeny (GaloisField 2 f) (u * z * u⁻¹)) := by
    have h := hcz.conj (e6Isogeny (GaloisField 2 f) u)
    rwa [← e] at h
  exact ⟨_, inferInstance, e6Isogeny (GaloisField 2 f), u * z * u⁻¹,
    e6Isogeny_surjective _, hπker, rfl, hcz'⟩

end TagE6

section TagE7


theorem ggRootInvolModelTypedTag_E7 : GGRootInvolModelTypedTag .E7 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e7Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e7Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := e7Isogeny_qL_typed hK hγ hz hz1
  have e : e7Isogeny (GaloisField 2 f) (u * z * u⁻¹) =
      e7Isogeny (GaloisField 2 f) u * e7Isogeny (GaloisField 2 f) z *
        (e7Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  have hcz' : GGRootCentQLTyped (e7Isogeny (GaloisField 2 f) (u * z * u⁻¹)) := by
    have h := hcz.conj (e7Isogeny (GaloisField 2 f) u)
    rwa [← e] at h
  exact ⟨_, inferInstance, e7Isogeny (GaloisField 2 f), u * z * u⁻¹,
    e7Isogeny_surjective _, hπker, rfl, hcz'⟩

end TagE7

section TagE8


theorem ggRootInvolModelTypedTag_E8 : GGRootInvolModelTypedTag .E8 := by
  intro X _ _ n f ψ hadm hrank hker hC r hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  have hcz : GGRootCentQLTyped z :=
    RootCentQLTyped.of_mem_rootGroup (P := GGRootCentQLTyped)
      (fun α z h => h.map α) _ (fun j => RootCentQLTyped.single_E8
        (P := GGRootCentQLTyped) (fun α z h => h.map α) _
        (xPar_e8HighRoot_typed hK _) j) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .E8 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).symm
  exact ⟨_, inferInstance, MonoidHom.id _, u * z * u⁻¹, Function.surjective_id,
    hker', rfl, hcz.conj u⟩

end TagE8

end TagTheorems

end CFSG.StandardType
