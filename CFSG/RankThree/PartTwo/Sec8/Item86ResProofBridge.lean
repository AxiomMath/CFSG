module

public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.LieType.Ree.LargeReeModelSchreier
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Bridges


theorem isoGTwo_of_mulEquiv_adjointGroup {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (e : X ≃* adjointGroup .G2 K) :
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = f ∧ Sec4.IsoGTwo X q := by
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  have hq : q.card = 2 ^ f := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · rw [LieTypeIndex.inStandardRange_iff]
      show 3 ≤ q.card
      rw [hq]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    · simp [LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv rfl K (hK.trans hq.symm)
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨q, rfl, rfl, hv, ⟨e.trans (((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.trans e₂)⟩⟩

theorem isoGTwo_of_isoGTwoEven {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (h : IsoGTwoEven X f) :
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = f ∧ Sec4.IsoGTwo X q := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact isoGTwo_of_mulEquiv_adjointGroup hf K hK e

theorem reeF4_of_mulEquiv_reeGamma {X : Type} [Group X] (k : ℕ)
    (hk : 1 ≤ k) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * k + 1)) (e : X ≃* ReeTag.F4.reeGamma K k) :
    ∃ hv : (LieTypeIndex.reeF4 k).Valid,
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 k, hv⟩).Group) := by
  have hv : (LieTypeIndex.reeF4 k).Valid := by
    refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · simpa [LieTypeIndex.inStandardRange_iff] using hk
    · simp [LieTypeIndex.isDuplicateRepresentative_iff]
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma hk hK
  have e' : X ≃* CFSG.Blueprint.DerivedCentralQuotient (ReeTag.F4.reeGamma K k) := e.trans E.symm
  have hEq := ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.F4) (K := K) (a := k)
  rw [hEq] at e'
  have hhalf : (ReeF4LieIndex.of k hv).toSuzukiReeIndex.halfExponent = k :=
    SuzukiReeIndex.halfExponent_reeF4 k hv
  have hcard : Nat.card K =
      2 ^ (2 * (ReeF4LieIndex.of k hv).toSuzukiReeIndex.halfExponent + 1) := by
    rw [hhalf]
    exact hK
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.reeF4_candidate_equiv_of_card (ReeF4LieIndex.of k hv) hcard
  rw [hhalf] at e₁
  exact ⟨hv, ⟨(e'.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv k)).trans e₁.symm⟩⟩

theorem reeF4_of_isoReeF4 {X : Type} [Group X] {f : ℕ}
    (hf : 3 ≤ f) (h : IsoReeF4 X f) :
    ∃ (k : ℕ) (hk : (TauCeti.LieTypeIndex.reeF4 k).Valid), 2 * k + 1 = f ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 k, hk⟩).Group) := by
  obtain ⟨k, K, _, _, _, hkf, hK, ⟨e⟩⟩ := h
  obtain ⟨hv, he⟩ := reeF4_of_mulEquiv_reeGamma k (by omega) K (by rw [hK, hkf]) e
  exact ⟨k, hv, hkf, he⟩

end Bridges

@[expose] def IsGammaType (X : Type) [Group X] (m : ℕ) : Prop :=
  (∃ (k : ℕ) (hk : (TauCeti.LieTypeIndex.reeF4 k).Valid), 2 * k + 1 = 3 * m ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 k, hk⟩).Group)) ∨
    IsoTrialityD4 X m ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 * m ∧ Sec4.IsoGTwo X q) ∨
    Nonempty (X ≃* projSU 3 2 (3 * m)) ∨ IsoSUThree X (2 ^ (3 * m)) ∨
    Nonempty (X ≃* projSp 2 (GaloisField 2 (3 * m)))

theorem isGammaType_of_isGammaIndex {G : Type} [Group G] [Finite G] {A Le : Subgroup G}
    {d : G} {m : ℕ} (h : IsGammaIndex A Le d m) :
    IsGammaType (Le ⧸ aschbacherSolvableCore 3 Le) m := by
  obtain ⟨-, -, -, ⟨k, hk, hkm, he, -⟩ | ⟨hD | hG | hU | hS | hSp, -⟩⟩ := h
  · exact Or.inl ⟨k, hk, hkm, he⟩
  · exact Or.inr (Or.inl hD)
  · exact Or.inr (Or.inr (Or.inl hG))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hU)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hS))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hSp))))

theorem one_le_of_isGammaIndex {G : Type} [Group G] [Finite G] {A Le : Subgroup G}
    {d : G} {m : ℕ} (h : IsGammaIndex A Le d m) : 1 ≤ m :=
  h.2.2.1

section Data83


variable {G : Type} [Group G] [Finite G]

theorem isGammaIndex_of_data83 {c : G} {L : Subgroup G} {a : G} {A₀ : Subgroup G} {d : G}
    {n : ℕ} (hd : Data83 G c L a A₀ d n) : IsGammaIndex A₀ L d n := by
  have hn1 : 1 ≤ n := hd.odd.pos
  refine ⟨hd.d_mem, hd.d_ne_one, hn1, ?_⟩
  rcases hd.cases with ⟨hD | hG, hK, -⟩ | ⟨hR, -, hK⟩ | ⟨hS, -, hK⟩ | ⟨hU, -, hK⟩ | ⟨hSp, -, hK⟩
  · exact Or.inr ⟨Or.inl hD, hK⟩
  · exact Or.inr ⟨Or.inr (Or.inl (isoGTwo_of_isoGTwoEven (by omega) hG)), hK⟩
  · exact Or.inl (by
      obtain ⟨k, hk, hkn, he⟩ := reeF4_of_isoReeF4 (by omega) hR
      exact ⟨k, hk, hkn, he, hK⟩)
  · exact Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inl hS))), hK⟩
  · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hU)), hK⟩
  · exact Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr hSp))), hK⟩

theorem isGammaType_of_data83 {c : G} {L : Subgroup G} {a : G} {A₀ : Subgroup G} {d : G}
    {n : ℕ} (hd : Data83 G c L a A₀ d n) :
    IsGammaType (L ⧸ aschbacherSolvableCore 3 L) n :=
  isGammaType_of_isGammaIndex (isGammaIndex_of_data83 hd)

end Data83

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
