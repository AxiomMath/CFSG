module

public import CFSG.RankThree.PartOne.CTP.SeitzSpGeneration
public import CFSG.RankThree.PartOne.CTP.SeitzLift
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartOne.CTP.SeitzThree

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCSpFull CFSG.Assembly.LowTwoRank TauCeti

theorem closure_centralizers_psp_elementary {ℓ f p r : ℕ} {K : Type} [Field K]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : p ≠ ℓ) (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    (E : Subgroup (StatedProj (StatedSp r K))) [CFSG.IsElementaryAbelian p E]
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSp r K) | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  refine closure_centralizers_of_lift (proj r K)
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := r) (K := K))
    ?_ E hcomm hexp ?_
  · intro hd
    have h1 := coprime_card_ker_proj (r := r) (K := K) (by omega) hp (by omega : p ≠ 2)
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 hd (dvd_refl p))
  · intro E' hc he hcd _
    have : CFSG.IsElementaryAbelian p E' :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (he x x.2) }
    exact closure_centralizers_spPlane ⟨hℓ, hf, hK, hp, by omega, hpℓ, hr, hrq, this,
      hcd.trans hcard⟩

theorem card_fixedField_B (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid) :
    Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) = q.p ^ q.exponent := by
  rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
    show ValidLieTypeIndex.characteristic ⟨.B r q, hv⟩ = q.p from
      LieTypeIndex.characteristic_B r q,
    show ValidLieTypeIndex.fieldExponent ⟨.B r q, hv⟩ = q.exponent from
      LieTypeIndex.fieldExponent_B r q]

theorem extSeitzAtInner_B2 (q : PrimePower) : ExtSeitzAtInner (.B 2 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpd' : p ≠ q.p := by simpa using hpd
  left
  have e := e0.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
  have h4 : 4 ≤ q.p ^ q.exponent := by
    have := (TypeB2LieIndex.of q hv).four_le_fieldOrder
    simpa [ValidLieTypeIndex.fieldOrder] using this
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_psp_elementary q.prime_p q.exponent_pos (card_fixedField_B 2 q hv)
    hp hp5 hpd' le_rfl (fun h => by omega) E₁ hcard₁

theorem extSeitzAtInner_B_even {r : ℕ} (hr : 3 ≤ r) {q : PrimePower} (hq : q.p = 2) :
    ExtSeitzAtInner (.B r q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hinner
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpd' : p ≠ q.p := by simpa using hpd
  left
  have e := e0.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv
    hq hr)
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_psp_elementary q.prime_p q.exponent_pos (card_fixedField_B r q hv)
    hp hp5 hpd' (by omega) (fun h => by omega) E₁ hcard₁

end CFSG.RankThree.PartOne.CTP
