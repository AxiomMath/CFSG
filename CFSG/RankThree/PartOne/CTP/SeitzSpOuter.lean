module

public import CFSG.RankThree.PartOne.CTP.SeitzSpIndex
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne.KCSpComm CFSG.Assembly.LowTwoRank TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem inner_of_mem_plane_of_exponent_lt {ℓ f r p : ℕ} {F : Type} [Field F] [Finite F]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r) (hF : Nat.card F = ℓ ^ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf5 : f < 5)
    (A : Subgroup (MulAut (StatedProj (StatedSp r F)))) [CFSG.IsElementaryAbelian p A]
    {a : MulAut (StatedProj (StatedSp r F))} (ha : a ∈ A) :
    a ∈ inner (StatedProj (StatedSp r F)) := by
  by_contra haH
  have : NeZero r := ⟨by omega⟩
  have hdvd := (noninner_element_data (spOuter hℓ hf hr hF) hp (by omega) ha haH).1
  have := Nat.le_of_dvd (by omega) hdvd
  omega

theorem outer_vacuous_of_psp_model {ℓ f r p : ℕ} {F : Type} [Field F] [Finite F]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r) (hF : Nat.card F = ℓ ^ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf5 : f < 5) {K : Type} [Group K] (e : K ≃* StatedProj (StatedSp r F))
    (E : Subgroup (MulAut K)) [CFSG.IsElementaryAbelian p E] :
    ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g := by
  have : Fact p.Prime := ⟨hp⟩
  intro φ hφ
  have hmem : MulAut.congr e φ ∈ E.map (MulAut.congr e).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hφ
  have : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  obtain ⟨g, hg⟩ := inner_of_mem_plane_of_exponent_lt hℓ hf hr hF hp hp5 hf5 _ hmem
  exact ⟨e.symm g, eq_conj_of_congr_eq_conj e hg.symm⟩

theorem extSeitzAtOuter_B2_of_exponent_lt_five {q : PrimePower} (he : q.exponent < 5) :
    ExtSeitzAtOuter (.B 2 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hc hout
  exfalso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF := card_fixedField_B 2 q hv
  have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ q.prime_p.ne_zero)
  exact hout (outer_vacuous_of_psp_model q.prime_p q.exponent_pos le_rfl hF hp hp5 he
    (e0.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)) E)

theorem extSeitzAtOuter_B_even_of_exponent_lt_five {r : ℕ} (hr : 3 ≤ r) {q : PrimePower}
    (hq : q.p = 2) (he : q.exponent < 5) : ExtSeitzAtOuter (.B r q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hc hout
  exfalso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF := card_fixedField_B r q hv
  have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ q.prime_p.ne_zero)
  exact hout (outer_vacuous_of_psp_model q.prime_p q.exponent_pos (by omega) hF hp hp5 he
    (e0.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq
      hr)) E)

end CFSG.RankThree.PartOne.CTP
