module

public import CFSG.RankThree.PartOne.CTP.SeitzFineDefs

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryPlane
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f p : ℕ} {K : Type} [Field K]

theorem closure_centralizers_statedProj_su_five_of_ne (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hne : p ≠ 5)
    (E : Subgroup (StatedProj (StatedSU 5 (ℓ ^ f) K))) [CFSG.IsElementaryAbelian p E]
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSU 5 (ℓ ^ f) K) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  refine closure_centralizers_statedProj_unitary_of_lift h hp (by norm_num) ?_ E hcard ?_
  · intro hd
    have h5 : p ∣ 5 := hd.trans (Nat.gcd_dvd_left _ _)
    exact hne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5)
  · intro E' hc he hcd
    exact closure_centralizers_unitarySU_four_five (n := 4) h hp hp5 hpℓ (Or.inr rfl) E' hc he hcd

theorem extSeitzAtInnerFor_twistedA_four_ne_five {q : TauCeti.PrimePower} :
    ExtSeitzAtInnerFor (.twistedA 4 q) fun p => p ≠ 5 := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd hne E hE hcard hinner
  have : Fact p.Prime := ⟨hp⟩
  left
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 4 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 4 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 4 q, hv⟩)
  have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 4 q hv)
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e1 (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_statedProj_su_five_of_ne hU hp hp5 hpd hne E₁ hcard₁

theorem extSeitzAtOuterFor_twistedA_of_exponent_lt_five {r : ℕ} {q : TauCeti.PrimePower}
    (P : ℕ → Prop) (hq : q.exponent < 5)
    (hnp : ∀ p : ℕ, P p → p.Prime → 5 ≤ p → p ∣ q.p ^ q.exponent + 1 → r + 1 < p) :
    ExtSeitzAtOuterFor (.twistedA r q) P := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd hP E hE hcard hout
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0)
  let ψ : MulAut K ≃* MulAut (primeFormP hU (idGram F (r + 1))) := MulAut.congr θ
  have hψconj : ∀ g : K, ψ (MulAut.conj g) = MulAut.conj (θ g) := by
    intro g
    refine MulEquiv.ext fun x => ?_
    simp [ψ, MulAut.congr_apply, MulAut.conj_apply]
  let A : Subgroup (MulAut (primeFormP hU (idGram F (r + 1)))) := E.map ψ.toMonoidHom
  have hAel : IsElementaryAbelian p A := CFSG.IsElementaryAbelian.map _
  have hAcard : Nat.card A = p ^ 2 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hcard]
  have hAnot : ¬ A ≤ innU hU (r + 1) := by
    intro hle
    apply hout
    intro φ hφ
    obtain ⟨t, ht⟩ := hle ⟨φ, hφ, rfl⟩
    refine ⟨θ.symm t, ψ.injective ?_⟩
    rw [hψconj, MulEquiv.apply_symm_apply]
    exact ht.symm
  have hpℓ : p ≠ q.p := by simpa using hpd
  by_cases hpq : p ∣ q.p ^ q.exponent + 1
  · have h1 := hnp p hP hp hp5 hpq
    have h2 := higher_unitary_noninner_plane_local_core_product_odd q.p q.exponent (r + 1) p F hU
      hp hpℓ hn3 h1 hne ⊤ le_top A le_top hAel hAcard hAnot
    have h3 := Nat.le_of_dvd hf h2.1
    omega
  · have h2 := nonsplit_unitary_noninner_plane_local_core_product_odd q.p q.exponent (r + 1) p F hU
      hp (by omega) hpℓ hpq hn3 hne ⊤ le_top A le_top hAel hAcard hAnot
    have h3 := Nat.le_of_dvd hf h2.2.1
    omega

theorem extSeitzAtOuterFor_twistedA_four_ne_five {q : TauCeti.PrimePower} (hq : q.exponent < 5) :
    ExtSeitzAtOuterFor (.twistedA 4 q) fun p => p ≠ 5 :=
  extSeitzAtOuterFor_twistedA_of_exponent_lt_five _ hq fun p hP _ hp5 _ => by omega

end CFSG.RankThree.PartOne.CTP
