module

public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitNoninnerPlane
public import CFSG.RankThree.PartOne.KC.UnitaryHigherNoninnerPlane
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem extSeitzAtOuter_twistedA_of_exponent_lt_five {r : ℕ} {q : TauCeti.PrimePower}
    (hq : q.exponent < 5)
    (hnp : ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ q.p ^ q.exponent + 1 → r + 1 < p) :
    ExtSeitzAtOuter (.twistedA r q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hcard hout
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
  · have h1 := hnp p hp hp5 hpq
    have h2 := higher_unitary_noninner_plane_local_core_product_odd q.p q.exponent (r + 1) p F hU
      hp hpℓ hn3 h1 hne ⊤ le_top A le_top hAel hAcard hAnot
    have h3 := Nat.le_of_dvd hf h2.1
    omega
  · have h2 := nonsplit_unitary_noninner_plane_local_core_product_odd q.p q.exponent (r + 1) p F hU
      hp (by omega) hpℓ hpq hn3 hne ⊤ le_top A le_top hAel hAcard hAnot
    have h3 := Nat.le_of_dvd hf h2.2.1
    omega

theorem extSeitzAtOuter_twistedA_two {q : TauCeti.PrimePower} (hq : q.exponent < 5) :
    ExtSeitzAtOuter (.twistedA 2 q) :=
  extSeitzAtOuter_twistedA_of_exponent_lt_five hq fun p _ hp5 _ => by omega

theorem extSeitzAtOuter_twistedA_three {q : TauCeti.PrimePower} (hq : q.exponent < 5) :
    ExtSeitzAtOuter (.twistedA 3 q) :=
  extSeitzAtOuter_twistedA_of_exponent_lt_five hq fun p _ hp5 _ => by omega

theorem extSeitzAtOuter_twistedA_four {q : TauCeti.PrimePower} (hq : q.exponent < 5)
    (h5 : ¬ 5 ∣ q.p ^ q.exponent + 1) : ExtSeitzAtOuter (.twistedA 4 q) :=
  extSeitzAtOuter_twistedA_of_exponent_lt_five hq fun p _ hp5 hpd => by
    have : p ≠ 5 := fun h => h5 (h ▸ hpd)
    omega

theorem extSeitzAtOuter_twistedA_five {q : TauCeti.PrimePower} (hq : q.p = 2)
    (he : q.exponent = 1) : ExtSeitzAtOuter (.twistedA 5 q) :=
  extSeitzAtOuter_twistedA_of_exponent_lt_five (by omega) fun p _ hp5 hpd => by
    rw [hq, he] at hpd
    have := Nat.le_of_dvd (by norm_num) hpd
    omega

end CFSG.RankThree.PartOne.CTP
