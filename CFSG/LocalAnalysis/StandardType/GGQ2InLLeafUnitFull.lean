module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
import CFSG.LocalAnalysis.StandardType.GGQ2CensusChainA

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ilu_cent_erase {N : ℕ} {S : Finset (Fin N)} {v : UnitRaw.Vfull N}
    (hSne : S.Nonempty) (hv : v ≠ 0)
    (hcent : UnitRaw.cent S = Submodule.span UnitRaw.F {v}) :
    ∃ m : Fin N, S = Finset.univ.erase m ∧
      Submodule.span UnitRaw.F {v} =
        Submodule.span UnitRaw.F {(UnitRaw.oneLine N).mkQ (Pi.single m 1)} := by
  have hSuniv : S ≠ Finset.univ := by
    intro h
    have hmem : v ∈ (⊥ : Submodule UnitRaw.F (UnitRaw.Vfull N)) := by
      rw [← UnitRaw.cent_univ, ← h, hcent]
      exact Submodule.mem_span_singleton_self v
    rw [Submodule.mem_bot] at hmem
    exact hv hmem
  have hdim : finrank UnitRaw.F (UnitRaw.cent S) = N - S.card :=
    UnitRaw.finrank_cent S hSne hSuniv
  have hspan1 : finrank UnitRaw.F (Submodule.span UnitRaw.F {v}) = 1 :=
    finrank_span_singleton hv
  have hNS : N - S.card = 1 := by rw [← hdim, hcent, hspan1]
  have hSle : S.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hScard : S.card = N - 1 := by omega
  have hcompl : Sᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hcompl
  have hmS : m ∉ S := by
    have : m ∈ Sᶜ := by rw [hm]; simp
    simpa using this
  have hScard' : (Finset.univ.erase m).card = S.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin,
      hScard]
  have hSsub : S ⊆ Finset.univ.erase m := by
    intro i hi
    rw [Finset.mem_erase]
    exact ⟨fun him => hmS (him ▸ hi), Finset.mem_univ i⟩
  have hSeq : S = Finset.univ.erase m :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard'])
  refine ⟨m, hSeq, ?_⟩
  have hdelta_mem : (UnitRaw.oneLine N).mkQ (Pi.single m 1) ∈
      Submodule.span UnitRaw.F {v} := by
    rw [← hcent, UnitRaw.mem_cent_iff]
    refine ⟨Pi.single m 1, rfl, ?_⟩
    intro i hi j hj
    have him : i ≠ m := by
      rw [hSeq, Finset.mem_erase] at hi
      exact hi.1
    have hjm : j ≠ m := by
      rw [hSeq, Finset.mem_erase] at hj
      exact hj.1
    rw [Pi.single_eq_of_ne him, Pi.single_eq_of_ne hjm]
  obtain ⟨i₀, hi₀⟩ := hSne
  have hdelta0 : (UnitRaw.oneLine N).mkQ (Pi.single m 1) ≠ 0 := by
    intro h0
    rw [Submodule.mkQ_apply] at h0
    rw [Submodule.Quotient.mk_eq_zero, UnitRaw.mem_oneLine] at h0
    obtain ⟨c, hc⟩ := h0
    have h1 := congrFun hc m
    have h2 := congrFun hc i₀
    rw [Pi.single_eq_same] at h1
    rw [hSeq, Finset.mem_erase] at hi₀
    have hne : i₀ ≠ m := hi₀.1
    rw [Pi.single_eq_of_ne hne] at h2
    exact one_ne_zero (h1.trans h2.symm)
  exact eq_span_singleton_of_mem_of_finrank_eq_one hspan1 hdelta_mem hdelta0

theorem inLLeafCases_unitFull (N : ℕ) : InLLeafCases (classicalCatalogue (.unitFull N)) := by
  classical
  intro vx hvx ℓ hℓadm hlab hocc hcent hvxinside U hU hvxU j hjadm hjocc hjcent hinj hnorm
    z hzU hzx k hcand hinsK
  have hℓadm' : 4 ≤ N ∧ 4 ≤ ℓ.card := hℓadm
  have hkadm' : 4 ≤ N ∧ 4 ≤ k.card := hcand.1
  have hℓne : ℓ.Nonempty := Finset.card_pos.mp (by omega)
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  have hkcent : UnitRaw.cent k = Submodule.span UnitRaw.F {z} := hcand.2.2.1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzx
    exact hzx (Submodule.zero_mem (Submodule.span UnitRaw.F {vx}))
  obtain ⟨m, hℓeq, hspanvx⟩ := ilu_cent_erase hℓne hvx hcent
  obtain ⟨m', hkeq, hspanz⟩ := ilu_cent_erase hkne hz0 hkcent
  have hmm' : m' ≠ m := by
    intro h
    have hzmem : z ∈ Submodule.span UnitRaw.F
        {(UnitRaw.oneLine N).mkQ (Pi.single m' 1)} := by
      rw [← hspanz]
      exact Submodule.mem_span_singleton_self z
    rw [h, ← hspanvx] at hzmem
    exact hzx hzmem
  have hN5 : 5 ≤ N := by
    have hcard : (Finset.univ.erase m).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
    have h4 := hℓadm'.2
    rw [hℓeq, hcard] at h4
    omega
  have hcentA : UnitRaw.cent (Finset.univ.erase m) = Submodule.span UnitRaw.F {vx} := by
    rw [← hℓeq]
    exact hcent
  have hcentB : UnitRaw.cent (Finset.univ.erase m') = Submodule.span UnitRaw.F {z} := by
    rw [← hkeq]
    exact hkcent
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  rw [hℓeq, hkeq]
  exact unitFull_inLLeafAt_erase hn (Ne.symm hmm') hcentA hcentB

end CFSG.StandardType.GGQ2Frame

end
