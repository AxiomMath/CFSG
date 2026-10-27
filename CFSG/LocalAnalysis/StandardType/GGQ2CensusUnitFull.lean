module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCensusStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2CensusChainA
import CFSG.LocalAnalysis.StandardType.GGQ2UnitCutThree
import CFSG.LocalAnalysis.StandardType.GGQ2UnitShapes

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem gccuf_e_ne_zero {N : ℕ} {m q : Fin N} (hq : q ≠ m) :
    UnitRaw.unitVec N m ≠ 0 := by
  intro h0
  rw [UnitRaw.unitVec] at h0
  rw [Submodule.mkQ_apply] at h0
  rw [Submodule.Quotient.mk_eq_zero, UnitRaw.mem_oneLine] at h0
  obtain ⟨c, hc⟩ := h0
  have h1 := congrFun hc m
  have h2 := congrFun hc q
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hq] at h1 h2
  exact zero_ne_one (h2.trans h1.symm)

private theorem gccuf_e_mem_cent {N : ℕ} {S : Finset (Fin N)} {m : Fin N} (hm : m ∉ S) :
    UnitRaw.unitVec N m ∈ UnitRaw.cent S := by
  rw [UnitRaw.mem_cent_iff]
  refine ⟨Pi.single m 1, rfl, ?_⟩
  intro i hi j hj
  rw [Pi.single_eq_of_ne (show i ≠ m from fun h => hm (h ▸ hi)),
    Pi.single_eq_of_ne (show j ≠ m from fun h => hm (h ▸ hj))]

private theorem gccuf_e_notMem_cent {N : ℕ} {S : Finset (Fin N)} {m i : Fin N}
    (hmS : m ∈ S) (hiS : i ∈ S) (him : i ≠ m) :
    UnitRaw.unitVec N m ∉ UnitRaw.cent S := by
  intro hmem
  obtain ⟨w, hw, hwconst⟩ := (UnitRaw.mem_cent_iff S (UnitRaw.unitVec N m)).mp hmem
  have h0 : UnitRaw.diffFun N m i (UnitRaw.unitVec N m) = 0 := by
    rw [← hw, UnitRaw.diffFun_mk, sub_eq_zero]
    exact hwconst m hmS i hiS
  change UnitRaw.diffFun N m i ((UnitRaw.oneLine N).mkQ (Pi.single m 1)) = 0 at h0
  rw [UnitRaw.diffFun_mk, Pi.single_eq_same, Pi.single_eq_of_ne him, sub_zero] at h0
  exact one_ne_zero h0

private theorem gccuf_e_notMem_span {N : ℕ} {m m' q : Fin N}
    (hmm' : m ≠ m') (hqm : q ≠ m) (hqm' : q ≠ m') :
    UnitRaw.unitVec N m ∉ Submodule.span UnitRaw.F {UnitRaw.unitVec N m'} := by
  intro hmem
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h1 : UnitRaw.diffFun N m q (c • UnitRaw.unitVec N m') = 0 := by
    rw [map_smul]
    have hz : UnitRaw.diffFun N m q (UnitRaw.unitVec N m') = 0 := by
      change UnitRaw.diffFun N m q
        ((UnitRaw.oneLine N).mkQ (Pi.single m' 1)) = 0
      rw [UnitRaw.diffFun_mk, Pi.single_eq_of_ne hmm', Pi.single_eq_of_ne hqm', sub_zero]
    rw [hz, smul_zero]
  have h2 : UnitRaw.diffFun N m q (UnitRaw.unitVec N m) = 1 := by
    change UnitRaw.diffFun N m q ((UnitRaw.oneLine N).mkQ (Pi.single m 1)) = 1
    rw [UnitRaw.diffFun_mk, Pi.single_eq_same, Pi.single_eq_of_ne hqm, sub_zero]
  rw [hc] at h1
  rw [h1] at h2
  exact zero_ne_one h2

private theorem gccuf_occurs_erase {N : ℕ} (hN : 2 ≤ N) (m' : Fin N) :
    UnitRaw.occurs (Submodule.span UnitRaw.F {UnitRaw.unitVec N m'}) (Finset.univ.erase m') := by
  constructor
  · exact Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ m'), Finset.card_univ, Fintype.card_fin]
      omega)
  · intro i hi j'
    constructor
    · intro hj' u hu
      rw [Finset.mem_erase] at hi hj'
      rw [Submodule.mem_span_singleton] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [map_smul]
      have hz : UnitRaw.diffFun N i j' (UnitRaw.unitVec N m') = 0 := by
        change UnitRaw.diffFun N i j'
          ((UnitRaw.oneLine N).mkQ (Pi.single m' 1)) = 0
        rw [UnitRaw.diffFun_mk, Pi.single_eq_of_ne hi.1, Pi.single_eq_of_ne hj'.1, sub_self]
      rw [hz, smul_zero]
    · intro hall
      rw [Finset.mem_erase] at hi
      by_contra hjk
      have hjm : j' = m' := by
        by_contra hne
        exact hjk (by rw [Finset.mem_erase]; exact ⟨hne, Finset.mem_univ j'⟩)
      have hz := hall (UnitRaw.unitVec N m') (Submodule.mem_span_singleton_self _)
      rw [hjm] at hz
      have h1 : UnitRaw.diffFun N i m' (UnitRaw.unitVec N m') = -1 := by
        change UnitRaw.diffFun N i m'
          ((UnitRaw.oneLine N).mkQ (Pi.single m' 1)) = -1
        rw [UnitRaw.diffFun_mk, Pi.single_eq_of_ne hi.1, Pi.single_eq_same, zero_sub]
      rw [h1] at hz
      exact one_ne_zero (neg_eq_zero.mp hz)

private theorem gccuf_cent_erase_eq_span {N : ℕ} (hN : 2 ≤ N) (m' : Fin N) :
    UnitRaw.cent (Finset.univ.erase m') = Submodule.span UnitRaw.F {UnitRaw.unitVec N m'} := by
  have hne : Finset.univ.erase m' ≠ Finset.univ := by
    intro h
    have hmem : m' ∈ Finset.univ.erase m' := by rw [h]; exact Finset.mem_univ m'
    rw [Finset.mem_erase] at hmem
    exact hmem.1 rfl
  have hnon : (Finset.univ.erase m').Nonempty :=
    Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ m'), Finset.card_univ, Fintype.card_fin]
      omega)
  have hdim : finrank UnitRaw.F (UnitRaw.cent (Finset.univ.erase m')) =
      N - (Finset.univ.erase m').card := UnitRaw.finrank_cent _ hnon hne
  have hcard : (Finset.univ.erase m').card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ m'), Finset.card_univ, Fintype.card_fin]
  have hdim1 : finrank UnitRaw.F (UnitRaw.cent (Finset.univ.erase m')) = 1 := by
    rw [hdim, hcard]
    omega
  have hm'not : m' ∉ Finset.univ.erase m' := by
    rw [Finset.mem_erase]
    exact fun h => h.1 rfl
  obtain ⟨q, hq⟩ := hnon
  rw [Finset.mem_erase] at hq
  exact eq_span_singleton_of_mem_of_finrank_eq_one hdim1 (gccuf_e_mem_cent hm'not)
    (gccuf_e_ne_zero hq.1)

private theorem gccuf_normalizerOf_mono {N : ℕ} {S T : Finset (Fin N)} (h : S ⊆ T) :
    UnitRaw.normalizerOf S ≤ UnitRaw.normalizerOf T := by
  rw [UnitRaw.normalizerOf, UnitRaw.normalizerOf, Subgroup.closure_le]
  rintro X ⟨i, hi, j, hj, rfl⟩
  exact Subgroup.subset_closure ⟨i, h hi, j, h hj, rfl⟩

theorem censusCasesUnitFull_holds : CensusCasesUnitFull := by
  classical
  intro N
  change CensusCases (unitFullEntry N)
  dsimp only [CensusCases, unitFullEntry]
  intro vx hvx ℓ hℓadm hocc hcent hvxins U hU hvxU j hjadm hjocc hjcent hinsj hnormj
  have hℓadm' : 4 ≤ N ∧ 4 ≤ ℓ.card := hℓadm
  have hjadm' : 4 ≤ N ∧ 4 ≤ j.card := hjadm
  obtain ⟨m, s, hs, hvxeq, hℓeq⟩ := UnitRaw.lineShapes_holds N vx ℓ hvx hocc hcent
  have hspanvx : Submodule.span UnitRaw.F {vx} =
      Submodule.span UnitRaw.F {UnitRaw.unitVec N m} := by
    rw [hvxeq]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hs) _
  obtain ⟨b, c, hbc, hjbc, -⟩ := UnitRaw.planeShapes_holds N U j hU hjocc hjcent
  have hmj : m ∉ j := by
    intro hm_mem
    obtain ⟨i, hi⟩ : (j.erase m).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hm_mem]; omega)
    rw [Finset.mem_erase] at hi
    have hdelta_cent : UnitRaw.unitVec N m ∈ UnitRaw.cent j := by
      have hle : Submodule.span UnitRaw.F {vx} ≤ U :=
        (Submodule.span_singleton_le_iff_mem vx U).mpr hvxU
      have hspan : UnitRaw.unitVec N m ∈ Submodule.span UnitRaw.F {vx} := by
        rw [hspanvx]
        exact Submodule.mem_span_singleton_self _
      rw [hjcent]
      exact hle hspan
    exact gccuf_e_notMem_cent hm_mem hi.2 hi.1 hdelta_cent
  obtain ⟨m', hmm', hjeq⟩ : ∃ m', m' ≠ m ∧ j = (Finset.univ.erase m).erase m' := by
    have hmbc : m = b ∨ m = c := by
      by_contra h
      apply hmj
      rw [hjbc, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨Finset.mem_univ m, h⟩
    have hset : ∀ d e : Fin N, Finset.univ \ {d, e} = (Finset.univ.erase d).erase e := by
      intro d e
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_erase, true_and, and_true]
      tauto
    rcases hmbc with hmb | hmc
    · refine ⟨c, ?_, ?_⟩
      · rw [hmb]
        exact hbc.symm
      · rw [hjbc, hmb]
        exact hset b c
    · refine ⟨b, ?_, ?_⟩
      · rw [hmc]
        exact hbc
      · rw [hjbc, hmc, Finset.pair_comm]
        exact hset c b
  have hm'_mem : m' ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hmm', Finset.mem_univ m'⟩
  have hcard_m : (Finset.univ.erase m).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
  have hjcard : j.card = N - 2 := by
    rw [hjeq, Finset.card_erase_of_mem hm'_mem, hcard_m]
    omega
  have hN6 : 6 ≤ N := by omega
  have hthird : ∃ q : Fin N, q ≠ m ∧ q ≠ m' := by
    have hcard : ((Finset.univ.erase m).erase m').card = N - 2 := by
      rw [Finset.card_erase_of_mem hm'_mem, hcard_m]
      omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (by rw [hcard]; omega)
    rw [Finset.mem_erase, Finset.mem_erase] at hq
    exact ⟨q, hq.2.1, hq.1⟩
  obtain ⟨q, hqm, hqm'⟩ := hthird
  have hz_cent : UnitRaw.unitVec N m' ∈ UnitRaw.cent j := by
    rw [UnitRaw.mem_cent_iff]
    refine ⟨Pi.single m' 1, rfl, ?_⟩
    intro i hi jj hj
    rw [hjeq, Finset.mem_erase, Finset.mem_erase] at hi hj
    rw [Pi.single_eq_of_ne hi.1, Pi.single_eq_of_ne hj.1]
  have hzU : UnitRaw.unitVec N m' ∈ U := by
    rw [← hjcent]
    exact hz_cent
  have hz_notmem : UnitRaw.unitVec N m' ∉ Submodule.span UnitRaw.F {vx} := by
    rw [hspanvx]
    exact gccuf_e_notMem_span hmm' hqm' hqm
  have hkadm : (unitFullEntry N).admissible (Finset.univ.erase m') := by
    show 4 ≤ N ∧ 4 ≤ (Finset.univ.erase m').card
    refine ⟨hℓadm'.1, ?_⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ m'), Finset.card_univ, Fintype.card_fin]
    omega
  have hocc_k : UnitRaw.occurs (Submodule.span UnitRaw.F {UnitRaw.unitVec N m'})
      (Finset.univ.erase m') := gccuf_occurs_erase (by omega) m'
  have hkcent : UnitRaw.cent (Finset.univ.erase m') =
      Submodule.span UnitRaw.F {UnitRaw.unitVec N m'} := gccuf_cent_erase_eq_span (by omega) m'
  have hjk : j ⊆ Finset.univ.erase m' := by
    rw [hjeq]
    intro x hx
    rw [Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, Finset.mem_univ x⟩
  have hnorm : UnitRaw.normalizerOf j ≤ UnitRaw.normalizerOf (Finset.univ.erase m') :=
    gccuf_normalizerOf_mono hjk
  have hvx_notmem : vx ∉ UnitRaw.cent (Finset.univ.erase m') := by
    intro hvxcent
    rw [hkcent] at hvxcent
    have hspan_le : Submodule.span UnitRaw.F {vx} ≤
        Submodule.span UnitRaw.F {UnitRaw.unitVec N m'} :=
      (Submodule.span_singleton_le_iff_mem vx _).mpr hvxcent
    have hmspan : UnitRaw.unitVec N m ∈ Submodule.span UnitRaw.F {vx} := by
      rw [hspanvx]
      exact Submodule.mem_span_singleton_self _
    exact gccuf_e_notMem_span (Ne.symm hmm') hqm hqm' (hspan_le hmspan)
  have hcw : CommonWitness (unitFullEntry N) vx (UnitRaw.unitVec N m') ℓ
      (Finset.univ.erase m') := by
    rw [hℓeq]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    have hn : 1 ≤ n := by omega
    have hcentA : UnitRaw.cent (Finset.univ.erase m) =
        Submodule.span UnitRaw.F {vx} := by rw [← hℓeq]; exact hcent
    have hcentB : UnitRaw.cent (Finset.univ.erase m') =
        Submodule.span UnitRaw.F {UnitRaw.unitVec (n + 2) m'} :=
      gccuf_cent_erase_eq_span (by omega) m'
    exact unitFull_commonWitness_erase hn (Ne.symm hmm') hcentA hcentB
  refine Or.inl ⟨UnitRaw.unitVec N m', hzU, hz_notmem, Finset.univ.erase m', ?_, hcw⟩
  exact ⟨hkadm, hocc_k, hkcent, hnorm, hvx_notmem⟩

end CFSG.StandardType.GGQ2Frame

end
