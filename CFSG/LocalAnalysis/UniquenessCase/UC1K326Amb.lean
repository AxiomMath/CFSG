module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem jOf_spec (h : Hyp326 G n P) :
    jOf P ≤ P ∧ CFSG.Open.IsElemAbelian 3 (jOf P) ∧ Nat.card (jOf P) = 27 ∧
    (∀ E : Subgroup G, E ≤ P → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 → E = jOf P) ∧
    (∀ E : Subgroup G, E ≤ P → (E.subgroupOf P).Normal → CFSG.Open.IsElemAbelian 3 E →
      E ≤ jOf P) := by
  obtain ⟨e⟩ := h.wr
  obtain ⟨A, hET, hEA, hcard, huniq, hnorm⟩ := zwr_unique_E27 h.one_le e
  have hjOf : jOf P = A.map P.subtype := by
    simp only [jOf, CFSG.inSubgroup, hET]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hjOf]
    exact Subgroup.map_subtype_le _
  · rw [hjOf]
    exact hEA.map P.subtype
  · rw [hjOf, Subgroup.card_map_of_injective P.subtype_injective, hcard]
  · intro E hEP hE hcardE
    have hsub : E.subgroupOf P = A := by
      refine huniq (E.subgroupOf P) (hE.subgroupOf P) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hcardE]
    rw [hjOf, ← hsub, Subgroup.map_subgroupOf_eq_of_le hEP]
  · intro E hEP hEn hE
    rw [hjOf, ← Subgroup.map_subgroupOf_eq_of_le hEP]
    exact Subgroup.map_mono (f := P.subtype) (hnorm (E.subgroupOf P) hEn (hE.subgroupOf P))

theorem map_conj_jOf_eq_of_mem_normalizer (h : Hyp326 G n P) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (jOf P).map (MulAut.conj g).toMonoidHom = jOf P := by
  obtain ⟨hjP, hEA, hcard, huniq, -⟩ := jOf_spec h
  refine huniq _ ?_ (hEA.map (MulAut.conj g).toMonoidHom) ?_
  · rintro y ⟨x, hx, rfl⟩
    have hconj : g * x * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg x).mp (hjP hx)
    simpa [MulAut.conj_apply] using hconj
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

theorem mem_normalizer_jOf_of_mem_normalizer (h : Hyp326 G n P) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer (jOf P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmap := map_conj_jOf_eq_of_mem_normalizer h hg
    have hmem : (MulAut.conj g).toMonoidHom x ∈
        (jOf P).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [hmap] at hmem
    simpa [MulAut.conj_apply] using hmem
  · intro hx
    have hginv : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).inv_mem hg
    have hmap := map_conj_jOf_eq_of_mem_normalizer h hginv
    have hx' : (MulAut.conj g).toMonoidHom x ∈ jOf P := by
      simpa [MulAut.conj_apply] using hx
    have hmem : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom x) ∈
        (jOf P).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx'
    rw [hmap] at hmem
    have hfix : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom x) = x := by
      simp [MulAut.conj_apply]
      group
    rwa [hfix] at hmem

theorem normalizer_le_normalizer_jOf (h : Hyp326 G n P) :
    P ≤ Subgroup.normalizer (jOf P : Set G) ∧
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (jOf P : Set G) :=
  ⟨fun _ hg => mem_normalizer_jOf_of_mem_normalizer h (Subgroup.le_normalizer hg),
   fun _ hg => mem_normalizer_jOf_of_mem_normalizer h hg⟩

theorem pCore_le_sylow (h : IsSylowOf 3 P ⊤) : CFSG.pCore 3 G ≤ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : ¬ 3 ∣ P.index := by
    have h' := (CFSG.ABGLocalTools.isSylowOf_iff.mp h).2.2
    rwa [Subgroup.relIndex_top_right] at h'
  haveI : (CFSG.pCore 3 G).Normal := CFSG.pCore_normal
  have hle := (CFSG.pCore_isPGroup (p := 3) (G := G)).le_sylow_of_normal
    (h.isPGroup.toSylow hdvd)
  simpa using hle

theorem le_oPrimeResidual_of_sylow (h : IsSylowOf 3 P ⊤) :
    P ≤ CFSG.GH74.GLS.oPrimeResidual 3 G := by
  intro x hx
  obtain ⟨k, hk⟩ := h.isPGroup ⟨x, hx⟩
  exact Subgroup.subset_closure ⟨k, by simpa using hk⟩

theorem genFittingFitting_eq_pCore (hc : CFSG.pPrimeCore 3 G = ⊥) :
    CFSG.Open.genFittingFitting G = CFSG.pCore 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ ?_
  · rw [CFSG.Open.genFittingFitting.eq_sSup]
    refine sSup_le ?_
    rintro N ⟨hNn, hNnil⟩
    haveI : N.Normal := hNn
    have htop := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥N) (p := 3) hNnil
    have hmap : N ≤ (CFSG.pCore 3 ↥N).map N.subtype ⊔
        (CFSG.pPrimeCore 3 ↥N).map N.subtype := by
      have h := Subgroup.map_mono (f := N.subtype) htop
      rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
      exact h
    have hpc : (CFSG.pCore 3 ↥N).map N.subtype = N ⊓ CFSG.pCore 3 G := by
      rw [CFSG.pCore_eq_piCore, CFSG.pCore_eq_piCore]
      exact CFSG.LocalCores.prime_set_core_normal_intersection
        {q : Nat.Primes | q.val = 3} hNn
    have hppc : (CFSG.pPrimeCore 3 ↥N).map N.subtype = N ⊓ CFSG.pPrimeCore 3 G := by
      rw [CFSG.pPrimeCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]
      exact CFSG.LocalCores.prime_set_core_normal_intersection
        {q : Nat.Primes | q.val ≠ 3} hNn
    rw [hpc, hppc, hc, inf_bot_eq, sup_bot_eq] at hmap
    exact hmap.trans inf_le_right
  · refine le_sSup ?_
    exact ⟨CFSG.pCore_normal (p := 3) (G := G), CFSG.pCore_isNilpotent (p := 3) (G := G)⟩

theorem noncomp_core (hc : CFSG.pPrimeCore 3 G = ⊥)
    (hnc : ∀ L : Subgroup G, ¬ CFSG.Open.IsComponentOf L ⊤) :
    Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤ CFSG.pCore 3 G := by
  have hlayer : CFSG.Open.genFittingLayer G = ⊥ := by
    rw [CFSG.Open.genFittingLayer.eq_sSup]
    have hset : {L : Subgroup G | CFSG.Open.IsComponentOf L ⊤} = ∅ := by
      ext L
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact hnc L
    rw [hset, sSup_empty]
  have hFStar : CFSG.Open.genFittingFStar G = CFSG.pCore 3 G := by
    rw [CFSG.Open.genFittingFStar.eq_sup, genFittingFitting_eq_pCore hc, hlayer, sup_bot_eq]
  rw [← hFStar]
  exact CFSG.Adapters.generalized_fitting_self_centralizing G

theorem map_conj_jOf_eq_of_le_pCore (h : Hyp326 G n P) (hA : jOf P ≤ CFSG.pCore 3 G) (g : G) :
    (jOf P).map (MulAut.conj g).toMonoidHom = jOf P := by
  obtain ⟨hjP, hEA, hcard, huniq, -⟩ := jOf_spec h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine huniq _ ?_ (hEA.map (MulAut.conj g).toMonoidHom) ?_
  · rintro y ⟨x, hx, rfl⟩
    have hx' : g * x * g⁻¹ ∈ CFSG.pCore 3 G :=
      (CFSG.pCore_normal (p := 3) (G := G)).conj_mem x (hA hx) g
    simpa [MulAut.conj_apply] using pCore_le_sylow h.sylow hx'
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

theorem normalizer_jOf_eq_top_of_le_pCore (h : Hyp326 G n P)
    (hA : jOf P ≤ CFSG.pCore 3 G) : Subgroup.normalizer (jOf P : Set G) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => Subgroup.mem_normalizer_iff.mpr fun x => ?_
  have hmap := map_conj_jOf_eq_of_le_pCore h hA g
  have hmapinv := map_conj_jOf_eq_of_le_pCore h hA g⁻¹
  constructor
  · intro hx
    have hmem : (MulAut.conj g).toMonoidHom x ∈ (jOf P).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [hmap] at hmem
    simpa [MulAut.conj_apply] using hmem
  · intro hx
    have hx' : (MulAut.conj g).toMonoidHom x ∈ jOf P := by
      simpa [MulAut.conj_apply] using hx
    have hmem : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom x) ∈
        (jOf P).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx'
    rw [hmapinv] at hmem
    have hfix : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom x) = x := by
      simp [MulAut.conj_apply]
      group
    rwa [hfix] at hmem

theorem not_jOf_le_pCore (h : Hyp326 G n P) {M : Subgroup G}
    (hM : Subgroup.normalizer (jOf P : Set G) ≤ M) (hMtop : M ≠ ⊤) :
    ¬ jOf P ≤ CFSG.pCore 3 G := by
  intro hA
  exact hMtop (top_le_iff.mp ((normalizer_jOf_eq_top_of_le_pCore h hA).symm.le.trans hM))

theorem pCore_ne_bot_of_centralizer_le (h : Hyp326 G n P)
    (hcent : Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤ CFSG.pCore 3 G) :
    CFSG.pCore 3 G ≠ ⊥ := by
  intro hbot
  obtain ⟨e⟩ := h.wr
  have hcard := (zwr_card_center h.one_le e).1
  have hPbot : P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : x ∈ Subgroup.centralizer (CFSG.pCore 3 G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy1 : y = 1 := by simpa [hbot] using hy
      rw [hy1, one_mul, mul_one]
    simpa [hbot] using hcent hmem
  have hcardP : Nat.card ↥P = 1 := by rw [hPbot, Subgroup.card_bot]
  have hgt : 1 < 3 ^ (3 * n + 1) := Nat.one_lt_pow (by norm_num) (by omega)
  rw [hcardP] at hcard
  exact absurd hcard (ne_of_lt hgt)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
