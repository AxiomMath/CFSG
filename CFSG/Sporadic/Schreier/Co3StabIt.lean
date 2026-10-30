module

public import CFSG.Sporadic.Schreier.Co3Sylow
public import CFSG.Sporadic.Schreier.Co3OrbitTCheck
public import CFSG.Certificates.Kernel.Spor.PointChainCard
public import CFSG.Certificates.NativeSetOrbit

public noncomputable section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native CFSG.KS.PCC
open scoped Pointwise

theorem co3StabItArrs_size : co3StabItArrs.size = 8 := by simp [co3StabItArrs]

@[expose] def co3StabItChain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3StabItArrs 8 co3StabItArrs_size.ge
    (co3FinList 276 (by decide) co3StabItBase) (by decide) (wordsArr 8 8 co3StabItDerivations)

theorem co3StabIt_facts :
    ChainCheckFacts 276 (co3StabItArrs.extract 0 8) co3StabItArrs co3StabItBaseArr
      (wordsArr 8 8 co3StabItDerivations) 4 :=
  chainCheckFacts co3OrbitT_check.1

theorem co3StabItArrays :
    ChainArrays co3StabItChain (co3StabItArrs.extract 0 8) co3StabItArrs co3StabItBaseArr
      (wordsArr 8 8 co3StabItDerivations) :=
  chainArrays_ofArrays co3StabIt_facts.strong_inv

theorem co3StabIt_valid : ValidSchreier co3StabItChain :=
  (validSchreier_of_chainOK co3StabItArrays (by norm_num) co3OrbitT_check.1).1

theorem co3StabItChain_baseCount : co3StabItChain.baseCount = 7 := rfl

@[expose] def co3ItB (l : ℕ) : Fin 276 :=
  ⟨[35, 41, 43, 79, 80, 108].getD l 108 % 276, Nat.mod_lt _ (by decide)⟩

theorem co3StabItChain_take {i : ℕ} (hi : i ≤ 6) :
    ∀ b ∈ co3StabItChain.base.toList.take i, ∃ k < i, b = co3ItB k := by
  have e : co3StabItChain.base.toList.take i = (List.range i).map co3ItB := by
    rw [co3StabItChain, RawSchreierDatum.ofArrays_base_toList]
    interval_cases i <;> rfl
  intro b hb
  rw [e, List.mem_map] at hb
  obtain ⟨k, hk, rfl⟩ := hb
  exact ⟨k, List.mem_range.1 hk, rfl⟩

theorem co3StabItChain_base_get (i : Fin co3StabItChain.baseCount) (hi : (i : ℕ) < 6) :
    co3StabItChain.base.get i = co3ItB i := by
  obtain ⟨i, hi'⟩ := i
  change i < 7 at hi'
  interval_cases i <;> rfl

theorem co3StabItChain_original :
    co3StabItChain.originalSubgroup = co3P := by
  have hle : co3StabItChain.originalSubgroup ≤ co3P := by
    rw [co3StabItChain, ofArrays_originalSubgroup, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : ℕ) < co3StabItArrs.size := by rw [co3StabItArrs_size]; exact k.2
    exact mem_co3P_of_sift (rep_permOfArr (co3StabIt_facts.strong_inv k hk)).1
      (co3OrbitT_check.2.2.1 k k.2)
  have hcard : Nat.card co3StabItChain.originalSubgroup = 495766656000 := by
    rw [card_originalSubgroup_of_chainOK co3StabItArrays (by norm_num) co3OrbitT_check.1,
      co3OrbitT_check.2.1]
    rfl
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_co3P])

theorem co3StabIt_levSize (i : ℕ) (hi : i < 7) :
    (ChainArrays.lev 276 co3StabItArrs co3StabItBaseArr i).pts.size =
      [276, 275, 162, 105, 64, 3, 2].getD i 0 := by
  have hb : co3StabItBaseArr.size = 7 := by decide
  have hs : i < (rawLevels 276 co3StabItArrs co3StabItBaseArr).size := by
    simp only [rawLevels, Array.size_ofFn, hb]
    exact hi
  rw [← co3OrbitT_check.2.1, rawOrbitSizes, ChainArrays.lev, getElem!_pos _ i hs,
    List.getD_eq_getElem _ _ (by simpa using hs)]
  simp

theorem mem_co3StabIt_level
    {i : ℕ} (hi : i ≤ 6) {g : Equiv.Perm (Fin 276)} (hg : g ∈ co3P)
    (hfix : ∀ k < i, g (co3ItB k) = co3ItB k) : g ∈ co3StabItChain.levelSubgroup i := by
  rw [co3StabItChain.mem_levelSubgroup_iff co3StabIt_valid i (by rw [co3StabItChain_baseCount]; omega),
    co3StabItChain_original]
  refine ⟨hg, fun b hb => ?_⟩
  obtain ⟨k, hk, rfl⟩ := co3StabItChain_take hi b hb
  exact hfix k hk

theorem co3StabIt_level5 {x : Fin 276}
    (hx : x ∈ co3StabItChain.orbitPoints ⟨5, by rw [co3StabItChain_baseCount]; omega⟩)
    (hI : (x : ℕ) ∈ co3ItNat) : x = co3ItB 5 := by
  have hF := co3StabIt_facts
  have hA := co3StabItArrays
  obtain ⟨hk, hpts, -⟩ := hA.orbitPoints_spec hF (by rw [co3StabItChain_baseCount]; omega) hx
  have hsz : (ChainArrays.lev 276 co3StabItArrs co3StabItBaseArr 5).pts.size = 3 :=
    co3StabIt_levSize 5 (by norm_num)
  rw [hsz] at hk
  have hv := hA.levPts_val hF (i := 5) (by rw [co3StabItChain_baseCount]; omega) (by rw [hsz]; exact hk)
  rw [hpts] at hv
  have h0 : (ChainArrays.lev 276 co3StabItArrs co3StabItBaseArr 5).pos[(x : ℕ)]! = 0 :=
    co3OrbitT_check.2.2.2 _ hk (by
      change (ChainArrays.lev 276 co3StabItArrs co3StabItBaseArr 5).pts[_]! ∈ co3ItNat
      rw [← hv]
      exact hI)
  have hroot := (hA.levelFacts hF (i := 5) (by rw [co3StabItChain_baseCount]; omega)).root
  rw [h0] at hv
  apply Fin.ext
  rw [hv, hroot]
  rfl

theorem co3StabIt_card_level6 :
    Nat.card (co3StabItChain.levelSubgroup 6) = 2 := by
  have h := co3StabItChain.level_card_eq_orbit_mul_next co3StabIt_valid
    ⟨6, by rw [co3StabItChain_baseCount]; omega⟩
  have h7 : co3StabItChain.levelSubgroup (6 + 1) = ⊥ :=
    co3StabItChain.levelSubgroup_terminal_eq_bot co3StabIt_valid
  have ho := (validSchreier_of_chainOK co3StabItArrays (by norm_num) co3OrbitT_check.1).2
    ⟨6, by rw [co3StabItChain_baseCount]; omega⟩
  rw [co3StabItChain.orbitSize_eq_card] at ho
  rw [show (rawLevels 276 co3StabItArrs co3StabItBaseArr)[((⟨6, by decide⟩ : Fin 7) : ℕ)]!.pts.size
      = 2 from co3StabIt_levSize 6 (by norm_num)] at ho
  change Nat.card (co3StabItChain.levelSubgroup 6) =
    Nat.card (co3StabItChain.orbitPoints ⟨6, _⟩) * Nat.card (co3StabItChain.levelSubgroup (6 + 1)) at h
  rw [h, ho, h7, Subgroup.card_bot]

@[expose] def co3ItStab : Subgroup (Equiv.Perm (Fin 276)) :=
  (MulAction.stabilizer co3P (finSet 276 co3ItNat)).map co3P.subtype

theorem mem_co3ItStab {g : Equiv.Perm (Fin 276)} :
    g ∈ co3ItStab ↔ g ∈ co3P ∧ g • finSet 276 co3ItNat = finSet 276 co3ItNat := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hs⟩
    exact ⟨⟨g, hg⟩, hs, rfl⟩

theorem co3ItStab_mem_It {g : Equiv.Perm (Fin 276)} (hg : g ∈ co3ItStab) {x : Fin 276}
    (hx : (x : ℕ) ∈ co3ItNat) : ((g x : Fin 276) : ℕ) ∈ co3ItNat := by
  have hs := (mem_co3ItStab.1 hg).2
  have h : g • x ∈ g • finSet 276 co3ItNat := Set.smul_mem_smul_set (by simpa [finSet] using hx)
  rw [hs] at h
  simpa [finSet] using h

@[expose] def co3ItRest (l : ℕ) : Finset (Fin 276) :=
  Finset.univ.filter fun x => (x : ℕ) ∈ co3ItNat ∧ ∀ k < l, x ≠ co3ItB k

theorem co3ItRest_card {l : ℕ} (hl : l < 5) : (co3ItRest l).card = 12 - l := by
  interval_cases l <;> decide

theorem co3ItB_mem {l : ℕ} (hl : l < 6) : ((co3ItB l : Fin 276) : ℕ) ∈ co3ItNat := by
  interval_cases l <;> decide

theorem co3ItB_ne {k l : ℕ} (hl : l < 6) (hk : k < l) : co3ItB l ≠ co3ItB k := by
  interval_cases l <;> interval_cases k <;> decide

theorem orbit_sub_co3ItRest {l : ℕ} (hl : l < 5) :
    MulAction.orbit (Gs co3ItStab co3ItB l) (co3ItB l) ⊆ ↑(co3ItRest l) := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := mem_orbit_Gs.1 hy
  obtain ⟨hgH, hfix⟩ := (mem_Gs l g).1 hg
  simp only [co3ItRest, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  refine ⟨co3ItStab_mem_It hgH (co3ItB_mem (by omega)), fun k hk e => ?_⟩
  rw [← hfix k hk] at e
  exact co3ItB_ne (by omega) hk (g.injective e)

theorem orbit_ncard_le {l : ℕ} (hl : l < 5) :
    (MulAction.orbit (Gs co3ItStab co3ItB l) (co3ItB l)).ncard ≤ 12 - l := by
  rw [← co3ItRest_card hl, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (orbit_sub_co3ItRest hl)

theorem orbit5_ncard_le :
    (MulAction.orbit (Gs co3ItStab co3ItB 5) (co3ItB 5)).ncard ≤ 1 := by
  have hsub : MulAction.orbit (Gs co3ItStab co3ItB 5) (co3ItB 5) ⊆ {co3ItB 5} := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := mem_orbit_Gs.1 hy
    obtain ⟨hgH, hfix⟩ := (mem_Gs 5 g).1 hg
    have hP := (mem_co3ItStab.1 hgH).1
    have hL := mem_co3StabIt_level (by norm_num) hP hfix
    have hx : g (co3ItB 5) ∈ co3StabItChain.orbitPoints ⟨5, by rw [co3StabItChain_baseCount]; omega⟩ := by
      rw [co3StabItChain.orbitPoints_eq_orbit, co3StabItChain_base_get _ (by norm_num)]
      exact ⟨⟨g, hL⟩, rfl⟩
    exact co3StabIt_level5 hx (co3ItStab_mem_It hgH (co3ItB_mem (by norm_num)))
  calc _ ≤ ({co3ItB 5} : Set (Fin 276)).ncard := Set.ncard_le_ncard hsub
    _ = 1 := Set.ncard_singleton _

theorem card_Gs6_le :
    Nat.card (Gs co3ItStab co3ItB 6) ≤ 2 := by
  rw [← co3StabIt_card_level6]
  refine Subgroup.card_le_of_le fun g hg => ?_
  obtain ⟨hgH, hfix⟩ := (mem_Gs 6 g).1 hg
  exact mem_co3StabIt_level le_rfl (mem_co3ItStab.1 hgH).1 hfix

theorem card_co3ItStab_le :
    Nat.card co3ItStab ≤ 190080 := by
  rw [card_chain co3ItStab co3ItB 6]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have h0 := orbit_ncard_le (l := 0) (by norm_num)
  have h1 := orbit_ncard_le (l := 1) (by norm_num)
  have h2 := orbit_ncard_le (l := 2) (by norm_num)
  have h3 := orbit_ncard_le (l := 3) (by norm_num)
  have h4 := orbit_ncard_le (l := 4) (by norm_num)
  have h5 := orbit5_ncard_le
  have h6 := card_Gs6_le
  calc _ ≤ 12 * 11 * 10 * 9 * 8 * 1 * 2 := by gcongr <;> assumption
    _ = 190080 := by norm_num

theorem co3It_orbit_ge :
    2608200 ≤ (Set.range fun g : co3P => g • finSet 276 co3ItNat).ncard := by
  have hidx := MulAction.index_stabilizer co3P (finSet 276 co3ItNat)
  have hmul := (MulAction.stabilizer co3P (finSet 276 co3ItNat)).card_mul_index
  have hcard : Nat.card (MulAction.stabilizer co3P (finSet 276 co3ItNat)) = Nat.card co3ItStab :=
    (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  rw [card_co3P, hcard] at hmul
  change 2608200 ≤ (MulAction.orbit co3P (finSet 276 co3ItNat)).ncard
  rw [← hidx]
  have hle := card_co3ItStab_le
  by_contra hlt
  push Not at hlt
  have : Nat.card co3ItStab * (MulAction.stabilizer co3P (finSet 276 co3ItNat)).index ≤
      190080 * 2608199 := Nat.mul_le_mul hle (by omega)
  omega

end CFSG.Sporadic.Schreier.Co3
