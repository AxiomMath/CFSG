module

public import CFSG.Sporadic.Recognition.McLCentralizerInputs
public import CFSG.Sporadic.SmallOddCore.McLLocal

public noncomputable section

namespace CFSG.Sporadic.Recognition.McLCentralizer

open Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

theorem isPerfect_of_simple_nonabelian {K : Type*} [Group K] (hs : IsSimpleGroup K)
    (h : ∃ a b : K, a * b ≠ b * a) : Group.IsPerfect K := by
  refine Group.isPerfect_def.2 ?_
  rcases hs.eq_bot_or_eq_top_of_normal (commutator K) with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator K :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rwa [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  · exact h1

theorem isPerfect_of_sq_eq {E K : Type*} [Group E] [Group K] [Group.IsPerfect K] (ρ : E →* K)
    (hρ : Function.Surjective ρ) {z g : E} (hz : z ∈ center E) (hz2 : z ^ 2 = 1)
    (hker : ρ.ker = zpowers z) (hg : g ^ 2 = z) : Group.IsPerfect E := by
  set D : Subgroup E := ⁅(⊤ : Subgroup E), ⊤⁆ with hD
  have hmap : D.map ρ = ⊤ := by
    rw [hD, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.2 hρ]
    exact Group.IsPerfect.commutator_eq_top
  have hsplit : ∀ e : E, ∃ d ∈ D, d⁻¹ * e ∈ ρ.ker := by
    intro e
    have : ρ e ∈ D.map ρ := by rw [hmap]; trivial
    obtain ⟨d, hd, hde⟩ := Subgroup.mem_map.1 this
    exact ⟨d, hd, by rw [MonoidHom.mem_ker, map_mul, map_inv, hde, inv_mul_cancel]⟩
  have hzD : z ∈ D := by
    obtain ⟨d, hd, hk⟩ := hsplit g
    rw [hker, mem_zpowers_iff] at hk
    obtain ⟨n, hn⟩ := hk
    have hg' : g = d * z ^ n := by rw [hn]; group
    have hcen : z ^ n ∈ center E := Subgroup.zpow_mem _ hz n
    have hc : Commute d (z ^ n) := Subgroup.mem_center_iff.1 hcen d
    have hzn2 : (z ^ n) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
    have hzd : z = d ^ 2 := by rw [← hg, hg', hc.mul_pow, hzn2, mul_one]
    rw [hzd]
    exact pow_mem hd 2
  refine Group.isPerfect_def.2 (eq_top_iff.2 fun e _ => ?_)
  obtain ⟨d, hd, hk⟩ := hsplit e
  have hkD : d⁻¹ * e ∈ D := by
    rw [hker] at hk
    exact (zpowers_le.2 hzD) hk
  have he : e = d * (d⁻¹ * e) := by group
  rw [he]
  exact D.mul_mem hd hkD

@[expose] def mooreLift
    (i : ℕ) : mclCt :=
  ((mooreWord i).map mclCGen).prod

theorem mooreWord_lt (i : ℕ) : ∀ j ∈ mooreWord i, j < 2 := by
  match i with
  | 0 => simp [mooreWord]
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | n + 7 => simp [mooreWord]

theorem size_mclCTabs : mclCTabs.size = 2 := Array.size_ofFn

theorem getElem_mclCTabs {k : ℕ} (hk : k < 2) : mclCTabs[k]! = natArr (mclCentTbl (k + 5)) := by
  rw [getElem!_pos mclCTabs k (by rw [size_mclCTabs]; exact hk)]
  simp [mclCTabs]

theorem size_natArr_mclCentTbl (k : ℕ) : (natArr (mclCentTbl k)).size = 275 := by
  simp [natArr, mclCentTbl, hexT]

theorem tabRep_mclCTabs :
    ∀ k < mclCTabs.size, TabRep mclCTabs[k]! ((mclCGen k : mclCt) : Equiv.Perm (Fin 275)) := by
  intro k hk
  rw [size_mclCTabs] at hk
  rw [getElem_mclCTabs hk]
  have hrep := co2Rep_natArr_iff.2 (rep_tp (mclX_basic.2.2.2.2.2 k hk))
  have hg : ((mclCGen k : mclCt) : Equiv.Perm (Fin 275)) = tp 275 (mclCentTbl (k + 5)) := by
    simp [mclCGen, hk]
  rw [hg]
  exact ⟨size_natArr_mclCentTbl _, fun i => hrep i⟩

theorem tabRep_liftTab :
    TabRep liftTab ((mooreLift 4 : mclCt) : Equiv.Perm (Fin 275)) := by
  have h := tabRep_wordTabS (f := fun k => ((mclCGen k : mclCt) : Equiv.Perm (Fin 275)))
    tabRep_mclCTabs (mooreWord 4) (fun j hj => by rw [size_mclCTabs]; exact mooreWord_lt 4 j hj)
  have e : ((mooreLift 4 : mclCt) : Equiv.Perm (Fin 275)) =
      ((mooreWord 4).map fun k => ((mclCGen k : mclCt) : Equiv.Perm (Fin 275))).prod := by
    rw [mooreLift]
    have hp := map_list_prod mclCt.subtype ((mooreWord 4).map mclCGen)
    rw [List.map_map] at hp
    exact hp
  rw [e]
  exact h

theorem mooreLift_sq
    (hL : liftCheck = true) :
    mooreLift 4 ^ 2 = (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) := by
  have h2 := tabRep_liftTab.comp tabRep_liftTab
  have hT0 : TabRep mclT0Arr mclT0 :=
    ⟨size_natArr_mclCentTbl 4, fun i => rep_mclT0 i⟩
  have hc : comp 275 liftTab liftTab = mclT0Arr := by simpa [liftCheck] using hL
  have := (h2.eq_iff hT0).1 hc
  apply Subtype.ext
  rw [pow_two]
  exact this

theorem mclRho_ker_eq :
    mclRho.ker = zpowers (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr mclT0_mem_ker) ?_
  rw [mclRho_range.2, Nat.card_zpowers, Subgroup.orderOf_mk, mclT0_facts.2.1]

theorem mclT0_mem_center :
    (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) ∈ center mclCt := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).2

theorem mclRho_ker_le_center :
    mclRho.ker ≤ center mclCt := by
  rw [mclRho_ker_eq, zpowers_le]
  exact mclT0_mem_center

theorem mclT0_sq :
    (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) ^ 2 = 1 := by
  apply Subtype.ext
  have := pow_orderOf_eq_one mclT0
  rwa [mclT0_facts.2.1] at this

theorem isSimple_range :
    IsSimpleGroup mclRho.range ∧ ∃ a b : mclRho.range, a * b ≠ b * a := by
  obtain ⟨hs, hnab⟩ := mclX_simple
  have hrange := mclRho_range.1
  exact ⟨by rw [hrange]; exact hs, by rw [hrange]; exact hnab⟩

theorem center_mclCt :
    center mclCt = mclRho.ker := by
  obtain ⟨hs, hnab⟩ := isSimple_range
  have hcen : center mclRho.range = ⊥ :=
    CFSG.Sporadic.SuzOddCore.center_eq_bot_of_simple' hs hnab
  have h := center_eq_ker_of_surjective mclRho.rangeRestrict mclRho.rangeRestrict_surjective hcen
    (by rw [MonoidHom.ker_rangeRestrict]; exact mclRho_ker_le_center)
  rwa [MonoidHom.ker_rangeRestrict] at h

theorem isPerfect_mclCt
    (hL : liftCheck = true) :
    Group.IsPerfect mclCt := by
  obtain ⟨hs, hnab⟩ := isSimple_range
  have : Group.IsPerfect mclRho.range := isPerfect_of_simple_nonabelian hs hnab
  refine isPerfect_of_sq_eq mclRho.rangeRestrict mclRho.rangeRestrict_surjective
    (z := (⟨mclT0, mclT0_mem_Ct⟩ : mclCt)) (g := mooreLift 4) mclT0_mem_center mclT0_sq ?_
    (mooreLift_sq hL)
  rw [MonoidHom.ker_rangeRestrict]
  exact mclRho_ker_eq

end CFSG.Sporadic.Recognition.McLCentralizer
