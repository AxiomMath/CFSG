module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Lat

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (Y P45)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45)

@[expose] def TAh : Subgroup Ah := That ⊓ Yh

theorem mem_TAh_iff (a : Ah) :
    a ∈ TAh ↔ ∃ y ∈ U42.T, incl y = a := by
  constructor
  · rintro ⟨hT, hY⟩
    obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl a).1 hY
    exact ⟨y, by rw [← comap_That]; exact hT, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨map_T_le_That (Subgroup.mem_map_of_mem _ hy), (mem_Yh_iff_incl _).2 ⟨y, rfl⟩⟩

theorem TAh_le_Bh : TAh ≤ Bh := inf_le_left.trans That_le_Bh

theorem TAh_isPGroup :
    IsPGroup 2 TAh := isSylowTwoOf_That_Bh.2.1.to_le inf_le_left

theorem conj_TAh {g : Ah}
    (hg : g ∈ Bh) {a : Ah} (ha : a ∈ TAh) : g * a * g⁻¹ ∈ TAh := by
  have inner : ∀ y : Y, incl y ∈ Bh → ∀ a ∈ TAh, incl y * a * (incl y)⁻¹ ∈ TAh := by
    intro y hy a ha
    obtain ⟨t, ht, rfl⟩ := (mem_TAh_iff a).1 ha
    have hyB : y ∈ U42.B0 := by rw [← comap_Bh]; exact hy
    have hyN : y ∈ Subgroup.normalizer (U42.T : Set Y) := by rw [U42.normalizer_T]; exact hyB
    refine (mem_TAh_iff _).2 ⟨y * t * y⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.1 hyN t).1 ht
  by_cases hgY : g ∈ Yh
  · obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl g).1 hgY
    exact inner y hg a ha
  · have hf : fhatA⁻¹ ∉ Yh := fun h => fhatA_not_mem_Yh (Yh.inv_mem_iff.1 h)
    have h1 : g * fhatA⁻¹ ∈ Yh := by
      rw [Subgroup.mul_mem_iff_of_index_two index_Yh]
      exact iff_of_false hgY hf
    obtain ⟨y, hy⟩ := (mem_Yh_iff_incl _).1 h1
    have hyB : incl y ∈ Bh := by
      rw [hy]
      exact Bh.mul_mem hg (Bh.inv_mem fhatA_mem_Bh)
    have hfa : fhatA * a * fhatA⁻¹ ∈ TAh :=
      ⟨That.mul_mem (That.mul_mem fhatA_mem_That ha.1) (That.inv_mem fhatA_mem_That),
        Yh_normal.conj_mem a ha.2 fhatA⟩
    have := inner y hyB _ hfa
    rw [hy] at this
    simpa [mul_assoc] using this

theorem Bh_le_normalizer_TAh :
    Bh ≤ Subgroup.normalizer (TAh : Set Ah) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact ⟨fun hh => conj_TAh hg hh, fun hh => by
    have := conj_TAh (Bh.inv_mem hg) hh
    simpa [mul_assoc] using this⟩

theorem TAh_le_pCoreOf :
    TAh ≤ pCoreOf 2 Bh :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 TAh_le_Bh Bh_le_normalizer_TAh TAh_isPGroup

theorem Thl_c3 : ∀ l ∈ Thl, comp (comp (comp c3L c3L) l) c3L ∈ Thl → l ∈ Tl := by
  decide +kernel

theorem c3A_mem_Bh : incl U42.c3Y ∈ Bh := by
  rw [← Subgroup.mem_comap, comap_Bh]
  exact U42.c3_mem_B0

theorem pCoreOf_le_TAh :
    pCoreOf 2 Bh ≤ TAh := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hnormal : (CFSG.Open.pCore 2 ↥Bh).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥Bh) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hle := hp.le_sylow_of_normal (A4.toSylow isSylowTwoOf_That_Bh)
  have hmemT : ∀ y' : ↥Bh, y' ∈ CFSG.Open.pCore 2 ↥Bh → (y' : Ah) ∈ That := fun y' hy' =>
    Subgroup.mem_subgroupOf.1 (hle hy')
  have hyT := hmemT y hy
  set c : ↥Bh := ⟨incl U42.c3Y, c3A_mem_Bh⟩ with hc
  have hy' : c⁻¹ * y * c ∈ CFSG.Open.pCore 2 ↥Bh := by
    have := hnormal.conj_mem y hy c⁻¹
    simpa using this
  have hy'T := hmemT _ hy'
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff _).1 hyT
  have hc3 : RepL c3L ((incl U42.c3Y : Ah) : P45) := U42.repL_c3
  have hc3i : RepL (comp c3L c3L) (((incl U42.c3Y : Ah) : P45)⁻¹) := U42.repL_c3_inv
  have hrep' : RepL (comp (comp (comp c3L c3L) l) c3L)
      ((((c⁻¹ * y * c : ↥Bh) : Ah)) : P45) := by
    have e : ((((c⁻¹ * y * c : ↥Bh) : Ah)) : P45) = ((incl U42.c3Y : Ah) : P45)⁻¹ *
        ((y : Ah) : P45) * ((incl U42.c3Y : Ah) : P45) := rfl
    rw [e]
    exact repL_mul (repL_mul hc3i hrep) hc3
  obtain ⟨l', hl', hrep''⟩ := (mem_That_iff _).1 hy'T
  have hmem : comp (comp (comp c3L c3L) l) c3L ∈ Thl := by
    have := repL_unique hrep' hrep''
    rw [this]
    exact hl'
  obtain ⟨g, hg, hgrep⟩ := exists_T_of_mem_Tl (Thl_c3 l hl hmem)
  exact (mem_TAh_iff _).2 ⟨g, hg, Subtype.ext (eq_of_repL hgrep hrep)⟩

theorem pCoreOf_Bh_eq :
    pCoreOf 2 Bh = TAh := le_antisymm pCoreOf_le_TAh TAh_le_pCoreOf

end CFSG.Quasithin.H13.F431.U42Aut
