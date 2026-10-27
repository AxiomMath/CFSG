module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bV
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod1

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_sT)

@[expose] def Vcar : Subgroup Ah where
  carrier := {g | ∃ l ∈ Vl, RepL l (g : P45)}
  mul_mem' := by
    rintro a b ⟨l, hl, hla⟩ ⟨m, hm, hmb⟩
    exact ⟨comp l m, Vl_mul l hl m hm, repL_mul hla hmb⟩
  one_mem' := ⟨idL, Vl_special.1, repL_one 45⟩
  inv_mem' := by
    intro a ha
    refine inv_mem_of_mul_closed (S := {g : Ah | ∃ l ∈ Vl, RepL l (g : P45)})
      ⟨idL, Vl_special.1, repL_one 45⟩ ?_ ha
    rintro a ⟨l, hl, hla⟩ b ⟨m, hm, hmb⟩
    exact ⟨comp l m, Vl_mul l hl m hm, repL_mul hla hmb⟩

theorem tpL_mem_Vl : ∀ p ∈ L0, tpL p ∈ Vl := by decide +kernel

theorem VA_le_Vcar : VA ≤ Vcar := by
  rw [VA, Subgroup.closure_le]
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨tpL p.val, tpL_mem_Vl p.val hp, repL_sT p⟩

theorem Vcar_le_VA : Vcar ≤ VA := by
  rintro g ⟨l, hl, hrep⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl
  have hi16 : i < 16 := by have := Vl_length; omega
  have hVl : Vl.getD i [] = Vl[i] := List.getD_eq_getElem _ _ hi
  have hw : ∀ j ∈ Vw.getD i [], j < 5 := by
    have hlen : Vw.length = 16 := by decide +kernel
    have hmem : Vw.getD i [] ∈ Vw := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    exact Vw_lt _ hmem
  have h1 := repL_prodA (Vw.getD i []) hw
  rw [Vw_check i hi16, hVl] at h1
  have : g = prodA (Vw.getD i []) := Subtype.ext (eq_of_repL hrep h1)
  rw [this]
  exact prodA_mem_VA _ hw

theorem VA_eq_Vcar : VA = Vcar := le_antisymm VA_le_Vcar Vcar_le_VA

theorem mem_VA_iff (g : Ah) : g ∈ VA ↔ ∃ l ∈ Vl, RepL l (g : P45) := by
  rw [VA_eq_Vcar]
  rfl

theorem VA_comm {a b : Ah} (ha : a ∈ VA) (hb : b ∈ VA) : a * b = b * a := by
  obtain ⟨l, hl, hla⟩ := (mem_VA_iff a).1 ha
  obtain ⟨m, hm, hmb⟩ := (mem_VA_iff b).1 hb
  apply Subtype.ext
  exact eq_of_repL (l := comp l m) (repL_mul hla hmb) (Vl_comm l hl m hm ▸ repL_mul hmb hla)

theorem VA_sq {a : Ah} (ha : a ∈ VA) : a * a = 1 := by
  obtain ⟨l, hl, hla⟩ := (mem_VA_iff a).1 ha
  apply Subtype.ext
  exact eq_of_repL (l := comp l l) (repL_mul hla hla) (Vl_sq l hl ▸ repL_one 45)

theorem VA_le_TAh : VA ≤ TAh := by
  intro a ha
  obtain ⟨l, hl, hrep⟩ := (mem_VA_iff a).1 ha
  obtain ⟨y, hy, hyrep⟩ := exists_T_of_mem_Tl (Vl_mem_Tl l hl)
  have : a = incl y := Subtype.ext (eq_of_repL hrep hyrep)
  rw [this]
  exact (mem_TAh_iff _).2 ⟨y, hy, rfl⟩

theorem VA_le_Bh : VA ≤ Bh :=
  VA_le_TAh.trans TAh_le_Bh

theorem VA_le_P2h : VA ≤ P2h :=
  VA_le_Bh.trans Bh_le_P2h

theorem card_VA_ge :
    16 ≤ Nat.card VA := by
  have h := length_le_card_of_nodup VA Vl_nodup (fun l hl => by
    obtain ⟨g, -, hrep⟩ := exists_That_of_mem_Thl (Vl_mem_Thl l hl)
    exact ⟨g, (mem_VA_iff g).2 ⟨l, hl, hrep⟩, hrep⟩)
  rw [Vl_length] at h
  exact h

@[expose] def wg : List ℕ := [1, 3, 2, 2]

theorem wg_check : sameSet (imgSet (evalAL wg) L0) L0 = true ∧
    ∀ l ∈ Thl, comp (comp (evalAL (invAL wg)) l) (evalAL wg) ∈ Thl → l ∈ Vl := by
  decide +kernel

theorem isSylowTwoOf_That_P2h :
    IsSylowTwoOf That P2h := by
  refine ⟨That_le_Bh.trans Bh_le_P2h, IsPGroup.of_card (n := 7) (by rw [card_That]; norm_num), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := That) (K := P2h)
  rw [inf_eq_left.2 (That_le_Bh.trans Bh_le_P2h), card_That, card_P2h] at h
  show ¬ 2 ∣ That.relIndex P2h
  omega

theorem pCoreOf_P2h_le :
    pCoreOf 2 P2h ≤ VA := by
  intro q hq
  have hqT : q ∈ That := pCoreOf_le_of_isSylowTwoOf isSylowTwoOf_That_P2h hq
  set g : Ah := ⟨wordAP wg, wordAP_mem wg⟩ with hg
  have hgP : g ∈ P2h := mem_P2h_of_repL (repL_wordAP wg) wg_check.1
  have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2h hgP
  have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ pCoreOf 2 P2h :=
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2h
      (P2h.inv_mem hgP)) q).1 hq
  have hqT' : g⁻¹ * q * g ∈ That := by
    have := pCoreOf_le_of_isSylowTwoOf isSylowTwoOf_That_P2h hq'
    simpa using this
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff q).1 hqT
  obtain ⟨l', hl', hrep'⟩ := (mem_That_iff _).1 hqT'
  have hinv : RepL (evalAL (invAL wg)) ((g⁻¹ : Ah) : P45) := by
    have : ((g⁻¹ : Ah) : P45) = wordAP (invAL wg) := by
      rw [wordAP_invAL]
      rfl
    rw [this]
    exact repL_wordAP _
  have h2 : RepL (comp (comp (evalAL (invAL wg)) l) (evalAL wg)) ((g⁻¹ * q * g : Ah) : P45) :=
    repL_mul (repL_mul hinv hrep) (repL_wordAP wg)
  have hl'eq := repL_unique h2 hrep'
  have hmem : comp (comp (evalAL (invAL wg)) l) (evalAL wg) ∈ Thl := by
    rw [hl'eq]
    exact hl'
  exact (mem_VA_iff q).2 ⟨l, wg_check.2 l hl hmem, hrep⟩

theorem pCoreOf_P2h_eq :
    pCoreOf 2 P2h = VA := by
  refine le_antisymm pCoreOf_P2h_le ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 VA_le_P2h
    (fun g hg => (Subgroup.mem_normalizer_iff.2 fun h =>
      ⟨fun hh => P2h_conj_VA hg hh, fun hh => by
        have := P2h_conj_VA (P2h.inv_mem hg) hh
        simpa [mul_assoc] using this⟩)) VA_isPGroup

end CFSG.Quasithin.H13.F431.U42Aut
