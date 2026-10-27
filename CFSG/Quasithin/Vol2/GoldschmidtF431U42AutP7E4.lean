module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7E16
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NOrbD
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Z

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def Bl1 : List PL :=
  [idL, Th2.getD 0 [], Th2.getD 3 [], comp (Th2.getD 0 []) (Th2.getD 3 [])]

@[expose] def Bl2 : List PL :=
  [idL, Th2.getD 1 [], Th2.getD 2 [], comp (Th2.getD 1 []) (Th2.getD 2 [])]

theorem Bl_check : (idL ∈ Bl1 ∧ (∀ a ∈ Bl1, ∀ b ∈ Bl1, comp a b ∈ Bl1) ∧ (∀ a ∈ Bl1, a ∈ Al2) ∧
    Bl1.Nodup ∧ Bl1.length = 4) ∧
    (idL ∈ Bl2 ∧ (∀ a ∈ Bl2, ∀ b ∈ Bl2, comp a b ∈ Bl2) ∧ (∀ a ∈ Bl2, a ∈ Al2) ∧
    Bl2.Nodup ∧ Bl2.length = 4) := by
  decide +kernel

theorem Bl_th : (∀ l ∈ Bl1, l ≠ idL → l ∈ Th2) ∧ (∀ l ∈ Bl2, l ≠ idL → l ∈ Th2) ∧
    (∀ l ∈ Th2, l ∈ Bl1 ∨ l ∈ Bl2) ∧ (∀ l ∈ Bl1, l ∈ Bl2 → l = idL) := by
  decide +kernel

theorem E4_pair : ∀ a ∈ Th2, ∀ b ∈ Th2, a ≠ b → comp a b ∈ Th2 →
    (a ∈ Bl1 ∧ b ∈ Bl1) ∨ (a ∈ Bl2 ∧ b ∈ Bl2) := by
  decide +kernel

theorem Bl_gens : (∀ l ∈ Bl1, l ∈ spanL [Th2.getD 0 [], Th2.getD 3 []]) ∧
    (∀ l ∈ Bl2, l ∈ spanL [Th2.getD 1 [], Th2.getD 2 []]) ∧
    (∀ g ∈ [Th2.getD 0 [], Th2.getD 3 []], g ∈ Bl1) ∧
    (∀ g ∈ [Th2.getD 1 [], Th2.getD 2 []], g ∈ Bl2) := by
  decide +kernel

theorem Ttl_normB : ∀ l ∈ Ttl, NormL l [Th2.getD 0 [], Th2.getD 3 []] Bl1 ∧
    NormL l [Th2.getD 1 [], Th2.getD 2 []] Bl2 := by
  decide +kernel

theorem Ttl_nd : Ttl.Nodup ∧ Ttl.length = 64 := by decide +kernel

@[expose] def B1h : Subgroup Ah := listSub Bl1 Bl_check.1.1 Bl_check.1.2.1

@[expose] def B2h : Subgroup Ah := listSub Bl2 Bl_check.2.1 Bl_check.2.2.1

theorem Bl_thl : (∀ l ∈ Bl1, l ∈ Thl) ∧ ∀ l ∈ Bl2, l ∈ Thl :=
  ⟨fun l hl => A2_check.2.2.2.1 l (Bl_check.1.2.2.1 l hl),
    fun l hl => A2_check.2.2.2.1 l (Bl_check.2.2.2.1 l hl)⟩

theorem B1h_le_A2h : B1h ≤ A2h := fun _ ⟨l, hl, hrep⟩ => ⟨l, Bl_check.1.2.2.1 l hl, hrep⟩

theorem B2h_le_A2h : B2h ≤ A2h := fun _ ⟨l, hl, hrep⟩ => ⟨l, Bl_check.2.2.2.1 l hl, hrep⟩

theorem card_B1h : Nat.card ↥B1h = 4 := by
  rw [B1h, card_listSub Bl_check.1.2.2.2.1 Bl_thl.1]
  exact Bl_check.1.2.2.2.2

theorem card_B2h : Nat.card ↥B2h = 4 := by
  rw [B2h, card_listSub Bl_check.2.2.2.2.1 Bl_thl.2]
  exact Bl_check.2.2.2.2.2

noncomputable def Tt : Subgroup Ah := That ⊓ Subgroup.centralizer ({t0A} : Set Ah)

theorem Tt_le_That : Tt ≤ That := inf_le_left

theorem Ttl_rep {g : Ah} (hg : g ∈ Tt) : ∃ l ∈ Ttl, RepL l (g : P45) := by
  obtain ⟨hgT, hgc⟩ := hg
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff g).1 hgT
  refine ⟨l, List.mem_filter.2 ⟨hl, ?_⟩, hrep⟩
  have h : g * t0A = t0A * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
  have := comp_comm_of_comm (v := t0A) (g := g) repL_t0A hrep h
  simpa using this

theorem exists_Tt_of_Ttl {l : PL} (hl : l ∈ Ttl) : ∃ g ∈ Tt, RepL l (g : P45) := by
  obtain ⟨hlT, hlc⟩ := List.mem_filter.1 hl
  obtain ⟨g, hg, hrep⟩ := exists_That_of_mem_Thl hlT
  refine ⟨g, ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, hrep⟩
  have hc : comp l (Tl.getD 20 []) = comp (Tl.getD 20 []) l := by simpa using hlc
  exact comm_of_comp_comm (v := t0A) (g := g) repL_t0A hrep hc

theorem Tt_le_normalizer_A2h : Tt ≤ Subgroup.normalizer (A2h : Set Ah) := by
  intro g hg
  obtain ⟨l, hl, hrep⟩ := Ttl_rep hg
  exact mem_normalizer_A2h_of_Ttl hl hrep

theorem N_P1h_A2h :
    P1h ⊓ Subgroup.normalizer (A2h : Set Ah) = Tt := by
  have hle : Tt ≤ P1h ⊓ Subgroup.normalizer (A2h : Set Ah) :=
    fun g hg => ⟨Bh_le_P1h (That_le_Bh hg.1), Tt_le_normalizer_A2h hg⟩
  have hge : 64 ≤ Nat.card ↥Tt := by
    have := length_le_card_of_nodup Tt Ttl_nd.1 fun l hl => exists_Tt_of_Ttl hl
    rwa [Ttl_nd.2] at this
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_N1_A2]; exact hge)).symm

theorem Tt_normalizer {g : Ah} (hg : g ∈ Tt) :
    g ∈ Subgroup.normalizer (B1h : Set Ah) ∧ g ∈ Subgroup.normalizer (B2h : Set Ah) := by
  obtain ⟨l, hl, hrep⟩ := Ttl_rep hg
  have h := Ttl_normB l hl
  exact ⟨mem_normalizer_of_normL (h1 := Bl_check.1.1) (hmul := Bl_check.1.2.1) Bl_thl.1
      Bl_gens.2.2.1 Bl_gens.1 hrep h.1,
    mem_normalizer_of_normL (h1 := Bl_check.2.1) (hmul := Bl_check.2.2.1) Bl_thl.2
      Bl_gens.2.2.2 Bl_gens.2.1 hrep h.2⟩

end CFSG.Quasithin.H13.F431.U42Aut
