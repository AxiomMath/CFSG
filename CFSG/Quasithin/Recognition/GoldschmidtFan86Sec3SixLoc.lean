module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Fan40
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3SixCop
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalGcirc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Arc.three {a b c d : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hcd : Γ.Adj c d)
    (hac : a ≠ c) (hbd : b ≠ d) : Arc Γ 3 where
  vert i := if i = 0 then a else if i = 1 then b else if i = 2 then c else d
  adj i hi := by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [hab, hbc, hcd]
  nb i hi := by
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [hac, hbd]

theorem relIndex_ne_zero_of_finite {G : Type*} [Group G] (H K : Subgroup G) [Finite K] :
    H.relIndex K ≠ 0 := by
  have h := Subgroup.relIndex_mul_card (H := H) (K := K)
  have : 0 < Nat.card K := Nat.card_pos
  intro h0
  rw [h0, zero_mul] at h
  omega

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem not_inf_le_right (h40 : Fan40 F) {a b c d : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (hcd : Γ.Adj c d) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ nbrStab Γ G b ⊓ nbrStab Γ G c ≤ nbrStab Γ G d := by
  intro hle
  obtain ⟨w, hw, hwc⟩ := F.exists_adj_ne d c
  refine h40 3 (by norm_num) (by norm_num) ⟨Arc.three hab hbc hcd hac hbd, w, ?_, ?_, ?_⟩
  · simpa [Arc.three] using hw
  · simpa [Arc.three] using hwc
  · intro g hg
    rw [F.mem_stabRange_iff_nbrStab (by norm_num)
      (fun m _ hm => (Arc.three hab hbc hcd hac hbd).adj m hm)
      (fun m _ hm => (Arc.three hab hbc hcd hac hbd).nb m hm)] at hg
    have hgb : g ∈ nbrStab Γ G b := by simpa [Arc.three] using hg 1 (by norm_num) (by norm_num)
    have hgc : g ∈ nbrStab Γ G c := by simpa [Arc.three] using hg 2 (by norm_num) (by norm_num)
    exact mem_nbrStab.1 (hle ⟨hgb, hgc⟩) w hw

theorem not_inf_le_left (h40 : Fan40 F) {a b c d : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (hcd : Γ.Adj c d) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ nbrStab Γ G b ⊓ nbrStab Γ G c ≤ nbrStab Γ G a := by
  intro hle
  exact F.not_inf_le_right h40 hcd.symm hbc.symm hab.symm hbd.symm hac.symm
    (by rwa [inf_comm])

theorem relIndex_le_cidx {v a : V} (hva : Γ.Adj v a) {S : Subgroup G}
    (hS : S ≤ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) :
    (nbrStab Γ G v).relIndex S ≤
      (nbrStab Γ G v).relIndex (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := by
  refine Subgroup.relIndex_le_of_le_right hS ?_
  have h := F.relIndex_nbrStab_mem_two_four hva
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  omega

theorem relIndex_le_two {v a : V} (hva : Γ.Adj v a) (hv : pval Γ v = 3) {S : Subgroup G}
    (hS : S ≤ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) :
    (nbrStab Γ G v).relIndex S ≤ 2 := by
  have := F.relIndex_le_cidx hva hS
  rwa [F.relIndex_nbrStab_eq_two hva hv] at this

theorem relIndex_le_four {v a : V} (hva : Γ.Adj v a) {S : Subgroup G}
    (hS : S ≤ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) :
    (nbrStab Γ G v).relIndex S ≤ 4 := by
  have := F.relIndex_le_cidx hva hS
  have h := F.relIndex_nbrStab_mem_two_four hva
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  omega

theorem relIndex_nbrStab_smul (g : G) (v a : V) :
    (nbrStab Γ G (g • v)).relIndex (MulAction.stabilizer G (g • v) ⊓ MulAction.stabilizer G (g • a))
      = (nbrStab Γ G v).relIndex (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) := by
  have h1 : nbrStab Γ G (g • v) = (nbrStab Γ G v).map (MulAut.conj g).toMonoidHom := by
    ext h
    rw [F.mem_nbrStab_smul_iff, Subgroup.mem_map]
    constructor
    · intro hh
      exact ⟨g⁻¹ * h * g, hh, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
  rw [h1, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem relIndex_eq_four_of_not_gcirc {α β : V} (hαβ : Γ.Adj α β) {g : G}
    (hg : g ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) (hng : g ∉ Gcirc Γ G α β) :
    (nbrStab Γ G α).relIndex (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 4 := by
  obtain ⟨H, hHeq, -, -, hHiff⟩ := F.exists_gcircSubgroup hαβ
  have h24 := F.relIndex_nbrStab_mem_two_four hαβ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h24
  rcases h24 with h2 | h4
  · exfalso
    apply hng
    have hHE := hHiff.2 h2
    rw [← hHeq]
    show g ∈ H
    rw [hHE]
    exact hg
  · exact h4

theorem exists_mem_nbrStab_smul_eq {u v : V} (huv : Γ.Adj u v) (hu : pval Γ u = 3)
    (hnle : ¬ nbrStab Γ G v ≤ nbrStab Γ G u)
    (hc : (nbrStab Γ G v).relIndex (MulAction.stabilizer G v ⊓ MulAction.stabilizer G u) =
      pval Γ v - 1) {w w' : V} (hw : Γ.Adj v w) (hwu : w ≠ u) (hw' : Γ.Adj v w') (hw'u : w' ≠ u) :
    ∃ k ∈ nbrStab Γ G u, k • w = w' := by
  set E : Subgroup G := MulAction.stabilizer G u ⊓ MulAction.stabilizer G v with hE
  have hKvE : nbrStab Γ G v ≤ E := fun k hk =>
    ⟨(F.nbrStab_le_edge v huv.symm hk).2, (F.nbrStab_le_edge v huv.symm hk).1⟩
  rw [inf_comm] at hc
  have hstab : MulAction.stabilizer G w ⊓ E = nbrStab Γ G v := by
    refine le_antisymm (fun e he => ?_) fun k hk =>
      ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hk w hw), hKvE hk⟩
    exact F.fix_two_nbrs hw huv.symm hwu (MulAction.mem_stabilizer_iff.1 he.1)
      (MulAction.mem_stabilizer_iff.1 he.2.1)
  have horb : MulAction.orbit ↥E w = Γ.neighborSet v \ {u} := by
    have hsub : MulAction.orbit ↥E w ⊆ Γ.neighborSet v \ {u} := by
      rintro _ ⟨⟨e, he⟩, rfl⟩
      refine ⟨F.adj_smul_of_mem_stabilizer he.2 hw, fun h => hwu ?_⟩
      have h1 : e • w = u := h
      have h2 : e • u = u := MulAction.mem_stabilizer_iff.1 he.1
      exact MulAction.injective e (h1.trans h2.symm)
    have hcard : (MulAction.orbit ↥E w).ncard = pval Γ v - 1 := by
      rw [← FanTree.relIndex_stabilizer_eq_ncard_orbit E w, ← Subgroup.inf_relIndex_right, hstab]
      exact hc
    have hfin := (F.ncard_neighborSet_le v).2
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin.sdiff
    rw [hcard, Set.ncard_sdiff_singleton_of_mem (s := Γ.neighborSet v) (a := u) huv.symm]
    exact le_of_eq rfl
  have hw'orb : w' ∈ MulAction.orbit ↥E w := by
    rw [horb]
    exact ⟨hw', hw'u⟩
  obtain ⟨⟨e, he⟩, hew⟩ := hw'orb
  have hew' : e • w = w' := hew
  by_cases heK : e ∈ nbrStab Γ G u
  · exact ⟨e, heK, hew'⟩
  obtain ⟨b₀, hb₀v, hb₀u⟩ : ∃ b ∈ nbrStab Γ G v, b ∉ nbrStab Γ G u := by
    by_contra h
    push Not at h
    exact hnle h
  obtain ⟨a, haE, ha⟩ := Subgroup.relIndex_eq_two_iff.1 (F.relIndex_nbrStab_eq_two huv hu)
  have hxor : ∀ y ∈ E, y ∉ nbrStab Γ G u → y * a ∈ nbrStab Γ G u := by
    intro y hy hyu
    rcases ha y hy with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 hyu
  have h1 := hxor e he heK
  have h2 := hxor b₀ (hKvE hb₀v) hb₀u
  have hk : e * b₀⁻¹ ∈ nbrStab Γ G u := by
    have := (nbrStab Γ G u).mul_mem h1 ((nbrStab Γ G u).inv_mem h2)
    simpa [mul_assoc] using this
  refine ⟨e * b₀⁻¹, hk, ?_⟩
  have hb₀w : b₀⁻¹ • w = w := by
    rw [inv_smul_eq_iff]
    exact (mem_nbrStab.1 hb₀v w hw).symm
  rw [mul_smul, hb₀w]
  exact hew'

end FanTree

end CFSG.Quasithin.Fan86
