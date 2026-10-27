module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECheck
public import CFSG.Sporadic.Fi24.OctadsInputs
public import CFSG.Fischer.NoF25.Octads
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24K

open CFSG.Fischer CFSG.Sporadic.Fi24

@[expose] def fi24ESbF (k : Fin 4) (i : Fin 24) : Fin 24 :=
  Fin.ofNat 24 (fi24ESb[k.val]!)[i.val]!

@[expose] def fi24EZ0F : Finset (Fin 24) := {0, 3, 13, 15}

theorem fi24ESbF_pair : ∀ i j : Fin 24, i ≠ j →
    ∃ k : Fin 4, fi24ESbF k i ∉ [i, j] ∨ fi24ESbF k j ∉ [i, j] := by
  decide +kernel

@[expose] def fi24ETetB (k : Fin 4) (a b c : Fin 24) : Bool :=
  let L := [0, a, b, c]
  (L.any fun x => !L.contains (fi24ESbF k x)) && L.any fun x => L.contains (fi24ESbF k x)

@[expose] def fi24EZB (a : Fin 24) : Bool := a == 3 || a == 13 || a == 15

@[expose] def fi24ETetAll (a b c : Fin 24) : Bool :=
  a == 0 || b == 0 || c == 0 || a == b || a == c || b == c ||
    (fi24EZB a && fi24EZB b && fi24EZB c) ||
    fi24ETetB 0 a b c || fi24ETetB 1 a b c || fi24ETetB 2 a b c || fi24ETetB 3 a b c

theorem fi24ESbF_tetrad : ∀ a b c : Fin 24, fi24ETetAll a b c = true := by
  decide +kernel

theorem fi24ESbF_Z0 : ∀ k : Fin 4, fi24EZ0F.image (fi24ESbF k) = fi24EZ0F ∨
    symmDiff (fi24EZ0F.image (fi24ESbF k)) fi24EZ0F = octF 586 ∨
    symmDiff (fi24EZ0F.image (fi24ESbF k)) fi24EZ0F = octF 572 := by
  decide +kernel

section Fam

variable {Y : Type*} [Group Y] (d : Fin 24 → Y) (hcomm : ∀ i j, d i * d j = d j * d i)
  (hsq : ∀ i, d i * d i = 1) (σ : Fin 4 → Equiv.Perm (Fin 24))
  (hσ : ∀ (k : Fin 4) (i : Fin 24), (σ k i).val = (fi24ESb[k.val]!)[i.val]!)

include hσ in
theorem map_eq_image_fi24ESbF (k : Fin 4) (U : Finset (Fin 24)) :
    U.map (σ k).toEmbedding = U.image (fi24ESbF k) := by
  rw [Finset.map_eq_image]
  refine Finset.image_congr fun i _ => ?_
  change σ k i = fi24ESbF k i
  rw [fi24ESbF, ← hσ k i, Fin.ofNat_val_eq_self]

include hsq in
private theorem famProd_symmDiff_eq_one {A B : Finset (Fin 24)}
    (h : famProd d hcomm A = famProd d hcomm B) : famProd d hcomm (symmDiff A B) = 1 := by
  rw [famProd_symmDiff d hcomm hsq, h, ← famProd_symmDiff d hcomm hsq, symmDiff_self,
    Finset.bot_eq_empty, famProd_empty]

variable (hsmall : ∀ S : Finset (Fin 24), S.card ≤ 6 → famProd d hcomm S = 1 → S = ∅)

include hsq hσ hsmall in
theorem famProd_pair_false {U : Finset (Fin 24)} (hU : U.card = 2)
    (h : ∀ k, famProd d hcomm (U.map (σ k).toEmbedding) = famProd d hcomm U) : False := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hU
  obtain ⟨k, hkij⟩ := fi24ESbF_pair i j hij
  have hk : ({i, j} : Finset (Fin 24)).image (fi24ESbF k) ≠ {i, j} := by
    intro he
    have hi : fi24ESbF k i ∈ ({i, j} : Finset (Fin 24)) := by
      rw [← he]
      exact Finset.mem_image_of_mem _ (by simp)
    have hj : fi24ESbF k j ∈ ({i, j} : Finset (Fin 24)) := by
      rw [← he]
      exact Finset.mem_image_of_mem _ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkij
    tauto
  have hD := famProd_symmDiff_eq_one d hcomm hsq (h k)
  rw [map_eq_image_fi24ESbF σ hσ] at hD
  have hc := card_symmDiff_add_two_mul (({i, j} : Finset (Fin 24)).image (fi24ESbF k)) {i, j}
  have hi : (({i, j} : Finset (Fin 24)).image (fi24ESbF k)).card ≤ ({i, j} : Finset _).card :=
    Finset.card_image_le
  exact hk (Finset.symmDiff_eq_empty.1 (hsmall _ (by omega) hD))

include hsq hσ hsmall in
theorem famProd_tetrad_eq {V : Finset (Fin 24)} (hV : V.card = 4) (h0 : 0 ∈ V)
    (h : ∀ k, famProd d hcomm (V.map (σ k).toEmbedding) = famProd d hcomm V) :
    V = fi24EZ0F := by
  by_contra hne
  obtain ⟨a, b, c, hab, hac, hbc, he3⟩ := Finset.card_eq_three.1
    (show (V.erase 0).card = 3 by rw [Finset.card_erase_of_mem h0, hV])
  have hV' : V = {0, a, b, c} := by rw [← Finset.insert_erase h0, he3]
  have hne0 : ∀ x ∈ ({a, b, c} : Finset (Fin 24)), x ≠ 0 := fun x hx =>
    (Finset.mem_erase.1 (he3 ▸ hx)).1
  have hL : ∀ z, z ∈ [0, a, b, c] ↔ z ∈ V := fun z => by
    rw [hV']
    simp
  have hZ : ¬((a = 3 ∨ a = 13 ∨ a = 15) ∧ (b = 3 ∨ b = 13 ∨ b = 15) ∧
      (c = 3 ∨ c = 13 ∨ c = 15)) := by
    rintro ⟨ha, hb, hc⟩
    refine hne (Finset.eq_of_subset_of_card_le ?_ (by rw [hV]; decide))
    intro x hx
    rw [hV'] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [fi24EZ0F, Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl | rfl | rfl <;> tauto
  have ha0 := hne0 a (by simp)
  have hb0 := hne0 b (by simp)
  have hc0 := hne0 c (by simp)
  have h4 : fi24ETetB 0 a b c = true ∨ fi24ETetB 1 a b c = true ∨ fi24ETetB 2 a b c = true ∨
      fi24ETetB 3 a b c = true := by
    have h := fi24ESbF_tetrad a b c
    simp only [fi24ETetAll, fi24EZB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ha0, hb0,
      hc0, hab, hac, hbc, false_or, or_assoc, and_assoc] at h
    exact h.resolve_left hZ
  obtain ⟨k, hk⟩ : ∃ k : Fin 4, fi24ETetB k a b c = true := by
    rcases h4 with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  rw [fi24ETetB, Bool.and_eq_true, List.any_eq_true, List.any_eq_true] at hk
  obtain ⟨⟨x, hx, hxo⟩, ⟨y, hy, hyi⟩⟩ := hk
  have hxo' : fi24ESbF k x ∉ V := by
    rw [← hL]
    simpa using hxo
  have hyi' : fi24ESbF k y ∈ V := by
    rw [← hL]
    simpa using hyi
  rw [hL] at hx hy
  have hk : V.image (fi24ESbF k) ≠ V := fun he =>
    hxo' (he ▸ Finset.mem_image_of_mem _ hx)
  have hm : (V.image (fi24ESbF k) ∩ V).Nonempty :=
    ⟨_, Finset.mem_inter.2 ⟨Finset.mem_image_of_mem _ hy, hyi'⟩⟩
  have hD := famProd_symmDiff_eq_one d hcomm hsq (h k)
  rw [map_eq_image_fi24ESbF σ hσ] at hD
  have hc := card_symmDiff_add_two_mul (V.image (fi24ESbF k)) V
  have hi : (V.image (fi24ESbF k)).card ≤ V.card := Finset.card_image_le
  have hp : 0 < (V.image (fi24ESbF k) ∩ V).card :=
    Finset.card_pos.2 hm
  exact hk (Finset.symmDiff_eq_empty.1 (hsmall _ (by omega) hD))

include hsq hσ in
theorem famProd_Z0 (hoct : ∀ O ∈ octads, famProd d hcomm O = 1) (k : Fin 4) :
    famProd d hcomm (fi24EZ0F.map (σ k).toEmbedding) = famProd d hcomm fi24EZ0F := by
  rw [map_eq_image_fi24ESbF σ hσ]
  have key : ∀ j : Fin 759, symmDiff (fi24EZ0F.image (fi24ESbF k)) fi24EZ0F = octF j →
      famProd d hcomm (fi24EZ0F.image (fi24ESbF k)) = famProd d hcomm fi24EZ0F := by
    intro j hj
    have e : fi24EZ0F.image (fi24ESbF k) = symmDiff (octF j) fi24EZ0F := by
      rw [← hj, symmDiff_symmDiff_cancel_right]
    rw [e, famProd_symmDiff d hcomm hsq,
      hoct _ (Finset.mem_image_of_mem octF (Finset.mem_univ j)), one_mul]
  rcases fi24ESbF_Z0 k with h | h | h
  · rw [h]
  · exact key _ h
  · exact key _ h

end Fam

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Fi24K
