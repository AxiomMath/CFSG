
module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ERigidBase
public import CFSG.Sporadic.Fi24.Local
public import CFSG.Sporadic.Fi24.OctadsInputs
public import CFSG.Fischer.NoF25.Octads
public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.Sporadic.Fi24.OctadData
public import CFSG.Sporadic.Fi24.Fi24EFacts
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open CFSG.Sporadic.Th CFSG.Sporadic.Fi24 CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "bP" => @famProd R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm

section Prod

theorem bbarProd_empty : bP ∅ = 1 :=
  @famProd_empty R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm

theorem bbarProd_insert {a : Fin 24} {S : Finset (Fin 24)} (ha : a ∉ S) :
    bP (insert a S) = bbar a * bP S :=
  @famProd_insert R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm a S ha

theorem bbarProd_singleton (a : Fin 24) : bP {a} = bbar a :=
  @famProd_singleton R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm a

theorem bbarProd_symmDiff (S T : Finset (Fin 24)) : bP (symmDiff S T) = bP S * bP T :=
  @famProd_symmDiff R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm bbar_sq S T

theorem bbarProd_mul_self (S : Finset (Fin 24)) : bP S * bP S = 1 := by
  rw [← bbarProd_symmDiff, symmDiff_self, Finset.bot_eq_empty, bbarProd_empty]

theorem bbarProd_inv (S : Finset (Fin 24)) : (bP S)⁻¹ = bP S :=
  inv_eq_of_mul_eq_one_right (bbarProd_mul_self S)

theorem bbarProd_mem (S : Finset (Fin 24)) : bP S ∈ fi24EB := by
  induction S using Finset.induction_on with
  | empty =>
    rw [bbarProd_empty]
    exact one_mem _
  | insert a S ha ih =>
    rw [bbarProd_insert ha]
    exact mul_mem (Subgroup.subset_closure ⟨a, rfl⟩) ih

theorem exists_bbarProd {x : R} (hx : x ∈ fi24EB) : ∃ S, bP S = x := by
  unfold fi24EB at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨{i}, bbarProd_singleton i⟩
  | one => exact ⟨∅, bbarProd_empty⟩
  | mul x y _ _ hx hy =>
    obtain ⟨S, rfl⟩ := hx
    obtain ⟨T, rfl⟩ := hy
    exact ⟨symmDiff S T, bbarProd_symmDiff S T⟩
  | inv x _ hx =>
    obtain ⟨S, rfl⟩ := hx
    exact ⟨S, (bbarProd_inv S).symm⟩

theorem fi24EB_mul_comm {x y : R} (hx : x ∈ fi24EB) (hy : y ∈ fi24EB) : x * y = y * x :=
  (comm_fi24EB (fun i => fi24EB_comm hy i) hx).symm

theorem bbar_not_mem_JR (i : Fin 24) : bbar i ∉ JR := not_mem_JR_of_mem_D24 (cls_mem _)

theorem bbarProd_mem_JR_iff (S : Finset (Fin 24)) :
    bP S ∈ JR ↔ Even S.card := by
  induction S using Finset.induction_on with
  | empty =>
    rw [bbarProd_empty, Finset.card_empty]
    exact ⟨fun _ => ⟨0, rfl⟩, fun _ => one_mem _⟩
  | insert a S ha ih =>
    rw [bbarProd_insert ha, Subgroup.mul_mem_iff_of_index_two index_JR, ih,
      Finset.card_insert_of_notMem ha, Nat.even_add_one]
    exact ⟨fun h he => bbar_not_mem_JR a (h.2 he),
      fun h => ⟨fun h' => absurd h' (bbar_not_mem_JR a), fun he => absurd he h⟩⟩

end Prod

section Rel

theorem bbarProd_octad {O : Finset (Fin 24)} (hO : O ∈ octads) : bP O = 1 := by
  obtain ⟨r, τ, hr, rfl⟩ := htrans_octads O hO
  rw [@famProd_map R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm τ r hr,
    famProd_octF_zero, mul_one, mul_inv_cancel]

theorem exists_octad_of_card_five {Y : Finset (Fin 24)} (hY : Y.card = 5) :
    ∃ O ∈ octads, Y ⊆ O := by
  obtain ⟨O, ⟨hO, hYO⟩, -⟩ := steiner_octads Y hY
  exact ⟨O, hO, hYO⟩

theorem bbarProd_ne_one {S : Finset (Fin 24)} (hS : S.card = 2 ∨ S.card = 4 ∨ S.card = 6) :
    bP S ≠ 1 := by
  rcases hS with h | h | h
  · exact @famProd_ne_one_of_card_two R inferInstance (Fin 24) inferInstance inferInstance bbar
      bbar_comm bbar_sq bbar_injective S h
  · exact @famProd_ne_one_of_card_four R inferInstance (Fin 24) inferInstance inferInstance bbar
      bbar_comm bbar_sq bbar_pair S h
  · exact @famProd_ne_one_of_card_six R inferInstance (Fin 24) inferInstance inferInstance bbar
      bbar_comm bbar_sq bbar_injective bbar_pair octads (fun _ hO => card_of_mem_octads hO)
      (fun _ hY => exists_octad_of_card_five hY) (fun _ hO => bbarProd_octad hO) S h

theorem eq_of_bbarProd_eq {S T : Finset (Fin 24)} (hc : (symmDiff S T).card ≤ 6)
    (h : bP S = bP T) : S = T := by
  have hD : bP (symmDiff S T) = 1 := by
    rw [bbarProd_symmDiff, h, bbarProd_mul_self]
  have he : Even (symmDiff S T).card := (bbarProd_mem_JR_iff _).1 (by rw [hD]; exact one_mem _)
  by_contra hne
  have h0 : (symmDiff S T).card ≠ 0 := fun h0 =>
    hne (Finset.symmDiff_eq_empty.1 (Finset.card_eq_zero.1 h0))
  obtain ⟨k, hk⟩ := he
  exact bbarProd_ne_one (by omega) hD

theorem bbarProd_inj {S T : Finset (Fin 24)} (hS : S.card ≤ 3) (hT : T.card ≤ 3)
    (h : bP S = bP T) : S = T :=
  eq_of_bbarProd_eq (by have := card_symmDiff_add_two_mul S T; omega) h

theorem le_card_fi24EB : 4096 ≤ Nat.card fi24EB := by
  let P : Finset (Finset (Fin 24)) :=
    Finset.powersetCard 1 Finset.univ ∪ Finset.powersetCard 3 Finset.univ
  have hmem : ∀ S ∈ P, S.card = 1 ∨ S.card = 3 := by
    intro S hS
    rcases Finset.mem_union.1 hS with h | h
    · exact Or.inl (Finset.mem_powersetCard.1 h).2
    · exact Or.inr (Finset.mem_powersetCard.1 h).2
  have hP : P.card = 2048 := by
    rw [Finset.card_union_of_disjoint, Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
    · rfl
    · rw [Finset.disjoint_left]
      intro S h1 h3
      rw [Finset.mem_powersetCard] at h1 h3
      omega
  have hodd : ∀ S ∈ P, bP S ∉ JR := by
    intro S hS
    rw [bbarProd_mem_JR_iff]
    rcases hmem S hS with h | h <;> rw [h] <;> decide
  have hpar : ∀ (S : P) (b : Bool), (if b = true then bbar 0 else 1) * bP S.1 ∈ JR ↔ b = true := by
    intro S b
    cases b
    · rw [if_neg Bool.false_ne_true, one_mul]
      exact iff_of_false (hodd S.1 S.2) Bool.false_ne_true
    · rw [if_pos rfl, Subgroup.mul_mem_iff_of_index_two index_JR]
      exact iff_of_true (iff_of_false (bbar_not_mem_JR 0) (hodd S.1 S.2)) rfl
  have hgB : ∀ p : P × Bool, (if p.2 = true then bbar 0 else 1) * bP p.1.1 ∈ fi24EB := by
    rintro ⟨S, b⟩
    refine mul_mem ?_ (bbarProd_mem _)
    split_ifs
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact one_mem _
  let f : P × Bool → fi24EB := fun p => ⟨(if p.2 = true then bbar 0 else 1) * bP p.1.1, hgB p⟩
  have hf : Function.Injective f := by
    rintro ⟨S, b⟩ ⟨T, c⟩ h
    have h' := Subtype.ext_iff.1 h
    simp only [f] at h'
    have hbc : b = c := by
      have e1 := hpar S b
      rw [h'] at e1
      exact Bool.eq_iff_iff.2 (e1.symm.trans (hpar T c))
    subst hbc
    rw [Prod.mk.injEq]
    have h3 : ∀ U ∈ P, U.card ≤ 3 := fun U hU => by rcases hmem U hU with h | h <;> omega
    exact ⟨Subtype.ext (bbarProd_inj (h3 _ S.2) (h3 _ T.2) (mul_left_cancel h')), rfl⟩
  calc 4096 = Nat.card (P × Bool) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe, hP, Nat.card_eq_fintype_card,
          Fintype.card_bool]
    _ ≤ Nat.card fi24EB := Nat.card_le_card_of_injective f hf

end Rel

section E

@[expose] noncomputable def fi24E : Subgroup CFSG.Sporadic.Fi24.J := fi24EB.comap jR

theorem mem_fi24E_iff {g : CFSG.Sporadic.Fi24.J} : g ∈ fi24E ↔ jR g ∈ fi24EB := Iff.rfl

theorem map_fi24E : fi24E.map jR = JR ⊓ fi24EB := by
  rw [fi24E, Subgroup.map_comap_eq, range_jR]

theorem fi24E_sq : ∀ e ∈ fi24E, e ^ 2 = 1 := by
  intro e he
  obtain ⟨S, hS⟩ := exists_bbarProd (mem_fi24E_iff.1 he)
  apply jR_injective
  rw [map_pow, map_one, pow_two, ← hS, bbarProd_mul_self]

end E

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
