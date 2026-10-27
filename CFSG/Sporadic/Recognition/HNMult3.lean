module

public import CFSG.Sporadic.Recognition.HNMult3Gens
public import CFSG.Sporadic.Recognition.HNMult3Words
public import CFSG.Sporadic.Recognition.CoverCubeTransfer

public section

namespace CFSG.Sporadic.Recognition.HNMult3

open CFSG.CosetTable CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.Recognition.CoverTransfer
  CFSG.Sporadic.GLQ.HNTwoRank CFSG.LieType.Multipliers Subgroup

attribute [local irreducible] Rg


noncomputable def gX (i : Fin 3) : Nsub := ⟨gN i, Subgroup.subset_closure ⟨i, rfl⟩⟩

theorem coe_gX (i : Fin 3) : (gX i : GLHN) = gN i := by
  unfold gX
  rfl

theorem closure_range_gX : Subgroup.closure (Set.range gX) = ⊤ := by
  have e : Set.range gX = Subtype.val ⁻¹' Set.range gN := by
    ext ⟨g, hg⟩
    simp only [Set.mem_range, Set.mem_preimage]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← coe_gX, hy]⟩, fun ⟨y, hy⟩ => ⟨y, Subtype.ext (by
      rw [coe_gX]; exact hy)⟩⟩
  rw [e]
  exact closure_closure_coe_preimage

theorem coe_lift_gX (w : FreeGroup (Fin 3)) :
    ((FreeGroup.lift gX w : Nsub) : GLHN) = FreeGroup.lift gN w := by
  have : Nsub.subtype.comp (FreeGroup.lift gX) = FreeGroup.lift gN :=
    FreeGroup.ext_hom _ _ fun i => by simp [coe_gX]
  exact congrArg (fun φ : FreeGroup (Fin 3) →* GLHN => φ w) this

theorem hn3_facts'
    (h : (∀ r ∈ hn3Rels, FreeGroup.lift gN (FreeGroup.mk r) = 1) ∧
      (∀ i, hn3Ord i = 0 → FreeGroup.lift gN (FreeGroup.mk (hn3Cw i)) = gN i) ∧
      (∀ i, hn3Ord i ≠ 0 → gN i ^ hn3Ord i = 1)) :
    (∀ r ∈ hn3Rels, FreeGroup.lift gX (FreeGroup.mk r) = 1) ∧
    (∀ i, FreeGroup.lift gX (FreeGroup.mk (hn3Cw i)) = gX i) ∧
    (∀ i, hn3Ord i ≠ 0 → gX i ^ hn3Ord i = 1) := by
  obtain ⟨hR, hA, hB⟩ := h
  refine ⟨fun r hr => Subtype.ext ?_, fun i => Subtype.ext ?_, fun i hi => Subtype.ext ?_⟩
  · rw [coe_lift_gX, hR r hr, Subgroup.coe_one]
  · rw [coe_lift_gX, coe_gX]
    by_cases h0 : hn3Ord i = 0
    · exact hA i h0
    · rw [hn3Cw, ite_eq_right h0, show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl,
        FreeGroup.lift_apply_of]
  · rw [Subgroup.coe_pow, Subgroup.coe_one, coe_gX]
    exact hB i hi

theorem hn3Ord_cases (i : Fin 3) (hi : hn3Ord i ≠ 0) : hn3Ord i = 2 := by
  fin_cases i <;> simp_all [hn3Ord]

theorem factorization_58320 : (Nat.factorization 58320) 3 = 6 := by
  rw [show 58320 = 3 ^ 6 * 80 by norm_num, Nat.factorization_mul (by positivity) (by positivity),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem ker_eq_bot_of_hn3
    (hfacts : (∀ r ∈ hn3Rels, FreeGroup.lift gN (FreeGroup.mk r) = 1) ∧
      (∀ i, hn3Ord i = 0 → FreeGroup.lift gN (FreeGroup.mk (hn3Cw i)) = gN i) ∧
      (∀ i, hn3Ord i ≠ 0 → gN i ^ hn3Ord i = 1))
    (hcard : 58320 ≤ Nat.card Nsub)
    (hcover : Finite (PG 3 hn3Cover) ∧ Nat.card (PG 3 hn3Cover) ≤ 58320)
    {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* GLHN) (hNle : Nsub ≤ π.range)
    (hsyl : (Nat.card π.range).factorization 3 ≤ 6) (hC : π.ker ≤ center E)
    (hp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  obtain ⟨hR, hw, hB⟩ := hn3_facts' hfacts
  obtain ⟨hfin, hle⟩ := hcover
  have hfin' : Finite (PG 3 (cover₃Words hn3Rels hn3Cw hn3Ord)) := hfin
  have hge : Nat.card Nsub ≤ Nat.card (PG 3 (cover₃Words hn3Rels hn3Cw hn3Ord)) :=
    card_le_card_cover₃ closure_range_gX hR hw hB
  have hcardN : Nat.card Nsub = 58320 := le_antisymm (hge.trans hle) hcard
  have hsylN : (Nat.card π.range).factorization 3 ≤ (Nat.card Nsub).factorization 3 := by
    rw [hcardN, factorization_58320]
    exact hsyl
  refine ker_eq_bot_of_sylow_subgroup π hC hp Nsub hNle hsylN ?_
  intro M _ _ φ hφ hc hpg hd
  refine ker_eq_bot_of_cover₃ (g := gX) (R := hn3Rels) (cw := hn3Cw) (ord := hn3Ord)
    closure_range_gX hR (fun i h0 => ⟨?_, hw i⟩)
    (fun i hi => ⟨?_, hB i hi, ?_⟩) hfin' (hle.trans hcardN.ge) φ hφ hc hpg hd
  · rw [hn3Cw, ite_eq_left h0]
    exact mk_commWords_mem_commutator _
  · rw [hn3Cw, ite_eq_right hi]
  · rw [hn3Ord_cases i hi]
    decide

end CFSG.Sporadic.Recognition.HNMult3
