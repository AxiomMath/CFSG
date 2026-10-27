module

public import CFSG.Timmesfeld.Bridge.RootSetsConn3
public import CFSG.Timmesfeld.Bridge.Asc72Unitary

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

namespace Step6

variable {G : Type} [Group G] {D : Set G} {a b c x z : G} {P : Subgroup G}

theorem not_mulEquiv_psu3 (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P)
    {n : ℕ} (hn : 2 ≤ n)
    (e : lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃* CFSG.Theory.Comparator.PSU3Model n) :
    False := by
  have := hC.setting.finite
  set X := lsub D x P with hX
  set R := CFSG.solvableRadical X with hR
  set π := QuotientGroup.mk' R with hπ
  have hK := h.isBenderGroup hB hC
  have hS' := h.quotient_setup hC
  set L : Set X := {w | (w : G) ∈ D ∧ (w : G) ∈ P} with hL
  have hLE : ∀ w ∈ L, π w ∈ π '' lclass D x P := fun w hw =>
    ⟨w, h.mem_classIn hC hw.1 hw.2, rfl⟩
  have hL2 : ∀ w ∈ π '' L, w * w = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    exact hS'.oddT.mul_self_eq_one (hLE w hw)
  have hLc : (π '' L).Pairwise Commute := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ -
    have huv : Commute u v := Subtype.ext (h.commute_of_mem hC hu.1 hv.1 hu.2 hv.2).eq
    exact huv.map π
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (isPGroup_closure_of_pairwise hLc hL2).exists_le_sylow
  have hcen : ∀ w ∈ π '' L,
      w ∈ (Subgroup.center (Q : Subgroup (X ⧸ R))).map (Q : Subgroup (X ⧸ R)).subtype := by
    intro w hw
    have hwQ : w ∈ Q := hQ (Subgroup.subset_closure hw)
    refine ⟨⟨w, hwQ⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hwQ (hL2 w hw) g g.2).eq.symm
  have ht : orderOf (π ⟨x, mem_lsub_x⟩) = 2 :=
    hS'.oddT.orderOf_eq_two ⟨_, mem_classIn_self _ x, rfl⟩
  apply Asc72.closure_insert_center_ne_top_of_psu3 hn e Q ht
  have htop : Subgroup.closure (π '' (X.subtype ⁻¹' insert x {y | y ∈ D ∧ y ∈ P})) = ⊤ := by
    have h1 := closure_preimage_subtype_eq_top (N := X) (S := insert x {y | y ∈ D ∧ y ∈ P})
      (fun w hw => Subgroup.subset_closure hw) rfl
    rw [← MonoidHom.map_closure, h1, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective R
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  rcases hw with hwx | hwL
  · have hw' : w = ⟨x, mem_lsub_x⟩ := Subtype.ext hwx
    rw [hw']
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (hcen _ ⟨w, hwL, rfl⟩))

theorem psl2_or_sz (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P) :
    (∃ n, 2 ≤ n ∧ Nonempty (lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃*
      CFSG.Theory.Comparator.PSL2Model n)) ∨
    (∃ n, 1 ≤ n ∧ Nonempty (lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃*
      CFSG.Theory.Comparator.SzModel n)) := by
  rcases h.isBenderGroup hB hC with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact Or.inl ⟨n, hn, ⟨e⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e⟩⟩
  · exact (h.not_mulEquiv_psu3 hB hC hn e).elim

end Step6

end CFSG.Timmesfeld.Bridge
