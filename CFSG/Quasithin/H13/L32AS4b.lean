module

public import CFSG.Quasithin.H13.L32ASecSplit

public section

namespace CFSG.Quasithin.H6

theorem isoMod_cases_of_h65 (h65 : VolI_H_6_5) {M : Type} [AddGroup M] [Finite M]
    {ρ : Γ →* AddMonoid.End M} (h2 : ∀ m : M, m + m = 0)
    (hfaith : ∀ g : Γ, (∀ m : M, ρ g m = m) → g = 1) {m : M} (hmT : ∀ t ∈ borel, ρ t m = m)
    (hgen : AddSubgroup.closure (Set.range fun g : Γ => ρ g m) = ⊤)
    (hl : Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m = y}) = 4) {x : Γ}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    (IsoMod ρ ρV ∧ Nat.card M = 4 * Nat.card {y : M // ρ x y = y}) ∨
      (IsoMod ρ ρCore ∧ Nat.card M = 16 * Nat.card {y : M // ρ x y = y}) ∨
      (IsoMod ρ ρSt ∧ Nat.card M = 64 * Nat.card {y : M // ρ x y = y}) ∨
      (IsoMod ρ (prodRep ρV ρSt) ∧ Nat.card M = 256 * Nat.card {y : M // ρ x y = y}) ∨
      (IsoMod ρ (prodRep ρCore ρSt) ∧ Nat.card M = 1024 * Nat.card {y : M // ρ x y = y}) := by
  obtain ⟨-, hcases⟩ := h65 M ρ h2 hfaith m hmT hgen hl
  rcases hcases with h | h | h | h | h
  · refine Or.inr (Or.inl ⟨h, ?_⟩)
    rw [h.card_eq, h.card_fix_eq x, card_core, card_fix_core x hx3 hx1]
  · refine Or.inr (Or.inr (Or.inl ⟨h, ?_⟩))
    rw [h.card_eq, h.card_fix_eq x, card_st, card_fix_st x hx3 hx1]
  · refine Or.inl ⟨h, ?_⟩
    rw [h.card_eq, h.card_fix_eq x, card_v3, card_fix_v3 x hx3 hx1]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h, ?_⟩)))
    rw [h.card_eq, h.card_fix_eq x, card_fix_prodRep x, Nat.card_prod, card_v3, card_st,
      card_fix_v3 x hx3 hx1, card_fix_st x hx3 hx1]
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h, ?_⟩)))
    rw [h.card_eq, h.card_fix_eq x, card_fix_prodRep x, Nat.card_prod, card_core, card_st,
      card_fix_core x hx3 hx1, card_fix_st x hx3 hx1]

end CFSG.Quasithin.H6

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.H6

variable {G : Type} [Group G]

namespace SecMod

variable {L X Y : Subgroup G} {θ : ↥L →* Γ}

theorem h65_cases [Finite G] (D : SecMod L X Y θ) [(Y.subgroupOf X).Normal] (h65 : VolI_H_6_5)
    {m : G} (hm : m ∈ X)
    (hmT : ∀ l : ↥L, θ l ∈ H6.borel → (l : G) * m * (l : G)⁻¹ * m⁻¹ ∈ Y)
    (hgen : ∀ s ∈ X,
      s ∈ Subgroup.closure ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (Y : Set G)))
    {W : Subgroup G}
    (hW : W = Subgroup.closure ({y | ∃ l : ↥L, θ l ∈ Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪
      (Y : Set G)))
    (hWY : Y.relIndex W = 4) {x : ↥L} (hx3 : θ x ^ 3 = 1) (hx1 : θ x ≠ 1) {C : Subgroup G}
    (hC : ∀ s, s ∈ C ↔ s ∈ X ∧ (x : G) * s * (x : G)⁻¹ * s⁻¹ ∈ Y) :
    ∃ ρ : Γ →* AddMonoid.End (Additive (↥X ⧸ Y.subgroupOf X)),
      (∀ (l : ↥L) (s : ↥X), ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
        Additive.ofMul (QuotientGroup.mk (D.conjX l s))) ∧
      ((IsoMod ρ ρV ∧ Y.relIndex X = 4 * Y.relIndex C) ∨
        (IsoMod ρ ρCore ∧ Y.relIndex X = 16 * Y.relIndex C) ∨
        (IsoMod ρ ρSt ∧ Y.relIndex X = 64 * Y.relIndex C) ∨
        (IsoMod ρ (prodRep ρV ρSt) ∧ Y.relIndex X = 256 * Y.relIndex C) ∨
        (IsoMod ρ (prodRep ρCore ρSt) ∧ Y.relIndex X = 1024 * Y.relIndex C)) := by
  classical
  set N := Y.subgroupOf X with hNdef
  obtain ⟨ρ, hρmk⟩ := D.exists_rep
  refine ⟨ρ, hρmk, ?_⟩
  have : Finite (Additive (↥X ⧸ N)) := Finite.of_equiv _ Additive.ofMul
  set m0 : Additive (↥X ⧸ N) := Additive.ofMul (QuotientGroup.mk ⟨m, hm⟩) with hm0
  have h2 : ∀ y : Additive (↥X ⧸ N), y + y = 0 := by
    intro y
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective y
    induction q using QuotientGroup.induction_on with
    | H s =>
    rw [← ofMul_mul, ← QuotientGroup.mk_mul, ← ofMul_one, ← QuotientGroup.mk_one]
    congr 1
    rw [D.mk_eq_mk_iff]
    have := D.sq _ s.2
    simpa [pow_two] using this
  have hfaith : ∀ g : Γ, (∀ y : Additive (↥X ⧸ N), ρ g y = y) → g = 1 := by
    intro g hg
    obtain ⟨l, rfl⟩ := D.surj g
    apply D.faithful l
    intro s hs
    have h1 := hg (Additive.ofMul (QuotientGroup.mk ⟨s, hs⟩))
    rw [hρmk] at h1
    have h3 := Additive.ofMul.injective h1
    rw [D.mk_eq_mk_iff, coe_conjX] at h3
    exact h3
  have hmT' : ∀ t ∈ H6.borel, ρ t m0 = m0 := by
    intro t ht
    obtain ⟨l, rfl⟩ := D.surj t
    rw [hm0, hρmk]
    congr 1
    rw [D.mk_eq_mk_iff, coe_conjX]
    exact hmT l ht
  have hmkY : ∀ (z : G) (hz : z ∈ Y),
      (Additive.ofMul (QuotientGroup.mk ⟨z, D.le hz⟩ : ↥X ⧸ N) : Additive (↥X ⧸ N)) = 0 := by
    intro z hz
    rw [← ofMul_one, ← QuotientGroup.mk_one]
    congr 1
    rw [D.mk_eq_mk_iff]
    simpa using hz
  have hclos : ∀ (P : AddSubgroup (Additive (↥X ⧸ N))) (Sg : Set G) (hSg : Sg ⊆ X),
      (∀ z (hz : z ∈ Sg), (Additive.ofMul
        (QuotientGroup.mk ⟨z, Set.mem_of_mem_of_subset hz hSg⟩ : ↥X ⧸ N) :
        Additive (↥X ⧸ N)) ∈ P) →
      ∀ z ∈ Subgroup.closure Sg, ∃ hz : z ∈ X,
        (Additive.ofMul (QuotientGroup.mk ⟨z, hz⟩ : ↥X ⧸ N) : Additive (↥X ⧸ N)) ∈ P := by
    intro P Sg hSg hP z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz => exact ⟨Set.mem_of_mem_of_subset hz hSg, hP z hz⟩
    | one =>
      refine ⟨one_mem _, ?_⟩
      rw [show (⟨1, one_mem X⟩ : ↥X) = 1 from rfl, QuotientGroup.mk_one, ofMul_one]
      exact zero_mem _
    | mul a b _ _ iha ihb =>
      obtain ⟨ha, ha'⟩ := iha
      obtain ⟨hb, hb'⟩ := ihb
      refine ⟨mul_mem ha hb, ?_⟩
      rw [show (⟨a * b, mul_mem ha hb⟩ : ↥X) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl,
        QuotientGroup.mk_mul, ofMul_mul]
      exact add_mem ha' hb'
    | inv a _ iha =>
      obtain ⟨ha, ha'⟩ := iha
      refine ⟨inv_mem ha, ?_⟩
      rw [show (⟨a⁻¹, inv_mem ha⟩ : ↥X) = (⟨a, ha⟩)⁻¹ from rfl, QuotientGroup.mk_inv,
        ofMul_inv]
      exact neg_mem ha'
  have hgen' : AddSubgroup.closure (Set.range fun g : Γ => ρ g m0) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective y
    induction q using QuotientGroup.induction_on with
    | H s =>
    have hSg : ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (Y : Set G)) ⊆ X := by
      rintro _ (⟨l, rfl⟩ | hy)
      · exact (D.conjX l ⟨m, hm⟩).2
      · exact D.le hy
    obtain ⟨hz, h⟩ := hclos (AddSubgroup.closure (Set.range fun g : Γ => ρ g m0)) _ hSg
      (fun z hz => by
      rcases hz with ⟨l, rfl⟩ | hzY
      · refine AddSubgroup.subset_closure ⟨θ l, ?_⟩
        show ρ (θ l) (Additive.ofMul (QuotientGroup.mk ⟨m, hm⟩)) = _
        rw [hρmk]
        rfl
      · rw [hmkY z hzY]
        exact zero_mem _) s (hgen s s.2)
    exact h
  have hcardImg : ∀ Z : Subgroup G, Z ≤ X →
      Nat.card ↥(((Z.subgroupOf X).map (QuotientGroup.mk' N)).toAddSubgroup) = Y.relIndex Z := by
    intro Z hZX
    have e : Nat.card ↥(((Z.subgroupOf X).map (QuotientGroup.mk' N)).toAddSubgroup) =
        Nat.card ↥((Z.subgroupOf X).map (QuotientGroup.mk' N)) :=
      Nat.card_congr (Additive.toMul.subtypeEquiv fun _ => Iff.rfl)
    rw [e, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', hNdef,
      Subgroup.relIndex_subgroupOf hZX]
  have hl' : Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m0 = y}) = 4 := by
    have hSg : ({y | ∃ l : ↥L, θ l ∈ Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪ (Y : Set G)) ⊆ X := by
      rintro _ (⟨l, -, rfl⟩ | hy)
      · exact (D.conjX l ⟨m, hm⟩).2
      · exact D.le hy
    have hWX : W ≤ X := by
      rw [hW, Subgroup.closure_le]
      exact hSg
    have heq : AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m0 = y} =
        ((W.subgroupOf X).map (QuotientGroup.mk' N)).toAddSubgroup := by
      apply le_antisymm
      · rw [AddSubgroup.closure_le]
        rintro _ ⟨g, hg, rfl⟩
        obtain ⟨l, rfl⟩ := D.surj g
        rw [hm0, hρmk]
        refine ⟨D.conjX l ⟨m, hm⟩, (Subgroup.mem_subgroupOf.mpr ?_ : _ ∈ W.subgroupOf X), rfl⟩
        rw [coe_conjX, hW]
        exact Subgroup.subset_closure (Or.inl ⟨l, hg, rfl⟩)
      · rintro y ⟨w, hw, hwy⟩
        have hw' : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
        rw [hW] at hw'
        obtain ⟨hz, h⟩ := hclos (AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m0 = y}) _ hSg
          (fun z hz => by
          rcases hz with ⟨l, hl, rfl⟩ | hzY
          · refine AddSubgroup.subset_closure ⟨θ l, hl, ?_⟩
            show ρ (θ l) (Additive.ofMul (QuotientGroup.mk ⟨m, hm⟩)) = _
            rw [hρmk]
            rfl
          · rw [hmkY z hzY]
            exact zero_mem _) w hw'
        have e : y = Additive.ofMul (QuotientGroup.mk w) := by
          rw [← ofMul_toMul y, ← hwy]
          rfl
        rw [e]
        exact h
    rw [heq, hcardImg W hWX, hWY]
  have hCX : C ≤ X := fun s hs => ((hC s).mp hs).1
  have hYC : Y ≤ C := fun y hy => (hC y).mpr ⟨D.le hy, mul_mem
    ((Subgroup.mem_normalizer_iff.mp (D.normY x.2) y).mp hy) (inv_mem hy)⟩
  have hcX : Nat.card (Additive (↥X ⧸ N)) = Y.relIndex X :=
    Nat.card_congr Additive.toMul
  have hcC : Nat.card {y : Additive (↥X ⧸ N) // ρ (θ x) y = y} = Y.relIndex C := by
    rw [← hcardImg C hCX]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun y => ?_)
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective y
    induction q using QuotientGroup.induction_on with
    | H s =>
    simp only [Equiv.refl_apply]
    rw [hρmk, Additive.mem_toAddSubgroup]
    constructor
    · intro hs
      have h4 := Additive.ofMul.injective hs
      rw [D.mk_eq_mk_iff, coe_conjX] at h4
      exact ⟨s, Subgroup.mem_subgroupOf.mpr ((hC s).mpr ⟨s.2, h4⟩), rfl⟩
    · rintro ⟨s', hs', hss'⟩
      have hss : (QuotientGroup.mk s' : ↥X ⧸ N) = QuotientGroup.mk s := hss'
      rw [D.mk_eq_mk_iff] at hss
      have hsC : (s : G) ∈ C := by
        have := mul_mem (inv_mem (hYC hss)) (Subgroup.mem_subgroupOf.mp hs')
        rwa [show ((s' : G) * (s : G)⁻¹)⁻¹ * s' = s * (s' : G)⁻¹ * s' by group,
          inv_mul_cancel_right] at this
      congr 1
      rw [D.mk_eq_mk_iff, coe_conjX]
      exact ((hC s).mp hsC).2
  rw [← hcX, ← hcC]
  exact isoMod_cases_of_h65 h65 h2 hfaith hmT' hgen' hl' hx3 hx1

end SecMod

end CFSG.Quasithin.H13.L32A
