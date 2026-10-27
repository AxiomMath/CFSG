module

public import CFSG.Quasithin.H13.L32NSp4Defs
public import CFSG.Quasithin.H13.L32NSp4Model

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

theorem lineOk_apply [Sp4Data] {s : Node} (hs : s ∈ ov5K ∨ s ∈ ov9K)
    {l : List ℕ} (hl : l ∈ tiLinesC) (hf : feasible s.els l = true) : concl specK s l = true := by
  have h6 := Sp4Data.line5
  have h7 := Sp4Data.line9
  have key : ∀ L, lineOk specK L = true → s ∈ L → concl specK s l = true := by
    intro L hL hsL
    have := List.all_eq_true.mp (List.all_eq_true.mp hL s hsL) l hl
    simpa [hf] using this
  rcases hs with hs | hs
  · exact key _ h6 hs
  · exact key _ h7 hs

theorem quadOk_apply [Sp4Data] {s : Node} (hs : s ∈ ov5K ∨ s ∈ ov9K)
    (hcase : s.mask = specK.s120.2 ∨ 360 ≤ s.els.length) {a : ℕ} (ha : a < 16) {l : List ℕ}
    (hl : l ∈ tiLinesC) (hz : (l.all fun y => !qJ a y) = true) :
    (s.els.any fun d => (List.range 16).any fun v => qJ a (mulVecC d v) != qJ a v) = true := by
  have h8 := Sp4Data.quad5
  have h9 := Sp4Data.quad9
  have key : ∀ L, quadOk specK L = true → s ∈ L →
      (s.els.any fun d => (List.range 16).any fun v => qJ a (mulVecC d v) != qJ a v) = true := by
    intro L hL hsL
    have h := List.all_eq_true.mp hL s hsL
    have hc : (s.mask == specK.s120.2 || decide (360 ≤ s.els.length)) = true := by
      rcases hcase with h' | h'
      · simp [h']
      · simp [h']
    simp only [hc, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h
    have := h a ha l hl
    simpa [hz] using this
  rcases hs with hs | hs
  · exact key _ h8 hs
  · exact key _ h9 hs

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {b : Module.Basis (Fin 4) (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {s : Node}
variable {W : Submodule (ZMod 2) V} {u w : V}

theorem card_nrm (h : IsNodeOf b Γ s) (hW : ∀ x ∈ W, x = 0 ∨ x = u ∨ x = w ∨ x = u + w)
    (huW : u ∈ W) (hwW : w ∈ W) (hu : u ≠ 0) (hw : w ≠ 0) (huw : u ≠ w) :
    Nat.card ↥(Γ ⊓ stabW W) = (nrmL s.els (lineOf b u w)).length :=
  h.card_filter _ _ fun γ _ => by
    rw [mem_stabW]
    exact (nrm_cf b hW huW hwW hu hw huw γ).symm

omit [Finite V] in
theorem card_fix (h : IsNodeOf b Γ s) (hW : ∀ x ∈ W, x = 0 ∨ x = u ∨ x = w ∨ x = u + w)
    (huW : u ∈ W) (hwW : w ∈ W) :
    Nat.card ↥(Γ ⊓ fixingSubgroup (V ≃ₗ[ZMod 2] V) (W : Set V)) =
      (fixL s.els (lineOf b u w)).length :=
  h.card_filter _ _ fun γ _ => by
    rw [mem_fixingSubgroup_iff']
    exact (fix_cf b hW huW hwW γ).symm

theorem feasible_of (h : IsNodeOf b Γ s) (hW : ∀ x ∈ W, x = 0 ∨ x = u ∨ x = w ∨ x = u + w)
    (huW : u ∈ W) (hwW : w ∈ W) (hu : u ≠ 0) (hw : w ≠ 0) (huw : u ≠ w)
    (hT : Nat.gcd (Nat.card Γ) 16 ∣ Nat.card ↥(Γ ⊓ stabW W))
    (h3 : ∃ y ∈ Γ, y ∈ stabW W ∧ y ≠ 1 ∧ y ^ 3 = 1 ∧ ∃ x ∈ W, y x ≠ x)
    (hne : ¬ Γ ≤ stabW W)
    (h2 : ∃ t ∈ Γ, t ∈ stabW W ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ ∃ x ∈ W, t x ≠ x) :
    feasible s.els (lineOf b u w) = true := by
  have hN := card_nrm h hW huW hwW hu hw huw
  have hG := h.card_eq
  have hmemN : ∀ γ ∈ Γ, γ ∈ stabW W → cf b γ ∈ nrmL s.els (lineOf b u w) := by
    intro γ hγ hγW
    simp only [nrmL, List.mem_filter]
    exact ⟨h.mem_els hγ, (nrm_cf b hW huW hwW hu hw huw γ).mpr hγW⟩
  simp only [feasible, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [← hN, ← hG]
    exact Nat.mod_eq_zero_of_dvd hT
  · obtain ⟨y, hyΓ, hyW, hy1, hy3, hmove⟩ := h3
    exact ⟨cf b y, hmemN y hyΓ hyW, (ord3_cf b y).mpr ⟨hy1, hy3⟩,
      (isNT_cf b hW huW hwW y).mpr hmove⟩
  · rw [← hN, ← hG]
    have hlt : Γ ⊓ stabW W < Γ := lt_of_le_of_ne inf_le_left fun he =>
      hne (by rw [← he]; exact inf_le_right)
    have : Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective (fun γ : V ≃ₗ[ZMod 2] V => (γ : V → V))
      (fun a b hab => LinearEquiv.ext (congrFun hab))
    exact Subgroup.card_lt_of_lt hlt
  · obtain ⟨t, htΓ, htW, ht1, ht2, hmove⟩ := h2
    exact ⟨cf b t, hmemN t htΓ htW, (invl_cf b t).mpr ⟨ht1, ht2⟩,
      (isNT_cf b hW huW hwW t).mpr hmove⟩

theorem specialOk_get [Sp4Data] {c : Bool} (hc : c ∈ specialChecks specK) :
    c = true := by
  exact List.all_eq_true.mp Sp4Data.special c hc

theorem specK_a36_mask [Sp4Data] : specK.a36.2 = maskOf specK.a36.1 := by
  have := specialOk_get (c := specK.a36.2 == maskOf specK.a36.1) (by simp [specialChecks])
  simpa using this

theorem specK_b36_mask [Sp4Data] : specK.b36.2 = maskOf specK.b36.1 := by
  have := specialOk_get (c := specK.b36.2 == maskOf specK.b36.1) (by simp [specialChecks])
  simpa using this

theorem specK_s36_mask [Sp4Data] : specK.s36.2 = maskOf specK.s36.1 := by
  have := specialOk_get (c := specK.s36.2 == maskOf specK.s36.1) (by simp [specialChecks])
  simpa using this

theorem specK_s120_mask [Sp4Data] :
    specK.s120.2 = maskOf specK.s120.1 := by
  have := specialOk_get (c := specK.s120.2 == maskOf specK.s120.1) (by simp [specialChecks])
  simpa using this

theorem valid_of_all {l : List (List ℕ)} (h : l.all validB = true) : ∀ x ∈ l, ValidC4 x :=
  fun x hx => validB_iff.mp (List.all_eq_true.mp h x hx)

theorem specK_a36_valid [Sp4Data] : ∀ x ∈ specK.a36.1, ValidC4 x :=
  valid_of_all (specialOk_get (c := specK.a36.1.all validB) (by simp [specialChecks]))

theorem specK_b36_valid [Sp4Data] : ∀ x ∈ specK.b36.1, ValidC4 x :=
  valid_of_all (specialOk_get (c := specK.b36.1.all validB) (by simp [specialChecks]))

theorem specK_s36_valid [Sp4Data] : ∀ x ∈ specK.s36.1, ValidC4 x :=
  valid_of_all (specialOk_get (c := specK.s36.1.all validB) (by simp [specialChecks]))

theorem specK_s120_valid [Sp4Data] : ∀ x ∈ specK.s120.1, ValidC4 x :=
  valid_of_all (specialOk_get (c := specK.s120.1.all validB) (by simp [specialChecks]))

theorem mem_iff_of_mask {s : Node} {l : List (List ℕ)} (hs : s.mask = maskOf s.els)
    (hsv : ∀ x ∈ s.els, ValidC4 x) (hl : ∀ x ∈ l, ValidC4 x) (hm : s.mask = maskOf l)
    {x : List ℕ} : x ∈ s.els ↔ x ∈ l := by
  constructor
  · intro hx
    have := memM_maskOf_of_mem hx
    rw [← hs, hm] at this
    exact mem_of_memM_maskOf hl (hsv x hx) this
  · intro hx
    have := memM_maskOf_of_mem hx
    rw [← hm, hs] at this
    exact mem_of_memM_maskOf hsv (hl x hx) this

theorem node_facts [Sp4Data] {s : Node} (hsL : s ∈ ov5K ∨ s ∈ ov9K) :
    s.mask = maskOf s.els ∧ ∀ x ∈ s.els, ValidC4 x :=
  ⟨(Sp4Data.facts s hsL).1, (Sp4Data.facts s hsL).2.1⟩

theorem node_nodup [Sp4Data] {s : Node} (hsL : s ∈ ov5K ∨ s ∈ ov9K) :
    s.els.Nodup :=
  (Sp4Data.facts s hsL).2.2

theorem concl_cases [Sp4Data] (hsL : s ∈ ov5K ∨ s ∈ ov9K)
    (h : IsNodeOf b Γ s) (hW : ∀ x ∈ W, x = 0 ∨ x = u ∨ x = w ∨ x = u + w) (huW : u ∈ W)
    (hwW : w ∈ W) (hu : u ≠ 0) (hw : w ≠ 0) (huw : u ≠ w)
    (hc : concl specK s (lineOf b u w) = true) :
    Nat.card Γ = 18 ∨
    ((∀ x, x ∈ s.els ↔ x ∈ specK.s36.1) ∧ Nat.card ↥(Γ ⊓ fixW W) = 2 ∧
      (((∀ γ ∈ Γ ⊓ fixW W, cf b γ ∈ specK.a36.1) ∧ ∀ γ ∈ Γ ⊓ stabW W, cf b γ ∈ specK.a36.1 →
          γ ≠ 1 → γ ^ 3 = 1 → ∀ x ∈ W, γ x = x) ∨
        ((∀ γ ∈ Γ ⊓ fixW W, cf b γ ∈ specK.b36.1) ∧ ∀ γ ∈ Γ ⊓ stabW W, cf b γ ∈ specK.b36.1 →
          γ ≠ 1 → γ ^ 3 = 1 → ∀ x ∈ W, γ x = x))) ∨
    (s.mask = specK.s120.2 ∧ (∀ x, x ∈ s.els ↔ x ∈ specK.s120.1) ∧
      (∀ γ ∈ Γ ⊓ fixW W, memM specK.m60 (cf b γ) = true) ∧
      ∀ t ∈ Γ ⊓ stabW W, t ≠ 1 → t ^ 2 = 1 → (∃ x ∈ W, t x ≠ x) →
        Nat.card ↥(Γ ⊓ (fixW W ⊓ Subgroup.centralizer {t})) = 2) ∨
    (Nat.card Γ = 360 ∧ Nat.card ↥(Γ ⊓ fixW W) = 4) ∨
    (Nat.card Γ = 720 ∧ Nat.card ↥(Γ ⊓ fixW W) = 8 ∧
      ∀ γ ∈ Γ, (∀ f ∈ Γ ⊓ fixW W, f * γ = γ * f) → γ ∈ fixW W) := by
  obtain ⟨hsm, hsv⟩ := node_facts hsL
  have hF := card_fix h hW huW hwW
  have hG := h.card_eq
  have hfixmem : ∀ γ ∈ Γ ⊓ fixW W, cf b γ ∈ fixL s.els (lineOf b u w) := by
    intro γ hγ
    simp only [fixL, List.mem_filter]
    exact ⟨h.mem_els hγ.1, (fix_cf b hW huW hwW γ).mpr (mem_fixingSubgroup_iff'.mp hγ.2)⟩
  have hnrmmem : ∀ γ ∈ Γ ⊓ stabW W, cf b γ ∈ nrmL s.els (lineOf b u w) := by
    intro γ hγ
    simp only [nrmL, List.mem_filter]
    exact ⟨h.mem_els hγ.1, (nrm_cf b hW huW hwW hu hw huw γ).mpr hγ.2⟩
  simp only [concl, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff] at hc
  rcases hc with (((h18 | ⟨⟨⟨h36, hm36⟩, hF2⟩, hAB⟩) | ⟨⟨⟨h120, hm120⟩, hF60⟩, hcen⟩) |
    ⟨h360, hF4⟩) | ⟨⟨h720, hF8⟩, hC⟩
  · exact Or.inl (hG.trans h18)
  · right; left
    refine ⟨fun x => mem_iff_of_mask hsm hsv specK_s36_valid (hm36.trans specK_s36_mask),
      hF.trans hF2, ?_⟩
    · have key : ∀ (X : List (List ℕ) × ℕ), X.2 = maskOf X.1 → (∀ x ∈ X.1, ValidC4 x) →
          ((∀ x ∈ fixL s.els (lineOf b u w), memM X.2 x = true) ∧
            ∀ x ∈ nrmL s.els (lineOf b u w), ((memM X.2 x = false ∨ ord3 x = false) ∨
              isNT x (lineOf b u w) = false)) →
          (∀ γ ∈ Γ ⊓ fixW W, cf b γ ∈ X.1) ∧ ∀ γ ∈ Γ ⊓ stabW W, cf b γ ∈ X.1 → γ ≠ 1 →
            γ ^ 3 = 1 → ∀ x ∈ W, γ x = x := by
        intro X hXm hXv ⟨h1, h2⟩
        refine ⟨fun γ hγ => ?_, fun γ hγ hγX hγ1 hγ3 => ?_⟩
        · have := h1 _ (hfixmem γ hγ)
          rw [hXm] at this
          exact mem_of_memM_maskOf hXv (validC4_cf b γ) this
        · rcases h2 _ (hnrmmem γ hγ) with (hx | hx) | hx
          · rw [hXm, memM_maskOf_of_mem hγX] at hx
            exact absurd hx (by decide)
          · rw [(ord3_cf b γ).mpr ⟨hγ1, hγ3⟩] at hx
            exact absurd hx (by decide)
          · intro x hx'
            by_contra hne
            rw [(isNT_cf b hW huW hwW γ).mpr ⟨x, hx', hne⟩] at hx
            exact absurd hx (by decide)
      rcases hAB with hA | hB
      · exact Or.inl (key _ specK_a36_mask specK_a36_valid hA)
      · exact Or.inr (key _ specK_b36_mask specK_b36_valid hB)
  · right; right; left
    refine ⟨hm120, fun x => mem_iff_of_mask hsm hsv specK_s120_valid
      (hm120.trans specK_s120_mask), fun γ hγ => hF60 _ (hfixmem γ hγ),
      fun t ht ht1 ht2 hmove => ?_⟩
    · rcases hcen _ (hnrmmem t ht) with (hx | hx) | hx
      · rw [(invl_cf b t).mpr ⟨ht1, ht2⟩] at hx
        exact absurd hx (by decide)
      · rw [(isNT_cf b hW huW hwW t).mpr hmove] at hx
        exact absurd hx (by decide)
      · rw [fixL, List.filter_filter] at hx
        refine (h.card_filter _ _ fun γ _ => ?_).trans hx
        rw [Subgroup.mem_inf, mem_fixingSubgroup_iff', Subgroup.mem_centralizer_singleton_iff,
          Bool.and_eq_true, ← fix_cf b hW huW hwW γ, comm_cf, eq_comm]
        constructor
        · rintro ⟨a, c⟩; exact ⟨c, a⟩
        · rintro ⟨c, a⟩; exact ⟨a, c⟩
  · right; right; right; left
    exact ⟨hG.trans h360, hF.trans hF4⟩
  · right; right; right; right
    refine ⟨hG.trans h720, hF.trans hF8, fun γ hγ hcomm => ?_⟩
    rcases hC _ (h.mem_els hγ) with hx | hx
    · exfalso
      have hx' : ∃ f ∈ fixL s.els (lineOf b u w),
          (mulC f (cf b γ) == mulC (cf b γ) f) = false := by
        by_contra hne
        simp only [not_exists, not_and, Bool.not_eq_false] at hne
        rw [List.all_eq_true.mpr hne] at hx
        exact absurd hx (by decide)
      obtain ⟨f, hf, hfc⟩ := hx'
      obtain ⟨hfs, -⟩ := List.mem_filter.mp hf
      obtain ⟨δ, hδ, rfl⟩ := h.surj f hfs
      have hδW : δ ∈ fixW W := by
        rw [mem_fixingSubgroup_iff']
        exact (fix_cf b hW huW hwW δ).mp (List.mem_filter.mp hf).2
      have := hcomm δ ⟨hδ, hδW⟩
      rw [← comm_cf] at this
      rw [this] at hfc
      exact absurd hfc (by decide)
    · have hx' : cf b γ ∈ fixL s.els (lineOf b u w) := by simpa using hx
      obtain ⟨-, hfix⟩ := List.mem_filter.mp hx'
      rw [mem_fixingSubgroup_iff']
      exact (fix_cf b hW huW hwW γ).mp hfix

end CFSG.Quasithin.H13.Sp4Cert
