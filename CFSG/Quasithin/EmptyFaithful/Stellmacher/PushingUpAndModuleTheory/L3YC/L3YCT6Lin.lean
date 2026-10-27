module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF3

public section

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

section Linear

variable {F : Type} [Field F] [Fintype F]

theorem exists_addEquiv_fix_not_mem (hF : Fintype.card F = 2) {W : AddSubgroup (Fin 3 → F)}
    (hW : Nat.card W = 4) {a : Fin 3 → F} (haW : a ∈ W) :
    ∃ φ : (Fin 3 → F) ≃+ (Fin 3 → F), φ a = a ∧ ∃ w ∈ W, φ w ∉ W := by
  classical
  obtain ⟨w, hwW, hw0, hwa⟩ : ∃ w ∈ W, w ≠ 0 ∧ w ≠ a := by
    by_contra hcon
    have hsub : (W : Set (Fin 3 → F)) ⊆ {0, a} := by
      intro x hx
      by_contra hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx'
      exact hcon ⟨x, hx, hx'.1, hx'.2⟩
    have h2 : (W : Set (Fin 3 → F)).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans (by simp))
    have h4 : (W : Set (Fin 3 → F)).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hW
    omega
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → F, v ∉ W := by
    by_contra hcon
    push Not at hcon
    have hall : W = ⊤ := top_unique fun x _ => hcon x
    have : Nat.card W = Nat.card (Fin 3 → F) := by
      rw [hall]
      exact Nat.card_congr (AddSubgroup.topEquiv).toEquiv
    rw [Nat.card_pi, hW] at this
    simp [Nat.card_eq_fintype_card, hF] at this
  have hwT : w ∉ Submodule.span F {a, v} := by
    intro hmem
    rw [Submodule.mem_span_pair] at hmem
    obtain ⟨x, y, hxy⟩ := hmem
    rcases eq_zero_or_one_of_card_two hF x with rfl | rfl <;>
      rcases eq_zero_or_one_of_card_two hF y with rfl | rfl
    · simp at hxy
      exact hw0 hxy.symm
    · simp at hxy
      exact hv (hxy ▸ hwW)
    · simp at hxy
      exact hwa hxy.symm
    · simp at hxy
      apply hv
      have : v = w - a := by rw [← hxy]; abel
      rw [this]
      exact W.sub_mem hwW haW
  obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hwT inferInstance
  have hfa : f a = 0 := by
    have : f a ∈ (Submodule.span F {a, v}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
    rw [hf] at this
    exact (Submodule.mem_bot F).mp this
  have hfv : f v = 0 := by
    have : f v ∈ (Submodule.span F {a, v}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
    rw [hf] at this
    exact (Submodule.mem_bot F).mp this
  have hfw1 : f w = 1 := (eq_zero_or_one_of_card_two hF _).resolve_left hfw
  have h2 : (2 : F) = 0 := by
    have : (1 : F) + 1 = 0 := by
      rcases eq_zero_or_one_of_card_two hF ((1 : F) + 1) with h | h
      · exact h
      · exact absurd (add_eq_right.mp h) one_ne_zero
    rw [← one_add_one_eq_two]
    exact this
  have hg : ∀ x : Fin 3 → F, (x + f x • v) + f (x + f x • v) • v = x := by
    intro x
    rw [map_add, map_smul, hfv]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rw [add_assoc, ← add_smul]
    have : f x + f x = 0 := by
      rw [← two_mul, h2, zero_mul]
    rw [this]; simp
  let φ : (Fin 3 → F) ≃+ (Fin 3 → F) :=
    { toFun := fun x => x + f x • v
      invFun := fun x => x + f x • v
      left_inv := hg
      right_inv := hg
      map_add' := fun x y => by
        simp only [map_add, add_smul]
        abel }
  refine ⟨φ, ?_, w, hwW, ?_⟩
  · show a + f a • v = a
    rw [hfa]; simp
  · intro hmem
    have : v ∈ W := by
      have h1 : w + f w • v - w ∈ W := W.sub_mem hmem hwW
      rw [hfw1] at h1
      simpa using h1
    exact hv this

end Linear

section Core

variable {G : Type} [Group G]

theorem natural_coord {L U : Subgroup G} {F : Type} [Field F] [Fintype F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)} (α : ↥L →* ↥Γ)
    (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1) :
    ∃ B : ↥U ≃* Multiplicative (Fin 3 → F), ∀ (a : ↥L) (u v : ↥U), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (B v) =
        ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (B u)) := by
  classical
  obtain ⟨-, -, β, hβs, hβk, hβe⟩ := hnat
  let e : Multiplicative (Fin 1 → Fin 3 → F) ≃* Multiplicative (Fin 3 → F) :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))
  let β0 : ↥U →* Multiplicative (Fin 3 → F) := e.toMonoidHom.comp β
  have hβ0s : Function.Surjective β0 := e.surjective.comp hβs
  have hβ0i : Function.Injective β0 := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : β u = 1 := e.injective (by simpa [β0] using hu)
    have h2 : u ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    exact Subtype.ext (by simpa using h2)
  refine ⟨MulEquiv.ofBijective β0 ⟨hβ0i, hβ0s⟩, fun a u v h => ?_⟩
  have := hβe a u v h 0
  simp [β0, e, moduleAct] at this ⊢
  exact this

theorem exists_fix_not_normalizing {L U W : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hα : Function.Surjective α) (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    (hWU : W ≤ U) (hW : Nat.card ↥W = 4) {a : G} (haW : a ∈ W) :
    ∃ y ∈ L, y * a * y⁻¹ = a ∧ ∃ w ∈ W, y * w * y⁻¹ ∉ W := by
  classical
  obtain ⟨B, hB⟩ := natural_coord α hnat
  let W' : AddSubgroup (Fin 3 → F) :=
    { carrier := {x | ∃ u : ↥U, (u : G) ∈ W ∧ Multiplicative.toAdd (B u) = x}
      zero_mem' := ⟨1, W.one_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u * v, W.mul_mem hu hv, by simp⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, W.inv_mem hu, by simp⟩ }
  have hmemW' : ∀ u : ↥U, Multiplicative.toAdd (B u) ∈ W' ↔ (u : G) ∈ W := by
    intro u
    constructor
    · rintro ⟨v, hv, hvu⟩
      have : v = u := B.injective (Multiplicative.toAdd.injective hvu)
      exact this ▸ hv
    · exact fun h => ⟨u, h, rfl⟩
  have hW'card : Nat.card W' = 4 := by
    rw [← hW]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun x : W => (⟨Multiplicative.toAdd (B ⟨x, hWU x.2⟩), (hmemW' _).mpr x.2⟩ : W')) ⟨?_, ?_⟩)).symm
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      have := B.injective (Multiplicative.toAdd.injective h1)
      exact Subtype.ext (Subtype.mk.inj this)
    · rintro ⟨_, ⟨u, hu, rfl⟩⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  let au : ↥U := ⟨a, hWU haW⟩
  obtain ⟨φ, hφa, w', hw'W, hφw'⟩ :=
    exists_addEquiv_fix_not_mem hF hW'card ((hmemW' au).mpr haW)
  obtain ⟨g, hg⟩ := exists_gl_of_addEquiv hF φ
  obtain ⟨l, hl⟩ := hα ⟨g, by rw [statedSL_eq_top_of_card_two hF]; trivial⟩
  have hact : ∀ u : ↥U, (l : G) * u * (l : G)⁻¹ ∈ U := fun u => by
    have : (l : G) ∈ Subgroup.normalizer (U : Set G) := hnat.1 l.2
    exact (Subgroup.mem_normalizer_iff.mp this u).mp u.2
  have hcoord : ∀ u : ↥U, Multiplicative.toAdd (B ⟨_, hact u⟩) = φ (Multiplicative.toAdd (B u)) := by
    intro u
    have := hB l u ⟨_, hact u⟩ rfl
    rw [this, hl, ← hg]
  refine ⟨l, l.2, ?_, ?_⟩
  · have h1 := hcoord au
    rw [hφa] at h1
    have h2 := B.injective (Multiplicative.toAdd.injective h1)
    exact congrArg Subtype.val h2
  · obtain ⟨u, hu, rfl⟩ := hw'W
    refine ⟨u, hu, fun hmem => hφw' ?_⟩
    rw [← hcoord u]
    exact (hmemW' _).mpr hmem

end Core

end Stellmacher.PU.L3YC

end CFSG.Quasithin
