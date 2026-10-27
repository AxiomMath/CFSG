module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveCartan
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

private theorem b12_TwelveMinimal_isPGroup_of_isElemAbelian {G : Type} [Group G]
    {A : Subgroup G} (hA : IsElemAbelian 2 A) : IsPGroup 2 A := fun a => ⟨1, by
  have h : a ^ 2 = 1 := Subtype.ext (hA.2 a a.2)
  simpa using h⟩

section Minimal

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] {n m : ℕ}

theorem exists_isMinimalNotLE {B A L₀ : Subgroup G} (hA : A ≤ L₀) (hL₀ : ¬ L₀ ≤ B) :
    ∃ L : Subgroup G, L ≤ L₀ ∧ IsMinimalNotLE B A L := by
  classical
  let p : Subgroup G → Prop := fun L => A ≤ L ∧ L ≤ L₀ ∧ ¬ L ≤ B
  have hp₀ : p L₀ := ⟨hA, le_rfl, hL₀⟩
  have hex : ∃ k : ℕ, ∃ L : Subgroup G, p L ∧ Nat.card L = k := ⟨_, L₀, hp₀, rfl⟩
  obtain ⟨L, hpL, hcardL⟩ := Nat.find_spec hex
  refine ⟨L, hpL.2.1, hpL.1, hpL.2.2, ?_⟩
  intro L' hAL' hL'L hL'B
  have hpL' : p L' := ⟨hAL', hL'L.trans hpL.2.1, hL'B⟩
  have hge : Nat.find hex ≤ Nat.card L' := Nat.find_min' hex ⟨L', hpL', rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hL'L (by omega)

theorem Setting12One.exists_minimal {ρ : G →* LGL 2 V}
    {B A : Subgroup G} {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m) :
    ∃ L : Subgroup G, IsMinimalNotLE B A L := by
  obtain ⟨S, hS⟩ := exists_sylow_of_isBorelIn h.borel
  have hne : ¬ (⊤ : Subgroup G) ≤ B := by
    intro htop
    exact rankOne_borel_ne_top h.type S (hS ▸ le_antisymm le_top htop)
  obtain ⟨L, -, hmin⟩ := exists_isMinimalNotLE (B := B) (A := A) (L₀ := ⊤) le_top hne
  exact ⟨L, hmin⟩

theorem rankOne_minimal_type {n : ℕ}
    (hG : CFSG.Quasithin.IsPSL 2 2 n G ∨ CFSG.Quasithin.IsSz n G) {B A L : Subgroup G}
    (hB : CFSG.Quasithin.IsBorelIn (⊤ : Subgroup G) B) (hAB : A ≤ B) (hA : IsElemAbelian 2 A)
    (h4 : 4 ≤ Nat.card A) (hL : IsMinimalNotLE B A L) :
    L = ⊤ ∨ ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧ k < n ∧
      ((CFSG.Quasithin.IsPSL 2 2 n G ∧ CFSG.Quasithin.IsPSL 2 2 k ↥L) ∨
        (CFSG.Quasithin.IsSz n G ∧ CFSG.Quasithin.IsSz k ↥L)) := by
  by_cases hLtop : L = ⊤
  · exact Or.inl hLtop
  · right
    have hA1 : A ≠ ⊥ := by
      intro hbot
      have : Nat.card A = 1 := by rw [hbot, Subgroup.card_bot]
      omega
    obtain ⟨E, hEA, hEelem, hEcard⟩ := exists_four_subgroup hA h4
    have hEL : E ≤ L := hEA.trans hL.1
    rcases rankOne_subgroup_cases hG hLtop hEL hEelem hEcard with hbor | hsub
    · exfalso
      obtain ⟨S', hLS'⟩ := hbor
      obtain ⟨S, hBS⟩ := exists_sylow_of_isBorelIn hB
      have hA2 : IsPGroup 2 A := b12_TwelveMinimal_isPGroup_of_isElemAbelian hA
      have hAS : A ≤ (S : Subgroup G) := le_sylow_of_le_normalizer hA2 (hBS ▸ hAB)
      have hAS' : A ≤ (S' : Subgroup G) := le_sylow_of_le_normalizer hA2 (hL.1.trans hLS')
      have hS'eq : S' = S := rankOne_sylow_eq_of_ne_bot hG hA1 hAS hAS'
      exact hL.2.1 (by rw [hBS, ← hS'eq]; exact hLS')
    · exact hsub

theorem Setting12One.restrict {ρ : G →* LGL 2 V}
    {B A : Subgroup G} {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    {L : Subgroup G} (hAL : A ≤ L) {k : ℕ}
    (hk : CFSG.Quasithin.IsPSL 2 2 k ↥L ∨ CFSG.Quasithin.IsSz k ↥L) :
    Setting12One (ρ.comp L.subtype) (B.subgroupOf L) Z (A.subgroupOf L) k m := by
  have hA1 : A ≠ ⊥ := by
    intro hbot
    have hm : 2 ≤ m := by have := h.one_lt_m; omega
    have h1 : 2 ^ m = 1 := by rw [← h.A_card, hbot, Subgroup.card_bot]
    have h2 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [h1] at h2
    norm_num at h2
  have hquad : RepQuad (ρ.comp L.subtype) (A.subgroupOf L) := by
    unfold RepQuad
    have hmap : (A.subgroupOf L).map (ρ.comp L.subtype) = A.map ρ := by
      rw [← Subgroup.map_map (g := ρ) (f := L.subtype),
        Subgroup.map_subgroupOf_eq_of_le hAL]
    rw [hmap]
    exact h.quad
  have helem : IsElemAbelian 2 (A.subgroupOf L) := by
    refine ⟨IsMulCommutative.of_comm fun x y => ?_, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have hx : ((x : ↥L) : G) ∈ A := Subgroup.mem_subgroupOf.mp x.2
      have hy : ((y : ↥L) : G) ∈ A := Subgroup.mem_subgroupOf.mp y.2
      have hcomm := h.A_elem.1.is_comm.comm ⟨((x : ↥L) : G), hx⟩ ⟨((y : ↥L) : G), hy⟩
      simpa using congrArg Subtype.val hcomm
    · have hx' : ((x : ↥L) : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
      exact Subtype.ext (by simpa using h.A_elem.2 ((x : ↥L) : G) hx')
  have hcard : Nat.card (A.subgroupOf L) = 2 ^ m :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv).trans h.A_card
  exact
    { type := hk
      borel := rankOne_isBorelIn_subgroupOf h.type h.borel h.A_le_B h.A_elem hA1 hAL
      stab := fun g => (Subgroup.mem_subgroupOf).trans (h.stab (g : G))
      A_le_B := fun x hx =>
        Subgroup.mem_subgroupOf.mpr (h.A_le_B (Subgroup.mem_subgroupOf.mp hx))
      A_elem := helem
      A_card := hcard
      one_lt_m := h.one_lt_m
      quad := hquad }

theorem IsMinimalNotLE.minimal_subgroupOf {B A L : Subgroup G} (hL : IsMinimalNotLE B A L) :
    ∀ L' : Subgroup ↥L, A.subgroupOf L ≤ L' → ¬ L' ≤ B.subgroupOf L → L' = ⊤ := by
  intro L' hAL' hL'B
  let L'' : Subgroup G := L'.map L.subtype
  have hL''le : L'' ≤ L := Subgroup.map_subtype_le L'
  have hAL'' : A ≤ L'' := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hL.1]
    exact Subgroup.map_mono hAL'
  have hL''B : ¬ L'' ≤ B := fun hle =>
    hL'B fun x hx => Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map_of_mem L.subtype hx))
  have hL''eq : L'' = L := hL.2.2 L'' hAL'' hL''le hL''B
  refine le_antisymm le_top ?_
  intro x _
  have hxL : (x : G) ∈ L'' := by rw [hL''eq]; exact x.2
  obtain ⟨y, hyL', hyx⟩ := hxL
  exact Subtype.ext hyx ▸ hyL'

theorem Setting12One.exists_restrict_of_minimal
    {ρ : G →* LGL 2 V}
    {B A : Subgroup G} {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    {L : Subgroup G} (hL : IsMinimalNotLE B A L) :
    ∃ k : ℕ, (k = n ∨ (2 ≤ k ∧ k ∣ n ∧ k < n)) ∧
      Setting12One (ρ.comp L.subtype) (B.subgroupOf L) Z (A.subgroupOf L) k m ∧
      ∀ L' : Subgroup ↥L, A.subgroupOf L ≤ L' → ¬ L' ≤ B.subgroupOf L → L' = ⊤ := by
  have h4 : 4 ≤ Nat.card A := by
    have hm : 2 ≤ m := by have := h.one_lt_m; omega
    rw [h.A_card]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rcases rankOne_minimal_type h.type h.borel h.A_le_B h.A_elem h4 hL with htop | hsub
  · subst htop
    refine ⟨n, Or.inl rfl, Setting12One.restrict h le_top ?_,
      IsMinimalNotLE.minimal_subgroupOf hL⟩
    rcases h.type with hPSL | hSz
    · exact Or.inl (CFSG.Quasithin.IsPSL.of_mulEquiv Subgroup.topEquiv.symm hPSL)
    · exact Or.inr (CFSG.Quasithin.IsSz.of_mulEquiv Subgroup.topEquiv.symm hSz)
  · obtain ⟨k, hk2, hkdn, hklt, htype⟩ := hsub
    refine ⟨k, Or.inr ⟨hk2, hkdn, hklt⟩, ?_, IsMinimalNotLE.minimal_subgroupOf hL⟩
    rcases htype with ⟨-, hPSL⟩ | ⟨-, hSz⟩
    · exact Setting12One.restrict h hL.1 (Or.inl hPSL)
    · exact Setting12One.restrict h hL.1 (Or.inr hSz)

end Minimal

end CFSG.LocalAnalysis.WeakClosure81
