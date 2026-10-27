module

public import CFSG.Quasithin.AppendixH.Common.OctadStabCore

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

private theorem mem_stabilizer_finset_iff {S : Finset (Fin 24)} {g : S24} :
    g ∈ MulAction.stabilizer S24 S ↔ ∀ x, g x ∈ S ↔ x ∈ S := by
  rw [MulAction.mem_stabilizer_finset]
  simp only [Equiv.Perm.smul_def]

private theorem mem_stabilizer_point_iff {a : Fin 24} {g : S24} :
    g ∈ MulAction.stabilizer S24 a ↔ g a = a := by
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

private theorem erase_iff_of_apply_eq (g : S24) {O : Finset (Fin 24)} {a : Fin 24}
    (hga : g a = a) (x : Fin 24) :
    (g x ∈ O.erase a ↔ x ∈ O.erase a) ↔ (g x ∈ O ↔ x ∈ O) := by
  by_cases hx : x = a
  · subst hx
    rw [hga]
    simp [Finset.mem_erase]
  · have hgx : g x ≠ a := fun h => hx (g.injective (by rw [h, hga]))
    simp [Finset.mem_erase, hx, hgx]

private theorem erase₂_iff_of_apply_eq (g : S24) {O : Finset (Fin 24)} {a b : Fin 24}
    (hga : g a = a) (hgb : g b = b) (x : Fin 24) :
    (g x ∈ (O.erase a).erase b ↔ x ∈ (O.erase a).erase b) ↔ (g x ∈ O ↔ x ∈ O) := by
  by_cases hxa : x = a
  · subst hxa
    rw [hga]
    simp [Finset.mem_erase]
  by_cases hxb : x = b
  · subst hxb
    rw [hgb]
    simp [Finset.mem_erase]
  · have hgxa : g x ≠ a := fun h => hxa (g.injective (by rw [h, hga]))
    have hgxb : g x ≠ b := fun h => hxb (g.injective (by rw [h, hgb]))
    simp [Finset.mem_erase, hxa, hxb, hgxa, hgxb]

private theorem mem_erase₂_iff_pair {O : Finset (Fin 24)} {a b x : Fin 24} (ha : a ∈ O)
    (hb : b ∈ O) : x ∈ O ↔ x ∈ (O.erase a).erase b ∨ x ∈ ({a, b} : Finset (Fin 24)) := by
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inr (Or.inl hxa)
    · by_cases hxb : x = b
      · exact Or.inr (Or.inr hxb)
      · exact Or.inl ⟨hxb, hxa, hx⟩
  · rintro (⟨-, -, hx⟩ | hx)
    · exact hx
    · rcases hx with hxa | hxb
      · rwa [hxa]
      · rwa [hxb]

private theorem mem_erase₂_iff {O : Finset (Fin 24)} {a b y : Fin 24} (ha : a ∈ O) (hb : b ∈ O) :
    y ∈ (O.erase a).erase b ↔ y ∈ O ∧ y ∉ ({a, b} : Finset (Fin 24)) := by
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hyb, hya, hyO⟩
    exact ⟨hyO, fun h => h.elim hya hyb⟩
  · rintro ⟨hyO, hyP⟩
    exact ⟨fun h => hyP (Or.inr h), fun h => hyP (Or.inl h), hyO⟩

private theorem erase₂_iff_of_stab_pair (g : S24) {O : Finset (Fin 24)} {a b : Fin 24}
    (ha : a ∈ O) (hb : b ∈ O) (x : Fin 24)
    (hY : g x ∈ (O.erase a).erase b ↔ x ∈ (O.erase a).erase b)
    (hP : g x ∈ ({a, b} : Finset (Fin 24)) ↔ x ∈ ({a, b} : Finset (Fin 24))) :
    g x ∈ O ↔ x ∈ O := by
  rw [mem_erase₂_iff_pair (O := O) (a := a) (b := b) (x := g x) ha hb,
    mem_erase₂_iff_pair (O := O) (a := a) (b := b) (x := x) ha hb, hY, hP]

private theorem pair_mem_iff_of_apply_eq (g : S24) {a b x : Fin 24} (hga : g a = a)
    (hgb : g b = b) :
    g x ∈ ({a, b} : Finset (Fin 24)) ↔ x ∈ ({a, b} : Finset (Fin 24)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (g.injective (by rw [h, hga]))
    · exact Or.inr (g.injective (by rw [h, hgb]))
  · rintro (h | h)
    · exact Or.inl (by rw [h, hga])
    · exact Or.inr (by rw [h, hgb])

private theorem mem_M23g_inf_erase_iff (g : S24) {O : Finset (Fin 24)} {a : Fin 24} :
    (g ∈ M23g a ⊓ MulAction.stabilizer S24 (O.erase a)) ↔
      (g ∈ octStab O ⊓ MulAction.stabilizer S24 a) := by
  simp only [M23g, octStab, Subgroup.mem_inf]
  simp only [mem_stabilizer_finset_iff, mem_stabilizer_point_iff]
  constructor
  · rintro ⟨⟨hgM, hga⟩, hY⟩
    exact ⟨⟨hgM, fun x => (erase_iff_of_apply_eq g hga x).mp (hY x)⟩, hga⟩
  · rintro ⟨⟨hgM, hO⟩, hga⟩
    exact ⟨⟨hgM, hga⟩, fun x => (erase_iff_of_apply_eq g hga x).mpr (hO x)⟩

private theorem mem_M22g_inf_erase₂_iff (g : S24) {O : Finset (Fin 24)} {a b : Fin 24} :
    (g ∈ M22g a b ⊓ MulAction.stabilizer S24 ((O.erase a).erase b)) ↔
      (g ∈ octStab O ⊓ MulAction.stabilizer S24 a ⊓ MulAction.stabilizer S24 b) := by
  simp only [M22g, octStab, Subgroup.mem_inf]
  simp only [mem_stabilizer_finset_iff, mem_stabilizer_point_iff]
  constructor
  · rintro ⟨⟨⟨hgM, hga⟩, hgb⟩, hY⟩
    exact ⟨⟨⟨hgM, fun x => (erase₂_iff_of_apply_eq g hga hgb x).mp (hY x)⟩, hga⟩, hgb⟩
  · rintro ⟨⟨⟨hgM, hO⟩, hga⟩, hgb⟩
    exact ⟨⟨⟨hgM, hga⟩, hgb⟩, fun x => (erase₂_iff_of_apply_eq g hga hgb x).mpr (hO x)⟩

private theorem mem_M2ab_inf_erase₂_iff (g : S24) {O : Finset (Fin 24)} {a b : Fin 24}
    (ha : a ∈ O) (hb : b ∈ O) :
    (g ∈ M2ab a b ⊓ MulAction.stabilizer S24 ((O.erase a).erase b)) ↔
      (g ∈ octStab O ⊓ MulAction.stabilizer S24 ({a, b} : Finset (Fin 24))) := by
  simp only [M2ab, octStab, Subgroup.mem_inf]
  simp only [mem_stabilizer_finset_iff]
  constructor
  · rintro ⟨⟨hgM, hP⟩, hY⟩
    exact ⟨⟨hgM, fun x => erase₂_iff_of_stab_pair g ha hb x (hY x) (hP x)⟩, hP⟩
  · rintro ⟨⟨hgM, hO⟩, hP⟩
    refine ⟨⟨hgM, hP⟩, fun x => ?_⟩
    rw [mem_erase₂_iff (O := O) (a := a) (b := b) (y := g x) ha hb,
      mem_erase₂_iff (O := O) (a := a) (b := b) (y := x) ha hb, hO x]
    constructor
    · rintro ⟨hxO, hgxP⟩
      exact ⟨hxO, fun hxP => hgxP ((hP x).mpr hxP)⟩
    · rintro ⟨hxO, hxP⟩
      exact ⟨hxO, fun hgxP => hxP ((hP x).mp hgxP)⟩

theorem M23g_inf_stabilizer_erase {O : Finset (Fin 24)} {a : Fin 24} (ha : a ∈ O) :
    M23g a ⊓ MulAction.stabilizer S24 (O.erase a) =
      octStab O ⊓ MulAction.stabilizer S24 a := by
  ext g
  exact mem_M23g_inf_erase_iff g

theorem M22g_inf_stabilizer_erase₂ {O : Finset (Fin 24)} {a b : Fin 24} (ha : a ∈ O)
    (hb : b ∈ O) : M22g a b ⊓ MulAction.stabilizer S24 ((O.erase a).erase b) =
      octStab O ⊓ MulAction.stabilizer S24 a ⊓ MulAction.stabilizer S24 b := by
  ext g
  exact mem_M22g_inf_erase₂_iff g

theorem M2ab_inf_stabilizer_erase₂ {O : Finset (Fin 24)} {a b : Fin 24} (ha : a ∈ O)
    (hb : b ∈ O) : M2ab a b ⊓ MulAction.stabilizer S24 ((O.erase a).erase b) =
      octStab O ⊓ MulAction.stabilizer S24 ({a, b} : Finset (Fin 24)) := by
  ext g
  exact mem_M2ab_inf_erase₂_iff g ha hb

theorem pCoreOf_M23g_stabilizer_erase {O : Finset (Fin 24)}
    {a : Fin 24} (hO : IsOctad O) (ha : a ∈ O) :
    pCoreOf 2 (M23g a ⊓ MulAction.stabilizer S24 (O.erase a)) = octFix O := by
  rw [M23g_inf_stabilizer_erase ha]
  refine pCoreOf_eq_octFix_of_stab (Z := ({a} : Finset (Fin 24)))
    (H := octStab O ⊓ MulAction.stabilizer S24 a) hO ?_ ?_ ?_ ?_ ?_ ?_
  · exact Finset.singleton_subset_iff.mpr ha
  · simp
  · intro g hg
    obtain ⟨hgM, hgfix⟩ := mem_octFix_iff.mp hg
    exact ⟨octFix_le_octStab O hg, mem_stabilizer_point_iff.mpr (hgfix a ha)⟩
  · exact inf_le_left
  · intro g hg z hz
    rw [Finset.mem_singleton] at hz
    rw [hz]
    have hga : g a = a := mem_stabilizer_point_iff.mp (Subgroup.mem_inf.mp hg).2
    rw [hga]
    exact Finset.mem_singleton_self a
  · intro g hg hfix
    exact ⟨hg, mem_stabilizer_point_iff.mpr (hfix a (Finset.mem_singleton_self a))⟩

theorem pCoreOf_between_stabilizer_erase₂ {O : Finset (Fin 24)}
    {a b : Fin 24} (hO : IsOctad O) (ha : a ∈ O) (hb : b ∈ O) {Γ : Subgroup S24}
    (h1 : M22g a b ≤ Γ) (h2 : Γ ≤ M2ab a b) :
    pCoreOf 2 (Γ ⊓ MulAction.stabilizer S24 ((O.erase a).erase b)) = octFix O := by
  refine pCoreOf_eq_octFix_of_stab (Z := ({a, b} : Finset (Fin 24)))
    (H := Γ ⊓ MulAction.stabilizer S24 ((O.erase a).erase b)) hO ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · exact (Finset.card_insert_le a ({b} : Finset (Fin 24))).trans (by simp)
  · intro g hg
    obtain ⟨hgM, hgfix⟩ := mem_octFix_iff.mp hg
    have hga : g a = a := hgfix a ha
    have hgb : g b = b := hgfix b hb
    refine ⟨h1 ((mem_M22g_iff a b g).mpr ⟨hgM, hga, hgb⟩), mem_stabilizer_finset_iff.mpr ?_⟩
    intro x
    rw [mem_erase₂_iff (O := O) (a := a) (b := b) (y := g x) ha hb,
      mem_erase₂_iff (O := O) (a := a) (b := b) (y := x) ha hb]
    constructor
    · rintro ⟨hgxO, hgxP⟩
      have hxO : x ∈ O := by
        have h : g x = x := g.injective (hgfix (g x) hgxO)
        exact h ▸ hgxO
      exact ⟨hxO, fun hxP => hgxP ((pair_mem_iff_of_apply_eq g hga hgb).mpr hxP)⟩
    · rintro ⟨hxO, hxP⟩
      exact ⟨by rw [hgfix x hxO]; exact hxO,
        fun hgxP => hxP ((pair_mem_iff_of_apply_eq g hga hgb).mp hgxP)⟩
  · intro g hg
    obtain ⟨hgΓ, hgY⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨hgM, hgP⟩ := Subgroup.mem_inf.mp (h2 hgΓ)
    simp only [mem_stabilizer_finset_iff] at hgY hgP
    rw [octStab, Subgroup.mem_inf]
    refine ⟨hgM, ?_⟩
    simp only [mem_stabilizer_finset_iff]
    intro x
    exact erase₂_iff_of_stab_pair g ha hb x (hgY x) (hgP x)
  · intro g hg z hz
    obtain ⟨hgΓ, -⟩ := Subgroup.mem_inf.mp hg
    have hgP : g ∈ MulAction.stabilizer S24 ({a, b} : Finset (Fin 24)) :=
      (Subgroup.mem_inf.mp (h2 hgΓ)).2
    simp only [mem_stabilizer_finset_iff] at hgP
    exact (hgP z).mpr hz
  · intro g hg hfix
    have hga : g a = a := hfix a (by simp)
    have hgb : g b = b := hfix b (by simp)
    obtain ⟨hgM, hgO⟩ := Subgroup.mem_inf.mp hg
    simp only [mem_stabilizer_finset_iff] at hgO
    refine ⟨h1 ((mem_M22g_iff a b g).mpr ⟨hgM, hga, hgb⟩), mem_stabilizer_finset_iff.mpr ?_⟩
    intro x
    rw [mem_erase₂_iff (O := O) (a := a) (b := b) (y := g x) ha hb,
      mem_erase₂_iff (O := O) (a := a) (b := b) (y := x) ha hb, hgO x]
    constructor
    · rintro ⟨hxO, hgxP⟩
      exact ⟨hxO, fun hxP => hgxP ((pair_mem_iff_of_apply_eq g hga hgb).mpr hxP)⟩
    · rintro ⟨hxO, hxP⟩
      exact ⟨hxO, fun hgxP => hxP ((pair_mem_iff_of_apply_eq g hga hgb).mp hgxP)⟩

end CFSG.ASVolI.AppH
