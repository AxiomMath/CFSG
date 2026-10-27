module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Setting

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.Quasithin.Asc94
open scoped Pointwise

variable {G : Type} [Group G]

theorem perm_smul_set_eq_of_mapsTo {X : Type*} [Finite X] {ρ : Equiv.Perm X} {S : Set X}
    (h : ∀ x ∈ S, ρ x ∈ S) : ρ • S = S := by
  have hsub : ρ • S ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite S)
  rw [← Set.image_smul, Set.ncard_image_of_injective _ (MulAction.injective ρ)]

@[expose] def m23Rho1 : Equiv.Perm (Fin 7) := Equiv.swap 3 4 * Equiv.swap 0 1

@[expose] def m23Rho2 : Equiv.Perm (Fin 7) := Equiv.swap 5 6 * Equiv.swap 0 1

@[expose] def m23Rho3 : Equiv.Perm (Fin 7) := Equiv.swap 4 6 * Equiv.swap 0 1

@[expose] def m23Word : Fin 6 → Equiv.Perm (Fin 7)
  | 0 => 1
  | 1 => m23Rho3
  | 2 => m23Rho2 * m23Rho3
  | 3 => m23Rho1 * m23Rho3
  | 4 => m23Rho1 * m23Rho2 * m23Rho3
  | 5 => m23Rho3 * m23Rho1 * m23Rho2 * m23Rho3

theorem m23Word_mem {Q : Subgroup (Equiv.Perm (Fin 7))} (h1 : m23Rho1 ∈ Q) (h2 : m23Rho2 ∈ Q)
    (h3 : m23Rho3 ∈ Q) (i : Fin 6) : m23Word i ∈ Q := by
  fin_cases i
  · exact Q.one_mem
  · exact h3
  · exact Q.mul_mem h2 h3
  · exact Q.mul_mem h1 h3
  · exact Q.mul_mem (Q.mul_mem h1 h2) h3
  · exact Q.mul_mem (Q.mul_mem (Q.mul_mem h3 h1) h2) h3

theorem exists_m23Word (a b : Fin 7) (ha : a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6)
    (hb : b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6) (hab : a ≠ b) :
    ∃ i : Fin 6, (m23Word i 5 = a ∧ m23Word i 6 = b) ∨ (m23Word i 5 = b ∧ m23Word i 6 = a) := by
  revert a b
  decide

section Cosets

variable {A M2 : Subgroup G} {π : ↥M2 →* Equiv.Perm (Fin 7)}

theorem mem_iff_of_inf_eq_setStabIn (hA : A ⊓ M2 = setStabIn M2 π {5, 6}) {g : G}
    (hg : g ∈ M2) : g ∈ A ↔ π ⟨g, hg⟩ • ({5, 6} : Set (Fin 7)) = {5, 6} := by
  have e : g ∈ A ⊓ M2 ↔ g ∈ setStabIn M2 π {5, 6} := by rw [hA]
  rw [Subgroup.mem_inf, mem_setStabIn] at e
  constructor
  · intro h
    obtain ⟨_, h'⟩ := e.mp ⟨h, hg⟩
    exact h'
  · intro h
    exact (e.mpr ⟨hg, h⟩).1

theorem mk_eq_mk_iff_of_inf_eq_setStabIn (hA : A ⊓ M2 = setStabIn M2 π {5, 6}) {g k : G}
    (hg : g ∈ M2) (hk : k ∈ M2) :
    ((g : G ⧸ A) = (k : G ⧸ A)) ↔
      π ⟨g, hg⟩ • ({5, 6} : Set (Fin 7)) = π ⟨k, hk⟩ • ({5, 6} : Set (Fin 7)) := by
  rw [QuotientGroup.eq, mem_iff_of_inf_eq_setStabIn hA (M2.mul_mem (M2.inv_mem hg) hk),
    show (⟨g⁻¹ * k, M2.mul_mem (M2.inv_mem hg) hk⟩ : ↥M2) = (⟨g, hg⟩ : ↥M2)⁻¹ * ⟨k, hk⟩
      from rfl, map_mul, map_inv, mul_smul, inv_smul_eq_iff, eq_comm]

theorem mem_stabilizer_pair_iff_of_inf_eq_setStabIn (hA : A ⊓ M2 = setStabIn M2 π {5, 6})
    {t : G} (hsw : IsM23Swap M2 π t) {g : G} (hg : g ∈ M2) :
    g ∈ stabilizer G ({((1 : G) : G ⧸ A), ((t : G) : G ⧸ A)} : Set (G ⧸ A)) ↔
      (π ⟨g, hg⟩ • ({5, 6} : Set (Fin 7)) = {5, 6} ∧
          π ⟨g, hg⟩ • ({4, 5} : Set (Fin 7)) = {4, 5}) ∨
        (π ⟨g, hg⟩ • ({5, 6} : Set (Fin 7)) = {4, 5} ∧
          π ⟨g, hg⟩ • ({4, 5} : Set (Fin 7)) = {5, 6}) := by
  obtain ⟨htM2, ht56, ht45⟩ := hsw
  have hπ1 : π ⟨1, M2.one_mem⟩ = 1 := map_one π
  have hmul : π ⟨g * t, M2.mul_mem hg htM2⟩ = π ⟨g, hg⟩ * π ⟨t, htM2⟩ :=
    map_mul π ⟨g, hg⟩ ⟨t, htM2⟩
  rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, Set.pair_eq_pair_iff,
    MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, mul_one,
    mk_eq_mk_iff_of_inf_eq_setStabIn hA hg M2.one_mem,
    mk_eq_mk_iff_of_inf_eq_setStabIn hA (M2.mul_mem hg htM2) htM2,
    mk_eq_mk_iff_of_inf_eq_setStabIn hA hg htM2,
    mk_eq_mk_iff_of_inf_eq_setStabIn hA (M2.mul_mem hg htM2) M2.one_mem,
    hπ1, one_smul, hmul, mul_smul, ht56]

end Cosets

theorem stmt5_2_22_of (h519 : Stmt5_2_19) : Stmt5_2_22 := by
  intro G _ _ T M L V H B D L₂ n M2 π t hyp hM23 hS htI hsw
  obtain ⟨hGxM2, hH⟩ := h519 G T M L V H B D L₂ n M2 π hyp hM23 hS
  have hA : m23Gx T M L H B D ⊓ M2 = setStabIn M2 π {5, 6} := hGxM2.trans hH
  set J := m23I M2 π ⊓ stabilizer G ({((1 : G) : G ⧸ m23Gx T M L H B D),
      ((t : G) : G ⧸ m23Gx T M L H B D)} : Set (G ⧸ m23Gx T M L H B D)) ⊔
    m23I M2 π ⊓ m23Gx T M L H B D with hJ
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  have hIM2 : m23I M2 π ≤ M2 := setStabIn_le M2 π _
  have hJI : J ≤ m23I M2 π := sup_le inf_le_left inf_le_left
  have hlift : ∀ ρ ∈ alternatingGroup (Fin 7), ∃ (r : G) (hr : r ∈ M2), π ⟨r, hr⟩ = ρ := by
    intro ρ hρ
    have : ρ ∈ π.range := by rw [hS.range_eq]; exact hρ
    obtain ⟨r, hr⟩ := this
    exact ⟨r, r.2, hr⟩
  have hΛ : ∀ ρ : Equiv.Perm (Fin 7), (∀ x : Fin 7, x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 →
      ρ x = 3 ∨ ρ x = 4 ∨ ρ x = 5 ∨ ρ x = 6) →
      ρ • ({3, 4, 5, 6} : Set (Fin 7)) = {3, 4, 5, 6} := by
    intro ρ h
    refine perm_smul_set_eq_of_mapsTo fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    exact h x hx
  set Q : Subgroup (Equiv.Perm (Fin 7)) := (J.subgroupOf M2).map π with hQ
  have memQ : ∀ (r : G) (hr : r ∈ M2), r ∈ J → π ⟨r, hr⟩ ∈ Q := fun r hr hrJ =>
    ⟨⟨r, hr⟩, hrJ, rfl⟩
  have hx : ∀ ρ ∈ alternatingGroup (Fin 7), ρ • ({3, 4, 5, 6} : Set (Fin 7)) = {3, 4, 5, 6} →
      ρ • ({5, 6} : Set (Fin 7)) = {5, 6} → ρ ∈ Q := by
    intro ρ hρ h1 h2
    obtain ⟨r, hr, e⟩ := hlift ρ hρ
    rw [← e]
    refine memQ r hr (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨mem_setStabIn.mpr ⟨hr, ?_⟩,
      (mem_iff_of_inf_eq_setStabIn hA hr).mpr ?_⟩))
    · rw [e]; exact h1
    · rw [e]; exact h2
  have h1 : m23Rho1 ∈ Q := by
    refine hx _ ?_ (hΛ _ (by decide)) (by rw [smul_pair_set_eq_iff]; decide)
    rw [Equiv.Perm.mem_alternatingGroup, m23Rho1, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  have h2 : m23Rho2 ∈ Q := by
    refine hx _ ?_ (hΛ _ (by decide)) (by rw [smul_pair_set_eq_iff]; decide)
    rw [Equiv.Perm.mem_alternatingGroup, m23Rho2, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  have h3 : m23Rho3 ∈ Q := by
    obtain ⟨r, hr, e⟩ := hlift m23Rho3 (by
      rw [Equiv.Perm.mem_alternatingGroup, m23Rho3, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
      decide)
    rw [← e]
    refine memQ r hr (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨mem_setStabIn.mpr ⟨hr, ?_⟩,
      (mem_stabilizer_pair_iff_of_inf_eq_setStabIn hA hsw hr).mpr (Or.inr ⟨?_, ?_⟩)⟩))
    · rw [e]; exact hΛ _ (by decide)
    · rw [e, smul_pair_set_eq_iff]; decide
    · rw [e, smul_pair_set_eq_iff]; decide
  intro g hg
  obtain ⟨hgM2, hgΛ⟩ := mem_setStabIn.mp hg
  have hmem : ∀ x : Fin 7, x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 →
      π ⟨g, hgM2⟩ x = 3 ∨ π ⟨g, hgM2⟩ x = 4 ∨ π ⟨g, hgM2⟩ x = 5 ∨ π ⟨g, hgM2⟩ x = 6 := by
    intro x hx'
    have : π ⟨g, hgM2⟩ • x ∈ π ⟨g, hgM2⟩ • ({3, 4, 5, 6} : Set (Fin 7)) :=
      Set.smul_mem_smul_set (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hx')
    rw [hgΛ] at this
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Equiv.Perm.smul_def] using this
  obtain ⟨i, hi⟩ := exists_m23Word _ _ (hmem 5 (by decide)) (hmem 6 (by decide))
    (fun h => absurd ((π ⟨g, hgM2⟩).injective h) (by decide))
  have hiQ : m23Word i ∈ Q := m23Word_mem h1 h2 h3 i
  obtain ⟨h', hh'J, hh'⟩ := Subgroup.mem_map.mp hiQ
  have hh'J' : (h' : G) ∈ J := hh'J
  have hpair : m23Word i • ({5, 6} : Set (Fin 7)) = π ⟨g, hgM2⟩ • ({5, 6} : Set (Fin 7)) := by
    have e : π ⟨g, hgM2⟩ • ({5, 6} : Set (Fin 7)) = {π ⟨g, hgM2⟩ 5, π ⟨g, hgM2⟩ 6} := by
      rw [Set.smul_set_insert, Set.smul_set_singleton]
      rfl
    rw [e, smul_pair_set_eq_iff]
    exact hi
  have hk : (h' : G)⁻¹ * g ∈ m23I M2 π ⊓ m23Gx T M L H B D := by
    have hkM2 : (h' : G)⁻¹ * g ∈ M2 := M2.mul_mem (M2.inv_mem h'.2) hgM2
    refine Subgroup.mem_inf.mpr ⟨(m23I M2 π).mul_mem ((m23I M2 π).inv_mem (hJI hh'J')) hg,
      (mem_iff_of_inf_eq_setStabIn hA hkM2).mpr ?_⟩
    rw [show (⟨(h' : G)⁻¹ * g, hkM2⟩ : ↥M2) = h'⁻¹ * ⟨g, hgM2⟩ from rfl, map_mul, map_inv,
      mul_smul, ← hpair, hh', inv_smul_smul]
  have := J.mul_mem hh'J' (Subgroup.mem_sup_right hk)
  rwa [mul_inv_cancel_left] at this

end CFSG.Quasithin.H13
