module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
public import CFSG.RankThree.PartTwo.Toolkit.M12Clause
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Subgroup CFSG.Blueprint
open CFSG.RankThree.PartTwo.Toolkit (M12SylowData)
open scoped commutatorElement

theorem forall_sylow_of_P0 (Q : ∀ (G : Type) [Group G], Subgroup G → Prop)
    (hQ : ∀ (G G' : Type) [Group G] [Group G'] (φ : G ≃* G') (P : Subgroup G),
      Q G P → Q G' (P.map φ.toMonoidHom))
    (h0 : Q _ Toolkit.M12.P0) (G : Type) [Group G] (h : Nonempty (G ≃* NativeSporadic.M12))
    (P : Sylow 3 G) : Q G P := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card G = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
  have hP0 : Nat.card (Toolkit.M12.P0.map e.symm.toMonoidHom) =
      3 ^ (Nat.card G).factorization 3 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, Toolkit.M12.card_P0, hcard,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 95040 = 3 ^ 3 * 3520 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map hP0 P
  rw [hg, Subgroup.map_map]
  exact hQ _ _ (e.symm.trans (MulAut.conj g)) _ h0

@[expose] def InvertsAt {G : Type} [Group G] (P : Subgroup G) : Prop :=
  ∃ t ∈ normalizer (P : Set G), (∀ z ∈ P ⊓ centralizer (P : Set G), t * z * t⁻¹ = z⁻¹) ∧
    ∃ B : Subgroup G, B ≤ P ∧ Nat.card B = 9 ∧ t ∉ normalizer (B : Set G)

theorem InvertsAt.map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {P : Subgroup G}
    (h : InvertsAt P) : InvertsAt (P.map φ.toMonoidHom) := by
  obtain ⟨t, ht, hinv, B, hBP, hB9, htB⟩ := h
  refine ⟨φ t, ?_, ?_, B.map φ.toMonoidHom, Subgroup.map_mono hBP,
    by rw [Subgroup.card_map_of_injective φ.injective, hB9], ?_⟩
  · rw [Toolkit.normalizer_map_equiv]
    exact Subgroup.mem_map_of_mem _ ht
  · intro z hz
    rw [← map_inf_centralizer] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have := congrArg φ (hinv z₀ hz₀)
    simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using this
  · rw [Toolkit.normalizer_map_equiv]
    intro hmem
    obtain ⟨t', ht', htt'⟩ := hmem
    rw [φ.injective htt'] at ht'
    exact htB ht'

theorem invertsAt_P0 : InvertsAt Toolkit.M12.P0 := by
  open Toolkit.M12 in
  refine ⟨g0, g0_mem_NP, ?_, A, A_le, basisA.card, g0_not_mem_NA⟩
  intro c hc
  rw [inf_centralizer_eq_map_center, center_P0] at hc
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  have hz3 : ⁅x, y⁆ ^ 3 = 1 := cube_of_mem_P0 z_mem_P0
  rw [← conj_zpow, g0_conj_z, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
  have h3 : ⁅x, y⁆ ^ ((3 : ℤ) * k) = 1 := by
    rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hz3, one_zpow]
  calc ⁅x, y⁆ ^ (((2 : ℕ) : ℤ) * k) = ⁅x, y⁆ ^ ((3 : ℤ) * k) * ⁅x, y⁆ ^ (-k) := by
        rw [← zpow_add]; congr 1; push_cast; ring
    _ = ⁅x, y⁆ ^ (-k) := by rw [h3, one_mul]

theorem invertsAt_of_sylow (G : Type) [Group G] (h : Nonempty (G ≃* NativeSporadic.M12))
    (P : Sylow 3 G) : InvertsAt (P : Subgroup G) :=
  forall_sylow_of_P0 (fun _ _ P => InvertsAt P) (fun _ _ _ _ φ _ hP => hP.map φ) invertsAt_P0 G
    h P

section Perm

variable {G : Type} [Group G]

theorem conjugate_le_of_mem_normalizer {P B : Subgroup G} {t : G}
    (ht : t ∈ normalizer (P : Set G)) (hB : B ≤ P) : conjugate B t ≤ P := by
  rintro _ ⟨b, hb, rfl⟩
  have := (mem_normalizer_iff.mp (inv_mem ht) b).mp (hB hb)
  simpa [conjugate] using this

theorem card_conjugate (B : Subgroup G) (t : G) : Nat.card (conjugate B t) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective

theorem conjugate_eq_self_iff {B : Subgroup G} {t : G} :
    conjugate B t = B ↔ t ∈ normalizer (B : Set G) := by
  constructor
  · intro h
    have h' : t⁻¹ ∈ normalizer (B : Set G) :=
      CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq h
    simpa using inv_mem h'
  · intro h
    exact CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer (inv_mem h)

theorem conjugate_injective (t : G) : Function.Injective fun B : Subgroup G => conjugate B t :=
  Subgroup.map_injective (MulAut.conj t⁻¹).injective

theorem ne_of_ncard_four {α : Type*} {a b c d : α} (h : ({a, b, c, d} : Set α).ncard = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hle : ∀ s : Set α, ∀ x : α, (insert x s).ncard ≤ s.ncard + 1 :=
    fun s x => Set.ncard_insert_le x s
  have h3 : ({c, d} : Set α).ncard ≤ 2 := by
    have := hle {d} c
    rw [Set.ncard_singleton] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq
  · rw [Set.insert_eq_of_mem (by simp)] at h
    have := hle {c, d} a
    omega
  · rw [show ({a, b, a, d} : Set α) = {b, a, d} by ext; simp] at h
    have := hle {a, d} b
    have := hle {d} a
    rw [Set.ncard_singleton] at this
    omega
  · rw [show ({a, b, c, a} : Set α) = {b, c, a} by ext; simp] at h
    have := hle {c, a} b
    have := hle {a} c
    rw [Set.ncard_singleton] at this
    omega
  · rw [show ({a, b, b, d} : Set α) = {a, b, d} by ext; simp] at h
    have := hle {b, d} a
    have := hle {d} b
    rw [Set.ncard_singleton] at this
    omega
  · rw [show ({a, b, c, b} : Set α) = {a, b, c} by ext; simp; tauto] at h
    have := hle {b, c} a
    have := hle {c} b
    rw [Set.ncard_singleton] at this
    omega
  · rw [show ({a, b, c, c} : Set α) = {a, b, c} by ext; simp] at h
    have := hle {b, c} a
    have := hle {c} b
    rw [Set.ncard_singleton] at this
    omega

theorem conjugate_eq_of_moves {P E F A A' : Subgroup G} {t : G}
    (hset : {B : Subgroup G | B ≤ P ∧ Nat.card B = 9} = {E, F, A, A'})
    (hncard : ({E, F, A, A'} : Set (Subgroup G)).ncard = 4)
    (ht : t ∈ normalizer (P : Set G)) (hE : t ∈ normalizer (E : Set G))
    (hF : t ∈ normalizer (F : Set G))
    (hmove : ∃ B : Subgroup G, B ≤ P ∧ Nat.card B = 9 ∧ t ∉ normalizer (B : Set G)) :
    conjugate A t = A' := by
  obtain ⟨hEF, hEA, hEA', hFA, hFA', hAA'⟩ := ne_of_ncard_four hncard
  have hmem : ∀ B : Subgroup G, B ∈ ({E, F, A, A'} : Set (Subgroup G)) →
      conjugate B t ∈ ({E, F, A, A'} : Set (Subgroup G)) := by
    intro B hB
    rw [← hset] at hB ⊢
    exact ⟨conjugate_le_of_mem_normalizer ht hB.1, by rw [card_conjugate, hB.2]⟩
  have hcE : conjugate E t = E := conjugate_eq_self_iff.mpr hE
  have hcF : conjugate F t = F := conjugate_eq_self_iff.mpr hF
  have hinj := conjugate_injective t
  have hA := hmem A (by simp)
  have hA' := hmem A' (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hA'
  obtain ⟨B, hBP, hB9, htB⟩ := hmove
  have hB : B ∈ ({E, F, A, A'} : Set (Subgroup G)) := hset ▸ ⟨hBP, hB9⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
  have hnE : conjugate A t ≠ E := fun h => hEA (hinj (hcE.trans h.symm))
  have hnF : conjugate A t ≠ F := fun h => hFA (hinj (hcF.trans h.symm))
  have hnE' : conjugate A' t ≠ E := fun h => hEA' (hinj (hcE.trans h.symm))
  have hnF' : conjugate A' t ≠ F := fun h => hFA' (hinj (hcF.trans h.symm))
  rcases hA with h | h | h | h
  · exact absurd h hnE
  · exact absurd h hnF
  · exfalso
    rcases hA' with h' | h' | h' | h'
    · exact hnE' h'
    · exact hnF' h'
    · exact hAA' (hinj (h.trans h'.symm))
    · rcases hB with rfl | rfl | rfl | rfl
      · exact htB hE
      · exact htB hF
      · exact htB (conjugate_eq_self_iff.mp h)
      · exact htB (conjugate_eq_self_iff.mp h')
  · exact h

end Perm

theorem item4_14_local_at {G : Type} [Group G] {P : Subgroup G} (hD : M12SylowData P)
    (hI : InvertsAt P) :
    IsHeisThree P ∧
    IsKleinFour (normalizer (P : Set G) ⧸ P.subgroupOf (normalizer (P : Set G))) ∧
    ∃ (E F A : Subgroup G) (t : G), t ∈ normalizer (P : Set G) ∧
      (∀ z ∈ P ⊓ centralizer (P : Set G), t * z * t⁻¹ = z⁻¹) ∧
      {B : Subgroup G | B ≤ P ∧ Nat.card B = 9} = {E, F, A, conjugate A t} ∧
      Nonempty (autIn ⊤ E ≃* GL (Fin 2) (ZMod 3)) ∧
      Nonempty (autIn ⊤ F ≃* GL (Fin 2) (ZMod 3)) ∧
      Nonempty (autIn ⊤ A ≃* Equiv.Perm (Fin 3)) ∧
      ∀ a ∈ A, a ∉ P ⊓ centralizer (P : Set G) →
        Nonempty (normalizer (zpowers a : Set G) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) := by
  obtain ⟨hex, hcard, hexp, hQ, hQcard, hncard, -, E, F, A, A', hset, hE, hF, -, -, -,
    ⟨eE⟩, ⟨eF⟩, -, -, ⟨eA⟩, -, hNa, -⟩ := hD
  obtain ⟨t, ht, hinv, hmove⟩ := hI
  have hconj : conjugate A t = A' := conjugate_eq_of_moves hset (hset ▸ hncard) ht (hE ht)
    (hF ht) hmove
  refine ⟨⟨hex, hcard, hexp⟩, isKleinFour_of_isElementaryAbelian hQ hQcard, E, F, A, t, ht,
    hinv, by rw [hconj, hset], ⟨(automizerEquivAutIn E).symm.trans eE⟩,
    ⟨(automizerEquivAutIn F).symm.trans eF⟩, ⟨(automizerEquivAutIn A).symm.trans eA⟩, ?_⟩
  intro a ha hZ
  rw [inf_centralizer_eq_map_center] at hZ
  exact hNa a ha hZ

theorem rank3II_4_14_local : Item4_14_local := by
  intro G _ _ h P
  exact item4_14_local_at (Toolkit.m12ThreeLocalData G h P) (invertsAt_of_sylow G h P)

end CFSG.RankThree.PartTwo.Sec4.Sporadic
