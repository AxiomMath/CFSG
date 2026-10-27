module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import CFSG.Quasithin.EmptyFaithful.A38c5FmDefs

public section

namespace CFSG.Quasithin.A38c5.Fm

open MulAction
open scoped Pointwise

private theorem blk_classify : ∀ F : Finset (Fin 8), (∀ x, x ∈ F ↔ partner x ∈ F) →
    (0 : Fin 8) ∈ F → F = {0, 1} ∨ F ∈ blocks3 ∨ 6 ≤ F.card := by
  decide +kernel

private theorem blk_card_blocks3 : ∀ F ∈ blocks3, F.card = 4 := by
  decide +kernel

private theorem blk_swap_mem (M : Subgroup P8) (hD : D8 ≤ M) :
    Equiv.swap (0 : Fin 8) 1 ∈ M ∧ Equiv.swap (2 : Fin 8) 3 ∈ M ∧ Equiv.swap (4 : Fin 8) 5 ∈ M ∧
      Equiv.swap (6 : Fin 8) 7 ∈ M := by
  have h : ∀ g ∈ ({Equiv.swap (0 : Fin 8) 1, Equiv.swap 2 3, Equiv.swap 4 5, Equiv.swap 6 7} :
      Set P8), g ∈ M := fun g hg => hD (Subgroup.subset_closure hg)
  exact ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp)⟩

private theorem blk_apply_mem_iff {M : Subgroup P8} {S : Set (Fin 8)} (hS : IsBlock ↥M S)
    {g : P8} (hg : g ∈ M) {a : Fin 8} (ha : a ∈ S) (hga : g a ∈ S) (x : Fin 8) :
    g x ∈ S ↔ x ∈ S := by
  have h := hS.smul_eq_of_mem (g := (⟨g, hg⟩ : ↥M)) ha hga
  have h2 : (⟨g, hg⟩ : ↥M) • x ∈ (⟨g, hg⟩ : ↥M) • S ↔ x ∈ S := Set.smul_mem_smul_set_iff
  rw [h] at h2
  exact h2

private theorem blk_swap {M : Subgroup P8} {S : Set (Fin 8)} (hS : IsBlock ↥M S)
    (hS2 : S.Nontrivial) {a b : Fin 8} (hab : Equiv.swap a b ∈ M) (ha : a ∈ S) : b ∈ S := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hS2
  by_cases hy : ∃ y ∈ S, y ≠ a ∧ y ≠ b
  · obtain ⟨y, hyS, hya, hyb⟩ := hy
    have h := blk_apply_mem_iff hS hab hyS (by rwa [Equiv.swap_apply_of_ne_of_ne hya hyb]) a
    rw [Equiv.swap_apply_left] at h
    exact h.mpr ha
  · push Not at hy
    by_cases hpa : p = a
    · have hqa : q ≠ a := fun h => hpq (hpa.trans h.symm)
      exact hy q hq hqa ▸ hq
    · exact hy p hp hpa ▸ hp

private theorem blk_swap_iff {M : Subgroup P8} {S : Set (Fin 8)} (hS : IsBlock ↥M S)
    (hS2 : S.Nontrivial) {a b : Fin 8} (hab : Equiv.swap a b ∈ M) : a ∈ S ↔ b ∈ S :=
  ⟨blk_swap hS hS2 hab, blk_swap hS hS2 (by rwa [Equiv.swap_comm])⟩

private theorem blk_pair {M : Subgroup P8} (hD : D8 ≤ M) {S : Set (Fin 8)}
    (hS : IsBlock ↥M S) (hS2 : S.Nontrivial) (x : Fin 8) : x ∈ S ↔ partner x ∈ S := by
  obtain ⟨h01, h23, h45, h67⟩ := blk_swap_mem M hD
  have h10 : Equiv.swap (1 : Fin 8) 0 ∈ M := by rwa [Equiv.swap_comm]
  have h32 : Equiv.swap (3 : Fin 8) 2 ∈ M := by rwa [Equiv.swap_comm]
  have h54 : Equiv.swap (5 : Fin 8) 4 ∈ M := by rwa [Equiv.swap_comm]
  have h76 : Equiv.swap (7 : Fin 8) 6 ∈ M := by rwa [Equiv.swap_comm]
  fin_cases x
  · exact blk_swap_iff hS hS2 h01
  · exact blk_swap_iff hS hS2 h10
  · exact blk_swap_iff hS hS2 h23
  · exact blk_swap_iff hS hS2 h32
  · exact blk_swap_iff hS hS2 h45
  · exact blk_swap_iff hS hS2 h54
  · exact blk_swap_iff hS hS2 h67
  · exact blk_swap_iff hS hS2 h76

private theorem blk_pigeon (g : P8) (F : Finset (Fin 8)) (hF : F.card = 4)
    (h : ∀ a ∈ F, g a ∉ F) (x : Fin 8) (hx : x ∉ F) : g x ∈ F := by
  by_contra hgx
  have h1 : (insert x F).card = 5 := by rw [Finset.card_insert_of_notMem hx, hF]
  have h2 : (insert x F).image g ⊆ Fᶜ := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_insert] at hy
    obtain ⟨a, ha | ha, rfl⟩ := hy
    · subst ha
      simpa using hgx
    · simpa using h a ha
  have h3 := Finset.card_le_card h2
  rw [Finset.card_image_of_injective _ g.injective, h1, Finset.card_compl, Fintype.card_fin,
    hF] at h3
  omega

theorem overgroup_classification (M : Subgroup P8) (hM : M ≠ ⊤) (hD : D8 ≤ M)
    (htrans : ∀ x y : Fin 8, ∃ g ∈ M, g x = y) :
    M ≤ Smu ∨ ∃ B ∈ blocks3, M ≤ PStab B := by
  classical
  have hpt : IsPretransitive ↥M (Fin 8) := ⟨fun x y => by
    obtain ⟨g, hg, hgxy⟩ := htrans x y
    exact ⟨⟨g, hg⟩, hgxy⟩⟩
  obtain ⟨h01, -, -, -⟩ := blk_swap_mem M hD
  obtain ⟨S, h0S, hS, hnt⟩ : ∃ S : Set (Fin 8), (0 : Fin 8) ∈ S ∧ IsBlock ↥M S ∧
      ¬ IsTrivialBlock S := by
    by_contra hcon
    push Not at hcon
    have hprim : IsPreprimitive ↥M (Fin 8) :=
      IsPreprimitive.of_isTrivialBlock_base 0 (fun h0 hS => hcon _ h0 hS)
    exact hM (Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim _
      ⟨0, 1, by decide, rfl⟩ h01)
  have hS2 : S.Nontrivial := Set.not_subsingleton_iff.mp fun h => hnt (Or.inl h)
  have hSu : S ≠ Set.univ := fun h => hnt (Or.inr h)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin 8), ∀ x, x ∈ F ↔ x ∈ S :=
    ⟨S.toFinset, fun x => Set.mem_toFinset⟩
  have hSF : S = (F : Set (Fin 8)) := Set.ext fun x => (hF x).symm
  have hcard : S.ncard = F.card := by rw [hSF, Set.ncard_coe_finset]
  have hpair : ∀ x, x ∈ F ↔ partner x ∈ F := fun x => by
    rw [hF, hF]
    exact blk_pair hD hS hS2 x
  rcases blk_classify F hpair ((hF 0).2 h0S) with h | h | h
  · left
    have hS01 : S = {0, 1} := by
      rw [hSF, h]
      ext x
      simp
    have key : ∀ g ∈ M, g 1 = partner (g 0) := by
      intro g hg
      have hgS : IsBlock ↥M ((⟨g, hg⟩ : ↥M) • S) := hS.translate _
      have hg0 : g 0 ∈ (⟨g, hg⟩ : ↥M) • S :=
        Set.smul_mem_smul_set (a := (⟨g, hg⟩ : ↥M)) h0S
      have hg1 : g 1 ∈ (⟨g, hg⟩ : ↥M) • S :=
        Set.smul_mem_smul_set (a := (⟨g, hg⟩ : ↥M)) (b := 1) (by rw [hS01]; simp)
      have hgS2 : ((⟨g, hg⟩ : ↥M) • S).Nontrivial :=
        ⟨g 0, hg0, g 1, hg1, fun h => absurd (g.injective h) (by decide)⟩
      have h2 := (blk_pair hD hgS hgS2 (g 1)).1 hg1
      obtain ⟨y, hy, hgy⟩ := Set.mem_smul_set.mp h2
      rw [hS01] at hy
      rcases hy with rfl | hy
      · have hgy' : g 0 = partner (g 1) := hgy
        rw [hgy', partner_partner]
      · have hy1 : y = 1 := hy
        subst hy1
        exact absurd hgy.symm (partner_ne _)
    intro g hg x
    obtain ⟨k, hk, hkx⟩ := htrans 0 x
    have e1 := key k hk
    have e2 := key (g * k) (M.mul_mem hg hk)
    simp only [Equiv.Perm.mul_apply, hkx] at e1 e2
    show g (partner x) = partner (g x)
    rw [← e1]
    exact e2
  · right
    have h4 : F.card = 4 := blk_card_blocks3 F h
    refine ⟨F, h, ?_⟩
    intro g hg
    show (∀ x, g x ∈ F ↔ x ∈ F) ∨ (∀ x, g x ∈ F ↔ x ∉ F)
    by_cases hex : ∃ a ∈ F, g a ∈ F
    · left
      obtain ⟨a, haF, hgaF⟩ := hex
      intro x
      rw [hF, hF]
      exact blk_apply_mem_iff hS hg ((hF a).1 haF) ((hF (g a)).1 hgaF) x
    · right
      push Not at hex
      intro x
      by_cases hx : x ∈ F
      · simp [hx, hex x hx]
      · simp [hx, blk_pigeon g F h4 hex x hx]
  · exfalso
    apply hSu
    apply hS.eq_univ_of_card_lt
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega

end CFSG.Quasithin.A38c5.Fm
