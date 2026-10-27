module

public import CFSG.Timmesfeld.ARS.Sec3Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec3

theorem conjSub_ne_of_special (hR : IsRootClass R) (hiso : NoIsolated R) {A B : Subgroup G}
    (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    conjSub B a ≠ B := by
  intro hBa
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  apply hb1
  refine eq_one_of_commute_of_special hR hiso hA hB h ha ha1 hb ?_
  have hne : B ≠ ⁅A, B⁆ := by
    have := h.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm] at this
  have h1 : ⁅a, b⁆ ∈ B ⊓ ⁅A, B⁆ := by
    refine ⟨?_, Subgroup.commutator_mem_commutator ha hb⟩
    rw [commutatorElement_def]
    refine B.mul_mem ?_ (B.inv_mem hb)
    rw [← hBa]
    exact conj_mem_conjSub a hb
  rw [inf_eq_bot hR hiso hB h.1 hne, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem sup_conjSub_eq_of_special [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : B ⊔ conjSub B a = ⁅B, A⁆ ⊔ B :=
  sup_eq_of_le_of_commuting hR hiso h.symm.1 hB hB (hR.conjSub_mem hB a) h.symm.2.1 le_sup_right
    (conjSub_le_commutator_sup ha) (conjSub_ne_of_special hR hiso hA hB h ha ha1).symm

theorem commutator_sup_le_of_commuting {H K L : Subgroup G} (hHK : Commuting H K)
    (hHKL : Commuting H (K ⊔ L)) (hHL : Commuting H L) : ⁅H ⊔ K, L⁆ ≤ ⁅K, L⁆ := by
  have hle : K ≤ Subgroup.normalizer (H : Set G) :=
    (commuting_iff_le_centralizer.1 hHK).trans (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.commutator_le]
  intro x hx l hl
  have hx' : x ∈ ((H ⊔ K : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H K hle] at hx'
  obtain ⟨h, hh, k, hk, rfl⟩ := hx'
  dsimp only
  have hkl : ⁅k, l⁆ ∈ ⁅K, L⁆ := Subgroup.commutator_mem_commutator hk hl
  have hkl' : ⁅k, l⁆ ∈ K ⊔ L := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right hl)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hk)))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hl))
  have e : ⁅h * k, l⁆ = h * ⁅k, l⁆ * h⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc h * k * l * (h * k)⁻¹ * l⁻¹ = h * (k * l * k⁻¹) * (h⁻¹ * l⁻¹) := by group
      _ = h * (k * l * k⁻¹) * (l⁻¹ * h⁻¹) := by rw [(hHL h hh l hl).inv_inv.eq]
      _ = h * (k * l * k⁻¹ * l⁻¹) * h⁻¹ := by group
  rw [e, (hHKL h hh _ hkl').eq, mul_inv_cancel_right]
  exact hkl

end Sec3

open Sec3

theorem commutator_conjSub_eq_of_special [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ psiSet R A) (hC : C ∈ psiSet R A)
    (hBC : Commuting B C) (hq : 2 < Nat.card A) {a₀ : G} (ha₀ : a₀ ∈ A)
    (h : ⁅conjSub B a₀, C⁆ ≠ ⊥) :
    ⁅conjSub B a₀, C⁆ ∈ R ∧
      (∀ a ∈ A, a ≠ 1 → ⁅conjSub B a, C⁆ = ⁅conjSub B a₀, C⁆ ∧
        ⁅B, conjSub C a⁆ = ⁅conjSub B a₀, C⁆) ∧
      Commuting ⁅conjSub B a₀, C⁆ (A ⊔ B ⊔ C) := by
  have hBR : B ∈ R := hB.1
  have hCR : C ∈ R := hC.1
  have hAB : Special R A B := hB.2
  have hAC : Special R A C := hC.2
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    rw [conjSub_one] at h
    exact h (commuting_iff_commutator_eq_bot.1 hBC)
  have hXY : ∀ a ∈ A, Commuting (B ⊔ conjSub C a) (conjSub B a ⊔ C) := fun a ha =>
    commuting_sup_conjSub hR hBR hCR hAB.symm hAC hBC ha
  have hlineB : ∀ a ∈ A, a ≠ 1 → B ⊔ conjSub B a = ⁅B, A⁆ ⊔ B := fun a ha ha1 =>
    sup_conjSub_eq_of_special hR hiso hA hBR hAB ha ha1
  have hlineC : ∀ a ∈ A, a ≠ 1 → C ⊔ conjSub C a = ⁅C, A⁆ ⊔ C := fun a ha ha1 =>
    sup_conjSub_eq_of_special hR hiso hA hCR hAC ha ha1
  have hcommB : ∀ a ∈ A, a ≠ 1 → ⁅conjSub B a, C⁆ = ⁅⁅B, A⁆ ⊔ B, C⁆ := by
    intro a ha ha1
    rw [← hlineB a ha ha1]
    refine le_antisymm (Subgroup.commutator_mono le_sup_right le_rfl) ?_
    have hBBa : Commuting B (conjSub B a) := (hXY a ha).mono le_sup_left le_sup_left
    exact commutator_sup_le_of_commuting hBBa ((hXY a ha).mono le_sup_left le_rfl) hBC
  have hcommC : ∀ a ∈ A, a ≠ 1 → ⁅B, conjSub C a⁆ = ⁅B, ⁅C, A⁆ ⊔ C⁆ := by
    intro a ha ha1
    rw [← hlineC a ha ha1, Subgroup.commutator_comm B, Subgroup.commutator_comm B]
    refine le_antisymm (Subgroup.commutator_mono le_sup_right le_rfl) ?_
    have hCCa : Commuting C (conjSub C a) := ((hXY a ha).mono le_sup_right le_sup_right).symm
    exact commutator_sup_le_of_commuting hCCa ((hXY a ha).symm.mono le_sup_right
      (sup_comm (conjSub C a) B ▸ le_rfl)) hBC.symm
  set L := ⁅conjSub B a₀, C⁆ with hLdef
  set M := ⁅B, ⁅C, A⁆ ⊔ C⁆ with hMdef
  have hLa : ∀ a ∈ A, a ≠ 1 → conjSub L a = M := by
    intro a ha ha1
    have ha' : a⁻¹ ∈ A := A.inv_mem ha
    have ha1' : a⁻¹ ≠ 1 := inv_ne_one.2 ha1
    rw [hLdef, hcommB a₀ ha₀ ha₀1, ← hcommB a⁻¹ ha' ha1', conjSub,
      Subgroup.map_commutator, ← conjSub, ← conjSub, ← conjSub_mul, mul_inv_cancel,
      conjSub_one, hcommC a ha ha1]
  have hAL : ∀ y ∈ A, conjSub L y = L := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1, conjSub_one]
    obtain ⟨a', ha', ha'1, ha'y⟩ : ∃ a' ∈ A, a' ≠ 1 ∧ a' ≠ y⁻¹ := by
      by_contra! hcon
      have hsub : (A : Set G) ⊆ {1, y⁻¹} := fun x hx => by
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · exact Or.inr (hcon x hx hx1)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [← Nat.card_coe_set_eq] at hle
      have h2 := Set.ncard_insert_le (1 : G) {y⁻¹}
      rw [Set.ncard_singleton] at h2
      have : Nat.card ↥A ≤ 2 := hle.trans h2
      omega
    have ha'y' : a' * y ≠ 1 := fun e => ha'y (eq_inv_of_mul_eq_one_left e)
    have h1 := hLa a' ha' ha'1
    have h2 := hLa (a' * y) (A.mul_mem ha' hy) ha'y'
    rw [conjSub_mul, ← h1] at h2
    exact (map_conj_inj.1 h2.symm).symm
  obtain ⟨-, hY⟩ := (commuting_or_special_conjSub hR hiso hBR hA hCR hAB.symm hAC hBC ha₀
    ha₀1).resolve_left fun hc => h (commuting_iff_commutator_eq_bot.1 hc.2)
  have hLR : L ∈ R := hY.1
  have hCAL : Commuting A L := commuting_of_forall_conjSub_eq hR hA hLR hAL hiso
  have hLM : L = M := by
    rw [← hLa a₀ ha₀ ha₀1, conjSub_of_forall_commute fun x hx => hCAL a₀ ha₀ x hx]
  refine ⟨hLR, fun a ha ha1 => ⟨?_, ?_⟩, ?_⟩
  · rw [hcommB a ha ha1, ← hcommB a₀ ha₀ ha₀1]
  · rw [hcommC a ha ha1]
    exact hLM.symm
  · obtain ⟨hX, -⟩ := (commuting_or_special_conjSub hR hiso hBR hA hCR hAB.symm hAC hBC ha₀
      ha₀1).resolve_left fun hc => h (commuting_iff_commutator_eq_bot.1 hc.2)
    have hMB : Commuting L B := by
      rw [hLM, ← hcommC a₀ ha₀ ha₀1]
      exact hX.2.1
    exact Commuting.sup_right (Commuting.sup_right hCAL.symm hMB) hY.2.2

end CFSG.Timmesfeld.ARS
