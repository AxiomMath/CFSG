module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderBasic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.SteinbergCA

open Module CFSG.QuasithinUnique.Setup.Offender

section Codimension

variable {k : Type*} [Field k] {U : Type*} [AddCommGroup U] [Module k U]
variable {E : Type*} [Group E]

theorem centSub_sup (ρ : E →* (U ≃ₗ[k] U)) (Z W : Submodule k U) :
    centSub ρ (Z ⊔ W) = centSub ρ Z ⊓ centSub ρ W := by
  ext a
  constructor
  · intro ha
    exact ⟨fun z hz => ha z (Submodule.mem_sup_left hz),
      fun w hw => ha w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨hZ, hW⟩ v hv
    obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hZ z hz, hW w hw]

theorem centSub_bot (ρ : E →* (U ≃ₗ[k] U)) : centSub ρ (⊥ : Submodule k U) = ⊤ := by
  ext a
  simp only [Subgroup.mem_top, iff_true]
  intro v hv
  rw [(Submodule.mem_bot k).1 hv, map_zero]

theorem finrank_quotient_fixSub_add [FiniteDimensional k U] (ρ : E →* (U ≃ₗ[k] U))
    (W : Submodule k U) (B : Subgroup E) :
    finrank k (↥W ⧸ (fixSub ρ B).comap W.subtype) + finrank k ↥(W ⊓ fixSub ρ B) =
      finrank k W := by
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  exact Submodule.finrank_quotient_add_finrank _

theorem finrank_sub_finrank_fix_sup_ge [FiniteDimensional k U] (ρ : E →* (U ≃ₗ[k] U))
    (Z W : Submodule k U) (B : Subgroup E) :
    ((finrank k Z : ℤ) - finrank k ↥(Z ⊓ fixSub ρ B)) +
        ((finrank k W : ℤ) - finrank k ↥(W ⊓ fixSub ρ (B ⊓ centSub ρ Z))) ≤
      (finrank k ↥(Z ⊔ W) : ℤ) - finrank k ↥((Z ⊔ W) ⊓ fixSub ρ B) := by
  set F := fixSub ρ B with hF
  set F' := fixSub ρ (B ⊓ centSub ρ Z) with hF'
  set C := (Z ⊔ W) ⊓ F with hC
  have hZF' : Z ≤ F' := fun z hz b hb => (Subgroup.mem_inf.1 hb).2 z hz
  have hCle : C ≤ Z ⊔ (W ⊓ F') := by
    intro x hx
    obtain ⟨hxZW, hxF⟩ := Submodule.mem_inf.1 hx
    obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.1 hxZW
    refine Submodule.mem_sup.2 ⟨z, hz, w, Submodule.mem_inf.2 ⟨hw, fun b hb => ?_⟩, rfl⟩
    have h1 := hxF b (Subgroup.mem_inf.1 hb).1
    have h2 := (Subgroup.mem_inf.1 hb).2 z hz
    rw [map_add, h2] at h1
    exact add_left_cancel h1
  have hZC : Z ⊓ C = Z ⊓ F := by
    rw [hC, ← inf_assoc, inf_sup_self]
  have hZW' : Z ⊓ (W ⊓ F') = Z ⊓ W := by
    rw [← inf_assoc, inf_of_le_left (inf_le_left.trans hZF')]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq Z W
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq Z C
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Z (W ⊓ F')
  have h5 := Submodule.finrank_mono (sup_le le_sup_left hCle : Z ⊔ C ≤ Z ⊔ (W ⊓ F'))
  rw [hZC] at h2
  rw [hZW'] at h3
  omega

end Codimension

section Indices

variable {E : Type*} [Group E] [Finite E]

theorem exists_relIndex_eq_pow {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E) (H L : Subgroup E) :
    ∃ c, H.relIndex L = p ^ c := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (hE.to_subgroup L)
  have hdvd : H.relIndex L ∣ p ^ a := ha ▸ Subgroup.index_dvd_card (H.subgroupOf L)
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  exact ⟨c, hc⟩

theorem log_relIndex_inf {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E) (H K L : Subgroup E) :
    Nat.log p ((H ⊓ K).relIndex L) = Nat.log p (H.relIndex (K ⊓ L)) + Nat.log p (K.relIndex L) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨a, ha⟩ := exists_relIndex_eq_pow hE H (K ⊓ L)
  obtain ⟨b, hb⟩ := exists_relIndex_eq_pow hE K L
  rw [← Subgroup.relIndex_inf_mul_relIndex, ha, hb, ← pow_add, Nat.log_pow hp.one_lt,
    Nat.log_pow hp.one_lt, Nat.log_pow hp.one_lt]

end Indices

theorem strict_fixed_space_bounds_pass_from_invariant_generators_to_their_sum {p : ℕ}
    [Fact p.Prime] {E : Type*} [Group E] [Finite E] (hE : IsPGroup p E) {U : Type*}
    [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]
    (ρ : E →* (U ≃ₗ[ZMod p] U)) {n : ℕ} (V : Fin n → Submodule (ZMod p) U) (hV : ⨆ i, V i = ⊤)
    (k : ℕ)
    (hbound : ∀ (i : Fin n) (B : Subgroup E), ¬ B ≤ centSub ρ (V i) →
      k * Nat.log p ((centSub ρ (V i)).relIndex B) <
        finrank (ZMod p) (↥(V i) ⧸ (fixSub ρ B).comap (V i).subtype))
    (B : Subgroup E) (hB : ¬ B ≤ centSub ρ ⊤) :
    k * Nat.log p ((centSub ρ ⊤).relIndex B) < finrank (ZMod p) (U ⧸ fixSub ρ B) := by
  classical
  set Z : ℕ → Submodule (ZMod p) U := fun m => ⨆ (j : Fin n) (_ : (j : ℕ) < m), V j with hZ
  have hZ0 : Z 0 = ⊥ := by
    simp [hZ]
  have hZsucc : ∀ m (hm : m < n), Z (m + 1) = Z m ⊔ V ⟨m, hm⟩ := by
    intro m hm
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le (iSup₂_le fun j hj =>
      le_iSup₂_of_le (f := fun (j : Fin n) (_ : (j : ℕ) < m + 1) => V j) j (by omega) le_rfl)
      (le_iSup₂_of_le (f := fun (j : Fin n) (_ : (j : ℕ) < m + 1) => V j) ⟨m, hm⟩
        (by simp) le_rfl))
    by_cases hjm : (j : ℕ) < m
    · exact le_sup_of_le_left
        (le_iSup₂_of_le (f := fun (j : Fin n) (_ : (j : ℕ) < m) => V j) j hjm le_rfl)
    · have hj : j = ⟨m, hm⟩ := Fin.ext (show (j : ℕ) = m by omega)
      rw [hj]
      exact le_sup_right
  have hZn : Z n = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hV]
    exact iSup_le fun j =>
      le_iSup₂_of_le (f := fun (j : Fin n) (_ : (j : ℕ) < n) => V j) j j.2 le_rfl
  have key : ∀ m ≤ n,
      ((k * Nat.log p ((centSub ρ (Z m)).relIndex B) : ℕ) : ℤ) ≤
          (finrank (ZMod p) (Z m) : ℤ) - finrank (ZMod p) ↥(Z m ⊓ fixSub ρ B) ∧
        (¬ B ≤ centSub ρ (Z m) →
          ((k * Nat.log p ((centSub ρ (Z m)).relIndex B) : ℕ) : ℤ) <
            (finrank (ZMod p) (Z m) : ℤ) - finrank (ZMod p) ↥(Z m ⊓ fixSub ρ B)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [hZ0, centSub_bot, Subgroup.relIndex_top_left, bot_inf_eq, finrank_bot]
      refine ⟨by simp, fun h => absurd le_top h⟩
    | succ m ih =>
      intro hm
      have hmn : m < n := by omega
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      set W := V ⟨m, hmn⟩ with hW
      set B' := B ⊓ centSub ρ (Z m) with hB'
      have hA := finrank_sub_finrank_fix_sup_ge ρ (Z m) W B
      rw [← hB', ← hZsucc m hmn] at hA
      have hcent : centSub ρ (Z (m + 1)) = centSub ρ W ⊓ centSub ρ (Z m) := by
        rw [hZsucc m hmn, centSub_sup, inf_comm]
      have hL : Nat.log p ((centSub ρ (Z (m + 1))).relIndex B) =
          Nat.log p ((centSub ρ W).relIndex B') + Nat.log p ((centSub ρ (Z m)).relIndex B) := by
        rw [hcent, log_relIndex_inf hE, hB', inf_comm B]
      have hq := finrank_quotient_fixSub_add ρ W B'
      have hW1 : ((k * Nat.log p ((centSub ρ W).relIndex B') : ℕ) : ℤ) ≤
          (finrank (ZMod p) W : ℤ) - finrank (ZMod p) ↥(W ⊓ fixSub ρ B') := by
        by_cases hBW : B' ≤ centSub ρ W
        · rw [Subgroup.relIndex_eq_one.2 hBW, Nat.log_one_right, mul_zero, Nat.cast_zero]
          have := Submodule.finrank_mono (inf_le_left : W ⊓ fixSub ρ B' ≤ W)
          omega
        · have := hbound ⟨m, hmn⟩ B' hBW
          rw [← hW] at this
          omega
      refine ⟨?_, fun hBZ => ?_⟩
      · rw [hL]
        push_cast
        push_cast at ih1 hW1
        linarith
      · rw [hL]
        push_cast
        push_cast at ih1 hW1
        by_cases hBm : B ≤ centSub ρ (Z m)
        ·
          have hB'B : B' = B := inf_of_le_left hBm
          have hBW : ¬ B' ≤ centSub ρ W := fun h => hBZ (by
            rw [hcent]
            exact le_inf (hB'B ▸ h) hBm)
          have h1 := hbound ⟨m, hmn⟩ B' hBW
          rw [← hW] at h1
          have h2 : ((k * Nat.log p ((centSub ρ W).relIndex B') : ℕ) : ℤ) <
              (finrank (ZMod p) W : ℤ) - finrank (ZMod p) ↥(W ⊓ fixSub ρ B') := by
            omega
          push_cast at h2
          linarith
        · have h2 := ih2 hBm
          push_cast at h2
          linarith
  obtain ⟨-, hstrict⟩ := key n le_rfl
  rw [hZn] at hstrict
  have h1 := hstrict hB
  have h2 := Submodule.finrank_quotient_add_finrank (fixSub ρ B)
  rw [top_inf_eq, finrank_top] at h1
  omega

end CFSG.Quasithin.SteinbergCA
