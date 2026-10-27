module

public import CFSG.Quasithin.H13.L32AM50f
public import CFSG.Quasithin.Background.SmithB45Alt7Res

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open Equiv Equiv.Perm
open scoped IsMulCommutative

theorem Mod16.card_le_35 {M : Type} [Group M] [Fintype M] [DecidableEq M]
    (h16 : Fintype.card M = 16) (S : Finset (Subgroup M)) (hS : ∀ Y ∈ S, Nat.card Y = 4) :
    S.card ≤ 35 := by
  classical
  set F : Subgroup M → Finset (M × M) := fun Y =>
    ((Finset.univ.filter (· ∈ Y)).erase 1).offDiag with hF
  have hcardY : ∀ Y ∈ S, (Finset.univ.filter (· ∈ Y)).card = 4 := by
    intro Y hY
    rw [← hS Y hY, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hFcard : ∀ Y ∈ S, (F Y).card = 6 := by
    intro Y hY
    rw [hF, Finset.offDiag_card, Finset.card_erase_of_mem (by simp), hcardY Y hY]
  have hdisj : (S : Set (Subgroup M)).PairwiseDisjoint F := by
    intro Y hY Y' hY' hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [hF, Finset.mem_offDiag, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
      true_and] at h1 h2
    obtain ⟨⟨ha1, haY⟩, ⟨hb1, hbY⟩, hab⟩ := h1
    obtain ⟨⟨-, haY'⟩, ⟨-, hbY'⟩, -⟩ := h2
    apply hne
    have h3 : 3 ≤ Nat.card ↥(Y ⊓ Y') := by
      have hsub : ({1, a, b} : Finset M) ⊆ Finset.univ.filter (· ∈ Y ⊓ Y') := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl | rfl
        · exact (Y ⊓ Y').one_mem
        · exact ⟨haY, haY'⟩
        · exact ⟨hbY, hbY'⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm hb1]),
        Finset.card_pair hab] at hc
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact hc
    have hdvd : Nat.card ↥(Y ⊓ Y') ∣ 4 := by
      rw [← hS Y hY]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h4 : Nat.card ↥(Y ⊓ Y') = 4 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      rcases (show Nat.card ↥(Y ⊓ Y') = 3 ∨ Nat.card ↥(Y ⊓ Y') = 4 by omega) with h | h
      · rw [h] at hdvd
        norm_num at hdvd
      · exact h
    have e1 : Y ⊓ Y' = Y :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hS Y hY])
    have e2 : Y ⊓ Y' = Y' :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h4, hS Y' hY'])
    exact e1.symm.trans e2
  have hsum : (S.biUnion F).card = S.card * 6 := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hFcard, Finset.sum_const, smul_eq_mul]
  have hsub : S.biUnion F ⊆ ((Finset.univ : Finset M).erase 1).offDiag := by
    intro ab hab
    obtain ⟨Y, -, hab⟩ := Finset.mem_biUnion.mp hab
    simp only [hF, Finset.mem_offDiag, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true] at hab ⊢
    exact ⟨hab.1.1, hab.2.1.1, hab.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [hsum, Finset.offDiag_card, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    h16] at hc
  omega

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top50

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 7)} (C : Top50 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]
include C

theorem card_stabHat_eq (h16 : Nat.card (Hat V H W) = 16) {X : Subgroup (Hat V H W)}
    (hX : Nat.card X = 4) : Nat.card (C.stabHat X) = 72 := by
  classical
  have : Fintype (Hat V H W) := Fintype.ofFinite _
  set ρ : B45Alt7.A7 → MulAut (Hat V H W) := fun γ => (C.iota.symm γ : MulAut (Hat V H W))
    with hρ
  have hρmul : ∀ a b, ρ (a * b) = ρ a * ρ b := fun a b => by
    simp only [hρ, map_mul, Subgroup.coe_mul]
  have hρinv : ∀ a, ρ a⁻¹ = (ρ a)⁻¹ := fun a => by
    simp only [hρ, map_inv, Subgroup.coe_inv]
  set f : B45Alt7.A7 → Subgroup (Hat V H W) := fun γ => X.map (ρ γ).toMonoidHom with hf
  have himg : ((Finset.univ : Finset B45Alt7.A7).image f).card ≤ 35 := by
    refine Mod16.card_le_35 (by rw [← Nat.card_eq_fintype_card]; exact h16) _ fun Y hY => ?_
    obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hY
    rw [hf, Subgroup.card_map_of_injective (ρ γ).injective, hX]
  have hmem : ∀ a b : B45Alt7.A7, f a = f b →
      ((a⁻¹ * b : B45Alt7.A7) : Perm (Fin 7)) ∈ C.stabHat X := by
    intro a b hab
    have hl : ρ (a⁻¹ * b) = (ρ a)⁻¹ * ρ b := by rw [hρmul, hρinv]
    refine ⟨(a⁻¹ * b).2, fun x hx => ⟨?_, ?_⟩⟩
    · show ρ (a⁻¹ * b) x ∈ X
      rw [hl, MulAut.mul_apply]
      have h1 : ρ b x ∈ f b := ⟨x, hx, rfl⟩
      rw [← hab] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have : (ρ a)⁻¹ (ρ b x) = y := by
        rw [← hyx]
        exact MulAut.inv_apply_self _ _ _
      rw [this]
      exact hy
    · show (ρ (a⁻¹ * b))⁻¹ x ∈ X
      rw [hl, mul_inv_rev, inv_inv, MulAut.mul_apply]
      have h1 : ρ a x ∈ f a := ⟨x, hx, rfl⟩
      rw [hab] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have : (ρ b)⁻¹ (ρ a x) = y := by
        rw [← hyx]
        exact MulAut.inv_apply_self _ _ _
      rw [this]
      exact hy
  have hfib : ∀ Y ∈ (Finset.univ : Finset B45Alt7.A7).image f,
      ((Finset.univ : Finset B45Alt7.A7).filter (fun γ => f γ = Y)).card ≤
        Nat.card (C.stabHat X) := by
    intro Y hY
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hY
    have hmaps : ∀ γ ∈ (Finset.univ : Finset B45Alt7.A7).filter (fun γ => f γ = f a),
        ((a⁻¹ * γ : B45Alt7.A7) : Perm (Fin 7)) ∈
          (Finset.univ : Finset (Perm (Fin 7))).filter (· ∈ C.stabHat X) := by
      intro γ hγ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      exact hmem a γ hγ.symm
    have hinj : Set.InjOn (fun γ : B45Alt7.A7 => ((a⁻¹ * γ : B45Alt7.A7) : Perm (Fin 7)))
        ((Finset.univ : Finset B45Alt7.A7).filter (fun γ => f γ = f a) : Set B45Alt7.A7) := by
      intro γ _ γ' _ h
      exact mul_left_cancel (Subtype.ext h)
    calc _ ≤ ((Finset.univ : Finset (Perm (Fin 7))).filter (· ∈ C.stabHat X)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = Nat.card (C.stabHat X) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hle := Finset.card_le_mul_card_image (f := f) (Finset.univ : Finset B45Alt7.A7) _ hfib
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Alt7.card_alt7] at hle
  have hdvd := C.card_stabHat_dvd h16 hX
  have hpos : 0 < Nat.card (C.stabHat X) := Nat.card_pos
  have hge : 72 ≤ Nat.card (C.stabHat X) := by nlinarith
  exact le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hge

end Top50

end CFSG.Quasithin.H13.L32A.C
