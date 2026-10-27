module

public import CFSG.GH74.GLS.C3.Layer1.EvenSelBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.ABGLocalTools CFSG.PSL2Table CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.L2Borel
  CFSG.Blueprint Polynomial
open scoped MatrixGroups

section Fields

variable {F : Type} [Field F] [Finite F]

theorem uc22p22qe_sum_two_squares (hodd : Odd (Nat.card F)) (c : F) : ∃ a b : F, a ^ 2 + b ^ 2 = c := by
  haveI := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by
    rw [Nat.card_eq_fintype_card] at hodd
    exact Nat.odd_iff.1 hodd
  have hf : (X ^ 2 - C c : F[X]).degree = 2 := by
    rw [degree_sub_C (by rw [degree_X_pow]; exact_mod_cast two_pos)]
    exact degree_X_pow 2
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf (degree_X_pow (R := F) 2) hcard
  refine ⟨a, b, ?_⟩
  simp only [eval_sub, eval_pow, eval_X, eval_C] at hab
  linear_combination hab

theorem uc22p22qe_pow_unip (t : F) (k : ℕ) : mk (unip t) ^ k = mk (unip ((k : F) * t)) := by
  induction k with
  | zero => simp [unip_zero]
  | succ k ih =>
    rw [pow_succ, ih, ← map_mul, ← unip_add]
    congr 2
    push_cast
    ring

theorem uc22p22qe_unipotent_pow {p : ℕ} (hchar : (p : F) = 0) {x : PSL(2, F)} (hx : x ∈ unipotent F) :
    x ^ p = 1 := by
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).1 hx
  rw [uc22p22qe_pow_unip, hchar, zero_mul, unip_zero, map_one]

theorem uc22p22qe_card_unipotent (h2 : (2 : F) ≠ 0) : Nat.card (unipotent F) = Nat.card F := by
  let f : Multiplicative F →* PSL(2, F) :=
    { toFun := fun t => mk (unip (Multiplicative.toAdd t))
      map_one' := by simp [unip_zero]
      map_mul' := fun s t => by simp [unip_add] }
  have hf : Function.Injective f := fun s t h =>
    Multiplicative.toAdd.injective ((mk_unip_eq_mk_unip_iff h2 _ _).1 h)
  have hr : f.range = unipotent F := by
    ext x
    rw [MonoidHom.mem_range, mem_unipotent_iff_exists]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.toAdd t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.ofAdd t, rfl⟩
  calc Nat.card (unipotent F) = Nat.card f.range := by rw [hr]
    _ = Nat.card (Multiplicative F) := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
    _ = Nat.card F := Nat.card_congr Multiplicative.toAdd

theorem uc22p22qe_unipotent_irr (hodd : Odd (Nat.card F)) {W : Subgroup PSL(2, F)} (hWU : W ≤ unipotent F)
    (hT : ∀ a : Fˣ, ∀ x ∈ W, mk (diag a) * x * (mk (diag a))⁻¹ ∈ W) : W = ⊥ ∨ W = unipotent F := by
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨x, hxW⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  obtain ⟨w, rfl⟩ := (mem_unipotent_iff_exists x).1 (hWU hxW)
  have hw : w ≠ 0 := fun h => hx1 (by rw [h, unip_zero, map_one])
  have hsq : ∀ a : F, mk (unip (a ^ 2 * w)) ∈ W := by
    intro a
    by_cases ha : a = 0
    · rw [ha]
      simpa [unip_zero] using W.one_mem
    · have := hT (Units.mk0 a ha) _ hxW
      rwa [mk_conj, diag_conj_unip, Units.val_mk0] at this
  refine le_antisymm hWU fun y hy => ?_
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists y).1 hy
  obtain ⟨a, b, hab⟩ := uc22p22qe_sum_two_squares hodd (t * w⁻¹)
  have : t = a ^ 2 * w + b ^ 2 * w := by
    calc t = (t * w⁻¹) * w := by field_simp
      _ = a ^ 2 * w + b ^ 2 * w := by rw [← hab]; ring
  rw [this, unip_add, map_mul]
  exact W.mul_mem (hsq a) (hsq b)

end Fields

private theorem uc22p22qe_setup {L : Type} [Group L] [Finite L] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel L .PSL 2 p n) {S : Subgroup L} (hS : IsSylowOf p S ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ψ : PSL(2, F) ≃* L),
      Nat.card F = p ^ n ∧ S = (unipotent F).map ψ.toMonoidHom := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hFf, hFfin, e, hF, hFq⟩ :=
    CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' hp hp2 hL
  obtain ⟨-, hSp, hSnd⟩ := isSylowOf_iff.1 hS
  let W : Sylow p L := hSp.toSylow (by simpa [Subgroup.relIndex_top_right] using hSnd)
  obtain ⟨c, hc⟩ := exists_psiEquiv_eq e hp hFq W
  exact ⟨F, hFf, hFfin, psiEquiv e c, hFq, hc⟩

theorem uc22p22q_psl2_sylow_elem {L : Type} [Group L] [Finite L] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel L .PSL 2 p n) {S : Subgroup L} (hS : IsSylowOf p S ⊤) :
    CFSG.Open.IsElemAbelian p S ∧ Nat.card S = p ^ n := by
  obtain ⟨F, hFf, hFfin, ψ, hFq, rfl⟩ := uc22p22qe_setup hp hp2 hL hS
  have hodd : Odd (Nat.card F) := by
    rw [hFq]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hchar : (p : F) = 0 := by
    haveI := Fintype.ofFinite F
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hFq] at h0
    have hn : n ≠ 0 := by
      rintro rfl
      have : Nat.card F = 1 := by simpa using hFq
      exact (Finite.one_lt_card (α := F)).ne' this
    push_cast at h0
    exact pow_eq_zero_iff hn |>.1 h0
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    change (a : L) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, unipotent_mul_comm ha' hb']
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, uc22p22qe_unipotent_pow hchar hy, map_one]
  · rw [Subgroup.card_map_of_injective ψ.injective, uc22p22qe_card_unipotent h2, hFq]

theorem uc22p22q_psl2_borel_irr {L : Type} [Group L] [Finite L] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel L .PSL 2 p n) {S : Subgroup L} (hS : IsSylowOf p S ⊤) {W : Subgroup L}
    (hWS : W ≤ S) (hW : ∀ g ∈ normalizer (S : Set L), ∀ w ∈ W, g * w * g⁻¹ ∈ W) : W = ⊥ ∨ W = S := by
  obtain ⟨F, hFf, hFfin, ψ, hFq, rfl⟩ := uc22p22qe_setup hp hp2 hL hS
  have hodd : Odd (Nat.card F) := by
    rw [hFq]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  set W' : Subgroup PSL(2, F) := W.comap ψ.toMonoidHom with hW'
  have hW'U : W' ≤ unipotent F := by
    intro x hx
    have : ψ x ∈ (unipotent F).map ψ.toMonoidHom := hWS hx
    obtain ⟨y, hy, hyx⟩ := this
    have := ψ.injective hyx
    rwa [← this]
  have hT : ∀ a : Fˣ, ∀ x ∈ W', mk (diag a) * x * (mk (diag a))⁻¹ ∈ W' := by
    intro a x hx
    have hmem : ψ (mk (diag a)) ∈ normalizer (((unipotent F).map ψ.toMonoidHom : Subgroup L) : Set L) := by
      rw [normalizer_map_equiv]
      refine ⟨mk (diag a), ?_, rfl⟩
      rw [normalizer_unipotent_eq h2]
      exact splitTorus_le_borel (mk_diag_mem_splitTorus a)
    have h := hW _ hmem _ hx
    change ψ (mk (diag a) * x * (mk (diag a))⁻¹) ∈ W
    simpa using h
  have hirr := uc22p22qe_unipotent_irr hodd hW'U hT
  have hWeq : W = W'.map ψ.toMonoidHom := (Subgroup.map_comap_eq_self_of_surjective ψ.surjective W).symm
  rcases hirr with h | h
  · left
    rw [hWeq, h, Subgroup.map_bot]
  · right
    rw [hWeq, h]

end CFSG.LocalAnalysis.UniquenessCase.UC22
