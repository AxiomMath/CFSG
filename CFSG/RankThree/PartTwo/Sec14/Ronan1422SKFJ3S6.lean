module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFBase
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SDefs
public import CFSG.Sporadic.Schreier.PairJ3CertBase

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

theorem pow_four_conj_vecPerm2_of_normalizes : ∀ σ : Perm (Fin 6),
    (∀ v : Fin 2 → ZMod 3, ∃ w, vecPerm2 6 w = σ * vecPerm2 6 v * σ⁻¹) →
    ∀ v : Fin 2 → ZMod 3, σ ^ 4 * vecPerm2 6 v * (σ ^ 4)⁻¹ = vecPerm2 6 v := by
  decide +kernel

theorem not_isS6Type_of_pow_four_inv {K : Type*} [Group K] {α : MulAut K} {B : Subgroup K}
    (hB : Nat.card B = 9) (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hαB : ∀ b ∈ B, α b ∈ B)
    (h4 : ∀ b ∈ B, (α ^ 4) b = b⁻¹) : ¬ IsS6Type K α := by
  rintro ⟨ψ, σ, hσ⟩
  set B' := B.map ψ.toMonoidHom with hB'
  have hB'9 : Nat.card B' = 9 := by
    rw [hB', Subgroup.card_map_of_injective ψ.injective, hB]
  obtain ⟨h, hh⟩ := exists_eq_map_conj_F06 hB'9
  have hσn : ∀ n : ℕ, ∀ k : K, ((ψ ((α ^ n) k) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      σ ^ n * (ψ k : Perm (Fin 6)) * (σ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [pow_succ', MulAut.mul_apply, hσ, ih, pow_succ']
      group
  have hmemB' : ∀ x : alternatingGroup (Fin 6), x ∈ B' ↔
      ∃ f ∈ F06, x = h * f * h⁻¹ := by
    intro x
    rw [hh]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, hf, rfl⟩
  have hψB : ∀ b ∈ B, ψ b ∈ B' := fun b hb => ⟨b, hb, rfl⟩
  have hB'ψ : ∀ x ∈ B', ∃ b ∈ B, ψ b = x := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  set σ' : Perm (Fin 6) := (h : Perm (Fin 6))⁻¹ * σ * (h : Perm (Fin 6)) with hσ'
  have hnorm : ∀ v : Fin 2 → ZMod 3, ∃ w, vecPerm2 6 w = σ' * vecPerm2 6 v * σ'⁻¹ := by
    intro v
    have hfv : alt6 (vecPerm2 6 v) (sign_vecPerm2_six v) ∈ F06 := mem_F06.mpr ⟨v, rfl⟩
    obtain ⟨b, hb, hbψ⟩ := hB'ψ _ ((hmemB' _).mpr ⟨_, hfv, rfl⟩)
    obtain ⟨f', hf', hf'eq⟩ := (hmemB' _).mp (hψB _ (hαB b hb))
    obtain ⟨w, hw⟩ := mem_F06.mp hf'
    refine ⟨w, ?_⟩
    have h1 := hσ b
    rw [hf'eq, hbψ] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h3 : ((alt6 (vecPerm2 6 v) (sign_vecPerm2_six v) : alternatingGroup (Fin 6)) :
        Perm (Fin 6)) = vecPerm2 6 v := rfl
    rw [h3] at h1
    rw [hw, hσ']
    have h2 : ((f' : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        (h : Perm (Fin 6))⁻¹ * (σ * ((h : Perm (Fin 6)) * vecPerm2 6 v * (h : Perm (Fin 6))⁻¹) *
          σ⁻¹) * (h : Perm (Fin 6)) := by
      rw [← h1]
      group
    rw [h2]
    group
  have hfix : ∀ b ∈ B, (α ^ 4) b = b := by
    intro b hb
    apply ψ.injective
    apply Subtype.ext
    rw [hσn 4]
    obtain ⟨f, hf, hfeq⟩ := (hmemB' _).mp (hψB b hb)
    obtain ⟨w, hw⟩ := mem_F06.mp hf
    have hc := pow_four_conj_vecPerm2_of_normalizes σ' hnorm w
    rw [hσ'] at hc
    have hc' : σ ^ 4 * ((h : Perm (Fin 6)) * vecPerm2 6 w * (h : Perm (Fin 6))⁻¹) *
        (σ ^ 4)⁻¹ = (h : Perm (Fin 6)) * vecPerm2 6 w * (h : Perm (Fin 6))⁻¹ := by
      have e : ((h : Perm (Fin 6))⁻¹ * σ * (h : Perm (Fin 6))) ^ 4 =
          (h : Perm (Fin 6))⁻¹ * σ ^ 4 * (h : Perm (Fin 6)) := by
        have e1 : (h : Perm (Fin 6))⁻¹ * σ * (h : Perm (Fin 6)) =
            (h : Perm (Fin 6))⁻¹ * σ * ((h : Perm (Fin 6))⁻¹)⁻¹ := by rw [inv_inv]
        rw [e1, conj_pow, inv_inv]
      rw [e] at hc
      calc σ ^ 4 * ((h : Perm (Fin 6)) * vecPerm2 6 w * (h : Perm (Fin 6))⁻¹) * (σ ^ 4)⁻¹
          = (h : Perm (Fin 6)) * (((h : Perm (Fin 6))⁻¹ * σ ^ 4 * (h : Perm (Fin 6))) *
              vecPerm2 6 w * ((h : Perm (Fin 6))⁻¹ * σ ^ 4 * (h : Perm (Fin 6)))⁻¹) *
              (h : Perm (Fin 6))⁻¹ := by group
        _ = (h : Perm (Fin 6)) * vecPerm2 6 w * (h : Perm (Fin 6))⁻¹ := by rw [hc]
    rw [hfeq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hw]
    exact hc'
  have hbot : B = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have h1 : b = b⁻¹ := (hfix b hb).symm.trans (h4 b hb)
    have h2 : b ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel b
    have h3 : b = b ^ 3 * (b ^ 2)⁻¹ := by group
    rw [hB3 b hb, h2] at h3
    simpa using h3
  rw [hbot, Subgroup.card_bot] at hB
  norm_num at hB

@[expose] def J3PermConfig : Prop :=
  ∀ (E K : Subgroup (Equiv.Perm (Fin 6156))) (c : Equiv.Perm (Fin 6156)),
    E ≤ CFSG.Sporadic.Schreier.j3P → K ≤ CFSG.Sporadic.Schreier.j3P →
    CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → c ∈ E → c ≠ 1 →
    K ≤ Subgroup.centralizer {c} → Nonempty (↥K ≃* alternatingGroup (Fin 6)) →
    Nat.card (E ⊓ K : Subgroup (Equiv.Perm (Fin 6156))) = 9 →
      ∃ t ∈ CFSG.Sporadic.Schreier.j3P, t ∈ Subgroup.normalizer (K : Set (Equiv.Perm (Fin 6156))) ∧
        t ∈ Subgroup.normalizer (E : Set (Equiv.Perm (Fin 6156))) ∧
        t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set (Equiv.Perm (Fin 6156))) ∧
        ∀ b ∈ E ⊓ K, t ^ 4 * b * (t ^ 4)⁻¹ = b⁻¹

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
