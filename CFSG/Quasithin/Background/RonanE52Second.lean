module

public import CFSG.Quasithin.Background.RonanE51Basic

public section

namespace CFSG.Quasithin.RonanE52

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_cjSub_le_centralizer {P Q' A : Subgroup G} {i j : ℕ}
    (hA : IsElemAbelianCorank P i A) (hQ'P : Q' ≤ P)
    (hAQ : Nat.card A ≤ 2 ^ j * Nat.card ↥(A ⊓ Q'))
    (hDQ' : omegaOneCenterOf (H13.thompsonJk (i + j) P) ≤ Q')
    {k : G} (hk : k ∈ Subgroup.normalizer (Q' : Set G)) :
    ∃ D₁ : Subgroup G, D₁ ≤ omegaOneCenterOf (H13.thompsonJk (i + j) P) ∧
      Nat.card ↥(omegaOneCenterOf (H13.thompsonJk (i + j) P)) ≤ 2 ^ (i + j) * Nat.card ↥D₁ ∧
      cjSub k A ≤ Subgroup.centralizer (D₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n := i + j with hn
  set J := H13.thompsonJk n P with hJdef
  set D := omegaOneCenterOf J with hDdef
  set A₁ := A ⊓ Q' with hA₁def
  set W := E5.wGen n P Q' with hWdef
  have hA₁ : A₁ ∈ E5.wFam n P Q' := RonanE51.inf_mem_wFam hA hAQ
  have hAJ : A ≤ J := RonanE51.le_thompsonJk_of_corank (Nat.le_add_right i j) hA
  have hDA : ∀ d ∈ D, ∀ a ∈ A, d * a = a * d := fun d hd a ha =>
    (mem_centralizer_of_mem_omegaOneCenterOf hd (hAJ ha)).symm
  have hDel : IsElemAbelian 2 D := B2F.isElemAbelian_omegaOneCenterOf _
  have hWJ : W ≤ J := E5.wGen_le_thompsonJk hQ'P
  have hWQ' : W ≤ Q' := E5.wGen_le n P Q'
  have hA₁W : A₁ ≤ W := E5.le_wGen hA₁
  have hDW : D ≤ W := RonanE51.le_wGen_of_commute hA₁ hDel hDQ' fun v hv a ha => hDA v hv a ha.1
  set E := omegaOneCenterOf W with hEdef
  have hDE : D ≤ E := fun d hd =>
    mem_omegaOneCenterOf (hDW hd) (fun w hw => mem_centralizer_of_mem_omegaOneCenterOf hd (hWJ hw))
      (hDel.2 d hd)
  have hkW : k ∈ Subgroup.normalizer (W : Set G) :=
    E5.le_normalizer_wGen n (K := Subgroup.zpowers k) (Subgroup.zpowers_le.2 hk)
      (Subgroup.mem_zpowers k)
  have hkE : k ∈ Subgroup.normalizer (E : Set G) := normalizer_le_normalizer_omegaOneCenterOf W hkW
  have hEel : IsElemAbelian 2 E := B2F.isElemAbelian_omegaOneCenterOf W
  have hEA₁ : IsElemAbelian 2 (E ⊔ A₁) :=
    B2F.isElemAbelian_sup_of_commute hEel hA₁.2.1 fun e he a ha =>
      (mem_centralizer_of_mem_omegaOneCenterOf he (hA₁W ha)).symm
  have hEA₁P : E ⊔ A₁ ≤ P :=
    sup_le (((omegaOneCenterOf_le W).trans hWQ').trans hQ'P) (inf_le_left.trans hA.1)
  have hrelE : A₁.relIndex E ≤ 2 ^ n := by
    have h3 := Subgroup.relIndex_mul_card A₁ (E ⊔ A₁)
    have e : A₁ ⊓ (E ⊔ A₁) = A₁ := inf_eq_left.2 le_sup_right
    rw [e] at h3
    have h4 : A₁.relIndex (E ⊔ A₁) * Nat.card ↥A₁ ≤ 2 ^ n * Nat.card ↥A₁ := by
      rw [h3]
      calc Nat.card ↥(E ⊔ A₁) ≤ 2 ^ CFSG.Open.pRank 2 P :=
            VolI.E54.card_le_two_pow_pRank_of_le hEA₁P hEA₁
        _ = Nat.card A * 2 ^ i := hA.2.2.symm
        _ ≤ (2 ^ j * Nat.card ↥A₁) * 2 ^ i := Nat.mul_le_mul_right _ hAQ
        _ = 2 ^ n * Nat.card ↥A₁ := by rw [hn, pow_add]; ring
    exact (Subgroup.relIndex_le_of_le_right le_sup_left (E3.relIndex_ne_zero' _ _)).trans
      (Nat.le_of_mul_le_mul_right h4 Nat.card_pos)
  have hconjE : cjSub k E = E :=
    Subgroup.eq_of_le_of_card_ge (cjSub_le hkE le_rfl) (by rw [card_cjSub])
  refine ⟨D ⊓ cjSub k A₁, inf_le_left, ?_, ?_⟩
  · have h5 : (cjSub k A₁).relIndex E = A₁.relIndex E := by
      conv_lhs => rw [← hconjE]
      exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj k).injective
    have h6 : (cjSub k A₁).relIndex D ≤ (cjSub k A₁).relIndex E :=
      Subgroup.relIndex_le_of_le_right hDE (E3.relIndex_ne_zero' _ _)
    have h7 := Subgroup.relIndex_mul_card (cjSub k A₁) D
    calc Nat.card ↥D = (cjSub k A₁).relIndex D * Nat.card ↥(cjSub k A₁ ⊓ D) := h7.symm
      _ ≤ 2 ^ n * Nat.card ↥(D ⊓ cjSub k A₁) := by
        rw [inf_comm]
        exact Nat.mul_le_mul_right _ (h6.trans (h5 ▸ hrelE))
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyA : y ∈ cjSub k A := (cjSub_mono inf_le_left) (Subgroup.mem_inf.1 hy).2
    exact (B2F.isElemAbelian_comm (isElemAbelian_cjSub hA.2.1) hyA hx)

end CFSG.Quasithin.RonanE52
