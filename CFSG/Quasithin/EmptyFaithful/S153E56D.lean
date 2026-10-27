module

public import CFSG.Quasithin.EmptyFaithful.S153E56C
public import CFSG.Quasithin.EmptyFaithful.S153E56A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace S153E56a

open CFSG.Quasithin.S153E

section Rank

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem card_U (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G}
    {s : ℕ} (c : Chain15354 cx N₁ N₂ g s) : Nat.card ↥(UH153 T M V₁ Mc) = 2 ^ (2 * s + 5) := by
  have hV := cx.c.hyp.elemAbelian
  have hW : Nat.card ↥(UH153 T M V₁ Mc ⊓ Subgroup.centralizer (VZ T M : Set G)) =
      2 ^ (2 * s + 3) := by
    rw [← W_eq cx c]
    exact card_W cx c
  have h4 : Nat.card ↥(autI hV (UH153 T M V₁ Mc)) = 4 := by
    rcases c.h51.two with ⟨-, hK, -⟩ | ⟨hE, -⟩
    · exact hK.1
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := c.h52
      exact hne (B2F.isElemAbelian_comm hE ha hb)
  have h5 := card_autI_mul_card_inf hV (U_le_N cx)
  rw [h4, hW] at h5
  rw [← h5]
  ring

theorem rank_eq (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G}
    {s : ℕ} (c : Chain15354 cx N₁ N₂ g s) :
    mIdx (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) = 2 * (s + 2) := by
  have h1 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)
  rw [inf_eq_left.2 (Z_le_U cx), cx.c.hyp.lemma_15_3_2_two.2, card_U cx c] at h1
  have h2 : (quasithinOmegaOneCenter T).relIndex (UH153 T M V₁ Mc) = 2 ^ (2 * s + 4) := by
    have e : (2 : ℕ) ^ (2 * s + 5) = 2 ^ (2 * s + 4) * 2 := by ring
    rw [e] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  unfold mIdx
  rw [h2, padicValNat.prime_pow]
  ring

end Rank

end S153E56a

namespace S153E

open CFSG.Quasithin.S153E56a

section Lemma

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_15_3_56_rank (_h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15355 cx N₁ N₂ g s) :
    mIdx (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) = 2 * (s + 2) :=
  rank_eq cx c.toChain15354

end Lemma

end S153E

end CFSG.Quasithin
