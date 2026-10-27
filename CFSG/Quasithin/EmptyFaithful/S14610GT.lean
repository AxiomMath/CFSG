module

public import CFSG.Quasithin.EmptyFaithful.S14610P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.i1_inf_i2 (S : Setting146 G T M) {H : Subgroup G} {u : G} {I I₂ : Subgroup G}
    (c : Hyp14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    i1Of1469 T M I ⊓ I₂ = T ⊓ I := by
  obtain ⟨e⟩ := S.i1_oTwoQuot hLT
  have hTI1 : T ⊓ I ≤ i1Of1469 T M I := le_sup_right
  have hsyl1 : IsSylowTwoOf (T ⊓ I) (i1Of1469 T M I) :=
    B6.isSylowTwoOf_mono hsyl hTI1 (i1Of1469_le T M I)
  have h3 : (T ⊓ I).relIndex (i1Of1469 T M I) = 3 := relIndex_eq_three_of_isSylowTwoOf e hsyl1
  have hle : T ⊓ I ≤ i1Of1469 T M I ⊓ I₂ := le_inf hTI1 c.le_I₂
  rcases eq_or_eq_of_relIndex_prime Nat.prime_three hle inf_le_left h3 with h | h
  · exact h
  · exfalso
    have hI₁ : i1Of1469 T M I ≤ I₂ := h.symm.le.trans inf_le_right
    have hG : I₂ ≤ mcOf T := c.I₂_le.trans (S.le_mcOf c.hH)
    exact S.not_lI_le_mcOf hLT (le_sup_left.trans (hI₁.trans hG))

theorem Setting146.isGoldschmidtTripleIn_14610 (S : Setting146 G T M) {H : Subgroup G} {u : G}
    {I I₂ : Subgroup G} (c : Hyp14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    F6.IsGoldschmidtTripleIn I (i1Of1469 T M I) I₂ := by
  refine ⟨c.gen.symm, S.i1_oTwoQuot hLT, c.s3, ?_⟩
  rw [S.i1_inf_i2 c hsyl hLT]
  exact hsyl

end CFSG.Quasithin
