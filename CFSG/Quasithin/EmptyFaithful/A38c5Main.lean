module

public import CFSG.Quasithin.EmptyFaithful.A38c5Ctx
public import CFSG.Quasithin.EmptyFaithful.S153GStrong

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

namespace CFSG.Quasithin.A38c5

section Conj

variable {G : Type} [Group G]

theorem rk_cjSub (g : G) (X : Subgroup G) : rk ↥(cjSub g X) = rk ↥X := by
  unfold rk
  rw [card_cjSub]

theorem cjSub_inf (g : G) (X Y : Subgroup G) : cjSub g (X ⊓ Y) = cjSub g X ⊓ cjSub g Y :=
  Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem cjSub_centralizer (g : G) (Y : Subgroup G) :
    cjSub g (Subgroup.centralizer (Y : Set G)) =
      Subgroup.centralizer ((cjSub g Y : Subgroup G) : Set G) :=
  centralizer_map_mulEquiv (MulAut.conj g) Y

end Conj

end CFSG.Quasithin.A38c5

namespace CFSG.Quasithin

open CFSG.Quasithin.A38c5

theorem countStrongD_of_finite_fact (hFM : FiniteFactS8)
    (hPre : Input32Preamble) : CountStrongD := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA hstrong
  have hP32 : Preamble32 T V₁ I L := hPre G T Mc M V₁ V₂ Yp I L t c
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t :=
    (c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L).ctx.hyp
  have ht'N : t' ∈ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp.hyp hyp.decomp ht'T
  have ht'XS : t' ∈ Subgroup.normalizer ((X153 T M V₁ ⊔ Sgp153 T V₁ : Subgroup G) : Set G) :=
    S153H.mem_normalizer_sup (S153H.T_le_normalizer_X c ht'T) ht'N
  have ht'P : t' ∈ Subgroup.normalizer (P153 T M V₁ : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _ ht'XS
  obtain ⟨A', hA', rfl⟩ : ∃ A' : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) A' ∧ A = cjSub t' A' :=
    ⟨cjSub t'⁻¹ A, isMaxElemAbelian_cjSub (inv_mem ht'N) hA, (cjSub_cjSub_inv t' A).symm⟩
  have hPeq : cjSub t' (P153 T M V₁) = P153 T M V₁ := map_conj_eq_of_mem_normalizer ht'P
  have e3 : cm3 (conjBy153 t' (UL153 T I L)) (cjSub t' A') = cm3 (UL153 T I L) A' := by
    show rk ↥(cjSub t' (UL153 T I L)) - rk ↥(cjSub t' (UL153 T I L) ⊓
      Subgroup.centralizer ((cjSub t' A' : Subgroup G) : Set G)) = _
    rw [← cjSub_centralizer, ← cjSub_inf, rk_cjSub, rk_cjSub]
  have e2 : rk ↥(cjSub t' A') - rk ↥(cjSub t' A' ⊓
      Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) =
      rk ↥A' - rk ↥(A' ⊓ Subgroup.centralizer ((UL153 T I L : Subgroup G) : Set G)) := by
    show rk ↥(cjSub t' A') - rk ↥(cjSub t' A' ⊓
      Subgroup.centralizer ((cjSub t' (UL153 T I L) : Subgroup G) : Set G)) = _
    rw [← cjSub_centralizer, ← cjSub_inf, rk_cjSub, rk_cjSub]
  have e1 : cm1 (P153 T M V₁) (conjBy153 t' (UL153 T I L)) (cjSub t' A') =
      cm1 (P153 T M V₁) (UL153 T I L) A' := by
    have h1 : cjSub t' A' ⊓ P153 T M V₁ = cjSub t' (A' ⊓ P153 T M V₁) := by
      rw [cjSub_inf, hPeq]
    have h2 : cjSub t' A' ⊓ P153 T M V₁ ⊓
        Subgroup.centralizer ((cjSub t' (UL153 T I L) : Subgroup G) : Set G) =
        cjSub t' (A' ⊓ P153 T M V₁ ⊓ Subgroup.centralizer ((UL153 T I L : Subgroup G) : Set G)) := by
      rw [cjSub_inf, cjSub_inf, hPeq, cjSub_centralizer]
    show rk ↥(cjSub t' A' ⊓ P153 T M V₁) - rk ↥(cjSub t' A' ⊓ P153 T M V₁ ⊓
      Subgroup.centralizer ((cjSub t' (UL153 T I L) : Subgroup G) : Set G)) = _
    rw [h2, h1, rk_cjSub, rk_cjSub]
  rw [e1, e3]
  refine core_of_ctx hFM hP32 c cc ht'T ht'S hA' ?_
  rw [← e3, ← e2]
  exact hstrong

end CFSG.Quasithin
