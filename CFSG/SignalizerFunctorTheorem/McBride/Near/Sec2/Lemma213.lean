module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma213AuxC
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma213AuxD

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

section Lemma213

variable (h : NearAsolvAction p A G) (hsol : sol G = ⊥) (hG1 : G ≠ ⊥) {W : Subgroup Γ}
  (hWK : W ≤ kOf G) (hW : Admits (cenIn G A ⊔ A) W) (hperf : Group.IsPerfect W)

include h hsol hG1 hWK hW hperf

theorem lemma213a
    : IsDirectPair (k1 G W) (k2 G W) (kOf G) :=
  (Lemma213.Hyp.mk h hsol hG1 hWK hW hperf).isDirectPair

theorem lemma213b :
    IsDirectPair (cenIn (k1 G W) A) (cenIn (k2 G W) A) (cenIn (kOf G) A) ∧
      cenIn (k2 G W) A = cenIn W A := by
  have H : Lemma213.Hyp p A G W := ⟨h, hsol, hG1, hWK, hW, hperf⟩
  refine ⟨Lemma213.isDirectPair_cenIn H.isDirectPair H.admits_A_k1 H.admits_A_k2,
    le_antisymm (fun d hd => ?_) (inf_le_inf_right _ H.le_k2)⟩
  obtain ⟨hdK₂, hdA⟩ := Subgroup.mem_inf.1 hd
  have hdW : d ∈ W ⊔ k1 G W :=
    H.cenIn_le_sup (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hdK₂).1, hdA⟩)
  obtain ⟨w, hw, k, hk, rfl⟩ := (mem_sup_iff_of_commute (fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x hx : x * y = y * x))).1 hdW
  have hkK₂ : k ∈ k2 G W := by
    have := mul_mem (inv_mem (H.le_k2 hw)) hdK₂
    simpa using this
  have hk1 : k = 1 := by
    have hmem : k ∈ k1 G W ⊓ k2 G W := Subgroup.mem_inf.2 ⟨hk, hkK₂⟩
    rw [H.isDirectPair.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  subst hk1
  rw [mul_one] at hdA ⊢
  exact Subgroup.mem_inf.2 ⟨hw, hdA⟩

theorem lemma213c
    (hK1 : k1 G W = ⊥) : cenIn G W = ⊥ :=
  (Lemma213.Hyp.mk h hsol hG1 hWK hW hperf).cenIn_eq_bot_of_k1_eq_bot hK1

theorem lemma213d
    {Z₀ Z : Subgroup Γ} (hZ : Z ≤ G) (hZ₀ : IsNormalIn Z₀ Z)
    (hadm₀ : Admits (cenIn G A ⊔ A) Z₀) (_hadm : Admits (cenIn G A ⊔ A) Z)
    (hD : Z₀ ⊓ kOf G ⊓ cenIn G A = cenIn (k1 G W) A) : Admits Z (k1 G W) := by
  exact (Lemma213.Hyp.mk h hsol hG1 hWK hW hperf).admits_k1_of_normal hZ hZ₀ hadm₀ hD

end Lemma213

end CFSG.SignalizerFunctorTheorem.McBride.Near
