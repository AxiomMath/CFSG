module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.Struct
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructA.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Ind
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Fixed
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613.KFunctor

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem sSet_one_eq_empty_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) :
    sSet p A θ 1 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun F hF => ?_
  have h1 := (h.mem_sSet_one_iff hF.1).mp hF
  rw [hA.bN_eq F hF.1, hF.1.2] at h1
  have h2 : p < p ^ 2 := by nlinarith [h.prime.one_lt]
  rw [pow_one] at h1
  omega

theorem kOf_line_of_typeA (h : Counterexample p A θ) (hA : TypeA p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : kOf (thetaOf θ F) = thetaOf θ F := by
  obtain ⟨a, ha, ha1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  exact hA.kOf_eq a ha ha1

theorem isRegFam_line_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) :
    IsRegFam A (thetaOf θ F) (lcal (thetaOf θ F)) F := by
  have h1 := h.isRegFam_lcal hF.1 (h.ne_bot_of_mem_E1 hF) (kOf_line_of_typeA h hA hF)
  rwa [hA.bN_eq F hF] at h1

theorem card_lcal_line_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : Nat.card (lcal (thetaOf θ F)) = p ^ 2 := by
  have h1 := (isRegFam_line_of_typeA h hA hF).card_mul_card
  rw [hF.2, h.card, pow_one] at h1
  exact Nat.eq_of_mul_eq_mul_right h.prime.pos (h1.trans (by ring))

theorem nonempty_mulEquiv_line_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) {L : Subgroup G}
    (hL : L ∈ lcal (thetaOf θ F)) : Nonempty (↥L ≃* ↥(thetaOf θ A)) :=
  h.nonempty_mulEquiv_of_isRegFam hF.1 (h.ne_bot_of_mem_E1 hF) (isRegFam_line_of_typeA h hA hF) hL
    (h.le_centralizer_of_mem_lcal hF.1 hL)

theorem ind_eq_lcal_line_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : Ind (thetaOf θ F) = lcal (thetaOf θ F) := by
  have hΩ := isRegFam_line_of_typeA h hA hF
  exact IsDirectProduct.ind_eq hΩ.isDirectProduct (h.sol_thetaOf hF.1 (h.ne_bot_of_mem_E1 hF))
    hΩ.ne_bot fun L hL => card_lcal_eq_one_of_isFStarSimple (isFStarSimple_of_mem_lcal hL)

theorem card_line_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) :
    Nat.card (thetaOf θ F) = Nat.card (thetaOf θ A) ^ (p ^ 2) := by
  rw [(isRegFam_line_of_typeA h hA hF).card_eq_pow (m := Nat.card (thetaOf θ A)) fun L hL =>
    Nat.card_congr (nonempty_mulEquiv_line_of_typeA h hA hF hL).some.toEquiv,
    card_lcal_line_of_typeA h hA hF]

theorem kOf_plane_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : kOf (thetaOf θ B) = thetaOf θ B :=
  T613.kOf_thetaOf_plane h (sSet_one_eq_empty_of_typeA h hA) hB

theorem bN_plane_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : bN A θ B = B := by
  have hB0 := h.ne_bot_of_mem_E2 hB
  obtain ⟨F, hF, hFB⟩ := h.exists_line_le_of_mem_E2 hB
  obtain ⟨F', hF', -, hF'F, hsup⟩ := h.exists_line_sup_eq_of_mem_E2 hB hF hFB
  have h1 := h.card_lcal_thetaOf_sup hF' hF
  have hnle : ¬ F' ≤ F := fun hle =>
    hF'F (Subgroup.eq_of_le_of_card_ge hle (by rw [hF.2, hF'.2]))
  rw [hA.bN_eq _ hF, sup_comm F', hsup, card_lcal_line_of_typeA h hA hF] at h1
  simp only [hnle, ↓reduceIte] at h1
  have h2 : Nat.card (lcal (thetaOf θ B)) = p :=
    Nat.eq_of_mul_eq_mul_left h.prime.pos (h1.symm.trans (by ring))
  have h3 := h.lemma_6_9_c hB.1 hB0
  rw [h2, h.card] at h3
  have h4 : Nat.card (bN A θ B) = p ^ 2 :=
    Nat.eq_of_mul_eq_mul_left h.prime.pos (h3.trans (by ring))
  exact (Subgroup.eq_of_le_of_card_ge (h.le_bN_of_le hB.1 hB0) (by rw [h4, hB.2])).symm

theorem isRegFam_plane_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) :
    IsRegFam A (thetaOf θ B) (lcal (thetaOf θ B)) B := by
  have h1 := h.isRegFam_lcal hB.1 (h.ne_bot_of_mem_E2 hB) (kOf_plane_of_typeA h hA hB)
  rwa [bN_plane_of_typeA h hA hB] at h1

theorem card_lcal_plane_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : Nat.card (lcal (thetaOf θ B)) = p := by
  have h1 := (isRegFam_plane_of_typeA h hA hB).card_mul_card
  rw [hB.2, h.card] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 2) (h1.trans (by ring))

theorem nonempty_mulEquiv_plane_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ)
    {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) {L : Subgroup G}
    (hL : L ∈ lcal (thetaOf θ B)) : Nonempty (↥L ≃* ↥(thetaOf θ A)) :=
  h.nonempty_mulEquiv_of_isRegFam hB.1 (h.ne_bot_of_mem_E2 hB) (isRegFam_plane_of_typeA h hA hB)
    hL (h.le_centralizer_of_mem_lcal hB.1 hL)

theorem ind_eq_lcal_plane_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : Ind (thetaOf θ B) = lcal (thetaOf θ B) := by
  have hΩ := isRegFam_plane_of_typeA h hA hB
  exact IsDirectProduct.ind_eq hΩ.isDirectProduct (h.sol_thetaOf hB.1 (h.ne_bot_of_mem_E2 hB))
    hΩ.ne_bot fun L hL => card_lcal_eq_one_of_isFStarSimple (isFStarSimple_of_mem_lcal hL)

theorem lcal_plane_eq_smear_of_typeA
    (h : Counterexample p A θ) (hA : TypeA p A θ) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1) (hab : b ∉ Subgroup.zpowers a) :
    lcal (thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) =
      {Y | ∃ L ∈ lcal (thetaOf θ (Subgroup.zpowers a)), Y = smear L (Subgroup.zpowers b)} := by
  have hb1 : b ≠ 1 := fun h1 => hab (h1 ▸ one_mem _)
  have hFa := h.zpowers_mem_E1 ha ha1
  have hFb := h.zpowers_mem_E1 hb hb1
  have hne : Subgroup.zpowers a ≠ Subgroup.zpowers b := fun heq =>
    hab (heq ▸ Subgroup.mem_zpowers b)
  have hP := h.sup_mem_E2_of_ne hFa hFb hne
  have hFN : Subgroup.zpowers b ⊓ Subgroup.zpowers a = ⊥ := by
    rw [inf_comm]
    exact h.inf_eq_bot_of_ne_E1 hFa hFb hne
  have hΩ := isRegFam_line_of_typeA h hA hFa
  have hsm := hΩ.smear_family h.elemAbelian.1 hFb.1 hFN
  rw [h.thetaOf_line_inf_centralizer hFa hFb.1] at hsm
  rw [← ind_eq_lcal_plane_of_typeA h hA hP]
  refine IsDirectProduct.ind_eq hsm.isDirectProduct
    (h.sol_thetaOf hP.1 (h.ne_bot_of_mem_E2 hP)) hsm.ne_bot ?_
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨e⟩ := hΩ.nonempty_mulEquiv_smear hFb.1 hFN hL
  exact card_lcal_eq_one_of_mulEquiv e (isFStarSimple_of_mem_lcal hL)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
