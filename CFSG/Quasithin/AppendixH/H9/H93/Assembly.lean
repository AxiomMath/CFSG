module

public import CFSG.Quasithin.AppendixH.H9.H93.Part1
public import CFSG.Quasithin.AppendixH.H9.H93.Theta
public import CFSG.Quasithin.AppendixH.H9.H93.JThompson
public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitR
public import CFSG.Quasithin.AppendixH.H9.H93.RankA1
public import CFSG.Quasithin.AppendixH.H9.H93.RankA2

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement Matrix

private theorem rk_fixV_conjAut {V : Type*} [CommGroup V] (g : MulAut V)
    (A : Subgroup (MulAut V)) : rk ↥(fixV (conjAut g A)) = rk ↥(fixV A) := by
  unfold rk
  rw [conjAut_eq_map, fixV_map_conj_eq, card_map_aut]

private theorem gammaCheck_top_conjAut {V : Type*} [CommGroup V] (k : ℕ) (g : MulAut V)
    (A : Subgroup (MulAut V)) (h : E3.gammaCheck k A = ⊤) :
    E3.gammaCheck k (conjAut g A) = ⊤ := by
  rw [gammaCheck_conjAut, h]
  exact Subgroup.map_top_of_surjective _ g.surjective

private theorem orbitSizes_trichotomy (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) (hab : IsElemAbelian2 A)
    (hc : Nat.card A = 16) :
    orbitSizesOf (imgPermOf ψ A) = {4, 4} ∨ orbitSizesOf (imgPermOf ψ A) = {4, 2, 2} ∨
      orbitSizesOf (imgPermOf ψ A) = {2, 2, 2, 2} :=
  orbitSizes_of_e16 ((isElemAbelian2_iff_imgPermOf ψ hA).mp hab)
    (by rw [card_imgPermOf ψ hA]; exact hc)

private theorem orbitSizes_of_le_Lg (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A : Subgroup (MulAut (PairN 4))} (hAM : A ≤ Mg 4) (hAL : A ≤ Lg 4) (hab : IsElemAbelian2 A)
    (hc : Nat.card A = 16) : orbitSizesOf (imgPermOf ψ A) = {4, 4} :=
  (e16_le_alternatingGroup_iff ((isElemAbelian2_iff_imgPermOf ψ hAM).mp hab)
    (by rw [card_imgPermOf ψ hAM]; exact hc)).mp
    ((le_Lg_iff_imgPermOf_le_alt ψ hAM).mp hAL)

private theorem exists_conj_of_orbitSizes (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8))
    {A B : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) (hB : B ≤ Mg 4) (habA : IsElemAbelian2 A)
    (habB : IsElemAbelian2 B) (hcA : Nat.card A = 16) (hcB : Nat.card B = 16)
    (h : orbitSizesOf (imgPermOf ψ A) = orbitSizesOf (imgPermOf ψ B)) :
    ∃ g ∈ Mg 4, conjAut g A = B := by
  obtain ⟨g', hg'⟩ := exists_conj_of_orbitSizes_eq ((isElemAbelian2_iff_imgPermOf ψ hA).mp habA)
    (by rw [card_imgPermOf ψ hA]; exact hcA) ((isElemAbelian2_iff_imgPermOf ψ hB).mp habB)
    (by rw [card_imgPermOf ψ hB]; exact hcB) h
  exact exists_conjAut_of_imgPermOf_conj ψ hA hB hg'

private theorem orbitSizes_eq_of_conjAut (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {g : MulAut (PairN 4)}
    (hg : g ∈ Mg 4) {A B : Subgroup (MulAut (PairN 4))} (hA : A ≤ Mg 4) (h : conjAut g A = B) :
    orbitSizesOf (imgPermOf ψ B) = orbitSizesOf (imgPermOf ψ A) := by
  rw [← h, imgPermOf_conjAut ψ hg hA, orbitSizesOf_map_conj]

private theorem orbitSizes_A1g (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) :
    orbitSizesOf (imgPermOf ψ A1g) = {2, 2, 2, 2} := by
  have hab := (isElemAbelian2_iff_imgPermOf ψ A1g_le_Mg).mp A1g_isElemAbelian2
  have hc : Nat.card (imgPermOf ψ A1g) = 16 := by rw [card_imgPermOf ψ A1g_le_Mg]; exact A1g_card
  have hcount := ncard_cycleType_two_four_of_e16 hab hc
  have hn : Set.ncard {x : Equiv.Perm (Fin 8) | x ∈ imgPermOf ψ A1g ∧
      x.cycleType = {2, 2, 2, 2}} = 1 := by
    rw [← ncard_isTvElt_inter_eq ψ A1g_le_Mg]; exact ncard_tv_A1g
  rcases orbitSizes_of_e16 hab hc with h | h | h
  · rw [hcount.1 h] at hn; omega
  · rw [hcount.2.1 h] at hn; omega
  · exact h

private theorem orbitSizes_A2g (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) :
    orbitSizesOf (imgPermOf ψ A2g) = {4, 2, 2} := by
  have hab := (isElemAbelian2_iff_imgPermOf ψ A2g_le_Mg).mp A2g_isElemAbelian2
  have hc : Nat.card (imgPermOf ψ A2g) = 16 := by rw [card_imgPermOf ψ A2g_le_Mg]; exact A2g_card
  have hcount := ncard_cycleType_two_four_of_e16 hab hc
  have hn : Set.ncard {x : Equiv.Perm (Fin 8) | x ∈ imgPermOf ψ A2g ∧
      x.cycleType = {2, 2, 2, 2}} = 3 := by
    rw [← ncard_isTvElt_inter_eq ψ A2g_le_Mg]; exact ncard_tv_A2g
  rcases orbitSizes_of_e16 hab hc with h | h | h
  · rw [hcount.1 h] at hn; omega
  · exact h
  · rw [hcount.2.2 h] at hn; omega

theorem h93_main (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) :
    ((∀ t ∈ Mg 4, t ∉ Lg 4 → orderOf t = 2 →
        ((psiExt ψ t).cycleType = {2} ∨ (psiExt ψ t).cycleType = {2, 2, 2})) ∧
      (∃ t ∈ Mg 4, t ∉ Lg 4 ∧ orderOf t = 2 ∧ (psiExt ψ t).cycleType = {2}) ∧
      (∃ u ∈ Mg 4, u ∉ Lg 4 ∧ orderOf u = 2 ∧ (psiExt ψ u).cycleType = {2, 2, 2}) ∧
      (∀ t ∈ Mg 4, ∀ u ∈ Mg 4, t ∉ Lg 4 → u ∉ Lg 4 → orderOf t = 2 → orderOf u = 2 →
        (psiExt ψ t).cycleType = (psiExt ψ u).cycleType → IsConjIn (Mg 4) t u) ∧
      (∀ t ∈ Mg 4, t ∉ Lg 4 → orderOf t = 2 → (psiExt ψ t).cycleType = {2} →
        Nonempty (↥(Lg 4 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 4)))) ≃*
          Equiv.Perm (Fin 6))) ∧
      (∀ u ∈ Mg 4, u ∉ Lg 4 → orderOf u = 2 → (psiExt ψ u).cycleType = {2, 2, 2} →
        Nonempty (↥(Lg 4 ⊓ Subgroup.centralizer ({u} : Set (MulAut (PairN 4)))) ≃*
          (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))))) ∧
    (∀ t ∈ Mg 4, t ∉ Lg 4 → orderOf t = 2 → ThetaIso 4 t) ∧
    ∀ T : Subgroup (MulAut (PairN 4)), IsSylowIn 2 T (Mg 4) →
      ∃ A₁ A₂ : Subgroup (MulAut (PairN 4)),
        (A₁ ≤ Mg 4 ∧ IsElemAbelian2 A₁ ∧ Nat.card A₁ = 16 ∧ ¬ A₁ ≤ Lg 4 ∧
          orbitSizesOf (imgPermOf ψ A₁) = {2, 2, 2, 2}) ∧
        (A₂ ≤ Mg 4 ∧ IsElemAbelian2 A₂ ∧ Nat.card A₂ = 16 ∧ ¬ A₂ ≤ Lg 4 ∧
          orbitSizesOf (imgPermOf ψ A₂) = {2, 2, 4}) ∧
        (thompsonJ (T ⊓ stabSub (V1n 4)) ≤ Mg 4 ∧
          IsElemAbelian2 (thompsonJ (T ⊓ stabSub (V1n 4))) ∧
          Nat.card (thompsonJ (T ⊓ stabSub (V1n 4))) = 16 ∧
          orbitSizesOf (imgPermOf ψ (thompsonJ (T ⊓ stabSub (V1n 4)))) = {4, 4}) ∧
        (∀ A : Subgroup (MulAut (PairN 4)), A ≤ Mg 4 → IsElemAbelian2 A → Nat.card A = 16 →
          (∃ g ∈ Mg 4, conjAut g (thompsonJ (T ⊓ stabSub (V1n 4))) = A) ∨
            (∃ g ∈ Mg 4, conjAut g A₁ = A) ∨ (∃ g ∈ Mg 4, conjAut g A₂ = A)) ∧
        (¬ ∃ g ∈ Mg 4, conjAut g (thompsonJ (T ⊓ stabSub (V1n 4))) = A₁) ∧
        (¬ ∃ g ∈ Mg 4, conjAut g (thompsonJ (T ⊓ stabSub (V1n 4))) = A₂) ∧
        (¬ ∃ g ∈ Mg 4, conjAut g A₁ = A₂) ∧
        (rk ↥(fixV (thompsonJ (T ⊓ stabSub (V1n 4)))) = 4 ∧
          E3.gammaCheck 2 (thompsonJ (T ⊓ stabSub (V1n 4))) = ⊤) ∧
        (rk ↥(fixV A₁) = 1 ∧
          ∃ r ∈ A₁, (r ∈ Lg 4 ∧ rk ↥(commOn (V1n 4) (Subgroup.zpowers r)) = 1) ∧
            (∀ r' ∈ A₁, (r' ∈ Lg 4 ∧ rk ↥(commOn (V1n 4) (Subgroup.zpowers r')) = 1) → r' = r) ∧
            E3.gammaCheck 2 A₁ = fixV (Subgroup.zpowers r) ∧ rk ↥(fixV (Subgroup.zpowers r)) = 6) ∧
        (∀ a ∈ A₂, a ∉ Lg 4 →
          ((fixV A₂ : Subgroup (PairN 4)) : Set (PairN 4)) =
              {x | ∃ w ∈ V1n 4 ⊓ fixV (A₂ ⊓ Lg 4), x = w * a w} ∧
            rk ↥(fixV A₂) = 2 ∧
            E3.gammaCheck 2 A₂ = fixV (A₂ ⊓ Lg 4) ⊔ fixV (Subgroup.zpowers a) ∧
            rk ↥(E3.gammaCheck 2 A₂) = 6) := by
  refine ⟨h93_part1 ψ, fun t ht htL ht2 => thetaIso_of_outer_involution 4 t ht htL ht2, ?_⟩
  intro T hT
  obtain ⟨hJL, hJab, hJc⟩ := thompsonJ_Sylow_facts ψ hT
  have hJM : thompsonJ (T ⊓ stabSub (V1n 4)) ≤ Mg 4 := hJL.trans Lg_le_Mg
  have hJtype := orbitSizes_of_le_Lg ψ hJM hJL hJab hJc
  have hA2type : orbitSizesOf (imgPermOf ψ A2g) = {2, 2, 4} := by
    rw [orbitSizes_A2g ψ]; decide
  refine ⟨A1g, A2g, ⟨A1g_le_Mg, A1g_isElemAbelian2, A1g_card, A1g_not_le_Lg, orbitSizes_A1g ψ⟩,
    ⟨A2g_le_Mg, A2g_isElemAbelian2, A2g_card, A2g_not_le_Lg, hA2type⟩,
    ⟨hJM, hJab, hJc, hJtype⟩, ?_, ?_, ?_, ?_, ?_, rank_A1g, rank_A2g⟩
  · intro A hA hab hc
    rcases orbitSizes_trichotomy ψ hA hab hc with h | h | h
    · exact Or.inl (exists_conj_of_orbitSizes ψ hJM hA hJab hab hJc hc (hJtype.trans h.symm))
    · refine Or.inr (Or.inr ?_)
      exact exists_conj_of_orbitSizes ψ A2g_le_Mg hA A2g_isElemAbelian2 hab A2g_card hc
        (by rw [orbitSizes_A2g ψ, h])
    · refine Or.inr (Or.inl ?_)
      exact exists_conj_of_orbitSizes ψ A1g_le_Mg hA A1g_isElemAbelian2 hab A1g_card hc
        (by rw [orbitSizes_A1g ψ, h])
  · rintro ⟨g, hg, h⟩
    have := orbitSizes_eq_of_conjAut ψ hg hJM h
    rw [orbitSizes_A1g ψ, hJtype] at this
    exact absurd this (by decide)
  · rintro ⟨g, hg, h⟩
    have := orbitSizes_eq_of_conjAut ψ hg hJM h
    rw [orbitSizes_A2g ψ, hJtype] at this
    exact absurd this (by decide)
  · rintro ⟨g, hg, h⟩
    have := orbitSizes_eq_of_conjAut ψ hg A1g_le_Mg h
    rw [orbitSizes_A2g ψ, orbitSizes_A1g ψ] at this
    exact absurd this (by decide)
  · obtain ⟨g, hg, hgR⟩ := exists_conj_of_orbitSizes ψ (Rg4_le_Lg.trans Lg_le_Mg) hJM
      Rg4_isElemAbelian2 hJab Rg4_card hJc
      ((orbitSizes_of_le_Lg ψ (Rg4_le_Lg.trans Lg_le_Mg) Rg4_le_Lg Rg4_isElemAbelian2
        Rg4_card).trans hJtype.symm)
    obtain ⟨h1, h2⟩ := rank_Rg4
    have key : ∀ J : Subgroup (MulAut (PairN 4)), conjAut g Rg4 = J →
        rk ↥(fixV J) = 4 ∧ E3.gammaCheck 2 J = ⊤ := by
      rintro J rfl
      exact ⟨(rk_fixV_conjAut g Rg4).trans h1, gammaCheck_top_conjAut 2 g Rg4 h2⟩
    exact key _ hgR

end CFSG.ASVolI.ChH
