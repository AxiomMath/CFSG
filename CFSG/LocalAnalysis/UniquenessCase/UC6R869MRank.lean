module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.R869S

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_centralizer_of_pRank_mulAut_le {M L : Subgroup G} (hLM : L ≤ M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    (hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ k) {B : Subgroup G}
    (hBM : B ≤ M) (hBN : B ≤ normalizer (L : Set G)) (hBel : IsElemAbelian p B)
    (hBcard : Nat.card B = p ^ (k + 2)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup G}
    (hEL : E ≤ L) (hE : IsPGroup q E) :
    2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  let φ : ↥B →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hBN)
  have hRel : IsElemAbelian p φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self B]
    exact (hBel.subgroupOf B).map φ
  have hR : Nat.card φ.range ≤ p ^ k := by
    obtain ⟨j, hj⟩ := hRel.isPGroup.exists_card_eq
    rw [hj]
    exact Nat.pow_le_pow_right hp.pos
      ((CFSG.SectionRank.le_pRank hp.one_lt le_top hRel hj).trans hAut)
  have hKc : p ^ 2 ≤ Nat.card φ.ker := by
    have h1 : p ^ k * p ^ 2 ≤ p ^ k * Nat.card φ.ker :=
      calc p ^ k * p ^ 2 = Nat.card φ.ker * Nat.card φ.range := by
            rw [Subgroup.card_ker_mul_card_range, hBcard]
            ring
        _ ≤ Nat.card φ.ker * p ^ k := Nat.mul_le_mul_left _ hR
        _ = p ^ k * Nat.card φ.ker := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos k)
  let B₀ : Subgroup G := φ.ker.map B.subtype
  have hB₀B : B₀ ≤ B := Subgroup.map_subtype_le _
  have hB₀card : p ^ 2 ≤ Nat.card B₀ := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact hKc
  obtain ⟨A, hAB₀, hAel, hAc⟩ := UC6S846.exists_card_p_sq hp (hBel.mono hB₀B) hB₀card
  have hNO := UC6S846.normalizer_le_normalizer_pCoreOf L
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hq hq2 hp hp2
    (pCoreOf 2 L) A E (UC6S846.isPGroup_pCoreOf L) ((hAB₀.trans (hB₀B.trans hBN)).trans hNO)
    ((hEL.trans Subgroup.le_normalizer).trans hNO) hAel.isPGroup hE (fun e he a ha => by
      obtain ⟨b, hb, rfl⟩ := hAB₀ ha
      have h1 : UC6S846.rhoL L (Subgroup.inclusion hBN b) = 1 := hb
      have h2 : (b : G) * e * (b : G)⁻¹ * e⁻¹ ∈ pCoreOf 2 L :=
        (UC6S846.rhoL_fix_iff L (Subgroup.inclusion hBN b) ⟨e, hEL he⟩).1
          (by rw [h1, MulAut.one_apply])
      have h3 : e * (b : G) * e⁻¹ * (b : G)⁻¹ = ((b : G) * e * (b : G)⁻¹ * e⁻¹)⁻¹ := by group
      change e * (b : G) * e⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 L
      rw [h3]
      exact inv_mem h2)
  have hA'M : A' ≤ M :=
    hA'le.trans (sup_le (hAB₀.trans (hB₀B.trans hBM)) ((Subgroup.map_subtype_le _).trans hLM))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = p ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
  exact CFSG.SectionRank.le_pRank hp.one_lt (le_inf hA'M hA'C) hA'el hA'c

end CFSG.LocalAnalysis.UniquenessCase.UC6.R869S
