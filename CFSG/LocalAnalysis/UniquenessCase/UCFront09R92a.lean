module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.GroupTheory.ThreeTranspositions.Basic
import CFSG.GroupTheory.ThreeTranspositions.CyclicSylow
import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.OrderPrimeConj
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

variable {G : Type} [Group G] [Finite G]

theorem not_hasE9_L9 {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃) :
    ¬ HasE9 ↥(L9 Y H) := fun h => by
  have h2 := CFSG.GroupTheory.ThreeTranspositions.two_le_pRank_of_hasE9_subgroup (L9 Y H) h
  have h1 : CFSG.Open.pRank 3 (L9 Y H) = 1 := hyp.2.1.2.2
  omega

theorem exists_map_conj_eq_of_card_eq_three {K : Subgroup G} (hK : ¬ HasE9 ↥K)
    {A B : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K) (hA3 : Nat.card A = 3)
    (hB3 : Nat.card B = 3) : ∃ l ∈ K, A.map (MulAut.conj l).toMonoidHom = B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3' : Nat.card (A.subgroupOf K) = 3 := by
    rw [← hA3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hB3' : Nat.card (B.subgroupOf K) = 3 := by
    rw [← hB3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isConj_of_natCard_eq_prime_of_sylow_cyclic
      (fun Q => CFSG.GroupTheory.ThreeTranspositions.isCyclic_of_isPGroup_three hK Q.isPGroup')
      hA3' hB3'
  refine ⟨g, g.2, ?_⟩
  have hc : K.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp K.subtype := by
    ext x
    simp [MulAut.conj_apply]
  have h := congrArg (Subgroup.map K.subtype) hg
  rw [Subgroup.map_map, hc, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAK,
    Subgroup.map_subgroupOf_eq_of_le hBK] at h
  exact h

theorem eq_L9_sup_of_hyp91 {D : Data G} {Y H D₃ : Subgroup G} (hyp : Hyp91 D Y H D₃) :
    H = L9 Y H ⊔ (H ⊓ D.M) := by
  have hXY : Opp 3 Y ≤ Y := opp_le_self 3 Y
  have hXH : Opp 3 Y ≤ H := hXY.trans hyp.2.1.1
  have hLH : L9 Y H ≤ H := iSup_le fun h => by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem h.2 (hXH hx)) (H.inv_mem h.2)
  refine le_antisymm (fun h hh => ?_) (sup_le hLH inf_le_left)
  have hD3 : Nat.card D₃ = 3 := hyp.2.2.2
  have hDL : D₃ ≤ L9 Y H := hyp.2.2.1.trans (opp_le_L9 Y H)
  have hDhL : D₃.map (MulAut.conj h).toMonoidHom ≤ L9 Y H :=
    (Subgroup.map_mono hyp.2.2.1).trans
      (le_iSup (fun k : ↥H => (Opp 3 Y).map (MulAut.conj (k : G)).toMonoidHom) ⟨h, hh⟩)
  have hDh3 : Nat.card (D₃.map (MulAut.conj h).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hD3]
  obtain ⟨l, hlL, hl⟩ :=
    exists_map_conj_eq_of_card_eq_three (not_hasE9_L9 hyp) hDL hDhL hD3 hDh3
  have hn : l⁻¹ * h ∈ normalizer (D₃ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have e : ∀ a b : G, (MulAut.conj (a * b)).toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := fun a b => by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have e1 : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    change D₃.map (MulAut.conj (l⁻¹ * h)).toMonoidHom = D₃
    rw [e, ← Subgroup.map_map, ← hl, Subgroup.map_map, e1, Subgroup.map_id]
  have hDU : D₃ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    hyp.1.2.2 D₃ (hyp.2.2.1.trans hXY) hD3
  have hM : l⁻¹ * h ∈ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hDU hn
  rw [show h = l * (l⁻¹ * h) by group]
  exact Subgroup.mul_mem _ ((le_sup_left : L9 Y H ≤ L9 Y H ⊔ (H ⊓ D.M)) hlL)
    ((le_sup_right : H ⊓ D.M ≤ L9 Y H ⊔ (H ⊓ D.M)) ⟨H.mul_mem (H.inv_mem (hLH hlL)) hh, hM⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
