module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp48Inner
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIOuterE9

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.RankThreeEven (projSp)
open KFacts

namespace Item434SmallTwoIII

section Out

open CFSG.QuasithinUnique.Lin2.Five (tauAut)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem card_outer_sp48_le :
    Nat.card (Outer (StatedProj (StatedSp 2 (GaloisField 2 3)))) ≤ 6 := by
  have hR : Nat.card (GaloisField 2 3 ≃+* GaloisField 2 3) = 3 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two
      (GaloisField 2 3) (by rw [card_gf8]; norm_num : Nat.card (GaloisField 2 3) = 2 ^ 3)).1
  have : Finite (GaloisField 2 3 ≃+* GaloisField 2 3) :=
    Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  set q := QuotientGroup.mk' (inner (StatedProj (StatedSp 2 (GaloisField 2 3)))) with hq
  have hsurj : Function.Surjective
      (fun p : (GaloisField 2 3 ≃+* GaloisField 2 3) × Fin 2 =>
        q (fieldAut 2 (GaloisField 2 3) p.1 * tauAut ^ (p.2 : ℕ))) := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨A, σ, ε, hε, rfl⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
    refine ⟨(σ, ⟨ε, by omega⟩), ?_⟩
    have hc : q (conjAut 2 _ A) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_inner_of_charTwo A)
    change q (fieldAut 2 _ σ * tauAut ^ ε) = q (conjAut 2 _ A * fieldAut 2 _ σ * tauAut ^ ε)
    rw [mul_assoc, map_mul q (conjAut 2 _ A), hc, one_mul]
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod, hR, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h1

end Out

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_sp48_twentySeven (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 2 (GaloisField 2 3))
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  set θ := e₀.trans (projSpEquivStatedProj 2 (GaloisField 2 3)) with hθ
  have hCA : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
    have h1 := h.card_inf_mul_card_layerStar
    change _ * Nat.card (A.map (layerConj G)) = 27 at h1
    rw [h27] at h1
    rw [← Subgroup.card_eq_one]
    omega
  have hA27 := Item434Kit.card_map_quotConj h hCA θ
  obtain ⟨E, hEe, hE9, hEN⟩ := exists_map_conj_le_of_card_27
    (CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot (GaloisField 2 3))
    (lt_of_le_of_lt card_outer_sp48_le (by norm_num))
    (Item434Kit.isElemAbelian_map_quotConj h θ) hA27
  exact Item434Kit.false_of_normalizer h θ fun Y hY3 hYN =>
    eq_bot_of_inn_le_normalizer hEe hE9 hY3 (hEN.trans hYN)

end Ctx

end Item434SmallTwoIII

section Families

theorem item434SmallTwoIII_Sp48_27 : Item434SmallTwoIII_Sp48_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoIII.false_of_sp48_twentySeven hc e₀ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
