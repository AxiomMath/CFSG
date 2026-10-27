module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSpTools
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.Item413AutSp4
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjAut fieldAut)
open CFSG.QuasithinUnique.Lin2.Five (tauAut tauAut_mul_self frobAut)
open scoped Pointwise

namespace Item434SmallTwoOther

noncomputable def statedProjSp44Equiv :
    StatedProj (StatedSp 2 (GaloisField 2 2)) ≃* StatedSp 2 (GaloisField 2 2) :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSp_eq_bot 2)).trans
    QuotientGroup.quotientBot

noncomputable def sp44Equiv : projSp 2 (GaloisField 2 2) ≃* StatedSp 2 (GaloisField 2 2) :=
  (projSpEquivStatedProj 2 (GaloisField 2 2)).trans statedProjSp44Equiv

theorem card_sp44 : Nat.card (StatedSp 2 (GaloisField 2 2)) = 979200 := by
  rw [SymplecticFlag.card_statedSp, GaloisField.card 2 2 (by norm_num),
    show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
  norm_num

theorem factorization_card_sp44 :
    (Nat.card (StatedSp 2 (GaloisField 2 2))).factorization 3 = 2 := by
  rw [card_sp44, show (979200 : ℕ) = 3 ^ 2 * 108800 by norm_num]
  exact Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)

theorem ringAut_gf4_mul_self (σ : GaloisField 2 2 ≃+* GaloisField 2 2) : σ * σ = 1 := by
  have h := (card_ringAut_and_isCyclic Nat.prime_two (GaloisField 2 2)
    (GaloisField.card 2 2 (by norm_num))).1
  have h2 := pow_card_eq_one' (G := GaloisField 2 2 ≃+* GaloisField 2 2) (x := σ)
  rwa [h, sq] at h2

theorem mem_range_conj_of_pow_three_ps44
    (α : MulAut (StatedProj (StatedSp 2 (GaloisField 2 2)))) (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : StatedProj (StatedSp 2 (GaloisField 2 2)) →* _).range := by
  set N := (conjAut 2 (GaloisField 2 2)).range with hN
  set C := (fieldAut 2 (GaloisField 2 2)).range with hC
  have hNn : N.Normal := KFacts.range_conjAut_normal_of_charTwo
  have hsq := sq_mem_sup_of_normal_form (N := N) (C := C) (t := tauAut)
    (fun c hc => by
      obtain ⟨σ, rfl⟩ := hc
      exact KFacts.tauAut_mul_fieldAut σ)
    ⟨frobAut _, tauAut_mul_self.symm⟩
    (fun g => by
      obtain ⟨A, σ, ε, hε, hg⟩ := KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow g
      exact ⟨_, ⟨A, rfl⟩, _, ⟨σ, rfl⟩, ε, hε, hg⟩)
  have hsq2 : ∀ x ∈ N ⊔ C, x * x ∈ N := by
    intro x hx
    have hmem : x ∈ (N : Set (MulAut (StatedProj (StatedSp 2 (GaloisField 2 2))))) *
        (C : Set (MulAut (StatedProj (StatedSp 2 (GaloisField 2 2))))) := by
      rw [← Subgroup.normal_mul]
      exact hx
    obtain ⟨n, hn, c, hc, rfl⟩ := Set.mem_mul.mp hmem
    obtain ⟨σ, rfl⟩ := hc
    have hcc : fieldAut 2 (GaloisField 2 2) σ * fieldAut 2 (GaloisField 2 2) σ = 1 := by
      rw [← map_mul, ringAut_gf4_mul_self, map_one]
    have h1 : n * fieldAut 2 (GaloisField 2 2) σ * (n * fieldAut 2 (GaloisField 2 2) σ) =
        n * (fieldAut 2 (GaloisField 2 2) σ * n * (fieldAut 2 (GaloisField 2 2) σ)⁻¹) *
          (fieldAut 2 (GaloisField 2 2) σ * fieldAut 2 (GaloisField 2 2) σ) := by
      group
    rw [h1, hcc, mul_one]
    exact N.mul_mem hn (hNn.conj_mem n hn _)
  have h4 : α = α * α * (α * α) := by
    calc α = α ^ 3 * α := by rw [hα, one_mul]
      _ = α * α * (α * α) := by
        rw [pow_three]
        simp only [mul_assoc]
  obtain ⟨A, hA⟩ : α ∈ N := by
    rw [h4]
    exact hsq2 _ (hsq α)
  rw [← hA]
  exact KFacts.conjAut_mem_inner_of_charTwo A

theorem mem_range_conj_of_pow_three_sp44 (φ : MulAut (StatedSp 2 (GaloisField 2 2)))
    (hφ : φ ^ 3 = 1) : φ ∈ (MulAut.conj : StatedSp 2 (GaloisField 2 2) →* _).range := by
  have h := mem_range_conj_of_pow_three_ps44 (MulAut.congr statedProjSp44Equiv.symm φ)
    (by rw [← map_pow, hφ, map_one])
  exact (KFacts.isInnerAut_congr statedProjSp44Equiv.symm φ).mp h

theorem center_sp44 : Subgroup.center (StatedSp 2 (GaloisField 2 2)) = ⊥ :=
  CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot_of_sp44 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 2 (GaloisField 2 2)) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic hodd
    (e₀.trans (projSpEquivStatedProj 2 (GaloisField 2 2)))

theorem false_of_sp44 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 2 (GaloisField 2 2)) : False := by
  refine false_of_gen_of_inner h (center_layer_eq_bot_of_sp44 h e₀) (e₀.trans sp44Equiv)
    mem_range_conj_of_pow_three_sp44 center_sp44 fun P _ hPc => ?_
  have hP9 : Nat.card P = 9 := by
    rcases h.card_layerStar with h9 | ⟨h27, -⟩
    · rw [hPc, h9]
    · exfalso
      have hdvd := Subgroup.card_subgroup_dvd_card P
      rw [hPc, h27, card_sp44] at hdvd
      norm_num at hdvd
  obtain ⟨g, rfl⟩ := exists_map_conj_of_sylow
    (P₀ := SymplecticTorusWeyl.torus 2 (GaloisField 2 2))
    (by rw [card_torus_gf4, factorization_card_sp44]) (by rw [hP9, card_torus_gf4]; norm_num)
  exact closure_hyperCent_map_conj closure_hyperCent_torus_gf4 g

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtSp44 : Item434SmallTwoOtherAtSp44 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoOther.false_of_sp44 hc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
