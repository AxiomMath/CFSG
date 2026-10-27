module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU33Tools
import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL33
import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU3
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Matrix
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace Item434CharThree

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem factorization_card_SU_three_nine {F : Type} [Field F] [Finite F] [CharP F 3]
    (hF : Nat.card F = (3 ^ 1) ^ 2) :
    (Nat.card (SU (unitaryInvolution F 3 1) 3)).factorization 3 = 3 := by
  rw [CFSG.LieType.Steinberg.card_SU_three hF, mul_assoc, show (3 ^ 1) ^ 3 = 3 ^ 3 by norm_num]
  exact Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)

theorem false_of_SU_three_three {F : Type} [Field F] [Finite F] [CharP F 3]
    (hF : Nat.card F = (3 ^ 1) ^ 2) (h : Ctx434Core G A M Q)
    (θ : layer G ⧸ Subgroup.center (layer G) ≃* SU (unitaryInvolution F 3 1) 3)
    (hout : ¬ 3 ∣ Nat.card (Outer (SU (unitaryInvolution F 3 1) 3))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  set π : layer G →* CFSG.Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) F :=
    (equivStatedSU hF 3).toMonoidHom.comp
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (layer G)))) with hπdef
  have hπ : Function.Surjective π :=
    (equivStatedSU hF 3).surjective.comp (θ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : π.ker = Subgroup.center (layer G) := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rw [← hker]
    exact CFSG.SectionRank.OddCover.prime_classical_three_perfect_odd_extension_trivial
      (K := F) Nat.prime_three (by norm_num) (ε := -1)
      (Or.inr ⟨rfl, by rw [hF]; norm_num, by rw [pow_one]⟩) π hπ hker.le hodd
  set Astar := A.map (Item434Alt.quotConj θ) with hAstar
  have hinj := Item434Kit.conj_injective_of_center_eq_bot
    (center_eq_bot_of_quasisimple_quotient h.isQuasisimple θ)
  set P : Subgroup (SU (unitaryInvolution F 3 1) 3) :=
    Astar.comap (MulAut.conj : SU (unitaryInvolution F 3 1) 3 →*
      MulAut (SU (unitaryInvolution F 3 1) 3)) with hP
  have hAmap : P.map MulAut.conj = Astar := Item434Kit.map_comap_conj_eq h θ hout
  have hPcard : Nat.card P = Nat.card Astar := by
    rw [← hAmap, Subgroup.card_map_of_injective hinj]
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    Item434Kit.isElemAbelian_of_map_injective hinj
      (by rw [hAmap]; exact Item434Kit.isElemAbelian_map_quotConj h θ)
  have hA9 : 9 ≤ Nat.card Astar := by
    have h27 := Item434Alt.card_eq_card_inf_ker_mul_card_map (Item434Alt.quotConj θ) A
    rw [Item434Kit.ker_quotConj h.isQuasisimple θ, h.isE27.2, ← hAstar] at h27
    have hC3 := h.card_inf_centralizer_layer_le
    by_contra hlt
    push Not at hlt
    have : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) *
        Nat.card Astar ≤ 3 * 8 := Nat.mul_le_mul hC3 (by omega)
    omega
  have : Finite (SU (unitaryInvolution F 3 1) 3) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := heisU (unitaryInvolution_involutive hF))
    (by rw [card_heisU hF, factorization_card_SU_three_nine hF]; norm_num)
    (Sec5.isPGroup_of_isElemAbelian hPe)
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'le : P' ≤ heisU (unitaryInvolution_involutive hF) := Item434AltPerm.map_conj_inv_le hg
  have hP'c : ∀ x ∈ P', ∀ y ∈ P', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hPe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨a₀, ha₀, hle⟩ := exists_le_lineU hP'le hP'c
  have hR9 : Nat.card (lineU (unitaryInvolution_involutive hF) a₀) ≤ 9 := by
    have := card_lineU_le hF ha₀
    norm_num at this
    exact this
  have hP'card : Nat.card P' = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hP'eq : P' = lineU (unitaryInvolution_involutive hF) a₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hP'card, hPcard]
    omega
  have hψ : Astar = ((lineU (unitaryInvolution_involutive hF) a₀).map MulAut.conj).map
      (MulAut.conj (MulAut.conj g)).toMonoidHom := by
    rw [← hP'eq, hP', ← map_conj_map_conj, Item434AltPerm.map_conj_map_conj_inv, hAmap]
  exact Item434Kit.false_of_normalizer_conj h θ
    (fun Y hY3 hRY => eq_bot_of_le_normalizer_unitary_three hF hinj ha₀ hY3 hRY)
    (MulAut.conj g) hψ

theorem false_of_projSU_three_three (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 3 3 1) : False := by
  refine false_of_SU_three_three (card_galois_two_mul one_ne_zero) h
    (e₀.trans (suEquivProjSU one_ne_zero).symm) fun h3 => ?_
  have h8 := h3.trans (card_outer_SU_three_dvd (e := 1) le_rfl)
  norm_num at h8

end Item434CharThree

open Item434CharThree

section Families


theorem item434CharThreeU3Three : Item434CharThreeU3Three := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (false_of_projSU_three_three hc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
