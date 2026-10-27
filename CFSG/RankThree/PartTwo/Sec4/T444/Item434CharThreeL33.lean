module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL33Tools
import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Matrix
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

namespace Item434CharThree

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem map_conj_map_conj {X : Type*} [Group X] (P : Subgroup X) (g : X) :
    (P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj : X →* MulAut X) =
      (P.map (MulAut.conj : X →* MulAut X)).map (MulAut.conj (MulAut.conj g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x y
  simp [MulAut.conj_apply, mul_assoc]

theorem false_of_projSL_three_three (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSL 3 (GaloisField 3 1)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ : layer G ⧸ Subgroup.center (layer G) ≃* SL(3, GaloisField 3 1) :=
    e₀.trans (slEquivProjSL (GaloisField 3 1)).symm with hθ
  have hK3 : Nat.card (GaloisField 3 1) = 3 := by rw [GaloisField.card 3 1 one_ne_zero, pow_one]
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  set π : layer G →* CFSG.Assembly.LowTwoRank.StatedSL 3 (GaloisField 3 1) :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (GaloisField 3 1)).toMonoidHom.comp
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (layer G)))) with hπdef
  have hπ : Function.Surjective π :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (GaloisField 3 1)).surjective.comp
      (θ.surjective.comp (QuotientGroup.mk'_surjective _))
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
      (K := GaloisField 3 1) Nat.prime_three (by norm_num) (ε := 1)
      (Or.inl ⟨rfl, hK3, rfl⟩) π hπ hker.le hodd
  have hout : ¬ 3 ∣ Nat.card (Outer SL(3, GaloisField 3 1)) := by
    intro h3
    have := Nat.le_of_dvd (by norm_num) (h3.trans (card_outer_SL_three_dvd (e := 1) le_rfl))
    omega
  set Astar := A.map (Item434Alt.quotConj θ) with hAstar
  have hinj := Item434Kit.conj_injective_of_center_eq_bot
    (center_SL_three_eq_bot (GaloisField 3 1))
  set P : Subgroup SL(3, GaloisField 3 1) :=
    Astar.comap (MulAut.conj : SL(3, GaloisField 3 1) →* MulAut SL(3, GaloisField 3 1)) with hP
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
  have : Finite SL(3, GaloisField 3 1) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := heis (GaloisField 3 1))
    (by rw [card_heis, hK3, factorization_card_SL_three one_ne_zero, mul_one])
    (Sec5.isPGroup_of_isElemAbelian hPe)
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'le : P' ≤ heis (GaloisField 3 1) := Item434AltPerm.map_conj_inv_le hg
  have hP'c : ∀ x ∈ P', ∀ y ∈ P', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hPe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨a₀, b₀, hab, hle⟩ := exists_le_lineSub hP'le hP'c
  have hR9 : Nat.card (lineSub a₀ b₀) = 9 := by rw [card_lineSub hab, hK3]; norm_num
  have hP'card : Nat.card P' = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hP'eq : P' = lineSub a₀ b₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hR9, hP'card, hPcard]
    exact hA9
  have hψ : Astar = ((lineSub a₀ b₀).map MulAut.conj).map
      (MulAut.conj (MulAut.conj g)).toMonoidHom := by
    rw [← hP'eq, hP', ← map_conj_map_conj, Item434AltPerm.map_conj_map_conj_inv, hAmap]
  exact Item434Kit.false_of_normalizer_conj h θ
    (fun Y hY3 hRY => eq_bot_of_le_normalizer_three hab hY3 hRY) (MulAut.conj g) hψ

end Item434CharThree

open Item434CharThree

section Families


theorem item434CharThreeL3Three : Item434CharThreeL3Three := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (false_of_projSL_three_three hc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
