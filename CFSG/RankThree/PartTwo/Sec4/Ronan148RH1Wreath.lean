module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1E27
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM24

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG.RankThree.PartTwo.Sec4.Ronan148L (E27Move)
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecElt baseA wreathW)

section Wreath

variable {X : Type} [Group X] {T : Fin 3 → X} {tw : X}

theorem vecElt_zero : vecElt T 0 = 1 := by
  simp [vecElt]

theorem mem_normalizer_baseA [Finite X] {n : X} (h : ∀ i, n * T i * n⁻¹ ∈ baseA T) :
    n ∈ Subgroup.normalizer (baseA T : Set X) := by
  refine Ronan148S.mem_normalizer_of_map_le ?_
  rw [baseA, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers]
  refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;> exact h _

variable [Finite X]

theorem e27Move_of_wreath (hf : WreathFacts T tw) (hW : Nat.card (wreathW T tw) = 81)
    (h3 : (Nat.card X).factorization 3 = 4)
    (hmv : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ n ∈ Subgroup.normalizer (baseA T : Set X),
      n ∉ Subgroup.normalizer ((Subgroup.zpowers (vecElt T v) : Subgroup X) : Set X)) :
    E27Move X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine e27Move_of_rep (E₀ := baseA T) (fun A hA hA27 => ?_) (fun s hs hs1 => ?_)
  · obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW T tw)
      (by rw [hW, h3]; norm_num) (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hA)
    have hle := Item434AltPerm.map_conj_inv_le hg
    have hcard : Nat.card (A.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective, hA27]
    have hEq := Item434Kit.eq_baseA_of_le_wreathW hf hW hle
      (Ronan148S.isElemAbelian_map _ hA) hcard
    refine ⟨MulAut.conj g, ?_⟩
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id X := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [← hEq, Subgroup.map_map, hcomp, Subgroup.map_id]
  · obtain ⟨v, rfl⟩ := (Item434Kit.mem_baseA_iff hf).mp hs
    have hv : v ≠ 0 := by
      rintro rfl
      exact hs1 vecElt_zero
    exact hmv v hv

theorem rankThreeData_of_wreath (hf : WreathFacts T tw) (hcube : CubeInner X) {t : X}
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (h0 : t * T 0 = T 0 * t) (h1 : t * T 1 = T 1 * t) :
    RankThreeData X := by
  refine ⟨hcube, Subgroup.zpowers (T 0) ⊔ Subgroup.zpowers (T 1), baseA T,
    Item434Kit.sup_zpowers_le_baseA 0 1,
    (Item434Kit.isElemAbelian_sup_zpowers hf (by decide : (0 : Fin 3) ≠ 1)).1,
    (Item434Kit.isElemAbelian_sup_zpowers hf (by decide : (0 : Fin 3) ≠ 1)).2,
    Item434Kit.isElemAbelian_baseA hf, Item434Kit.card_baseA hf, t, ht1, ht2, fun f hf' => ?_⟩
  have hle : Subgroup.zpowers (T 0) ⊔ Subgroup.zpowers (T 1) ≤
      Subgroup.centralizer ({t} : Set X) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h0.symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h1.symm))
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hf')).symm

end Wreath

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
