module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerStructure
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Eng
import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.Sporadic.Schreier.PairJ3CertBase

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem rows_of_mulEquiv_J3
    {Q : Type} [Group Q] (e : Q ≃* Blueprint.NativeSporadic.J3) {x : Q} (hx : orderOf x = 3) :
    (¬ 5 ∣ Nat.card (Subgroup.centralizer {x}) ∧ ¬ 7 ∣ Nat.card (Subgroup.centralizer {x})) ∨
      ∃ I : Subgroup Q, I ≤ Subgroup.centralizer {x} ∧ ⁅I, I⁆ = I ∧
        ∃ u ∈ I, orderOf u = 3 ∧ u ∉ Subgroup.zpowers x := by
  have ha3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have ha1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  rcases CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_centralizer_of_equiv_J3_dichotomy
    e ha3 ha1 with h | h
  · right
    let ψ : Q ≃* ↥CFSG.Sporadic.Schreier.j3P :=
      e.trans CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.j3CarrierEquiv
    have hy3 : orderOf ((ψ x : CFSG.Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156)) = 3 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hx
    have hcard := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ψ x
    have h5 : 5 ∣ Nat.card (Subgroup.centralizer
        ({((ψ x : CFSG.Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156))} :
          Set (Equiv.Perm (Fin 6156))) ⊓ CFSG.Sporadic.Schreier.j3P :
        Subgroup (Equiv.Perm (Fin 6156))) := by
      rw [← hcard, h]
      norm_num
    obtain ⟨Dy, hDyC, -, -, ⟨eD⟩⟩ :=
      CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.exists_A6_in_centralizer_j3P (ψ x).2 hy3 h5
    let I : Subgroup Q := (Dy.subgroupOf CFSG.Sporadic.Schreier.j3P).map ψ.symm.toMonoidHom
    let eI : ↥I ≃* alternatingGroup (Fin 6) :=
      ((MulEquiv.subgroupMap ψ.symm (Dy.subgroupOf CFSG.Sporadic.Schreier.j3P)).symm.trans
        (Subgroup.subgroupOfEquivOfLe (hDyC.trans inf_le_right))).trans eD
    have hIC : I ≤ Subgroup.centralizer {x} := by
      rintro _ ⟨d, hd, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm := Subgroup.mem_centralizer_singleton_iff.1
        (Subgroup.mem_inf.1 (hDyC (Subgroup.mem_subgroupOf.1 hd))).1
      change ψ.symm d * x = x * ψ.symm d
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hcomm
    haveI : Finite I := Finite.of_equiv _ eI.symm.toEquiv
    have hI360 : Nat.card I = 360 := by
      rw [Nat.card_congr eI.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := I) 3 (by rw [hI360]; norm_num)
    refine ⟨I, hIC, CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.perfect_of_equiv_alt6 I eI, u,
      u.2, ?_, fun hmem => ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact hu
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      have hcen : u ∈ Subgroup.center ↥I := by
        rw [Subgroup.mem_center_iff]
        intro w
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk]
        exact ((show Commute (w : Q) x from
          Subgroup.mem_centralizer_singleton_iff.1 (hIC w.2)).zpow_right k).eq
      rw [CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.center_eq_bot_of_equiv_alt6 I eI,
        Subgroup.mem_bot] at hcen
      rw [hcen, orderOf_one] at hu
      omega
  · left
    rw [h]
    omega

theorem res3L125_rows_J3
    (x : Blueprint.NativeSporadic.J3) (hx : orderOf x = 3) :
    (¬ 5 ∣ Nat.card (Subgroup.centralizer {x}) ∧ ¬ 7 ∣ Nat.card (Subgroup.centralizer {x})) ∨
      ∃ I : Subgroup Blueprint.NativeSporadic.J3, I ≤ Subgroup.centralizer {x} ∧ ⁅I, I⁆ = I ∧
        ∃ u ∈ I, orderOf u = 3 ∧ u ∉ Subgroup.zpowers x :=
  @rows_of_mulEquiv_J3 Blueprint.NativeSporadic.J3 Units.instGroup
    (@MulEquiv.refl Blueprint.NativeSporadic.J3 _) x hx

theorem res3L125_isPGroup_two_outer_J3 :
    IsPGroup 2 (Outer Blueprint.NativeSporadic.J3) := by
  haveI : Finite (MulAut Blueprint.NativeSporadic.J3) := MulEquiv.finite_left
  exact res3L125_isPGroup_two_outer_of_card_le_two CFSG.RankThree.PartTwo.Sec4.card_outer_J3

theorem res3NoDatumJ3_holds :
    Res3NoDatumJ3 := by
  rintro J _ _ _ hq ⟨e⟩ c g V U hd
  exact @res3L125_false_of_rows J _ _ hq Blueprint.NativeSporadic.J3 Units.instGroup
    (Finite.of_equiv _ e.toEquiv) e res3L125_isPGroup_two_outer_J3
    (fun x hx => Or.imp_right Or.inr (res3L125_rows_J3 x hx)) c g V U hd

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
