module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143RowCrit
import CFSG.Sporadic.Recognition.McLASThreeLocalCert
public import CFSG.Sporadic.Schreier.PairMcLCertBase
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open CFSG.Sporadic.Schreier (mclP)

private theorem conj_mem_closure_inter {G : Type*} [Group G] {T : Subgroup G} {x g : G}
    (hg : g ∈ T) {a : G} (ha : a ∈ Subgroup.closure ((T : Set G) ∩ {y | IsConj x y})) :
    g * a * g⁻¹ ∈ Subgroup.closure ((T : Set G) ∩ {y | IsConj x y}) := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    refine Subgroup.subset_closure ⟨T.mul_mem (T.mul_mem hg ha.1) (T.inv_mem hg), ?_⟩
    exact ha.2.trans (isConj_iff.mpr ⟨g, rfl⟩)
  | one => simp
  | mul a b _ _ iha ihb =>
    have h : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
    rw [h]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
    have h : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [h]
    exact Subgroup.inv_mem _ iha

private theorem factorization_three_card_mclP :
    (Nat.card mclP).factorization 3 = 6 := by
  rw [CFSG.Sporadic.Schreier.card_mclP, show (898128000 : ℕ) = 3 ^ 6 * 1232000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem l143Rows_mclP :
    L143Rows mclP := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, R, T, A, -, -, -, -, hL⟩ :=
    CFSG.Sporadic.Recognition.McLAS.threeLocal_of_embedding mclP.subtype mclP.subtype_injective
      (Subgroup.range_subtype mclP) CFSG.Sporadic.Recognition.McLAS.threeFacts_cert'
      CFSG.Sporadic.Recognition.McLAS.threeLocalCheck_eq_true
  have hT : Nat.card T = 3 ^ (Nat.card mclP).factorization 3 :=
    calc Nat.card T = 729 := hL.card_T
      _ = 3 ^ 6 := by norm_num
      _ = 3 ^ (Nat.card mclP).factorization 3 := by rw [factorization_three_card_mclP]
  let P : Sylow 3 mclP := Sylow.ofCard T hT
  have hP : (P : Subgroup mclP) = T := Sylow.coe_ofCard _ _
  haveI := hL.A_elementaryAbelian
  refine L143Rows.of_normal P A ?_ ?_ ?_ (by rw [hL.card_A])
  · intro g hg a ha
    rw [hP] at hg
    rw [hL.A_eq] at ha ⊢
    exact conj_mem_closure_inter hg ha
  · intro a ha b hb
    exact congrArg Subtype.val (this.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · exact fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha

private theorem l143Rows_of_mulEquiv_McL
    {Q : Type} [Group Q] (e : Q ≃* CFSG.Blueprint.NativeSporadic.McL) : L143Rows Q :=
  L143Rows.of_mulEquiv (e.trans CFSG.Sporadic.Schreier.mclPermEquiv) l143Rows_mclP

theorem l143RowsT_McL :
    ∀ (T : Type) [Group T], Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.McL) → L143Rows T := by
  intro T _ h
  obtain ⟨e⟩ := h
  exact l143Rows_of_mulEquiv_McL e

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
