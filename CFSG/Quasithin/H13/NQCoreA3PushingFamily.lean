module

public import CFSG.Quasithin.H13.NQCoreA3TransitiveCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannA3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumann
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isElemAbelian_iSup_of_commute {ι : Sort*} {U : ι → Subgroup G}
    (hU : ∀ i, ∀ u ∈ U i, u ^ 2 = 1) (hc : ∀ i j, U i ≤ centralizer (U j : Set G)) :
    IsElemAbelian 2 (⨆ i, U i) := by
  have hcent : (⨆ i, U i) ≤ centralizer ((⨆ i, U i : Subgroup G) : Set G) :=
    iSup_le fun i => le_centralizer_iff.mp (iSup_le fun j => hc j i)
  refine ⟨le_centralizer_iff_isMulCommutative.mp hcent, fun x hx => ?_⟩
  refine Subgroup.iSup_induction' U (C := fun x _ => x ^ 2 = 1) (fun i x hx => hU i x hx)
    (one_pow 2) ?_ hx
  intro y z hy hz hy2 hz2
  have hyz : Commute y z := (mem_centralizer_iff.mp (hcent hy) z hz).symm
  rw [hyz.mul_pow, hy2, hz2, one_mul]

variable [Finite G]

theorem two_local_rank_actual_A3_pushing_family_common_normal_subgroup
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G)
    (he2 : CFSG.Assembly.evenRank G ≤ 2) (T : Sylow 2 G) {M R : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hRT : R ≤ T) (hRM : M ≤ normalizer (R : Set G)) {r : ℕ}
    (hr : 0 < r) (Kf : Fin r → Subgroup G) (hK : ∀ i, IsShort2 (Kf i))
    (h3 : ∀ i, Nat.card (Kf i ⧸ CFSG.pCore 2 (Kf i)) = 3)
    (hcomm : ∀ i j, i ≠ j → ⁅Kf i, Kf j⁆ = ⊥)
    (hperm : ∀ t ∈ (T : Subgroup G), ∀ i, ∃ j, CFSG.conjugate (Kf i) t = Kf j)
    (htrans : ∀ i j, ∃ t ∈ (T : Subgroup G), CFSG.conjugate (Kf i) t = Kf j)
    (hRsyl : IsSylowTwoOf R ((⨆ i, Kf i) ⊔ R))
    (hJ : ∀ i, ⁅Kf i, Setup.Campbell.elemThompsonIn 2 R⁆ = Kf i) :
    r ≤ 2 ∧ conjJoin M (blockQ (Kf ⟨0, hr⟩)) ≠ ⊥ ∧
      IsElemAbelian 2 (conjJoin M (blockQ (Kf ⟨0, hr⟩))) ∧
      conjJoin M (blockQ (Kf ⟨0, hr⟩)) ≤ Setup.Campbell.elemBaumannIn 2 R ∧
      Setup.Campbell.elemBaumannIn 2 R ≤ R ∧
      M ⊔ ((⨆ i, Kf i) ⊔ (T : Subgroup G)) ≤
        normalizer (conjJoin M (blockQ (Kf ⟨0, hr⟩)) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hdata := fun i => SteinbergBS.ReversalPair.a3_data (hK i) (h3 i)
  have halt := fun i => Setup.Campbell.short_order_three_is_alternating_four (hK i) (h3 i)
  set U := ⨆ i, blockQ (Kf i) with hUdef
  have hcent : ∀ i j, i ≠ j → Kf i ≤ centralizer (Kf j : Set G) := fun i j hij =>
    commutator_eq_bot_iff_le_centralizer.mp (hcomm i j hij)
  have hUe : IsElemAbelian 2 U := by
    refine isElemAbelian_iSup_of_commute (fun i u hu => by rw [sq]; exact (hdata i).2.2.2.1 u hu)
      fun i j => ?_
    by_cases hij : i = j
    · subst hij
      exact (hdata i).2.2.2.2.1
    · exact ((hdata i).2.1.trans (hcent i j hij)).trans
        (centralizer_le (SetLike.coe_subset_coe.mpr (hdata j).2.1))
  have hKU : ∀ k, Kf k ≤ normalizer (U : Set G) := by
    intro k
    refine LieType.Steinberg.le_normalizer_iSup fun i => ?_
    by_cases hik : i = k
    · subst hik
      exact (hdata i).2.2.2.2.2.2.2.1
    · exact (hcent k i (Ne.symm hik)).trans ((centralizer_le
        (SetLike.coe_subset_coe.mpr (hdata i).2.1)).trans (centralizer_le_normalizer _))
  have hRU : R ≤ normalizer (U : Set G) := by
    refine LieType.Steinberg.le_normalizer_of_map_conj_le fun t ht => ?_
    rw [hUdef, Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    obtain ⟨j, hj⟩ := hperm t⁻¹ (inv_mem (hRT ht)) i
    have h1 : (blockQ (Kf i)).map (MulAut.conj t).toMonoidHom = blockQ (Kf j) := by
      rw [← hj, show CFSG.conjugate (Kf i) t⁻¹ = (Kf i).map (MulAut.conj t).toMonoidHom by
        rw [CFSG.conjugate, inv_inv]]
      exact (pCoreOf_map_equiv 2 (MulAut.conj t) (Kf i)).symm
    rw [h1]
    exact le_iSup (fun i => blockQ (Kf i)) j
  have hUKR : U ≤ (⨆ i, Kf i) ⊔ R := (iSup_mono fun i => (hdata i).2.1).trans le_sup_left
  have hU2 : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hUe.2 x x.2)⟩
  have hUR : U ≤ R := (le_pCoreOf_of_normalizes hUKR (sup_le (iSup_le hKU) hRU) hU2).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRsyl)
  have hJeq : Setup.Campbell.elemThompsonIn 2 R = thompsonJ R :=
    elemThompson_map_subtype_eq_thompsonJ R
  have hSeq : Setup.Campbell.elemBaumannIn 2 R = baum R := elemBaumann_map_subtype_eq_baum R
  have hth : ∀ i, ⁅Kf i, thompsonJ R⁆ = Kf i := fun i => by
    rw [← hJeq]
    exact hJ i
  have hUiR : ∀ i, blockU (Kf i) ≤ R := fun i => by
    rw [← (halt i).1]
    exact (le_iSup (fun i => blockQ (Kf i)) i).trans hUR
  have hUS : ∀ i, blockQ (Kf i) ≤ Setup.Campbell.elemBaumannIn 2 R := fun i => by
    rw [hSeq, (halt i).1]
    exact (C56.a3_blockU_le_baum hR2 (hK i) (halt i).2.2.2.2 (hUiR i) (hth i)).1
  have hSK : ∀ i, Setup.Campbell.elemBaumannIn 2 R ≤ normalizer (Kf i : Set G) := fun i => by
    rw [hSeq]
    refine C56.a3_baum_le_normalizer hR2 (hK i) (halt i).2.2.2.2 (hUiR i) (hth i) fun s hs => ?_
    obtain ⟨j, hj⟩ := hperm s (hRT (mem_inf.mp hs).1) i
    by_cases hij : j = i
    · left
      subst hij
      exact hj
    · right
      intro a ha b hb
      have hb' : b ∈ Kf j := by
        rw [← hj]
        exact hb
      exact (mem_centralizer_iff.mp (hcent i j (Ne.symm hij) ha) b hb').symm
  have hSR : Setup.Campbell.elemBaumannIn 2 R ≤ R := Setup.Campbell.elemBaumannIn_le 2 R
  have hSM : M ≤ normalizer (Setup.Campbell.elemBaumannIn 2 R : Set G) := by
    refine hRM.trans (normalizer_le_normalizer_of_characteristic hSR ?_)
    rw [hSeq]
    exact C1GN.characteristic_baum R
  obtain ⟨hr2, -, hR1, hRe, hRS, hN⟩ := two_local_rank_transitive_A3_family_common_normal_core
    hev he2 T hTM hSM (hSR.trans hRT) hr Kf hK h3 hcomm hSK hUS hperm htrans
  refine ⟨hr2, hR1, hRe, hRS, hSR, le_trans ?_ hN⟩
  exact sup_le le_sup_left (sup_le (le_sup_right.trans le_sup_right)
    (le_sup_left.trans le_sup_right))

end CFSG.Quasithin.H13.NQCore
