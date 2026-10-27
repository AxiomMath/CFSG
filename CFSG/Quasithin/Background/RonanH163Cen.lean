module

public import CFSG.Quasithin.Background.RonanH163Base
public import CFSG.Quasithin.Background.B5FinPerm
public import CFSG.Quasithin.Background.RonanH143NF
public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem R_kappa (σ : ↥mog22plus) {m : G6.PermMod 24} (hm : m ∈ golayC ⊓ pairKer 0 1) :
    R σ (code22Coords.κ m) = code22Coords.κ (G6.permAct 24 (σ : P24) m) :=
  (code22Coords.κ_permAct_rho mog22plus (fun _ hσ => preserves_code22 hσ) σ hm).symm

theorem eSetR_smul (g : P24) (Y : Finset (Fin 24)) :
    G6.permAct 24 g (eSetR Y) = eSetR (g • Y) := by
  rw [permAct_eSet, smul_finset_eq_map]

theorem eSetR_mem_numer {Y : Finset (Fin 24)} (hY : IsOctR Y)
    (h01 : (0 : Fin 24) ∈ Y ↔ (1 : Fin 24) ∈ Y) : eSetR Y ∈ golayC ⊓ pairKer 0 1 := by
  refine ⟨hY.2, (mem_pairKer 0 1 _).2 ?_⟩
  rw [toAdd_eSet, toAdd_eSet]
  by_cases h0 : (0 : Fin 24) ∈ Y
  · have h1 : (1 : Fin 24) ∈ Y := h01.1 h0
    simp only [h0, h1, if_true]
    decide
  · have h1 : (1 : Fin 24) ∉ Y := fun h => h0 (h01.2 h)
    simp only [h0, h1, if_false]
    decide

theorem smul_eq_of_R_fix {Y : Finset (Fin 24)} (hY : IsOctR Y)
    (h01 : (0 : Fin 24) ∈ Y ↔ (1 : Fin 24) ∈ Y) (g : ↥mog22plus)
    (h : R g (code22Coords.κ (eSetR Y)) = code22Coords.κ (eSetR Y)) : (g : P24) • Y = Y := by
  have hnum : eSetR Y ∈ golayC ⊓ pairKer 0 1 := eSetR_mem_numer hY h01
  rw [R_kappa g hnum, eSetR_smul] at h
  have hnum' : eSetR ((g : P24) • Y) ∈ golayC ⊓ pairKer 0 1 := by
    have := (preserves_code22 g.2).1 _ hnum
    rwa [eSetR_smul] at this
  have hker : eSetR ((g : P24) • Y) * (eSetR Y)⁻¹ ∈ Subgroup.zpowers (G6.allOnes 24) := by
    refine (code22Coords.ker_iff _ ((golayC ⊓ pairKer 0 1).mul_mem hnum'
      ((golayC ⊓ pairKer 0 1).inv_mem hnum))).1 ?_
    rw [map_mul, map_inv, h]
    exact mul_inv_cancel _
  rcases B5FinPerm.mem_zpowers_allOnes_iff.1 hker with h1 | h1
  · have he : eSetR ((g : P24) • Y) = eSetR Y := mul_inv_eq_one.1 h1
    ext i
    have := congrFun (congrArg Multiplicative.toAdd he) i
    rw [toAdd_eSet, toAdd_eSet] at this
    by_cases hi : i ∈ (g : P24) • Y <;> by_cases hi' : i ∈ Y <;> simp_all
  · exfalso
    have he : eSetR ((g : P24) • Y) = G6.allOnes 24 * eSetR Y := mul_inv_eq_iff_eq_mul.1 h1
    have hcomp : (g : P24) • Y = Finset.univ \ Y := by
      ext i
      have := congrFun (congrArg Multiplicative.toAdd he) i
      simp only [toAdd_mul, Pi.add_apply, toAdd_eSet, G6.allOnes, toAdd_ofAdd] at this
      by_cases hi : i ∈ (g : P24) • Y <;> by_cases hi' : i ∈ Y <;> simp_all <;> revert this <;> decide
    have h8 : ((g : P24) • Y).card = 8 := by rw [Finset.card_smul_finset]; exact hY.1
    rw [hcomp, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hY.1] at h8
    omega

theorem Zq_ne_Bstd : ∀ i : Fin 5, Zq i ≠ Bstd := by decide +kernel

theorem Zq_union_Bstd_zero_one : ∀ i : Fin 5,
    ((0 : Fin 24) ∈ Zq i ∪ Bstd ↔ (1 : Fin 24) ∈ Zq i ∪ Bstd) := by decide +kernel

theorem Zq_union_inter : ∀ i j : Fin 5, i ≠ j → (Zq i ∪ Bstd) ∩ (Zq j ∪ Bstd) = Bstd := by
  decide +kernel

theorem Zq_union_sdiff : ∀ i : Fin 5, (Zq i ∪ Bstd) \ Bstd = Zq i := by decide +kernel

theorem isOct_Zq_union (i : Fin 5) : IsOctR (Zq i ∪ Bstd) := by
  refine isSext_Sstd.2.2.2.2 (Zq i) ?_ Bstd ?_ (Zq_ne_Bstd i)
  · exact Finset.mem_insert_of_mem ((mem_Qstd_iff _).2 ⟨i, rfl⟩)
  · exact Finset.mem_insert_self _ _

theorem cen_std :
    cenM R (fixV (rImg R (KY mog22plus Qstd))) = (KY mog22plus Qstd).subgroupOf mog22plus ∧
      IsPGroup 2 ↥(KY mog22plus Qstd) := by
  rw [KY_Q_L2]
  refine ⟨?_, isPGroup_NQ2⟩
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hg' : ∀ u ∈ fixV (rImg R NQ2), R g u = u := hg
    have hoct : ∀ i : Fin 5, (g : P24) • (Zq i ∪ Bstd) = Zq i ∪ Bstd := by
      intro i
      refine smul_eq_of_R_fix (isOct_Zq_union i) (Zq_union_Bstd_zero_one i) g ?_
      apply hg'
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
      have hkNQ : (k : P24) ∈ NQ2 := Subgroup.mem_subgroupOf.1 hk
      have hQ : (k : P24) • Qstd = Qstd := smul_Qstd_of_perm 1 (fun j => by
        simpa using nq2_fix_Zq _ hkNQ j)
      have hfix : (k : P24) • (Zq i ∪ Bstd) = Zq i ∪ Bstd := by
        rw [Finset.smul_finset_union, nq2_fix_Zq _ hkNQ i, smul_Bstd_of_smul_Qstd hQ]
      refine (R_kappa k (eSetR_mem_numer (isOct_Zq_union i) (Zq_union_Bstd_zero_one i))).trans ?_
      rw [eSetR_smul, hfix]
    have hB : (g : P24) • Bstd = Bstd := by
      have h01 := Zq_union_inter 0 1 (by decide)
      rw [← h01, Finset.smul_finset_inter, hoct 0, hoct 1]
    have hZ : ∀ i : Fin 5, (g : P24) • Zq i = Zq i := by
      intro i
      rw [← Zq_union_sdiff i, Finset.smul_finset_sdiff, hoct i, hB]
    have hMQ : (g : P24) ∈ MY mog22plus Qstd :=
      mem_MY_Q_of_perm g.2 1 (fun i => by simpa using hZ i)
    have hker : (⟨(g : P24), hMQ⟩ : ↥(MY mog22plus Qstd)) ∈ (piQ mog22plus).ker := by
      rw [MonoidHom.mem_ker]
      exact piQ_eq_of_smul _ 1 (fun i => by simpa using hZ i)
    rw [ker_piQ_L2, Subgroup.mem_subgroupOf] at hker
    exact hker
  · intro hg
    show R g ∈ centSub _
    intro u hu
    exact hu (R g) (Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩)

end CFSG.Quasithin.RonanH163
