module

public import CFSG.Quasithin.Background.E3Prop

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Uniq

variable {G : Type u} [Group G] [Finite G] {V S H M : Subgroup G}

theorem e3_21_comm (hV : IsElemAbelian 2 V) (hVN : S ≤ Subgroup.normalizer (V : Set G)) {i : ℕ}
    (hia : i + aParam (autI hV ⊤) < sParam hV) : ⁅V, wClos V i S⁆ = ⊥ := by
  refine e3_18_comm hV (H := S) le_rfl hVN hV ?_
  have := aParam_mono (autI_mono hV (le_top : S ≤ ⊤))
  omega

theorem e3_21_le (hV : IsElemAbelian 2 V) (hVN : S ≤ Subgroup.normalizer (V : Set G)) {i : ℕ}
    (hia : i + aParam (autI hV ⊤) < sParam hV) :
    wClos V i S ≤ S ⊓ Subgroup.centralizer (V : Set G) := by
  refine le_inf (wClos_le i S) ?_
  have h := e3_21_comm hV hVN hia
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h

theorem e3_21_le_sub (hV : IsElemAbelian 2 V) (hVN : S ≤ Subgroup.normalizer (V : Set G))
    (has : aParam (autI hV ⊤) < sParam hV) :
    wClos V (sParam hV - aParam (autI hV ⊤) - 1) S ≤ S ⊓ Subgroup.centralizer (V : Set G) :=
  e3_21_le hV hVN (by omega)

theorem e3_21_normalizer (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) (hVS : V ≤ S)
    (hVN : S ≤ Subgroup.normalizer (V : Set G)) {i : ℕ}
    (hia : i + aParam (autI hV ⊤) < sParam hV)
    (hM : IsUniqueM
      (Subgroup.normalizer ((S ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M) :
    Subgroup.normalizer (wClos V i S : Set G) ≤ M ∧
      Subgroup.centralizer (cClos V i S : Set G) ≤ M := by
  have hQH : S ⊓ Subgroup.centralizer (V : Set G) ≤ H := inf_le_left.trans hS.le
  have hQ2 : IsPGroup 2 ↥(S ⊓ Subgroup.centralizer (V : Set G)) := hS.isPGroup.to_le inf_le_left
  have hW := e3_21_le hV hVN hia
  have hi : i < rk ↥V := lt_of_lt_of_le (by omega) (sParam_le_rk hV)
  have hW1 : wClos V i S ≠ ⊥ := wClos_ne_bot hV hVS hi
  exact ⟨(e3_16_one hS hQH hQ2 hW hW1 hM).2, e3_16_three hS hQH hQ2 hW hW1 hM⟩

theorem e3_21_one (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) (hVS : V ≤ S)
    (hVN : S ≤ Subgroup.normalizer (V : Set G)) {i : ℕ}
    (hia : i + aParam (autI hV ⊤) < sParam hV)
    (hM : IsUniqueM
      (Subgroup.normalizer ((S ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M) :
    ⁅V, wClos V i S⁆ = ⊥ ∧
      wClos V (sParam hV - aParam (autI hV ⊤) - 1) S ≤ S ⊓ Subgroup.centralizer (V : Set G) ∧
      Subgroup.normalizer (wClos V i S : Set G) ≤ M ∧
      Subgroup.centralizer (cClos V i S : Set G) ≤ M :=
  ⟨e3_21_comm hV hVN hia, e3_21_le_sub hV hVN (by omega), (e3_21_normalizer hV hS hVS hVN hia hM).1,
    (e3_21_normalizer hV hS hVS hVN hia hM).2⟩

theorem e3_21_two (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) (hVS : V ≤ S)
    (hVN : S ≤ Subgroup.normalizer (V : Set G)) {i : ℕ}
    (hia : i + aParam (autI hV ⊤) < sParam hV)
    (hM : IsUniqueM
      (Subgroup.normalizer ((S ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M)
    (hj : E1.nParam H = i) : H ≤ M := by
  have h19 := e3_19 hV hS (i := 0) (j := i) hj (by omega)
  have hia0 : 0 + aParam (autI hV ⊤) < sParam hV := by omega
  have hN0 := (e3_21_normalizer hV hS hVS hVN hia0 hM).1
  have hCi := (e3_21_normalizer hV hS hVS hVN hia hM).2
  rw [← h19]
  refine sup_le ?_ ?_
  · rw [zero_add]
    exact inf_le_right.trans hCi
  · exact inf_le_right.trans hN0

theorem e3_21_three (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) (hVS : V ≤ S)
    (hVN : S ≤ Subgroup.normalizer (V : Set G)) {i : ℕ} (hi1 : 1 ≤ i)
    (hia : i + aParam (autI hV ⊤) < sParam hV)
    (hM : IsUniqueM
      (Subgroup.normalizer ((S ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M)
    (hsol : Group.IsSolvable ↥H) : H ≤ M := by
  have hn : E1.nParam H ≤ 1 := E1.solvable_nParam_le_one hsol
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (by simp : (1 : ℕ∞) ≠ ⊤) hn)
  have hj1 : j ≤ 1 := by
    rw [← hj] at hn
    exact_mod_cast hn
  exact e3_21_two hV hS hVS hVN (i := j) (by omega) hM hj.symm

end Uniq

end E3

end CFSG.Quasithin
