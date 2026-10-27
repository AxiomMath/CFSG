module

public import CFSG.Quasithin.Background.SimsE213L33Aut
public import CFSG.Quasithin.Background.SimsE2Defs
public import CFSG.Quasithin.Vol2.Ch3E213MOL5
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.Vol2.Ch3E213MOL4

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Ch3E213M
open scoped MatrixGroups

namespace E213L33

theorem not_isPGroup_of_isPerfect {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    [Nontrivial A] : ¬ IsPGroup 2 A := fun h2 =>
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Group.IsPerfect.not_isNilpotent A h2.isNilpotent

theorem isPerfect_star {Γ : Type} [Group Γ] {H M K : Subgroup Γ} (hKc : K ∈ cComp H) :
    Group.IsPerfect ↥(E2.star M H K) := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKc)
  exact Group.IsPerfect.ofSurjective
    (f := ((E2P.starMap M H).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
    (((E2P.starMap M H).subgroupMap_surjective _).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective)

end E213L33

theorem not_isL33Exception_of_charTwo
    {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (hc : CharTwo H) :
    ¬ IsL33Exception (⊤ : Subgroup (E2.StarQuot M H)) (E2.star M H V) := by
  rintro ⟨hL, hVL⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := E2P.finite_starQuot M H
  set L := oTwoUpper (⊤ : Subgroup (E2.StarQuot M H)) with hLdef
  haveI hLn : L.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_oTwoUpper ⊤))
  have hmpY := E2P.minParabolic_star h.minParabolic
  have hJY := E2P.kerIn_star M H
  obtain ⟨ι⟩ := OLB.exists_equiv_sl3 hL
  haveI : Group.IsPerfect SL(3, GaloisField 3 1) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  haveI hperfL : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := ι.toMonoidHom) ι.surjective
  have hsL : IsSimpleGroup ↥L := OL.isSimpleGroup_of_L3U3 Nat.prime_three le_rfl (Or.inr hL)
  haveI hntL : Nontrivial ↥L := hsL.toNontrivial
  have hnabL : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative ↥L ⟨⟨hcon⟩⟩
  have hsup : L ⊔ E2.star M H T = ⊤ := by
    by_contra hne
    have hle := hmpY.le_of_lt le_sup_right (lt_top_iff_ne_top.mpr hne)
    have hLJ : L ≤ kerIn (E2.star M H M) ⊤ :=
      le_kerIn_of_le_normalizer (le_sup_left.trans hle) (le_normalizer_oTwoUpper ⊤)
    rw [hJY] at hLJ
    exact (Subgroup.nontrivial_iff_ne_bot L).mp hntL (le_bot_iff.mp hLJ)
  have hCL := OS.centralizer_eq_bot hmpY hJY hLn (OL.center_eq_bot_of_simple hnabL) hsup
  have hMH : M ≤ H := h.minParabolic.maximal.1.le
  have hVT : E2.star M H V ≤ E2.star M H T :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H h.le_T)
  have hTV := OS.star_le_normalizer (M := M) (H := H) h.normal_T
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (h.elem.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hsq : ∀ x ∈ E2.star M H V, x * x = 1 :=
    OS.star_sq fun v hv => by rw [← pow_two]; exact h.elem.2 v hv
  have hVe : IsElemAbelian 2 (E2.star M H V) :=
    ⟨⟨⟨fun a b => Subtype.ext (OS.star_comm hVcomm _ a.2 _ b.2)⟩⟩,
      fun x hx => by rw [pow_two]; exact hsq x hx⟩
  have hVM := OS.star_le_pCoreOf hMH h.le_pCoreOf
  have hV4 : 4 ≤ Nat.card (E2.star M H V) :=
    E213L33.four_le_card hmpY hL hCL hVT hTV hVe hVM hVL
  have hns : ¬ Group.IsSolvable ↥H := by
    intro hsolv
    haveI : Group.IsSolvable (E2.StarQuot M H) :=
      Group.isSolvable_of_surjective (E2P.starMap_surjective M H)
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, hsqtk⟩ :=
    e22StatementNoN_proved Γ H T M h.minParabolic h.sqtk hns
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have h4le : 4 ≤ (V ⊓ pCoreOf 2 H).relIndex V := by
    have hcard : Nat.card (E2.star M H V) = (kerIn M H).relIndex V := by
      rw [E2P.star_def, ← Subgroup.relIndex_ker, E2P.ker_starMap,
        Subgroup.relIndex_subgroupOf h.le_H]
    have hle : V ⊓ pCoreOf 2 H ≤ kerIn M H := inf_le_right.trans h.minParabolic.pCoreOf_le_kerIn
    calc 4 ≤ Nat.card (E2.star M H V) := hV4
      _ = (kerIn M H).relIndex V := hcard
      _ ≤ (V ⊓ pCoreOf 2 H).relIndex V :=
        Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
  have hS : Setting H T M V K := ⟨h, hc, hns, h4le, hKc, hHK, hq, hsqtk⟩
  haveI hperfK : Group.IsPerfect ↥(E2.star M H K) := E213L33.isPerfect_star hKc
  have hKL : E2.star M H K ≤ L := B1Red.perfect_le_oTwoUpper' le_top hperfK
  have hsupK := OS.star_sup_eq_top (M := M) hHK
  have hnot2 : ¬ IsPGroup 2 ↥(E2.star M H K) := by
    intro h2
    by_cases hbot : E2.star M H K = ⊥
    · rw [hbot, bot_sup_eq] at hsupK
      exact E213L33.not_isPGroup_of_isPerfect
        (hmpY.isSylow.2.1.to_le (le_top.trans hsupK.ge) : IsPGroup 2 ↥L)
    · haveI : Nontrivial ↥(E2.star M H K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
      exact E213L33.not_isPGroup_of_isPerfect h2
  have hJU : kerIn M H ≤ pCoreOf 2 H := by
    dsimp only [E2.E22CasesNoN] at hcases
    rcases hcases with ⟨hJ, -⟩ | ⟨hTK, hker, -⟩
    · exact hJ.le
    · have hHK' : H ≤ Subgroup.normalizer (K : Set Γ) := by
        rw [hHK]
        exact sup_le Subgroup.le_normalizer hTK
      have hKn : (E2.star M H K).Normal := OS.normal_star (M := M) hKH hHK'
      have hKeq : E2.star M H K = L := by
        refine le_antisymm hKL ?_
        haveI := hsL
        haveI := hKn.subgroupOf L
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((E2.star M H K).subgroupOf L) with
          hb | ht
        · exfalso
          have hbot : E2.star M H K = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hKL
          exact hnot2 (hbot ▸ IsPGroup.of_bot)
        · exact Subgroup.subgroupOf_eq_top.mp ht
      have hL' : IsPSL 3 3 1 ↥(E2.star M H K) := by
        rw [hKeq]
        exact hL
      exact OL.kerIn_le_pCoreOf hS ⟨hTK, hker⟩ hL'
  obtain ⟨W, _, _, hcomm, hexp, ρ, ⟨k, hk, hk1⟩, hquad⟩ :=
    OL.exists_quadratic_module hS hJU hnot2
  exact E213L33.false_of_quadratic hmpY hL hCL hVT hVe hVM hV4 hcomm hexp ρ ⟨k, hKL hk, hk1⟩
    hquad

end CFSG.Quasithin.SimsE2
