module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3TwoD
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3OddPaired
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Borel
public import CFSG.Quasithin.Vol2.Ch3E213MOL3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M E217R1 CFSG.GH74.GLS.IVK CFSG.GH74.GLS E2P
open scoped commutatorElement

namespace E217R3

@[expose] def R3Pkg2c7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case2 H T M K →
    IsPSL 2 7 1 ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → False

theorem r3Pkg2c_of_seven (h12 : IVK_1_2_general) (h13a : IVK_1_3a) (h13b : IVK_1_3b)
    (hcoat : ∀ (F : Type) [Field F] [Finite F], L2Field F → 11 ≤ Nat.card F →
      ∀ (L : Type) [Group L] [Finite L], (L ≃* L2 F) → ∀ u : L, orderOf u = 2 →
        IsCoatom (Subgroup.centralizer ({u} : Set L)))
    (p7 : R3Pkg2c7) : R3Pkg2c := by
  intro G _ _ H T M V K hS hlt hC2 p e hp hp3 he hp8 hpsl hMK hAut
  have h7 := card_eq_seven_of_twoC h12 h13a h13b hcoat hS.toHyp2 hS.mem_cComp hS.eq_sup hC2 hp
    hp3 he hp8 hpsl hMK hAut
  rcases he with rfl | rfl
  · rw [pow_one] at h7
    subst h7
    exact p7 G H T M V K hS hlt hC2 hpsl hMK hAut
  · exfalso
    rw [sq] at h7
    nlinarith

@[expose] def R3Pkg2d3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case2 H T M K →
    IsPSL 3 3 1 ↥(E2.star M H K) → E2.InducesOuter (E2.star M H T) (E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) → False

theorem r3Pkg2d_of_three (hA : Ch3E213M.OL.KFactL3U3OuterInv) (hNot : KFactL3U3NotOddCube)
    (p3 : R3Pkg2d3) : R3Pkg2d := by
  intro G _ _ H T M V K hS hlt hC2 p hp hp2 hcase hMK
  have hK' : (p % 4 = 1 ∧ IsPSU 3 p 1 ↥(E2.star M H K)) ∨
      (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(E2.star M H K)) :=
    hcase.imp id (fun h => ⟨h.1, h.2.1⟩)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hsimp : IsSimpleGroup ↥(E2.star M H K) :=
    Ch3E213M.OL.isSimpleGroup_of_L3U3 hp hp3 (hK'.imp (fun h => h.2) (fun h => h.2))
  have hnab := nonab_star' (M := M) hS.mem_cComp
  have hmp := hS.toHyp2.hyp.minParabolic
  have hX := asHyp_star' hmp hS.mem_cComp hS.eq_sup hC2 hsimp
    (Ch3E213M.OL.center_eq_bot_of_simple hnab) hnab
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    star_inf_T hmp.isSylow hS.mem_cComp.2.2.1 hKH
  have hMK' : E2.star M H M ⊓ E2.star M H K = E2.star M H K ⊓
      Subgroup.centralizer (zOf (E2.star M H T ⊓ E2.star M H K) : Set (E2.StarQuot M H)) := by
    rw [← star_inf_M, hMK, ← hTK]
    rfl
  obtain ⟨v, hv2, hv1, hvT, hvM, hodd⟩ := exists_vbar hS.toHyp2
  have hp3' : p = 3 := eq_three_of_asHyp_L3U3 hA hNot hX hp hp2 hK' hMK' hv2 hv1 hvT hvM hodd
  subst hp3'
  rcases hcase with ⟨h1, -⟩ | ⟨-, hL, hout⟩
  · omega
  · exact p3 G H T M V K hS hlt hC2 hL hout hMK

@[expose] def R3Pkg1b7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case1 H T M K →
    IsPSL 2 7 1 ↥(E2.star M H K) →
    E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H)) →
    8 < E2.autCard (E2.star M H T) (E2.star M H K) → False

theorem r3Pkg1b_of_seven
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (p7 : R3Pkg1b7) : R3Pkg1b := by
  intro G _ _ H T M V K hS hlt h1 p hp hp8 hPSL hMK haut
  have h7 := eq_seven_of_oddPaired h38 hS.toHyp2 hS.not_solvable hS.mem_cComp hS.eq_sup h1 hp hp8
    hPSL haut
  subst h7
  exact p7 G H T M V K hS hlt h1 hPSL hMK haut

end E217R3

end CFSG.Quasithin
