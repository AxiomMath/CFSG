module

public import CFSG.Quasithin.H13.A6S1372Fifteen
public import CFSG.Quasithin.Background.B42SmallComm
public import CFSG.Quasithin.Background.B5IrrA

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6FifteenB

variable {V : Type} [CommGroup V] [Finite V]

theorem card_commV_autSec_le (X : Subgroup (MulAut V)) (W U : Subgroup V) :
    Nat.card (commV (autSec X W U)) ≤ Nat.card (commV X) := by
  classical
  set q : ↥W →* Sec W U := QuotientGroup.mk' (U.subgroupOf W) with hq
  have hle : commV (autSec X W U) ≤ ((commV X).subgroupOf W).map q := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, s, rfl⟩
    obtain ⟨ψ, hψX, rfl⟩ := mem_autQuot.1 hφ
    obtain ⟨g, hgX, hg⟩ := mem_autSub.1 hψX
    induction s using QuotientGroup.induction_on with
    | H w =>
      have hgw : g.1 (w : V) ∈ W := (g.2 (w : V)).2 w.2
      refine ⟨⟨g.1 (w : V) * (w : V)⁻¹, W.mul_mem hgw (W.inv_mem w.2)⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨g.1, hgX, (w : V), rfl⟩), ?_⟩
      rw [quotHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      show QuotientGroup.mk _ = QuotientGroup.mk _
      congr 1
      apply Subtype.ext
      show g.1 (w : V) * (w : V)⁻¹ = ((ψ.1 w : ↥W) : V) * (w : V)⁻¹
      rw [← hg]
      rfl
  calc Nat.card (commV (autSec X W U)) ≤ Nat.card (((commV X).subgroupOf W).map q) :=
        Subgroup.card_le_of_le hle
    _ ≤ Nat.card ((commV X).subgroupOf W) :=
        Nat.le_of_dvd Nat.card_pos (((commV X).subgroupOf W).card_map_dvd q)
    _ ≤ Nat.card (commV X) := by
        refine Nat.card_le_card_of_injective
          (fun d => (⟨((d : ↥W) : V), d.2⟩ : ↥(commV X))) ?_
        intro a b hab
        exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥(commV X) => (x : V)) hab))

@[expose] def B42Restricted (G L A : Subgroup (MulAut V)) : Prop :=
  (B42Case1 G L A ∧ BinaryNaturalSL L ⊤ ⊥ 2 2) ∨
    (B42Case2 G L ∧ ∀ n, BinaryNaturalSL L ⊤ ⊥ 3 n → n ≤ 2) ∨
    (B42Case3 G L ∧ ∀ n, BinaryNaturalSp4 (ffJ G) ⊤ ⊥ n → n ≤ 2) ∨
    B42Case4 G L A ∨ B42Case5 G A ∨ B42Case6 G L A ∨ B42Case7 G L A ∨ B42Case9 G L ∨
    B42Case10 G L A ∨ B42Case11 G L A

theorem le_two_of_realizes {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {H A : Subgroup (MulAut V)} {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥) (hAH : A ≤ H) (hA : A ≠ ⊥)
    (hc : Nat.card (commV A) ≤ 4) : n ≤ 2 := by
  obtain ⟨π, hπ⟩ := hR
  have h1 := (B42Small.card_field_le_card_commV hπ hAH hA).trans hc
  rw [hF] at h1
  by_contra hn
  push Not at hn
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem restricted_of_card_le_four {G L A : Subgroup (MulAut V)} (hb4 : B4Hyp G L)
    (hA : IsFFStarOffender G A) (hc : Nat.card (commV A) ≤ 4) (h : B42Conclusion G L A) :
    B42Restricted G L A := by
  have hAJ : A ≤ ffJ G := B6.le_ffJ hA
  have hA0 : A ≠ ⊥ := hA.2.1
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact Or.inl ⟨h1, B42Small.natural_two_of_case1 h1 hb4 hA0 hc⟩
  · refine Or.inr (Or.inl ⟨h2, fun n hn => ?_⟩)
    obtain ⟨F, _, _, hF, hR⟩ := hn
    exact le_two_of_realizes hF hR (hAJ.trans h2.1.le) hA0 hc
  · refine Or.inr (Or.inr (Or.inl ⟨h3, fun n hn => ?_⟩))
    obtain ⟨F, _, _, hF, hR⟩ := hn
    exact le_two_of_realizes hF hR hAJ hA0 hc
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  · exact (B42Small.not_case8 h8 hA hc).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h11))))))))

theorem exists_section_offender_of (hV : ∀ v : V, v ^ 2 = 1) {G L B : Subgroup (MulAut V)}
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤) (hB : IsFFStarOffender G B) :
    ∃ B', B' ≤ autSec B (commV L) (fixV L ⊓ commV L) ∧
      IsFFStarOffender (autSec (L ⊔ B) (commV L) (fixV L ⊓ commV L)) B' := by
  have hn := B5.normal_L h
  have hLG := B5.le_G h
  have hTG : B ≤ G := hB.1
  have hT2 : IsPGroup 2 B := hB.2.2.1.isPGroup
  have hGU : G ≤ stabSub (commV L) := B5.le_stabSub_commV hn (fun g hg => G.inv_mem hg)
  have hGC : G ≤ stabSub (fixV L ⊓ commV L) :=
    B5.le_stabSub_fixV_inf_commV hn (fun g hg => G.inv_mem hg)
  have hMG : L ⊔ B ≤ G := sup_le hLG hTG
  have hAM : IsFFStarOffender (L ⊔ B) B := ⟨le_sup_right, hB.2.1, hB.2.2.1, hB.2.2.2⟩
  obtain ⟨-, hcomm, hlt, -⟩ := B5.irr_data hU
  have hS : ¬ commSub (commV L) (quasithinGenFitting (L ⊔ B)) ≤ fixV L ⊓ commV L := by
    rw [B5.genFitting_sup_eq h hTG hT2, hcomm]
    intro hle
    have h1 : fixV L ⊓ commV L = commV L := le_antisymm inf_le_right hle
    rw [inf_comm, h1] at hlt
    exact lt_irrefl _ hlt
  have hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (L ⊔ B)) := by
    rw [B5.genFitting_sup_eq h hTG hT2]
    exact B5.quasi_L h
  obtain ⟨-, ⟨B', hB'A, hB'⟩, -⟩ := B1_5_8 hV hAM (W := commV L) (U := fixV L ⊓ commV L)
    inf_le_right (hMG.trans hGU) (hMG.trans hGC) hq (B5.pCoreOf_sup_eq_bot h hTG hT2) hS
  exact ⟨B', hB'A, hB'⟩

theorem b42Restricted_section (h42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    {G L B : Subgroup (MulAut V)} (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤)
    (hB : IsFFStarOffender G B) (hc : Nat.card (commV B) ≤ 4) :
    ∃ B', B' ≤ autSec B (commV L) (fixV L ⊓ commV L) ∧
      IsFFStarOffender (autSec (L ⊔ B) (commV L) (fixV L ⊓ commV L)) B' ∧
      B4Hyp (autSec (L ⊔ B) (commV L) (fixV L ⊓ commV L))
        (autSec L (commV L) (fixV L ⊓ commV L)) ∧
      B42Restricted (autSec (L ⊔ B) (commV L) (fixV L ⊓ commV L))
        (autSec L (commV L) (fixV L ⊓ commV L)) B' := by
  obtain ⟨B', hB'B, hB'⟩ := exists_section_offender_of hV h hU hB
  have hb4 := B5.b4Hyp_section hV h hU hB.1 hB.2.2.1.isPGroup
  have hc' : Nat.card (commV B') ≤ 4 :=
    (Subgroup.card_le_of_le (B19.commV_mono hB'B)).trans
      ((card_commV_autSec_le _ _ _).trans hc)
  have hconcl := h42 (Sec (commV L) (fixV L ⊓ commV L)) (sq_eq_one_sec hV _ _) _ _ hb4 B' hB'
  exact ⟨B', hB'B, hB', hb4, restricted_of_card_le_four hb4 hB' hc' hconcl⟩

@[expose] def K15 (J K B : Subgroup (MulAut V)) : Prop :=
  (B51Case1i J K ∧ ∃ B', B' ≤ autSec B (commV K) (fixV K ⊓ commV K) ∧
      IsFFStarOffender (autSec (K ⊔ B) (commV K) (fixV K ⊓ commV K)) B' ∧
      B4Hyp (autSec (K ⊔ B) (commV K) (fixV K ⊓ commV K))
        (autSec K (commV K) (fixV K ⊓ commV K)) ∧
      B42Restricted (autSec (K ⊔ B) (commV K) (fixV K ⊓ commV K))
        (autSec K (commV K) (fixV K ⊓ commV K)) B') ∨
    (J = K ∧ ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      DirectSumOfCopies K (commV K) ⊥
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) 1)

end A6FifteenB

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem b51Hyp_J (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
    {K : Subgroup G}
    (hB : IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B)
    (hKcomp : CFSG.Open.IsComponentOf (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
      (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
    (hBN : B ≤ Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
      Subgroup _) : Set _))
    (hBnot : ¬ B ≤ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
      Subgroup _) : Set _))
    (hFJ : quasithinGenFitting (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) =
      autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) :
    B51Hyp (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
      (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
  have hHU : H ≤ Subgroup.normalizer ((conjClosure S.V3 H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  set ρ := A6Mod.secAct hHU hHC with hρ
  set X := autSec (autOn H (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hX
  set Kp := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hKp
  set J := ffJ X with hJ
  have hrange : ρ.range = X := S.range_secAct_plus
  have hKq : CFSG.IsQuasisimple ↥Kp := B1Red.isQuasisimple_of_open hKcomp.2.2
  have hKB : ⁅Kp, B⁆ = Kp := FFJImage.commutator_eq_of_not_le_centralizer hKq hBN hBnot
  have hKX : Kp ≤ X := hKcomp.1
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple
    S.h13.nonabelian hH.1.2
  have hSQX : SQTKGroup ↥X := by
    have h1 := InternalSec.sqtkGroup_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      (by
        rw [MonoidHom.ker_rangeRestrict, S.ker_secAct_plus hNS h13315 h1356two hH hab hNU hhat
          hLem]
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)) hSQ
    exact hrange ▸ h1
  have hSQK : SQTKGroup ↥Kp :=
    A6Fifteen.sqtkGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX)
      (InternalSec.sqtkGroup_subgroup hSQX (Kp.subgroupOf X))
  have hO2 := S.pCoreOf_plus_eq_bot hNS h13315 h1356two hH hab hNU hhat hLem
  have hb53 : B53Hyp J := by
    rw [hJ, ← hrange]
    exact FFJImage.b53Hyp_ffJ_range hSQ ρ (by rw [hrange]; exact hO2)
  have hKJ : Kp ≤ J := B1Red.K_le_ffJ hKX hB.1 hKB
  have hZ : centerOf J ≤ Kp := hFJ ▸ InternalSec.centerOf_le_quasithinGenFitting J
  exact ⟨by rw [hFJ, sup_eq_left.2 hZ], hKq, hSQK, hKJ, hb53.1, hb53.2.1⟩

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem card_commV_le_four
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14)
    [IsMulCommutative ↥(conjClosure S.V3 H)]
    {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
    (hBA : B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) :
    Nat.card (commV B) ≤ 4 := by
  have hAH := C.A_le_H hNS h13315 h1356two hH hab hhat
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hUH : conjClosure S.V3 H ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hBW := (B19.commV_mono hBA).trans (C.commV_A_plus_le hUH hAH fun u hu a ha =>
    C.comm_UH_A_mem hNS h13315 h1356two hH hab hhat hna h13314 hu ha)
  exact (Subgroup.card_le_of_le hBW).trans (S.card_V3_plus hNS h13315 h1356two hH h13314).le

theorem exists_K_b42
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) (hLem : Lem1374One) (h56 : AsB56) (h51 : AsB51) (h42 : AsB42)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B, IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
      B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
      ∃ K ∈ cComp H, CFSG.Open.IsComponentOf (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
          (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
        B ≤ Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        ¬ B ≤ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ≤
          Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
              Subgroup _) : Set _) ∧
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) = ⊤ ∧
        quasithinGenFitting (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) =
          autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
        Nat.card (commV B) ≤ 4 ∧
        A6FifteenB.K15 (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
          (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B := by
  obtain ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, hcases⟩ :=
    C.exists_K_b51 hNS h13315 h1356two hH hab hhat hNU hna h13314 hLem h56 h51
  have hb51 := S.b51Hyp_J hNS h13315 h1356two hH hab hhat hNU hLem hB hKcomp hBN hBnot hFJ
  have hB4 := C.card_commV_le_four hNS h13315 h1356two hH hab hhat hna h13314 hBA
  have hBJ : IsFFStarOffender (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) B :=
    ⟨B6.le_ffJ hB.1, hB.1.2.1, hB.1.2.2.1, hB.1.2.2.2⟩
  have hV' : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hV := Bridge.sec_sq_eq_one hV' (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))
  refine ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, hB4, ?_⟩
  rcases hcases with h1 | h2
  · exact Or.inl ⟨h1, A6FifteenB.b42Restricted_section h42 hV hb51 h1.1 hBJ hB4⟩
  · exact Or.inr h2

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
