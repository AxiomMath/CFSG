module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ExceptionalParabolicsGen
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Delta
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417RankOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Swap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsFourSixteenHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormalHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexFHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexWreathHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapSp4InFHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapL3InFHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W] [Finite W]

theorem pCore_two_eq_bot_of_isComponentOf_of_o2Trivial {Y L : Subgroup (MulAut W)}
    (hcomp : IsComponentOf L Y) (hO2 : O2Trivial Y) : CFSG.pCore 2 ↥L = ⊥ := by
  have hL : pCoreOf 2 L = ⊥ := by
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hcomp.2.1,
      o2Trivial_iff_pCoreOf_eq_bot.1 hO2, inf_bot_eq]
  rw [CFSG.openPCoreOf_eq_map_pCore] at hL
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hL

theorem isSubnormal_sup_of_le_of_isComponentOf {Y L K T : Subgroup (MulAut W)}
    (hcomp : IsComponentOf L Y) (hTY : T ≤ Y) (hKL : K ≤ L)
    (hinv : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      K.map (MulAut.conj t).toMonoidHom = K) :
    IsSubnormal K (K ⊔ T) := by
  set N : Subgroup (MulAut W) := CFSG.SignalizerFunctorTheorem.McBride.orbitClosure K T
    with hN
  have hKN : K ≤ N := CFSG.SignalizerFunctorTheorem.McBride.le_orbitClosure K T
  have hNle : N ≤ K ⊔ T := by
    refine CFSG.SignalizerFunctorTheorem.McBride.orbitClosure_le fun t ht => ?_
    rintro _ ⟨k, hk, rfl⟩
    have htKT : t ∈ K ⊔ T := (le_sup_right : T ≤ K ⊔ T) ht
    have hkKT : k ∈ K ⊔ T := (le_sup_left : K ≤ K ⊔ T) hk
    exact (K ⊔ T).mul_mem ((K ⊔ T).mul_mem htKT hkKT) ((K ⊔ T).inv_mem htKT)
  have hNnorm : N ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
    refine CFSG.SignalizerFunctorTheorem.McBride.orbitClosure_le fun t ht => ?_
    by_cases htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))
    · rw [hinv t ht htN]
      exact Subgroup.le_normalizer
    · have hLt : IsComponentOf (L.map (MulAut.conj t).toMonoidHom) Y :=
        CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hcomp (hTY ht)
      have hne : L ≠ L.map (MulAut.conj t).toMonoidHom := fun h =>
        htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
      have hc : ⁅L.map (MulAut.conj t).toMonoidHom, L⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact CFSG.Quasithin.B69.components_commute_of_ne hcomp hLt hne
      have h1 : L.map (MulAut.conj t).toMonoidHom ≤
          Subgroup.centralizer (K : Set (MulAut W)) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
          (Subgroup.centralizer_le hKL)
      exact (Subgroup.map_mono hKL).trans
        (h1.trans (Subgroup.centralizer_le_normalizer _))
  have hKn : (K.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hNnorm
  have hNn : (N.subgroupOf (K ⊔ T)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr (sup_le ?_ ?_)
    · exact hKN.trans Subgroup.le_normalizer
    · intro t ht
      exact CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514.mem_normalizer_orbitClosure ht
  exact IsSubnormal.step hKN hKn (IsSubnormal.step hNle hNn (IsSubnormal.refl _))

theorem bParam_le_of_inFSq (h416 : W4Lem4_16) (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    (hsq : InFSq n Y) : bParam L Y ≤ n := by
  refine bParam_le_of_fIndexSum_le h416 hW hLT hcomp hsyl hO2 hfix (Set.finite_singleton Y) ?_
    (by simp) ?_
  · intro H hH
    rw [Set.mem_singleton_iff.mp hH]
    exact ⟨le_rfl, hsyl.1⟩
  · rw [fIndexSum, finsum_mem_singleton]
    exact fIndex_le_iff.mpr hsq

theorem inFSq_sup_of_isSubnormal_rankOne
    (h43c : W3Lem45_2Chief) {G : Type} [Group G] [Finite G] {K T : Subgroup G} {n : ℕ}
    (hsub : IsSubnormal K (K ⊔ T)) (hperf : ⁅K, K⁆ = K) (hsyl : IsSylowIn 2 T (K ⊔ T))
    (hshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n) : InFSq n (K ⊔ T) := by
  have hKH : K ≤ K ⊔ T := le_sup_left
  have hTH : T ≤ K ⊔ T := le_sup_right
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := by
    rcases hshape with h | h
    · exact uc22p22sg_isQuasisimple_bar2_of_shape hperf (Or.inr (Or.inl h))
    · exact uc22p22sg_isQuasisimple_bar2_of_shape hperf (Or.inl h)
  let Kbar : Subgroup (Bar2 (K ⊔ T)) :=
    (K.subgroupOf (K ⊔ T)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T)))
  let Tbar : Subgroup (Bar2 (K ⊔ T)) :=
    (T.subgroupOf (K ⊔ T)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T)))
  have hKbar : CFSG.IsComponent Kbar :=
    s13_barImage_isComponent (M := K ⊔ T) (L := K) ⟨hsub, hperf, hq⟩
  have hTbar : IsSylowIn 2 Tbar ⊤ := isSylowIn_barImage hsyl
  have hgen : Kbar ⊔ Tbar = ⊤ := by
    have h := s13_barImage_sup (M := K ⊔ T) (A := K) (B := T) hKH hTH
    rw [s13_barImage_self] at h
    exact h.symm
  obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hKH hsub
  have hO2K : CFSG.pCore 2 ↥Kbar = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 e
    rw [pCore_two_bar2_eq_bot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hshapeK : IsL2 ↥Kbar n ∨ IsSz ↥Kbar n ∨ IsSU3 ↥Kbar n := by
    rcases hshape with h | h
    · exact Or.inl (LieModel.of_mulEquiv e h)
    · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
  have hU3 : S17.K_U3Index :=
    S17.k_U3Index_of_normal_and_F k_U3IndexNormal_holds S17.k_U3IndexF_holds h43c
  have hsq : InFSq n (⊤ : Subgroup (Bar2 (K ⊔ T))) :=
    inFSq_sup_of_rankOne h43c k_L2SzAutRank_holds hU3 ((CFSG.isComponent_iff_open Kbar).1 hKbar)
      hO2K hTbar hgen hshapeK
  obtain ⟨e2⟩ := nonempty_bar2_top_mulEquiv_of_pCore_eq_bot (pCore_two_bar2_eq_bot (K ⊔ T))
  exact (inFSq_iff_bar2_inF_mulEquiv e2 n).1 hsq

theorem isSL3_of_isL3_of_isQuasisimple {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsL3 X n) : UC22.IsSL3 X n := by
  have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  haveI := hs
  haveI := uc22p22a_qs_nontrivial hq
  have hc : Subgroup.center X = ⊥ :=
    uc22p22a_center_eq_bot (uc22p22d_noncomm_of_perfect hq.1)
  exact ⟨hq, CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm h⟩

theorem isSL3_of_isSLn_of_isQuasisimple {X : Type} [Group X] {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (h : IsSLn X 3 n) : UC22.IsSL3 X n := by
  have hn : 1 ≤ n := by
    obtain ⟨K, hKf, hKfin, hK, -⟩ := h
    letI : Field K := hKf
    haveI : Finite K := hKfin
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact hpos
  exact ⟨hq, Thm14_5.isLn_quot_center_of_isSLn h le_rfl hn⟩

theorem bParam_le_of_w4Lem4_17_one
    (h43c : W3Lem45_2Chief) (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} {n : ℕ} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    (hshape : IsL2 ↥L n ∨ IsSz ↥L n ∨ IsSU3 ↥L n ∨
      ((IsL3 ↥L n ∨ IsSLn ↥L 3 n ∨ IsSp4 ↥L n) ∧
        S17.SwapsParabolics (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) L)) :
    bParam L Y ≤ n := by
  have hL2 : CFSG.pCore 2 ↥L = ⊥ := pCore_two_eq_bot_of_isComponentOf_of_o2Trivial hcomp hO2
  have hsq : InFSq n Y := by
    have hU3 : S17.K_U3Index :=
      S17.k_U3Index_of_normal_and_F k_U3IndexNormal_holds S17.k_U3IndexF_holds h43c
    rcases hshape with h | h | h | ⟨hsh, hsw⟩
    · exact inFSq_sup_of_rankOne h43c k_L2SzAutRank_holds hU3 hcomp hL2 hsyl hLT (Or.inl h)
    · exact inFSq_sup_of_rankOne h43c k_L2SzAutRank_holds hU3 hcomp hL2 hsyl hLT
        (Or.inr (Or.inl h))
    · exact inFSq_sup_of_rankOne h43c k_L2SzAutRank_holds hU3 hcomp hL2 hsyl hLT
        (Or.inr (Or.inr h))
    · have hsh' : UC22.IsSL3 ↥L n ∨ IsSp4 ↥L n := by
        rcases hsh with h | h | h
        · exact Or.inl (isSL3_of_isL3_of_isQuasisimple hcomp.2.2 h)
        · exact Or.inl (isSL3_of_isSLn_of_isQuasisimple hcomp.2.2 h)
        · exact Or.inr h
      exact inFSq_sup_of_swap h43c k_SwapSp4InF_holds k_SwapL3InF_holds w4Lem4_10_holds hcomp
        hL2 hsyl hLT hsh' hsw
  exact bParam_le_of_inFSq w4Lem4_16_holds hW hLT hcomp hsyl hO2 hfix hsq

theorem bParam_le_two_mul_of_is2F4
    (h43c : W3Lem45_2Chief)
    (hP : K_2F4ParabolicGen) (hW : ∀ w : W, w ^ 2 = 1) {Y L T : Subgroup (MulAut W)} {n : ℕ}
    (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y)
    (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y) (h2F4 : Is2F4 n ↥L) :
    bParam L Y ≤ 2 * n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTY : T ≤ Y := hsyl.1
  have hLY : L ≤ Y := hcomp.1
  have hTL : IsSylowIn 2 (T ⊓ L) L :=
    CFSG.Quasithin.F6.isSylowIn_inf_of_isSubnormal hcomp.2.1 hsyl
  set S : Subgroup ↥L := (T ⊓ L).subgroupOf L with hSdef
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hTL.2.1.comap_of_injective L.subtype L.subtype_injective, ?_⟩
    have h1 : (S.subgroupOf (⊤ : Subgroup ↥L)).index = S.index := Subgroup.relIndex_top_right _
    rw [h1]
    exact hTL.2.2
  obtain ⟨Y₁, Y₂, hperf₁, hperf₂, hSz, hL2, hgen, hinv⟩ := hP ↥L n h2F4 S hS
  have hcompat : ∀ (t : MulAut W) (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)))
      (Z : Subgroup ↥L), (Z.map L.subtype).map (MulAut.conj t).toMonoidHom =
        (Z.map (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom).map L.subtype := by
    intro t htN Z
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hαS : ∀ (t : MulAut W) (ht : t ∈ T)
      (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))),
      S.map (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom = S := by
    intro t ht htN
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : MulAut W) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hx
      have hval : ((L.normalizerMonoidHom ⟨t, htN⟩ x : ↥L) : MulAut W) =
          t * (x : MulAut W) * t⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨t, htN⟩ x
      show (L.normalizerMonoidHom ⟨t, htN⟩ x : ↥L) ∈ (T ⊓ L).subgroupOf L
      rw [Subgroup.mem_subgroupOf, hval]
      exact ⟨T.mul_mem (T.mul_mem ht hx'.1) (T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp htN (x : MulAut W)).mp x.2⟩
    · exact (Subgroup.card_map_of_injective
        (f := (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom) (MulEquiv.injective _)).ge
  have hKinv : ∀ (Z : Subgroup ↥L), (∀ α : MulAut ↥L, S.map α.toMonoidHom = S →
      Z.map α.toMonoidHom = Z) → ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      (Z.map L.subtype).map (MulAut.conj t).toMonoidHom = Z.map L.subtype := by
    intro Z hZ t ht htN
    rw [hcompat t htN Z, hZ _ (hαS t ht htN)]
  set K₁ : Subgroup (MulAut W) := Y₁.map L.subtype with hK₁
  set K₂ : Subgroup (MulAut W) := Y₂.map L.subtype with hK₂
  have hK₁L : K₁ ≤ L := Subgroup.map_subtype_le Y₁
  have hK₂L : K₂ ≤ L := Subgroup.map_subtype_le Y₂
  have hinv₁ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      K₁.map (MulAut.conj t).toMonoidHom = K₁ :=
    hKinv Y₁ (fun α hα => (hinv α hα).1)
  have hinv₂ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      K₂.map (MulAut.conj t).toMonoidHom = K₂ :=
    hKinv Y₂ (fun α hα => (hinv α hα).2)
  have hbar : ∀ Z : Subgroup ↥L, Nonempty (Bar2 Z ≃* Bar2 (Z.map L.subtype)) := by
    intro Z
    let e : ↥Z ≃* ↥(Z.map L.subtype) := Z.equivMapOfInjective L.subtype L.subtype_injective
    exact ⟨QuotientGroup.congr (CFSG.pCore 2 ↥Z) (CFSG.pCore 2 ↥(Z.map L.subtype)) e
      (CFSG.pCore_map_iso 2 e)⟩
  obtain ⟨e₁⟩ := hbar Y₁
  obtain ⟨e₂⟩ := hbar Y₂
  have hsylH : ∀ K : Subgroup (MulAut W), K ≤ Y → IsSylowIn 2 T (K ⊔ T) := by
    intro K hKY
    refine ⟨le_sup_right, hsyl.2.1, fun h => hsyl.2.2 ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex T (K ⊔ T) Y le_sup_right (sup_le hKY hTY)]
    exact Dvd.dvd.mul_right h _
  have hInF₁ : InFSq n (K₁ ⊔ T) :=
    inFSq_sup_of_isSubnormal_rankOne h43c
      (isSubnormal_sup_of_le_of_isComponentOf hcomp hTY hK₁L hinv₁)
      (by rw [hK₁, ← Subgroup.map_commutator, hperf₁]) (hsylH K₁ (hK₁L.trans hLY))
      (Or.inr (LieModel.of_mulEquiv e₁ hSz))
  have hInF₂ : InFSq n (K₂ ⊔ T) :=
    inFSq_sup_of_isSubnormal_rankOne h43c
      (isSubnormal_sup_of_le_of_isComponentOf hcomp hTY hK₂L hinv₂)
      (by rw [hK₂, ← Subgroup.map_commutator, hperf₂]) (hsylH K₂ (hK₂L.trans hLY))
      (Or.inl (LieModel.of_mulEquiv e₂ hL2))
  have hLle : L ≤ K₁ ⊔ K₂ ⊔ T := by
    have hmap := congrArg (Subgroup.map L.subtype) hgen
    rw [Subgroup.map_sup, Subgroup.map_sup, hSdef, Subgroup.subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    calc L = Y₁.map L.subtype ⊔ Y₂.map L.subtype ⊔ T ⊓ L ⊓ L := hmap.symm
      _ ≤ K₁ ⊔ K₂ ⊔ T :=
        sup_le le_sup_left ((inf_le_left.trans inf_le_left).trans le_sup_right)
  have hsupΔ : (⨆ H ∈ ({K₁ ⊔ T, K₂ ⊔ T} : Set (Subgroup (MulAut W))), H) = Y := by
    rw [iSup_insert, iSup_singleton]
    refine le_antisymm (sup_le (sup_le (hK₁L.trans hLY) hTY) (sup_le (hK₂L.trans hLY) hTY)) ?_
    rw [← hLT]
    refine sup_le (hLle.trans (sup_le (sup_le ?_ ?_) ?_)) ?_
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have hsum : fIndexSum ({K₁ ⊔ T, K₂ ⊔ T} : Set (Subgroup (MulAut W))) ≤
      ((2 * n : ℕ) : ℕ∞) := by
    by_cases h12 : K₁ ⊔ T = K₂ ⊔ T
    · rw [h12, Set.pair_eq_singleton, fIndexSum, finsum_mem_singleton]
      exact (fIndex_le_iff.mpr hInF₂).trans (by exact_mod_cast (by omega : n ≤ 2 * n))
    · rw [fIndexSum, finsum_mem_pair h12]
      calc fIndex (K₁ ⊔ T) + fIndex (K₂ ⊔ T) ≤ (n : ℕ∞) + n :=
            add_le_add (fIndex_le_iff.mpr hInF₁) (fIndex_le_iff.mpr hInF₂)
        _ = ((2 * n : ℕ) : ℕ∞) := by push_cast; ring
  refine bParam_le_of_fIndexSum_le w4Lem4_16_holds hW hLT hcomp hsyl hO2 hfix
    ((Set.finite_singleton _).insert _) ?_ hsupΔ hsum
  intro H hH
  rcases hH with rfl | hH
  · exact ⟨sup_le (hK₁L.trans hLY) hTY, le_sup_right⟩
  · rw [Set.mem_singleton_iff.mp hH]
    exact ⟨sup_le (hK₂L.trans hLY) hTY, le_sup_right⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
