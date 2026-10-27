module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417Delta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsFourSixteenHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Reps417RankOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormalHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexFHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexWreathHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem inFSq_sup_of_isSubnormal_SU3
    (h43c : W3Lem45_2Chief) {G : Type} [Group G] [Finite G] {K T : Subgroup G} {n : ℕ}
    (hsub : IsSubnormal K (K ⊔ T)) (hperf : ⁅K, K⁆ = K) (hsyl : IsSylowIn 2 T (K ⊔ T))
    (hshape : UC22.IsSU3 (Bar2 K) n) : InFSq n (K ⊔ T) := by
  have hKH : K ≤ K ⊔ T := le_sup_left
  have hTH : T ≤ K ⊔ T := le_sup_right
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hshape.1
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
  have hshapeK : IsL2 ↥Kbar n ∨ IsSz ↥Kbar n ∨ UC22.IsSU3 ↥Kbar n :=
    Or.inr (Or.inr (uc22p20p_isSU3_of_mulEquiv e hshape))
  have hU3 : S17.K_U3Index :=
    S17.k_U3Index_of_normal_and_F k_U3IndexNormal_holds S17.k_U3IndexF_holds h43c
  have hsq : InFSq n (⊤ : Subgroup (Bar2 (K ⊔ T))) :=
    inFSq_sup_of_rankOne h43c k_L2SzAutRank_holds hU3 ((CFSG.isComponent_iff_open Kbar).1 hKbar)
      hO2K hTbar hgen hshapeK
  obtain ⟨e2⟩ := nonempty_bar2_top_mulEquiv_of_pCore_eq_bot (pCore_two_bar2_eq_bot (K ⊔ T))
  exact (inFSq_iff_bar2_inF_mulEquiv e2 n).1 hsq


section Pair

variable {W : Type} [CommGroup W] [Finite W]

theorem map_conj_map_subtype_eq_map_normalizerMonoidHom (L : Subgroup (MulAut W)) (t : MulAut W)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (Z : Subgroup ↥L) :
    (Z.map L.subtype).map (MulAut.conj t).toMonoidHom =
      (Z.map (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom).map L.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_normalizerMonoidHom_subgroupOf_inf_eq (T L : Subgroup (MulAut W)) (t : MulAut W)
    (ht : t ∈ T) (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ((T ⊓ L).subgroupOf L).map (L.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom =
      (T ⊓ L).subgroupOf L := by
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

theorem map_conj_subtype_eq_of_invariant (T L : Subgroup (MulAut W)) (S : Subgroup ↥L)
    (hSdef : S = (T ⊓ L).subgroupOf L) (Z : Subgroup ↥L)
    (hZ : ∀ α : MulAut ↥L, S.map α.toMonoidHom = S → Z.map α.toMonoidHom = Z)
    (t : MulAut W) (ht : t ∈ T)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (Z.map L.subtype).map (MulAut.conj t).toMonoidHom = Z.map L.subtype := by
  rw [map_conj_map_subtype_eq_map_normalizerMonoidHom L t htN Z]
  have h := hZ _ (by rw [hSdef]; exact map_normalizerMonoidHom_subgroupOf_inf_eq T L t ht htN)
  rw [h]

theorem nonempty_bar2_subtype_map (L : Subgroup (MulAut W)) (Z : Subgroup ↥L) :
    Nonempty (Bar2 Z ≃* Bar2 (Z.map L.subtype)) := by
  let e : ↥Z ≃* ↥(Z.map L.subtype) := Z.equivMapOfInjective L.subtype L.subtype_injective
  exact ⟨QuotientGroup.congr (CFSG.pCore 2 ↥Z) (CFSG.pCore 2 ↥(Z.map L.subtype)) e
    (CFSG.pCore_map_iso 2 e)⟩

theorem isSylowIn_sup_of_le_of_isSylowIn {T Y : Subgroup (MulAut W)} (hsyl : IsSylowIn 2 T Y)
    {K : Subgroup (MulAut W)} (hKY : K ≤ Y) : IsSylowIn 2 T (K ⊔ T) := by
  refine ⟨le_sup_right, hsyl.2.1, fun h => hsyl.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T (K ⊔ T) Y le_sup_right (sup_le hKY hsyl.1)]
  exact Dvd.dvd.mul_right h _

theorem bParam_le_add_of_pair_inFSq (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    {K₁ K₂ : Subgroup (MulAut W)} {n₁ n₂ c : ℕ} (hK₁L : K₁ ≤ L) (hK₂L : K₂ ≤ L)
    (hLle : L ≤ K₁ ⊔ K₂ ⊔ T) (h₁ : InFSq n₁ (K₁ ⊔ T)) (h₂ : InFSq n₂ (K₂ ⊔ T))
    (hc : n₁ + n₂ ≤ c) : bParam L Y ≤ c := by
  have hTY : T ≤ Y := hsyl.1
  have hLY : L ≤ Y := hcomp.1
  have hsupΔ : (⨆ H ∈ ({K₁ ⊔ T, K₂ ⊔ T} : Set (Subgroup (MulAut W))), H) = Y := by
    rw [iSup_insert, iSup_singleton]
    refine le_antisymm (sup_le (sup_le (hK₁L.trans hLY) hTY) (sup_le (hK₂L.trans hLY) hTY)) ?_
    rw [← hLT]
    refine sup_le (hLle.trans (sup_le (sup_le ?_ ?_) ?_)) ?_
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have hsum : fIndexSum ({K₁ ⊔ T, K₂ ⊔ T} : Set (Subgroup (MulAut W))) ≤ (c : ℕ∞) := by
    by_cases h12 : K₁ ⊔ T = K₂ ⊔ T
    · rw [h12, Set.pair_eq_singleton, fIndexSum, finsum_mem_singleton]
      refine (fIndex_le_iff.mpr h₂).trans ?_
      exact_mod_cast (le_trans (Nat.le_add_left n₂ n₁) hc)
    · rw [fIndexSum, finsum_mem_pair h12]
      calc fIndex (K₁ ⊔ T) + fIndex (K₂ ⊔ T) ≤ (n₁ : ℕ∞) + n₂ :=
            add_le_add (fIndex_le_iff.mpr h₁) (fIndex_le_iff.mpr h₂)
        _ = ((n₁ + n₂ : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ (c : ℕ∞) := by exact_mod_cast hc
  refine bParam_le_of_fIndexSum_le w4Lem4_16_holds hW hLT hcomp hsyl hO2 hfix
    ((Set.finite_singleton _).insert _) ?_ hsupΔ hsum
  intro H hH
  rcases hH with rfl | hH
  · exact ⟨sup_le (hK₁L.trans hLY) hTY, le_sup_right⟩
  · rw [Set.mem_singleton_iff.mp hH]
    exact ⟨sup_le (hK₂L.trans hLY) hTY, le_sup_right⟩

theorem isMaxParabolicOver_map_subtype_of_isCoatom {G : Type} [Group G] (L : Subgroup G)
    {S P : Subgroup ↥L} (hP : IsCoatom P) (hN : Subgroup.normalizer (S : Set ↥L) ≤ P) :
    S17.IsMaxParabolicOver L (S.map L.subtype) (P.map L.subtype) := by
  have hmemS : ∀ y : ↥L, (y : G) ∈ S.map L.subtype ↔ y ∈ S := fun y =>
    Subgroup.mem_map_iff_mem L.subtype_injective
  refine ⟨Subgroup.map_subtype_le P, ?_, ?_, ?_⟩
  · rintro x ⟨hxL, hxN⟩
    refine ⟨⟨x, hxL⟩, hN ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [← hmemS s, ← hmemS (⟨x, hxL⟩ * s * ⟨x, hxL⟩⁻¹)]
    exact Subgroup.mem_normalizer_iff.mp hxN (s : G)
  · intro h
    apply hP.1
    apply Subgroup.map_injective L.subtype_injective
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · intro Q hPQ hQL
    rcases eq_or_ne (Q.subgroupOf L) P with h | h
    · left
      rw [← h, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQL]
    · right
      have hle : P ≤ Q.subgroupOf L := fun p hp => by
        rw [Subgroup.mem_subgroupOf]
        exact hPQ ⟨p, hp, rfl⟩
      have htop : Q.subgroupOf L = ⊤ := hP.2 _ (lt_of_le_of_ne hle (Ne.symm h))
      refine le_antisymm hQL fun x hx => ?_
      have hx' : (⟨x, hx⟩ : ↥L) ∈ Q.subgroupOf L := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'

end Pair

theorem inFSq_sup_of_isSubnormal_of_shape
    (h43c : W3Lem45_2Chief) {G : Type} [Group G] [Finite G] {K T : Subgroup G} {n : ℕ}
    (hsub : IsSubnormal K (K ⊔ T)) (hperf : ⁅K, K⁆ = K) (hsyl : IsSylowIn 2 T (K ⊔ T))
    (hshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n ∨ UC22.IsSU3 (Bar2 K) n) :
    InFSq n (K ⊔ T) := by
  rcases hshape with h | h | h
  · exact inFSq_sup_of_isSubnormal_rankOne h43c hsub hperf hsyl (Or.inl h)
  · exact inFSq_sup_of_isSubnormal_rankOne h43c hsub hperf hsyl (Or.inr h)
  · exact inFSq_sup_of_isSubnormal_SU3 h43c hsub hperf hsyl h

section PairShape

variable {W : Type} [CommGroup W] [Finite W]

theorem bParam_le_of_pair_of_conj_inv
    (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    {n₁ n₂ c : ℕ} {Y₁ Y₂ : Subgroup ↥L}
    (hgen : Y₁ ⊔ Y₂ ⊔ (T ⊓ L).subgroupOf L = ⊤)
    (hperf₁ : ⁅Y₁, Y₁⁆ = Y₁) (hperf₂ : ⁅Y₂, Y₂⁆ = Y₂)
    (hsh₁ : IsL2 (Bar2 Y₁) n₁ ∨ IsSz (Bar2 Y₁) n₁ ∨ UC22.IsSU3 (Bar2 Y₁) n₁)
    (hsh₂ : IsL2 (Bar2 Y₂) n₂ ∨ IsSz (Bar2 Y₂) n₂ ∨ UC22.IsSU3 (Bar2 Y₂) n₂)
    (hinv₁ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      (Y₁.map L.subtype).map (MulAut.conj t).toMonoidHom = Y₁.map L.subtype)
    (hinv₂ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      (Y₂.map L.subtype).map (MulAut.conj t).toMonoidHom = Y₂.map L.subtype)
    (hc : n₁ + n₂ ≤ c) : bParam L Y ≤ c := by
  have hInF : ∀ {Z : Subgroup ↥L} {m : ℕ}, ⁅Z, Z⁆ = Z →
      (IsL2 (Bar2 Z) m ∨ IsSz (Bar2 Z) m ∨ UC22.IsSU3 (Bar2 Z) m) →
      (∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut W)) →
        (Z.map L.subtype).map (MulAut.conj t).toMonoidHom = Z.map L.subtype) →
      InFSq m (Z.map L.subtype ⊔ T) := by
    intro Z m hperf hsh hinv
    obtain ⟨e⟩ := nonempty_bar2_subtype_map L Z
    refine inFSq_sup_of_isSubnormal_of_shape
      CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.w3Lem45_2Chief_holds
      (isSubnormal_sup_of_le_of_isComponentOf hcomp hsyl.1 (Subgroup.map_subtype_le Z) hinv) ?_
      (isSylowIn_sup_of_le_of_isSylowIn hsyl ((Subgroup.map_subtype_le Z).trans hcomp.1)) ?_
    · rw [← Subgroup.map_commutator, hperf]
    · rcases hsh with h | h | h
      · exact Or.inl (LieModel.of_mulEquiv e h)
      · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
      · exact Or.inr (Or.inr (uc22p20p_isSU3_of_mulEquiv e h))
  have hLle : L ≤ Y₁.map L.subtype ⊔ Y₂.map L.subtype ⊔ T := by
    have hmap := congrArg (Subgroup.map L.subtype) hgen
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    calc L = Y₁.map L.subtype ⊔ Y₂.map L.subtype ⊔ T ⊓ L ⊓ L := hmap.symm
      _ ≤ Y₁.map L.subtype ⊔ Y₂.map L.subtype ⊔ T :=
          sup_le le_sup_left ((inf_le_left.trans inf_le_left).trans le_sup_right)
  exact bParam_le_add_of_pair_inFSq hW hLT hcomp hsyl hO2 hfix (Subgroup.map_subtype_le Y₁)
    (Subgroup.map_subtype_le Y₂) hLle (hInF hperf₁ hsh₁ hinv₁) (hInF hperf₂ hsh₂ hinv₂) hc

theorem bParam_le_of_pair_of_aut_inv
    (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)} (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hO2 : O2Trivial Y) (hfix : fixV T ≠ fixV Y)
    {n₁ n₂ c : ℕ} {Y₁ Y₂ : Subgroup ↥L}
    (hgen : Y₁ ⊔ Y₂ ⊔ (T ⊓ L).subgroupOf L = ⊤)
    (hperf₁ : ⁅Y₁, Y₁⁆ = Y₁) (hperf₂ : ⁅Y₂, Y₂⁆ = Y₂)
    (hsh₁ : IsL2 (Bar2 Y₁) n₁ ∨ IsSz (Bar2 Y₁) n₁ ∨ UC22.IsSU3 (Bar2 Y₁) n₁)
    (hsh₂ : IsL2 (Bar2 Y₂) n₂ ∨ IsSz (Bar2 Y₂) n₂ ∨ UC22.IsSU3 (Bar2 Y₂) n₂)
    (hinv : ∀ α : MulAut ↥L,
      ((T ⊓ L).subgroupOf L).map α.toMonoidHom = (T ⊓ L).subgroupOf L →
        Y₁.map α.toMonoidHom = Y₁ ∧ Y₂.map α.toMonoidHom = Y₂)
    (hc : n₁ + n₂ ≤ c) : bParam L Y ≤ c :=
  bParam_le_of_pair_of_conj_inv hW hLT hcomp hsyl hO2 hfix hgen hperf₁ hperf₂ hsh₁ hsh₂
    (fun t ht htN => map_conj_subtype_eq_of_invariant T L _ rfl Y₁
      (fun α hα => (hinv α hα).1) t ht htN)
    (fun t ht htN => map_conj_subtype_eq_of_invariant T L _ rfl Y₂
      (fun α hα => (hinv α hα).2) t ht htN) hc

end PairShape

theorem isSylowTwoOf_subgroupOf_inf {W : Type} [CommGroup W] [Finite W]
    {Y L T : Subgroup (MulAut W)} (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : IsSylowIn 2 (T ⊓ L) L :=
    CFSG.Quasithin.F6.isSylowIn_inf_of_isSubnormal hcomp.2.1 hsyl
  refine ⟨le_top, hTL.2.1.comap_of_injective L.subtype L.subtype_injective, ?_⟩
  have h1 : (((T ⊓ L).subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index =
      ((T ⊓ L).subgroupOf L).index := Subgroup.relIndex_top_right _
  rw [h1]
  exact hTL.2.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
