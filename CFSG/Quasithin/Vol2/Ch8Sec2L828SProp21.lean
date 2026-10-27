module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828SLem12
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SMB
public import CFSG.Quasithin.Vol2.Ch8Sec2L828C
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section L828SProp21

variable {G : Type} [Group G] [Finite G]

theorem s828_perfect_autOn_LU {T L I : Subgroup G} {h : G}
    [IsMulCommutative ↥(fsuV T I)]
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    perfectCore (autOn L (fsuV T I) ⊓ stabSub (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) =
      autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) := by
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  rw [hfix, ← autOn_inf_normalizer_82 hUV, ← autOn_perfectCore_82 (inf_le_left.trans hLN)]
  rfl

theorem s828_B'_eq_map {T L I : Subgroup G} {h : G} [IsMulCommutative ↥(fsuV T I)]
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G)) :
    ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔ ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔
        ch82U (fsuV T I) h =
      (s828BPrime (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I))).map
        (fsuV T I).subtype := by
  have hLUN : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hLN)
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  unfold s828BPrime
  rw [Subgroup.map_sup, Subgroup.map_sup, s828_perfect_autOn_LU hLN hAN, hfix,
    CFSG.Quasithin.AutOn.map_commV_autOn_eq hAN, CFSG.Quasithin.AutOn.map_commV_autOn_eq hLUN,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUV]

theorem s828_mQuot_map {W : Subgroup G} (X : Subgroup ↥W) :
    mQuot W (X.map W.subtype) = mQuot ⊤ X := by
  unfold mQuot
  congr 1
  have h1 := Subgroup.relIndex_map_map_of_injective X ⊤ W.subtype_injective
  have htop : (⊤ : Subgroup ↥W).map W.subtype = W := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [htop] at h1
  exact h1

theorem s828_prop21 {T L I H : Subgroup G} {h : G} {k : ℕ} [hc : IsMulCommutative ↥(fsuV T I)]
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    (hrow : Case8_2 T L I) (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H)
    (hC : Concl822 T L I H h k) (hC5 : Concl825 T L I h k)
    (hMB0 : MB0_828) (hSyl : Sylow822VB_828) (hcard : Mathieu.StmtH13Card)
    (hV : IsElemAbelian 2 (fsuV T I)) (hL0 : fsuL0 T L = L)
    (hVT : fsuV T I ≤ T) (hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hVB : ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ≤ ch82B (fsuV T I) h) :
    ch82B (fsuV T I) h = ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔
      ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := s828_pair hV hVT hTV hC
  have hCc := hC
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, -, -, hA7, -, -, -, -, hUB, -, -, -⟩ := hC
  set V := fsuV T I with hVdef
  set A := ch82A V h with hAdef
  set U := ch82U V h with hUdef
  set LU := ch82LU L U with hLUdef
  set B := ch82B V h with hBdef
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hA7]
    exact inf_le_right
  have hAP : A ≤ pCoreOf 2 (ch82I V h) := inf_le_right
  have hAe : IsElemAbelian 2 A := isElemAbelian_of_le_conjSub_82 hV inf_le_left
  have hAp : IsPGroup 2 ↥A := B6.isPGroup_of_isElemAbelian hAe
  have hVA : ⁅V, A⁆ ≤ B :=
    (Subgroup.commutator_mono le_rfl hAP).trans (s828_commutator_V_le_B hP hker)
  have hB'le : ⁅V, A⁆ ⊔ ⁅V, LU⁆ ⊔ U ≤ B := sup_le (sup_le hVA hVB) hUB
  have hX : autOn A V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
    autOn_le_normalizer_82 hAL
  have hXe : IsElemAbelian2 (autOn A V) := isElemAbelian2_of_828 (isElemAbelian_autOn_82 hAe)
  have hrows := rows_hlu82_828 hcard hL0 hV hC5 hAN hAp
  have hmB' : mQuot V (⁅V, A⁆ ⊔ ⁅V, LU⁆ ⊔ U) = k := by
    rw [s828_B'_eq_map hLN hAN hAL, s828_mQuot_map]
    rcases hrow with hr | hr | hr | hr
    · have hk : k = 1 := by
        have := hC5.1.symm.trans (hC5.2.2.2.1 hr).1
        exact_mod_cast this
      rw [hk]
      exact (hMB0 V (autOn L V) (autOn A V) hX hXe).1 (hrows.1 hr)
    · have hk : k = 1 := by
        have := hC5.1.symm.trans (hC5.2.2.2.2.1 hr).1
        exact_mod_cast this
      rw [hk]
      exact (hMB0 V (autOn L V) (autOn A V) hX hXe).2.1 (hrows.2.1 hr)
    · have hk : k = 1 := by
        have := hC5.1.symm.trans (hC5.2.2.2.2.2.1 hr).1
        exact_mod_cast this
      rw [hk]
      exact (hMB0 V (autOn L V) (autOn A V) hX hXe).2.2.1 (hrows.2.2.1 hr)
    · have hk : k = 2 := by
        have := hC5.1.symm.trans (hC5.2.2.2.2.2.2.1 hr).1
        exact_mod_cast this
      rw [hk]
      exact (hMB0 V (autOn L V) (autOn A V) hX hXe).2.2.2 (hrows.2.2.2 hr)
  have hmB : mQuot V B = k := hSyl G T L I hyp h731 h821 hc hrow H h k hH hh hCc
  have hVp : IsPGroup 2 ↥V := B6.isPGroup_of_isElemAbelian hV
  have hBV : B ≤ V := inf_le_left
  have e1 := card_eq_two_pow_mul hVp hBV
  have e2 := card_eq_two_pow_mul hVp (hB'le.trans hBV)
  rw [hmB] at e1
  rw [hmB'] at e2
  have hcardeq : Nat.card ↥(⁅V, A⁆ ⊔ ⁅V, LU⁆ ⊔ U) = Nat.card ↥B := by
    have := e2.symm.trans e1
    have hpos : 0 < 2 ^ k := by positivity
    exact Nat.eq_of_mul_eq_mul_left hpos this
  exact (Subgroup.eq_of_le_of_card_ge hB'le (le_of_eq hcardeq.symm)).symm

end L828SProp21

end CFSG.Quasithin.H13
