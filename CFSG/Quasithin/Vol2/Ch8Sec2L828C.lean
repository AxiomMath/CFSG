module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825L
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsLU
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section L828C

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem rk_subgroupOf_828 {U V : Subgroup G} (hUV : U ≤ V) : rk ↥(U.subgroupOf V) = rk ↥U := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv]

theorem rows_hlu82_828 (hcard : Mathieu.StmtH13Card) [hc : IsMulCommutative ↥(fsuV T I)]
    (hL0 : fsuL0 T L = L) (hV : IsElemAbelian 2 (fsuV T I)) {h : G} {k : ℕ}
    (hC5 : Concl825 T L I h k)
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h)) :
    ((∃ n : ℕ, Row711L3Nine T L I n) →
        BinaryNineTensor (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ 1 ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 4 ∧
        rk ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 4) ∧
      (Row711M22Code T L I → MathieuCode22 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 5 ∧
        rkIdx (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 6) ∧
      (Row711M24Code T L I → MathieuCode24 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 6 ∧
        rkIdx (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 7) ∧
      (Row711M24Cocode T L I → MathieuCocode24 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 6 ∧
        rk ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  rw [hfix]
  obtain ⟨-, -, hn1, hTabL, hTabM, hTab24, hTab24c, -⟩ := hC5
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hrkA : rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      mQuot (ch82A (fsuV T I) h)
        (ch82A (fsuV T I) h ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    unfold rk
    rw [card_autOn_82 hAN hAp, padicValNat.prime_pow]
  have hrkU := rk_subgroupOf_828 hUV
  have hidx : rkIdx ((ch82U (fsuV T I) h).subgroupOf (fsuV T I)) =
      mQuot (fsuV T I) (ch82U (fsuV T I) h) := rfl
  have hsum := mQuot_add_rk (A := fsuV T I) (B := ch82U (fsuV T I) h) hUV
  refine ⟨fun ⟨n, hn⟩ => ?_, fun hr => ?_, fun hr => ?_, fun hr => ?_⟩
  · obtain rfl := hn1 n hn
    obtain ⟨-, -, hA4, hU4⟩ := hTabL ⟨1, hn⟩
    exact ⟨by rw [← hL0]; exact hn.2, by rw [hrkA, hA4], by rw [hrkU, hU4]⟩
  · obtain ⟨-, -, hA5, hU4⟩ := hTabM hr
    have hV10 : rk ↥(fsuV T I) = 10 :=
      rk_eq_of_card_82 ((hcard ↥(fsuV T I) (autOn (fsuL0 T L) (fsuV T I))).2.2 (Or.inr hr))
    refine ⟨by rw [← hL0]; exact hr, by rw [hrkA, hA5], ?_⟩
    rw [hidx]
    omega
  · obtain ⟨-, -, hA6, hU4⟩ := hTab24 hr
    have hV11 : rk ↥(fsuV T I) = 11 :=
      rk_eq_of_card_82 ((hcard ↥(fsuV T I) (autOn (fsuL0 T L) (fsuV T I))).1 (Or.inr hr))
    refine ⟨by rw [← hL0]; exact hr, by rw [hrkA, hA6], ?_⟩
    rw [hidx]
    omega
  · obtain ⟨-, -, hA6, hU3⟩ := hTab24c hr
    exact ⟨by rw [← hL0]; exact hr, by rw [hrkA, hA6], by rw [hrkU, hU3]⟩

omit [Finite G] in
theorem isElemAbelian2_of_828 {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
    (hX : IsElemAbelian 2 X) : IsElemAbelian2 X := by
  refine ⟨fun a ha b hb => ?_, hX.2⟩
  have := hX.1
  exact setLike_mul_comm ha hb

theorem hlu82_82 (hLU : HLU82) (hcard : Mathieu.StmtH13Card) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) (hL0 : fsuL0 T L = L) (hV : IsElemAbelian 2 (fsuV T I))
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G)) {h : G} {k : ℕ}
    (hC5 : Concl825 T L I h k) (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h)) (hAe : IsElemAbelian 2 (ch82A (fsuV T I) h)) :
    CFSG.IsQuasisimple (↥(autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I)) ⧸
        CFSG.pCore 2 ↥(autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))) ∧
      (((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I) →
        AlternatingNatural (V := ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))))
          (autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
            (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) ⊤ ⊥ 5) ∧
      (Row711M24Code T L I →
        AlternatingNatural (V := ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))))
          (autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
            (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) ⊤ ⊥ 6) ∧
      (Row711M24Cocode T L I →
        autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
          (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = ⊤) := by
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  have hP : perfectCore (autOn L (fsuV T I) ⊓ stabSub (fixV (autOn (ch82A (fsuV T I) h)
      (fsuV T I)))) = autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) := by
    rw [hfix, ← autOn_inf_normalizer_82 hUV, ← autOn_perfectCore_82 (inf_le_left.trans hLN)]
    rfl
  obtain ⟨hr9, hr22, hr24, hr24c⟩ := rows_hlu82_828 hcard hL0 hV hC5 hAN hAp
  have hrows : (BinaryNineTensor (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ 1 ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 4 ∧
        rk ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 4) ∨
      (MathieuCode22 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 5 ∧
        rkIdx (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 6) ∨
      (MathieuCode24 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 6 ∧
        rkIdx (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 7) ∨
      (MathieuCocode24 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 6 ∧
        rk ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 3) := by
    rcases hrow with hr | hr | hr | hr
    · exact Or.inl (hr9 hr)
    · exact Or.inr (Or.inl (hr22 hr))
    · exact Or.inr (Or.inr (Or.inl (hr24 hr)))
    · exact Or.inr (Or.inr (Or.inr (hr24c hr)))
  obtain ⟨hq, h5, h6, h3⟩ := hLU ↥(fsuV T I) (autOn L (fsuV T I))
    (autOn (ch82A (fsuV T I) h) (fsuV T I)) (autOn_le_normalizer_82 hAL)
    (isElemAbelian2_of_828 (isElemAbelian_autOn_82 hAe)) hrows
  refine ⟨?_, fun hr => ?_, fun hr => ?_, fun hr => ?_⟩
  · rw [← hP]
    exact hq
  · rw [← hP]
    rcases hr with hr | hr
    · exact h5 (Or.inl (hr9 hr))
    · exact h5 (Or.inr (hr22 hr))
  · rw [← hP]
    exact h6 (hr24 hr)
  · rw [← hP]
    exact h3 (hr24c hr)

end L828C

end CFSG.Quasithin.H13
