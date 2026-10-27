module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TMB2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open CFSG.Quasithin.H13.L828T
open scoped IsMulCommutative commutatorElement

@[expose] def MBRows {V : Type} [CommGroup V] (H X : Subgroup (MulAut V)) : Prop :=
  (BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) ∨
    (MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) ∨
    (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) ∨
    (MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3)

section MBApp

variable {G : Type} [Group G] [Finite G]

theorem s828_mb_data (hcard : Mathieu.StmtH13Card) {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) (c : S828Ctx T L I H h k) :
    autOn (ch82A (fsuV T I) h) (fsuV T I) ≤
        Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) ∧
      IsElemAbelian2 (autOn (ch82A (fsuV T I) h) (fsuV T I)) ∧
      MBRows (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)) := by
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian c.hAe
  have hrows := rows_hlu82_828 hcard c.hL0 c.hV c.hC5 c.hAN hAp
  refine ⟨autOn_le_normalizer_82 c.hAL, isElemAbelian2_of_828 (isElemAbelian_autOn_82 c.hAe), ?_⟩
  rcases hrow with hr | hr | hr | hr
  · exact Or.inl (hrows.1 hr)
  · exact Or.inr (Or.inl (hrows.2.1 hr))
  · exact Or.inr (Or.inr (Or.inl (hrows.2.2.1 hr)))
  · exact Or.inr (Or.inr (Or.inr (hrows.2.2.2 hr)))

theorem s828_mb_eqs {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) :
    s828BPrime (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
        (ch82B (fsuV T I) h).subgroupOf (fsuV T I) ∧
      fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
        (ch82U (fsuV T I) h).subgroupOf (fsuV T I) ∧
      perfectCore (autOn L (fsuV T I) ⊓ stabSub (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) =
        autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) := by
  refine ⟨?_, fixV_autOn_82 c.hAN, s828_perfect_autOn_LU c.hLN c.hAN⟩
  have h1 := s828_B'_eq_map c.hLN c.hAN c.hAL
  rw [← c.hB] at h1
  have h2 : ((s828BPrime (autOn L (fsuV T I))
      (autOn (ch82A (fsuV T I) h) (fsuV T I))).map (fsuV T I).subtype).comap
        (fsuV T I).subtype = s828BPrime (autOn L (fsuV T I))
          (autOn (ch82A (fsuV T I) h) (fsuV T I)) :=
    Subgroup.comap_map_eq_self_of_injective (fsuV T I).subtype_injective _
  rw [← h2, ← h1]
  rfl

theorem mb2_unit_five' (hMB2 : MB2_828) (V : Type) [CommGroup V] [Finite V]
    (H X : Subgroup (MulAut V)) (hXH : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hX : IsElemAbelian2 X) (hrow : MBRows H X) {B' U' : Subgroup V} {S : Set (MulAut V)}
    (hB' : s828BPrime H X = B') (hU' : fixV X = U')
    (hS : (perfectCore (H ⊓ stabSub (fixV X)) : Set (MulAut V)) = S)
    (φ : AddMonoid.End (QMod B' U')) (hφ : φ ∈ commutant B' U' S) (n : ℕ)
    (hn : φ ^ 5 ^ n = 1) : φ = 1 := by
  subst hB' hU' hS
  exact mb2_unit_five hMB2 V H X hXH hX hrow φ hφ n hn

theorem mb2_field4' (hMB2 : MB2_828) (V : Type) [CommGroup V] [Finite V]
    (H X : Subgroup (MulAut V)) (hXH : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hX : IsElemAbelian2 X)
    (hr : (BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) ∨
      (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7))
    {B' U' : Subgroup V} {S : Set (MulAut V)}
    (hB' : s828BPrime H X = B') (hU' : fixV X = U')
    (hS : (perfectCore (H ⊓ stabSub (fixV X)) : Set (MulAut V)) = S) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥(commutant B' U' S) ≃+* K) := by
  subst hB' hU' hS
  exact (hMB2 V H X hXH hX).1 hr

theorem mb2_field2' (hMB2 : MB2_828) (V : Type) [CommGroup V] [Finite V]
    (H X : Subgroup (MulAut V)) (hXH : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hX : IsElemAbelian2 X)
    (hr : MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6)
    {B' U' : Subgroup V} {S : Set (MulAut V)}
    (hB' : s828BPrime H X = B') (hU' : fixV X = U')
    (hS : (perfectCore (H ⊓ stabSub (fixV X)) : Set (MulAut V)) = S) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (↥(commutant B' U' S) ≃+* K) := by
  subst hB' hU' hS
  exact (hMB2 V H X hXH hX).2.1 hr

theorem s828_mb2_unit_five_G (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) (c : S828Ctx T L I H h k)
    (φ : AddMonoid.End (QMod ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))))
    (hφ : φ ∈ commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
      ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
      ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
        Set (MulAut ↥(fsuV T I))))
    (n : ℕ) (hn : φ ^ 5 ^ n = 1) : φ = 1 := by
  obtain ⟨hX, hXe, hr⟩ := s828_mb_data hcard hrow c
  obtain ⟨e1, e2, e3⟩ := s828_mb_eqs c
  exact mb2_unit_five' hMB2 _ _ _ hX hXe hr e1 e2 (by rw [e3]) φ hφ n hn

theorem s828_mb2_field4_G (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) (hr : (∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M24Code T L I) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
        ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
          Set (MulAut ↥(fsuV T I)))) ≃+* K) := by
  have hrow : Case8_2 T L I := by
    rcases hr with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inr (Or.inl hr))
  obtain ⟨hX, hXe, -⟩ := s828_mb_data hcard hrow c
  obtain ⟨e1, e2, e3⟩ := s828_mb_eqs c
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian c.hAe
  have hrows := rows_hlu82_828 hcard c.hL0 c.hV c.hC5 c.hAN hAp
  have hsel : (BinaryNineTensor (autOn L (fsuV T I)) ⊤ ⊥ 1 ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 4 ∧
        rk ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 4) ∨
      (MathieuCode24 (autOn L (fsuV T I)) ⊤ ⊥ ∧
        rk ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 6 ∧
        rkIdx (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 7) := by
    rcases hr with hr | hr
    · exact Or.inl (hrows.1 hr)
    · exact Or.inr (hrows.2.2.1 hr)
  exact mb2_field4' hMB2 _ _ _ hX hXe hsel e1 e2 (by rw [e3])

theorem s828_mb2_field2_G (hMB2 : MB2_828) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) (hr : Row711M22Code T L I) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (↥(commutant ((ch82B (fsuV T I) h).subgroupOf (fsuV T I))
        ((ch82U (fsuV T I) h).subgroupOf (fsuV T I))
        ((autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I) : Subgroup (MulAut ↥(fsuV T I))) :
          Set (MulAut ↥(fsuV T I)))) ≃+* K) := by
  have hrow : Case8_2 T L I := Or.inr (Or.inl hr)
  obtain ⟨hX, hXe, -⟩ := s828_mb_data hcard hrow c
  obtain ⟨e1, e2, e3⟩ := s828_mb_eqs c
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian c.hAe
  have hrows := rows_hlu82_828 hcard c.hL0 c.hV c.hC5 c.hAN hAp
  exact mb2_field2' hMB2 _ _ _ hX hXe (hrows.2.1 hr) e1 e2 (by rw [e3])

end MBApp

end CFSG.Quasithin.H13
