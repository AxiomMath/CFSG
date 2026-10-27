module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Quasithin.Background.HSL2InvFix
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4SubPSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SectionRank.ClassicalEven

variable {W : Type} [CommGroup W]

private theorem s16h_nontrivial_of_isQuasisimple {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  haveI : Nontrivial (X ⧸ Subgroup.center X) := h.2.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial

private theorem s16h_isSolvable_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    [Group.IsSolvable H] : Group.IsSolvable G :=
  Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s16h_subsingleton_statedSL_le_one {n : ℕ} (hn : n ≤ 1) (K : Type) [Field K] :
    Subsingleton ↥(StatedSL n K) := by
  haveI : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
  rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
  exact Subtype.ext (by rw [← hx, ← hy, Subsingleton.elim x y])

private theorem s16h_subsingleton_statedSU_le_one {n : ℕ} (hn : n ≤ 1) (K : Type) [Field K] :
    Subsingleton ↥(StatedSU n 2 K) := by
  haveI : Subsingleton ↥(StatedSL n K) := s16h_subsingleton_statedSL_le_one hn K
  exact (Subgroup.inclusion_injective
    (CFSG.Open.StatedAPI.statedSU_le_statedSL n 2 K)).subsingleton

private theorem s16h_pRank_eq_top_of_mulEquiv {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {X : Type} [Group X] [Finite X] (e : ↥L ≃* X) :
    CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L).trans
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e)

private theorem s16h_two_le_pRank_three_statedSU {n : ℕ} (hn : 3 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSU n 2 K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard_units : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard_units])
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    omega
  have hcube : ∀ x : Kˣ, x ^ 3 = 1 := by
    intro x
    have h := pow_card_eq_one' (G := Kˣ) (x := x)
    rwa [hcard_units] at h
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h02 : i0 ≠ i2 := fun h => by
    have := congrArg Fin.val h
    simp [i0, i2] at this
  have h12 : i1 ≠ i2 := fun h => by
    have := congrArg Fin.val h
    simp [i1, i2] at this
  have h10 : i1 ≠ i0 := fun h => by
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hv0 : (torusVec ζ i0 i2) ^ 3 = 1 := by
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    exact hcube _
  have hv1 : (torusVec ζ i1 i2) ^ 3 = 1 := by
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    exact hcube _
  have hmem0 : torusDiag (torusVec ζ i0 i2) ∈ StatedSU n 2 K :=
    torusDiag_mem_SU (by norm_num : 2 ≠ 0) (prod_torusVec ζ i0 i2) hv0
  have hmem1 : torusDiag (torusVec ζ i1 i2) ∈ StatedSU n 2 K :=
    torusDiag_mem_SU (by norm_num : 2 ≠ 0) (prod_torusVec ζ i1 i2) hv1
  refine CFSG.Quasithin.A3Facts.two_le_pRank_of_gens
    (x := (⟨torusDiag (torusVec ζ i0 i2), hmem0⟩ : ↥(StatedSU n 2 K)))
    (y := (⟨torusDiag (torusVec ζ i1 i2), hmem1⟩ : ↥(StatedSU n 2 K))) ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hv0, map_one]
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hv1, map_one]
  · apply Subtype.ext
    exact ((Commute.all (torusVec ζ i0 i2) (torusVec ζ i1 i2)).map torusDiag).eq
  · intro h
    have h1 : torusDiag (torusVec ζ i0 i2) = 1 := congrArg Subtype.val h
    have h2 : torusVec ζ i0 i2 = 1 := torusDiag_injective (by rw [h1, map_one])
    have h3 := congrFun h2 i0
    rw [torusVec_apply_left ζ h02] at h3
    exact hζ1 (by simpa using h3)
  · intro m h
    have h1 : (torusDiag (torusVec ζ i0 i2)) ^ m = torusDiag (torusVec ζ i1 i2) :=
      congrArg Subtype.val h
    rw [← map_pow, torusVec_pow] at h1
    have h2 : torusVec (ζ ^ m) i0 i2 = torusVec ζ i1 i2 := torusDiag_injective h1
    have h3 := congrFun h2 i1
    rw [torusVec_apply_of_ne (ζ ^ m) h10 h12, torusVec_apply_left ζ h12] at h3
    exact hζ1 h3.symm

theorem s16h_H5_isSUn_class [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {n : ℕ} (h : IsSUn ↥L n 1) : False := by
  obtain ⟨K, hF, hFin, hKcard, ⟨e⟩⟩ := h
  letI := hF
  letI := hFin
  have hK4 : Nat.card K = 4 := by simpa using hKcard
  rcases lt_or_ge n 3 with hn | hn
  · have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    have hN : Nontrivial ↥L := s16h_nontrivial_of_isQuasisimple hc.comp.2.2
    rcases hn' with rfl | rfl | rfl
    · haveI : Subsingleton ↥(StatedSU 0 2 K) :=
        s16h_subsingleton_statedSU_le_one (n := 0) (by omega) K
      haveI : Subsingleton ↥L :=
        ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
      obtain ⟨a, b, hab⟩ := hN
      exact hab (Subsingleton.elim a b)
    · haveI : Subsingleton ↥(StatedSU 1 2 K) :=
        s16h_subsingleton_statedSU_le_one (n := 1) (by omega) K
      haveI : Subsingleton ↥L :=
        ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
      obtain ⟨a, b, hab⟩ := hN
      exact hab (Subsingleton.elim a b)
    · haveI : Group.IsPerfect ↥L := ⟨hc.comp.2.2.1⟩
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
        CFSG.GroupTheory.groups_order_below_sixty_solvable
          (G := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
          (by rw [CFSG.Quasithin.H.SL2Nat.card_sl2]; norm_num)
      obtain ⟨e2⟩ := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4.su2_equiv_sl2
        (K := K) (r := 2) (by simpa using hK4)
      haveI : Group.IsSolvable ↥(StatedSU 2 2 K) := s16h_isSolvable_of_mulEquiv e2
      haveI : Group.IsSolvable ↥L := s16h_isSolvable_of_mulEquiv e
      exact (Group.IsPerfect.not_isSolvable ↥L) inferInstance
  · have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
      rw [s16h_pRank_eq_top_of_mulEquiv e]
      exact s16h_two_le_pRank_three_statedSU hn hK4
    have h1 := hc.thin 3 Nat.prime_three (by norm_num)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
