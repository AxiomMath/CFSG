module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ShapeId
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrNat
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

private theorem s16t3_card_natOmegaMinus_six {L : Subgroup (MulAut W)} {I : Subgroup W}
    (h : NatOmegaMinus L I ⊥ 6 1) : Nat.card ↥I = 64 := by
  obtain ⟨-, K, hKf, hKfin, b, c, hK, -, hreal⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hcard := s16c1610_card_of_realizes_nat (V := W) hreal
  rw [hK] at hcard
  have hidx : Fintype.card (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2) = 6 := by
    simp [Fintype.card_sum]
  rw [hidx] at hcard
  norm_num at hcard
  exact hcard

private theorem s16t3_exists_order_three_stabilizer
    {G X : Type} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    (hG : Fintype.card G = 25920) (hX : Fintype.card X ≤ 64) (w : X) :
    ∃ y : G, orderOf y = 3 ∧ y • w = w := by
  classical
  haveI : Fintype (MulAction.orbit G w) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer G w) := Fintype.ofFinite _
  haveI : Nonempty (MulAction.orbit G w) := ⟨⟨w, MulAction.mem_orbit_self w⟩⟩
  haveI : Nonempty (MulAction.stabilizer G w) := ⟨1⟩
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) w
  have hOle : Fintype.card (MulAction.orbit G w) ≤ 64 :=
    (Fintype.card_le_of_injective (fun x : MulAction.orbit G w => (x : X))
      Subtype.coe_injective).trans hX
  have hO3 : (Fintype.card (MulAction.orbit G w)).factorization 3 ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ (Fintype.card (MulAction.orbit G w)).factorization 3 := not_le.1 h
    have hdvd : 3 ^ 4 ∣ Fintype.card (MulAction.orbit G w) :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (Fintype.card_ne_zero (α := MulAction.orbit G w))).2 h4
    have hle : 3 ^ 4 ≤ Fintype.card (MulAction.orbit G w) :=
      Nat.le_of_dvd (Fintype.card_pos_iff.mpr inferInstance) hdvd
    have hcontra : (81 : ℕ) ≤ 64 := by
      calc (81 : ℕ) = 3 ^ 4 := by norm_num
        _ ≤ Fintype.card (MulAction.orbit G w) := hle
        _ ≤ 64 := hOle
    omega
  have hfac : (Fintype.card (MulAction.orbit G w) *
        Fintype.card (MulAction.stabilizer G w)).factorization 3 =
      (Fintype.card (MulAction.orbit G w)).factorization 3 +
        (Fintype.card (MulAction.stabilizer G w)).factorization 3 := by
    rw [Nat.factorization_mul (Fintype.card_ne_zero (α := MulAction.orbit G w))
      (Fintype.card_ne_zero (α := MulAction.stabilizer G w)), Finsupp.add_apply]
  have h4 : 4 ≤ (Fintype.card (MulAction.orbit G w) *
        Fintype.card (MulAction.stabilizer G w)).factorization 3 := by
    rw [hOS, hG]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).1
      ⟨320, by norm_num⟩
  have hS3 : 1 ≤ (Fintype.card (MulAction.stabilizer G w)).factorization 3 := by
    rw [hfac] at h4
    omega
  have hdvd3 : 3 ∣ Nat.card (MulAction.stabilizer G w) := by
    rw [Nat.card_eq_fintype_card]
    exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three
      (Fintype.card_ne_zero (α := MulAction.stabilizer G w))).2 hS3
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer G w) 3 hdvd3
  exact ⟨(y : G), by rw [Subgroup.orderOf_coe, hy], MulAction.mem_stabilizer_iff.mp y.2⟩

theorem ThreeNat.exists_fix_vector_omegaMinus6 (h : ThreeNat A L T)
    (hL : IsOmegaMinus ↥L 6 1) :
    ∃ w : W, w ≠ 1 ∧ (∀ t ∈ T, t w = w) ∧ ∃ y ∈ L, orderOf y = 3 ∧ y w = w := by
  classical
  have hWp : IsPGroup 2 W := fun g => ⟨1, by rw [pow_one, pow_two]; exact h.elem g⟩
  have hTp : IsPGroup 2 ↥T := h.sylow.isPGroup
  have hLcard : Nat.card ↥L = 25920 := s16c167_card_isOmegaMinus_six hL
  by_cases hZ : fixV L = ⊥
  ·
    obtain ⟨I, hI, hTI, hInat⟩ := h.exists_stable_natural
    have hInat' : SumOfNatShape L I ⊥ 1 := by simpa [hZ] using hInat
    have hOm : NatOmegaMinus L I ⊥ 6 1 :=
      s16t3_sumOfNat_one (s16t3_shape_branch_omegaMinus hInat' hL)
    have hcardI : Nat.card ↥I = 64 := s16t3_card_natOmegaMinus_six hOm
    have hLI : StableUnder L I := hI.2.2.1
    have hI2 : 2 ∣ Nat.card ↥I := by rw [hcardI]; norm_num
    letI : MulAction ↥T ↥I :=
      { smul := fun t x => ⟨(t : MulAut W) (x : W), hTI t t.2 x x.2⟩
        one_smul := fun _ => Subtype.ext rfl
        mul_smul := fun _ _ _ => Subtype.ext rfl }
    have h1fix : (1 : ↥I) ∈ MulAction.fixedPoints ↥T ↥I := by
      rw [MulAction.mem_fixedPoints]
      intro t
      exact Subtype.ext (map_one (t : MulAut W))
    obtain ⟨w, hwfix, hwne⟩ :=
      hTp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥I) hI2 h1fix
    have hwt : ∀ t : ↥T, (t : MulAut W) (w : W) = (w : W) :=
      fun t => congrArg Subtype.val (MulAction.mem_fixedPoints.1 hwfix t)
    have hwW_ne : (w : W) ≠ 1 := fun h1 => hwne (Subtype.ext (by simpa using h1.symm))
    letI : MulAction ↥L ↥I :=
      { smul := fun l x => ⟨(l : MulAut W) (x : W), hLI l l.2 x x.2⟩
        one_smul := fun _ => Subtype.ext rfl
        mul_smul := fun _ _ _ => Subtype.ext rfl }
    haveI : Fintype ↥L := Fintype.ofFinite _
    haveI : Fintype ↥I := Fintype.ofFinite _
    have hLc : Fintype.card ↥L = 25920 := by rw [← Nat.card_eq_fintype_card, hLcard]
    have hIc : Fintype.card ↥I ≤ 64 := by rw [← Nat.card_eq_fintype_card, hcardI]
    obtain ⟨y, hyord, hyw⟩ := s16t3_exists_order_three_stabilizer hLc hIc w
    exact ⟨(w : W), hwW_ne, fun t ht => hwt ⟨t, ht⟩,
      ⟨(y : MulAut W), y.2, by rw [Subgroup.orderOf_coe, hyord], congrArg Subtype.val hyw⟩⟩
  ·
    have hTnorm : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := h.sylow.le.trans h.normal
    have hZstab : StableUnder T (fixV L) := by
      intro t ht z hz
      rw [mem_fixV] at hz ⊢
      intro l hl
      have htinv : t⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        (Subgroup.normalizer (L : Set (MulAut W))).inv_mem (hTnorm ht)
      have hconj : t⁻¹ * l * t ∈ L := (Subgroup.mem_normalizer_iff.mp htinv l).mp hl
      calc l (t z) = (l * t) z := rfl
        _ = (t * (t⁻¹ * l * t)) z := by congr 1; group
        _ = t ((t⁻¹ * l * t) z) := rfl
        _ = t z := by rw [hz _ hconj]
    have hZnontriv : Nontrivial ↥(fixV L) := (Subgroup.nontrivial_iff_ne_bot (H := fixV L)).mpr hZ
    have hZp : IsPGroup 2 ↥(fixV L) := hWp.to_subgroup (fixV L)
    have hZ2 : 2 ∣ Nat.card ↥(fixV L) := by
      obtain ⟨k, hk⟩ := hZp.exists_card_eq
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · exfalso
          rw [hk0, pow_zero] at hk
          have := Finite.one_lt_card_iff_nontrivial.mpr hZnontriv
          omega
        · exact hkpos
      rw [hk]
      exact pow_dvd_pow 2 hk1
    letI : MulAction ↥T ↥(fixV L) :=
      { smul := fun t z => ⟨(t : MulAut W) (z : W), hZstab t t.2 z z.2⟩
        one_smul := fun _ => Subtype.ext rfl
        mul_smul := fun _ _ _ => Subtype.ext rfl }
    have h1fix : (1 : ↥(fixV L)) ∈ MulAction.fixedPoints ↥T ↥(fixV L) := by
      rw [MulAction.mem_fixedPoints]
      intro t
      exact Subtype.ext (map_one (t : MulAut W))
    obtain ⟨w, hwfix, hwne⟩ :=
      hTp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥(fixV L)) hZ2 h1fix
    have hwt : ∀ t : ↥T, (t : MulAut W) (w : W) = (w : W) :=
      fun t => congrArg Subtype.val (MulAction.mem_fixedPoints.1 hwfix t)
    have hwW_ne : (w : W) ≠ 1 := fun h1 => hwne (Subtype.ext (by simpa using h1.symm))
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3dvd : 3 ∣ Nat.card ↥L := by rw [hLcard]; norm_num
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3dvd
    exact ⟨(w : W), hwW_ne, fun t ht => hwt ⟨t, ht⟩,
      ⟨(y : MulAut W), y.2, by rw [Subgroup.orderOf_coe, hy],
        mem_fixV.mp w.2 (y : MulAut W) y.2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
