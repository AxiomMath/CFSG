module

public import CFSG.Quasithin.Vol2.Ch10SecKId
public import CFSG.Quasithin.Vol2.Ch10SecQ1SU3
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] {G L : Subgroup (MulAut V)}

theorem nontrivial_of_targetCard (hT : TargetCard (Nat.card ↥L)) : Nontrivial ↥L := by
  have h := le_of_targetCard hT
  have : Finite ↥L := Nat.finite_of_card_ne_zero (by omega)
  exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

theorem false_of_row_alt7 (h : AlternatingNatural L ⊤ ⊥ 7) (hT : TargetCard (Nat.card ↥L)) :
    False := by
  obtain ⟨π, hR⟩ := h
  refine false_of_simple_surj (SecA.isSimpleGroup_alt (n := 7) (by norm_num)) ?_ hT π hR.1
  rw [SecA.card_alt 7 (by norm_num)]
  exact not_targetCard_2520

theorem false_of_row_orth {m : ℕ} (hm : 1 ≤ m) (h : BinaryOrthogonalFour L ⊤ ⊥ m)
    (hT : TargetCard (Nat.card ↥L)) : False := by
  obtain ⟨K, _, _, _, hK, π, hR⟩ := h
  have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Ch11.SecA.isSimpleGroup_SL2 (n := 2 * m) (by omega) hK
  have hs' : IsSimpleGroup ↥(StatedSL 2 K) :=
    (specialLinearGroupEquivStatedSL 2 K).symm.isSimpleGroup
  refine false_of_simple_surj hs' ?_ hT π hR.1
  rw [SecA.card_statedSL, SecA.card_SL_two_pow hK]
  exact not_targetCard_sl2 _

theorem false_of_row_su3 {m : ℕ} (h : BinaryNaturalSU3 L ⊤ ⊥ m) (hT : TargetCard (Nat.card ↥L))
    (hZ : Nat.card (Subgroup.center ↥L) ≤ 3) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_equiv
  have ha : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact hpos
  set Z₀ := (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ m) K) with hZ₀
  have hcardL : Nat.card ↥L = Nat.card (StatedProj (StatedSU 3 (2 ^ m) K)) * Nat.card Z₀ := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Z₀
  have hP := SecA.C10P01.card_psu3 ha hK
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm1 : m = 1 := by omega
    have h72 : Nat.card (StatedProj (StatedSU 3 (2 ^ m) K)) = 72 := by
      rw [hP, hm1]
      norm_num
    have hle : Z₀ ≤ Subgroup.center ↥(StatedSU 3 (2 ^ m) K) := by
      intro x hx
      have hc : (x : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact hx
      exact Subgroup.mem_center_iff.2 fun y =>
        Subtype.ext (Subgroup.mem_center_iff.mp hc (y : GL (Fin 3) K))
    have hZc : Nat.card Z₀ ≤ 3 :=
      calc Nat.card Z₀ ≤ Nat.card (Subgroup.center ↥(StatedSU 3 (2 ^ m) K)) :=
            Subgroup.card_le_of_le hle
        _ = Nat.card (Subgroup.center ↥L) := Nat.card_congr (Subgroup.centerCongr e).toEquiv
        _ ≤ 3 := hZ
    refine not_targetCard_of_lt ?_ hT
    rw [hcardL, h72]
    omega
  · refine not_sixteen_dvd hT ?_
    rw [hcardL, hP]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul]
    exact (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 (by omega)

theorem false_of_row_sz {f : ℕ} (h : BinaryNaturalSz L ⊤ ⊥ f)
    (hT : TargetCard (Nat.card ↥L)) : False := by
  obtain ⟨a, K, _, _, ha, hf, hK, ⟨e⟩⟩ := h.exists_equiv
  subst hf
  refine not_sixteen_dvd hT ?_
  rw [← Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
  rw [← pow_mul]
  exact (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 (by omega)

theorem false_of_row_nine {m : ℕ} (hm : 1 ≤ m) (h : BinaryNineTensor L ⊤ ⊥ m)
    (hT : TargetCard (Nat.card ↥L)) : False := by
  obtain ⟨K, _, _, _, hK, π, hR⟩ := h
  have := nontrivial_of_targetCard hT
  have htriv := sl3_hom_trivial hK (by omega) (not_sixteen_dvd hT)
    (π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
  obtain ⟨g, rfl⟩ := hR.1 x
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 3 K).surjective g
  exact hx (htriv A)

theorem false_of_row_g2d
    (h : G2NaturalDerived L ⊤ ⊥ 1) (hT : TargetCard (Nat.card ↥L)) : False := by
  obtain ⟨K, _, _, hK, π, hR⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  refine false_of_simple_surj (H13.isSimpleGroup_g2Two_commutator hK2) ?_ hT π hR.1
  rw [SecA.C10P01.card_g2Two_commutator hK2]
  exact not_targetCard_of_dvd (by norm_num)

theorem false_of_part3 [Finite V] (h3 : AsB45Part3 G L)
    (hT : TargetCard (Nat.card ↥L)) : False := by
  obtain ⟨-, -, ⟨a, ha, K, _, _, _, hK, π, hR⟩ | ⟨⟨e⟩, -, -⟩⟩ := h3
  · have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
        (Or.inl (Or.inr h4))
    have hbij : Function.Bijective
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    have hsimple' : IsSimpleGroup ↥(StatedSp 2 K) := (MulEquiv.ofBijective _ hbij).isSimpleGroup
    refine false_of_simple_surj hsimple' ?_ hT π hR.1
    rw [SecA.card_Sp4_pow hK]
    exact not_targetCard_of_dvd (sixteen_dvd_two_pow_mul (by omega) _)
  · refine not_sixteen_dvd hT ?_
    have hc : Nat.card ↥L = 604800 := (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
    rw [hc]
    norm_num

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
