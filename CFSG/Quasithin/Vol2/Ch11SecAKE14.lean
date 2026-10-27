module

public import CFSG.Quasithin.Vol2.Ch11SecAKE11
public import CFSG.Quasithin.Vol2.Ch11SecAKE13
public import CFSG.Quasithin.Vol2.Ch11SecAKDe
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace C10KH

theorem nonabelian_of_two_le_pRank {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p : ℕ}
    (hp : p.Prime) (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) : ∃ a b : X, a * b ≠ b * a := by
  apply nonabelian_of_simple
  intro hpr
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup X)
  have h1 : p ^ 2 ∣ Nat.card X :=
    (pow_dvd_pow p h).trans (hE ▸ Subgroup.card_subgroup_dvd_card E)
  have h2 := (Nat.prime_dvd_prime_iff_eq hp hpr).mp ((dvd_pow_self p two_ne_zero).trans h1)
  rw [← h2] at h1
  have := Nat.le_of_dvd hp.pos h1
  have := hp.two_le
  nlinarith

theorem card_center_sl3_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) ∣ 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
  have h3 : max (Fintype.card (Fin 3)) 1 = 3 := by simp
  rw [h3, ← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
  exact Subtype.ext ((mem_rootsOfUnity 3 _).mp g.2)

theorem ne_two_of_dvd_two_pow_sub_one {n p : ℕ} (hn : 1 ≤ n) (hd : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ^ n % 2 = 0 := by
    obtain ⟨g, rfl⟩ : ∃ g, n = g + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, Nat.mul_mod_left]
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega


theorem list2_pRank {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (h : List11_1_1Two X n) {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := ne_two_of_dvd_two_pow_sub_one (by omega) hd
  have hdd : p ∣ 2 ^ (2 * n) - 1 := hd.trans (by
    rw [pow_mul']
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2)
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | h | h | h | h | h | ⟨h3, h⟩
  ·
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (e.trans (specialLinearGroupEquivStatedSL 3 K).symm)]
    exact two_le_pRank_sl3 (by rw [hK]; exact hd)
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    have hpK : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hd
    by_cases h3 : p = 3
    · subst h3
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hpK
      have hu3 : (u : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
      have hu1 : (u : K) ≠ 1 := fun h1 => by
        rw [show u = 1 from Units.ext h1, orderOf_one] at hu
        norm_num at hu
      exact two_le_pRank_statedProj_sl3 hu3 hu1
    · have := CFSG.RankThree.PartOne.two_le_pRank_projectiveSL le_rfl hp h3 hpK
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at this
      rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
        (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 K)]
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    obtain ⟨g, hg⟩ := exists_orderOf_sl2 hK hdd
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact (two_le_pRank_sp4 hg).trans (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K)
      CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo)
  ·
    obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ :=
      CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel h
    obtain ⟨g, hg⟩ := exists_orderOf_sl2 hK hdd
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact two_le_pRank_cayley hg
  ·
    exact two_le_pRank_is2F4 h hp hp2 hd
  ·
    exact two_le_pRank_is3D4 h hp (Or.inl hd)
  ·
    have hn3 : 2 ^ n = (2 ^ (n / 3)) ^ 3 := by
      rw [← pow_mul, Nat.div_mul_cancel h3]
    rw [hn3, C11P9B.pow_three_sub_one _ Nat.one_le_two_pow] at hd
    exact two_le_pRank_is3D4 h hp ((Nat.Prime.dvd_mul hp).mp hd)


theorem list2_quasisimple {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (h : List11_1_1Two X n) :
    CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 := by
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega)
  have hr := list2_pRank hn h hp hd
  have of_simple : IsSimpleGroup X →
      CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 := fun hs => by
    obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (nonabelian_of_two_le_pRank hp hr)
    refine ⟨hq, ?_⟩
    rw [hZ, Subgroup.card_bot]
    exact one_dvd 3
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | h | h | h | h | h | ⟨-, h⟩
  · let e' : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
      e.trans (specialLinearGroupEquivStatedSL 3 K).symm
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl), ?_⟩
    have hc : Nat.card (Subgroup.center X) =
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) := by
      rw [← Subgroup.map_center_eq e', Subgroup.card_map_of_injective e'.injective]
    rw [hc]
    exact card_center_sl3_dvd K
  · exact of_simple (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 n h).2
  · exact of_simple (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp
      X 2 2 n h)
  · exact of_simple (CFSG.LieType.Simplicity.fam_g2_simplicity X 2 n h).2
  · exact of_simple (CFSG.LieType.Simplicity.fam_2f4_simplicity X 2 n h).2
  · exact of_simple (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 n h).2
  · exact of_simple (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 (n / 3) h).2

end C10KH

open C10KH


theorem factList2Table_holds : FactList2Table := fun _ _ _ _ hn h =>
  ⟨(list2_quasisimple hn h).1, (list2_quasisimple hn h).2, fun _ hp hd => list2_pRank hn h hp hd⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
