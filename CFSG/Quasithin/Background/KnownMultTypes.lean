module

public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.Quasithin.Background.KnownMultL2
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.SectionRank.SporadicCover

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem psl_two_sylow_isCyclic_even {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (R : Sylow r (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :
    IsCyclic (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) := by
  by_cases h7 : 7 ≤ Nat.card K
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK h7 r hr2 ?_ R
    rw [hK]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hr.out Nat.prime_two).2 hr2)
  · have hn2 : n = 2 := by
      by_contra hne
      have h3 : 3 ≤ n := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
      omega
    subst hn2
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have hdvd : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ∣
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Subgroup.card_quotient_dvd_card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    rw [CFSG.GorensteinWalter.sl2_card_formula K, hK4] at hdvd
    refine CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd (fun h => ?_) R
    have h60 : r ^ 2 ∣ 60 := h.trans (by simpa using hdvd)
    have hle : r ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h60
    have hr7 : r ≤ 7 := by nlinarith
    have hr' := hr.out
    interval_cases r <;> first | omega | (exfalso; norm_num at hr')

theorem isPGroup_two_of_mulEquiv_stated_psl_two_even {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X) {K : Type}
    [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : X ⧸ Z ≃* StatedProj (StatedSL 2 K)) : IsPGroup 2 Z :=
  isPGroup_two_of_mulEquiv_cyclic_odd_sylow Z hZ
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
    fun _ _ hr2 _ Q => psl_two_sylow_isCyclic_even hn hK hr2 Q

theorem isPGroup_two_of_isSz {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X) {n : ℕ} (h : IsSz n (X ⧸ Z)) :
    IsPGroup 2 Z := by
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel h
  exact isPGroup_two_of_mulEquiv_cyclic_odd_sylow Z hZ e
    fun _ _ hr2 _ Q => CFSG.SectionRank.suzuki_sylow_isCyclic a ha hr2 Q

theorem isPGroup_two_of_isSporadic_J1 {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X)
    (hJ1 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J1) = 175560)
    (h : IsSporadic .J1 (X ⧸ Z)) : IsPGroup 2 Z := by
  obtain ⟨e⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J1) := Finite.of_equiv _ e.toEquiv
  refine isPGroup_two_of_mulEquiv_cyclic_odd_sylow Z hZ e fun r hr hr2 _ Q => ?_
  refine CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd ?_ Q
  rw [hJ1]
  by_cases hr3 : r = 3
  · subst hr3
    decide
  · exact (CFSG.SectionRank.small_sporadic_order_conditions (n := 175560) (by norm_num)).2
      r hr hr2 hr3

theorem mult2Fact_of_card_J1 (hJ1 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J1) = 175560) :
    Mult2Fact := by
  intro X _ _ hX hT
  have : Group.IsPerfect X := hX.1
  rcases hT with ⟨n, hn⟩ | ⟨n, hn⟩ | hn | ⟨p, e, hp, hp3, he1, he2, hn⟩
  · obtain ⟨⟨-, hn1, -, hne, -⟩, K, _, _, hK, ⟨eq⟩⟩ := hn
    have hn2 : 2 ≤ n := by
      by_contra h
      have : n = 1 := by omega
      subst this
      exact hne (by simp)
    exact isPGroup_two_of_mulEquiv_stated_psl_two_even (Subgroup.center X) le_rfl hn2 hK eq
  · exact isPGroup_two_of_isSz (Subgroup.center X) le_rfl hn
  · exact isPGroup_two_of_isSporadic_J1 (Subgroup.center X) le_rfl hJ1 hn
  · obtain ⟨-, K, _, _, hK, ⟨eq⟩⟩ := hn
    have : Fact p.Prime := ⟨hp⟩
    refine isPGroup_two_of_mulEquiv_stated_psl_two_odd (Subgroup.center X) le_rfl
      (by omega) hK ?_ eq
    intro h9
    have := (CFSG.SectionRank.OddCover.eq_three_of_pow_eq_nine hp h9).1
    omega

theorem mult2Fact
    : Mult2Fact := mult2Fact_of_card_J1 CFSG.Sporadic.J1.card_J1

end CFSG.Quasithin
