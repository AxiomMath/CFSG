module

public import CFSG.RankThree.ThinCatalog.MathieuThreeRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Candidates
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal

public section

namespace CFSG.RankThree.ThinCatalog

open CFSG.Blueprint CFSG.SectionRank
open scoped commutatorElement

theorem two_le_pRank_of_square_witness {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    {x y : G} (hx : x ^ r = 1) (hy : y ^ r = 1) (hxy : x * y = y * x)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 2) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 := hr.two_le
  have hcyc : ∀ z : G, z ^ r = 1 → Nat.card (Subgroup.zpowers z) ≤ r := fun z hz => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hr.pos (orderOf_dvd_of_pow_eq_one hz)
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens hx hy hxy ?_
    fun n hn => ?_
  · rintro rfl
    have hle : Subgroup.closure ({1, y} : Set G) ≤ Subgroup.zpowers y := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    nlinarith [hcyc y hy]
  · have hle : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.zpowers x := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · rw [← hn]
        exact Subgroup.npow_mem_zpowers x n
    have := Subgroup.card_le_of_le hle
    nlinarith [hcyc x hx]

theorem two_le_pRank_of_cubic_witness {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    {x y : G} (hx : x ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hzr : ⁅x, y⁆ ^ r = 1 := by
    rw [LocalWitness.commutator_pow_eq hzx, hx, commutatorElement_one_left]
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens hx hzr hzx.symm ?_
    fun n hn => ?_
  · rintro rfl
    exact hz1 (commutatorElement_one_left y)
  ·
    have hnr : ¬ r ∣ n := by
      rintro ⟨k, rfl⟩
      apply hz1
      rw [← hn, pow_mul, hx, one_pow]
    have hcop : Nat.Coprime n r := (Nat.Prime.coprime_iff_not_dvd hr).2 hnr |>.symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
    have hxz : x = ⁅x, y⁆ ^ m := by
      rw [← hn, ← pow_mul, pow_eq_pow_mod _ (show x ^ r = 1 from hx), hm, pow_one]
    apply hz1
    have hxy : Commute x y := by
      rw [hxz]
      exact hzy.pow_left m
    exact commutatorElement_eq_one_iff_mul_comm.2 hxy.eq

theorem two_le_pRank_three_of_mulEquiv {S G : Type} [Group S] [Finite S] [Group G] [Finite G]
    (e : S ≃* G) (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) : 2 ≤ CFSG.pRank 3 S := by
  rw [pRank_eq_open_pRank_top, pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact h

theorem sqt_sporadic_three_rank_one_is_J1 (S : Type) [Group S] [Finite S] [Nontrivial S]
    (hSQT : CFSG.IsStronglyQuasithin S) (h3 : CFSG.pRank 3 S ≤ 1)
    (hrep : NativeSporadic.SporadicRep S) : Nonempty (S ≃* NativeSporadic.J1) := by
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X1.unique_SQT_sporadic_eleven_candidate_restriction hSQT hrep
  have hno : 2 ≤ CFSG.pRank 3 S → False := fun h => by omega
  have h3p : Nat.Prime 3 := Nat.prime_three
  cases s with
  | M11 => exact (hno (two_le_pRank_three_M11_sylow e)).elim
  | M12 =>
    have : Finite NativeSporadic.M12 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := M12_sylow3_cubic_witness
    exact (hno (two_le_pRank_three_of_mulEquiv (G := NativeSporadic.M12) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy))).elim
  | M22 => exact (hno (two_le_pRank_three_M22_sylow e)).elim
  | M23 => exact (hno (two_le_pRank_three_M23_sylow e)).elim
  | M24 =>
    have : Finite NativeSporadic.M24 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := M24_sylow3_cubic_witness
    exact (hno (two_le_pRank_three_of_mulEquiv (G := NativeSporadic.M24) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy))).elim
  | J1 => exact ⟨e⟩
  | J2 =>
    have : Finite NativeSporadic.J2 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := J2_sylow3_cubic_witness
    exact (hno (two_le_pRank_three_of_mulEquiv (G := NativeSporadic.J2) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy))).elim
  | J4 =>
    have : Finite NativeSporadic.J4 := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := J4_sylow3_cubic_witness
    exact (hno (two_le_pRank_three_of_mulEquiv (G := NativeSporadic.J4) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy))).elim
  | HS =>
    have : Finite NativeSporadic.HS := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, hy, hxy, hQ, -⟩ := HS_sylow3_square_witness
    exact (hno (two_le_pRank_three_of_mulEquiv (G := NativeSporadic.HS) e
      (two_le_pRank_of_square_witness h3p hx hy hxy hQ))).elim
  | He =>
    have : Finite NativeSporadic.He := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := He_sylow3_cubic_witness
    exact (hno (two_le_pRank_three_of_mulEquiv (G := NativeSporadic.He) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy))).elim
  | Ru =>
    have : Finite NativeSporadic.Ru := Finite.of_equiv S e.toEquiv
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := Ru_sylow3_cubic_witness
    exact (hno (two_le_pRank_three_of_mulEquiv (G := NativeSporadic.Ru) e
      (two_le_pRank_of_cubic_witness h3p hx hz hzx hzy))).elim
  | _ => exact absurd hs (by simp [sqtkSporadicNames])

end CFSG.RankThree.ThinCatalog
