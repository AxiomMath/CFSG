module

public import CFSG.RankThree.PartOne.KF.F122Glue
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank
  (StatedLieAdmissible StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem psl_two_aut_inner {T : Type} [Group T] [Finite T] {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hC : StatedClassicalModel T .PSL n 2 1) {α : MulAut T} (hαp : α ^ p = 1) :
    α ∈ innerAut T := by
  by_contra hαinn
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hadm := hC.1
  have hn3 : 3 ≤ n := by
    have h2 : 2 ≤ n := hadm.2.2.1
    by_contra hlt
    have hn2 : n = 2 := by omega
    exact hadm.2.2.2.1 (by rw [hn2]; norm_num)
  have hf : 1 ≤ 1 := le_rfl
  have hα1 : α ≠ 1 := fun h => hαinn (h ▸ Subgroup.one_mem _)
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hdiag : ¬ p ∣ Nat.gcd n (2 ^ 1 - 1) := by
    intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_right _ _))
    omega
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have hdiagK : ¬ p ∣ Nat.gcd n (Nat.card K - 1) := by rwa [hK]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
  let e : T ≃* projectiveSL n K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  have : Finite (projectiveSL n K) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (projectiveSL n K) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'ord : orderOf (MulAut.congr e α) = p := (orderOf_congr e α).trans hord
  have hα'p : MulAut.congr e α ^ p = 1 := by
    have := pow_orderOf_eq_one (MulAut.congr e α)
    rwa [hα'ord] at this
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn3
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hE : MulAut.congr e α ∈ semilinearAutGroup n K := by
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2' : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2'
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ linearAutGroup n K := by
    intro hD
    exact hα'inn (OutStructure.linear_D2 hp hn3 hdiagK _ hD 1
      (by rw [pow_one, hα'p]; exact Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two hf
      hn3 hK
  obtain ⟨hpf, -⟩ := hdesc p hp hp2 _ hE hD hα'ord
  exact absurd (Nat.le_of_dvd (by norm_num) hpf) (by omega)

theorem kf122PSLTwo_holds : KF122PSLTwo := by
  intro G _ _ p L hp hp5 hq hL x hx hxp
  obtain ⟨n, hn⟩ := hL
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨x, hx⟩
  have hαp : α ^ p = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) ^ p = 1 :=
      Subtype.ext (by simp [hxp])
    rw [this, map_one]
  obtain ⟨l, hl⟩ := psl_two_aut_inner hp hp5 hn hαp
  have hcomm : ∀ y : L, ((l : G) * (y : G) * (l : G)⁻¹) = x * (y : G) * x⁻¹ := by
    intro y
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ y : L) : G)) hl
    simpa [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using h1
  have hz : (l : G)⁻¹ * x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := hcomm ⟨y, hy⟩
    calc y * ((l : G)⁻¹ * x) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * x := by group
      _ = (l : G)⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
      _ = ((l : G)⁻¹ * x) * y := by group
  have : x = (l : G) * ((l : G)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup l.2 hz

end CFSG.RankThree.PartOne
