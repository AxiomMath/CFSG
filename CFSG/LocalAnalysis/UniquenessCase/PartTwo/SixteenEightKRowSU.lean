module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSU4Kernel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSU4Z
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSU4Zero
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSUThree
import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_not_isSolvable_of_isQuasisimple {Q : Type} [Group Q]
    (hq : CFSG.Open.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  intro hs
  haveI := hs
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hq.2.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
  rw [hq.1] at h
  exact lt_irrefl _ h

private theorem s16k_statedSU_one_eq_bot (q : ℕ) (K : Type) [Field K] :
    StatedSU 1 q K = ⊥ := by
  unfold StatedSU
  rw [eq_bot_iff, Subgroup.closure_le]
  intro A hA
  rw [SetLike.mem_coe, Subgroup.mem_bot]
  apply Units.ext
  have hmat : (A : Matrix (Fin 1) (Fin 1) K) = 1 := by
    have hdet : (A : Matrix (Fin 1) (Fin 1) K) 0 0 = 1 := by
      simpa [Matrix.det_fin_one] using hA.1
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simpa using hdet
  exact hmat

private theorem s16k_isSolvable_statedSU_of_le_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {n : ℕ} (hn : n ≤ 3) :
    Group.IsSolvable (StatedSU n (2 ^ 1) K) := by
  interval_cases n
  · infer_instance
  · rw [s16k_statedSU_one_eq_bot]
    infer_instance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 :=
      CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) (by rw [hK]; norm_num)
    have hcard : Nat.card (StatedSU 2 (2 ^ 1) K) = 6 := by
      have h := CFSG.RankThree.SubgroupLists.card_statedSU_two (K := K) (r := 2) (f := 1)
        (by rw [hK]; norm_num)
      norm_num at h ⊢
      exact h
    haveI : Fintype (StatedSU 2 (2 ^ 1) K) := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (G := ↥(StatedSU 2 (2 ^ 1) K)) (p := 2) (q := 3) (a := 1) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  · exact CFSG.Quasithin.isSolvable_statedSU_one (F := K) (by rw [hK]; norm_num)

theorem s16k_false_of_natSUn (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n : ℕ}
    (hSU : IsSUn ↥(lBar V₀ V hV L) n 1)
    (hN : NatSUn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n 1) : False := by
  have hN' := hN
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have hn3 : n ≤ 3 := by omega
    obtain ⟨K', hF', hFin', hK', ⟨e⟩⟩ := hSU
    letI := hF'
    letI := hFin'
    have hK'4 : Nat.card K' = 4 := by rw [hK']; norm_num
    haveI : Group.IsSolvable ↥(StatedSU n (2 ^ 1) K') :=
      s16k_isSolvable_statedSU_of_le_three hK'4 hn3
    haveI : Group.IsSolvable ↥(lBar V₀ V hV L) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (s16k_not_isSolvable_of_isQuasisimple h.quasi) inferInstance
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨K, hF, hFin, hK, hR⟩ := hN
  letI := hF
  letI := hFin
  simp only [pow_one] at hK hR
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 := h.three_le_pRank hpσ
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  rcases eq_or_ne p 3 with hp3 | hp3
  · subst hp3
    by_cases hn5 : 5 ≤ n
    · exact h.false_of_fixNc hR hpσ (s16k_fixNc_statedSU_three hK4 hn5)
    · have hn_eq : n = 4 := by omega
      subst hn_eq
      by_cases hrk : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 3
      · exact s16k_false_of_su4_kernel h hGA hSU hN' hpσ hrk
      · have hrk4 : 4 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) :=
          Nat.succ_le_of_lt (Nat.lt_of_not_le hrk)
        by_cases hZ : fixV (lBar V₀ V hV L) = ⊥
        · exact s16k_false_of_su4_zero h hGA hSU hN' hpσ hrk4 hZ
        · exact s16k_false_of_su4_z h hGA hSU hN' hpσ hrk4 hZ
  · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    exact h.false_of_fixNc hR hpσ
      (s16k_fixNc_statedSU_of_pRank hK4 hn4 hp hp5 ρ hρ hρN hrk3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
