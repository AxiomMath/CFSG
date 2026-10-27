module

public import CFSG.RankThree.PartOne.KF.ClsCover
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.RankThree.PartOne.KF.ClsSUQuot
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial

namespace KFU

theorem card_hopfMultiplier_psu
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {n f : ℕ} (hn : 7 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Group.IsPerfect (StatedProj (StatedSU n (2 ^ f) K)) ∧
      Nat.card (hopfMultiplier (StatedProj (StatedSU n (2 ^ f) K))) =
        Nat.gcd n (2 ^ f + 1) := by
  have hadm : StatedLieAdmissible .PSU n 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_⟩
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hcl : StatedClassicalModel (StatedProj (StatedSU n (2 ^ f) K)) .PSU n 2 f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hm : Models.LieModel (StatedProj (StatedSU n (2 ^ f) K)) .PSU n 2 f :=
    ⟨hadm, Or.inl hcl⟩
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  refine ⟨hperf, ?_⟩
  rw [hcard]
  have hgen : Blueprint.Multiplier.genericOrders .PSU n 2 f = (Nat.gcd n (2 ^ f + 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSU n 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]

theorem exists_cover_psu
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {n f : ℕ} (hn : 7 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {L : Type} [Group L] [Finite L] (hLp : Group.IsPerfect L)
    (p : L →* StatedProj (StatedSU n (2 ^ f) K)) (hp : Function.Surjective p)
    (hpc : p.ker ≤ Subgroup.center L) :
    ∃ ρ : StatedSU n (2 ^ f) K →* L, Function.Surjective ρ ∧
      ρ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) := by
  obtain ⟨hperf, hcardM⟩ := card_hopfMultiplier_psu hGA hn hf hK
  have hSU : Group.IsPerfect (StatedSU n (2 ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := f) hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  set π : StatedSU n (2 ^ f) K →* StatedProj (StatedSU n (2 ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) :=
    QuotientGroup.ker_mk' _
  have hπc : π.ker ≤ Subgroup.center (StatedSU n (2 ^ f) K) := by
    rw [hπk]
    exact CFSG.RankThree.PartTwo.Census.statedScalars_subgroupOf_le_center _
  have hcard : Nat.card (hopfMultiplier (StatedProj (StatedSU n (2 ^ f) K))) =
      Nat.card π.ker := by
    rw [hcardM, hπk, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by omega)).2.2]
  obtain ⟨ρ, hρ, hρs⟩ := exists_hom_of_card_multiplier_eq hperf hSU π hπs hπc hcard p hp hpc
  refine ⟨ρ, hρs hLp, fun x hx => ?_⟩
  have h1 : π x = 1 := by
    rw [← hρ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  rw [← hπk]
  exact h1

end KFU

open KFU in
theorem psu_large_false {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Table123Generic p L A₀ F) {n f : ℕ} (hn : 7 ≤ n)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) : False := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hf1 : 1 ≤ f := hadm.2.1
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) := h.coprime_center
  have hq := isCentralPQuot_center e hcop
  have hLp : Group.IsPerfect ↥L := h.quasisimple.1
  obtain ⟨ρ, hρs, hρk⟩ := exists_cover_psu hGA hn hf1 hK hLp _ hq.surjective hq.central
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
      (by rw [Fintype.card_eq_nat_card, hK, pow_mul])
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf1
  obtain ⟨r, hr, hr2, hrq⟩ := CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf1
  have h4 := CFSG.RankThree.PartOne.KFU.le_localRank_of_surjective_statedSU_torus (k := 3) hU hr
    hrq (by omega) (Or.inl (by omega)) ρ hρs hρk
  have h3 := (CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans h.evenRank_le
  omega

end CFSG.RankThree.PartOne
