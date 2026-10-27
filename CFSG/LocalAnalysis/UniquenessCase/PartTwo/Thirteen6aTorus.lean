module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEightLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s136a_commutator_mem {D : Data G} {K : Subgroup G} (hKM : K ≤ D.M)
    (hKn : (K.subgroupOf D.M).Normal) {Sstar : Subgroup (Bar2 K)}
    (hSstar : Sstar = ((D.T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
    (hcomm : ∀ a b : Bar2 K, a ∈ normalizer (Sstar : Set (Bar2 K)) →
      b ∈ normalizer (Sstar : Set (Bar2 K)) → a * b * a⁻¹ * b⁻¹ ∈ Sstar)
    {x y : G} (hx : x ∈ K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G))
    (hy : y ∈ K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ D.T ⊓ K := by
  have hN : ∀ {z : G} (hz : z ∈ K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨z, hz.1⟩ ∈ normalizer (Sstar : Set (Bar2 K)) := by
    intro z hz
    rw [hSstar, ← S17.subgroupOf_inf_normalizer_map_eq hKM hKn]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr hz)
  have h : (⟨x, hx.1⟩ * ⟨y, hy.1⟩ * (⟨x, hx.1⟩ : ↥K)⁻¹ * (⟨y, hy.1⟩ : ↥K)⁻¹ : ↥K) ∈
      (D.T ⊓ K).subgroupOf K := by
    rw [S17.subgroupOf_sylow_eq_comap_map hKM hKn, mem_comap]
    simp only [map_mul, map_inv]
    rw [← hSstar]
    exact hcomm _ _ (hN hx) (hN hy)
  exact mem_subgroupOf.mp h

private theorem s136a_isSylowTwoOf_bar {D : Data G} {K : Subgroup G} (hKM : K ≤ D.M)
    (hKn : (K.subgroupOf D.M).Normal) :
    CFSG.QuasithinUnique.IsSylowTwoOf
      (((D.T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) ⊤ := by
  have hS := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff (p := 2) (P := D.T ⊓ K) (K := K)
    (H := K) inf_le_right le_rfl).mpr (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      (D.sylowM.inf_of_le_normalizer hKM ((normal_subgroupOf_iff_le_normalizer hKM).mp hKn)))
  rw [subgroupOf_self] at hS
  exact CFSG.Quasithin.E1.isSylowIn_two_iff.mp
    (CFSG.Quasithin.E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective _) hS)

private theorem s136a_dvd_of_mul_gcd_eq {b s z n r : ℕ}
    (h : b * Nat.gcd 3 (2 ^ n + 1) = s * (4 ^ n - 1) * z) (hr : r.Prime) (hr3 : r ≠ 3)
    (hrn : r ∣ 2 ^ (2 * n) - 1) : r ∣ b := by
  have hcop : Nat.Coprime r (Nat.gcd 3 (2 ^ n + 1)) := hr.coprime_iff_not_dvd.mpr fun h3 =>
    ((Nat.dvd_prime Nat.prime_three).mp (h3.trans (Nat.gcd_dvd_left 3 _))).elim hr.ne_one hr3
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  refine hcop.dvd_of_dvd_mul_right ?_
  rw [h, h4]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hrn s) z

theorem s136a_exists_permutes_of_borel {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal) {Sstar : Subgroup (Bar2 K)}
    (hSstar : Sstar = ((D.T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : r ∣ Nat.card ↥(Subgroup.normalizer (Sstar : Set (Bar2 K))))
    (hcomm : ∀ a b : Bar2 K, a ∈ Subgroup.normalizer (Sstar : Set (Bar2 K)) →
      b ∈ Subgroup.normalizer (Sstar : Set (Bar2 K)) → a * b * a⁻¹ * b⁻¹ ∈ Sstar) :
    ∃ E ≤ K, IsElemAbelian r E ∧ 1 ≤ CFSG.Open.pRank r E ∧ Permutes E D.T := by
  have hMK : D.M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hTK : D.T ≤ normalizer (K : Set G) := D.sylowM.le.trans hMK
  have hSB : D.T ⊓ K ≤ K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
    le_inf inf_le_right le_normalizer
  have hTS : D.T ≤ normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
    (le_inf le_normalizer hTK).trans inf_normalizer_le_normalizer_inf
  have : ((D.T ⊓ K).subgroupOf (K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hSB).mpr inf_le_right
  have hquot : ∀ a b : ↥(K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G)) ⧸
      (D.T ⊓ K).subgroupOf (K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G)), a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have e : ((x * y)⁻¹ * (y * x) : ↥(K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G))) =
        (y⁻¹ : G) * (x⁻¹ : G) * (y⁻¹ : G)⁻¹ * (x⁻¹ : G)⁻¹ := by
      simp only [coe_mul, coe_inv]
      group
    rw [e]
    exact s136a_commutator_mem hKM hKn hSstar hcomm (inv_mem y.2) (inv_mem x.2)
  obtain ⟨E, hEB, hEel, hEcard, hperm⟩ := exists_elemAbelian_permutes_of_abelian_quotient hquot
    hSB inf_le_left ((le_inf hTK (hTS.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf)
    hTS hr hr2 (D.sylowM.inf_of_le_normalizer hKM hMK).isPGroup
  refine ⟨E, hEB.trans inf_le_left, hEel, ?_, hperm⟩
  have hrB : r ∣ Nat.card ↥(K ⊓ normalizer ((D.T ⊓ K : Subgroup G) : Set G)) := by
    rw [S17.card_inf_normalizer_eq_card_normalizer_bar_mul hKM hKn, ← hSstar]
    exact dvd_mul_of_dvd_left hrN _
  rw [← (Nat.pow_right_inj hr.one_lt).mp
    (hEcard.symm.trans (card_eq_pow_pRank_of_isElemAbelian hr hEel))]
  exact s13_one_le_pRank_of_dvd _ hr hrB

theorem s136a_exists_permutes_of_isL2 {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal) {a r : ℕ} (hshape : IsL2 (Bar2 K) a)
    (hr : r.Prime) (hr2 : r ≠ 2) (hra : r ∣ 2 ^ a - 1) :
    ∃ E ≤ K, IsElemAbelian r E ∧ 1 ≤ CFSG.Open.pRank r E ∧ Permutes E D.T := by
  have hPSL : CFSG.Quasithin.IsPSL 2 2 a ↥(⊤ : Subgroup (Bar2 K)) :=
    CFSG.Quasithin.IsPSL.of_mulEquiv Subgroup.topEquiv.symm
      ((CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (n := 2) (p := 2) (f := a)
        (by decide)).mp hshape)
  obtain ⟨-, -, hcardB, -, hcommB, -, -⟩ := CFSG.Quasithin.H13.P31X.l2BorelFacts_holds a
    (s13_two_le_of_isL2 hshape) (Bar2 K) ⊤ _ hPSL (s136a_isSylowTwoOf_bar hKM hKn)
  rw [top_inf_eq] at hcardB
  refine s136a_exists_permutes_of_borel hKM hKn rfl hr hr2 ?_
    fun x y hx hy => hcommB x ⟨mem_top x, hx⟩ y ⟨mem_top y, hy⟩
  rw [hcardB]
  exact dvd_mul_of_dvd_right hra (2 ^ a)

theorem s136a_exists_permutes_of_isSU3
    {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal) {n r : ℕ} (hshape : IsSU3 (Bar2 K) n)
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrn : r ∣ 2 ^ (2 * n) - 1) :
    ∃ E ≤ K, IsElemAbelian r E ∧ 1 ≤ CFSG.Open.pRank r E ∧ Permutes E D.T := by
  have hperf : Group.IsPerfect (↥(⊤ : Subgroup (Bar2 K))) := by
    rw [Group.IsPerfect.top_iff]
    exact Group.isPerfect_def.mpr hshape.1.1
  let eTop : ↥(⊤ : Subgroup (Bar2 K)) ≃* Bar2 K := Subgroup.topEquiv
  let eQ : (↥(⊤ : Subgroup (Bar2 K)) ⧸ Subgroup.center ↥(⊤ : Subgroup (Bar2 K))) ≃*
      (Bar2 K ⧸ Subgroup.center (Bar2 K)) :=
    QuotientGroup.congr _ _ eTop (Subgroup.map_center_eq eTop)
  have hPSU : CFSG.Quasithin.IsPSU 3 2 n
      (↥(⊤ : Subgroup (Bar2 K)) ⧸ Subgroup.center ↥(⊤ : Subgroup (Bar2 K))) :=
    CFSG.Quasithin.IsPSU.of_mulEquiv eQ.symm
      ((CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hshape.2)
  obtain ⟨-, hcardB, -, hgen, -⟩ := CFSG.Quasithin.H13.P31X.u3BorelFacts_holds n
    (s13_two_le_of_isU3 hshape.2) (Bar2 K) ⊤ _ hperf hPSU (s136a_isSylowTwoOf_bar hKM hKn)
  rw [top_inf_eq] at hcardB
  exact s136a_exists_permutes_of_borel hKM hKn rfl hr hr2
    (s136a_dvd_of_mul_gcd_eq hcardB hr hr3 hrn) fun x y hx hy =>
      CFSG.Quasithin.H13.P31X.habel_of_cyc (le_inf le_top le_normalizer) inf_le_right hgen
        x ⟨mem_top x, hx⟩ y ⟨mem_top y, hy⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
