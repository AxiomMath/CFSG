module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Kernel
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16e_d3_eq_seven_or_eq_three_of_cube_dvd {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hr : r ≤ 5) (h : q ^ 3 ∣ 7 ^ (r + 1) * 3 * Nat.factorial (r + 1)) :
    q = 7 ∨ (q = 3 ∧ r = 5) := by
  have hq3 : 3 ≤ q := by
    by_contra hle
    have hlt : q < 3 := not_le.1 hle
    interval_cases q
    · exact Nat.not_prime_zero hq
    · exact Nat.not_prime_one hq
    · exact hq2 rfl
  have hdvd : q ∣ 7 ^ (r + 1) * 3 * Nat.factorial (r + 1) :=
    (dvd_pow_self q (n := 3) (by norm_num)).trans h
  have hqmem : q = 7 ∨ q = 3 ∨ q = 5 := by
    rcases hq.dvd_mul.1 hdvd with h1 | h1
    · rcases hq.dvd_mul.1 h1 with h2 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).1
          (hq.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).1 h2))
    · have hle : q ≤ r + 1 := (hq.dvd_factorial).1 h1
      have hq6 : q ≤ 6 := by omega
      interval_cases q
      · exact Or.inr (Or.inl rfl)
      · exact absurd hq (by decide)
      · exact Or.inr (Or.inr rfl)
      · exact absurd hq (by decide)
  rcases hqmem with rfl | rfl | rfl
  · exact Or.inl rfl
  · right
    refine ⟨rfl, ?_⟩
    interval_cases r
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · rfl
  · exfalso
    interval_cases r <;> norm_num at h

variable {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)} {r : ℕ}
  {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}

private theorem s16e_d3_isElemAbelian_of_rank {X : Type*} [Group X] {p n : ℕ} {E : Subgroup X}
    (hE : IsElemAbelianOfRank p n ↥E) : IsElemAbelian p E := by
  obtain ⟨e⟩ := hE
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun a ha => ?_⟩
  · have h1 : e a * e b = e b * e a := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact e.injective h1
  · have h1 : e (⟨a, ha⟩ ^ p) = 1 := by
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      simp
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))

private theorem s16e_d3_normal_subgroupOf {W : Type*} [CommGroup W]
    {A L : Subgroup (MulAut W)} (h : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) :
    (L.subgroupOf A).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg := h g g.2
  have hmem : (MulAut.conj (g : MulAut W)).toMonoidHom (n : MulAut W) ∈
      L.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hn
  rw [hg] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem s16e_d3_eq_of_three_le_pRank (h : s16e_d3_Ctx A L r Δ σ) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h3 : 3 ≤ CFSG.Open.pRank q A) : q = 7 ∨ (q = 3 ∧ r = 5) := by
  obtain ⟨E, -, hEcard⟩ := exists_isElemAbelian_subgroupOf_of_le_pRank (M := A) hq h3
  have hdvd : q ^ 3 ∣ Nat.card ↥A := by
    rw [← hEcard]
    exact Subgroup.card_subgroup_dvd_card E
  exact s16e_d3_eq_seven_or_eq_three_of_cube_dvd hq hq2 h.le_five
    (hdvd.trans (s16e_d3_card_dvd_seven_pow_mul_three_mul_factorial h))

theorem s16e_d3_three_le_pRank_seven (h : s16e_d3_Ctx A L r Δ σ) (hr : 3 ≤ r) :
    3 ≤ CFSG.Open.pRank 7 A := by
  have hE : IsElemAbelian 7 L := s16e_d3_isElemAbelian_of_rank h.elem
  have hcard : Nat.card ↥L = 7 ^ r :=
    CFSG.Quasithin.A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 7) h.elem
  have hle := CFSG.SectionRank.le_pRank (p := 7) (H := A) (E := L) (by norm_num) h.le hE hcard
  omega

theorem s16e_d3_le_pCoreOf (h : s16e_d3_Ctx A L r Δ σ) : L ≤ pCoreOf 7 A := by
  have hcard : Nat.card ↥L = 7 ^ r :=
    CFSG.Quasithin.A38.card_eq_of_isElemAbelianOfRank (by norm_num : Nat.Prime 7) h.elem
  have hLp : IsPGroup 7 ↥L := IsPGroup.of_card (n := r) hcard
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 7 L A h.le
    (s16e_d3_normal_subgroupOf h.normal) hLp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
