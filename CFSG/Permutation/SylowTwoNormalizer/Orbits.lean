module

public import CFSG.Permutation.SylowTwoNormalizer.Basic

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv MulAction Subgroup
open scoped Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] noncomputable def threeColour (s t : Set Ω) : Ω → Fin 3 := by
  classical
  exact fun x => if x ∈ s then 0 else if x ∈ t then 1 else 2

theorem threeColour_eq_zero {s t : Set Ω} {x : Ω} : threeColour s t x = 0 ↔ x ∈ s := by
  classical
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  unfold threeColour
  by_cases hx : x ∈ s
  · simp [hx]
  · by_cases hxt : x ∈ t <;> simp [hx, hxt, h1, h2]

theorem threeColour_eq_one {s t : Set Ω} (hst : Disjoint s t) {x : Ω} :
    threeColour s t x = 1 ↔ x ∈ t := by
  classical
  have h0 : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 : Fin 3) ≠ 1 := by decide
  have h : ∀ x, x ∈ s → x ∉ t := Set.disjoint_left.1 hst
  unfold threeColour
  by_cases hx : x ∈ s
  · simp [hx, h x hx]
  · by_cases hxt : x ∈ t <;> simp [hx, hxt, h0, h2]

theorem card_threeColour_zero (s t : Set Ω) :
    Nat.card {x // threeColour s t x = 0} = Nat.card s := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => threeColour_eq_zero (s := s) (t := t)))]

theorem card_threeColour_one (s t : Set Ω) (hst : Disjoint s t) :
    Nat.card {x // threeColour s t x = 1} = Nat.card t := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => threeColour_eq_one hst (s := s) (t := t)))]

theorem card_threeColour_sum (s t : Set Ω) (hst : Disjoint s t) :
    Nat.card s + Nat.card t + Nat.card {x // threeColour s t x = 2} = Nat.card Ω := by
  classical
  have hsum : Nat.card Ω = ∑ i : Fin 3, Nat.card {x // threeColour s t x = i} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (threeColour s t)), Nat.card_sigma]
  rw [hsum, Fin.sum_univ_three, card_threeColour_zero, card_threeColour_one s t hst]

theorem threeColour_apply_eq {R : Subgroup (Perm Ω)} {s t : Set Ω}
    (hRs : R ≤ stabilizer (Perm Ω) s) (hRt : R ≤ stabilizer (Perm Ω) t) :
    ∀ g ∈ R, ∀ x, threeColour s t (g x) = threeColour s t x := by
  intro g hg x
  have hgs : g • s = s := MulAction.mem_stabilizer_iff.1 (hRs hg)
  have hgt : g • t = t := MulAction.mem_stabilizer_iff.1 (hRt hg)
  have h1 : g x ∈ s ↔ x ∈ s := by
    have h := Set.smul_mem_smul_set_iff (s := s) (a := g) (x := x)
    rwa [hgs] at h
  have h2 : g x ∈ t ↔ x ∈ t := by
    have h := Set.smul_mem_smul_set_iff (s := t) (a := g) (x := x)
    rwa [hgt] at h
  unfold threeColour
  rw [h1, h2]

theorem not_pow_dvd_pow_padicValNat {m c n : ℕ} (hm : m ≠ 0) (hn : n = 2 * m + c) :
    ¬ 2 ^ padicValNat 2 n.factorial ∣
      2 ^ (2 * padicValNat 2 m.factorial + padicValNat 2 c.factorial) := by
  intro hdvd
  have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).1 hdvd
  have h1 := two_mul_padicValNat_two_factorial_lt hm
  have h2 := padicValNat_two_factorial_add_le (2 * m) c
  rw [hn] at hle
  omega

theorem two_dvd_index_of_disjoint {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R) {s t : Set Ω}
    (hst : Disjoint s t) (hs : s.Nonempty) (hcard : Nat.card s = Nat.card t)
    (hRs : R ≤ stabilizer (Perm Ω) s) (hRt : R ≤ stabilizer (Perm Ω) t) : 2 ∣ R.index := by
  classical
  by_contra hRi
  have hm0 : Nat.card s ≠ 0 := Nat.card_ne_zero.2 ⟨hs.to_subtype, inferInstance⟩
  have hsum : Nat.card s + Nat.card s + Nat.card {x // threeColour s t x = 2} = Nat.card Ω := by
    have h := card_threeColour_sum s t hst
    rwa [← hcard] at h
  have hf := threeColour_apply_eq hRs hRt
  have hyoung := card_dvd_of_forall_apply_eq (threeColour s t) hR hf
  rw [card_eq_of_not_two_dvd_index hR hRi] at hyoung
  rw [Fin.sum_univ_three, card_threeColour_zero, card_threeColour_one s t hst,
    ← hcard] at hyoung
  have hdvd : 2 ^ padicValNat 2 (Nat.card Ω).factorial ∣
      2 ^ (2 * padicValNat 2 (Nat.card s).factorial +
        padicValNat 2 (Nat.card {x // threeColour s t x = 2}).factorial) := by
    rw [show 2 * padicValNat 2 (Nat.card s).factorial +
        padicValNat 2 (Nat.card {x // threeColour s t x = 2}).factorial
        = padicValNat 2 (Nat.card s).factorial + padicValNat 2 (Nat.card s).factorial +
          padicValNat 2 (Nat.card {x // threeColour s t x = 2}).factorial by omega]
    exact hyoung
  exact not_pow_dvd_pow_padicValNat hm0 (by omega) hdvd

theorem two_dvd_relIndex_of_disjoint (h4 : 4 ≤ Nat.card Ω) {R : Subgroup (Perm Ω)}
    (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R) {s t : Set Ω} (hst : Disjoint s t)
    (hs : s.Nonempty) (hcard : Nat.card s = Nat.card t) (hRs : R ≤ stabilizer (Perm Ω) s)
    (hRt : R ≤ stabilizer (Perm Ω) t) : 2 ∣ R.relIndex (alternatingGroup Ω) := by
  classical
  by_contra hRi
  have h2 : 2 ≤ Nat.card Ω := by omega
  have hm0 : Nat.card s ≠ 0 := Nat.card_ne_zero.2 ⟨hs.to_subtype, inferInstance⟩
  have hsum : Nat.card s + Nat.card s + Nat.card {x // threeColour s t x = 2} = Nat.card Ω := by
    have h := card_threeColour_sum s t hst
    rwa [← hcard] at h
  have hi : ∃ i : Fin 3, 2 ≤ Nat.card {x // threeColour s t x = i} := by
    by_cases hm2 : 2 ≤ Nat.card s
    · exact ⟨0, by rwa [card_threeColour_zero]⟩
    · refine ⟨2, by omega⟩
  have hf := threeColour_apply_eq hRs hRt
  have hyoung := two_mul_card_dvd_of_forall_apply_eq (threeColour s t) hRA hR hf hi
  rw [two_mul_card_eq_of_not_two_dvd_relIndex h2 hRA hR hRi] at hyoung
  rw [Fin.sum_univ_three, card_threeColour_zero, card_threeColour_one s t hst,
    ← hcard] at hyoung
  have hdvd : 2 ^ padicValNat 2 (Nat.card Ω).factorial ∣
      2 ^ (2 * padicValNat 2 (Nat.card s).factorial +
        padicValNat 2 (Nat.card {x // threeColour s t x = 2}).factorial) := by
    rw [show 2 * padicValNat 2 (Nat.card s).factorial +
        padicValNat 2 (Nat.card {x // threeColour s t x = 2}).factorial
        = padicValNat 2 (Nat.card s).factorial + padicValNat 2 (Nat.card s).factorial +
          padicValNat 2 (Nat.card {x // threeColour s t x = 2}).factorial by omega]
    exact hyoung
  exact not_pow_dvd_pow_padicValNat hm0 (by omega) hdvd

theorem le_stabilizer_orbit (R : Subgroup (Perm Ω)) (x : Ω) :
    R ≤ stabilizer (Perm Ω) (MulAction.orbit R x) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  have h := MulAction.smul_orbit (⟨g, hg⟩ : R) x
  rwa [Subgroup.smul_def] at h

theorem smul_orbit_eq_orbit_of_mem_normalizer {G α : Type*} [Group G] [MulAction G α]
    {R : Subgroup G} {σ : G} (hσR : σ ∈ normalizer (R : Set G)) (x : α) :
    σ • MulAction.orbit R x = MulAction.orbit R (σ • x) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.1 hy
    obtain ⟨r, hr⟩ := MulAction.mem_orbit_iff.1 hz
    have hconj : σ * (r : G) * σ⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.1 hσR (r : G)).1 r.2
    refine MulAction.mem_orbit_iff.2 ⟨⟨σ * (r : G) * σ⁻¹, hconj⟩, ?_⟩
    rw [Subgroup.smul_def]
    calc
      (σ * (r : G) * σ⁻¹) • (σ • x) = σ • ((r : G) • x) := by
        rw [mul_smul, mul_smul, inv_smul_smul]
      _ = σ • (r • x) := by rw [Subgroup.smul_def]
      _ = σ • z := by rw [hr]
      _ = y := hzy
  · intro hy
    obtain ⟨r, hr⟩ := MulAction.mem_orbit_iff.1 hy
    have hconj : σ⁻¹ * (r : G) * σ ∈ R := by
      have hσinv : σ⁻¹ ∈ normalizer (R : Set G) := Subgroup.inv_mem _ hσR
      have h := (Subgroup.mem_normalizer_iff.1 hσinv (r : G)).1 r.2
      simpa using h
    refine Set.mem_smul_set.2 ⟨(⟨σ⁻¹ * (r : G) * σ, hconj⟩ : R) • x, ?_, ?_⟩
    · exact MulAction.mem_orbit_iff.2 ⟨⟨σ⁻¹ * (r : G) * σ, hconj⟩, rfl⟩
    · rw [Subgroup.smul_def]
      have h : σ * ((⟨σ⁻¹ * (r : G) * σ, hconj⟩ : R) : G) = (r : G) * σ := by
        simp only [Subgroup.coe_mk]
        group
      rw [← mul_smul, h, mul_smul, ← Subgroup.smul_def]
      exact hr

theorem mem_stabilizer_orbit {R : Subgroup (Perm Ω)} {σ : Perm Ω}
    (hσR : σ ∈ normalizer (R : Set (Perm Ω))) {x : Ω} (hx : σ x ∈ MulAction.orbit R x) :
    σ ∈ stabilizer (Perm Ω) (MulAction.orbit R x) := by
  rw [MulAction.mem_stabilizer_iff, smul_orbit_eq_orbit_of_mem_normalizer hσR x]
  exact MulAction.orbit_eq_iff.2 hx

theorem apply_mem_orbit {R : Subgroup (Perm Ω)} (hR : IsPGroup 2 R) (hRi : ¬ 2 ∣ R.index)
    {σ : Perm Ω} (hσR : σ ∈ normalizer (R : Set (Perm Ω))) (x : Ω) :
    σ x ∈ MulAction.orbit R x := by
  classical
  by_contra hx
  have hO : (MulAction.orbit R x).Nonempty := ⟨x, MulAction.mem_orbit_self x⟩
  have hdisj : Disjoint (MulAction.orbit R x) (σ • MulAction.orbit R x) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    rw [smul_orbit_eq_orbit_of_mem_normalizer hσR x] at hy'
    have h1 : MulAction.orbit R y = MulAction.orbit R x := MulAction.orbit_eq_iff.2 hy
    have h2 : MulAction.orbit R y = MulAction.orbit R (σ • x) := MulAction.orbit_eq_iff.2 hy'
    exact hx (MulAction.orbit_eq_iff.1 (h2.symm.trans h1))
  have hcard : Nat.card ↥(MulAction.orbit R x) = Nat.card ↥(σ • MulAction.orbit R x) := by
    rw [← Set.image_smul]
    exact (Nat.card_image_of_injective (Equiv.injective σ) (MulAction.orbit R x)).symm
  have hRs : R ≤ stabilizer (Perm Ω) (MulAction.orbit R x) := le_stabilizer_orbit R x
  have hRt : R ≤ stabilizer (Perm Ω) (σ • MulAction.orbit R x) := by
    rw [smul_orbit_eq_orbit_of_mem_normalizer hσR x]
    exact le_stabilizer_orbit R (σ • x)
  exact hRi (two_dvd_index_of_disjoint hR hdisj hO hcard hRs hRt)

theorem apply_mem_orbit_of_le_alternatingGroup (h4 : 4 ≤ Nat.card Ω) {R : Subgroup (Perm Ω)}
    (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.relIndex (alternatingGroup Ω)) {σ : Perm Ω}
    (hσR : σ ∈ normalizer (R : Set (Perm Ω))) (x : Ω) : σ x ∈ MulAction.orbit R x := by
  classical
  by_contra hx
  have hO : (MulAction.orbit R x).Nonempty := ⟨x, MulAction.mem_orbit_self x⟩
  have hdisj : Disjoint (MulAction.orbit R x) (σ • MulAction.orbit R x) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    rw [smul_orbit_eq_orbit_of_mem_normalizer hσR x] at hy'
    have h1 : MulAction.orbit R y = MulAction.orbit R x := MulAction.orbit_eq_iff.2 hy
    have h2 : MulAction.orbit R y = MulAction.orbit R (σ • x) := MulAction.orbit_eq_iff.2 hy'
    exact hx (MulAction.orbit_eq_iff.1 (h2.symm.trans h1))
  have hcard : Nat.card ↥(MulAction.orbit R x) = Nat.card ↥(σ • MulAction.orbit R x) := by
    rw [← Set.image_smul]
    exact (Nat.card_image_of_injective (Equiv.injective σ) (MulAction.orbit R x)).symm
  have hRs : R ≤ stabilizer (Perm Ω) (MulAction.orbit R x) := le_stabilizer_orbit R x
  have hRt : R ≤ stabilizer (Perm Ω) (σ • MulAction.orbit R x) := by
    rw [smul_orbit_eq_orbit_of_mem_normalizer hσR x]
    exact le_stabilizer_orbit R (σ • x)
  exact hRi (two_dvd_relIndex_of_disjoint h4 hRA hR hdisj hO hcard hRs hRt)

end CFSG.Permutation.SylowTwoNormalizer
