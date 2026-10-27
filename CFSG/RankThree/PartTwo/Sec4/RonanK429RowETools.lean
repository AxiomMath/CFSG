module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open scoped Matrix

section Krylov

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem mulVec_pow_mulVec_of_commute {X y : Matrix ι ι R} (h : X * y = y * X) (k : ℕ)
    (v : ι → R) : X *ᵥ (y ^ k *ᵥ v) = y ^ k *ᵥ (X *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (Commute.pow_right h k).eq]

theorem eq_zero_of_commute_of_mulVec_eq_zero {y Z kr kr' : Matrix ι ι R} {v : ι → R}
    {e : ι → ℕ} (hkr : ∀ i j, kr i j = (y ^ e j *ᵥ v) i) (hinv : kr' * kr = 1)
    (hZ : Z * y = y * Z) (hZv : Z *ᵥ v = 0) : Z = 0 := by
  have hZk : Z * kr = 0 := by
    ext i j
    have hcol : (fun k => kr k j) = y ^ e j *ᵥ v := funext fun k => hkr k j
    have h1 : (Z * kr) i j = (Z *ᵥ (fun k => kr k j)) i := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, hcol, mulVec_pow_mulVec_of_commute hZ, hZv, Matrix.mulVec_zero]
    rfl
  have hkr1 : kr * kr' = 1 := mul_eq_one_comm.mp hinv
  rw [← Matrix.mul_one Z, ← hkr1, ← Matrix.mul_assoc, hZk, Matrix.zero_mul]

theorem eq_of_commute_of_mulVec_eq {y X Y kr kr' : Matrix ι ι R} {v : ι → R} {e : ι → ℕ}
    (hkr : ∀ i j, kr i j = (y ^ e j *ᵥ v) i) (hinv : kr' * kr = 1)
    (hX : X * y = y * X) (hY : Y * y = y * Y) (hv : X *ᵥ v = Y *ᵥ v) : X = Y := by
  have h := eq_zero_of_commute_of_mulVec_eq_zero (Z := X - Y) hkr hinv
    (by rw [Matrix.sub_mul, Matrix.mul_sub, hX, hY]) (by rw [Matrix.sub_mulVec, hv, sub_self])
  exact sub_eq_zero.mp h

@[expose] def krylovPoly (y kr' : Matrix ι ι R) (e : ι → ℕ) (w : ι → R) : Matrix ι ι R :=
  ∑ j, (kr' *ᵥ w) j • y ^ e j

theorem krylovPoly_commute (y kr' : Matrix ι ι R) (e : ι → ℕ) (w : ι → R) :
    krylovPoly y kr' e w * y = y * krylovPoly y kr' e w := by
  simp only [krylovPoly, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    ← pow_succ, ← pow_succ']

theorem krylovPoly_mulVec {y kr kr' : Matrix ι ι R} {v : ι → R} {e : ι → ℕ}
    (hkr : ∀ i j, kr i j = (y ^ e j *ᵥ v) i) (hinv : kr' * kr = 1) (w : ι → R) :
    krylovPoly y kr' e w *ᵥ v = w := by
  have hkr1 : kr * kr' = 1 := mul_eq_one_comm.mp hinv
  have h : krylovPoly y kr' e w *ᵥ v = kr *ᵥ (kr' *ᵥ w) := by
    rw [krylovPoly, Matrix.sum_mulVec]
    ext i
    rw [Finset.sum_apply]
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hkr i j, mul_comm]
  rw [h, Matrix.mulVec_mulVec, hkr1, Matrix.one_mulVec]

theorem eq_krylovPoly_of_commute {y X kr kr' : Matrix ι ι R} {v : ι → R} {e : ι → ℕ}
    (hkr : ∀ i j, kr i j = (y ^ e j *ᵥ v) i) (hinv : kr' * kr = 1) (hX : X * y = y * X) :
    X = krylovPoly y kr' e (X *ᵥ v) :=
  eq_of_commute_of_mulVec_eq hkr hinv hX (krylovPoly_commute y kr' e _)
    (krylovPoly_mulVec hkr hinv _).symm

end Krylov

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem not_dvd_card_centralizer_of_sylow {r : ℕ} (hr : r.Prime) {y : G} (hy : orderOf y = r)
    (hr2 : ¬ r ^ 2 ∣ Nat.card G) (hC : ∀ s : G, s * y = y * s → s ^ 3 = 1 → s = 1) {s : G}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) : ¬ r ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  intro hdvd
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({s} : Set G)) r hdvd
  have hgs : (g : G) * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hg' : orderOf (g : G) = r := by rw [Subgroup.orderOf_coe, hg]
  have hrG : r ∣ Nat.card G := by
    rw [← hy]
    exact orderOf_dvd_natCard y
  have hsyl : ∀ z : G, orderOf z = r →
      IsPGroup r (Subgroup.zpowers z) ∧ ¬ r ∣ (Subgroup.zpowers z).index := by
    intro z hz
    refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]), fun hi => ?_⟩
    have hmul := Subgroup.card_mul_index (Subgroup.zpowers z)
    rw [Nat.card_zpowers, hz] at hmul
    apply hr2
    rw [← hmul, pow_two]
    exact Nat.mul_dvd_mul_left r hi
  obtain ⟨hPy, hPyi⟩ := hsyl y hy
  obtain ⟨hPg, hPgi⟩ := hsyl _ hg'
  let SY : Sylow r G := hPy.toSylow hPyi
  let SG : Sylow r G := hPg.toSylow hPgi
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G SY SG
  have hmap : Subgroup.zpowers (g : G) =
      (Subgroup.zpowers y).map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • SY : Sylow r G) : Subgroup G) = (SG : Subgroup G) := by rw [hx]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1.symm
  have hgmem : (g : G) ∈ (Subgroup.zpowers y).map (MulAut.conj x).toMonoidHom :=
    hmap ▸ Subgroup.mem_zpowers _
  obtain ⟨u, hu, hgu⟩ := hgmem
  set s' : G := x⁻¹ * s * x with hs'
  have hgu' : (g : G) = x * u * x⁻¹ := by
    rw [← hgu]
    rfl
  have hus : u * s' = s' * u := by
    have h := hgs
    rw [hgu'] at h
    calc u * s' = x⁻¹ * ((x * u * x⁻¹) * s) * x := by rw [hs']; group
      _ = x⁻¹ * (s * (x * u * x⁻¹)) * x := by rw [h]
      _ = s' * u := by rw [hs']; group
  have hu_ord : orderOf u = r := by
    have : orderOf (g : G) = orderOf u := by
      rw [hgu']
      exact orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective u
    rw [← this, hg']
  have hyu : y ∈ Subgroup.zpowers u := by
    have hle : Subgroup.zpowers u ≤ Subgroup.zpowers y :=
      (Subgroup.zpowers_le).mpr hu
    have hc : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers u) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hy, hu_ord]
    rw [Subgroup.eq_of_le_of_card_ge hle hc]
    exact Subgroup.mem_zpowers y
  obtain ⟨k, hk⟩ := hyu
  have hk' : u ^ k = y := hk
  have hys : s' * y = y * s' := by
    rw [← hk']
    exact (Commute.zpow_left hus k).eq.symm
  have hs'3 : s' ^ 3 = 1 := by
    rw [hs']
    have : (x⁻¹ * s * x) ^ 3 = x⁻¹ * s ^ 3 * x := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [this, hs3, mul_one, inv_mul_cancel]
  have h1 := hC s' hys hs'3
  apply hs1
  have : s = x * s' * x⁻¹ := by rw [hs']; group
  rw [this, h1]
  group

end Sylow

section Criterion

variable {S : Type} [Group S] [Finite S]

theorem good429_of_not_dvd {C : Subgroup S} {N B : ℕ} (hCN : Nat.card C ∣ N) (hN0 : 0 < N)
    (hB : N < B ^ 3) (rs : List ℕ) (hrs : ∀ r ∈ rs, ¬ r ∣ Nat.card C)
    (hall : (typeOrders N B).all (fun t => rs.any (fun r => decide (r ∣ t))) = true) :
    Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  haveI := nontrivial_of_isType429 hT
  obtain ⟨a, ha⟩ := exists_card_eq_mul_two_pow K
  have h1 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card C :=
    (show Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card K from ha ▸ Dvd.intro _ rfl).trans
      (Subgroup.card_dvd_of_le hKC)
  have hmem := card_mem_typeOrders hN0 hB hT (h1.trans hCN)
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hall
  obtain ⟨r, hr, hrt⟩ := hall _ hmem
  exact hrs r hr (hrt.trans h1)

end Criterion

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
