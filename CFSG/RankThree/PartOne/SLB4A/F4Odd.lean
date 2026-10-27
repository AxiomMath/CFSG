module

public import CFSG.RankThree.PartOne.SLB4A.ExcOdd
public import CFSG.RankThree.PartOne.SLB4A.WeylWord3

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk

def omegaF4 : List (Fin Tag.F4.rank) :=
  ([0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3] : List (Fin 4)).map
    (Fin.cast (by decide))

theorem wsq_omegaF4 : WSq Tag.F4 omegaF4 := by
  unfold WSq
  decide +kernel

theorem hpar_omegaF4 : ∀ i : Fin Tag.F4.rank, ∀ k < Tag.F4.rootCertificate.roots.length,
    (∑ j, Tag.F4.cartan i j * Tag.F4.rootCertificate.root k j) % 2 =
      (∑ j, Tag.F4.cartan i j * Tag.F4.rootCertificate.root (walk Tag.F4 omegaF4 k).1 j) % 2 := by
  decide +kernel

theorem walk_omegaF4_zero : (walk Tag.F4 omegaF4 0).1 ≠ 0 := by
  decide +kernel

def f4i (k : Fin 4) : Fin Tag.F4.rank := Fin.cast (by decide) k

def aF4 : Fin 5 → Fin Tag.F4.rank := fun k => f4i (![0, 1, 2, 3, 0] k)

theorem hcombF4 : ∀ v : V2 5, (∀ j : Fin Tag.F4.rank,
    sgp Tag.F4 aF4 0 j ^ ex (v 0) * sgp Tag.F4 aF4 1 j ^ ex (v 1) *
      sgp Tag.F4 aF4 2 j ^ ex (v 2) * sgp Tag.F4 aF4 3 j ^ ex (v 3) = 1) →
    v 0 = 1 ∧ v 1 = 1 ∧ v 2 = 1 ∧ v 3 = 1 := by
  decide +kernel

section F4

variable {K : Type} [Field K]

noncomputable def gF4 (k : Fin 5) : adjointGroup Tag.F4 K :=
  if h : k.1 < 4 then dElt (f4i ⟨k.1, h⟩) (-1 : Kˣ) else wElt omegaF4

theorem exists_two_pow_five_F4_odd (hneg : (-1 : K) ≠ 1) :
    ∃ U : Subgroup (adjointGroup Tag.F4 K), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  have hct : ∀ i : Fin Tag.F4.rank,
      (wElt omegaF4 * dElt i (-1 : Kˣ) : adjointGroup Tag.F4 K) =
        dElt i (-1 : Kˣ) * wElt omegaF4 := fun i => wElt_comm_dElt omegaF4 i (hpar_omegaF4 i)
  refine exists_two_pow_five_of_commInvol (gF4 (K := K)) ?_ ?_ ?_
  · intro i j
    by_cases hi : i.1 < 4
    · by_cases hj : j.1 < 4
      · simp only [gF4, hi, hj, ↓reduceDIte]
        exact dElt_mul_comm' _ _ _ _
      · simp only [gF4, hi, hj, ↓reduceDIte]
        exact (hct _).symm
    · by_cases hj : j.1 < 4
      · simp only [gF4, hi, hj, ↓reduceDIte]
        exact hct _
      · simp only [gF4, hi, hj, ↓reduceDIte]
  · intro k
    by_cases hk : k.1 < 4
    · simp only [gF4, hk, ↓reduceDIte]
      exact dElt_neg_one_sq _
    · simp only [gF4, hk, ↓reduceDIte]
      exact wElt_mul_wElt_eq_one wsq_omegaF4
  · intro v hv
    have e0 : gF4 (K := K) 0 = dElt (f4i 0) (-1 : Kˣ) := by simp [gF4]
    have e1 : gF4 (K := K) 1 = dElt (f4i 1) (-1 : Kˣ) := by simp [gF4]
    have e2 : gF4 (K := K) 2 = dElt (f4i 2) (-1 : Kˣ) := by simp [gF4]
    have e3 : gF4 (K := K) 3 = dElt (f4i 3) (-1 : Kˣ) := by simp [gF4]
    have e4 : gF4 (K := K) 4 = wElt omegaF4 := by simp [gF4]
    rw [e0, e1, e2, e3, e4] at hv
    have hD : HasEig (opOf (dElt (f4i 0) (-1 : Kˣ) ^ ex (v 0) * dElt (f4i 1) (-1 : Kˣ) ^ ex (v 1) *
        dElt (f4i 2) (-1 : Kˣ) ^ ex (v 2) * dElt (f4i 3) (-1 : Kˣ) ^ ex (v 3) :
          adjointGroup Tag.F4 K)) (rootVec Tag.F4 K (Tag.F4.rootCertificate.root
          (walk Tag.F4 omegaF4 0).1)) := by
      have hr := isRoot_rootCertificate_root (τ := Tag.F4) (walk_fst_lt omegaF4 (k := 0) (by decide))
      simp only [opOf_mul]
      exact ((((dElt_pow_hasEig _ _ _ hr).mul (dElt_pow_hasEig _ _ _ hr)).mul
        (dElt_pow_hasEig _ _ _ hr)).mul (dElt_pow_hasEig _ _ _ hr))
    rcases ex_cases (v 4) with h4 | h4
    · rw [h4, pow_zero, mul_one] at hv
      have hM : ∀ j, Mult j (dElt (f4i 0) (-1 : Kˣ) ^ ex (v 0) * dElt (f4i 1) (-1 : Kˣ) ^ ex (v 1) *
          dElt (f4i 2) (-1 : Kˣ) ^ ex (v 2) * dElt (f4i 3) (-1 : Kˣ) ^ ex (v 3))
          ((((-1 : Kˣ) ^ Tag.F4.cartan (f4i 0) j : Kˣ) : K) ^ ex (v 0) *
            (((-1 : Kˣ) ^ Tag.F4.cartan (f4i 1) j : Kˣ) : K) ^ ex (v 1) *
            (((-1 : Kˣ) ^ Tag.F4.cartan (f4i 2) j : Kˣ) : K) ^ ex (v 2) *
            (((-1 : Kˣ) ^ Tag.F4.cartan (f4i 3) j : Kˣ) : K) ^ ex (v 3)) := fun j =>
        Mult_mul (Mult_mul (Mult_mul (Mult_dElt_pow _ j (-1 : Kˣ) _)
          (Mult_dElt_pow _ j (-1 : Kˣ) _)) (Mult_dElt_pow _ j (-1 : Kˣ) _))
          (Mult_dElt_pow _ j (-1 : Kˣ) _)
      have hall := hcombF4 v fun j => by
        have h1 := eq_of_Mult_one (hv ▸ hM j)
        simp only [neg_one_zpow_eq_eps, eps_pow, ← eps_mul] at h1
        exact eps_inj hneg (h1.trans (eps_one K).symm)
      obtain ⟨a0, a1, a2, a3⟩ := hall
      funext k
      fin_cases k
      · exact a0
      · exact a1
      · exact a2
      · exact a3
      · exact eq_one_of_ex_eq_zero h4
    · rw [h4, pow_one] at hv
      exact absurd hv (no_torus_mul_wElt _ omegaF4 (k := 0) (by decide) walk_omegaF4_zero hD)

end F4

end CFSG.RankThree.PartOne.SLB4A
