module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenPi
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTheta
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTight

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.CGT.PushingUpLit.SolK
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

private theorem eq_one_of_mem_pCoreOf_of_odd (H : Subgroup G) {r : G}
    (hr : r ∈ CFSG.Open.pCoreOf 2 H) {m : ℕ} (hm : Odd m) (hrm : r ^ m = 1) : r = 1 := by
  obtain ⟨j, hj⟩ := isPGroup_pCoreOf' H ⟨r, hr⟩
  have hj' : r ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have h := pow_gcd_eq_one.2 ⟨hrm, hj'⟩
  rwa [((Nat.coprime_two_right.2 hm).pow_right j).gcd_eq_one, pow_one] at h

theorem mem_centralizer_of_odd {C : Cfg G M X n} (D : C.PiData) {k : G} (hk : k ∈ C.K) {m : ℕ}
    (hm : Odd m) (hkm : k ^ m = 1) : k ∈ Subgroup.centralizer (X : Set G) := by
  refine (D.ker ⟨k, hk⟩).1 ?_
  obtain ⟨j, rfl⟩ := hm
  have hsq : D.π ⟨k, hk⟩ ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    exact permBar_add_self _
  have hpow : D.π ⟨k, hk⟩ ^ (2 * j + 1) = 1 := by
    have h1 : (⟨k, hk⟩ : ↥C.K) ^ (2 * j + 1) = 1 := Subtype.ext (by simpa using hkm)
    rw [← map_pow, h1, map_one]
  rwa [pow_succ, pow_mul, hsq, one_pow, one_mul] at hpow

theorem eq_one_of_odd_of_comm_R (S : Setting G M X n) {x : G}
    (hxC : x ∈ Subgroup.centralizer (X : Set G)) (hxR : ∀ r ∈ Rc X, x * r = r * x)
    {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) : x = 1 := by
  have hxM : x ∈ M := S.centralizer_le hxC
  have hcomm : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * x = x * q := by
    intro q hq
    have hqM : q ∈ M := pCoreOf_le_self M hq
    have hcQ : x * q * x⁻¹ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem (pCoreOf_normalized M hxM hq)
        ((CFSG.Open.pCoreOf 2 M).inv_mem hq)
    have hcR : x * q * x⁻¹ * q⁻¹ ∈ Rc X := by
      rw [S.R_eq_inf]
      refine Subgroup.mem_inf.2 ⟨hcQ, ?_⟩
      have e : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
      rw [e]
      exact (Subgroup.centralizer (X : Set G)).mul_mem hxC
        (Theta.conj_mem_centralizer_of_mem S hqM
          ((Subgroup.centralizer (X : Set G)).inv_mem hxC))
    have hxc : Commute x (x * q * x⁻¹ * q⁻¹) := hxR _ hcR
    have hpow := Commute.commutatorElement_pow_left (a := x) (b := q) hxc m
    rw [hxm, commutatorElement_one_left] at hpow
    have h1 : x * q * x⁻¹ * q⁻¹ = 1 :=
      eq_one_of_mem_pCoreOf_of_odd M hcQ hm hpow
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  have hcent : x ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    Subgroup.mem_centralizer_iff.2 hcomm
  have hxQ : x ∈ CFSG.Open.pCoreOf 2 M := S.charTwo M S.maxLocal.1 ⟨hxM, hcent⟩
  exact eq_one_of_mem_pCoreOf_of_odd M hxQ hm hxm

theorem comm_of_pow_three_of_fixes {R : Subgroup G} (hR4 : Nat.card R = 4)
    {x : G} (hxn : ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hx3 : x ^ 3 = 1) {r₀ : G} (hr₀ : r₀ ∈ R) (hr₀1 : r₀ ≠ 1) (hfix : x * r₀ = r₀ * x) :
    ∀ r ∈ R, x * r = r * x := by
  intro a haR
  by_contra hne
  have hx3' : x * x * x = 1 := by rw [← hx3, pow_three']
  have hinj : ∀ c d : G, x * c * x⁻¹ = x * d * x⁻¹ → c = d := fun c d h =>
    mul_left_cancel (mul_right_cancel h)
  have hφ1 : x * 1 * x⁻¹ = 1 := by group
  have hφr₀ : x * r₀ * x⁻¹ = r₀ := mul_inv_eq_iff_eq_mul.2 hfix
  obtain ⟨b, hb⟩ : ∃ b : G, b = x * a * x⁻¹ := ⟨_, rfl⟩
  have hbR : b ∈ R := by rw [hb]; exact hxn a haR
  have ha1 : a ≠ 1 := fun h => hne (by rw [h]; group)
  have har₀ : a ≠ r₀ := fun h => hne (by rw [h]; exact hfix)
  have hba : b ≠ a := fun h => hne (mul_inv_eq_iff_eq_mul.1 (hb.symm.trans h))
  have hb1 : b ≠ 1 := fun h => ha1 (hinj a 1 ((hb.symm.trans h).trans hφ1.symm))
  have hbr₀ : b ≠ r₀ := fun h => har₀ (hinj a r₀ ((hb.symm.trans h).trans hφr₀.symm))
  have hU : ({1, r₀, a, b} : Set G) = (R : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact R.one_mem
      · exact hr₀
      · exact haR
      · exact hbR
    · have h1 : (1 : G) ∉ ({r₀, a, b} : Set G) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hr₀1, Ne.symm ha1, Ne.symm hb1⟩
      have h2 : r₀ ∉ ({a, b} : Set G) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm har₀, Ne.symm hbr₀⟩
      have hcard : ({1, r₀, a, b} : Set G).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair hba.symm]
      rw [hcard, ← Nat.card_coe_set_eq]
      exact hR4.le
  have hφbR : x * b * x⁻¹ ∈ ({1, r₀, a, b} : Set G) := by
    rw [hU]
    exact hxn b hbR
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφbR
  rcases hφbR with h | h | h | h
  · exact hb1 (hinj b 1 (h.trans hφ1.symm))
  · exact hbr₀ (hinj b r₀ (h.trans hφr₀.symm))
  · have h2 : x * (x * a * x⁻¹) * x⁻¹ = a := by rw [← hb]; exact h
    have h3 : x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = a := by
      have e : x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by
        group
      rw [e, hx3', inv_one]
      group
    rw [h2, ← hb] at h3
    exact hba h3
  · exact hba (hinj b a (h.trans hb))

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
