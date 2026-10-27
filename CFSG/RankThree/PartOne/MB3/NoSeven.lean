module

public import CFSG.RankThree.PartOne.MB3.Plane
public import CFSG.RankThree.PartOne.S11d.InnerBasic

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

section Fixed

variable [Finite G]

theorem exists_orderOf_seven_commute {K : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) (hc7 : c ^ 7 = 1) (h7 : 7 ∣ Nat.card K) :
    ∃ y ∈ K, orderOf y = 7 ∧ y * c = c * y := by
  classical
  have hmem : ∀ k : K, c * (k : G) * c⁻¹ ∈ K := fun k =>
    ((Subgroup.mem_normalizer_iff.mp hc k).mp k.2)
  let f : Function.End K := fun k => ⟨c * (k : G) * c⁻¹, hmem k⟩
  have hfn : ∀ n : ℕ, ∀ k : K, ((f ^ n) k : G) = c ^ n * (k : G) * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro k; simp; rfl
    | succ n ih =>
      intro k
      rw [pow_succ, pow_succ]
      show (((f ^ n) (f k) : K) : G) = _
      rw [ih (f k)]
      show c ^ n * (c * (k : G) * c⁻¹) * (c ^ n)⁻¹ = c ^ n * c * (k : G) * (c ^ n * c)⁻¹
      group
  have hf7 : f ^ 7 ^ 1 = 1 := by
    funext k
    apply Subtype.ext
    rw [pow_one, hfn, hc7]
    simp
    rfl
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fintype K := Fintype.ofFinite K
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) hf7
  let F : Subgroup K := (Subgroup.centralizer ({c} : Set G)).subgroupOf K
  have hcard : Fintype.card (Function.fixedPoints f) = Nat.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun k => ⟨k.1, by
          have h1 : c * (k.1 : G) * c⁻¹ = k.1 := congrArg Subtype.val k.2
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
          rw [mul_inv_eq_iff_eq_mul] at h1
          exact h1.symm⟩
        invFun := fun k => ⟨k.1, by
          have h1 := Subgroup.mem_centralizer_singleton_iff.mp
            (Subgroup.mem_subgroupOf.mp k.2)
          apply Subtype.ext
          show c * (k.1 : G) * c⁻¹ = k.1
          rw [mul_inv_eq_iff_eq_mul]
          exact h1.symm⟩
        left_inv := fun k => rfl
        right_inv := fun k => rfl }
  rw [hcard, ← Nat.card_eq_fintype_card] at hmod
  have h7F : 7 ∣ Nat.card F := by
    have := (Nat.modEq_zero_iff_dvd.mpr h7).symm.trans hmod
    exact (Nat.modEq_zero_iff_dvd).mp this.symm
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := F) 7 h7F
  refine ⟨((z : K) : G), (z : K).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  · have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp z.2)
    exact this

end Fixed

namespace Branch

variable [Finite G] {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ} {b : G}
  {S K K' : Subgroup G} {a' : G}

theorem not_dvd_card_K (H : Branch 7 A c L B n b S K K' a') (hKq : CFSG.IsQuasisimple K)
    (hZ : ¬ 7 ∣ Nat.card (Subgroup.center K))
    (hout : c ∉ K ⊔ Subgroup.centralizer (K : Set G)) : ¬ 7 ∣ Nat.card K := by
  intro h7K
  have hcA : c ∈ A := H.config.c_mem
  obtain ⟨y, hyK, hy7, hyc⟩ := exists_orderOf_seven_commute (K := K) (c := c)
    (H.A_le_normalizer_K hcA) (H.config.pow_p_eq_one hcA) h7K
  have hyA : ∀ a ∈ A, y * a = a * y := H.commute_A_of_mem_K hKq hyK hyc
  have hyC : y ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => (hyA a ha).symm
  have hy1 : y ^ 7 = 1 := by rw [← hy7]; exact pow_orderOf_eq_one y
  have hyAm : y ∈ A := H.config.mem_of_mem_centralizer hyC hy1
  set D := thetaQuotientCentralizer 7 A K with hD
  have hDA : D ≤ A := thetaQuotientCentralizer_le 7 A K
  by_cases hyD : y ∈ D
  · have hyZ : (⟨y, hyK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (H.D_centralizes hKq y hyD g g.2).symm
    apply hZ
    have h1 : orderOf (⟨⟨y, hyK⟩, hyZ⟩ : Subgroup.center K) = 7 := by
      rw [← hy7, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rw [← h1]
    exact orderOf_dvd_natCard _
  · have hE : A ≤ D ⊔ Subgroup.zpowers y := by
      have hEA : D ⊔ Subgroup.zpowers y ≤ A := sup_le hDA (Subgroup.zpowers_le.mpr hyAm)
      have hdvd1 : 49 ∣ Nat.card (D ⊔ Subgroup.zpowers y : Subgroup G) := by
        rw [← H.card_D]
        exact Subgroup.card_dvd_of_le le_sup_left
      have hdvd2 : Nat.card (D ⊔ Subgroup.zpowers y : Subgroup G) ∣ 7 ^ 3 := by
        rw [← H.card_A]
        exact Subgroup.card_dvd_of_le hEA
      obtain ⟨k, hk, hkE⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hdvd2
      have hk2 : 2 ≤ k := by
        by_contra hlt
        push Not at hlt
        have : 7 ^ k ∣ 7 ^ 1 := pow_dvd_pow 7 (by omega)
        rw [← hkE] at this
        have := Nat.le_of_dvd (by norm_num) (hdvd1.trans this)
        omega
      have hk3 : k = 3 := by
        by_contra hne
        have hk2' : k = 2 := by omega
        have hcardD : Nat.card D = 49 := H.card_D
        have hEq : D = D ⊔ Subgroup.zpowers y := by
          apply Subgroup.eq_of_le_of_card_ge le_sup_left
          rw [hkE, hk2', hcardD]
          norm_num
        exact hyD (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
      have hcardE : Nat.card (D ⊔ Subgroup.zpowers y : Subgroup G) = Nat.card A := by
        rw [hkE, hk3, H.card_A]
      exact (Subgroup.eq_of_le_of_card_ge hEA (le_of_eq hcardE.symm)).ge
    have hcM : c ∈ K ⊔ Subgroup.centralizer (K : Set G) := by
      refine (hE.trans (sup_le (fun d hd => ?_) ?_)) hcA
      · exact Subgroup.mem_sup_right
          (Subgroup.mem_centralizer_iff.mpr fun k hk => (H.D_centralizes hKq d hd k hk).symm)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hyK)
    exact hout hcM

end Branch

end CFSG.RankThree.PartOne.MB3
