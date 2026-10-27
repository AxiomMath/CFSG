module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonCounting
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSmallAlternating

namespace CFSG
end CFSG
open CFSG

/-!
# Dickson case II.8.23
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open scoped Pointwise

universe u

/-- Huppert II.8.23: the Dickson case with a nontrivial self-normalizing Sylow p-subgroup. -/
public theorem huppert_II_8_23_dickson_case_p_part_normalizer_self
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m) (hpm : 1 < p ^ m)
    (hnormalizer : Subgroup.normalizer (P : Set H) = (P : Subgroup H)) :
    (Nat.card H = p ^ m ∧ IsElementaryAbelian p H) ∨
    (p ^ m = 2 ∧ ∃ z : ℕ, ¬ 2 ∣ z ∧
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    (p ^ m = 3 ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) := by
  classical
  rcases huppert_II_8_22_dickson_counting hFcard H P hPcard with
    ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct, hs, hnormalizerZ, hdihedral,
      _hnormalizerP, hdivides, _hcounting⟩
  let NP := Subgroup.normalizer (P : Set H)
  let NZ : Fin r → Subgroup H := fun i => Subgroup.normalizer (Z i : Set H)
  have h823_partition_count :
      Nat.card H =
        1 + (p ^ m - 1) * NP.index +
          ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    dsimp only [NP, NZ]
    apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
    intro x hx
    convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
      hcoprime hmaximal hrepresentative hdistinct x hx using 1
    funext A
    rcases A with Q | z <;> rfl
  have h823_p_index_factor : p ^ m * NP.index = Nat.card H := by
    have hNPcard : Nat.card NP = p ^ m := by
      dsimp only [NP]
      rw [hnormalizer, hPcard]
    calc
      p ^ m * NP.index = Nat.card NP * NP.index := by rw [hNPcard]
      _ = Nat.card H := NP.card_mul_index
  have h823_z_index_factor :
      ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
    intro i
    have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
      dsimp only [NZ]
      exact hnormalizerZ i
    calc
      (Nat.card (Z i) * s i) * (NZ i).index =
          Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
      _ = Nat.card H := (NZ i).card_mul_index
  have h823_index_count :
      NP.index =
        1 + ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    let T := ∑ i, (Nat.card (Z i) - 1) * (NZ i).index
    have hsplit :
        (p ^ m - 1) * NP.index + NP.index = p ^ m * NP.index := by
      calc
        (p ^ m - 1) * NP.index + NP.index =
            (p ^ m - 1 + 1) * NP.index := by ring
        _ = p ^ m * NP.index := by rw [Nat.sub_add_cancel hpm.le]
    have hcancel :
        (p ^ m - 1) * NP.index + NP.index =
          (p ^ m - 1) * NP.index + (1 + T) := by
      calc
        (p ^ m - 1) * NP.index + NP.index =
            p ^ m * NP.index := hsplit
        _ = Nat.card H := h823_p_index_factor
        _ = 1 + (p ^ m - 1) * NP.index + T := by
          simpa only [T] using h823_partition_count
        _ = (p ^ m - 1) * NP.index + (1 + T) := by omega
    change NP.index = 1 + T
    exact Nat.add_left_cancel hcancel
  have h823_range_bound : r * p ^ m < 4 := by
    let T := ∑ i, (Nat.card (Z i) - 1) * (NZ i).index
    have hterm (i : Fin r) :
        Nat.card H ≤ 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by
      have hzbound :
          Nat.card (Z i) * s i ≤ 4 * (Nat.card (Z i) - 1) := by
        calc
          Nat.card (Z i) * s i ≤ Nat.card (Z i) * 2 :=
            Nat.mul_le_mul_left (Nat.card (Z i)) (hs i).2
          _ ≤ (2 * (Nat.card (Z i) - 1)) * 2 :=
            Nat.mul_le_mul_right 2 (by
              have hzi := hnontrivial i
              omega)
          _ = 4 * (Nat.card (Z i) - 1) := by ring
      calc
        Nat.card H = (Nat.card (Z i) * s i) * (NZ i).index :=
          (h823_z_index_factor i).symm
        _ ≤ (4 * (Nat.card (Z i) - 1)) * (NZ i).index :=
          Nat.mul_le_mul_right (NZ i).index hzbound
        _ = 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by ring
    have hrs : r * Nat.card H ≤ 4 * T := by
      calc
        r * Nat.card H = Finset.univ.sum fun _ : Fin r => Nat.card H := by simp
        _ ≤ Finset.univ.sum fun i : Fin r =>
            4 * ((Nat.card (Z i) - 1) * (NZ i).index) :=
          Finset.sum_le_sum fun i _hi => hterm i
        _ = 4 * T := by simp [T, Finset.mul_sum]
    have hcountT : NP.index = 1 + T := by
      simpa only [T] using h823_index_count
    have hT_lt_index : T < NP.index := by omega
    have hscaled_lt : p ^ m * T < Nat.card H := by
      calc
        p ^ m * T < p ^ m * NP.index :=
          (Nat.mul_lt_mul_left (by omega : 0 < p ^ m)).2 hT_lt_index
        _ = Nat.card H := h823_p_index_factor
    have hcancel : (r * p ^ m) * Nat.card H < 4 * Nat.card H := by
      calc
        (r * p ^ m) * Nat.card H = p ^ m * (r * Nat.card H) := by ring
        _ ≤ p ^ m * (4 * T) := Nat.mul_le_mul_left (p ^ m) hrs
        _ = 4 * (p ^ m * T) := by ring
        _ < 4 * Nat.card H :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hscaled_lt
    exact (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
  have h823_small_cases :
      r = 0 ∨ (r = 1 ∧ (p ^ m = 2 ∨ p ^ m = 3)) := by
    have hr_le : r ≤ r * p ^ m := by
      simpa using Nat.mul_le_mul_left r hpm.le
    have hr_lt : r < 4 := lt_of_le_of_lt hr_le h823_range_bound
    interval_cases r <;> omega
  have h823_case_zero (hr : r = 0) :
      Nat.card H = p ^ m ∧ IsElementaryAbelian p H := by
    subst r
    have hNPindex : NP.index = 1 := by
      simpa using h823_index_count
    have hPindex : (P : Subgroup H).index = 1 := by
      dsimp only [NP] at hNPindex
      rwa [hnormalizer] at hNPindex
    have hPtop : (P : Subgroup H) = ⊤ := Subgroup.index_eq_one.mp hPindex
    have hHcard : Nat.card H = p ^ m := by
      have h := hPcard
      rw [hPtop] at h
      simpa using h
    let : Fintype F := Fintype.ofFinite F
    let : CharP F p :=
      charP_of_card_eq_prime_pow (by simpa using hFcard)
    obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
    have hHleQ : H ≤ (Q : Subgroup (PSL2MatrixGroup F)) := by
      intro x hx
      change (⟨x, hx⟩ : H) ∈ (Q : Subgroup _).comap H.subtype
      rw [hQcomap, hPtop]
      simp
    have hFieldElementary : IsElementaryAbelian p (Multiplicative F) := by
      refine
        { toIsMulCommutative :=
            { is_comm := ⟨fun x y => mul_comm x y⟩ }
          exponent_dvd_p := ?_ }
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      change Multiplicative.ofAdd x.toAdd ^ p = 1
      rw [← ofAdd_nsmul]
      simp
    obtain ⟨eQ⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard Q
    have hQElementary : IsElementaryAbelian p Q := by
      refine
        { toIsMulCommutative :=
            { is_comm := ⟨fun x y => ?_⟩ }
          exponent_dvd_p := ?_ }
      · apply eQ.symm.injective
        simpa using
          hFieldElementary.toIsMulCommutative.is_comm.comm
            (eQ.symm x) (eQ.symm y)
      · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro x
        apply eQ.symm.injective
        have hx : (eQ.symm x) ^ p = 1 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            hFieldElementary.exponent_dvd_p (eQ.symm x)
        simpa using hx
    have hHElementary : IsElementaryAbelian p H := by
      let : IsElementaryAbelian p Q := hQElementary
      refine
        { toIsMulCommutative :=
            { is_comm := ⟨fun x y =>
                Subtype.ext <|
                  setLike_mul_comm (hHleQ x.2) (hHleQ y.2)⟩ }
          exponent_dvd_p := ?_ }
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      let xQ : Q := ⟨(x : PSL2MatrixGroup F), hHleQ x.2⟩
      have hxpow : xQ ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p Q) xQ
      simpa [xQ] using congrArg Subtype.val hxpow
    exact ⟨hHcard, hHElementary⟩
  have h823_case_two (hr : r = 1) (hpm2 : p ^ m = 2) :
      ∃ z : ℕ, ¬ 2 ∣ z ∧
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z) := by
    subst r
    have hcount0 :
        NP.index =
          1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
      simpa using h823_index_count
    have hPfactor2 : 2 * NP.index = Nat.card H := by
      calc
        2 * NP.index = p ^ m * NP.index :=
          congrArg (fun a => a * NP.index) hpm2.symm
        _ = Nat.card H := h823_p_index_factor
    have hZfactor0 :
        (Nat.card (Z 0) * s 0) * (NZ 0).index = Nat.card H :=
      h823_z_index_factor 0
    have hs0_two : s 0 = 2 := by
      have hs0 := hs 0
      rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
      · have hzbound :
            Nat.card (Z 0) ≤ 2 * (Nat.card (Z 0) - 1) := by
          have hz := hnontrivial 0
          omega
        have hlt :
            Nat.card (Z 0) * (NZ 0).index < 2 * NP.index := by
          calc
            Nat.card (Z 0) * (NZ 0).index ≤
                (2 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
              Nat.mul_le_mul_right (NZ 0).index hzbound
            _ = 2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
            _ < 2 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
              omega
            _ = 2 * NP.index := by rw [← hcount0]
        have hbad : Nat.card H < Nat.card H := by
          calc
            Nat.card H = Nat.card (Z 0) * (NZ 0).index := by
              simpa [hs0_one] using hZfactor0.symm
            _ < 2 * NP.index := hlt
            _ = Nat.card H := hPfactor2
        exact (Nat.lt_irrefl _ hbad).elim
      · exact hs0_two
    have hk0_one : (NZ 0).index = 1 := by
      have hZfactor2 :
          2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
          _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hs0_two]
          _ = Nat.card H := hZfactor0
      have hindex_eq : NP.index = Nat.card (Z 0) * (NZ 0).index := by
        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
        exact hPfactor2.trans hZfactor2.symm
      have hzsplit :
          Nat.card (Z 0) * (NZ 0).index =
            (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
        calc
          Nat.card (Z 0) * (NZ 0).index =
              (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by
            rw [Nat.sub_add_cancel (hnontrivial 0).le]
          _ = (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
            ring
      have hcancel :
          (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
            (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by
        calc
          (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
              Nat.card (Z 0) * (NZ 0).index := hzsplit.symm
          _ = NP.index := hindex_eq.symm
          _ = 1 + (Nat.card (Z 0) - 1) * (NZ 0).index := hcount0
          _ = (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by omega
      exact Nat.add_left_cancel hcancel
    have hHcard2 : Nat.card H = 2 * Nat.card (Z 0) := by
      calc
        Nat.card H = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
          hZfactor0.symm
        _ = 2 * Nat.card (Z 0) := by rw [hs0_two, hk0_one]; ring
    have hp_eq_two : p = 2 := by
      have hm_ne_zero : m ≠ 0 := by
        intro hm
        subst m
        norm_num at hpm2
      have hp_dvd : p ∣ 2 := by
        have hp_pow : p ∣ p ^ m := dvd_pow_self p hm_ne_zero
        exact hpm2 ▸ hp_pow
      exact
        (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp_dvd
    have hzodd : ¬ 2 ∣ Nat.card (Z 0) := by
      apply Nat.prime_two.coprime_iff_not_dvd.mp
      simpa [hp_eq_two] using hcoprime 0
    have hNZtop : NZ 0 = ⊤ := by
      exact Subgroup.index_eq_one.mp hk0_one
    have hHequiv : Nonempty (H ≃* DihedralGroup (Nat.card (Z 0))) := by
      obtain ⟨eD⟩ := hdihedral 0 hs0_two
      let eH : NZ 0 ≃* H :=
        (MulEquiv.subgroupCongr hNZtop).trans
          (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
      exact ⟨eH.symm.trans eD⟩
    exact ⟨Nat.card (Z 0), hzodd, hdivides 0, hHcard2, hHequiv⟩
  have h823_case_three (hr : r = 1) (hpm3 : p ^ m = 3) :
      Nonempty (H ≃* alternatingGroup (Fin 4)) := by
    subst r
    have hcount0 :
        NP.index =
          1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
      simpa using h823_index_count
    have hPfactor3 : 3 * NP.index = Nat.card H := by
      calc
        3 * NP.index = p ^ m * NP.index :=
          congrArg (fun a => a * NP.index) hpm3.symm
        _ = Nat.card H := h823_p_index_factor
    have hZfactor0 :
        (Nat.card (Z 0) * s 0) * (NZ 0).index = Nat.card H :=
      h823_z_index_factor 0
    have hs0_two : s 0 = 2 := by
      have hs0 := hs 0
      rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
      · have hzbound :
            Nat.card (Z 0) ≤ 3 * (Nat.card (Z 0) - 1) := by
          have hz := hnontrivial 0
          omega
        have hlt :
            Nat.card (Z 0) * (NZ 0).index < 3 * NP.index := by
          calc
            Nat.card (Z 0) * (NZ 0).index ≤
                (3 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
              Nat.mul_le_mul_right (NZ 0).index hzbound
            _ = 3 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
            _ < 3 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
              omega
            _ = 3 * NP.index := by rw [← hcount0]
        have hbad : Nat.card H < Nat.card H := by
          calc
            Nat.card H = Nat.card (Z 0) * (NZ 0).index := by
              simpa [hs0_one] using hZfactor0.symm
            _ < 3 * NP.index := hlt
            _ = Nat.card H := hPfactor3
        exact (Nat.lt_irrefl _ hbad).elim
      · exact hs0_two
    have hz0_two : Nat.card (Z 0) = 2 := by
      have hZfactor2 :
          2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
          _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hs0_two]
          _ = Nat.card H := hZfactor0
      have hfactor_eq :
          3 * NP.index = 2 * (Nat.card (Z 0) * (NZ 0).index) :=
        hPfactor3.trans hZfactor2.symm
      by_contra hz_ne_two
      have hz_ge_three : 3 ≤ Nat.card (Z 0) := by
        have hz := hnontrivial 0
        omega
      have hzbound :
          2 * Nat.card (Z 0) ≤ 3 * (Nat.card (Z 0) - 1) := by
        omega
      have hlt :
          2 * (Nat.card (Z 0) * (NZ 0).index) < 3 * NP.index := by
        calc
          2 * (Nat.card (Z 0) * (NZ 0).index) =
              (2 * Nat.card (Z 0)) * (NZ 0).index := by ring
          _ ≤ (3 * (Nat.card (Z 0) - 1)) * (NZ 0).index :=
            Nat.mul_le_mul_right (NZ 0).index hzbound
          _ = 3 * ((Nat.card (Z 0) - 1) * (NZ 0).index) := by ring
          _ < 3 * (1 + (Nat.card (Z 0) - 1) * (NZ 0).index) := by
            omega
          _ = 3 * NP.index := by rw [← hcount0]
      exact (Nat.lt_irrefl _ (hlt.trans_eq hfactor_eq)).elim
    have hk0_three : (NZ 0).index = 3 := by
      have hcount' : NP.index = 1 + (NZ 0).index := by
        simpa [hz0_two] using hcount0
      have hZfactor4 : 4 * (NZ 0).index = Nat.card H := by
        calc
          4 * (NZ 0).index =
              (Nat.card (Z 0) * s 0) * (NZ 0).index := by
            rw [hz0_two, hs0_two]
          _ = Nat.card H := hZfactor0
      have hfactor' : 3 * NP.index = 4 * (NZ 0).index :=
        hPfactor3.trans hZfactor4.symm
      omega
    have hHcard12 : Nat.card H = 12 := by
      calc
        Nat.card H = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
          hZfactor0.symm
        _ = 12 := by rw [hz0_two, hs0_two, hk0_three]
    have hp_eq_three : p = 3 := by
      have hm_ne_zero : m ≠ 0 := by
        intro hm
        subst m
        norm_num at hpm3
      have hp_dvd : p ∣ 3 := by
        have hp_pow : p ∣ p ^ m := dvd_pow_self p hm_ne_zero
        exact hpm3 ▸ hp_pow
      exact
        (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hp_dvd
    subst p
    have hSylow4 : Nat.card (Sylow 3 H) = 4 := by
      have hPindex4 : NP.index = 4 := by
        simpa [hz0_two, hk0_three] using hcount0
      calc
        Nat.card (Sylow 3 H) =
            (Subgroup.normalizer (P : Set H)).index :=
          P.card_eq_index_normalizer
        _ = NP.index := by rfl
        _ = 4 := hPindex4
    exact huppert_II_8_17_b_order_twelve_four_sylow_three hHcard12 hSylow4
  rcases h823_small_cases with hr | ⟨hr, hpm2 | hpm3⟩
  · exact Or.inl (h823_case_zero hr)
  · exact Or.inr (Or.inl ⟨hpm2, h823_case_two hr hpm2⟩)
  · exact Or.inr (Or.inr ⟨hpm3, h823_case_three hr hpm3⟩)

end Dickson
end CFSG.Glauberman
