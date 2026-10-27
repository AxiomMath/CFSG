module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_exists_pGroup_permutes {A T : Subgroup G} (hAo : Odd (Nat.card A))
    (hAc : IsMulCommutative A) (hT : IsPGroup 2 T) (hAT : Permutes A T) {r : ℕ} (hr : r.Prime)
    (hrA : r ∣ Nat.card A) : ∃ R ≤ A, IsPGroup r R ∧ r ∣ Nat.card R ∧ Permutes R T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hHK, hTH, hHpi, hHidx⟩ := CFSG.Quasithin.E1.exists_hall_two_p hr le_sup_right hT
    (uc22p2214_isSolvable_sup hAo hAc hT hAT)
  have hAT1 : A ⊓ T = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hAo)
  have hperm : Permutes (A ⊓ H) T := CFSG.Quasithin.H23P4.mul_comm_inf_of_le hAT hTH
  have hHeq : (A ⊓ H) ⊔ T = H := by
    refine le_antisymm (sup_le inf_le_right hTH) fun h hh => ?_
    obtain ⟨a, ha, t, ht, rfl⟩ := uc22p2214_mem_sup_of_permutes hAT (hHK hh)
    have haH : a ∈ H := by
      have h1 := H.mul_mem hh (H.inv_mem (hTH ht))
      rwa [mul_inv_cancel_right] at h1
    exact mul_mem_sup ⟨ha, haH⟩ ht
  have hcardH : Nat.card H = Nat.card ↥(A ⊓ H) * Nat.card T := by
    have h := uc22p2214_card_sup_of_permutes hperm (by
      rw [eq_bot_iff, ← hAT1]
      exact inf_le_inf_right T inf_le_left)
    rwa [hHeq] at h
  have hidx := Subgroup.relIndex_mul_card H (A ⊔ T)
  rw [inf_eq_left.2 hHK, uc22p2214_card_sup_of_permutes hAT hAT1, hcardH, ← mul_assoc] at hidx
  have hA : Nat.card A = H.relIndex (A ⊔ T) * Nat.card ↥(A ⊓ H) :=
    (Nat.eq_of_mul_eq_mul_right Nat.card_pos hidx).symm
  have hrR : r ∣ Nat.card ↥(A ⊓ H) := by
    rw [hA] at hrA
    rcases (Nat.Prime.dvd_mul hr).1 hrA with h | h
    · exact absurd rfl (hHidx r hr h).2
    · exact h
  refine ⟨A ⊓ H, inf_le_left, ?_, hrR, hperm⟩
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdR => ?_)
  rcases hHpi _ hd (hdR.trans (Subgroup.card_dvd_of_le inf_le_right)) with h | h
  · subst h
    exact absurd (even_iff_two_dvd.2 (hdR.trans (Subgroup.card_dvd_of_le inf_le_left)))
      (Nat.not_even_iff_odd.2 hAo)
  · exact h

theorem uc22s2112r34_exists_rSub_calB1 {T M L B₀ : Subgroup G} (hB₀ : B₀ ∈ calB1 T M L)
    (hT : IsPGroup 2 T) {r : ℕ} (hr : r.Prime) (hrB : r ∣ Nat.card B₀) :
    ∃ R ≤ B₀, IsPGroup r R ∧ r ∣ Nat.card R ∧ Nat.card R ∣ r ^ 2 ∧ Permutes R T ∧
      ∀ x ∈ R, x ≠ 1 → orderOf x = r := by
  have : Fact r.Prime := ⟨hr⟩
  have hsqB := fun x (hx : x ∈ B₀) => Ctx23L.orderOf_squarefree_of_mem_calB1 hB₀ hx
  obtain ⟨-, hB₀c, D, C, ⟨-, hDcy, hDsq, hDo, hDT, -⟩, -, hCo, hCsyl, hB₀eq, hB₀T, -, -⟩ := hB₀
  have hDC : ∀ x ∈ D, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB₀c.is_comm.comm ⟨x, hB₀eq ▸ mem_sup_left hx⟩
      ⟨y, hB₀eq ▸ mem_sup_right hy⟩)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D C hDC).1
  rw [← hB₀eq] at hprod
  have hB₀dvd : Nat.card B₀ ∣ Nat.card D * Nat.card C := Dvd.intro _ hprod
  have key : ∃ R ≤ B₀, IsPGroup r R ∧ r ∣ Nat.card R ∧ Nat.card R ∣ r ^ 2 ∧ Permutes R T := by
    by_cases hrD : r ∣ Nat.card D
    · obtain ⟨R, hRD, hRp, hrR, hRT⟩ :=
        uc22s2112r34_exists_pGroup_permutes hDo inferInstance hT hDT hr hrD
      refine ⟨R, hRD.trans (hB₀eq ▸ le_sup_left), hRp, hrR, ?_, hRT⟩
      obtain ⟨k, hk⟩ := hRp.exists_card_eq
      have hsq : Squarefree (r ^ k) := hk ▸ hDsq.squarefree_of_dvd (Subgroup.card_dvd_of_le hRD)
      rw [hk]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact one_dvd _
      · obtain rfl := ((Nat.squarefree_pow_iff hr.ne_one hk0.ne').1 hsq).2
        exact pow_dvd_pow r one_le_two
    · have hB₀o : Odd (Nat.card B₀) := Odd.of_dvd_nat (hDo.mul hCo) hB₀dvd
      obtain ⟨R, hRB, hRp, hrR, hRT⟩ :=
        uc22s2112r34_exists_pGroup_permutes hB₀o hB₀c hT hB₀T hr hrB
      refine ⟨R, hRB, hRp, hrR, ?_, hRT⟩
      obtain ⟨k, hk⟩ := hRp.exists_card_eq
      have hRC : r ^ k ∣ Nat.card C :=
        Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left k ((hr.coprime_iff_not_dvd).2 hrD))
          (hk ▸ (Subgroup.card_dvd_of_le hRB).trans hB₀dvd)
      have hrC : r ∣ Nat.card C :=
        (Nat.Coprime.dvd_of_dvd_mul_left ((hr.coprime_iff_not_dvd).2 hrD) (hrB.trans hB₀dvd))
      obtain ⟨P, hP, -⟩ := hCsyl r hr hrC
      rw [hk, ← hP]
      exact P.pow_dvd_card_of_pow_dvd_card hRC
  obtain ⟨R, hRB, hRp, hrR, hR2, hRT⟩ := key
  refine ⟨R, hRB, hRp, hrR, hR2, hRT, fun x hx hx1 => ?_⟩
  obtain ⟨k, hk⟩ := hRp.exists_card_eq
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).1 (hk ▸ Subgroup.orderOf_dvd_natCard R hx)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by rw [hj, pow_zero]))
  have hsq := hsqB x (hRB hx)
  rw [hj] at hsq ⊢
  rw [((Nat.squarefree_pow_iff hr.ne_one hj0).1 hsq).2, pow_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
