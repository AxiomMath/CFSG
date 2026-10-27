module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftLie

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

namespace Lem11Borel

theorem exists_prime_gt_three_dvd {n : ℕ} (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n - 1 := by
  have h8 : 2 ^ n = 8 * 2 ^ (n - 3) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  have hpos : 1 ≤ 2 ^ (n - 3) := Nat.one_le_two_pow
  have hmod : (2 ^ n - 1) % 8 = 7 := by omega
  have hne : 2 ^ n - 1 ≠ 0 := by omega
  by_contra hcon
  push Not at hcon
  have h3 : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ n - 1 → d = 3 := by
    intro d hd hdv
    have hd3 : d ≤ 3 := by
      by_contra h
      exact hcon d hd (by omega) hdv
    have hd2 : d ≠ 2 := by
      rintro rfl
      omega
    have := hd.two_le
    omega
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hne h3
  have hpow : ∀ k : ℕ, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> norm_num
  rcases hpow (2 ^ n - 1).primeFactorsList.length with h | h <;> rw [← heq] at h <;> omega

variable {G : Type} [Group G] [Finite G]

@[expose] def omegaSub (C : Subgroup G) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (p : ℕ) :
    Subgroup G where
  carrier := {x | x ∈ C ∧ x ^ p = 1}
  mul_mem' := fun {x y} hx hy => ⟨C.mul_mem hx.1 hy.1, by
    rw [(Commute.mul_pow (hC x hx.1 y hy.1)), hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨C.one_mem, one_pow p⟩
  inv_mem' := fun {x} hx => ⟨C.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

omit [Finite G] in
theorem omegaSub_le {C : Subgroup G} (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (p : ℕ) :
    omegaSub C hC p ≤ C := fun _ hx => hx.1

theorem omegaSub_mul_comm {C R T X : Subgroup G} (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hCodd : Odd (Nat.card C)) (hR : IsPGroup 2 R) (hRT : R ≤ T) (hTX : T ≤ X) (hCX : C ≤ X)
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hXCR : X ≤ Subgroup.normalizer ((C ⊔ R : Subgroup G) : Set G)) (p : ℕ) :
    ((omegaSub C hC p : Subgroup G) : Set G) * (T : Set G) =
      (T : Set G) * (omegaSub C hC p : Set G) := by
  set A := omegaSub C hC p with hA
  have hAC : A ≤ C := omegaSub_le hC p
  have hCR0 : C ⊓ R = ⊥ := E2.BorelLift.inf_eq_bot_of_odd hCodd hR
  have hCN : C ≤ Subgroup.normalizer (R : Set G) := hCX.trans hXR
  have hAN : A ≤ Subgroup.normalizer (R : Set G) := hAC.trans hCN
  have hXAR : X ≤ Subgroup.normalizer ((A ⊔ R : Subgroup G) : Set G) := by
    intro m hm
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have hle : (A ⊔ R).map (MulAut.conj m).toMonoidHom ≤ A ⊔ R := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        have h1 : m * a * m⁻¹ ∈ ((C ⊔ R : Subgroup G) : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (hXCR hm) a).mp (Subgroup.mem_sup_left (hAC ha))
        rw [Subgroup.coe_mul_of_left_le_normalizer_right C R hCN] at h1
        obtain ⟨c, hc, r, hr, hcr⟩ := h1
        have hcr' : c * r = m * a * m⁻¹ := hcr
        have hp : (c * r) ^ p = 1 := by
          rw [hcr', conj_pow, ha.2, mul_one, mul_inv_cancel]
        obtain ⟨r', hr', hpow⟩ := exists_pow_mul_eq_pow_mul (hCN hc) hr p
        have hcp : c ^ p ∈ C ⊓ R := by
          refine ⟨C.pow_mem hc p, ?_⟩
          have : c ^ p = (r')⁻¹ := by
            rw [hpow] at hp
            exact eq_inv_of_mul_eq_one_left hp
          rw [this]
          exact R.inv_mem hr'
        rw [hCR0, Subgroup.mem_bot] at hcp
        show (MulAut.conj m).toMonoidHom a ∈ A ⊔ R
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← hcr']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hc, hcp⟩) (Subgroup.mem_sup_right hr)
      · rintro _ ⟨r, hr, rfl⟩
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hXR hm) r).mp hr)
    exact hle ⟨x, hx, rfl⟩
  have hTAR : T ≤ Subgroup.normalizer ((A ⊔ R : Subgroup G) : Set G) := hTX.trans hXAR
  have hRTset : (R : Set G) * (T : Set G) = T := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨r, hr, t, ht, rfl⟩
      exact T.mul_mem (hRT hr) ht
    · intro t ht
      exact ⟨1, R.one_mem, t, ht, one_mul t⟩
  have hTRset : (T : Set G) * (R : Set G) = T := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨t, ht, r, hr, rfl⟩
      exact T.mul_mem ht (hRT hr)
    · intro t ht
      exact ⟨t, ht, 1, R.one_mem, mul_one t⟩
  have h1 : ((A ⊔ R : Subgroup G) : Set G) = (A : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A R hAN
  have h2 : ((A ⊔ R : Subgroup G) : Set G) = (R : Set G) * (A : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left R A hAN
  have h3 : (((A ⊔ R) ⊔ T : Subgroup G) : Set G) = ((A ⊔ R : Subgroup G) : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (A ⊔ R) T hTAR
  have h4 : ((T ⊔ (A ⊔ R) : Subgroup G) : Set G) = (T : Set G) * ((A ⊔ R : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right T (A ⊔ R) hTAR
  calc (A : Set G) * (T : Set G) = (A : Set G) * ((R : Set G) * (T : Set G)) := by rw [hRTset]
    _ = ((A ⊔ R : Subgroup G) : Set G) * (T : Set G) := by rw [h1, mul_assoc]
    _ = (T : Set G) * ((A ⊔ R : Subgroup G) : Set G) := by rw [← h3, ← h4, sup_comm]
    _ = ((T : Set G) * (R : Set G)) * (A : Set G) := by rw [h2, mul_assoc]
    _ = (T : Set G) * (A : Set G) := by rw [hTRset]

end Lem11Borel

open Lem11Borel

theorem lem12211Borel_of (hE : E2.E22StatementC)
    (hTor : E2.E22TorusCover) : Lem12211Borel := by
  intro G _ _ T M H hs hnab hqtke hT hM hTM hNT hHs hn2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hT
  have hmin : MinParabolic H (S : Subgroup G) (H ⊓ M) :=
    ⟨isSylowTwoOf_of_isSylowTwo hT hHs.1.1, fun h => hHs.2.1 (h.trans hNT),
      IsHStar.isUniqueMaxOver S hHs hTM⟩
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hqtke hs hnab hHs.1.2
  have hn1 : 1 < E1.nParam H := lt_of_lt_of_le (by norm_num) hn2
  obtain ⟨n, hn, hnH, -, R, hRT, hR2, hRN, hex, hall⟩ := E2.e22BorelLift hE hTor hmin hSQ hn1
  refine ⟨hex, fun C hCM hCodd hCidx => ?_⟩
  obtain ⟨hCR, -, ⟨⟨hab⟩⟩, Y, hYC, -, hYcard, -⟩ := hall C hCM hCodd hCidx
  have hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab ⟨x, hx⟩ ⟨y, hy⟩)
  have hYdvd : 2 ^ n - 1 ∣ Nat.card C := hYcard ▸ Subgroup.card_dvd_of_le hYC
  refine ⟨?_, fun hcase => ?_⟩
  ·
    intro hbot
    rw [hbot, Subgroup.card_bot] at hYdvd
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := Nat.le_of_dvd one_pos hYdvd
    omega
  obtain ⟨p, hp, hp3, hpC⟩ : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ Nat.card C := by
    rcases hcase with h | h
    · have hn3 : 3 ≤ n := by
        have : (2 : ℕ∞) < n := lt_of_lt_of_le h hnH
        exact_mod_cast Order.add_one_le_of_lt this
      obtain ⟨p, hp, hp3, hpd⟩ := exists_prime_gt_three_dvd hn3
      exact ⟨p, hp, hp3, hpd.trans hYdvd⟩
    · by_contra hcon
      push Not at hcon
      apply h
      have hne : Nat.card C ≠ 0 := Nat.card_pos.ne'
      have h3 : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card C → d = 3 := by
        intro d hd hdv
        have hd3 : d ≤ 3 := by
          by_contra h'
          exact hcon d hd (by omega) hdv
        have hd2 : d ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr hCodd) (even_iff_two_dvd.mpr hdv)
        have := hd.two_le
        omega
      exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hne h3)
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, omegaSub C hC p, hp, hp3, omegaSub_le hC p, ?_, ⟨?_, fun x hx => hx.2⟩, ?_⟩
  ·
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpC
    intro hbot
    have hgA : (g : G) ∈ omegaSub C hC p :=
      ⟨g.2, by rw [← Subgroup.orderOf_coe] at hg; rw [← hg]; exact pow_orderOf_eq_one _⟩
    rw [hbot, Subgroup.mem_bot] at hgA
    rw [← Subgroup.orderOf_coe, hgA, orderOf_one] at hg
    exact hp.one_lt.ne hg
  · exact ⟨⟨fun x y => Subtype.ext (hC x x.2.1 y y.2.1)⟩⟩
  · exact omegaSub_mul_comm hC hCodd hR2 hRT hmin.le hCM hRN hCR p

end CFSG.Quasithin.H13
