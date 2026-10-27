module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z6c
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z4c
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z2

public section

namespace CFSG.Quasithin.Stellmacher.PU.L3YC.M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open CFSG.Quasithin.A312M24
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.QuasithinUnique
open scoped Pointwise

theorem idx_63_dvd : ∀ j < 13, 63 ∣ memIdx[j]! → j = 1 ∨ j = 2 := by decide

theorem Z6_le_Z2 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Z6 ≤ Z2 := by
  let W : Subgroup G24 := Subgroup.closure {x | x ∈ gens2 ++ gens6}
  have hZ2W : Z2 ≤ W := Subgroup.closure_mono (fun x hx => List.mem_append_left _ hx)
  have hZ6W : Z6 ≤ W := Subgroup.closure_mono (fun x hx => List.mem_append_right _ hx)
  have hWinv : ∀ z ∈ W, ∀ x ∈ T2, z • x ∈ T2 :=
    inv_list_of_gens (gens2 ++ gens6) T2 fun g hg x hx => by
      rw [hact_set]
      rcases List.mem_append.mp hg with hg | hg
      · exact T2_gens _ (by rw [← gens2_tab]; exact List.mem_map_of_mem hg) x hx
      · exact T2_gens6 _ (by rw [← gens6_tab]; exact List.mem_map_of_mem hg) x hx
  have hSW : m24CtxE.S ≤ W := S_le_Z2.trans hZ2W
  have hWtop : W ≠ ⊤ := by
    intro h
    have hm : m24b ∈ W := h ▸ Subgroup.mem_top _
    have h1 := hWinv _ hm ({0, 2, 3, 7, 10, 15, 17, 21} : Finset ℕ) (by decide)
    rw [hact_set, m24_tab_b] at h1
    revert h1
    decide +kernel
  obtain ⟨j, hj, hWj, hc⟩ := overgroup_member hSW hWtop
  have h63 : 63 ∣ memIdx[j]! := by
    have h1 : Nat.card Z2 ∣ Nat.card W := Subgroup.card_dvd_of_le hZ2W
    rw [Z2_eq_Y2.1, hc] at h1
    omega
  rcases idx_63_dvd j hj h63 with rfl | rfl
  · exfalso
    have hy : y1 ∈ W := by
      rw [hWj, ← Z1_eq_Y1.2]
      exact y1_mem
    have h1 := hWinv _ hy ({0, 2, 3, 7, 10, 15, 17, 21} : Finset ℕ) (by decide)
    rw [hact_set, tab_y1] at h1
    revert h1
    decide +kernel
  · have hcard : Nat.card W = Nat.card Z2 := by rw [hc, Z2_eq_Y2.1]; rfl
    have : Z2 = W := Subgroup.eq_of_le_of_card_ge hZ2W (by rw [hcard])
    exact hZ6W.trans this.ge

@[expose] def omega : G24 := y2 ^ 7

theorem tab_omega : tab 24 omega = powTabL 24 y2T 7 := by
  rw [omega, tab_pow_L, tab_y2]

theorem omega_mem : omega ∈ Z2 := Subgroup.pow_mem _ y2_mem 7

theorem omega_pow_three : omega ^ 3 = 1 := by
  apply eq_of_tab_eq (n := 24)
  rw [tab_pow_L, tab_omega, tab_one_L]
  decide +kernel

theorem rho2_omega : rho2 ⟨omega, omega_mem⟩ ≠ 1 := by
  intro h
  have := listHom_val Z2 T2 T2_nodup Z2_inv ⟨omega, omega_mem⟩ ⟨0, by decide⟩
  rw [show listHom Z2 T2 T2_nodup Z2_inv ⟨omega, omega_mem⟩ = 1 from h] at this
  simp only [hact_set, tab_omega] at this
  revert this
  decide +kernel

theorem rho2_s0 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    rho2 ⟨s0, Z6_le_Z2 s0_mem⟩ ≠ 1 := by
  intro h
  have := listHom_val Z2 T2 T2_nodup Z2_inv ⟨s0, Z6_le_Z2 s0_mem⟩ ⟨0, by decide⟩
  rw [show listHom Z2 T2 T2_nodup Z2_inv ⟨s0, Z6_le_Z2 s0_mem⟩ = 1 from h] at this
  simp only [hact_set, tab_s0] at this
  revert this
  decide +kernel

theorem card_rho2 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Nat.card rho2.range = 6 ∧ Nat.card rho2.ker = 10752 := by
  have hperm : Nat.card (Equiv.Perm (Fin T2.length)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hdvd : Nat.card rho2.range ∣ 6 := hperm ▸ Subgroup.card_subgroup_dvd_card rho2.range
  have h3 : 3 ∣ Nat.card rho2.range := by
    have hx : rho2 ⟨omega, omega_mem⟩ ∈ rho2.range := ⟨_, rfl⟩
    have hord : orderOf (rho2 ⟨omega, omega_mem⟩) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine orderOf_eq_prime ?_ rho2_omega
      rw [← map_pow]
      have : (⟨omega, omega_mem⟩ : ↥Z2) ^ 3 = 1 := Subtype.ext (by simpa using omega_pow_three)
      rw [this, map_one]
    exact hord ▸ Subgroup.orderOf_dvd_natCard rho2.range hx
  have h2 : 2 ∣ Nat.card rho2.range := by
    have hx : rho2 ⟨s0, Z6_le_Z2 s0_mem⟩ ∈ rho2.range := ⟨_, rfl⟩
    have hs0 : s0 ∈ m24CtxE.S := by
      have : s0 ∈ Subgroup.closure {x | x ∈ m24Sg} := evalEltL_mem m24Sg
        (fun _ hx => Subgroup.subset_closure hx) [0]
      have hSeq : Subgroup.closure {x | x ∈ m24Sg} = m24CtxE.S := m24CtxE.hSeq
      rwa [hSeq] at this
    obtain ⟨k, hk⟩ := m24_S_isPGroup ⟨s0, hs0⟩
    have hpow : (rho2 ⟨s0, Z6_le_Z2 s0_mem⟩) ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      have : (⟨s0, Z6_le_Z2 s0_mem⟩ : ↥Z2) ^ (2 ^ k) = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      rw [this, map_one]
    have hdv : orderOf (rho2 ⟨s0, Z6_le_Z2 s0_mem⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdv
    have hne : orderOf (rho2 ⟨s0, Z6_le_Z2 s0_mem⟩) ≠ 1 := by
      intro h1
      exact rho2_s0 (orderOf_eq_one_iff.mp h1)
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hio)
    have : 2 ∣ orderOf (rho2 ⟨s0, Z6_le_Z2 s0_mem⟩) := by
      rw [hio]
      exact dvd_pow_self 2 hi0
    exact this.trans (Subgroup.orderOf_dvd_natCard rho2.range hx)
  have h6 : Nat.card rho2.range = 6 := by
    have h6d : 6 ∣ Nat.card rho2.range := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    exact Nat.dvd_antisymm hdvd h6d
  refine ⟨h6, ?_⟩
  have h := card_ker_mul rho2
  rw [Z2_eq_Y2.1, h6] at h
  omega

end CFSG.Quasithin.Stellmacher.PU.L3YC.M24
