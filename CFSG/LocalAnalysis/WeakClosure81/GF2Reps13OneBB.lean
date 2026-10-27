module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBA
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_prime_sq_dvd_two_pow_sub_one {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he1 : 1 ≤ e) (he6 : e ≤ 6) (hdiv : p ^ 2 ∣ 2 ^ e - 1) : p = 3 ∧ e = 6 := by
  have hpos : 0 < 2 ^ e - 1 := by
    have h : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
    omega
  have h1 : p ^ 2 ≤ 2 ^ e - 1 := Nat.le_of_dvd hpos hdiv
  have h2 : 2 ^ e - 1 ≤ 63 := by
    have h3 : 2 ^ e ≤ 64 := by
      calc 2 ^ e ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) he6
        _ = 64 := by norm_num
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp7 : p ≤ 7 := by nlinarith
  have hpcases : p = 3 ∨ p = 5 ∨ p = 7 := by
    have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have hp6 : p ≠ 6 := fun h => by rw [h] at hp; norm_num at hp
    omega
  rcases hpcases with rfl | rfl | rfl
  · interval_cases e <;> norm_num at hdiv
    norm_num
  · interval_cases e <;> norm_num at hdiv
  · interval_cases e <;> norm_num at hdiv

theorem w16g_false_of_inverted_orderOf_sq (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : orderOf t = 2) (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hgood : 3 < p ∨ InducesTransvection t ⊤) {c : MulAut W}
    (hc : orderOf c = p ^ 2) (hinv : t * c * t⁻¹ = c⁻¹) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have hcp_pow : (c ^ p) ^ p = 1 := by
    rw [← pow_mul, show p * p = p ^ 2 by ring, ← hc, pow_orderOf_eq_one]
  have hcp_ne : c ^ p ≠ 1 := by
    intro h1
    have hdvd : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hc] at hdvd
    have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
    nlinarith [hp.two_le]
  have hcp_ord : orderOf (c ^ p) = p := by
    have hdvd : orderOf (c ^ p) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hcp_pow
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hcp_ne
    · exact h1
  set X₁ : Subgroup (MulAut W) := Subgroup.zpowers (c ^ p) with hX₁def
  have hX₁card : Nat.card X₁ = p := by rw [hX₁def, Nat.card_zpowers, hcp_ord]
  have hX₁ : IsElemAbelianOfRank p 1 ↥X₁ := w16g_isElemAbelianOfRank_one_of_card hp hX₁card
  have hconj : MulAut.conj t (c ^ p) = (c ^ p)⁻¹ := by
    rw [MulAut.conj_apply, w16g_conj_pow_inv hinv p]
  have hinvX₁ : ∀ x ∈ X₁, t * x * t⁻¹ = x⁻¹ := by
    intro x hx
    rw [hX₁def] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    calc t * (c ^ p) ^ k * t⁻¹ = MulAut.conj t ((c ^ p) ^ k) := (MulAut.conj_apply t _).symm
      _ = (MulAut.conj t (c ^ p)) ^ k := map_zpow (MulAut.conj t) (c ^ p) k
      _ = ((c ^ p)⁻¹) ^ k := by rw [hconj]
      _ = ((c ^ p) ^ k)⁻¹ := by rw [inv_zpow]
  set U : Subgroup W := commSub ⊤ X₁ with hUdef
  have hUrank : rk ↥U = 2 * rk ↥(commSub U (Subgroup.zpowers t)) := by
    rw [hUdef]
    exact rk_commSub_eq_two_mul_of_inverted hW ht hp hp2 (by norm_num) hX₁ hinvX₁
  have hrkU6 : rk ↥U ≤ 6 := by
    rw [hUrank]
    have h1 : rk ↥(commSub U (Subgroup.zpowers t)) ≤ 3 :=
      le_trans (rk_mono (commSub_mono le_top le_rfl)) hrk
    omega
  have hrkU2 (htr : InducesTransvection t ⊤) : rk ↥U ≤ 2 := by
    rw [hUrank]
    have h1 : rk ↥(commSub U (Subgroup.zpowers t)) ≤ 1 := by
      rw [← htr.2]
      exact rk_mono (commSub_mono le_top le_rfl)
    omega
  have hU_ne : U ≠ ⊥ := by
    intro hbot
    have hle : (⊤ : Subgroup W) ≤ fixV X₁ := commSub_eq_bot_iff.mp (hUdef ▸ hbot)
    have hcpt : c ^ p = 1 := by
      ext w
      exact hle (Subgroup.mem_top w) (c ^ p) (Subgroup.mem_zpowers (c ^ p))
    exact hcp_ne hcpt
  have hX₁odd : Odd (Nat.card X₁) := by rw [hX₁card]; exact hp.odd_of_ne_two hp2
  have hfixU : U ⊓ fixV X₁ = ⊥ := by
    rw [hUdef, inf_comm]
    exact CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW hX₁odd
  have hcX₁ : ∀ h ∈ Subgroup.zpowers c, ∀ x ∈ X₁, h * x * h⁻¹ ∈ X₁ := by
    intro h hh x hx
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [hX₁def] at hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : Commute (c ^ a) ((c ^ p) ^ b) := by
      rw [show (c ^ p) ^ b = c ^ ((p : ℤ) * b) from (zpow_mul c (p : ℤ) b).symm]
      exact Commute.zpow_zpow_self c a ((p : ℤ) * b)
    have hconj2 : c ^ a * (c ^ p) ^ b * (c ^ a)⁻¹ = (c ^ p) ^ b := by
      rw [hcomm.eq]
      group
    rw [hconj2]
    exact Subgroup.zpow_mem_zpowers (c ^ p) b
  have hUstab : StableUnder (Subgroup.zpowers c) U := by
    rw [hUdef]
    exact stableUnder_commSub hcX₁ (fun _ _ _ _ => Subgroup.mem_top _)
  have hc_stab : c ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hcu
      have h1 : c⁻¹ (c u) ∈ U :=
        hUstab c⁻¹ (Subgroup.inv_mem (Subgroup.zpowers c) (Subgroup.mem_zpowers c)) (c u) hcu
      simpa using h1
    · intro hu
      exact hUstab c (Subgroup.mem_zpowers c) u hu
  let σ : MulAut U := resHom U ⟨c, hc_stab⟩
  have hσp_ne : σ ^ p ≠ 1 := by
    intro hσp
    have hcp_fix : ∀ u : U, (c ^ p) (u : W) = (u : W) := by
      intro u
      have h1 : (σ ^ p) u = u := by rw [hσp]; rfl
      have h2 : (resHom U (⟨c, hc_stab⟩ ^ p)) u = u := by
        rw [map_pow]
        exact h1
      have h3 := congrArg (fun v : U => (v : W)) h2
      rw [resHom_apply] at h3
      simpa using h3
    have hUfix : U ≤ fixV X₁ := by
      intro u hu
      rw [mem_fixV]
      intro x hx
      rw [hX₁def, Subgroup.zpowers_eq_closure] at hx
      refine Subgroup.closure_induction (p := fun y _ => y u = u) ?_ ?_ ?_ ?_ hx
      · rintro y rfl
        exact hcp_fix ⟨u, hu⟩
      · exact MulAut.one_apply W u
      · intro a b _ _ ha hb
        rw [MulAut.mul_apply, hb, ha]
      · intro a _ ha
        rw [← ha, MulAut.inv_apply_self]
        exact ha.symm
    have hbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have h1 : u ∈ U ⊓ fixV X₁ := ⟨hu, hUfix hu⟩
      rw [hfixU] at h1
      exact h1
    exact hU_ne hbot
  have hσp2 : σ ^ (p ^ 2) = 1 := by
    have h1 : (⟨c, hc_stab⟩ : stabSub U) ^ (p ^ 2) = 1 := by
      apply Subtype.ext
      change (c : MulAut W) ^ (p ^ 2) = 1
      rw [← hc, pow_orderOf_eq_one]
    rw [show σ = resHom U ⟨c, hc_stab⟩ from rfl, ← map_pow, h1, map_one]
  have horder : orderOf σ = p ^ 2 := by
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hσp2)
    have hk2 : k = 2 := by
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact hσp_ne (by rw [orderOf_eq_one_iff.mp hk, one_pow])
      have hk1 : k ≠ 1 := by
        rintro rfl
        rw [pow_one] at hk
        exact hσp_ne (by rw [← hk]; exact pow_orderOf_eq_one σ)
      omega
    rw [hk, hk2]
  have hdvd : p ^ 2 ∣ orderOf σ := by rw [horder]
  have hUcard : Nat.card U = 2 ^ rk ↥U := card_eq_two_pow hW U
  obtain ⟨e, he1, heU, hdiv⟩ :=
    CFSG.RankThree.PartTwo.Sec20.prime_pow_dvd_two_pow_sub_one_of_dvd_orderOf
      hUcard σ hp hp2 (by norm_num) hdvd
  have he6 : e ≤ 6 := le_trans heU hrkU6
  obtain ⟨hp3, heq⟩ := w16g_prime_sq_dvd_two_pow_sub_one hp hp2 he1 he6 hdiv
  rcases hgood with hg | hg
  · omega
  · have he2 : e ≤ 2 := le_trans heU (hrkU2 hg)
    omega

end CFSG.LocalAnalysis.WeakClosure81
