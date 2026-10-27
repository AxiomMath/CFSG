module

public import CFSG.Quasithin.Background.F7TwoInvTitsCheck
public import CFSG.Quasithin.Background.F7TwoInvTitsGen
public import CFSG.Quasithin.Background.SmithB45TorTits
public import CFSG.Quasithin.Background.F7TwoDefs

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.B45Tor

theorem exists_comm_orderOf_of_isConj {G : Type*} [Group G] {u₀ u : G} (h : IsConj u₀ u) {n : ℕ}
    (hx : ∃ x : G, orderOf (u₀ * x * u₀⁻¹ * x⁻¹) = n) :
    ∃ x : G, orderOf (u * x * u⁻¹ * x⁻¹) = n := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  obtain ⟨x, hx⟩ := hx
  refine ⟨c * x * c⁻¹, ?_⟩
  have e : c * u₀ * c⁻¹ * (c * x * c⁻¹) * (c * u₀ * c⁻¹)⁻¹ * (c * x * c⁻¹)⁻¹ =
      c * (u₀ * x * u₀⁻¹ * x⁻¹) * c⁻¹ := by group
  rw [e, show c * (u₀ * x * u₀⁻¹ * x⁻¹) * c⁻¹ = MulAut.conj c (u₀ * x * u₀⁻¹ * x⁻¹) from rfl,
    MulEquiv.orderOf_eq, hx]

section Classes


theorem comm_titsGenD_pow_of_check {r : titsD} {a : Array ℕ}
    (hra : Rep 1755 a (r : Equiv.Perm (Fin 1755))) (hsq : r * r = 1) {j : ℕ} (hj : j < 2) {k : ℕ}
    (h : invTitsHasOrder (invTitsComm a titsDerivedArrs[j]!) k = true) :
    (r * titsGenD j hj * r⁻¹ * (titsGenD j hj)⁻¹) ^ k = 1 ∧
      r * titsGenD j hj * r⁻¹ * (titsGenD j hj)⁻¹ ≠ 1 := by
  have hdi : isInvA 1755 titsDerivedArrs[j]! (invCand 1755 titsDerivedArrs[j]!) = true :=
    isInvA_of_allPermsOK titsChains_check.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; omega)
  have hc := rep_invTitsComm hra (titsT_rep (by omega : j < 13)) hdi
  obtain ⟨hpow, hne⟩ := invTitsHasOrder_spec hc h
  have hr2 : (r : Equiv.Perm (Fin 1755)) * r = 1 :=
    congrArg (fun v : titsD => (v : Equiv.Perm (Fin 1755))) hsq
  have hinv : (r : Equiv.Perm (Fin 1755))⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hval : ((r * titsGenD j hj * r⁻¹ * (titsGenD j hj)⁻¹ : titsD) : Equiv.Perm (Fin 1755)) =
      (r : Equiv.Perm (Fin 1755)) * titsT j * ((r : Equiv.Perm (Fin 1755)) * (titsT j)⁻¹) := by
    simp only [titsGenD, Subgroup.coe_mul, Subgroup.coe_inv, hinv, mul_assoc]
  refine ⟨Subtype.ext ?_, fun h1 => hne ?_⟩
  · simp only [Subgroup.coe_pow, hval, Subgroup.coe_one]
    exact hpow
  · rw [← hval, h1]
    rfl

theorem exists_conj_titsZD_comm_orderOf_five :
    ∃ r x : titsD, IsConj titsZD r ∧ orderOf (r * x * r⁻¹ * x⁻¹) = 5 := by
  have h := invTitsZCheck
  simp only [invTitsClassCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hw, hgw⟩, hgi⟩, hsq⟩, ho0⟩, -⟩ := h
  set gD : titsD := ⟨wordIn 13 titsT invTitsZConjWord, wordIn_titsT_mem_titsD _⟩ with hgD
  have hg := rep_wordArr_titsT (w := invTitsZConjWord) hgw
  have hz := rep_wordArr_titsT (w := titsCenterWord) hw
  have hr : Rep 1755 (conjArr (wordArr 1755 titsDerivedArrs invTitsZConjWord)
      (wordArr 1755 titsDerivedArrs titsCenterWord))
      ((gD * titsZD * gD⁻¹ : titsD) : Equiv.Perm (Fin 1755)) :=
    rep_compA (rep_compA hg hz) (rep_inv_of_isInvA hg hgi)
  have hsq' : (gD * titsZD * gD⁻¹) * (gD * titsZD * gD⁻¹) = 1 :=
    Subtype.ext (eq_of_eqA (rep_compA hr hr) rep_idA hsq)
  obtain ⟨hpow, hne⟩ := comm_titsGenD_pow_of_check hr hsq' (by norm_num : 0 < 2) ho0
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨_, _, isConj_iff.2 ⟨gD, rfl⟩, orderOf_eq_prime hpow hne⟩

theorem exists_conj_titsTD_comm_orderOf_five :
    ∃ r x : titsD, IsConj titsTD r ∧ orderOf (r * x * r⁻¹ * x⁻¹) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B45Tor.titsR) 5
    (by rw [card_titsR]; norm_num)
  refine ⟨titsI * titsI, x, isConj_titsTD, ?_⟩
  rw [invOn_titsR x x.2, ← mul_inv_rev, orderOf_inv, ← sq, orderOf_pow' _ two_ne_zero,
    Subgroup.orderOf_coe, hx]
  rfl

theorem titsD_exists_comm_orderOf_five (u : titsD) (hu : orderOf u = 2) :
    ∃ x : titsD, orderOf (u * x * u⁻¹ * x⁻¹) = 5 := by
  rcases titsD_involution_conj u hu with h | h
  · obtain ⟨r, x, hr, hx⟩ := exists_conj_titsZD_comm_orderOf_five
    exact exists_comm_orderOf_of_isConj (hr.symm.trans h) ⟨x, hx⟩
  · obtain ⟨r, x, hr, hx⟩ := exists_conj_titsTD_comm_orderOf_five
    exact exists_comm_orderOf_of_isConj (hr.symm.trans h) ⟨x, hx⟩

end Classes

end CFSG.Quasithin.F7Two
