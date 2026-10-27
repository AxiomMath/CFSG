module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Tr

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Quasithin.F6.GoldAmL4

instance (priority := high) trDecEq : DecidableEq Tr := fun ⟨v, g⟩ ⟨v', g'⟩ =>
  if h : v = v' ∧ g = g' then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
  else isFalse (fun e => h (by cases e; exact ⟨rfl, rfl⟩))

@[expose] def thA : Tr := rA⁻¹ * rB * rB
@[expose] def thB : Tr := rA * rA * rB
@[expose] def thS : Tr := rS * rR
@[expose] def thR : Tr := rR

@[expose] def thFun (w : Tr) : Tr :=
  thA ^ w.i.val * thB ^ w.j.val * thS ^ w.e.val * thR ^ w.f.val

theorem thFun_mul : ∀ x y : Tr, thFun (x * y) = thFun x * thFun y := by decide +kernel

@[expose] def thetaStd : Tr →* Tr := MonoidHom.mk' thFun thFun_mul

theorem thetaStd_rA : thetaStd rA = rA⁻¹ * rB * rB := by decide +kernel
theorem thetaStd_rB : thetaStd rB = rA * rA * rB := by decide +kernel
theorem thetaStd_rS : thetaStd rS = rS * rR := by decide +kernel
theorem thetaStd_rR : thetaStd rR = rR := by decide +kernel

theorem thetaStd_invol : ∀ w : Tr, thetaStd (thetaStd w) = w := by decide +kernel

theorem thetaStd_zR : thetaStd zR = zR := by decide +kernel

theorem thetaStd_Q2 : ∀ w : Tr, inQ2 w → inQ2 (thetaStd w) := by decide +kernel

theorem thetaStd_alpha : ∀ w : Tr, inQ2 w →
    thetaStd (Fq alpha5 w) = Fq alpha5 (Fq alpha5 (thetaStd w)) := by decide +kernel

theorem tr_hom_ext {E : Type*} [Group E] {f g : Tr →* E} (h1 : f rA = g rA) (h2 : f rB = g rB)
    (h3 : f rS = g rS) (h4 : f rR = g rR) : f = g := by
  ext w
  rw [tr_nf w]
  simp only [map_mul, map_pow, h1, h2, h3, h4]

theorem thetaStd_not_inner : ∀ t : Tr, ∃ w : Tr, inQ2 w ∧ t * thetaStd w * t⁻¹ ≠ w := by
  decide +kernel

theorem Tr_center : ∀ u : Tr, (∀ w : Tr, u * w = w * u) → u = 1 ∨ u = zR := by decide +kernel

theorem rR_ne_zR : rR ≠ zR := by decide +kernel
theorem rR_ne_one : rR ≠ 1 := by decide +kernel

theorem actA_fix : ∀ w : Tr, inQ1 w → actA w = w → w = 1 ∨ w = rR := by decide +kernel

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 1000000 in
theorem classify_tau :
    ∀ ta : Tr, inQ1 ta → ta ^ 4 = 1 → ta * ta ≠ 1 →
    ∀ tb : Tr, actA ta = tb → tb ^ 4 = 1 → ta * tb = tb * ta → actA tb = ta⁻¹ * tb⁻¹ →
    ∀ tr : Tr, inQ1 tr → actA tr = tr → tr * tr = 1 → tr * ta * tr = ta⁻¹ →
      tr * tb * tr = tb⁻¹ →
    ∀ tq : Tr, inQ1 tq → actA tq = tq → (tq * rS) * (tq * rS) = 1 →
      (tq * rS) * ta * (tq * rS) = tb → (tq * rS) * tb * (tq * rS) = ta →
      tr * (tq * rS) * tr = tq * rS →
      (ta = rA ∧ tb = rB ∧ tq * rS = rS ∧ tr = rR) ∨
      (rR * ta * rR = rA ∧ rR * tb * rR = rB ∧ rR * (tq * rS) * rR = rS ∧ tr = rR) ∨
      (ta = thA ∧ tb = thB ∧ tq * rS = thS ∧ tr = thR) ∨
      (rR * ta * rR = thA ∧ rR * tb * rR = thB ∧ rR * (tq * rS) * rR = thS ∧ tr = rR) := by
  decide +kernel

theorem actA_rA : actA rA = rB := by decide +kernel
theorem actA_rB : actA rB = rA⁻¹ * rB⁻¹ := by decide +kernel
theorem actA_rR : actA rR = rR := by decide +kernel

theorem rA_inQ1 : inQ1 rA := by decide +kernel
theorem rB_inQ1 : inQ1 rB := by decide +kernel
theorem rR_inQ1 : inQ1 rR := by decide +kernel
theorem rS_not_inQ1 : ¬ inQ1 rS := by decide +kernel

theorem rS_rB_rS : rS * rB * rS = rA := by decide +kernel

end CFSG.Quasithin.F6.GoldAmL5
