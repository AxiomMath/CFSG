module

public import CFSG.Sporadic.Co2Smith.HPCore
public import CFSG.Certificates.Kernel.Co2Census.SpinSound
public import Certificates.Kernel.Co2Census.S0

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem nfS_lt (s v : ℕ) : KernelCo2SmithS.nfS s v < 2 ^ 484 := by
  have hm : ∀ l : List ℕ, l.foldr (fun i acc => if v.testBit i then
      mulV (KernelCo2SmithS.hS i) acc else acc) IDP < 2 ^ 484 := by
    intro l
    induction l with
    | nil => exact IDP_lt
    | cons a l ih =>
      rw [List.foldr_cons]
      split_ifs
      · exact mulV_lt _ _
      · exact ih
  unfold KernelCo2SmithS.nfS
  dsimp only
  split
  · exact mulV_lt _ _
  · exact hm _

theorem repK_qElt {e : ℕ} (he : e < 512) :
    repK (qElt e) (KernelCo2SmithS.nfS (e / 256) (e % 256)) :=
  ⟨nfS_lt _ _, by rw [qElt_val he, hR, KernelCo2SmithS.nfRows_eq]⟩

theorem repK_cElt
    {e : ℕ} (he : e < 512) (n : ℕ) :
    repK (cElt e n) (mulV (SK n) (KernelCo2SmithS.nfS (e / 256) (e % 256))) :=
  repK_mul (repK_sElt n) (repK_qElt he)

noncomputable abbrev zPP :
    FibP :=
  cfgCz.zPair covMap coverZ covMap_coverZ

section HP


theorem mkHP_eq_iff' {u u' : FibP} : mkHP u = mkHP u' ↔ u = u' ∨ u = u' * zPP := by
  show (QuotientGroup.mk u : Hprime) = QuotientGroup.mk u' ↔ _
  rw [QuotientGroup.eq, mem_normalClosure_zPair]
  constructor
  · rintro (h | h)
    · exact Or.inl (inv_mul_eq_one.mp h)
    · right
      have h1 : u' = u * cfgCz.zPair covMap coverZ covMap_coverZ := by rw [← h]; group
      change u = u' * cfgCz.zPair covMap coverZ covMap_coverZ
      rw [h1, mul_assoc, zPair_sq, mul_one]
  · rintro (rfl | h)
    · left
      exact inv_mul_cancel _
    · right
      change u = u' * cfgCz.zPair covMap coverZ covMap_coverZ at h
      rw [h, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_eq_of_mul_eq_one_right zPair_sq

theorem zPP_fst : ((zPP.1.1 : Cz) : K) = z0 := cfgCz_zE

theorem zPP_snd : zPP.1.2 = coverZ := rfl

theorem mkHP_eq_same {u u' : FibP} (h : u.1.2 = u'.1.2) :
    mkHP u = mkHP u' ↔ ((u.1.1 : Cz) : K) = u'.1.1 := by
  rw [mkHP_eq_iff']
  constructor
  · rintro (rfl | e)
    · rfl
    · exfalso
      have e2 := congrArg (fun x : FibP => x.1.2) e
      simp only [Subgroup.coe_mul, Prod.snd_mul, zPP_snd] at e2
      rw [h] at e2
      exact coverZ_ne_one (mul_eq_left.mp e2.symm)
  · intro e
    left
    exact Subtype.ext (Prod.ext (Subtype.ext e) h)

theorem mkHP_eq_twist {u u' : FibP} (h : u.1.2 = coverZ * u'.1.2) :
    mkHP u = mkHP u' ↔ ((u.1.1 : Cz) : K) = u'.1.1 * z0 := by
  rw [mkHP_eq_iff']
  constructor
  · rintro (rfl | e)
    · exfalso
      exact coverZ_ne_one (mul_eq_right.mp h.symm)
    · have e1 := congrArg (fun x : FibP => ((x.1.1 : Cz) : K)) e
      simp only [Subgroup.coe_mul, Prod.fst_mul] at e1
      rw [e1, zPP_fst]
  · intro e
    right
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) ?_)
    · simp only [Subgroup.coe_mul, Prod.fst_mul]
      rw [e, zPP_fst]
    · simp only [Subgroup.coe_mul, Prod.snd_mul, zPP_snd]
      rw [h, coverZ_comm]

theorem pgcov_sign {p q : PGcov} (hpq : covMap p = covMap q) {v u1 u2 : List ℕ}
    (h1 : decV u1 = castM (spinHom p : Matrix (Fin 8) (Fin 8) ℤ) *ᵥ decV v)
    (h2 : decV u2 = castM (spinHom q : Matrix (Fin 8) (Fin 8) ℤ) *ᵥ decV v)
    (hne : decV u2 ≠ 0) : (u1 = u2 → p = q) ∧ (u1 = negVP u2 → p = coverZ * q) := by
  have hcase : p = q ∨ p = coverZ * q := by
    have h0 : covMap (p * q⁻¹) = 1 := by rw [map_mul, map_inv, hpq, mul_inv_cancel]
    rcases (covMap_eq_one_iff _).mp h0 with e | e
    · exact Or.inl (mul_inv_eq_one.mp e)
    · exact Or.inr (by rw [← e]; group)
  have hz : castM (spinHom (coverZ * q) : Matrix (Fin 8) (Fin 8) ℤ) =
      -castM (spinHom q : Matrix (Fin 8) (Fin 8) ℤ) := by
    rw [map_mul, Units.val_mul, spinHom_coverZ, neg_one_mul, castM_neg]
  have two0 : ∀ w : Fin 8 → ZMod spP, w = -w → w = 0 := by
    intro w hw
    funext i
    have hi := congrFun hw i
    simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
    have h2 : w i + w i = w i + -w i := congrArg (w i + ·) hi
    rw [add_neg_cancel] at h2
    exact two_mul_eq_zero h2
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rcases hcase with hc | hc
    · exact hc
    · exfalso
      apply hne
      rw [e, h2, hc, hz, Matrix.neg_mulVec] at h1
      rw [h2]
      exact two0 _ h1
  · rcases hcase with hc | hc
    · exfalso
      apply hne
      rw [e, decV_negVP, h2, hc] at h1
      rw [h2]
      exact two0 _ (neg_eq_iff_eq_neg.mp h1)
    · exact hc

end HP

end CertificateChecks.KernelCo2Census

end
