module

public import Certificates.Kernel.Co2Census.HPRepK
public import Certificates.Kernel.Co2Census.HPDefs
public import Certificates.Kernel.Co2Census.Fibre
public import Certificates.Kernel.Co2Census.SpinG

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem length_spinMV
    (n : ℕ) (v : List ℕ) :
    (spinMV n v).length = 8 := by
  rw [spinMV, length_mvRP]
  exact (tsp_spec' (k := 0) (i := n % 63) (by norm_num)
    (by rw [show Native.chainOrb[0]! = 63 from rfl]; omega) (j := n % 63)
    (by rw [show trOff 0 = 0 from rfl, Nat.zero_add])).1.1

theorem spin_one
    (a : ℕ) :
    decV (spinMV a v0) = castM (spinHom (pLift a) : Matrix (Fin 8) (Fin 8) ℤ) *ᵥ decV v0 :=
  spinMV_spec a rfl

theorem spin_prod
    (a b : ℕ) :
    decV (spinMV a (spinMV b v0)) =
      castM (spinHom (pLift a * pLift b) : Matrix (Fin 8) (Fin 8) ℤ) *ᵥ decV v0 := by
  rw [spinMV_spec a (length_spinMV b v0), spin_one b, map_mul, Units.val_mul, castM_mul,
    Matrix.mulVec_mulVec]

theorem decV_ne_zero_of_nzV {b : List ℕ} (hb : b.length = 8) (h : nzV b = true) :
    decV b ≠ 0 := by
  unfold nzV at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hx'⟩ := h
  rw [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at hx'
  have hx0 : x ≠ 0 := Nat.ne_of_beq_eq_false hx'.1
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  intro h0
  have h1 := congrFun h0 ⟨i, by omega⟩
  simp only [decV, Pi.zero_apply] at h1
  rw [List.getD_eq_getElem _ _ hi, ZMod.natCast_eq_zero_iff] at h1
  exact hx0 (Nat.eq_zero_of_dvd_of_lt h1 hx'.2)

section HP


theorem sign_cases {p q : PGcov} (hpq : covMap p = covMap q) {u1 u2 : List ℕ}
    (h1 : decV u1 = castM (spinHom p : Matrix (Fin 8) (Fin 8) ℤ) *ᵥ decV v0)
    (h2 : decV u2 = castM (spinHom q : Matrix (Fin 8) (Fin 8) ℤ) *ᵥ decV v0)
    (hl : u2.length = 8) (hnz : nzV u2 = true) (hs : sgnV u1 u2 < 2) :
    (sgnV u1 u2 = 0 ∧ p = q) ∨ (sgnV u1 u2 = 1 ∧ p = coverZ * q) := by
  have hsg := pgcov_sign hpq h1 h2 (decV_ne_zero_of_nzV hl hnz)
  unfold sgnV at hs ⊢
  by_cases e1 : (u1 == u2) = true
  · rw [if_pos e1]
    exact Or.inl ⟨rfl, hsg.1 (beq_iff_eq.mp e1)⟩
  · rw [if_neg e1] at hs ⊢
    by_cases e2 : (u1 == negVP u2) = true
    · rw [if_pos e2]
      exact Or.inr ⟨rfl, hsg.2 (beq_iff_eq.mp e2)⟩
    · rw [if_neg e2] at hs
      exact absurd hs (by norm_num)

theorem repK_z0 (hz : Z0 < 2 ^ 484) : repK z0 Z0 :=
  ⟨hz, by rw [rows_z0, Z0, KernelCo2SmithS.seeds_get 0 (by norm_num)]⟩

theorem repK_twist (hz : Z0 < 2 ^ 484) {x : K} {X : ℕ} (hX : repK x X) (k : ℕ) :
    repK (if k = 1 then x * z0 else x) (twistK k X) := by
  unfold twistK
  split_ifs
  · exact repK_mul hX (repK_z0 hz)
  · exact hX

theorem mkHP_iff_sign (hz : Z0 < 2 ^ 484) {u u' : FibP} {k : ℕ}
    (hk : (k = 0 ∧ u.1.2 = u'.1.2) ∨ (k = 1 ∧ u.1.2 = coverZ * u'.1.2)) {X X' : ℕ}
    (hX : repK ((u.1.1 : Cz) : K) X) (hX' : repK ((u'.1.1 : Cz) : K) X') :
    mkHP u = mkHP u' ↔ X = twistK k X' := by
  rcases hk with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [mkHP_eq_same h]
    constructor
    · intro e
      rw [e] at hX
      exact repK_unique hX hX'
    · intro e
      rw [twistK, if_neg (by norm_num)] at e
      rw [e] at hX
      exact repK_fun hX hX'
  · rw [mkHP_eq_twist h]
    have ht := repK_twist hz hX' 1
    rw [if_pos rfl] at ht
    constructor
    · intro e
      rw [e] at hX
      exact repK_unique hX ht
    · intro e
      rw [e] at hX
      exact repK_fun hX ht

@[expose] noncomputable def piK : Hprime →* K := S0.subtype.comp piHP

theorem piK_hpElt (e n : ℕ) : piK (hpElt e n) = sElt n := piHP_hpElt e n

theorem piK_mkHP (u : FibP) : piK (mkHP u) = (covMap u.1.2 : K) := rfl

@[expose] def hpPred (r c : Hprime) (comm : Bool) (y : Hprime) : Prop :=
  (comm = true → y * r = r * y) ∧ y * y = c

theorem fpElt_snd (e n : ℕ) : (fpElt e n).1.2 = pLift n := rfl

theorem fpElt_fst (e n : ℕ) : ((fpElt e n).1.1 : K) = cElt e n := rfl

theorem fib_hp_eq (hz : Z0 < 2 ^ 484) {QK : ℕ → ℕ}
    (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256))
    {ur uc : FibP} {nr nc RR CR : ℕ} (hrC : repK ((ur.1.1 : Cz) : K) RR)
    (hrP : ur.1.2 = pLift nr) (hcC : repK ((uc.1.1 : Cz) : K) CR) (hcP : uc.1.2 = pLift nc)
    (comm : Bool) {n : ℕ} (hn : n < 1451520) (hok : fcOK n nr nc comm = true) :
    fib piK (hpPred (mkHP ur) (mkHP uc) comm) (sElt n) = fcK QK n nr nc RR CR comm := by
  classical
  rw [fib_elt (elt := hpElt) exists_hpElt (fun e e' n n' he he' hn hn' h =>
    hpElt_injOn he he' hn hn' h) piK_hpElt _ hn]
  have hY : ∀ e < 512, repK (cElt e n) (mulV (SK n) (QK e)) := fun e he => by
    rw [hQK e he]
    exact repK_cElt he n
  unfold fcK
  rw [strictN_eq', strictN_eq']
  by_cases hs : s0Cond n nr nc comm = true
  · rw [if_pos hs, strictN_eq', strictN_eq', strictN_eq', strictN_eq', length_filter_range]
    unfold fcOK at hok
    rw [hs, Bool.not_true, Bool.false_or] at hok
    unfold s0Cond at hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq,
      Nat.blt_eq] at hs hok
    have hsq : sElt n * sElt n = sElt nc := repK_fun (hs.1 ▸ repK_mul (repK_sElt n) (repK_sElt n))
      (repK_sElt nc)
    have hcov2 : covMap (pLift n * pLift n) = covMap (pLift nc) := by
      simp only [map_mul, covMap_pLift']
      exact Subtype.ext hsq
    have hk2 := sign_cases hcov2 (spin_prod n n) (spin_one nc) (length_spinMV _ _) hok.2 hok.1.2
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro e he
    have he := Finset.mem_range.1 he
    rw [letB_eq]
    have hy := hY e he
    have hsqE : hpElt e n * hpElt e n = mkHP uc ↔
        mulV (mulV (SK n) (QK e)) (mulV (SK n) (QK e)) = twistK (kSq n nc) CR := by
      change mkHP (fpElt e n) * mkHP (fpElt e n) = mkHP uc ↔ _
      rw [← map_mul]
      refine mkHP_iff_sign hz ?_ (repK_mul hy hy) hcC
      rcases hk2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inl ⟨h0, by rw [hcP]; exact h1⟩
      · exact Or.inr ⟨h0, by rw [hcP]; exact h1⟩
    unfold hpPred
    rw [Bool.and_eq_true, Nat.beq_eq, ← hsqE]
    cases hcm : comm
    · simp
    · rw [hcm] at hs hok
      simp only [Bool.not_true, Bool.false_or, true_implies, Bool.true_eq_false, false_or]
        at hs hok ⊢
      have hcomm : sElt n * sElt nr = sElt nr * sElt n :=
        repK_fun (hs.2 ▸ repK_mul (repK_sElt n) (repK_sElt nr))
          (repK_mul (repK_sElt nr) (repK_sElt n))
      have hcov1 : covMap (pLift n * pLift nr) = covMap (pLift nr * pLift n) := by
        simp only [map_mul, covMap_pLift']
        exact Subtype.ext hcomm
      have hk1 := sign_cases hcov1 (spin_prod n nr) (spin_prod nr n) (length_spinMV _ _)
        hok.1.1.2 hok.1.1.1
      have hrep : hpElt e n * mkHP ur = mkHP ur * hpElt e n ↔
          mulV (mulV (SK n) (QK e)) RR = twistK (kComm n nr) (mulV RR (mulV (SK n) (QK e))) := by
        change mkHP (fpElt e n) * mkHP ur = mkHP ur * mkHP (fpElt e n) ↔ _
        rw [← map_mul, ← map_mul]
        refine mkHP_iff_sign hz ?_ (repK_mul hy hrC) (repK_mul hrC hy)
        rcases hk1 with ⟨h0, h1⟩ | ⟨h0, h1⟩
        · refine Or.inl ⟨h0, ?_⟩
          change pLift n * ur.1.2 = ur.1.2 * pLift n
          rw [hrP]
          exact h1
        · refine Or.inr ⟨h0, ?_⟩
          change pLift n * ur.1.2 = coverZ * (ur.1.2 * pLift n)
          rw [hrP]
          exact h1
      rw [hrep, Nat.beq_eq]
      exact and_comm
  · rw [if_neg hs]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hP
    apply hs
    have he' := Finset.mem_range.1 he
    have hy := hY e he'
    obtain ⟨hcm, hsq⟩ := hP
    unfold s0Cond
    rw [Bool.and_eq_true, Nat.beq_eq]
    have h1 := congrArg piK hsq
    rw [map_mul, piK_hpElt, piK_mkHP, hcP, covMap_pLift] at h1
    refine ⟨repK_unique (h1 ▸ repK_mul (repK_sElt n) (repK_sElt n)) (repK_sElt nc), ?_⟩
    cases hc : comm
    · rfl
    · have h2 := congrArg piK (hcm hc)
      rw [map_mul, map_mul, piK_hpElt, piK_mkHP, hrP, covMap_pLift] at h2
      rw [Bool.not_true, Bool.false_or, Nat.beq_eq]
      exact repK_unique (h2 ▸ repK_mul (repK_sElt n) (repK_sElt nr))
        (repK_mul (repK_sElt nr) (repK_sElt n))

end HP

end CertificateChecks.KernelCo2Census

end
