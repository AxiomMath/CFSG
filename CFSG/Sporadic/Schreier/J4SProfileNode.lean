
module

public import CFSG.Sporadic.Schreier.J4SProfileNodeBase1

public import CFSG.Sporadic.Schreier.J4SProfileCheck
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.Schreier.J4SFrattini
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.J4SSylowCheck

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def nfElt
    (n e : ℕ) : J := η n * uElt e

theorem nfElt_eq
    (n e : ℕ) : nfElt n e = etaV (toVecD 11 n) * uElt e := by
  rw [nfElt, etaV_toVecD]

theorem nfElt_inj
    {n e n' e' : ℕ} (hn : n < 2048) (he : e < 1024) (hn' : n' < 2048)
    (he' : e' < 1024) (h : nfElt n e = nfElt n' e') : n = n' ∧ e = e' := by
  rw [nfElt_eq, nfElt_eq] at h
  obtain ⟨h1, h2⟩ := nf_unique he he' h
  exact ⟨toVecD_injective hn hn' h1, h2⟩

theorem nfElt_mem
    (n e : ℕ) : nfElt n e ∈ S0 :=
  S0.mul_mem (N_le_S0 (η_mem_N n)) (U_le_S0 (uElt_mem_U e))

@[expose] def nfMap
    (p : Fin 2048 × Fin 1024) : S0 := ⟨nfElt p.1 p.2, nfElt_mem _ _⟩

theorem uElt_sq
    {e : ℕ} (he : e < 1024) : uElt e * uElt e = uElt squares[e]! :=
  eq_of_actsBy (K.mul_mem (U_le_K (uElt_mem_U e)) (U_le_K (uElt_mem_U e)))
    (U_le_K (uElt_mem_U _)) (actsBy_mul (uElt_acts he) (uElt_acts he))
    ((sq_all e he).2 ▸ uElt_acts (sq_all e he).1)

theorem nfElt_sq
    {n e : ℕ} (he : e < 1024) :
    nfElt n e * nfElt n e = nfElt (stepNF (n, e)).1 (stepNF (n, e)).2 := by
  rw [nfElt_eq, nf_mul _ _ he, (idxU_spec (U.mul_mem (uElt_mem_U e) (uElt_mem_U e))).2,
    uElt_sq he, nfElt_eq, stepNF, toVecD_xor, ← colsMatrix_mulVec]

theorem nfElt_pow
    {n e : ℕ} (hn : n < 2048) (he : e < 1024) :
    ∀ m : ℕ, nfElt n e ^ (2 ^ m) = nfElt (stepNF^[m] (n, e)).1 (stepNF^[m] (n, e)).2 ∧
      (stepNF^[m] (n, e)).1 < 2048 ∧ (stepNF^[m] (n, e)).2 < 1024 := by
  intro m
  induction m with
  | zero => exact ⟨by rw [pow_zero, pow_one]; rfl, hn, he⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨h4, h5⟩ := stepNF_lt h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rw [pow_succ, pow_mul, h1, sq, nfElt_sq h3, Function.iterate_succ_apply']
    · rw [Function.iterate_succ_apply']; exact h4
    · rw [Function.iterate_succ_apply']; exact h5

theorem nfElt_eq_one_iff
    {n e : ℕ} (hn : n < 2048) (he : e < 1024) :
    nfElt n e = 1 ↔ n = 0 ∧ e = 0 := by
  have h1 : (1 : J) = nfElt 0 0 := by rw [nfElt, η_zero, uElt_zero, mul_one]
  constructor
  · intro h
    exact nfElt_inj hn he (by norm_num) (by norm_num) (h.trans h1)
  · rintro ⟨rfl, rfl⟩
    exact h1.symm

theorem orderOf_nfElt
    {n e : ℕ} (hn : n < 2048) (he : e < 1024) :
    orderOf (nfElt n e) = 2 ^ kfun n e := by
  have hk := kfun_lt e he n hn
  obtain ⟨h1, h2⟩ := kfun_spec n e hk
  have hp := nfElt_pow hn he (kfun n e)
  have hpow : nfElt n e ^ (2 ^ kfun n e) = 1 := by
    rw [hp.1, h1]
    exact (nfElt_eq_one_iff (by norm_num) (by norm_num)).2 ⟨rfl, rfl⟩
  obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
  rw [hie]
  congr 1
  by_contra hne
  have hlt : i < kfun n e := lt_of_le_of_ne hi hne
  have hpi := nfElt_pow hn he i
  have : nfElt n e ^ (2 ^ i) = 1 := by rw [← hie]; exact pow_orderOf_eq_one _
  rw [hpi.1, nfElt_eq_one_iff hpi.2.1 hpi.2.2] at this
  exact h2 i hlt (Prod.ext this.1 this.2)

theorem nfMap_bijective :
    Function.Bijective nfMap := by
  constructor
  · rintro ⟨n, e⟩ ⟨n', e'⟩ h
    have h' := Subtype.ext_iff.1 h
    dsimp only [nfMap] at h'
    obtain ⟨h1, h2⟩ := nfElt_inj n.isLt e.isLt n'.isLt e'.isLt h'
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · rintro ⟨s, hs⟩
    obtain ⟨a, e, he, rfl⟩ := exists_nf hs
    refine ⟨(⟨binOf a, binOf_lt a⟩, ⟨e, he⟩), Subtype.ext ?_⟩
    dsimp only [nfMap]
    rw [nfElt, η_binOf_eq]

@[expose] def hcount
    (a : Multiplicative (Fin 5 → ZMod 2)) (d : ℕ) : ℕ :=
  Nat.card {s : S0 // fS0 s = a ∧ orderOf s = d}

theorem fS0_nfMap_iff
    {b : ℕ} (hb : b < 32) (p : Fin 2048 × Fin 1024) :
    fS0 (nfMap p) = Multiplicative.ofAdd (toVecD 5 b) ↔
      ell p.1.val = b % 2 ∧ cTable[p.2.val]! = b / 2 := by
  rw [fS0_apply, nfMap]
  dsimp only
  rw [nfElt_eq, fVec_nf _ p.2.isLt, (ell_eq _ p.1.isLt).2]
  constructor
  · intro h
    have h' := (cons_toVecD_iff b hb _ ((c_all _ p.2.isLt).1) _).1
      (Multiplicative.ofAdd.injective h)
    refine ⟨?_, h'.2⟩
    have hl := (ell_eq _ p.1.isLt).1
    have hb2 : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 h'.1
    rwa [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hb2] at this
  · rintro ⟨h1, h2⟩
    exact congrArg Multiplicative.ofAdd
      ((cons_toVecD_iff b hb _ ((c_all _ p.2.isLt).1) _).2 ⟨by rw [h1], h2⟩)

theorem orderOf_nfMap
    (p : Fin 2048 × Fin 1024) :
    orderOf (nfMap p) = 2 ^ kfun p.1.val p.2.val := by
  rw [← orderOf_injective S0.subtype S0.subtype_injective, nfMap]
  exact orderOf_nfElt p.1.isLt p.2.isLt

theorem hcount_eq
    {b : ℕ} (hb : b < 32) {j : ℕ} :
    hcount (Multiplicative.ofAdd (toVecD 5 b)) (2 ^ j) = profCount b j := by
  classical
  rw [hcount]
  have e : {s : S0 // fS0 s = Multiplicative.ofAdd (toVecD 5 b) ∧ orderOf s = 2 ^ j} ≃
      {p : Fin 2048 × Fin 1024 // ell p.1.val = b % 2 ∧ cTable[p.2.val]! = b / 2 ∧
        kfun p.1.val p.2.val = j} :=
    { toFun := fun s => ⟨(Equiv.ofBijective _ nfMap_bijective).symm s, by
        have hs := (Equiv.ofBijective _ nfMap_bijective).apply_symm_apply s
        obtain ⟨h1, h2⟩ := (fS0_nfMap_iff hb _).1 (by
          rw [Equiv.ofBijective_apply] at hs; rw [hs]; exact s.2.1)
        refine ⟨h1, h2, ?_⟩
        have h3 := s.2.2
        rw [Equiv.ofBijective_apply] at hs
        rw [← hs, orderOf_nfMap] at h3
        exact Nat.pow_right_injective (le_refl 2) h3⟩
      invFun := fun p => ⟨nfMap p, (fS0_nfMap_iff hb _).2 ⟨p.2.1, p.2.2.1⟩, by
        rw [orderOf_nfMap, p.2.2.2]⟩
      left_inv := fun s => Subtype.ext ((Equiv.ofBijective _ nfMap_bijective).apply_symm_apply s)
      right_inv := fun p => Subtype.ext ((Equiv.ofBijective _ nfMap_bijective).symm_apply_apply p) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type_right, profCount]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with hce
  · rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hce, true_and]
  · refine Finset.sum_eq_zero fun n _ => ?_
    rw [ite_eq_right]
    exact fun h => hce h.2.1

@[expose] def hprof
    (a : Fin 5 → ZMod 2) : Fin 5 → ℕ :=
  fun j => hcount (Multiplicative.ofAdd a) (2 ^ j.val)

theorem hprof_eq
    {b : ℕ} (hb : b < 32) (j : Fin 5) :
    hprof (toVecD 5 b) j = (profTable[b]!)[j.val]! := by
  rw [hprof, hcount_eq hb, profCount_eq b hb j.val j.isLt]

theorem R3E_J4_Sylow_two_Frattini_basis_unique_order_profiles :
    (∀ s : S0, orderOf s ∈ ({1, 2, 4, 8, 16} : Set ℕ)) ∧
      hprof (toVecD 5 5) = ![0, 0, 0, 0, 65536] ∧
      hprof (toVecD 5 6) = ![0, 2560, 54784, 8192, 0] ∧
      hprof (toVecD 5 7) = ![0, 1024, 31744, 32768, 0] ∧
      hprof (toVecD 5 8) = ![0, 1024, 39936, 24576, 0] ∧
      hprof (toVecD 5 17) = ![0, 0, 24576, 40960, 0] ∧
      (∀ a ∈ ({5, 6, 7, 8, 17} : Set ℕ), ∀ w : Fin 5 → ZMod 2,
        hprof w = hprof (toVecD 5 a) → w = toVecD 5 a) ∧
      (∀ w : Fin 5 → ZMod 2, ∃ c : Fin 5 → ZMod 2,
        ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = w) ∧
      (∀ c : Fin 5 → ZMod 2, ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = 0 → c = 0) := by
  have hrow : ∀ b < 32, hprof (toVecD 5 b) = fun j : Fin 5 => (profTable[b]!)[j.val]! :=
    fun b hb => funext (hprof_eq hb)
  refine ⟨fun s => ?_, ?_, ?_, ?_, ?_, ?_, fun a ha w hw => ?_, basis_five_span,
    basis_five_indep⟩
  · obtain ⟨p, rfl⟩ := nfMap_bijective.2 s
    rw [orderOf_nfMap]
    have := kfun_lt p.2.val p.2.isLt p.1.val p.1.isLt
    interval_cases kfun p.1.val p.2.val <;> simp
  · rw [hrow 5 (by norm_num)]; funext j; fin_cases j <;> rfl
  · rw [hrow 6 (by norm_num)]; funext j; fin_cases j <;> rfl
  · rw [hrow 7 (by norm_num)]; funext j; fin_cases j <;> rfl
  · rw [hrow 8 (by norm_num)]; funext j; fin_cases j <;> rfl
  · rw [hrow 17 (by norm_num)]; funext j; fin_cases j <;> rfl
  · obtain ⟨b, hb, rfl⟩ := toVecD_five_surj w
    have ha' : a < 32 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> norm_num
    rw [hrow b hb, hrow a ha'] at hw
    have heq : profTable[b]! = profTable[a]! := by
      refine Array.ext (by rw [(profTable_size.2 b hb), (profTable_size.2 a ha')]) fun j h1 h2 => ?_
      have hj : j < 5 := (profTable_size.2 b hb) ▸ h1
      have h3 : (profTable[b]!)[j]! = (profTable[a]!)[j]! := congrFun hw ⟨j, hj⟩
      rwa [getElem!_pos (profTable[b]!) j h1, getElem!_pos (profTable[a]!) j h2] at h3
    have ha'' : a ∈ [5, 6, 7, 8, 17] := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp
    rw [profTable_unique a ha'' b hb heq]

end CFSG.Sporadic.J4Schreier
