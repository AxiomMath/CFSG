module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitWeylGen
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.QTwo

private def qtwoDB36_signUnit {m : ℕ} (T : Finset (Fin m)) : Fin m → (ZMod 3)ˣ :=
  fun k => if k ∈ T then -1 else 1

private def qtwoDB36_sign {m : ℕ} (T : Finset (Fin m)) : Fin m → ZMod 3 :=
  fun k => if k ∈ T then -1 else 1

private lemma qtwoDB36_signUnit_coe {m : ℕ} (T : Finset (Fin m)) (k : Fin m) :
    ((qtwoDB36_signUnit T k : (ZMod 3)ˣ) : ZMod 3) = qtwoDB36_sign T k := by
  by_cases h : k ∈ T <;> simp [qtwoDB36_signUnit, qtwoDB36_sign, h]

private lemma qtwoDB36_sign_ne_zero {m : ℕ} (T : Finset (Fin m)) (k : Fin m) :
    qtwoDB36_sign T k ≠ 0 := by
  by_cases h : k ∈ T <;> simp [qtwoDB36_sign, h]

private lemma qtwoDB36_mem_iff_sign_eq_neg_one {m : ℕ} (T : Finset (Fin m)) (j : Fin m) :
    j ∈ T ↔ qtwoDB36_sign T j = -1 := by
  by_cases h : j ∈ T <;> simp [qtwoDB36_sign, h]
  decide

private lemma qtwoDB36_prod_sign {m : ℕ} (T : Finset (Fin m)) :
    ∏ i : Fin m, qtwoDB36_sign T i = (-1 : ZMod 3) ^ T.card := by
  simp only [qtwoDB36_sign]
  rw [Fintype.prod_ite_mem, Finset.prod_const]

private lemma qtwoDB36_diag_perm_apply {m : ℕ} (T : Finset (Fin m))
    (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (ZS.diagMap 3 (dBasis m) (qtwoDB36_signUnit T) * dPerm m σ) (dBasis m i) =
      qtwoDB36_sign T (σ i) • dBasis m (σ i) := by
  rw [LinearEquiv.mul_apply, dPerm_apply, ZS.diagMap_apply_basis, qtwoDB36_signUnit_coe]

private lemma qtwoDB36_smul_basis_inj {m : ℕ} {x y : ZMod 3} {i j : Fin m} (hx : x ≠ 0)
    (h : x • dBasis m i = y • dBasis m j) : i = j := by
  by_contra hne
  have hval := congrFun h i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hval
  simp only [dBasis, Pi.basisFun_apply] at hval
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, mul_zero, mul_one] at hval
  exact hx hval

private lemma qtwoDB36_smul_basis_eq {m : ℕ} {x y : ZMod 3} {i j : Fin m} (hx : x ≠ 0)
    (h : x • dBasis m i = y • dBasis m j) : i = j ∧ x = y := by
  have hij : i = j := qtwoDB36_smul_basis_inj hx h
  refine ⟨hij, ?_⟩
  rw [← hij] at h
  have hval := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply, Pi.single_eq_same,
    mul_one] at hval
  exact hval

private lemma qtwoDB36_single_eq_dBasis (m : ℕ) (c : Fin m) :
    Pi.single c 1 = dBasis m c := by
  rw [dBasis, Pi.basisFun_apply]

private def qtwoDB36_parityFlip {ι : Type*} [DecidableEq ι] (i : ι) (s : Finset ι) :
    Finset ι :=
  if i ∈ s then s.erase i else insert i s

private theorem qtwoDB36_parityFlip_parityFlip {ι : Type*} [DecidableEq ι] (i : ι)
    (s : Finset ι) : qtwoDB36_parityFlip i (qtwoDB36_parityFlip i s) = s := by
  by_cases h : i ∈ s
  · simp [qtwoDB36_parityFlip, h, Finset.insert_erase h]
  · simp [qtwoDB36_parityFlip, h, Finset.erase_insert h]

private theorem qtwoDB36_even_card_parityFlip {ι : Type*} [DecidableEq ι] (i : ι)
    (s : Finset ι) : Even (qtwoDB36_parityFlip i s).card ↔ ¬ Even s.card := by
  by_cases h : i ∈ s
  · have h1 : 1 ≤ s.card := Finset.card_pos.mpr ⟨i, h⟩
    simp [qtwoDB36_parityFlip, h, Finset.card_erase_of_mem h, Nat.even_sub h1]
  · simp [qtwoDB36_parityFlip, h, Finset.card_insert_of_notMem h, Nat.even_add_one]

private theorem qtwoDB36_card_even_finset {ι : Type*} [Fintype ι] [Nonempty ι] :
    Nat.card {S : Finset ι // Even S.card} = 2 ^ (Nat.card ι - 1) := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hbij : (Finset.univ.filter fun s : Finset ι => Even s.card).card
      = (Finset.univ.filter fun s : Finset ι => ¬ Even s.card).card := by
    refine Finset.card_bij' (fun s _ => qtwoDB36_parityFlip i s)
      (fun s _ => qtwoDB36_parityFlip i s) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact fun hcon => (qtwoDB36_even_card_parityFlip i s).mp hcon hs
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact (qtwoDB36_even_card_parityFlip i s).mpr hs
    · intro s _
      exact qtwoDB36_parityFlip_parityFlip i s
    · intro s _
      exact qtwoDB36_parityFlip_parityFlip i s
  have htot : (Finset.univ.filter fun s : Finset ι => Even s.card).card
      + (Finset.univ.filter fun s : Finset ι => ¬ Even s.card).card
        = 2 ^ Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_finset]
  have hpow : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  omega

private abbrev qtwoDB36_PermStab (m : ℕ) (c : Fin m) : Type :=
  {σ : Equiv.Perm (Fin m) // ∀ a, ¬(a ≠ c) → σ a = a}

private abbrev qtwoDB36_Subsets (m : ℕ) (c : Fin m) : Type :=
  {T : Finset (Fin m) // c ∉ T ∧ Even T.card}

private abbrev qtwoDB36_Pairs (m : ℕ) (c : Fin m) : Type :=
  qtwoDB36_PermStab m c × qtwoDB36_Subsets m c

private noncomputable def qtwoDB36_ofPair (m : ℕ) (c : Fin m) :
    qtwoDB36_Pairs m c → dEvenStab m (Pi.single c 1) := fun p => by
  refine ⟨ZS.diagMap 3 (dBasis m) (qtwoDB36_signUnit p.2.1) * dPerm m p.1.1, ?_, ?_⟩
  · refine ⟨p.1.1, fun i => qtwoDB36_sign p.2.1 (p.1.1 i), ?_, ?_, ?_⟩
    · intro i
      by_cases h : p.1.1 i ∈ p.2.1 <;> simp [qtwoDB36_sign, h]
    · dsimp only
      rw [Equiv.prod_comp p.1.1 (qtwoDB36_sign p.2.1), qtwoDB36_prod_sign]
      exact (neg_one_pow_eq_one_iff_even (show (-1 : ZMod 3) ≠ 1 by decide)).mpr p.2.2.2
    · intro i
      rw [qtwoDB36_diag_perm_apply]
  · rw [qtwoDB36_single_eq_dBasis]
    rw [qtwoDB36_diag_perm_apply, p.1.2 c (by simp)]
    have hc : qtwoDB36_sign p.2.1 c = 1 := by
      simp only [qtwoDB36_sign]
      rw [if_neg]
      exact p.2.2.1
    rw [hc, one_smul]

private lemma qtwoDB36_ofPair_val (m : ℕ) (c : Fin m) (p : qtwoDB36_Pairs m c) :
    (qtwoDB36_ofPair m c p).1
      = ZS.diagMap 3 (dBasis m) (qtwoDB36_signUnit p.2.1) * dPerm m p.1.1 := rfl

private theorem qtwoDB36_ofPair_injective (m : ℕ) (c : Fin m) :
    Function.Injective (qtwoDB36_ofPair m c) := by
  intro p q hpq
  have hval : (ZS.diagMap 3 (dBasis m) (qtwoDB36_signUnit p.2.1) * dPerm m p.1.1)
      = (ZS.diagMap 3 (dBasis m) (qtwoDB36_signUnit q.2.1) * dPerm m q.1.1) := by
    rw [← qtwoDB36_ofPair_val m c p, ← qtwoDB36_ofPair_val m c q]
    exact congrArg Subtype.val hpq
  have hstep : ∀ k : Fin m,
      qtwoDB36_sign p.2.1 (p.1.1 k) • dBasis m (p.1.1 k)
        = qtwoDB36_sign q.2.1 (q.1.1 k) • dBasis m (q.1.1 k) := by
    intro k
    have hk := congrArg (fun (f : DVec m ≃ₗ[ZMod 3] DVec m) => f (dBasis m k)) hval
    rwa [qtwoDB36_diag_perm_apply, qtwoDB36_diag_perm_apply] at hk
  have hσ : p.1.1 = q.1.1 := by
    refine Equiv.ext fun k => ?_
    exact (qtwoDB36_smul_basis_eq (qtwoDB36_sign_ne_zero p.2.1 (p.1.1 k)) (hstep k)).1
  have hsign : qtwoDB36_sign p.2.1 = qtwoDB36_sign q.2.1 := by
    funext j
    obtain ⟨k, hk⟩ := p.1.1.surjective j
    have hcoef :=
      (qtwoDB36_smul_basis_eq (qtwoDB36_sign_ne_zero p.2.1 (p.1.1 k)) (hstep k)).2
    rw [← hσ, hk] at hcoef
    exact hcoef
  have hT : p.2.1 = q.2.1 := by
    apply Finset.ext
    intro j
    rw [qtwoDB36_mem_iff_sign_eq_neg_one, qtwoDB36_mem_iff_sign_eq_neg_one, hsign]
  exact Prod.ext (Subtype.ext hσ) (Subtype.ext hT)

private theorem qtwoDB36_ofPair_surjective (m : ℕ) (c : Fin m) :
    Function.Surjective (qtwoDB36_ofPair m c) := by
  intro w
  obtain ⟨σ, T, hσc, hcT, heven, hact⟩ := ggQTwoDUnit_dEven_fix_decomp w.2.1 w.2.2
  refine ⟨(⟨σ, fun a ha => ?_⟩, ⟨T, hcT, heven⟩), ?_⟩
  · have ha' : a = c := not_not.mp ha
    simp [ha', hσc]
  · refine Subtype.ext ?_
    rw [qtwoDB36_ofPair_val]
    refine (dBasis m).ext' fun k => ?_
    rw [qtwoDB36_diag_perm_apply, hact k]
    by_cases h : σ k ∈ T
    · simp only [qtwoDB36_sign, h, if_true]
      rfl
    · simp only [qtwoDB36_sign, h, if_false]

private lemma qtwoDB36_card_compl (m : ℕ) (c : Fin m) :
    Nat.card {x : Fin m // x ≠ c} = m - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]

private theorem qtwoDB36_card_permStab (m : ℕ) (c : Fin m) :
    Nat.card (qtwoDB36_PermStab m c) = (m - 1).factorial := by
  classical
  have h := Nat.card_congr
    (Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin m => x ≠ c))
  rw [← h, Nat.card_perm, qtwoDB36_card_compl]

private noncomputable def qtwoDB36_subsetsEquiv (m : ℕ) (c : Fin m) :
    qtwoDB36_Subsets m c ≃ {S : Finset {x : Fin m // x ≠ c} // Even S.card} where
  toFun T := ⟨T.1.subtype (fun x => x ≠ c), by
    rw [Finset.card_subtype]
    have hf : T.1.filter (fun x => x ≠ c) = T.1 := by
      apply Finset.filter_true_of_mem
      intro x hx hxc
      exact T.2.1 (hxc ▸ hx)
    rw [hf]
    exact T.2.2⟩
  invFun S := ⟨S.1.map (Function.Embedding.subtype (fun x : Fin m => x ≠ c)), by
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_map]
      rintro ⟨x, -, hx⟩
      exact x.2 hx
    · rw [Finset.card_map]
      exact S.2⟩
  left_inv T := by
    apply Subtype.ext
    refine Finset.subtype_map_of_mem (fun x hx => ?_)
    intro hxc
    exact T.2.1 (hxc ▸ hx)
  right_inv S := by
    apply Subtype.ext
    apply Finset.ext
    intro a
    rw [Finset.mem_subtype, Finset.mem_map]
    constructor
    · rintro ⟨b, hb, hba⟩
      have hba' : b = a := Subtype.ext hba
      rwa [hba'] at hb
    · intro ha
      exact ⟨a, ha, rfl⟩

private theorem qtwoDB36_card_subsets (m : ℕ) (c : Fin m) (hm : 2 ≤ m) :
    Nat.card (qtwoDB36_Subsets m c) = 2 ^ (m - 2) := by
  classical
  have hcard := qtwoDB36_card_compl m c
  haveI : Nonempty {x : Fin m // x ≠ c} := by
    rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card, hcard]
    omega
  rw [show Nat.card (qtwoDB36_Subsets m c)
      = Nat.card {S : Finset {x : Fin m // x ≠ c} // Even S.card} from
    Nat.card_congr (qtwoDB36_subsetsEquiv m c)]
  rw [qtwoDB36_card_even_finset, hcard]
  exact congrArg (fun k => 2 ^ k) (by omega : (m - 1) - 1 = m - 2)

theorem qtwoDB36_card_dEvenStab {m : ℕ} (hm : 2 ≤ m) (c : Fin m) :
    Nat.card (dEvenStab m (Pi.single c 1)) = 2 ^ (m - 2) * (m - 1).factorial := by
  classical
  have hbij : Function.Bijective (qtwoDB36_ofPair m c) :=
    ⟨qtwoDB36_ofPair_injective m c, qtwoDB36_ofPair_surjective m c⟩
  rw [← Nat.card_congr (Equiv.ofBijective (qtwoDB36_ofPair m c) hbij)]
  change Nat.card (qtwoDB36_PermStab m c × qtwoDB36_Subsets m c) = _
  rw [Nat.card_prod, qtwoDB36_card_permStab, qtwoDB36_card_subsets m c hm, mul_comm]

private lemma qtwoDB36_factorial_eq (n : ℕ) (hn : 0 < n) :
    n.factorial = n * (n - 1).factorial :=
  (Nat.mul_factorial_pred (Nat.pos_iff_ne_zero.mp hn)).symm

private lemma qtwoDB36_factorial_succ_eq (m : ℕ) (hm : 1 ≤ m) :
    (m + 1).factorial = (m * (m + 1)) * (m - 1).factorial := by
  rw [Nat.factorial_succ, qtwoDB36_factorial_eq m (by omega)]
  ring

private theorem qtwoDB36_add_two_le_two_pow_sub_two (m : ℕ) (hm : 5 ≤ m) :
    m + 2 ≤ 2 ^ (m - 2) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hpow : 2 ^ ((m + 1) - 2) = 2 ^ (m - 2) * 2 := by
      rw [show (m + 1) - 2 = (m - 2) + 1 by omega, pow_succ]
    rw [hpow]
    calc m + 1 + 2 ≤ (m + 2) * 2 := by omega
      _ ≤ 2 ^ (m - 2) * 2 := by linarith [ih]

theorem qtwoDB36_not_dvd {m : ℕ} (hm : 7 ≤ m) :
    ¬ 2 ^ (m - 2) * (m - 1).factorial ∣ m.factorial ∧
      ¬ 2 ^ (m - 2) * (m - 1).factorial ∣ (m + 1).factorial := by
  have hm5 : 5 ≤ m := by omega
  have hlt : m < 2 ^ (m - 2) := by
    have := qtwoDB36_add_two_le_two_pow_sub_two m hm5
    omega
  have hlt' : m + 1 < 2 ^ (m - 2) := by
    have := qtwoDB36_add_two_le_two_pow_sub_two m hm5
    omega
  have hfacpos : 0 < (m - 1).factorial := Nat.factorial_pos _
  have hnotm : ¬ 2 ^ (m - 2) ∣ m := Nat.not_dvd_of_pos_of_lt (by omega) hlt
  have hnotm' : ¬ 2 ^ (m - 2) ∣ m * (m + 1) := by
    intro h
    rcases Nat.even_or_odd m with hEven | hOdd
    · have hodd : Odd (m + 1) := hEven.add_one
      have hc : Nat.Coprime (2 ^ (m - 2)) (m + 1) := by
        rw [Nat.coprime_pow_left_iff (by omega : 0 < m - 2)]
        exact hodd.coprime_two_left
      exact hnotm (hc.dvd_of_dvd_mul_right h)
    · have hc : Nat.Coprime (2 ^ (m - 2)) m := by
        rw [Nat.coprime_pow_left_iff (by omega : 0 < m - 2)]
        exact hOdd.coprime_two_left
      exact Nat.not_dvd_of_pos_of_lt (by omega) hlt' (hc.dvd_of_dvd_mul_left h)
  constructor
  · intro h
    have h' : 2 ^ (m - 2) * (m - 1).factorial ∣ m * (m - 1).factorial := by
      rw [← qtwoDB36_factorial_eq m (by omega)]
      exact h
    exact hnotm ((Nat.mul_dvd_mul_iff_right hfacpos).mp h')
  · intro h
    rw [qtwoDB36_factorial_succ_eq m (by omega)] at h
    exact hnotm' ((Nat.mul_dvd_mul_iff_right hfacpos).mp h)

end CFSG.StandardType.QTwo

end
