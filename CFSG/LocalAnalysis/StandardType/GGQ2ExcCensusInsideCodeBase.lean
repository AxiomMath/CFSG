
module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideWit
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusChecks
public import Certificates.Data.CFSGNative.ExcCensus.Inside

@[expose] public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

private theorem pairing_eq_sum_of_factorOK (hT : Chk.tabsOK m T = true) {D : ℕ}
    {Q P : Array (Array ℤ)} (hF : Chk.factorOK T (nroots m) D Q P = true) (i j : Root m) :
    pairing m i j = ∑ kk : Fin D, (Q[i.val]!)[kk.val]! * (P[j.val]!)[kk.val]! := by
  have h1 := nat_all_iff.mp hF i.val i.isLt
  have h2 := nat_all_iff.mp h1 j.val j.isLt
  rw [beq_iff_eq] at h2
  rw [← tabsOK_pair hT i j, h2, nat_fold_add]

theorem nonempty_satWitness_of_satOK (hT : Chk.tabsOK m T = true) {D : ℕ}
    {Q P : Array (Array ℤ)} (hF : Chk.factorOK T (nroots m) D Q P = true) {c : ℕ}
    {w : Chk.SatW} (h : Chk.satOK T (nroots m) D P c w = true) :
    Nonempty (SatWitness m (ofMask m c)) := by
  classical
  let ρ := w.b.size
  have hsat := h
  dsimp only [Chk.satOK] at hsat
  simp only [Bool.and_eq_true] at hsat
  rcases hsat with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  have hb_lt : ∀ a : Fin ρ, w.b[a.val]! < nroots m := fun a =>
    of_decide_eq_true (Bool.and_eq_true_iff.mp (nat_all_iff.mp h1 a.val a.isLt)).1
  let b : Fin ρ → Root m := fun a => ⟨w.b[a.val]!, hb_lt a⟩
  have hb_mem : ∀ a : Fin ρ, b a ∈ ofMask m c := fun a =>
    mem_ofMask.mpr (Bool.and_eq_true_iff.mp (nat_all_iff.mp h1 a.val a.isLt)).2
  have hk_lt : ∀ a : Fin ρ, w.k[a.val]! < nroots m := fun a =>
    of_decide_eq_true (nat_all_iff.mp h4 a.val a.isLt)
  let k : Fin ρ → Root m := fun a => ⟨w.k[a.val]!, hk_lt a⟩
  let M : Matrix (Fin ρ) (Fin ρ) ℤ := fun i j => pairing m (k i) (b j)
  have hene : w.e % 3 ≠ 0 := by simpa using h2
  have hfact : ∀ i j : Root m, pairing m i j =
      ∑ kk : Fin D, (Q[i.val]!)[kk.val]! * (P[j.val]!)[kk.val]! :=
    pairing_eq_sum_of_factorOK hT hF
  have hcoef : ∀ i : Root m, i ∈ ofMask m c → ∀ kk : Fin D,
      w.e * (P[i.val]!)[kk.val]! =
        ∑ a : Fin ρ, (w.n[i.val]!)[a.val]! * (P[w.b[a.val]!]!)[kk.val]! := by
    intro i hi kk
    have hmem : c.testBit i.val = true := mem_ofMask.mp hi
    have h3' := nat_all_iff.mp h3 i.val i.isLt
    have h4' : (Nat.all D fun kk _ =>
        w.e * (P[i.val]!)[kk]! == Nat.fold ρ
          (fun a _ s => s + (w.n[i.val]!)[a]! * (P[w.b[a]!]!)[kk]!) 0) = true := by
      rcases Bool.or_eq_true_iff.mp h3' with h | h
      · rw [hmem] at h
        exact absurd h (by simp)
      · exact h
    have h5' := nat_all_iff.mp h4' kk.val kk.isLt
    rw [beq_iff_eq] at h5'
    rw [h5', nat_fold_add]
  refine ⟨{
    r := ρ
    b := b
    k := k
    e := w.e
    n := fun i a => (w.n[i.val]!)[a.val]!
    A := Matrix.adjugate M
    D := M.det
    b_mem := hb_mem
    pairing_eq := ?_
    mul_eq := ?_
    not_three_dvd_e := ?_
    not_three_dvd_D := ?_ }⟩
  · intro i hi j
    have hci := hcoef i hi
    calc w.e * pairing m j i
        = w.e * ∑ kk : Fin D, (Q[j.val]!)[kk.val]! * (P[i.val]!)[kk.val]! := by
            rw [hfact j i]
      _ = ∑ kk : Fin D, (Q[j.val]!)[kk.val]! * (w.e * (P[i.val]!)[kk.val]!) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun kk _ => by ring
      _ = ∑ kk : Fin D, (Q[j.val]!)[kk.val]! *
            (∑ a : Fin ρ, (w.n[i.val]!)[a.val]! * (P[w.b[a.val]!]!)[kk.val]!) := by
            exact Finset.sum_congr rfl fun kk _ => by rw [hci kk]
      _ = ∑ kk : Fin D, ∑ a : Fin ρ, (Q[j.val]!)[kk.val]! *
            ((w.n[i.val]!)[a.val]! * (P[w.b[a.val]!]!)[kk.val]!) := by
            exact Finset.sum_congr rfl fun kk _ => by rw [Finset.mul_sum]
      _ = ∑ a : Fin ρ, ∑ kk : Fin D, (Q[j.val]!)[kk.val]! *
            ((w.n[i.val]!)[a.val]! * (P[w.b[a.val]!]!)[kk.val]!) := Finset.sum_comm
      _ = ∑ a : Fin ρ, (w.n[i.val]!)[a.val]! *
            (∑ kk : Fin D, (Q[j.val]!)[kk.val]! * (P[w.b[a.val]!]!)[kk.val]!) := by
            exact Finset.sum_congr rfl fun a _ => by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun kk _ => by ring
      _ = ∑ a : Fin ρ, (w.n[i.val]!)[a.val]! * pairing m j (b a) := by
            exact Finset.sum_congr rfl fun a _ => by rw [← hfact j (b a)]
  · intro a a'
    change (∑ a'', Matrix.adjugate M a a'' * M a'' a') = if a = a' then M.det else 0
    have hm := congrFun (congrFun (Matrix.adjugate_mul M) a) a'
    rw [Matrix.mul_apply] at hm
    simpa [Matrix.smul_apply, Matrix.one_apply] using hm
  · intro hd
    exact hene (Int.dvd_iff_emod_eq_zero.mp hd)
  · intro hd
    have hcast : ((M.det : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd M.det 3).mpr hd
    have hMeq : (Matrix.of fun i j => (T.pair[w.k[i.val]!]!)[w.b[j.val]!]!) = M := by
      ext i j
      simp only [Matrix.of_apply, M]
      exact tabsOK_pair hT (k i) (b j)
    have hInv := invOK_det_ne_zero h5
    rw [hMeq] at hInv
    exact hInv hcast

private theorem vec_three_pow (k : Fin (dim m)) : vec m (3 ^ k.val) = Pi.single k 1 := by
  funext j
  rw [vec, Pi.single_apply]
  by_cases h : j = k
  · subst h
    rw [Chk.dig, Nat.div_self (by positivity)]
    simp
  · rw [if_neg h]
    have hmod : 3 ^ k.val / 3 ^ j.val % 3 = 0 := by
      rw [Nat.mod_eq_zero_of_dvd]
      rcases Nat.lt_or_gt_of_ne (fun hval => h (Fin.ext hval)) with hlt | hgt
      · have hk : 3 ^ k.val = 3 ^ j.val * 3 ^ (k.val - j.val) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        rw [hk, Nat.mul_div_right _ (Nat.pow_pos (by norm_num))]
        exact dvd_pow_self 3 (by omega)
      · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hgt)]
        exact dvd_zero 3
    rw [Chk.dig, hmod, Nat.cast_zero]

private theorem pairing_eq_of_chainSum (hT : Chk.tabsOK m T = true) {D : ℕ}
    {Q P : Array (Array ℤ)} (hF : Chk.factorOK T (nroots m) D Q P = true) {bs : Array ℕ}
    {b : Fin 8 → Root m} (hb : ∀ s, (b s).val = bs[s.val]!) {i : Root m} {a a' : ℕ} {ε : ℤ}
    (hQ : ∀ kk : Fin D, (Q[i.val]!)[kk.val]! = ε * Chk.chainSumN Q bs a a' kk) (j : Root m) :
    pairing m i j = ε * ∑ s ∈ Finset.univ.filter (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'),
      pairing m (b s) j := by
  have hcs : ∀ kk : ℕ, Chk.chainSumN Q bs a a' kk =
      ∑ s ∈ Finset.univ.filter (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'),
        (Q[(b s).val]!)[kk]! := by
    intro kk
    have hfun : (fun (s : ℕ) (_ : s < 8) (acc : ℤ) =>
        if a ≤ s ∧ s < a' then acc + (Q[bs[s]!]!)[kk]! else acc) =
        fun s _ acc => acc + if a ≤ s ∧ s < a' then (Q[bs[s]!]!)[kk]! else 0 := by
      funext s _ acc
      split_ifs <;> simp
    calc Chk.chainSumN Q bs a a' kk
        = Nat.fold 8 (fun s _ acc => acc + if a ≤ s ∧ s < a' then (Q[bs[s]!]!)[kk]! else 0) 0 :=
          congrArg (fun f => Nat.fold 8 f (0 : ℤ)) hfun
      _ = _ := by
          rw [nat_fold_add, Finset.sum_filter]
          exact Finset.sum_congr rfl fun s _ => by rw [hb s]
  calc pairing m i j = ∑ kk : Fin D, (Q[i.val]!)[kk.val]! * (P[j.val]!)[kk.val]! :=
        pairing_eq_sum_of_factorOK hT hF i j
    _ = ∑ kk : Fin D, (ε * ∑ s ∈ Finset.univ.filter
          (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'), (Q[(b s).val]!)[kk.val]!) *
          (P[j.val]!)[kk.val]! :=
        Finset.sum_congr rfl fun kk _ => by rw [hQ kk, hcs kk]
    _ = ε * ∑ s ∈ Finset.univ.filter (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'),
          ∑ kk : Fin D, (Q[(b s).val]!)[kk.val]! * (P[j.val]!)[kk.val]! := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = _ := by simp only [pairing_eq_sum_of_factorOK hT hF]

theorem nonempty_a8Witness_of_a8OK (hT : Chk.tabsOK m T = true) {D : ℕ}
    {Q P : Array (Array ℤ)} (hF : Chk.factorOK T (nroots m) D Q P = true) {c : ℕ}
    {w : Chk.A8W} (h : Chk.a8OK T (dim m) (nroots m) D Q c w = true) :
    Nonempty (A8Witness m (ofMask m c)) := by
  have hsat := h
  simp only [Chk.a8OK, Bool.and_eq_true] at hsat
  rcases hsat with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩
  have h1' : ∀ a : Fin 8, w.b[a.val]! < nroots m ∧ c.testBit w.b[a.val]! = true := fun a =>
    have h := Bool.and_eq_true_iff.mp (nat_all_iff.mp h1 a.val a.isLt)
    ⟨of_decide_eq_true h.1, h.2⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin 8 → Root m, ∀ a, (b a).val = w.b[a.val]! :=
    ⟨fun a => ⟨w.b[a.val]!, (h1' a).1⟩, fun a => rfl⟩
  refine ⟨{
    b := b
    cz := vec m w.cz
    b_mem := fun a => mem_ofMask.mpr (by rw [hb a]; exact (h1' a).2)
    gram := ?_
    span := ?_
    root_cz := ?_
    hyper := ?_ }⟩
  · intro a a'
    rw [← tabsOK_pair hT (b a) (b a'), hb a, hb a',
      beq_iff_eq.mp (nat_all_iff.mp (nat_all_iff.mp h2 a.val a.isLt) a'.val a'.isLt),
      Chk.chainGramN]
    by_cases haa : a = a'
    · exact (if_pos (congrArg Fin.val haa)).trans (if_pos haa).symm
    · exact (if_neg fun h => haa (Fin.ext h)).trans (if_neg haa).symm
  · intro i hi
    have h3i := nat_all_iff.mp h3 i.val i.isLt
    simp only [mem_ofMask.mp hi, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at h3i
    obtain ⟨⟨he1, he2⟩, hQ⟩ := h3i
    refine ⟨_, _, he1, he2, if (w.span[i.val]!).2.2 then -1 else 1, by split_ifs <;> simp,
      pairing_eq_of_chainSum hT hF hb fun kk => ?_⟩
    exact beq_iff_eq.mp (nat_all_iff.mp hQ kk.val kk.isLt)
  · intro k
    obtain ⟨hmod, hdig⟩ := Bool.and_eq_true_iff.mp (nat_all_iff.mp h5 k.val k.isLt)
    have hsum : ∑ a : Fin 8, ((a : ℕ) + 1 : ℤ) * pairing m k (b a) =
        Chk.chainExpN T w.b k.val := by
      rw [Chk.chainExpN, nat_fold_add]
      exact Finset.sum_congr rfl fun a _ => by
        rw [← tabsOK_pair hT k (b a), hb a, Nat.cast_add, Nat.cast_one]
    have hcast : ∀ x : ℤ, ((x % 3 : ℤ) : ZMod 3) = (x : ZMod 3) := fun x => by
      exact_mod_cast ZMod.intCast_mod x 3
    refine ⟨Chk.chainExpN T w.b k.val / 3, ?_, ?_⟩
    · rw [hsum]
      exact (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero (beq_iff_eq.mp hmod))).symm
    · rw [← hcast, beq_iff_eq.mp hdig, Chk.evA, nat_fold_add, hcast, root_apply, Int.cast_sum]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [Int.cast_mul, Int.cast_natCast, tabsOK_f hT k j, vec]
  · have hmem : ∀ k : Fin (dim m),
        Pi.single k 1 - ((w.hyp[k.val]!).1 : ZMod 3) • vec m w.cz ∈ inside m (ofMask m c) := by
      intro k
      obtain ⟨hlt, hin⟩ := Bool.and_eq_true_iff.mp (nat_all_iff.mp h6 k.val k.isLt)
      have h' := inOK_sound hT hin
      rw [vec_combN, vec_three_pow, Nat.cast_one, one_smul,
        Nat.cast_sub (of_decide_eq_true hlt).le, ZMod.natCast_self, zero_sub, neg_smul] at h'
      rw [sub_eq_add_neg]
      exact h'
    intro v
    refine ⟨∑ k, v k * ((w.hyp[k.val]!).1 : ZMod 3), ?_⟩
    have hv : v - (∑ k, v k * ((w.hyp[k.val]!).1 : ZMod 3)) • vec m w.cz =
        ∑ k, v k • (Pi.single k 1 - ((w.hyp[k.val]!).1 : ZMod 3) • vec m w.cz) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_sub, Finset.sum_mul, mul_assoc]
      refine Eq.trans ?_ (Finset.sum_sub_distrib _ _).symm
      exact sub_left_inj.mpr ((Finset.sum_ite_eq Finset.univ j v).trans
        (if_pos (Finset.mem_univ j))).symm
    rw [hv]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hmem k)

private theorem icf_testBit_trunc {r c t : ℕ} (ht : t < r) :
    (Chk.trunc r c).testBit t = c.testBit t := by
  rw [Chk.trunc, Nat.testBit_land, Nat.testBit_two_pow_sub_one]
  simp [ht]

theorem flagE6N_sound (hT : Chk.tabsOK m T = true) {c : ℕ}
    (h : Chk.flagE6N T (nroots m) c = true) :
    ofMask m c = Finset.univ ∨ ∃ k : Root m,
      ofMask m c = Finset.univ.filter fun i => pairing m k i = 0 ∧ pairing m i k = 0 := by
  rw [Chk.flagE6N, Bool.or_eq_true, beq_iff_eq, Nat.any_eq_finRange_any, List.any_eq_true] at h
  rcases h with h | ⟨⟨k, hk⟩, -, hkc⟩
  · left
    ext t
    have ht := congrArg (fun n => n.testBit t) h
    simp only [icf_testBit_trunc t.isLt, Nat.testBit_two_pow_sub_one, t.isLt, decide_true] at ht
    simp [mem_ofMask, ht]
  · right
    refine ⟨⟨k, hk⟩, ?_⟩
    ext t
    have ht := congrArg (fun n => n.testBit t) (beq_iff_eq.mp hkc)
    simp only [icf_testBit_trunc t.isLt] at ht
    have h1 : (T.pair[k]!)[t.val]! = pairing m ⟨k, hk⟩ t := tabsOK_pair hT ⟨k, hk⟩ t
    have h2 : (T.pair[t.val]!)[k]! = pairing m t ⟨k, hk⟩ := tabsOK_pair hT t ⟨k, hk⟩
    rw [mem_ofMask, ht, Chk.orthMaskN, maskN_testBit, h1, h2]
    simp [t.isLt]

end CFSG.StandardType.GGQ2Frame.ExcRaw
