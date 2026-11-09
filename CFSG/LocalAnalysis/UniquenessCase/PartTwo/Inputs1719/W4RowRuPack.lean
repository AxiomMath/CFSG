module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowInvPack
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuPerm
public import Certificates.Certificate725003

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.RuExcl CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

private theorem ne_of_eqA_eq_false {n : ℕ} {t u : Array ℕ} {g h : Equiv.Perm (Fin n)}
    (ht : Rep n t g) (hu : Rep n u h) (he : eqA n t u = false) : g ≠ h := by
  intro hgh
  have htrue : eqA n t u = true := (eqA_iff ht hu).2 hgh
  rw [htrue] at he
  exact Bool.false_ne_true he.symm

private theorem not_mem_zpowers_of_forall_ne_pow {G : Type*} [Group G] {x y : G} {p : ℕ}
    (hp : 0 < p) (hx : x ^ p = 1) (h : ∀ k < p, y ≠ x ^ k) : y ∉ Subgroup.zpowers x := by
  intro hy
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hpos : 0 < (p : ℤ) := by exact_mod_cast hp
  have hnonneg : 0 ≤ i % (p : ℤ) := Int.emod_nonneg i hpos.ne'
  have hlt : i % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos i hpos
  have hlt' : (i % (p : ℤ)).toNat < p := by
    rw [Int.toNat_lt hnonneg]
    exact hlt
  have hpow : x ^ i = x ^ (i % (p : ℤ)).toNat := by
    calc x ^ i = x ^ (i % (p : ℤ)) := zpow_eq_zpow_emod i (by rw [zpow_natCast]; exact hx)
      _ = x ^ (((i % (p : ℤ)).toNat) : ℤ) := by rw [Int.toNat_of_nonneg hnonneg]
      _ = x ^ (i % (p : ℤ)).toNat := zpow_natCast x _
  exact h _ hlt' (hi.symm.trans hpow)

private theorem e25_pair_inj {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {y w : G}
    (hy : y ^ p = 1) (hw : w ^ p = 1) (hne : y ≠ 1) (hnm : w ∉ Subgroup.zpowers y)
    {a b a' b' : ℕ} (ha : a < p) (hb : b < p) (ha' : a' < p) (hb' : b' < p)
    (h : y ^ a * w ^ b = y ^ a' * w ^ b') : a = a' ∧ b = b' := by
  have hbb : b = b' := by
    by_contra hbb
    wlog hlt : b' < b generalizing a b a' b'
    · exact this ha' hb' ha hb h.symm (Ne.symm hbb) (by omega)
    have hd : w ^ (b - b') ∈ Subgroup.zpowers y := by
      have e : w ^ (b - b') = (y ^ a)⁻¹ * y ^ a' := by
        have h2 : y ^ a * (w ^ (b - b') * w ^ b') = y ^ a' * w ^ b' := by
          rw [← pow_add, Nat.sub_add_cancel hlt.le, h]
        rw [← mul_assoc] at h2
        rw [eq_inv_mul_iff_mul_eq]
        exact mul_right_cancel h2
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers y a))
        (Subgroup.npow_mem_zpowers y a')
    have hcop : Nat.Coprime (b - b') p :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    apply hnm
    have e : w = (w ^ (b - b')) ^ u := by
      rw [← pow_mul, pow_eq_pow_mod _ hw, hu, pow_one]
    rw [e]
    exact Subgroup.pow_mem _ hd u
  subst hbb
  refine ⟨?_, rfl⟩
  have h1 : y ^ a = y ^ a' := mul_right_cancel h
  have hfact : Fact p.Prime := ⟨hp⟩
  have ho : orderOf y = p := orderOf_eq_prime hy hne
  rw [pow_inj_mod, ho, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h1
  exact h1

private theorem e25_conj_step {G : Type*} [Group G] {p : ℕ} {y w h : G} {cs : List (ℕ × ℕ)}
    (hy : y ^ p = 1) (hw : w ^ p = 1) (hc : Commute y w)
    (h0 : h * y * h⁻¹ = y ^ (cs.getD 0 (0, 0)).1 * w ^ (cs.getD 0 (0, 0)).2)
    (h1 : h * w * h⁻¹ = y ^ (cs.getD 1 (0, 0)).1 * w ^ (cs.getD 1 (0, 0)).2) (v : ℕ × ℕ) :
    h * (y ^ v.1 * w ^ v.2) * h⁻¹ = y ^ (e25Step p cs v).1 * w ^ (e25Step p cs v).2 := by
  obtain ⟨a, b⟩ := v
  simp only [e25Step]
  generalize cs.getD 0 (0, 0) = q0 at h0 ⊢
  generalize cs.getD 1 (0, 0) = q1 at h1 ⊢
  obtain ⟨c0, d0⟩ := q0
  obtain ⟨c1, d1⟩ := q1
  dsimp only at h0 h1 ⊢
  have e : h * (y ^ a * w ^ b) * h⁻¹ = (h * y * h⁻¹) ^ a * (h * w * h⁻¹) ^ b := by
    rw [conj_pow, conj_pow]
    simp only [mul_assoc, inv_mul_cancel_left]
  have hc' : Commute ((w ^ d0) ^ a) ((y ^ c1) ^ b) := ((hc.pow_pow c1 d0).pow_pow b a).symm
  rw [← pow_eq_pow_mod _ hy, ← pow_eq_pow_mod _ hw, pow_add, pow_add, pow_mul', pow_mul',
    pow_mul', pow_mul', e, h0, h1, (hc.pow_pow c0 d0).mul_pow, (hc.pow_pow c1 d1).mul_pow]
  simp only [mul_assoc]
  rw [hc'.left_comm]

private theorem e25_conj_iter {G : Type*} [Group G] {p : ℕ} {y w h : G} {cs : List (ℕ × ℕ)}
    (hy : y ^ p = 1) (hw : w ^ p = 1) (hc : Commute y w)
    (h0 : h * y * h⁻¹ = y ^ (cs.getD 0 (0, 0)).1 * w ^ (cs.getD 0 (0, 0)).2)
    (h1 : h * w * h⁻¹ = y ^ (cs.getD 1 (0, 0)).1 * w ^ (cs.getD 1 (0, 0)).2) (k : ℕ)
    (v : ℕ × ℕ) : h ^ k * (y ^ v.1 * w ^ v.2) * (h ^ k)⁻¹ =
      y ^ ((e25Step p cs)^[k] v).1 * w ^ ((e25Step p cs)^[k] v).2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← e25_conj_step hy hw hc h0 h1, ← ih, pow_succ']
    simp only [mul_inv_rev, mul_assoc]

theorem invPack_of_check {n p m : ℕ} (hp : p.Prime) {τ y w h : PArr} {cs : List (ℕ × ℕ)}
    {gτ gy gw gh : Equiv.Perm (Fin n)} (hτ : PRep n τ gτ) (hy : PRep n y gy) (hw : PRep n w gw)
    (hh : PRep n h gh) (hc : invPackCheck n p m τ y w h cs = true) :
    InvPack p m gτ gy gw gh := by
  simp only [invPackCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpowl, hpowr⟩, hcomm⟩, hne⟩, hnotmem⟩, hinvl⟩, hinvr⟩, hcl⟩,
    hcr⟩, hcil⟩, hcir⟩, hlines⟩ := hc
  have hpowl' : gy ^ p = 1 :=
    (eqA_iff (rep_powA hy.1 p) (rep_idA (n := n))).1 hpowl
  have hpowr' : gw ^ p = 1 :=
    (eqA_iff (rep_powA hw.1 p) (rep_idA (n := n))).1 hpowr
  have hne' : gy ≠ 1 := ne_of_eqA_eq_false hy.1 (rep_idA (n := n)) hne
  have hcomm' : gy * gw = gw * gy :=
    (eqA_iff (rep_compA hy.1 hw.1) (rep_compA hw.1 hy.1)).1 hcomm
  have hnotmem' : gw ∉ Subgroup.zpowers gy := by
    refine not_mem_zpowers_of_forall_ne_pow hp.pos hpowl' fun k hk => ?_
    exact ne_of_eqA_eq_false hw.1 (rep_powA hy.1 k)
      (by simpa only [Bool.not_eq_true'] using allLt_iff.1 hnotmem k hk)
  have hcl' : gh * gy * gh⁻¹ = gy ^ (cs.getD 0 (0, 0)).1 * gw ^ (cs.getD 0 (0, 0)).2 :=
    (eqA_iff (rep_compA (rep_compA hh.1 hy.1) hh.2)
      (rep_compA (rep_powA hy.1 _) (rep_powA hw.1 _))).1 hcl
  have hcr' : gh * gw * gh⁻¹ = gy ^ (cs.getD 1 (0, 0)).1 * gw ^ (cs.getD 1 (0, 0)).2 :=
    (eqA_iff (rep_compA (rep_compA hh.1 hw.1) hh.2)
      (rep_compA (rep_powA hy.1 _) (rep_powA hw.1 _))).1 hcr
  refine ⟨hpowl', hpowr', hcomm', hne', hnotmem', ?_, ?_, ⟨_, _, hcl'⟩, ⟨_, _, hcr'⟩, ?_, ?_, ?_⟩
  · exact (eqA_iff (rep_compA (rep_compA hτ.1 hy.1) hτ.2) hy.2).1 hinvl
  · exact (eqA_iff (rep_compA (rep_compA hτ.1 hw.1) hτ.2) hw.2).1 hinvr
  · exact ⟨_, _, (eqA_iff (rep_compA (rep_compA hh.2 hy.1) hh.1)
      (rep_compA (rep_powA hy.1 _) (rep_powA hw.1 _))).1 hcil⟩
  · exact ⟨_, _, (eqA_iff (rep_compA (rep_compA hh.2 hw.1) hh.1)
      (rep_compA (rep_powA hy.1 _) (rep_powA hw.1 _))).1 hcir⟩
  · intro a ha b hb hneab k hk0 hkm j hj heq
    have hcm : Commute gy gw := hcomm'
    unfold e25Lines at hlines
    have hl := allLt_iff.1 (allLt_iff.1 hlines a ha) b hb
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hl
    rcases hl with ⟨rfl, rfl⟩ | hl
    · exact hneab (by simp)
    have hk := allLt_iff.1 hl k hkm
    simp only [Bool.or_eq_true, beq_iff_eq] at hk
    rcases hk with hk | hk
    · omega
    have hj' := allLt_iff.1 hk j hj
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hj'
    apply hj'
    rw [e25_conj_iter hpowl' hpowr' hcm hcl' hcr' k (a, b), (hcm.pow_pow a b).mul_pow,
      ← pow_mul', ← pow_mul', pow_eq_pow_mod (j * a) hpowl',
      pow_eq_pow_mod (j * b) hpowr'] at heq
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    rw [Function.iterate_succ_apply'] at heq ⊢
    obtain ⟨e1, e2⟩ := e25_pair_inj hp hpowl' hpowr' hne' hnotmem'
      (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) heq
    exact Prod.ext e1 e2

theorem ruE25_invPack :
    ∃ y ∈ ruP, ∃ w ∈ ruP, ∃ h ∈ ruP, InvPack 5 6 (ruA1 * ruA1) y w h := by
  obtain ⟨y, hyP, hy⟩ := regIn_ruP.word ruE25WY
  obtain ⟨w, hwP, hw⟩ := regIn_ruP.word ruE25WW
  obtain ⟨h, hhP, hh⟩ := regIn_ruP.word ruE25WH
  exact ⟨y, hyP, w, hwP, h, hhP,
    invPack_of_check (by norm_num) pRep_ruZtP hy hw hh Certificates.certificate725003⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

end
