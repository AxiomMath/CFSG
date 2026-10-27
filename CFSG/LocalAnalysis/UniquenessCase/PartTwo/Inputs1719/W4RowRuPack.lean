module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowInvPack
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuPerm
public import Certificates.Certificate725003

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.RuExcl CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

private def invPackLineCheck (n p m : ℕ) (y w h : PArr) (a b : ℕ) : Bool :=
  allLt m fun k =>
    k == 0 ||
      allLt p fun j =>
        !eqA n
          (compA n
            (compA n (powA n h.1 k)
              (compA n (powA n y.1 a) (powA n w.1 b)))
            (powA n h.2 k))
          (powA n (compA n (powA n y.1 a) (powA n w.1 b)) j)

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

private theorem invPack_lines_of_check {n p m : ℕ} {y w h : PArr}
    {gy gw gh : Equiv.Perm (Fin n)} (hy : PRep n y gy) (hw : PRep n w gw) (hh : PRep n h gh)
    {a b : ℕ} (hne : gy ^ a * gw ^ b ≠ 1)
    (hc : ((a == 0 && b == 0) || invPackLineCheck n p m y w h a b) = true)
    {k j : ℕ} (hk0 : 0 < k) (hkm : k < m) (hj : j < p) :
    gh ^ k * (gy ^ a * gw ^ b) * (gh ^ k)⁻¹ ≠ (gy ^ a * gw ^ b) ^ j := by
  have h0 : (a == 0 && b == 0) = false := by
    cases hval : (a == 0 && b == 0) with
    | false => rfl
    | true =>
      simp only [beq_iff_eq, Bool.and_eq_true] at hval
      obtain ⟨rfl, rfl⟩ := hval
      exact absurd (by simp) hne
  have h1 : invPackLineCheck n p m y w h a b = true := by
    rw [Bool.or_eq_true] at hc
    rcases hc with h | h
    · rw [h0] at h
      exact (Bool.false_ne_true h).elim
    · exact h
  simp only [invPackLineCheck] at h1
  have hk := allLt_iff.1 h1 k hkm
  have hk0' : (k == 0) = false := by
    cases hval : (k == 0) with
    | false => rfl
    | true =>
      have : k = 0 := by simpa using hval
      omega
  have he : eqA n
      (compA n (compA n (powA n h.1 k)
        (compA n (powA n y.1 a) (powA n w.1 b))) (powA n h.2 k))
      (powA n (compA n (powA n y.1 a) (powA n w.1 b)) j) = false := by
    rw [Bool.or_eq_true] at hk
    rcases hk with h | h
    · rw [hk0'] at h
      exact (Bool.false_ne_true h).elim
    · simpa only [Bool.not_eq_true'] using allLt_iff.1 h j hj
  have hpr : Rep n (compA n (powA n y.1 a) (powA n w.1 b)) (gy ^ a * gw ^ b) :=
    rep_compA (rep_powA hy.1 a) (rep_powA hw.1 b)
  have hleft : Rep n
      (compA n (compA n (powA n h.1 k)
        (compA n (powA n y.1 a) (powA n w.1 b))) (powA n h.2 k))
      (gh ^ k * (gy ^ a * gw ^ b) * (gh ^ k)⁻¹) := by
    have := rep_compA (rep_compA (rep_powA hh.1 k) hpr) (rep_powA hh.2 k)
    simpa [mul_assoc, inv_pow] using this
  exact ne_of_eqA_eq_false hleft (rep_powA hpr j) he

theorem invPack_of_check {n p m : ℕ} (hp : 0 < p) {τ y w h : PArr} {cs : List (ℕ × ℕ)}
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
  refine ⟨hpowl', hpowr', ?_, hne', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (eqA_iff (rep_compA hy.1 hw.1) (rep_compA hw.1 hy.1)).1 hcomm
  · refine not_mem_zpowers_of_forall_ne_pow hp hpowl' fun k hk => ?_
    exact ne_of_eqA_eq_false hw.1 (rep_powA hy.1 k)
      (by simpa only [Bool.not_eq_true'] using allLt_iff.1 hnotmem k hk)
  · exact (eqA_iff (rep_compA (rep_compA hτ.1 hy.1) hτ.2) hy.2).1 hinvl
  · exact (eqA_iff (rep_compA (rep_compA hτ.1 hw.1) hτ.2) hw.2).1 hinvr
  · exact ⟨_, _, (eqA_iff (rep_compA (rep_compA hh.1 hy.1) hh.2)
      (rep_compA (rep_powA hy.1 _) (rep_powA hw.1 _))).1 hcl⟩
  · exact ⟨_, _, (eqA_iff (rep_compA (rep_compA hh.1 hw.1) hh.2)
      (rep_compA (rep_powA hy.1 _) (rep_powA hw.1 _))).1 hcr⟩
  · exact ⟨_, _, (eqA_iff (rep_compA (rep_compA hh.2 hy.1) hh.1)
      (rep_compA (rep_powA hy.1 _) (rep_powA hw.1 _))).1 hcil⟩
  · exact ⟨_, _, (eqA_iff (rep_compA (rep_compA hh.2 hw.1) hh.1)
      (rep_compA (rep_powA hy.1 _) (rep_powA hw.1 _))).1 hcir⟩
  · intro a ha b hb hneab k hk0 hkm j hj
    have hab : ((a == 0 && b == 0) || invPackLineCheck n p m y w h a b) = true := by
      simpa only [invPackLineCheck] using allLt_iff.1 (allLt_iff.1 hlines a ha) b hb
    exact invPack_lines_of_check hy hw hh hneab hab hk0 hkm hj

theorem ruE25_invPack :
    ∃ y ∈ ruP, ∃ w ∈ ruP, ∃ h ∈ ruP, InvPack 5 6 (ruA1 * ruA1) y w h := by
  obtain ⟨y, hyP, hy⟩ := regIn_ruP.word ruE25WY
  obtain ⟨w, hwP, hw⟩ := regIn_ruP.word ruE25WW
  obtain ⟨h, hhP, hh⟩ := regIn_ruP.word ruE25WH
  exact ⟨y, hyP, w, hwP, h, hhP,
    invPack_of_check (by norm_num) pRep_ruZtP hy hw hh Certificates.certificate725003⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
