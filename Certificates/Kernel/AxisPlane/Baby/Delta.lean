module

public import Certificates.Kernel.AxisPlane.Baby.DeltaData
public import CFSG.Monster.AxisCount.BabyShort
import CFSG.Monster.AxisCount.CoverLetters
import CFSG.Monster.B.Short.ShortStab

public section

namespace CertificateChecks.KernelAP.Baby

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert
  CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby CFSG.KLie.CT CFSG.KC.SortTree

theorem memS_of_short {x : ℕ} (hx : x < 2 ^ 24) (h : dec x ∈ shortSet) :
    CertificateChecks.Short3014.memS x = true := by
  rw [CertificateChecks.Short3014.memS_iff, CertificateChecks.Short3014.reach_iff,
    ← CertificateChecks.Short3014.mem_treeSet]
  by_contra hnot
  have hT : ∀ y ∈ insert x CertificateChecks.Short3014.treeSet, y < 2 ^ 24 ∧ dec y ∈ shortSet := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ⟨hx, h⟩
    · exact CertificateChecks.Short3014.reach_short (CertificateChecks.Short3014.treeSet_reach hy)
  have hinj : Set.InjOn dec (insert x CertificateChecks.Short3014.treeSet : Finset ℕ) :=
    fun a ha b hb e => dec_inj a b (hT a ha).1 (hT b hb).1 e
  have hsub : dec '' (insert x CertificateChecks.Short3014.treeSet : Finset ℕ) ⊆ shortSet := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hT y hy).2
  have hfin : shortSet.Finite := Set.finite_of_ncard_pos (by rw [ncard_shortSet]; norm_num)
  have := Set.ncard_le_ncard hsub hfin
  rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_insert_of_notMem hnot,
    CertificateChecks.Short3014.treeSet_card, ncard_shortSet] at this
  omega

theorem short_of_memS {x : ℕ} (h : CertificateChecks.Short3014.memS x = true) : dec x ∈ shortSet :=
  (CertificateChecks.Short3014.reach_short ((CertificateChecks.Short3014.memS_iff x).1 h)).2

theorem land_mod256 (v m : ℕ) (hm : m < 256) : v &&& m = (v % 256) &&& m := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e : (256 : ℕ) = 2 ^ 8 := rfl
  rw [Nat.testBit_and, Nat.testBit_and, e, Nat.testBit_mod_two_pow]
  by_cases hi : i < 8
  · simp [hi]
  · have : m.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (by
        rw [e]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this]

theorem parity_table : ∀ y < 256, (Code.popc 24 (y &&& 62) + Code.popc 24 (y &&& 129)) % 2 = 0 →
    Nat.land (Nat.shiftRight PT (y &&& 191)) 1 = 0 := by
  decide +kernel

theorem parity_of {v : ℕ}
    (h : ((Code.popc 24 (v &&& 62) + Code.popc 24 (v &&& 129) : ℕ) : ZMod 2) = 0) :
    Nat.land (Nat.shiftRight PT (v &&& 191)) 1 = 0 := by
  have h2 : (Code.popc 24 (v &&& 62) + Code.popc 24 (v &&& 129)) % 2 = 0 := by
    rw [← ZMod.val_natCast, h]
    rfl
  rw [land_mod256 v 62 (by norm_num), land_mod256 v 129 (by norm_num)] at h2
  rw [land_mod256 v 191 (by norm_num)]
  exact parity_table _ (Nat.mod_lt _ (by norm_num)) h2

theorem gramRow_12 : gramRow ((12 : Fin 24) : ℕ) = 62 := rfl

theorem gramRow_13 : gramRow ((13 : Fin 24) : ℕ) = 129 := rfl

theorem dec_12288 : dec 12288 = ellCls 12 + ellCls 13 := by
  have e : (12288 : ℕ) = 2 ^ ((12 : Fin 24) : ℕ) ^^^ 2 ^ ((13 : Fin 24) : ℕ) := rfl
  rw [e, dec_xor, dec_two_pow, dec_two_pow]

theorem two_add_self (x : L2) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem condD_of_mem {x : L2} (hx : x ∈ babyDelta) {u : ℕ} (hu : u < 2 ^ 24)
    (hux : dec u = x + uStarCls) : condD u = true := by
  obtain ⟨⟨hx0, hq, hns⟩, hs⟩ := hx
  have hxe : x = dec u + dec 12288 := by
    rw [hux, add_assoc, uStarCls, two_add_self, add_zero]
  have hus : dec u ∈ shortSet := by rw [hux]; exact hs
  have hq1 : qL (dec u) = 0 := shortSet_subset_singular hus
  have hq2 : qL (dec 12288) = 0 := shortSet_subset_singular uStarCls_mem_shortSet
  unfold condD
  rw [andB_true_iff, andB_true_iff]
  refine ⟨?_, ?_, ?_⟩
  · cases h : Nat.beq u 12288
    · rfl
    · rw [Nat.beq_eq] at h
      subst h
      exact (hx0 (by rw [hxe, two_add_self])).elim
  · rw [Nat.beq_eq]
    apply parity_of
    have hpol := CFSG.Monster.B.Short.qL_add (dec u) (dec 12288)
    rw [← hxe, hq, hq1, hq2, dec_12288, map_add, CFSG.Monster.B.Short.bL, bL_dec, bL_dec,
      gramRow_12, gramRow_13] at hpol
    simp only [zero_add] at hpol
    push_cast
    exact hpol.symm
  · cases h : CertificateChecks.Short3014.memS (Nat.xor u 12288)
    · rfl
    · have h1 := short_of_memS h
      have e : dec (Nat.xor u 12288) = x := by
        rw [hxe]
        exact dec_xor u 12288
      exact (hns (by rw [← e]; exact h1)).elim

theorem sumN_eq_sum (n : ℕ) (f : ℕ → ℕ) : sumN n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f n + sumN n f = _
    rw [ih, Finset.sum_range_succ, Nat.add_comm]

theorem sumN_add (f : ℕ → ℕ) (a : ℕ) : ∀ b, sumN (a + b) f = sumN a f + sumN b (fun j => f (a + j))
  | 0 => rfl
  | b + 1 => by
    change f (a + b) + sumN (a + b) f = sumN a f + (f (a + b) + sumN b (fun j => f (a + j)))
    rw [sumN_add f a b]
    omega

theorem sumN_chunks (f : ℕ → ℕ) (B : ℕ) : ∀ n,
    sumN (n * B) f = sumN n (fun c => sumN B (fun j => f (Nat.add (Nat.mul c B) j)))
  | 0 => by rw [Nat.zero_mul]; rfl
  | n + 1 => by
    rw [show (n + 1) * B = n * B + B by ring, sumN_add, sumN_chunks f B n]
    exact Nat.add_comm _ _

theorem cntC_eq {c : ℕ} (hc : c < 52) : cntC c = fget PC c 12 := by
  have hs : ∀ k < 13, sliceD (4 * k) 4 = true := by
    intro k hk
    interval_cases k
    exacts [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12]
  have := (allN_iff _ _).1 (hs (c / 4) (by omega)) (c % 4) (Nat.mod_lt _ (by norm_num))
  change Nat.beq (cntC (4 * (c / 4) + c % 4)) (fget PC (4 * (c / 4) + c % 4) 12) = true at this
  rwa [Nat.div_add_mod, Nat.beq_eq] at this

theorem card_pass : ((Finset.range 98280).filter fun i =>
    condD (valF 24 (CertificateChecks.Short3014.recS i)) = true).card = 46575 := by
  have h1 : sumN 98280 indD = 46575 := by
    have e : (98280 : ℕ) = 52 * 1890 := rfl
    rw [e, sumN_chunks indD 1890 52]
    have e2 : sumN 52 (fun c => sumN 1890 (fun j => indD (Nat.add (Nat.mul c 1890) j))) =
        sumN 52 (fun c => fget PC c 12) := by
      rw [sumN_eq_sum, sumN_eq_sum]
      exact Finset.sum_congr rfl fun c hc => cntC_eq (Finset.mem_range.1 hc)
    rw [e2]
    exact Nat.eq_of_beq_eq_true total
  rw [sumN_eq_sum] at h1
  rw [Finset.card_filter, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold indD
  cases condD (valF 24 (CertificateChecks.Short3014.recS i)) <;> rfl

theorem babyDelta_ncard_le : babyDelta.ncard ≤ 46575 := by
  let S : Finset ℕ := ((Finset.range 98280).filter fun i =>
    condD (valF 24 (CertificateChecks.Short3014.recS i)) = true).image
      fun i => valF 24 (CertificateChecks.Short3014.recS i)
  have hsub : babyDelta ⊆ (fun y => y + uStarCls) '' (dec '' (S : Set ℕ)) := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := exists_dec (x + uStarCls)
    have hm := memS_of_short hu (by rw [hux]; exact hx.2)
    obtain ⟨i, hi, hiu⟩ := (CertificateChecks.Short3014.reach_iff u).1
      ((CertificateChecks.Short3014.memS_iff u).1 hm)
    refine ⟨dec u, ⟨u, ?_, rfl⟩, ?_⟩
    · rw [Finset.coe_image]
      refine ⟨i, ?_, hiu⟩
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      exact ⟨hi, by rw [hiu]; exact condD_of_mem hx hu hux⟩
    · change dec u + uStarCls = x
      rw [hux, add_assoc, two_add_self, add_zero]
  have hfin : ((fun y => y + uStarCls) '' (dec '' (S : Set ℕ))).Finite :=
    ((S.finite_toSet.image _).image _)
  calc babyDelta.ncard ≤ ((fun y => y + uStarCls) '' (dec '' (S : Set ℕ))).ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ (dec '' (S : Set ℕ)).ncard := Set.ncard_image_le (S.finite_toSet.image _)
    _ ≤ (S : Set ℕ).ncard := Set.ncard_image_le S.finite_toSet
    _ = S.card := Set.ncard_coe_finset S
    _ ≤ 46575 := Finset.card_image_le.trans card_pass.le

end CertificateChecks.KernelAP.Baby

end
