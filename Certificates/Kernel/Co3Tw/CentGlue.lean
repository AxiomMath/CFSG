module

public import Certificates.Kernel.Co3Tw.SiftChk
public import Certificates.Kernel.Co3Tw.VChk
public import CFSG.Certificates.Kernel.Misc.CentSrchSound
public import CFSG.Certificates.Kernel.Co3Tw.PairsSound
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.PermWitSound
public import CFSG.RankThree.Native.Co3FiveCentralizers

public section

namespace CertificateChecks.KernelCo3Tw

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Certificates.Native CFSG.Certificates
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.B3S3K CFSG.KC.PermWit CFSG.KC.Co3Tw
  CFSG.KC.CentSrch CertificateChecks.KernelSpor

@[expose] noncomputable def ppK (p : Nat) : Equiv.Perm (Fin 276) := permOfArr 276 (unpack 276 9 p)

theorem prep_ppK {p : Nat} (hp : CFSG.KC.Misc.ArrEnum.permB 276 9 p = true) :
    Orb.PRep 276 9 p (ppK p) :=
  Orb.prep_of_rep (rep_of_validA (validA_of hp))


theorem ppK_mem {p : Nat} (hp : CFSG.KC.Misc.ArrEnum.permB 276 9 p = true)
    (hs : siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 p = true) : ppK p ∈ co3P := by
  have h : siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0
      (unpack 276 9 p) = true := siftR_sound Co3C.binds Co3C.perm Co3C.hl hs
  exact mem_co3P_of_sift (rep_of_validA (validA_of hp)) h

theorem bp_lt : ∀ t < 7, pg 9 (mask 9) Co3C.BP t < 276 := by
  have h : allN 7 (fun t => Nat.blt (pg 9 (mask 9) Co3C.BP t) 276) = true := by decide +kernel
  exact fun t ht => Nat.le_of_ble_eq_true (Orb.allN_iff.1 h t ht)

theorem sepCo3 : SepB 276 9 Co3C.BP 7 co3P := by
  refine ⟨bp_lt, fun g hg hfix => ?_⟩
  refine co3Chain.eq_one_of_fixes_base co3Chain_valid.1 hg fun i => ?_
  have hv : ((co3Chain.base.get i : Fin 276) : ℕ) = co3ChainBaseArr[(i : ℕ)]! :=
    co3ChainArrays.base_val i
  have hi : (i : ℕ) < 7 := lt_of_lt_of_eq i.2 co3Chain_baseCount
  have hb := Co3C.binds.2.2.2.2.2.2 i hi
  have e : co3Chain.base.get i = ⟨pg 9 (mask 9) Co3C.BP i, bp_lt i hi⟩ :=
    Fin.ext (hv.trans hb)
  rw [e]
  exact hfix i hi (bp_lt i hi)

theorem hro : ∀ i < 7, roff 276 (276 * 9) (Co3C.LR i) + rcnt (Co3C.LR i) ≤ 65536 := by
  have h : allN 7 (fun i => Nat.ble (roff 276 (276 * 9) (Co3C.LR i) + rcnt (Co3C.LR i)) 65536) =
      true := by decide +kernel
  exact fun i hi => Nat.le_of_ble_eq_true (Orb.allN_iff.1 h i hi)

theorem card_cent_of {X Y DP : Nat} {pl : List Nat}
    (hX : CFSG.KC.Misc.ArrEnum.permB 276 9 X = true) (hY : CFSG.KC.Misc.ArrEnum.permB 276 9 Y = true)
    (sX : siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 X = true)
    (sY : siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 Y = true)
    (hpl : planOK 276 9 7 Co3C.BP DP pl 0 = true) (hd : dOK 276 9 X Y DP = true) :
    Nat.card ↥(co3P ⊓ Subgroup.centralizer ({ppK X, ppK Y} : Set (Equiv.Perm (Fin 276)))) =
      srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP DP [X, Y] pl 0 0 0 :=
  srch_sound co3ChainArrays (chainCheckFacts co3Order_check.1) co3Chain_valid.1 Co3C.binds
    Co3C.perm Co3C.hl co3Chain_baseCount hro (prep_ppK hX) (prep_ppK hY) (ppK_mem hX sX)
    (ppK_mem hY sY) hpl hd

theorem gk (k : Nat) (hk : k < 7) : CFSG.KC.Misc.ArrEnum.permB 276 9 (xpK k) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 276 9 (ypK k) = true := by
  have h := Orb.allN_iff.1 ch431008g k hk
  rwa [bA_eq, Bool.and_eq_true] at h

theorem sk (k : Nat) (hk : k < 7) : siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 (xpK k) = true ∧
    siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 (ypK k) = true := by
  have h := Orb.allN_iff.1 ch431008sd k hk
  rwa [bA_eq, Bool.and_eq_true] at h

noncomputable abbrev Cent (k : Nat) : Subgroup (Equiv.Perm (Fin 276)) :=
  co3P ⊓ Subgroup.centralizer ({ppK (xpK k), ppK (ypK k)} : Set (Equiv.Perm (Fin 276)))

theorem ts_eq : SD.ts0 = [SD.xp0, SD.yp0] ∧ SD.ts2 = [SD.xp2, SD.yp2] ∧
    SD.ts5 = [SD.xp5, SD.yp5] := by
  have h := ch431008ts
  rw [bA_eq, bA_eq, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
  exact h

theorem card_cent_k (k : Nat) (hk : k < 7) {DP : Nat} {pl : List Nat}
    (hpl : planOK 276 9 7 Co3C.BP DP pl 0 = true) (hd : dOK 276 9 (xpK k) (ypK k) DP = true) :
    Nat.card (Cent k) = srch 276 9 7 Co3C.LR Co3C.TR Co3C.TRI Co3C.BP DP [xpK k, ypK k] pl 0 0 0 :=
  card_cent_of (gk k hk).1 (gk k hk).2 (sk k hk).1 (sk k hk).2 hpl hd

theorem card_cent0 : Nat.card (Cent 0) = 486 := by
  have h := Nat.eq_of_beq_eq_true ch431008s0
  rw [ts_eq.1] at h
  exact (card_cent_k 0 (by norm_num) ch431008p0 ch431008d0).trans h

theorem card_cent1 : Nat.card (Cent 1) = 1458 :=
  (card_cent_k 1 (by norm_num) ch431008p1 ch431008d1).trans (Nat.eq_of_beq_eq_true ch431008t1)

theorem card_cent2 : Nat.card (Cent 2) = 81 := by
  have h := Nat.eq_of_beq_eq_true ch431008s2
  rw [ts_eq.2.1] at h
  exact (card_cent_k 2 (by norm_num) ch431008p2 ch431008d2).trans h

theorem card_cent3 : Nat.card (Cent 3) = 972 :=
  (card_cent_k 3 (by norm_num) ch431008p3 ch431008d3).trans (Nat.eq_of_beq_eq_true ch431008t3)

theorem card_cent4 : Nat.card (Cent 4) = 972 :=
  (card_cent_k 4 (by norm_num) ch431008p4 ch431008d4).trans (Nat.eq_of_beq_eq_true ch431008t4)

theorem card_cent5 : Nat.card (Cent 5) = 54 := by
  have h := Nat.eq_of_beq_eq_true ch431008s5
  rw [ts_eq.2.2] at h
  exact (card_cent_k 5 (by norm_num) ch431008p5 ch431008d5).trans h

theorem card_cent6 : Nat.card (Cent 6) = 54 :=
  (card_cent_k 6 (by norm_num) ch431008p6 ch431008d6).trans (Nat.eq_of_beq_eq_true ch431008t6)

section Closed

variable {Γ : Type*} [Group Γ]


theorem mem_sylow_of_pow {H : Subgroup Γ} [Finite H] (P : Sylow 3 H)
    (hP : (P : Subgroup H).Normal) (c : H) {m : ℕ} (hm : c ^ 3 ^ m = 1) :
    c ∈ (P : Subgroup H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz : IsPGroup 3 (Subgroup.zpowers c) := by
    refine IsPGroup.of_card (n := (orderOf c).factorization 3) ?_
    rw [Nat.card_zpowers]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hm)
    rw [hi, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  have : Unique (Sylow 3 H) := Sylow.unique_of_normal P hP
  rw [← Subsingleton.elim Q P]
  exact hQ (Subgroup.mem_zpowers c)

theorem closed_of_normal {H : Subgroup Γ} [Finite H] (P : Sylow 3 H)
    (hP : (P : Subgroup H).Normal) {a b : Γ} (ha : a ∈ H) (hb : b ∈ H)
    (ha3 : ∃ m, a ^ 3 ^ m = 1) (hb3 : ∃ m, b ^ 3 ^ m = 1) : ∃ m, (a * b) ^ 3 ^ m = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := ha3
  obtain ⟨m', hm'⟩ := hb3
  have hA := mem_sylow_of_pow P hP ⟨a, ha⟩ (m := m) (Subtype.ext (by simpa using hm))
  have hB := mem_sylow_of_pow P hP ⟨b, hb⟩ (m := m') (Subtype.ext (by simpa using hm'))
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨_, (P : Subgroup H).mul_mem hA hB⟩
  exact ⟨k, by simpa using congrArg (fun z : (P : Subgroup H) => ((z : H) : Γ)) hk⟩

theorem normal_sylow_of_card {H : Subgroup Γ} {e m : ℕ} (hc : Nat.card H = 3 ^ e * m)
    (hm1 : 0 < m) (hm : m ≤ 2) : ∃ _ : Finite H, ∃ P : Sylow 3 H, (P : Subgroup H).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  refine ⟨hfin, ?_⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  refine ⟨P, ?_⟩
  have h3 : ¬ 3 ∣ m := by omega
  have hfac : (Nat.card H).factorization 3 = e := by
    rw [hc, Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd h3, add_zero]
  have hPc : Nat.card (P : Subgroup H) = 3 ^ e := by rw [P.card_eq_multiplicity, hfac]
  have hidx : (P : Subgroup H).index = m := by
    have := (P : Subgroup H).card_mul_index
    rw [hPc, hc] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  rcases (by omega : m = 1 ∨ m = 2) with rfl | rfl
  · rw [Subgroup.index_eq_one.1 hidx]
    infer_instance
  · exact Subgroup.normal_of_index_eq_two hidx

theorem normal_of_normalizer {H : Subgroup Γ} [Finite H] (hc : Nat.card H = 972) {V : Subgroup H}
    (hV : Nat.card V = 243) {c : H} (hcN : c ∈ Subgroup.normalizer (V : Set H)) (hcV : c ∉ V) :
    V.Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card H).factorization 3 = 5 := by
    rw [hc, show (972 : ℕ) = 3 ^ 5 * 4 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hidx := Sylow.card_eq_index_normalizer (Sylow.ofCard V (by rw [hV, hfac]; norm_num))
  replace hidx : Nat.card (Sylow 3 H) = (Subgroup.normalizer (V : Set H)).index := hidx
  have hn := card_sylow_modEq_one 3 H
  have hmod : (Subgroup.normalizer (V : Set H)).index % 3 = 1 := by
    rw [← hidx]
    exact hn
  set N := Subgroup.normalizer (V : Set H) with hN
  have hle : V ≤ N := Subgroup.le_normalizer
  have hdvd : Nat.card V ∣ Nat.card N := Subgroup.card_dvd_of_le hle
  have hne : Nat.card N ≠ 243 := by
    intro h
    have e := Subgroup.eq_of_le_of_card_ge hle (le_of_eq (h.trans hV.symm))
    exact hcV (by rw [e]; exact hcN)
  have hmul := N.card_mul_index
  rw [hc] at hmul
  rw [hV] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  rw [hq] at hmul hne
  have hq4 : q * N.index = 4 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 243) (by rw [← mul_assoc]; omega)
  have hi : N.index = 1 := by
    have h1 : N.index ∣ 4 := Dvd.intro_left q hq4
    have h2 : N.index ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    interval_cases h : N.index <;> omega
  exact Subgroup.normalizer_eq_top_iff.1 (Subgroup.index_eq_one.1 hi)

end Closed


theorem closed_cent_small {k : Nat} (hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 5 ∨ k = 6) {a b : Equiv.Perm (Fin 276)}
    (ha : a ∈ Cent k) (hb : b ∈ Cent k) (ha3 : ∃ m, a ^ 3 ^ m = 1) (hb3 : ∃ m, b ^ 3 ^ m = 1) :
    ∃ m, (a * b) ^ 3 ^ m = 1 := by
  have hc : ∃ e m : ℕ, 0 < m ∧ m ≤ 2 ∧ Nat.card (Cent k) = 3 ^ e * m := by
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact ⟨5, 2, by norm_num, by norm_num, card_cent0⟩
    · exact ⟨6, 2, by norm_num, by norm_num, card_cent1⟩
    · exact ⟨4, 1, by norm_num, by norm_num, card_cent2⟩
    · exact ⟨3, 2, by norm_num, by norm_num, card_cent5⟩
    · exact ⟨3, 2, by norm_num, by norm_num, card_cent6⟩
  obtain ⟨e, m, hm1, hm2, hcard⟩ := hc
  obtain ⟨_, P, hP⟩ := normal_sylow_of_card hcard hm1 hm2
  exact closed_of_normal P hP ha hb ha3 hb3

end CertificateChecks.KernelCo3Tw

end
