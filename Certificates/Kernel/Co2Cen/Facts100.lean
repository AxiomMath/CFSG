module

public import Certificates.Kernel.Co2Cen.GlueBase
public import Certificates.Kernel.Co2Cen.Scan8
public import Certificates.Kernel.Co2Cen.Cent
public import Certificates.Kernel.Co2Cen.Img
public import CFSG.Certificates.Kernel.Co2Cen.Glue
public import CFSG.RankThree.Co2.C4Facts

public section

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J CFSG.KC.Co2Cen
  CFSG.KC.TabMatGrp CertificateChecks.KernelSpor.Co2Syl CertificateChecks.KernelSpor.Co2Cls
  CertificateChecks.KernelSpor.Co2TInv CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem lam_facts {y : M22} (hy : CrConj (repMat 2) y ∨ CrConj (repMat 7) y)
    (hc : y * repMat 8 = repMat 8 * y)
    (hp : y * repMat 8 = repMat 0 ∨ CrConj (repMat 2) (y * repMat 8) ∨
      CrConj (repMat 7) (y * repMat 8)) : y = repMat 7 := by
  have hr : (y * repMat 8 + 1).rank = 6 := by
    rcases hp with e | e | e
    · rw [e]
      exact rk_rep.1
    · exact rank_InA ⟨2, by simp, e⟩
    · exact rank_InA ⟨7, by simp, e⟩
  rw [Co2Syl.repMat_eq (by norm_num : 8 < 10)] at hc hr
  have key : ∀ {CF CR : ℕ → ℕ} {k : ℕ},
      scanC CF CR (fun X _ => Nat.beq X (RP 7)) (RP 8) 6 k = true → MatP 22 (elemAt CF k) = y →
      y = repMat 7 := by
    intro CF CR k h e
    subst e
    rcases scanC_sound h hc with ⟨-, hx⟩ | hx
    · rw [Nat.eq_of_beq_eq_true hx, Co2Syl.repMat_eq (by norm_num)]
    · exact absurd hr hx
  rcases hy with h | h
  · obtain ⟨k, hk, e⟩ := rec_of_conj2 h
    exact key (scan28 k hk) e
  · obtain ⟨k, hk, e⟩ := rec_of_conj7 h
    exact key (scan78 k hk) e

theorem zuGenWords_lt : ∀ k < 4, ∀ l ∈ zuGenWords[k]!, l < 42 := by decide +kernel

theorem MatP_GA {k : ℕ} (hk : k < 4) : MatP 22 (GA k) = wordMat zuGenWords[k]! := by
  rw [Nat.eq_of_beq_eq_true (gaZu k hk), MatP_wordK (zuGenWords_lt k hk)]

theorem zu_sq {k : ℕ} (hk : k < 4) : wordMat zuGenWords[k]! * wordMat zuGenWords[k]! = 1 := by
  rw [← MatP_GA hk]
  exact (jGen_sound aGen).1 k (by omega)

theorem zu_comm {k j : ℕ} (hk : k < 4) (hj : j < 4) :
    wordMat zuGenWords[k]! * wordMat zuGenWords[j]! =
      wordMat zuGenWords[j]! * wordMat zuGenWords[k]! := by
  rw [← MatP_GA hk, ← MatP_GA hj]
  exact (jGen_sound aGen).2 k (by omega) j (by omega)

theorem zuMatN_eq (m : ℕ) : ∀ n ≤ 4, zuMatN n m = bitProd (fun i => MatP 22 (GA i)) n m
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [zuMatN, bitProd]
    rw [zuMatN_eq m n (by omega), MatP_GA (by omega : n < 4)]

theorem MatP_AE {m : ℕ} (hm : m < 16) : MatP 22 (AE m) = zuMat m := by
  rw [((jEnum_sound aEnum).1 m (by omega)).2, zuMat, zuMatN_eq m 4 le_rfl]
  exact bitProd_high _ (by norm_num; omega) 10 (by norm_num)

theorem pow8 : ∀ x ∈ genMon G8, x ^ 32 = 1 := by
  rw [genMon8]
  exact facts8.1.pow

theorem zu_central {m : ℕ} (hm : m < 16) :
    zuMat m ∈ matGrp pWords8 ∧ ∀ y ∈ matGrp pWords8, zuMat m * y = y * zuMat m := by
  have h := fixK_central aGen aEnum aInP8 coord8 fix8 hm
  rw [F8_eq m hm, MatP_AE hm, genMon8] at h
  exact h

theorem central_zu (hc : Nat.card (matGrp pWords8) ≤ 2 ^ 14) {x : M22}
    (hx : x ∈ matGrp pWords8) (hz : ∀ y ∈ matGrp pWords8, x * y = y * x) :
    ∃ m < 16, x = zuMat m := by
  rw [← genMon8] at hc hx hz
  obtain ⟨i, hi, e⟩ := center_of_fixK aGen aEnum aInP8 coord8 (unit_of_pow pow8) fix8
    (treeNK_spec img8) (hc.trans (by norm_num)) hx hz
  rw [F8_eq i hi, MatP_AE hi] at e
  exact ⟨i, hi, e⟩

theorem zuCls_eq : ∀ m < 16, zuCls[m]! = zuClsT.getD m 0 := by decide

theorem zu_cls {m : ℕ} (h0 : 0 < m) (hm : m < 16) :
    CrConj (repMat zuCls[m]!) (zuMat m) := by
  obtain ⟨-, h⟩ := crConj_look (by norm_num) (lookZ (m - 1) (by omega))
  have e : m - 1 + 1 = m := by omega
  rw [lookZ_cls (m - 1) (by omega), e, MatP_AE hm] at h
  rw [zuCls_eq m hm]
  exact h

theorem c4Facts : C4Facts where
  lam _ hy hc hp := lam_facts hy hc hp
  sq _ hk := zu_sq hk
  comm _ hk _ hj := zu_comm hk hj
  mem _ hm := zu_central hm
  all hc _ hx hz := central_zu hc hx hz
  cls _ h0 hm := zu_cls h0 hm

end CertificateChecks.KernelSpor.Co2Cen

end
