module

public import CFSG.Monster.B.Dyadic.Facts
public import CFSG.Certificates.Kernel.BabyMonster.LatStats
public import Certificates.Kernel.BabyMonster.LatBind
public import Certificates.Kernel.BabyMonster.LaneCont
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.LatBind.All
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.B64 CFSG.Monster.B.Dyadic
  CFSG.Monster.B.Dyadic.Native CertificateChecks.KernelBM.Lat

theorem fact3102_of : Fact3102 := by
  have hd : ∀ i < 4371, (48 ≤ chAt (getP CFSG.KD.LatBind.CH 0).1 i ∧
      chAt (getP CFSG.KD.LatBind.CH 0).1 i ≤ 55) ∧
      fld (recOf CFSG.KC.BM.Dyadic.Bs i) 0 = 2 ^ (chAt (getP CFSG.KD.LatBind.CH 0).1 i - 48) :=
    diagOK_sound CFSG.KD.LatBind.diag
  have hde : ∀ i < 4371, diagExpK[i]! = chAt (getP CFSG.KD.LatBind.CH 0).1 i - 48 := by
    rw [diagExpK, CertificateChecks.KernelBM.Lat.text_eq]
    exact diagExpOf_eq CFSG.KD.LatBind.diag
  have hbz : ∀ t k : Fin 4371, Bz t k = (ent CFSG.KC.BM.Dyadic.Bs t k : ℤ) := by
    intro t k
    rw [Bz, basisRowsK, basisRows_of_text t k t.2 k.2]
    rfl
  refine ⟨fun i => ?_, fun i => ?_, fun i k hk => ?_, fun i k hk => ?_, fun i => ?_⟩
  · rw [hde i i.2]
    have := (hd i i.2).1
    omega
  · rw [hbz, ent, ite_eq_right (lt_irrefl _), Nat.sub_self, (hd i i.2).2, hde i i.2]
    push_cast
    rfl
  · rw [hbz, ent, ite_eq_left (Fin.lt_def.1 hk)]
    rfl
  · have hk' := Fin.lt_def.1 hk
    have := k.2
    rw [hbz, ent, ite_eq_right (by omega)]
    exact_mod_cast dyRowOK_sound (by decide) (rows i i.2) (k - i) (by omega) (by omega)
  · have hp : ∀ i < 4371, chAt (getP CFSG.KD.LatBind.CH 0).1 i - 48 ≤ 7 ∧
        fld (recOf CFSG.KC.BM.Dyadic.Bs i) 0 = 2 ^ (chAt (getP CFSG.KD.LatBind.CH 0).1 i - 48) :=
      fun i hi => ⟨by have := (hd i hi).1; omega, (hd i hi).2⟩
    have hq : ∀ i < 4371, ∃ q : ℕ → ℤ, ∀ c < 4371, i < c →
        ((128 / fld (recOf CFSG.KC.BM.Dyadic.Bs i) 0 * ent CFSG.KC.BM.Dyadic.Bs i c : ℕ) : ℤ) ≡
          ∑ j ∈ Finset.Ico (i + 1) 4371, q j * (ent CFSG.KC.BM.Dyadic.Bs j c : ℤ) [ZMOD 128] := by
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
      · exact contOK_sound blocks rows hi (conts i h)
      · exact ⟨0, fun c hc hic => absurd hic (by omega)⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (contain_of hp hq i)
    refine ⟨c, fun k => ?_⟩
    have := congrFun hc k
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at this
    simp only [hbz]
    exact this

end CertificateChecks.KernelBM.Dy

end
