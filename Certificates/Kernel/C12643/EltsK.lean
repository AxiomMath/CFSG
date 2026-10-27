module

public import Certificates.Kernel.C12643.Enum
public import Certificates.Kernel.Misc.Perm.J2EnumS
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC12643

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155
open CFSG.ComponentClassification.J2Cover CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2Fam (R)

theorem rX7 : R x7A X7 := ⟨hx7, pX7⟩
theorem rX5a : R x5aA X5A := ⟨hx5a, pX5A⟩
theorem rX5c : R x5cA X5C := ⟨hx5c, pX5C⟩
theorem rY2 : R y2A Y2 := ⟨hy2, pY2⟩
theorem rE1 : R e1A E1 := ⟨he1, pE1⟩
theorem rE2 : R e2A E2 := ⟨he2, pE2⟩

theorem rG5a {k : ℕ} (hk : k < 2) : R gC5a[k]! (GC5A k) :=
  ⟨hg5a k hk, by interval_cases k <;> quickRfl⟩
theorem rG5c {k : ℕ} (hk : k < 2) : R gC5c[k]! (GC5C k) :=
  ⟨hg5c k hk, by interval_cases k <;> quickRfl⟩
theorem rGE {k : ℕ} (hk : k < 2) : R gCE[k]! (GCEP k) :=
  ⟨hgE k hk, by interval_cases k <;> quickRfl⟩
theorem rGD {k : ℕ} (hk : k < 2) : R gD[k]! (GDP k) :=
  ⟨hgD k hk, by interval_cases k <;> quickRfl⟩
theorem rLN {k : ℕ} (hk : k < 6) : R lineA[k]! (LNP k) :=
  ⟨hln k hk, by interval_cases k <;> quickRfl⟩
theorem rTR {k : ℕ} (hk : k < 6) : R transA[k]! (TRP k) :=
  ⟨htr k hk, by interval_cases k <;> quickRfl⟩
theorem rDU {k : ℕ} (hk : k < 2) : R dUA[k]! (DUP k) :=
  ⟨hdu k hk, by interval_cases k <;> quickRfl⟩
theorem rDV {k : ℕ} (hk : k < 2) : R dVA[k]! (DVP k) :=
  ⟨hdv k hk, by interval_cases k <;> quickRfl⟩
theorem rG7 {k : ℕ} (hk : k < 1) : R gC7[k]! (G7 k) :=
  ⟨hg7 k hk, by interval_cases k; quickRfl⟩

theorem okx7 : okA x7A = true := rX7.ok (by quickRfl) (by quickRfl)
theorem okx5a : okA x5aA = true := rX5a.ok (by quickRfl) (by quickRfl)
theorem okx5c : okA x5cA = true := rX5c.ok (by quickRfl) (by quickRfl)
theorem oky2 : okA y2A = true := rY2.ok (by quickRfl) (by quickRfl)
theorem oke1 : okA e1A = true := rE1.ok (by quickRfl) (by quickRfl)
theorem oke2 : okA e2A = true := rE2.ok (by quickRfl) (by quickRfl)

theorem ok5aG (k : ℕ) (hk : k < 2) : okA gC5a[k]! = true := by
  interval_cases k <;> exact (rG5a (by norm_num)).ok (by quickRfl) (by quickRfl)
theorem ok5cG (k : ℕ) (hk : k < 2) : okA gC5c[k]! = true := by
  interval_cases k <;> exact (rG5c (by norm_num)).ok (by quickRfl) (by quickRfl)
theorem okEG (k : ℕ) (hk : k < 2) : okA gCE[k]! = true := by
  interval_cases k <;> exact (rGE (by norm_num)).ok (by quickRfl) (by quickRfl)
theorem okDG (k : ℕ) (hk : k < 2) : okA gD[k]! = true := by
  interval_cases k <;> exact (rGD (by norm_num)).ok (by quickRfl) (by quickRfl)
theorem okLN (k : ℕ) (hk : k < 6) : okA lineA[k]! = true := by
  interval_cases k <;> exact (rLN (by norm_num)).ok (by quickRfl) (by quickRfl)
theorem okTR (k : ℕ) (hk : k < 6) : okA transA[k]! = true := by
  interval_cases k <;> exact (rTR (by norm_num)).ok (by quickRfl) (by quickRfl)
theorem okDU (k : ℕ) (hk : k < 2) : okA dUA[k]! = true := by
  interval_cases k <;> exact (rDU (by norm_num)).ok (by quickRfl) (by quickRfl)
theorem okDV (k : ℕ) (hk : k < 2) : okA dVA[k]! = true := by
  interval_cases k <;> exact (rDV (by norm_num)).ok (by quickRfl) (by quickRfl)

theorem ok7G (k : ℕ) (hk : k < 1) : okA gC7[k]! = true := by
  interval_cases k
  exact okx7

theorem okSplit {a : Array ℕ} (h : okA a = true) : validA 315 a = true ∧ inP a = true := by
  unfold okA at h
  rwa [Bool.and_eq_true] at h

theorem allA {a : Array (Array ℕ)} {m : ℕ} (hs : a.size = m) {F : Array ℕ → Bool}
    (h : ∀ k < m, F a[k]! = true) : a.all F = true := by
  rw [CertificateChecks.KernelMisc.J2En.arrAll, hs]
  exact List.all_eq_true.2 fun j hj => h j (List.mem_range.1 hj)

theorem cm5aG (k : ℕ) (hk : k < 2) : commA gC5a[k]! x5aA = true := by
  rw [(rG5a hk).commA rX5a]
  interval_cases k <;> quickRfl
theorem cm5cG (k : ℕ) (hk : k < 2) : commA gC5c[k]! x5cA = true := by
  rw [(rG5c hk).commA rX5c]
  interval_cases k <;> quickRfl
theorem cm7G (k : ℕ) (hk : k < 1) : commA gC7[k]! x7A = true := by
  rw [(rG7 hk).commA rX7]
  interval_cases k
  quickRfl
theorem cmEG (k : ℕ) (hk : k < 2) : commA gCE[k]! e1A = true ∧ commA gCE[k]! e2A = true := by
  rw [(rGE hk).commA rE1, (rGE hk).commA rE2]
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem eltsOK_K : eltsOK () = true := by
  unfold eltsOK
  rw [okx7, okx5a, okx5c, oky2, oke1, oke2, allA g5a_size ok5aG, allA g5c_size ok5cG,
    allA gE_size okEG, allA gD_size okDG, allA ln_size okLN, allA tr_size okTR,
    allA du_size okDU, allA dv_size okDV, (rX7.pow 7).eq R.id, (rX5a.pow 5).eq R.id,
    (rX5c.pow 5).eq R.id, (rE1.pow 2).eq R.id, (rE2.pow 2).eq R.id, rX7.eq R.id, rX5a.eq R.id,
    rX5c.eq R.id, rE1.eq R.id, rE2.eq R.id, rE1.eq rE2, rE1.commA rE2, rE1.commA rX5a,
    rE2.commA rX5a]
  quickRfl

theorem enumsOK_K : enumsOK (c5a ()) (c5c ()) (c7 ()) (cE ()) (cD ()) (cS5 ()) = true := by
  unfold enumsOK
  rw [bfs5a.1, bfs5a.2, bfs5c.1, bfs5c.2, bfs7.1, bfs7.2, bfsE.1, bfsE.2, bfsD.1, bfsD.2,
    bfsS5.1, bfsS5.2, allA (F := fun t => commA t x5aA) g5a_size cm5aG,
    allA (F := fun t => commA t x5cA) g5c_size cm5cG,
    allA (F := fun t => commA t e1A && commA t e2A) gE_size fun k hk => by
      rw [Bool.and_eq_true]
      exact cmEG k hk]
  rfl

end CertificateChecks.KernelC12643

end
