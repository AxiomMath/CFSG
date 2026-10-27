module

public import Certificates.Kernel.C12643.EltsK
public import Certificates.Kernel.Misc.Perm.J2Elts45
public import CFSG.Certificates.Kernel.Misc.EnumBfsMem
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC12643

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155
open CFSG.ComponentClassification.J2Cover CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2Fam (R pw iv)
open CertificateChecks.KernelMisc.J2C3 (hw cm I all_of_chunks)
open CertificateChecks.KernelMisc.J2En (certL_bound ptPerm)
open CFSG.KC.EnumBfs (enumBfs_mem allLt_congr_of_mem any_congr_of_mem)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem memS5 : ∀ x, x ∈ (cS5 ()).pts ↔ x ∈ cS5L.pts :=
  enumBfs_mem enumS5 (by rw [sizeS5]; norm_num)

theorem memE : ∀ x, x ∈ (cE ()).pts ↔ x ∈ cEL.pts :=
  enumBfs_mem enumE (by rw [sizeE]; norm_num)

theorem memD : ∀ x, x ∈ (cD ()).pts ↔ x ∈ cDL.pts :=
  enumBfs_mem enumD (by rw [sizeD]; norm_num)

theorem inE {t : Array ℕ} {p : ℕ} (ht : R t p) : inCert (cE ()) t = memK 240 (lget CEP) p := by
  have b := certL_bound 240 2 CEP CEE CER CEL
  unfold inCert
  rw [any_congr_of_mem memE, ht.1]
  exact any_eqA_unpack hw b.1 b.2.1 (ptPerm (all_of_chunks 60 4 c12643ptES)) ht.2

theorem inD {t : Array ℕ} {p : ℕ} (ht : R t p) : inCert (cD ()) t = memK 60 (lget DP) p := by
  have b := certL_bound 60 2 DP DE DR DL
  unfold inCert
  rw [any_congr_of_mem memD, ht.1]
  exact any_eqA_unpack hw b.1 b.2.1 (ptPerm (all_of_chunks 60 1 c12643ptDS)) ht.2

@[expose] noncomputable def lnK (p : ℕ) : Bool :=
  Nat.beq p I || (List.range 6).any fun j => (List.range 5).any fun e => Nat.beq p (pw (LNP j) e)

theorem lnAll : ∀ k < 25, lnK (lget S5P k) = true :=
  (CFSG.KC.Misc.Clos.allN_iff _ _).1 (by quickRfl)

@[expose] noncomputable def CAS : ℕ → ℕ := lget [X5C, X5A, X5A, X5C, X5A, X5C]

theorem rCase {j : ℕ} (hj : j < 6) : R caseA[recL.getD j 0]! (CAS j) := by
  interval_cases j
  · exact rX5c
  · exact rX5a
  · exact rX5a
  · exact rX5c
  · exact rX5a
  · exact rX5c

theorem lines_pts : allLt (cS5 ()).pts.size (fun k => eqA 315 (cS5 ()).pts[k]! (idA 315) ||
      (List.range 6).any fun j => (List.range 5).any fun e =>
        eqA 315 (cS5 ()).pts[k]! (powArr 315 lineA[j]! e)) = true := by
  refine (allLt_congr_of_mem memS5 fun t => eqA 315 t (idA 315) ||
      (List.range 6).any fun j => (List.range 5).any fun e =>
        eqA 315 t (powArr 315 lineA[j]! e)).trans ?_
  have b : ∀ i < 25, cS5L.pts[i]! = unpack 315 9 (lget S5P i) :=
    (certL_bound 25 2 S5P S5E S5R S5L).2.1
  rw [sizeS5, allLt_iff]
  intro k hk
  have rk : R cS5L.pts[k]! (lget S5P k) :=
    ⟨b k hk, ptPerm (all_of_chunks 25 1 c12643ptSS) k hk⟩
  have h := lnAll k hk
  unfold lnK at h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at h ⊢
  rcases h with h | ⟨j, hj, e, he, h⟩
  · rw [rk.eq R.id]
    exact Or.inl h
  · refine Or.inr ⟨j, hj, e, he, ?_⟩
    rw [rk.eq ((rLN hj).pow e)]
    exact h

theorem lines_tr : allLt 6 (fun j => eqA 315 (powArr 315 lineA[j]! 5) (idA 315) &&
      decide (recL.getD j 0 < 2) &&
      eqA 315 (conjA 315 transA[j]! caseA[recL.getD j 0]!) lineA[j]!) = true := by
  rw [allLt_iff]
  intro j hj
  rw [((rLN hj).pow 5).eq R.id, ((rTR hj).conj (rCase hj)).eq (rLN hj)]
  interval_cases j <;> quickRfl

theorem linesOK_K : linesOK (cS5 ()) = true := by
  unfold linesOK
  rw [lines_pts, lines_tr, ln_size, tr_size]
  rfl

theorem dOK_K : dOK (cE ()) (cD ()) = true := by
  have hA : gD.all (inCert (cE ())) = true := allA gD_size fun k hk => by
    rw [inE (rGD hk)]
    interval_cases k <;> quickRfl
  have hB : allLt gD.size (fun i => inCert (cD ()) dUA[i]! && inCert (cD ()) dVA[i]! &&
      eqA 315 gD[i]! (commutatorA 315 dUA[i]! dVA[i]!)) = true := by
    rw [gD_size, allLt_iff]
    intro i hi
    rw [inD (rDU hi), inD (rDV hi), (rGD hi).eq ((rDU hi).commt (rDV hi))]
    interval_cases i <;> quickRfl
  unfold dOK
  rw [hA, hB, du_size, dv_size, gD_size, inD rE1, inD rE2, inD (rE1.comp rE2)]
  quickRfl

end CertificateChecks.KernelC12643

end
