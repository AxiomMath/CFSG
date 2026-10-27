
module

public import Certificates.Kernel.HMathieu.Fix7062
public import CFSG.Certificates.Kernel.HMathieu.FixCertSound

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu
open CertificateChecks.KernelHMathieu

public section

namespace CertificateChecks.Batch7062

theorem fixMasks_single {X : Type} (n : ℕ) (f : X → ℕ → ℕ) (s : X) :
    fixMasks n f [s] = (List.range (2 ^ n)).filter fun m => f s m == m := by
  simp [fixMasks]

theorem getD_mem_take {l : List (List ℕ)} {k r : ℕ} (hk : k < r) (hl : k < l.length) :
    l.getD k [] ∈ l.take r := by
  rw [List.getD_eq_getElem _ _ hl]
  exact List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp⟩

theorem count_eq {f : ℕ → ℕ} (hf : XorLin f) {Js Ks : List (List ℕ)}
    (h1 : allImg 11 4 Fix7062.mats4 Js = true) (h2 : allKer 11 7 Fix7062.mats4 Ks = true)
    (hM : matOf 11 f ∈ Fix7062.mats4) :
    ((List.range (2 ^ 11)).filter fun m => f m == m).length = 2 ^ 7 := by
  have e : (List.range (2 ^ 11)).filter (fun m => f m == m) =
      (List.range (2 ^ 11)).filter (fun m => actM (matOf 11 f) m == m) :=
    List.filter_congr fun m hm => by rw [actM_matOf hf 11 m (List.mem_range.1 hm)]
  rw [e]
  exact le_antisymm (allImg_sound h1 _ hM) (allKer_sound h2 _ hM)

end CertificateChecks.Batch7062

