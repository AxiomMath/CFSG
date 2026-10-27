module

public import Certificates.Kernel.Co2J.Checks
public import Certificates.Kernel.Co2J.Sets
public import Certificates.Kernel.Co2J.Letters
public import Certificates.Kernel.Co2Syl.Letters
public import CFSG.Certificates.Kernel.Co2J.Glue
public import CFSG.Certificates.Kernel.Co2Syl.Words
public import CFSG.RankThree.Co2.JFacts

public section

namespace CertificateChecks.KernelSpor.Co2J

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2J CFSG.KC.TabMatGrp CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem MatP_wordK' {w : List ℕ} (hw : ∀ l ∈ w, l < 42) :
    MatP 22 (CertificateChecks.KernelSpor.Co2Syl.wordK w) = wordMat w :=
  MatP_foldR_eq
    (f := CertificateChecks.KernelSpor.Co2Syl.lAt CertificateChecks.KernelSpor.Co2Syl.LT) fun l hl => (rowsMat_eq_MatP (CertificateChecks.KernelSpor.Co2Syl.letters l (hw l hl))).symm

theorem MatP_G {k : ℕ} (hk : k < 5) : MatP 22 (G k) = wordMat sylWords[k]! := by
  rw [Nat.eq_of_beq_eq_true (gensT k hk), MatP_wordK' (sylWords_lt k hk)]

theorem MatP_GJ {i : ℕ} (hi : i < 10) : MatP 22 (GJ i) = wordMat jWords[i]! := by
  rw [Nat.eq_of_beq_eq_true (gensJ i hi), MatP_wordK' (jWords_lt i hi)]

theorem genMon_G : genMon G = matGrp sylWords :=
  genMon_eq_matGrp (fun j hj => ⟨j, by rw [sylWords_size]; exact hj, MatP_G hj⟩) fun k hk => by
    rw [sylWords_size] at hk
    exact ⟨k, hk, MatP_G hk⟩

section Gen

variable {H : ℕ → ℕ}

theorem genJ_eq {ws : Array (List ℕ)} (hs : ws.size = 10)
    (hH : ∀ i < 10, MatP 22 (H i) = wordMat ws[i]!) : genJ H = matGrp ws := by
  unfold genJ matGrp
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    refine ⟨⟨i, by rw [hs]; exact hi⟩, ?_⟩
    change wordMat ws[i] = MatP 22 (H i)
    rw [hH i hi, getElem!_pos ws i (by rw [hs]; exact hi)]
  · rintro ⟨⟨i, hi⟩, rfl⟩
    have hi' : i < 10 := by rw [hs] at hi; exact hi
    refine ⟨⟨i, hi'⟩, ?_⟩
    change MatP 22 (H i) = wordMat ws[i]
    rw [hH i hi', getElem!_pos ws i hi]

variable (hH : ∀ i < 10, MatP 22 (H i) = wordMat jWords[i]!)

include hH in
theorem jMatN_eq (v : ℕ) : ∀ n ≤ 10, jMatN n v = bitProd (fun i => MatP 22 (H i)) n v
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [jMatN, bitProd]
    rw [jMatN_eq v n (by omega), hH n (by omega)]

end Gen

theorem genJ_GJ : genJ GJ = matGrp jWords := genJ_eq jWords_size fun _ hi => MatP_GJ hi

theorem jMat_eq : jMat = bitProd (fun i => MatP 22 (GJ i)) 10 :=
  funext fun v => jMatN_eq (fun _ hi => MatP_GJ hi) v 10 le_rfl

theorem pow32 : ∀ x ∈ genMon G, x ^ 32 = 1 := utK_sound ut

theorem treeR : TreeI PE PM PS PT MK := treeIK_spec tree

theorem tFacts : TFacts where
  pow := by rw [← genMon_G]; exact pow32
  card := by rw [← genMon_G]; exact card_T jGen jEnum jInT coord pow32 treeR

theorem jFacts : JFacts where
  sq i hi := by rw [← MatP_GJ hi]; exact (jGen_sound jGen).1 i hi
  comm i hi k hk := by rw [← MatP_GJ hi, ← MatP_GJ hk]; exact (jGen_sound jGen).2 i hi k hk
  bij := by rw [← genJ_GJ, jMat_eq]; exact jm_bij jGen jEnum
  le := by rw [← genJ_GJ, ← genMon_G]; exact genJ_le jInT
  norm := by
    rw [← genJ_GJ, ← genMon_G]
    exact fun t ht x hx => normalizes jGen jEnum coord ht hx
  cent := by
    rw [← genJ_GJ, ← genMon_G]
    exact fun hc t ht hJ => cent_le jGen jEnum jInT coord pow32 treeR hc ht hJ
  ea := by
    rw [← genJ_GJ, ← genMon_G]
    exact fun hc A hAT h1 hmul hcomm hsq hA => ea_unique jGen jEnum jInT coord pow32 treeR invAll
      tab (Nat.eq_of_beq_eq_true sm0) (by norm_num) sets hc A hAT h1 hmul hcomm hsq hA

end CertificateChecks.KernelSpor.Co2J

end
