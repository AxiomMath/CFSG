module

public import Certificates.Kernel.Co1M.Base10077
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KD.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.TreeK

theorem fr77_sym : symK AP77 = true := by quickRfl

theorem fr77_dist_chk : distFK AP77 om77 = true := by quickRfl

theorem fr77_dist : ∀ i j k l, i < 24 → j < 24 → k < 24 → l < 24 → i ≠ j → k ≠ l →
    (avK AP77 i j = avK AP77 k l ∨ avK AP77 i j = avK AP77 k l ^^^ om77) →
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) :=
  dist_spec fr77_dist_chk fr77_sym

theorem fr77_symm : ∀ i < 24, ∀ j < 24, avK AP77 i j = avK AP77 j i := sym_spec fr77_sym

theorem ind77_n1_chk : indK AP77 om77 N1T77 P77n1 = true := by quickRfl

theorem ind77_n2_chk : indK AP77 om77 N2T77 P77n2 = true := by quickRfl

theorem ind77_sB_chk : indK AP77 om77 SBT77 P77sB = true := by quickRfl

theorem ind77_e0_chk : ind1K AP77 om77 (getL 0 ET77 0) = true := by quickRfl

theorem ind77_e1_chk : ind1K AP77 om77 (getL 0 ET77 1) = true := by quickRfl

theorem ind77_e2_chk : ind1K AP77 om77 (getL 0 ET77 2) = true := by quickRfl

theorem ind77_e3_chk : ind1K AP77 om77 (getL 0 ET77 3) = true := by quickRfl

theorem ind77_e4_chk : ind1K AP77 om77 (getL 0 ET77 4) = true := by quickRfl

@[expose] def IndAt (MT P : Nat) : Prop :=
  vmF 24 MT om77 = om77 ∧ ∀ i < 24, ∀ j < 24, i ≠ j →
    (vmF 24 MT (avK AP77 i j) = avK AP77 (ppg P i) (ppg P j) ∨
      vmF 24 MT (avK AP77 i j) = avK AP77 (ppg P i) (ppg P j) ^^^ om77)

@[expose] def Ind1At (MT : Nat) : Prop :=
  vmF 24 MT om77 = om77 ∧ ∀ i < 24, ∀ j < 24, i ≠ j →
    (vmF 24 MT (avK AP77 i j) = avK AP77 i j ∨ vmF 24 MT (avK AP77 i j) = avK AP77 i j ^^^ om77)

theorem ind77_n1 : IndAt N1T77 P77n1 :=
  ind_full ind77_n1_chk fr77_sym fun i hi => (perm_spec (CFSG.KC.Co1M.andB_true b77_perm).1 i hi).1

theorem ind77_n2 : IndAt N2T77 P77n2 :=
  ind_full ind77_n2_chk fr77_sym fun i hi =>
    (perm_spec (CFSG.KC.Co1M.andB_true (CFSG.KC.Co1M.andB_true b77_perm).2).1 i hi).1

theorem ind77_sB : IndAt SBT77 P77sB :=
  ind_full ind77_sB_chk fr77_sym fun i hi =>
    (perm_spec (CFSG.KC.Co1M.andB_true (CFSG.KC.Co1M.andB_true
      (CFSG.KC.Co1M.andB_true b77_perm).2).2).1 i hi).1

theorem ind77_e : ∀ k < 5, Ind1At (getL 0 ET77 k) := by
  intro k hk
  rcases k with _ | _ | _ | _ | _ | k
  · exact ind1_full ind77_e0_chk fr77_sym
  · exact ind1_full ind77_e1_chk fr77_sym
  · exact ind1_full ind77_e2_chk fr77_sym
  · exact ind1_full ind77_e3_chk fr77_sym
  · exact ind1_full ind77_e4_chk fr77_sym
  · omega

theorem e77_conj_chk : distinctK 5 (conjK EM77 SBK) = true := by quickRfl

theorem e77_invs_chk : invsK EM77 = true := by quickRfl

theorem e77_conj : (conjK EM77 SBK).Nodup := distinctK_sound e77_conj_chk

theorem e77_invs : ∀ e ∈ prodsK EM77 5, mulF 24 e e = idF 24 := invs_spec e77_invs_chk

theorem e77_len : (prodsK EM77 5).length = 32 := Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelCo1M

end
