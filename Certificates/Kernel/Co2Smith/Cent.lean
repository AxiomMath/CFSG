module

public import Certificates.Kernel.Co2Smith.ChainCard
public import Certificates.Kernel.Co2Smith.CentK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
open CFSG.Monster.B.Co2

@[expose] noncomputable def xP : Equiv.Perm (Fin 2300) := permK (XW 0)

noncomputable abbrev centX : Subgroup (Equiv.Perm (Fin 2300)) :=
  co2P ⊓ Subgroup.centralizer {xP}

theorem xw_facts : permOK 2300 12 (mask 12) (2300 * 12) (XW 0) (XW 1) = true ∧
    permOK 2300 12 (mask 12) (2300 * 12) (XW 2) (XW 3) = true ∧ siftP (XW 0) = true ∧
    siftP (XW 2) = true ∧ Nat.beq (pcomp 2300 12 (mask 12) (XW 0) (XW 2))
      (pcomp 2300 12 (mask 12) (XW 2) (KernelSporSch.Co2M.WE 0)) = true := by
  have h := xw_k
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem prep_x : PRep 2300 12 (XW 0) xP := prep_of_permOK xw_facts.1

theorem prep_z :
    PRep 2300 12 (KernelSporSch.Co2M.WE 0) locZ := by
  have hz : unpack 2300 12 (KernelSporSch.Co2M.WE 0) = zArr := by
    have e : KernelSporSch.Co2M.ztP 0 = KernelSporSch.Co2M.zP := by
      simp [KernelSporSch.Co2M.ztP]
    exact KernelSporSch.Co2M.unpack_eq KernelSporSch.Co2M.zRep
      (e ▸ allN_spec KernelSporSch.Co2M.bind_e 0 (by norm_num))
  refine prep_of_rep ?_
  rw [hz]
  exact KernelSporSch.Co2M.repK_z

theorem mem_P {P Q : Nat}
    (hp : permOK 2300 12 (mask 12) (2300 * 12) P Q = true) (hs : siftP P = true) :
    permK P ∈ co2P :=
  mem_P_of_sift (prep_of_permOK hp) hs

theorem mem_centX {P Q : Nat}
    (hp : permOK 2300 12 (mask 12) (2300 * 12) P Q = true) (hs : siftP P = true)
    (hc : Nat.beq (pcomp 2300 12 (mask 12) P (XW 0)) (pcomp 2300 12 (mask 12) (XW 0) P) = true) :
    permK P ∈ centX := by
  refine Subgroup.mem_inf.2 ⟨mem_P hp hs, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  exact comm_of_pcomp (prep_of_permOK hp) prep_x hc

theorem x_mem : xP ∈ co2P :=
  mem_P xw_facts.1 xw_facts.2.2.1

theorem w_mem :
    permK (XW 2) ∈ co2P :=
  mem_P xw_facts.2.1 xw_facts.2.2.2.1

theorem xw_conj :
    xP * permK (XW 2) = permK (XW 2) * locZ := by
  have h1 := prep_pcomp (by norm_num) prep_x (prep_of_permOK xw_facts.2.1)
  have h2 := prep_pcomp (by norm_num) (prep_of_permOK xw_facts.2.1) prep_z
  rw [Nat.eq_of_beq_eq_true xw_facts.2.2.2.2] at h1
  exact prep_unique h1 h2

theorem card_cent_le
    {K : Subgroup (Equiv.Perm (Fin 2300))} (hK : K ≤ centX) : Nat.card K ≤ 743178240 := by
  have h := card_mul_le_of_fix x_mem w_mem xw_conj hK
  exact Nat.le_of_mul_le_mul_right (h.trans (le_of_eq (by norm_num))) (by norm_num : 0 < 56925)

theorem tz_facts {k : Nat} (hk : k < 28) :
    permOK 2300 12 (mask 12) (2300 * 12) (TZ k) (TZ (28 + k)) = true ∧ siftP (TZ k) = true ∧
      Nat.beq (pcomp 2300 12 (mask 12) (TZ k) (XW 0)) (pcomp 2300 12 (mask 12) (XW 0) (TZ k)) =
        true ∧
      ∀ j < k, (!Nat.beq (pg 12 (mask 12) (TZ k) 0) (pg 12 (mask 12) (TZ j) 0)) = true := by
  have h := allN_spec tz_k k hk
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun j hj => allN_spec h4 j hj⟩

theorem tz_mem (k : Fin 28) :
    permK (TZ k.val) ∈ centX :=
  mem_centX (tz_facts k.isLt).1 (tz_facts k.isLt).2.1 (tz_facts k.isLt).2.2.1

theorem tz_pt (k : Fin 28) : ((permK (TZ k.val)) 0).val = pg 12 (mask 12) (TZ k.val) 0 :=
  ((prep_of_permOK (tz_facts k.isLt).1) 0).symm

theorem tz_ne {a b : Fin 28} (hlt : a.val < b.val) :
    pg 12 (mask 12) (TZ b.val) 0 ≠ pg 12 (mask 12) (TZ a.val) 0 := by
  intro e
  have h := (tz_facts b.isLt).2.2.2 a.val hlt
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem tz_pg {a b : Fin 28} (hab : permK (TZ a.val) 0 = permK (TZ b.val) 0) :
    pg 12 (mask 12) (TZ a.val) 0 = pg 12 (mask 12) (TZ b.val) 0 := by
  rw [← tz_pt, ← tz_pt, hab]

theorem tz_inj : Function.Injective fun k : Fin 28 => permK (TZ k.val) 0 := by
  intro a b hab
  have e := tz_pg hab
  apply Fin.ext
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact absurd e.symm (tz_ne h)
  · exact h
  · exact absurd e (tz_ne h)

theorem card_cent0_le
    {K : Subgroup (Equiv.Perm (Fin 2300))} (hK : K ≤ centX) (h0 : ∀ g ∈ K, g 0 = 0) :
    Nat.card K ≤ 26542080 := by
  have h := card_mul_le_of_orbit x_mem w_mem xw_conj tz_mem tz_inj hK h0
  rw [Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right (h.trans (le_of_eq (by norm_num))) (by norm_num : 0 < 28 * 56925)

end CertificateChecks.KernelCo2Smith
