module

public import Certificates.Kernel.Co2Cent.CaseBFix
public import Certificates.Kernel.Co2Cent.FusChk
public import CFSG.Certificates.Kernel.OrbRow.FusSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KD.Co2Cent
  Subgroup CFSG.Sporadic.Co2Cert

theorem fh_mem {j : ℕ} (hj : j < 40) :
    PRep 2300 12 (getS H j) (wvB (getLs HW j)) ∧ wvB (getLs HW j) ∈ co2P := by
  obtain ⟨hl, he⟩ := wordEqK_sound (allN_spec ch17351_fh j hj)
  rw [he]
  exact word_repB hl

theorem fkFacts : (∀ k, 0 < k → k < 81 → fusK 2300 12 (mask 12) DG H xA xB FI FC FE k = true) ∧
    getS FC 5 = 0 ∧ getS FC 4 = 1 := by
  have h := ch17351_fk
  simp only [bAnd_iff] at h
  refine ⟨fun k hk0 hk => ?_, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  exact allN_spec h.1 t (by omega)

theorem lenH : lenS H = 40 := by decide +kernel

theorem fusion
    {d : ℕ → Equiv.Perm (Fin 2300)} (hd : ∀ i < 4, PRep 2300 12 (getS DG i) (d i))
    {xa xb : Equiv.Perm (Fin 2300)} (hxa : PRep 2300 12 xA xa) (hxb : PRep 2300 12 xB xb)
    {k : ℕ} (hk0 : 0 < k) (hk : k < 81) :
    ∃ h ∈ co2P, ∃ c : Equiv.Perm (Fin 2300), (c = xa ∨ c = xb) ∧ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      h * ((dgtWord k).map d).prod * h⁻¹ = c ^ e ∧ (getS FC k = 0 → c = xa) ∧
      (getS FC k ≠ 0 → c = xb) := by
  have hf := fkFacts.1 k hk0 hk
  have hj : getS FI k < 40 := by
    have := fusK_idx hf
    rwa [lenH] at this
  obtain ⟨hp, hm⟩ := fh_mem hj
  obtain ⟨-, hA, hB, he⟩ := fusK_sound (by norm_num) (by norm_num) hf hd hxa hxb hp
  by_cases hc : getS FC k = 0
  · exact ⟨_, hm, xa, Or.inl rfl, _, he, hA hc, fun _ => rfl, fun h => absurd hc h⟩
  · exact ⟨_, hm, xb, Or.inr rfl, _, he, hB hc, fun h => absurd h hc, fun _ => rfl⟩

theorem fusion_d5
    {d : ℕ → Equiv.Perm (Fin 2300)} (hd : ∀ i < 4, PRep 2300 12 (getS DG i) (d i))
    {xa xb : Equiv.Perm (Fin 2300)} (hxa : PRep 2300 12 xA xa) (hxb : PRep 2300 12 xB xb) :
    ∃ h ∈ co2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ h * ((dgtWord 5).map d).prod * h⁻¹ = xa ^ e := by
  obtain ⟨h, hh, c, -, e, he, hc, hA, -⟩ := fusion hd hxa hxb (k := 5) (by norm_num) (by norm_num)
  rw [hA fkFacts.2.1] at hc
  exact ⟨h, hh, e, he, hc⟩

theorem fusion_d4
    {d : ℕ → Equiv.Perm (Fin 2300)} (hd : ∀ i < 4, PRep 2300 12 (getS DG i) (d i))
    {xa xb : Equiv.Perm (Fin 2300)} (hxa : PRep 2300 12 xA xa) (hxb : PRep 2300 12 xB xb) :
    ∃ h ∈ co2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ h * ((dgtWord 4).map d).prod * h⁻¹ = xb ^ e := by
  obtain ⟨h, hh, c, -, e, he, hc, -, hB⟩ := fusion hd hxa hxb (k := 4) (by norm_num) (by norm_num)
  rw [hB (by rw [fkFacts.2.2]; norm_num)] at hc
  exact ⟨h, hh, e, he, hc⟩

end CertificateChecks.KernelCo2Cent

end
