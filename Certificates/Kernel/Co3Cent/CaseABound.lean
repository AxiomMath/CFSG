module

public import Certificates.Kernel.Co3Cent.CaseAGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.OrbRow.CentGrp CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KD.Co3Cent Subgroup
open CFSG.KC.Misc.ArrEnum (permB)
open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

@[expose] noncomputable def CA : Subgroup (Equiv.Perm (Fin 276)) := centralizer {xA} ⊓ co3P

theorem mem_CA {g : Equiv.Perm (Fin 276)} : g ∈ CA ↔ g * xA = xA * g ∧ g ∈ co3P := by
  rw [CA, Subgroup.mem_inf, mem_centralizer_singleton_iff]

theorem fix_CA {g : Equiv.Perm (Fin 276)} (hg : g ∈ CA) {r : Fin 276} (hr : xA r = r) :
    xA (g r) = g r := by
  have e := congrArg (fun σ : Equiv.Perm (Fin 276) => σ r) (mem_CA.1 hg).1
  simp only [Equiv.Perm.mul_apply, hr] at e
  exact e.symm

theorem BA_inj : ∀ s t : Fin 6, getS BA s = getS BA t → s = t := by decide +kernel

@[expose] noncomputable def capA (i : ℕ) : Finset (Fin 276) :=
  (Finset.univ.filter fun t : Fin 6 => i ≤ t.val).image FA

theorem capA_card : ∀ i < 6, (capA i).card ≤ 6 - i := by
  intro i hi
  refine Finset.card_image_le.trans ?_
  interval_cases i <;> decide

theorem img_capA {i : ℕ} (hi : i < 6) {g : Equiv.Perm (Fin 276)} (hg : g ∈ stabB CA bA i) :
    g (bA i) ∈ capA i := by
  obtain ⟨t, ht⟩ := (fixA _).1 (fix_CA hg.1 (fixA_lt hi))
  refine Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ht⟩
  by_contra hlt
  push Not at hlt
  have e : g (FA t) = FA t := hg.2 t hlt
  rw [← e] at ht
  have h2 := congrArg Fin.val (g.injective ht)
  have h3 : t.val = i := congrArg Fin.val (BA_inj t ⟨i, hi⟩ h2)
  omega

theorem le_half {d n : ℕ} (hd : d ∣ n) (hne : d ≠ n) (hn : 0 < n) : d ≤ n / 2 := by
  obtain ⟨k, rfl⟩ := hd
  rcases k with _ | _ | k
  · simp at hn
  · simp at hne
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith

theorem card_CA :
    Nat.card CA ≤ 349920 := by
  have hL : Nat.card (stabB CA bA 6) ≤ 486 := by
    have hle : stabB CA bA 6 ≤ Gv SA MA 17 6 := by
      intro g hg
      rw [KA_eq]
      exact ⟨(mem_CA.1 hg.1).2, hg.2⟩
    have hJ : sv SA JK ∈ Gv SA MA 17 6 :=
      subset_closure ⟨JK, lvOk_of_letter ⟨Nat.le_of_ble_eq_true xaFacts.2.2.2.1,
        xaFacts.2.2.2.2.1⟩, rfl⟩
    have hJn : sv SA JK ∉ stabB CA bA 6 := by
      intro h
      have hc := (mem_CA.1 h.1).1
      have hp := permS sFacts.1 JK (Nat.le_of_ble_eq_true xaFacts.2.2.2.1)
      have h1 : commOK 276 9 (mask 9) (getS SA JK) xAp = true :=
        (commOK_iff (prep_pv hp) prepXA).2 hc
      have h2 : commOK 276 9 511 (getS SA JK) xAp = true := h1
      have hx := xaFacts.2.2.2.2.2
      rw [h2] at hx
      exact absurd hx (by decide)
    have hne : Nat.card (stabB CA bA 6) ≠ 972 := by
      intro h
      have := Subgroup.eq_of_le_of_card_ge hle (by rw [card_KA, h])
      exact hJn (this ▸ hJ)
    have hd : Nat.card (stabB CA bA 6) ∣ 972 := card_KA ▸ Subgroup.card_dvd_of_le hle
    have := le_half hd hne (by norm_num)
    omega
  have h := CFSG.KC.Co3Cent.bound_of_chain CA bA 6 (fun i => 6 - i) 486
    (fun i hi => ⟨capA i, capA_card i hi, fun g hg => img_capA hi hg⟩) hL
  have hp : ∏ i ∈ Finset.range 6, (6 - i) = 720 := by decide
  rw [hp] at h
  exact h

@[expose] noncomputable def HAg : Subgroup (Equiv.Perm (Fin 276)) := Gv SHA MHA 17 0

theorem cHA : allN 17 (fun j => commOK 276 9 511 (getS SHA j) xAp) = true := by
  have h := ch17370_c
  simp only [bAnd_iff] at h
  exact h.1

theorem sha_facts {j : ℕ}
    (hj : j < 17) : permB 276 9 (getS SHA j) = true ∧ sv SHA j ∈ CA := by
  have hp := permS sFacts.2.2.1 j hj
  have hc : commOK 276 9 (mask 9) (getS SHA j) xAp = true := allN_spec cHA j hj
  exact ⟨hp, mem_CA.2 ⟨(commOK_iff (prep_pv hp) prepXA).1 hc, pv_mem (allN_spec sFacts.2.2.1 j hj)⟩⟩

theorem HAg_le : HAg ≤ CA := by
  rw [HAg, Gv, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact (sha_facts (lvOk_iff.1 hj).1).2

theorem CA_eq : HAg = CA :=
  Subgroup.eq_of_le_of_card_ge HAg_le (card_CA.trans card_HA)

theorem card_CA_eq :
    Nat.card CA = 349920 := by
  rw [← CA_eq]
  exact le_antisymm (CA_eq ▸ card_CA) card_HA

theorem conj_K
    {y r : Equiv.Perm (Fin 276)} (hy : y ∈ CA) (hr : r ∈ Gv SA MA 17 6) :
    y * r * y⁻¹ ∈ Gv SA MA 17 6 := by
  obtain ⟨hrP, hrF⟩ := (memK_iff r).1 hr
  have hyP : y ∈ co3P := (mem_CA.1 hy).2
  rw [memK_iff]
  refine ⟨co3P.mul_mem (co3P.mul_mem hyP hrP) (co3P.inv_mem hyP), fun t => ?_⟩
  have hfx : xA (y⁻¹ (FA t)) = y⁻¹ (FA t) := fix_CA (CA.inv_mem hy) ((fixA _).2 ⟨t, rfl⟩)
  obtain ⟨s, hs⟩ := (fixA _).1 hfx
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hs, hrF s, hs]
  exact y.apply_symm_apply (FA t)

theorem conj_mem_RA
    {yp : ℕ} {y : Equiv.Perm (Fin 276)} (hy : PRep 276 9 yp y)
    (hn : normK 276 9 511 RGp 5 yp BA 6 5 RK = true) {j : ℕ} (hj : j < 5)
    (hK : y * rv j * y⁻¹ ∈ Gv SA MA 17 6) : y * rv j * y⁻¹ ∈ RA := by
  obtain ⟨hp, hk⟩ := normK_sound hn
  have hyi := prep_inv hp hy
  have e := conjKey_tkey hy hyi (prepRG hj) hvR
  refine keyR_facts.2 _ hK (mem_ER.2 ?_)
  rw [← e]
  exact hk j hj

theorem rnFacts : allN 17 (fun j => normK 276 9 511 RGp 5 (getS SHA j) BA 6 5 RK) = true ∧
    allN 2 (fun j => normK 276 9 511 RGp 5 (getS U j) BA 6 5 RK) = true := by
  have h := ch17370_rn
  simp only [bAnd_iff] at h
  exact h

theorem RA_norm :
    ∀ g ∈ CA, ∀ r ∈ RA, g * r * g⁻¹ ∈ RA := by
  rw [← CA_eq]
  refine conj_mem_of_closure RA_eq ?_
  rintro _ ⟨j, hj, rfl⟩ _ ⟨l, rfl⟩
  have hj17 := (lvOk_iff.1 hj).1
  obtain ⟨hp, hCj⟩ := sha_facts hj17
  exact conj_mem_RA (prep_pv hp) (allN_spec rnFacts.1 j hj17) l.2
    (conj_K hCj (RA_le (rv_mem_RA l.2)))

end CertificateChecks.KernelCo3Cent

end
